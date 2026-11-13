#!/usr/bin/env python3
"""Generate the leanblueprint LaTeX from the Markdown blueprints (documentation plan B1-B12).

Sources (B2): the Markdown blueprints (authoritative), `blueprint/status.md` (statuses, B6) and
the item -> Lean-name table `blueprint/lean-map.md` (B10). The declaration dump of
`scripts/blueprint_decls.py` (`blueprint/.cache/decls.jsonl`) is used to seed the table and to
check the `\\uses` edges against the Lean dependencies (B3).

Subcommands:
  seed   write `blueprint/lean-map.md` from the docstring tags (only if it does not exist, or
         with --force); the main agent then curates it (B10).
  build  write `blueprint/src/chapters/*.tex` and `blueprint/src/content.tex`.
  check  names in lean-map exist; tagged declarations not covered; Lean dependencies between
         items that the Markdown does not mention (B3); Markdown edges without Lean support.
  nodes  list the parsed nodes (debugging).

Nodes (B5): one per blueprint item. `blueprint.md` items come from its `### ID — Title (TAG)`
headings (sections 1-5; LATER items and the checks K* are left out, B4, B6); Z4 items from the
list in blueprint section 11 v1.14; Z2, Z5 and Z3 items from the item tables of blueprint-tr,
blueprint-ll and blueprint-tw, with the proof steps their rows cite (B11).
Edges: item numbers mentioned in a node's text (sub-items such as A4.b count for A4), plus the
extra edges of lean-map; self-mentions and the "Drop uses" of lean-map are removed.
"""
import json
import os
import re
import sys
from collections import OrderedDict, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BP = os.path.join(ROOT, 'blueprint')
SRC = os.path.join(BP, 'src')
CHAP_DIR = os.path.join(SRC, 'chapters')
DECLS = os.path.join(BP, '.cache', 'decls.jsonl')
LEAN_MAP = os.path.join(BP, 'lean-map.md')
DISPLAY = os.path.join(BP, 'node-statements.md')
STATUS = os.path.join(BP, 'status.md')
# Working notes of the private repository; optional (absent in the public copy).
PROGRESS = os.path.join(ROOT, 'internal', 'PROGRESS.md')
SUMMARY = os.path.join(ROOT, 'docs', 'formalization-summary.tex')


def read(path):
    with open(path, encoding='utf-8') as f:
        return f.read()


# ----------------------------------------------------------------------------------------------
# Data model

class Node:
    def __init__(self, nid, chapter, title, source, statement='', proof=''):
        self.id = nid
        self.chapter = chapter
        self.title = title
        self.source = source          # "file §section" for the reader
        self.statement = statement    # Markdown (from the blueprints; edges are read from it)
        self.proof = proof            # Markdown
        self.display = ''             # readable statement from node-statements.md (shown)
        self.tag = 'BUILD'
        self.status = None            # proved / stated / todo / None
        self.lean = []                # main declarations (lean-map)
        self.uses_stmt = set()
        self.uses_proof = set()

    @property
    def label(self):
        return self.id.replace('′', 'prime')


# Chapters (B7: one per sub-blueprint; blueprint.md split by layer).
CHAPTERS = OrderedDict([
    ('A', 'Cohesive modules over a dga'),
    ('S', 'Sheaves on a compact space'),
    ('C', 'The comparison theorem'),
    ('F', 'The Dolbeault sheaf and the main theorem'),
    ('Z4', 'Proof of H1: the Dolbeault–Grothendieck lemma'),
    ('Z5', 'Proof of H2: the local gauge lemma'),
    ('Z2', 'The triangulated structure on Ho(P_A)'),
    ('Z3', 'The twisted theorem'),
])

# Mentions of a whole Z-project stand for its main item.
ALIASES = {'Z2': 'Z2.g', 'Z3': 'Z3.v', 'Z4': 'Z4.g', 'Z5': 'Z5.i'}


# ----------------------------------------------------------------------------------------------
# Markdown helpers

def sections(text, level):
    """Split Markdown text at headings of the given level: list of (heading, body)."""
    out = []
    head, buf = None, []
    prefix = '#' * level + ' '
    in_code = False
    for line in text.split('\n'):
        if line.startswith('```'):
            in_code = not in_code
        if not in_code and line.startswith(prefix):
            if head is not None or buf:
                out.append((head, '\n'.join(buf)))
            head, buf = line[len(prefix):].strip(), []
        else:
            buf.append(line)
    out.append((head, '\n'.join(buf)))
    return out


def cut_at_higher(body, level):
    """Body up to the first heading of a level < `level` (sections() already cuts equal ones)."""
    lines, out, in_code = body.split('\n'), [], False
    for line in lines:
        if line.startswith('```'):
            in_code = not in_code
        if not in_code and re.match(r'#{1,%d} ' % (level - 1), line):
            break
        out.append(line)
    return '\n'.join(out)


def split_proof(md):
    """Statement / proof split: a top-level paragraph starting with "Proof" starts the proof."""
    paras = re.split(r'\n\s*\n', md.strip())
    for i, p in enumerate(paras):
        if re.match(r'(\*\*)?\*?Proof\b', p.strip()):
            return '\n\n'.join(paras[:i]), '\n\n'.join(paras[i:])
    return md.strip(), ''


# ----------------------------------------------------------------------------------------------
# Parsing blueprint.md

HEAD_RE = re.compile(r'^(\S+) — (.*)$')
TAG_RE = re.compile(r'\b(BUILD|HYP|LATER)\b')


def parse_head(head):
    m = HEAD_RE.match(head)
    if not m:
        return None
    nid, rest = m.group(1), m.group(2)
    t = TAG_RE.search(rest)
    tag = t.group(1) if t else 'BUILD'
    title = re.sub(r'\s*\([^()]*\)\s*$', '', rest).strip()
    title = re.sub(r'\s*\([^()]*\)\s*$', '', title).strip()
    return nid, title, tag


def chapter_of(nid):
    if nid == 'M' or nid in ('H1', 'H2'):
        return 'F'
    return nid[0] if nid[0] in 'ASCF' else None


def parse_main_blueprint():
    text = read(os.path.join(BP, 'blueprint.md'))
    nodes, intros = [], {}
    for h2, body2 in sections(text, 2):
        if not h2:
            continue
        num = h2.split('.')[0]
        if num not in ('1', '2', '3', '4', '5'):
            continue
        parts = sections(body2, 3)
        intro = parts[0][1] if parts and parts[0][0] is None else ''
        layer = {'2': 'A', '3': 'S', '4': 'C', '5': 'F'}.get(num)
        if layer:
            intros[layer] = intro.strip()
        for h3, body3 in parts:
            if not h3:
                continue
            parsed = parse_head(h3)
            if not parsed:
                continue
            nid, title, tag = parsed
            if tag == 'LATER' or nid.startswith('K'):
                continue
            ch = chapter_of(nid)
            if ch is None:
                continue
            st, pf = split_proof(body3)
            n = Node(nid, ch, title, f'blueprint.md §{num}', st, pf)
            n.tag = tag
            nodes.append(n)
    return nodes, intros


def parse_z4():
    """Z4.a-Z4.h: the list in blueprint.md §11, v1.14 item 2."""
    text = read(os.path.join(BP, 'blueprint.md'))
    start = text.index('**Items Z4.a–Z4.h**')
    end = text.index('\n3. **Conventions**', start)
    block = text[start:end]
    nodes = []
    for m in re.finditer(r'^   - \*\*(Z4\.[a-h]) ([^*]+)\*\*(.*?)(?=^   - \*\*Z4|\Z)', block,
                         re.M | re.S):
        nid, title, body = m.group(1), m.group(2).strip(), m.group(3)
        body = re.sub(r'\n     ', '\n', body).strip()
        if body.startswith(':'):
            body = body[1:].strip()
        nodes.append(Node(nid, 'Z4', title, 'blueprint.md §11 v1.14', body))
    return nodes


def table_rows(md, first_col_re):
    rows = []
    for line in md.split('\n'):
        if not line.startswith('|'):
            continue
        cells = [c.strip() for c in re.split(r'(?<!\\)\|', line.strip())[1:-1]]
        if cells and re.match(first_col_re, cells[0]):
            rows.append(cells)
    return rows


# Proof steps: "**C.4 Smoothness.**", "**A.2**", "**D.**", "### D. Induction".
STEP_RE = re.compile(r'\*\*([A-H])\.(\d+′*)?|^### ([A-H])\. ', re.M)


def steps_of(md):
    """Segments of a proof section keyed by (letter, number or None)."""
    marks = [(m.start(), (m.group(1) or m.group(3), m.group(2))) for m in STEP_RE.finditer(md)]
    segs = OrderedDict()
    for i, (pos, key) in enumerate(marks):
        end = marks[i + 1][0] if i + 1 < len(marks) else len(md)
        seg = md[pos:end]
        seg = re.sub(r'\n\s*-\s*$', '', seg.rstrip()).rstrip()
        if seg.endswith('\n-'):
            seg = seg[:-2]
        segs.setdefault(key, '')
        segs[key] += seg.strip() + '\n'
    return segs


def cited_steps(cell, segs):
    """Step keys cited in a table cell: A.2, A.2–A.4, C.7 (a)–(f), whole letters (D), F:."""
    keys = []
    for m in re.finditer(r'\b([A-H])\.(\d+)(′*)(?:\s*[–-]\s*(?:[A-H]\.)?(\d+))?', cell):
        letter, a, prime, b = m.group(1), int(m.group(2)), m.group(3), m.group(4)
        for k in range(a, (int(b) if b else a) + 1):
            for key in segs:
                if key[0] == letter and key[1] and re.fullmatch(r'%d′*' % k, key[1]):
                    if key not in keys:
                        keys.append(key)
    for m in re.finditer(r'\(([A-H])\)|\b([A-H]):', cell):
        letter = m.group(1) or m.group(2)
        for key in segs:
            if key[0] == letter and key not in keys:
                keys.append(key)
    return keys


def table_nodes(fname, chapter, item_re, table_heading, proof_heading, extra_sections=None):
    text = read(os.path.join(BP, fname))
    secs = dict(sections(text, 2))
    table_md = next(b for h, b in secs.items() if h and h.startswith(table_heading))
    proof_md = next((b for h, b in secs.items() if h and h.startswith(proof_heading)), '')
    proof_md = re.sub(r'```.*?```', '', proof_md, flags=re.S)
    segs = steps_of(proof_md)
    used = {}
    nodes = []
    sub3 = {}
    for h, b in sections(text, 3):
        if h:
            sub3[h.split(' ')[0]] = b
    for cells in table_rows(table_md, item_re):
        m = re.match(r'(\S+)\s*(.*)', cells[0])
        nid, title = m.group(1), re.sub(r'\s*\(v1\.\d+\)', '', m.group(2)).strip()
        file_col = cells[1] if len(cells) > 1 else ''
        content = cells[2] if len(cells) > 2 else ''
        stmt = content
        if file_col:
            stmt += '\n\nFiles: ' + file_col + '.'
        proof = []
        for key in cited_steps(content, segs):
            if key in used:
                proof.append(f'Step {key[0]}{"." + key[1] if key[1] else ""}: see {used[key]}.')
            else:
                used[key] = nid
                proof.append(segs[key])
        for sec in (extra_sections or {}).get(nid, []):
            if sec in sub3:
                proof.append(sub3[sec].strip())
        # §2.1-2.2 style citations of definition subsections of the same file
        for m2 in re.finditer(r'§(\d+)\.(\d+)(?:[–-](\d+)\.(\d+))?', content):
            a, b = int(m2.group(2)), int(m2.group(4) or m2.group(2))
            for k in range(a, b + 1):
                key = f'{m2.group(1)}.{k}'
                if key in sub3:
                    proof.append(sub3[key].strip())
        title = title[:1].upper() + title[1:] if title and title[0] != '`' else title
        n = Node(nid, chapter, title or nid, f'{fname} §{table_heading.split(".")[0]}', stmt,
                 '\n\n'.join(p for p in proof if p.strip()))
        nodes.append(n)
    return nodes, secs


# Sub-items moved into a node of their own because they are not formalized and not needed, so
# that they do not block the "fully proved" colour of everything above their item (leanblueprint
# colours a node dark green only if all its ancestors are proved). (new id, title, bullet, note
# left in the parent item)
SPLITS = {
    'A3': ('A3.b′', 'Flatness in all degrees', '**A3.b**',
           'A3.b in degree 0 (`X0_X0`) is part of this item; the other degrees are A3.b′ '
           '(not formalized, not needed).'),
}


def apply_splits(nodes):
    out = []
    for n in nodes:
        out.append(n)
        if n.id not in SPLITS:
            continue
        nid, title, marker, note = SPLITS[n.id]
        m = re.search(r'^- ' + re.escape(marker) + r'.*?(?=^- \*\*|\Z)', n.statement, re.M | re.S)
        if not m:
            continue
        bullet = m.group(0).strip()
        n.statement = (n.statement[:m.start()] + n.statement[m.end():]).rstrip() + '\n\n' + note
        n.split_children = {nid}      # the note mentions the child; that is not a dependency
        out.append(Node(nid, n.chapter, title, n.source, bullet[2:]))
    return out


def parse_subblueprints():
    nodes, intros = [], {}
    z2, secs = table_nodes('blueprint-tr.md', 'Z2', r'Z2\.[a-z]$', '5.', '3.',
                           extra_sections={'Z2.f': ['3c.'], 'Z2.g': ['3d.']})
    titles = {'Z2.a': 'Shift', 'Z2.b': 'Shift functor on Ho(P_A)', 'Z2.c': 'Zero object',
              'Z2.d': 'Cone', 'Z2.e': 'Maps of cones', 'Z2.f': 'Pretriangulated structure',
              'Z2.g': 'Octahedron axiom'}
    for n in z2:
        n.title = titles.get(n.id, n.title)
    nodes += z2
    intros['Z2'] = (secs.get('Overview', '') + '\n\n' +
                    next(b for h, b in secs.items() if h and h.startswith('2.'))).strip()
    z5, secs = table_nodes('blueprint-ll.md', 'Z5', r'Z5\.[a-j]$', '5.', '4.')
    titles = {'Z5.a': 'Kernel estimate', 'Z5.b': 'Derivatives of the solver',
              'Z5.c': 'One-variable gauge solver', 'Z5.d': 'Fibre operators',
              'Z5.e': 'Flat superconnections and gauges', 'Z5.f': 'Gauge induction',
              'Z5.g': 'Local freeness', 'Z5.h': 'Frame model', 'Z5.i': 'The local gauge lemma',
              'Z5.j': 'Block\'s theorem without hypotheses'}
    for n in z5:
        n.title = titles.get(n.id, n.title)
    nodes += z5
    intros['Z5'] = secs.get('Overview', '').strip()
    z3, secs = table_nodes('blueprint-tw.md', 'Z3', r'Z3\.[a-z]′?\b', '4.', '3.')
    nodes += z3
    intros['Z3'] = secs.get('Overview', '').strip()
    text = read(os.path.join(BP, 'blueprint-dg.md'))
    s = dict(sections(text, 2))
    intros['Z4'] = (s.get('Overview', '') + '\n\n' + s.get('Mathematical proof', '')).strip()
    nodes += parse_z4()
    return nodes, intros


# ----------------------------------------------------------------------------------------------
# Status (B6) and the Lean-name table (B10)

def parse_progress(nodes, path=None):
    """Set `n.status` from the item tables of `path` (default: `blueprint/status.md`)."""
    ids = {n.id for n in nodes}
    status = defaultdict(list)
    for line in read(path or STATUS).split('\n'):
        if not line.startswith('| '):
            continue
        cells = [c.strip() for c in line.split('|')[1:-1]]
        if len(cells) < 3:
            continue
        tok = cells[0].split(' ')[0]
        nid = tok if tok in ids else re.sub(r'\d+$', '', tok)   # Z2.f1 -> Z2.f
        if nid in ids:
            status[nid].append(cells[2].split(' ')[0])
    for n in nodes:
        st = status.get(n.id, [])
        if not st:
            n.status = None
        elif all(s == 'proved' for s in st):
            n.status = 'proved'
        elif any(s == 'todo' for s in st):
            n.status = 'todo'
        else:
            n.status = 'proved' if 'proved' in st and 'stated' not in st else 'stated'
    # B6': H1 and H2 are proved (by Z4.g and Z5.i).
    for n in nodes:
        if n.id in ('H1', 'H2'):
            n.status = 'proved'


def load_decls():
    decls = {}
    with open(DECLS, encoding='utf-8') as f:
        for line in f:
            r = json.loads(line)
            decls[r['n']] = r
    return decls


TAG_DOC_RE = re.compile(r'^\*\*([A-Z][0-9]+(?:\.[a-z][0-9]*′?)?)')


def node_of_tag(tag, ids):
    if tag in ids:
        return tag
    t = re.sub(r'\d+$', '', tag)          # Z2.f1 -> Z2.f
    if t in ids:
        return t
    t = tag.split('.')[0]                 # A2.a -> A2
    return t if t in ids else None


def tagged(decls, ids):
    """node id -> public tagged declarations (in dump order)."""
    out = defaultdict(list)
    for n, r in decls.items():
        if r['p'] or r['i'] or not r['d']:
            continue
        m = TAG_DOC_RE.match(r['d'].strip())
        if not m:
            continue
        nid = node_of_tag(m.group(1), ids)
        if nid:
            out[nid].append(n)
    return out


ITEM_LIST_RE = re.compile(r'[A-Z][0-9]+(?:\.[a-z][0-9]*′?)?|\bM\b')


LEAN_MAP_HEADER = ('| Item | Lean | Extra uses | Cycle breaks | Dropped (no Lean dependency) | '
                   'Lean uses (B3) |')


def parse_lean_map():
    """lean-map.md: | Item | Lean | Extra uses | Cycle breaks | Dropped | Lean uses |

    Returns item -> (names, extra, breaks, dropped, lean_uses). Columns 2-4 are written by hand;
    5 and 6 by `sync` (Lean is the arbiter of dependencies, human 10 Nov 2026):
      Extra uses    edges to add (they are checked like Markdown mentions);
      Cycle breaks  Lean dependencies left out because Lean has a cycle between the two items
                    (an effect of how declarations are tagged to items);
      Dropped       Markdown mentions that are not Lean dependencies (automatic);
      Lean uses     Lean dependencies the Markdown does not give, transitively reduced
                    (automatic)."""
    m = {}
    if not os.path.exists(LEAN_MAP):
        return m
    for cells in table_rows(read(LEAN_MAP), r'[A-Z]'):
        if cells[0] == 'Item':
            continue
        col = lambda i: cells[i] if len(cells) > i else ''
        m[cells[0]] = (re.findall(r'`([^`]+)`', col(1)), ITEM_LIST_RE.findall(col(2)),
                       ITEM_LIST_RE.findall(col(3)), ITEM_LIST_RE.findall(col(4)),
                       ITEM_LIST_RE.findall(col(5)))
    return m


def write_auto_columns(nodes, breaks, dropped, lean_uses):
    """Rewrite lean-map.md with columns 4-6 computed by `sync`; columns 1-3 are kept, and rows
    are added for nodes that have none."""
    lines = read(LEAN_MAP).split('\n')
    rows, head, tail = {}, [], []
    state = 'head'                       # head -> table -> tail (e.g. "Owner overrides")
    for line in lines:
        if state == 'head' and line.startswith('| Item'):
            state = 'table'
        if state == 'table' and not line.startswith('|'):
            state = 'tail'
        if state == 'head':
            head.append(line)
        elif state == 'tail':
            tail.append(line)
        elif not line.startswith('| Item') and not line.startswith('| ---'):
            cells = [c.strip() for c in line.strip().split('|')[1:-1]]
            rows[cells[0]] = (cells + [''] * 6)[:6]
    out = head + [LEAN_MAP_HEADER, '| --- | --- | --- | --- | --- | --- |']
    for n in nodes:
        cells = rows.get(n.id, [n.id, '', '', '', '', ''])
        cells[3] = ', '.join(sorted(breaks.get(n.id, [])))
        cells[4] = ', '.join(sorted(dropped.get(n.id, [])))
        cells[5] = ', '.join(sorted(lean_uses.get(n.id, [])))
        out.append('| ' + ' | '.join(cells) + ' |')
    out += tail
    with open(LEAN_MAP, 'w', encoding='utf-8') as f:
        f.write('\n'.join(out).rstrip('\n') + '\n')


# ----------------------------------------------------------------------------------------------
# Edges from mentions

ID_RE = re.compile(r'(?<![\w.`])([ASCFHZ][0-9]+(?:\.[a-z][0-9]*′?)?)'
                   r'(?:\s*[–-]\s*([a-z0-9]+))?(?![\w′])')


def mentions(md, ids):
    md = re.sub(r'```.*?```', '', md, flags=re.S)
    md = re.sub(r'`[^`]*`', '', md)
    # audit findings are numbered like items ("audit F5", "audit F6, F9, F12"; blueprint-dg's
    # simplifications S1-S3): not item mentions
    md = re.sub(r'audit [A-Z][0-9]+[a-z]?(?:,\s*[A-Z][0-9]+)*', '', md)
    md = re.sub(r'simplifications? S[0-9](?:[–-]S?[0-9])?|\(S[0-9]\)', '', md)
    out = set()
    for m in ID_RE.finditer(md):
        tok, upto = m.group(1), m.group(2)
        cands = [tok]
        if upto:   # ranges: Z5.g–i, A1–A13 (written A1–13 rarely), Z3.a–e
            mm = re.match(r'(.*?\.)([a-z])$', tok)
            if mm and re.fullmatch(r'[a-z]', upto):
                cands = [mm.group(1) + chr(c) for c in range(ord(mm.group(2)), ord(upto) + 1)]
            mm = re.match(r'([A-Z])(\d+)$', tok)
            if mm and upto.isdigit():
                cands = [f'{mm.group(1)}{k}' for k in range(int(mm.group(2)), int(upto) + 1)]
        for c in cands:
            c = ALIASES.get(c, c)
            nid = node_of_tag(c, ids)
            if nid:
                out.add(nid)
    return out


def assign_edges(nodes, lean_map, apply_drops=True):
    """Edges from mentions and Extra uses, minus Cycle breaks and Dropped, plus Lean uses.
    `sync` calls it with apply_drops=False to see the raw Markdown edges."""
    ids = {n.id for n in nodes}
    for n in nodes:
        st = mentions(n.statement, ids) - {n.id}
        pf = mentions(n.proof, ids) - {n.id}
        names, extra, breaks, dropped, lean_uses = lean_map.get(n.id, ([], [], [], [], []))
        n.breaks = set(breaks)
        n.drop = getattr(n, 'split_children', set())
        if apply_drops:
            n.drop |= set(breaks) | set(dropped)
        if n.proof.strip() or n_is_theorem(n):
            n.uses_stmt, n.uses_proof = st, pf | set(extra) | set(lean_uses)
        else:
            n.uses_stmt, n.uses_proof = st | set(extra) | set(lean_uses), set()
        n.uses_stmt -= n.drop
        n.uses_proof -= n.drop | n.uses_stmt
        n.uses_stmt &= ids
        n.uses_proof &= ids


def n_is_theorem(n):
    return getattr(n, 'env', 'theorem') == 'theorem'


# ----------------------------------------------------------------------------------------------
# Markdown -> LaTeX

def esc_code(s):
    rep = {'\\': r'\textbackslash{}', '{': r'\{', '}': r'\}', '#': r'\#', '$': r'\$',
           '%': r'\%', '&': r'\&', '_': r'\_', '^': r'\textasciicircum{}',
           '~': r'\textasciitilde{}'}
    return ''.join(rep.get(c, c) for c in s)


SCRIPT_RE = re.compile(r'(?<=[^\s^_])([\^_])(\{[^{}]*\}|[\w•′⁰¹²³⁴⁵⁶⁷⁸⁹∞+−*]+)')


def esc_text(s):
    """Escape prose; `A^0`, `X^{p+1}`, `D_perf` become super- and subscripts (the Markdown
    writes mathematics in Unicode with ^ and _, conventions of the blueprints)."""
    out, pos = [], 0
    for m in SCRIPT_RE.finditer(s):
        out.append(esc_code(s[pos:m.start()]))
        body = m.group(2)
        if body.startswith('{'):
            body = body[1:-1]
        cmd = r'\textsuperscript' if m.group(1) == '^' else r'\textsubscript'
        out.append(cmd + '{' + esc_code(body) + '}')
        pos = m.end()
    out.append(esc_code(s[pos:]))
    return ''.join(out).replace('⚠', r'\warn{}')


def inline(s):
    out, pos = [], 0
    for m in re.finditer(r'`([^`]+)`|\[([^\]]+)\]\(([^)]+)\)', s):
        out.append(fmt(esc_text(s[pos:m.start()])))
        if m.group(1) is not None:
            out.append(r'\texttt{' + esc_code(m.group(1)) + '}')
        else:
            out.append(r'\href{' + m.group(3).replace('%', r'\%').replace('#', r'\#') + '}{' +
                       fmt(esc_text(m.group(2))) + '}')
        pos = m.end()
    out.append(fmt(esc_text(s[pos:])))
    return ''.join(out)


def fmt(s):
    s = re.sub(r'\*\*(.+?)\*\*', r'\\textbf{\1}', s)
    s = re.sub(r'(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])', r'\\emph{\1}', s)
    return s


LIST_RE = re.compile(r'^(\s*)([-*]|\d+\.)\s+(.*)$')


def md2tex(md):
    lines = md.split('\n')
    out, para = [], []
    stack = []   # (indent, env)
    i = 0

    def flush():
        if para:
            out.append(inline(' '.join(l.strip() for l in para)))
            out.append('')
            para.clear()

    def close_to(indent):
        while stack and stack[-1][0] >= indent:
            out.append(r'\end{%s}' % stack.pop()[1])

    while i < len(lines):
        line = lines[i]
        if line.strip().startswith('```'):
            flush()
            close_to(0)
            code = []
            i += 1
            while i < len(lines) and not lines[i].strip().startswith('```'):
                code.append(lines[i])
                i += 1
            out.append(r'\begin{verbatim}')
            out.extend(code)
            out.append(r'\end{verbatim}')
            i += 1
            continue
        if line.startswith('|'):
            flush()
            close_to(0)
            rows = []
            while i < len(lines) and lines[i].startswith('|'):
                cells = [c.strip() for c in re.split(r'(?<!\\)\|', lines[i].strip())[1:-1]]
                if not all(re.fullmatch(r':?-+:?', c) for c in cells if c):
                    rows.append(cells)
                i += 1
            if rows:
                head, body = rows[0], rows[1:]
                out.append(r'\begin{itemize}')
                for r in body:
                    parts = [f'{inline(h)}: {inline(c)}' if h else inline(c)
                             for h, c in zip(head, r) if c]
                    out.append(r'\item ' + '; '.join(parts))
                out.append(r'\end{itemize}')
            continue
        h = re.match(r'^#{2,6} (.*)$', line)
        if h:
            flush()
            close_to(0)
            out.append(r'\paragraph{' + inline(h.group(1)) + '}')
            i += 1
            continue
        lm = LIST_RE.match(line)
        if lm:
            flush()
            indent = len(lm.group(1))
            env = 'enumerate' if lm.group(2)[0].isdigit() else 'itemize'
            close_to(indent + 1)
            if not stack or stack[-1][0] < indent:
                out.append(r'\begin{%s}' % env)
                stack.append((indent, env))
            item = [lm.group(3)]
            i += 1
            while i < len(lines) and lines[i].strip() and not LIST_RE.match(lines[i]) \
                    and not lines[i].strip().startswith('```') and \
                    (lines[i].startswith(' ') or not stack):
                item.append(lines[i].strip())
                i += 1
            out.append(r'\item ' + inline(' '.join(item)))
            continue
        if not line.strip():
            flush()
            if stack and (i + 1 >= len(lines) or not lines[i + 1].startswith(' ')) and \
                    not (i + 1 < len(lines) and LIST_RE.match(lines[i + 1])):
                close_to(0)
            i += 1
            continue
        if stack and not line.startswith(' '):
            close_to(0)
        para.append(line)
        i += 1
    flush()
    close_to(0)
    return '\n'.join(out).strip()


# ----------------------------------------------------------------------------------------------
# Output

def lean_cmd(names):
    return r'\lean{' + ', '.join(names) + '}' if names else ''


def uses_cmd(ids, by_id):
    labels = sorted(by_id[i].label for i in ids if i in by_id)
    return r'\uses{' + ', '.join(labels) + '}' if labels else ''


def render_node(n, by_id):
    title = f'{n.id} — {n.title}'
    lines = []
    env = n.env
    lines.append(r'\begin{%s}[%s]' % (env, inline(title)))
    lines.append(r'\label{%s}' % n.label)
    if n.lean:
        lines.append(lean_cmd(n.lean))
    if n.status in ('proved', 'stated'):
        lines.append(r'\leanok')
    u = uses_cmd(n.uses_stmt, by_id)
    if u:
        lines.append(u)
    # The readable statement (node-statements.md) is what the graph's statement panel shows;
    # the blueprint text it summarizes follows as notes (in the proof for theorems).
    notes = ''
    if n.display.strip():
        lines.append(md2tex(n.display))
        if n.statement.strip():
            notes = r'\paragraph{Blueprint notes.}' + '\n' + md2tex(n.statement)
    else:
        lines.append(md2tex(n.statement) or '(See the proof.)')
    lines.append(r'\par\smallskip{\footnotesize Source: %s.}' % esc_text(n.source))
    lines.append(r'\end{%s}' % env)
    if env == 'theorem':
        lines.append(r'\begin{proof}')
        if n.status == 'proved':
            lines.append(r'\leanok')
        u = uses_cmd(n.uses_proof, by_id)
        if u:
            lines.append(u)
        lines.append(md2tex(n.proof) if n.proof.strip() else
                     'See the Lean proof and the cited items.')
        if notes:
            lines.append(notes)
        lines.append(r'\end{proof}')
    elif notes:
        lines.append(notes)
    return '\n'.join(lines)


def parse_display(nodes):
    """Readable statements: `## ID` sections of node-statements.md (hand-written, checked
    against Lean). Text before the first `## ` is a preamble and ignored."""
    if not os.path.exists(DISPLAY):
        return
    by_id = {n.id: n for n in nodes}
    for h, body in sections(read(DISPLAY), 2):
        if not h:
            continue
        nid = h.split()[0]
        if nid in by_id:
            by_id[nid].display = body.strip()
            if ' — ' in h:      # the heading's title overrides the Markdown blueprint's
                by_id[nid].title = h.split(' — ', 1)[1].strip()
        else:
            print(f'DISPLAY   {nid}: section in node-statements.md for an unknown node')


SUMMARY_MACROS = [   # braces: `\simeq\Dperf` must not become `\simeqD_...`
    (r'\cA', r'{\mathcal{A}}'), (r'\Ocal', r'{\mathcal{O}}'), (r'\dbar', r'{\bar\partial}'),
    (r'\Ho', r'{\mathrm{Ho}}'), (r'\Dperf', r'{D_{\mathrm{perf}}}'),
    (r'\Hom', r'{\mathrm{Hom}}'), (r'\X', r'{\mathbb{X}}'), (r'\hc', r'{\check h}'),
    (r'\code', r'\texttt'), (r'\lsub', r'\textsubscript'),
]
SUMMARY_REFS = {'sec:h1': 'chap:Z4', 'sec:h2': 'chap:Z5', 'sec:tr': 'chap:Z2',
                'sec:tw-proof': 'chap:Z3'}


def intro_chapter():
    """Chapter 0 from docs/formalization-summary.tex §1-§2 (B12) plus its bibliography."""
    t = read(SUMMARY)
    body = t[t.index(r'\section{The theorem}'):t.index(r'\section{The proof}')]
    bib = t[t.index(r'\begin{thebibliography}'):t.index(r'\end{thebibliography}') +
            len(r'\end{thebibliography}')]
    for a, b in sorted(SUMMARY_MACROS, key=lambda p: -len(p[0])):
        body = re.sub(re.escape(a) + r'(?![A-Za-z])', lambda _: b, body)
        bib = re.sub(re.escape(a) + r'(?![A-Za-z])', lambda _: b, bib)
    body = body.replace(r'\section{', r'\section*{')
    body = body.replace(r'\section*{The theorem}',
                        r'\chapter{Introduction}\label{chap:intro}' + '\n' + r'\section{The theorem}')
    body = body.replace(r'\section*{', r'\section{')
    body = re.sub(r'\\begin\{lean\}', r'\\begin{verbatim}', body)
    body = re.sub(r'\\end\{lean\}', r'\\end{verbatim}', body)
    body = body.replace('§lsub«l»', 'ₗ')
    for a, b in SUMMARY_REFS.items():
        body = body.replace(r'\ref{%s}' % a, r'\ref{%s}' % b)
    body = re.sub(r'\(K7, \\S\\ref\{sec:k7\}\)', '(K7)', body)
    body = re.sub(r'\\label\{sec:k7\}', '', body)
    for a in ('mathcal', 'mathrm'):
        pass
    return body, bib


def build(nodes, intros):
    os.makedirs(CHAP_DIR, exist_ok=True)
    by_id = {n.id: n for n in nodes}
    files = []
    intro, bib = intro_chapter()
    with open(os.path.join(CHAP_DIR, 'intro.tex'), 'w', encoding='utf-8') as f:
        f.write('% Generated by scripts/blueprint_gen.py from docs/formalization-summary.tex.\n')
        f.write(intro)
    files.append('intro')
    for ch, title in CHAPTERS.items():
        chap_nodes = [n for n in nodes if n.chapter == ch]
        if not chap_nodes:
            continue
        out = ['% Generated by scripts/blueprint_gen.py; do not edit.',
               r'\chapter{%s}\label{chap:%s}' % (inline(title), ch)]
        if intros.get(ch):
            out.append(md2tex(intros[ch]))
        for n in chap_nodes:
            out.append('')
            out.append(render_node(n, by_id))
        fname = 'chap-' + ch.replace('.', '')
        with open(os.path.join(CHAP_DIR, fname + '.tex'), 'w', encoding='utf-8') as f:
            f.write('\n'.join(out) + '\n')
        files.append(fname)
    with open(os.path.join(SRC, 'content.tex'), 'w', encoding='utf-8') as f:
        f.write('% Generated by scripts/blueprint_gen.py; do not edit.\n')
        for fn in files:
            f.write(r'\input{chapters/%s}' % fn + '\n')
        f.write('\n' + bib + '\n')
    print(f'{len(nodes)} nodes in {len(files)} chapter files written to {CHAP_DIR}')


# ----------------------------------------------------------------------------------------------
# Seed and check

def progress_names():
    """node id -> backticked names in its PROGRESS rows, in order (empty without PROGRESS)."""
    out = defaultdict(list)
    if not os.path.exists(PROGRESS):
        return out
    for line in read(PROGRESS).split('\n'):
        if not line.startswith('| '):
            continue
        cells = line.split('|')
        if len(cells) < 5:
            continue
        tok = cells[1].strip().split(' ')[0]
        for name in re.findall(r'`([^`\s]+)`', '|'.join(cells[4:])):
            out[tok].append(name.split('(')[0])
            out[re.sub(r'\d+$', '', tok)].append(name.split('(')[0])
    return out


def seed(nodes, decls, force=False):
    if os.path.exists(LEAN_MAP) and not force:
        print(f'{LEAN_MAP} exists; use --force to overwrite')
        return
    ids = {n.id for n in nodes}
    tg = tagged(decls, ids)
    pn = progress_names()
    lines = ['# Blueprint items → Lean names (documentation plan B10)', '',
             'Curated by the main agent, checked by the human in excerpts. `scripts/blueprint_gen.py` '
             'reads it: "Lean" gives the `\\lean{}` names of each node (fully qualified), '
             '"Extra uses" adds `\\uses` edges, "Drop uses" removes edges that the mention '
             'scan finds in the Markdown text but that are not dependencies (e.g. "replaces S7.a").',
             '', '| Item | Lean | Extra uses | Drop uses |', '| --- | --- | --- | --- |']
    for n in nodes:
        cands = tg.get(n.id, [])
        short = {c.split('.')[-1]: c for c in cands}
        picked = []
        for p in pn.get(n.id, []):
            full = short.get(p.split('.')[-1])
            if full and full in cands and full not in picked:
                picked.append(full)
        if not picked:
            picked = [c for c in cands if decls[c]['k'] not in ('instance',)][:4]
        picked = picked[:6]
        lines.append(f'| {n.id} | ' + ', '.join(f'`{p}`' for p in picked) + ' | | |')
    with open(LEAN_MAP, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines) + '\n')
    print(f'seeded {LEAN_MAP} ({len(nodes)} items)')


def owner_overrides():
    """lean-map.md, section "Owner overrides": | Declaration | Item | Reason |. For declarations
    whose docstring tag names a later item than the first one that uses them (the tag cannot
    always be changed: frozen files)."""
    text = read(LEAN_MAP) if os.path.exists(LEAN_MAP) else ''
    if '## Owner overrides' not in text:
        return {}
    sec = text.split('## Owner overrides', 1)[1]
    out = {}
    for cells in table_rows(sec, r'`'):
        out[cells[0].strip('`')] = cells[1]
    return out


def owners(nodes, decls):
    """Declaration -> item: an owner override, else its docstring tag (the Lean side says where
    a declaration belongs), else lean-map for untagged declarations (e.g. the main statements)."""
    ids = {n.id for n in nodes}
    owner = {}
    for nid, names in tagged(decls, ids).items():
        for d in names:
            owner[d] = nid
    for n in nodes:
        for d in n.lean:
            owner.setdefault(d, n.id)
    for d, nid in owner_overrides().items():
        if nid in ids:
            owner[d] = nid
    return owner


def lean_edges(nodes, decls):
    """Item -> items its tagged declarations depend on, through untagged project constants."""
    owner = owners(nodes, decls)
    edges = defaultdict(set)
    for d, nid in owner.items():
        seen, todo = {d}, list(decls.get(d, {}).get('u', []))
        while todo:
            c = todo.pop()
            if c in seen:
                continue
            seen.add(c)
            o = owner.get(c)
            if o is not None:
                if o != nid:
                    edges[nid].add(o)
                continue
            todo.extend(decls.get(c, {}).get('u', []))
    return edges


def reach(by_id):
    memo = {}

    def go(i, stack=()):
        if i in memo:
            return memo[i]
        if i in stack:
            return set()
        n = by_id[i]
        r = set()
        for j in n.uses_stmt | n.uses_proof:
            r.add(j)
            r |= go(j, stack + (i,))
        memo[i] = r
        return r
    return {i: go(i) for i in by_id}


def check(nodes, decls):
    by_id = {n.id: n for n in nodes}
    bad = 0
    for n in nodes:
        for d in n.lean:
            if d not in decls:
                print(f'MISSING   {n.id}: {d} not a project declaration')
                bad += 1
    ids = set(by_id)
    tg = tagged(decls, ids)
    for n in nodes:
        if n.status and not n.lean:
            print(f'NO-LEAN   {n.id}: status {n.status} but no Lean names in lean-map')
        if not n.display.strip():
            print(f'NO-TEXT   {n.id}: no readable statement in node-statements.md')
    unknown = defaultdict(int)
    for name, r in decls.items():
        if r['p'] or r['i'] or not r['d']:
            continue
        m = TAG_DOC_RE.match(r['d'].strip())
        if m and not node_of_tag(m.group(1), ids) and not m.group(1).startswith('K'):
            unknown[m.group(1)] += 1
    for t, k in sorted(unknown.items()):
        print(f'UNKNOWN-TAG {t}: {k} declarations tagged with an item that is not a node')
    le = lean_edges(nodes, decls)
    r = reach(by_id)
    for i in sorted(le):
        for j in sorted(le[i]):
            if j not in r.get(i, set()) and j not in by_id[i].breaks:
                print(f'B3        {i} -> {j}: Lean dependency not in the Markdown (not even '
                      f'transitively)')
                bad += 1
    for n in nodes:
        for j in sorted(n.uses_stmt | n.uses_proof):
            lean_ok = j in le.get(n.id, set()) or j in reach_lean(le, n.id)
            if not lean_ok:
                print(f'MD-ONLY   {n.id} -> {j}: Markdown edge without Lean dependency')
    cyc = [i for i in by_id if i in r[i]]
    for i in cyc:
        print(f'CYCLE     {i} reaches itself')
    print(f'{len(nodes)} nodes, {sum(len(n.uses_stmt | n.uses_proof) for n in nodes)} edges; '
          f'{bad} errors (MISSING, B3)')
    return bad


def why(nodes, decls, src, dst):
    """Print declaration chains behind the Lean dependency src -> dst (debugging B3)."""
    owner = owners(nodes, decls)
    shown = 0
    for d in [d for d, o in owner.items() if o == src]:
        prev, todo = {d: None}, [d]
        while todo:
            c = todo.pop(0)
            for u in decls.get(c, {}).get('u', []):
                if u in prev:
                    continue
                prev[u] = c
                if owner.get(u) == dst:
                    chain, x = [u], c
                    while x is not None:
                        chain.append(x)
                        x = prev[x]
                    print(' <- '.join(chain))
                    shown += 1
                    todo = []
                    break
                if owner.get(u) is None:
                    todo.append(u)
        if shown >= 5:
            break


def sync(nodes, decls):
    """Lean is the arbiter of dependencies (human, 10 Nov 2026). For each item with Lean code:
    Markdown mentions (and Extra uses) that are not Lean dependencies, even through other items,
    go to "Dropped"; then a minimal set of Lean dependencies that the remaining edges do not give,
    even transitively, goes to "Lean uses". Entries of "Cycle breaks" stay only while they are
    Lean dependencies (otherwise they are simply dropped)."""
    by_id = {n.id: n for n in nodes}      # loaded with ignore_b3=True
    le = lean_edges(nodes, decls)
    has_lean = set(le) | {n.id for n in nodes if n.lean}
    ids = set(by_id)
    owner_items = {o for o in tagged(decls, ids)}
    has_lean |= owner_items
    breaks, dropped = {}, defaultdict(set)
    for n in nodes:
        rl = reach_lean(le, n.id)
        # a break is needed only where Lean itself has a cycle between the two items
        breaks[n.id] = {j for j in n.breaks if j in rl and n.id in reach_lean(le, j)}
        if n.id not in has_lean:
            continue
        for j in list(n.uses_stmt | n.uses_proof):
            if j not in rl:
                dropped[n.id].add(j)
                n.uses_stmt.discard(j)
                n.uses_proof.discard(j)
        for j in breaks[n.id]:
            n.uses_stmt.discard(j)
            n.uses_proof.discard(j)
        n.drop = breaks[n.id] | getattr(n, 'split_children', set())
    base = {i: set(by_id[i].uses_stmt | by_id[i].uses_proof) for i in by_id}
    order, seen = [], set()

    def visit(i, stack=()):
        if i in seen or i in stack:
            return
        for j in sorted(le.get(i, ())):
            visit(j, stack + (i,))
        seen.add(i)
        order.append(i)
    for i in sorted(by_id):
        visit(i)
    added = defaultdict(set)
    memo = {}

    def reach_of(i, stack=()):
        if i in memo:
            return memo[i]
        out = set()
        for j in base[i] | added[i]:
            if j in stack:
                continue
            out.add(j)
            out |= reach_of(j, stack + (i,))
        return out
    skipped = []
    for i in order:          # targets first, so their reach is final
        memo.pop(i, None)
        cur = reach_of(i)
        cands = [j for j in le.get(i, ()) if j not in cur and j not in by_id[i].drop]
        cands.sort(key=lambda j: -len(memo.get(j) or reach_of(j)))
        for j in cands:
            if j in cur:
                continue
            memo.clear()
            if i in reach_of(j):     # the edge would close a cycle: report, do not add
                skipped.append((i, j))
                continue
            added[i].add(j)
            memo.clear()
            cur = reach_of(i)
        memo[i] = cur
    write_auto_columns(nodes, breaks, dropped, added)
    for i, j in skipped:
        print(f'SKIPPED   {i} -> {j}: Lean dependency would close a cycle; add it to "Cycle '
              f'breaks" of one of the two items')
    print(f'{sum(len(v) for v in dropped.values())} Markdown edges dropped, '
          f'{sum(len(v) for v in added.values())} Lean edges added, '
          f'{sum(len(v) for v in breaks.values())} cycle breaks kept, in {LEAN_MAP}')


_lr = {}


def reach_lean(le, i):
    if i in _lr:
        return _lr[i]
    seen, todo = set(), list(le.get(i, ()))
    while todo:
        j = todo.pop()
        if j in seen:
            continue
        seen.add(j)
        todo.extend(le.get(j, ()))
    _lr[i] = seen
    return seen


# ----------------------------------------------------------------------------------------------

def load_nodes(ignore_b3=False):
    nodes, intros = parse_main_blueprint()
    nodes = apply_splits(nodes)
    sub, intros2 = parse_subblueprints()
    nodes += sub
    intros.update(intros2)
    parse_progress(nodes)
    parse_display(nodes)
    lean_map = parse_lean_map()
    if ignore_b3:   # sync recomputes the automatic columns
        lean_map = {k: (a, b, c, [], []) for k, (a, b, c, _, _) in lean_map.items()}
    decls = load_decls() if os.path.exists(DECLS) else {}
    for n in nodes:
        names = lean_map.get(n.id, ([], [], [], [], []))[0]
        n.lean = names
        kinds = [decls[d]['k'] for d in names if d in decls]
        defs = {'def', 'abbrev', 'structure', 'inductive', 'instance', 'opaque'}
        n.env = 'definition' if kinds and all(k in defs for k in kinds) and not n.proof.strip() \
            else 'theorem'
    assign_edges(nodes, lean_map, apply_drops=not ignore_b3)
    return nodes, intros, decls


def status_drift(nodes):
    """Warn where the item tables of PROGRESS (if present) give another status than status.md."""
    if not os.path.exists(PROGRESS):
        return
    shadow = [Node.__new__(Node) for _ in nodes]
    for s, n in zip(shadow, nodes):
        s.id = n.id
    parse_progress(shadow, PROGRESS)
    for s, n in zip(shadow, nodes):
        if s.status is not None and s.status != n.status:
            print(f'STATUS-DRIFT {n.id}: status.md says {n.status}, PROGRESS says {s.status}')


def main(argv):
    if not argv:
        print(__doc__)
        return 1
    cmd = argv[0]
    nodes, intros, decls = load_nodes(ignore_b3=(cmd == 'sync'))
    if cmd == 'nodes':
        for n in nodes:
            print(f'{n.chapter:3} {n.id:7} {n.env:10} {str(n.status):7} {n.title[:50]:50} '
                  f'uses={sorted(n.uses_stmt | n.uses_proof)}')
        print(len(nodes), 'nodes')
    elif cmd == 'dump':
        for n in nodes:
            print(f'===== {n.id} | {n.title} | {n.env} | {n.status} | lean={n.lean}')
            print(n.statement.strip() + '\n')
    elif cmd == 'seed':
        seed(nodes, decls, force='--force' in argv)
    elif cmd == 'build':
        build(nodes, intros)
    elif cmd == 'check':
        status_drift(nodes)
        return 1 if check(nodes, decls) else 0
    elif cmd == 'sync':
        sync(nodes, decls)
    elif cmd == 'why' and len(argv) == 3:
        why(nodes, decls, argv[1], argv[2])
    else:
        print(__doc__)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
