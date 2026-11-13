#!/usr/bin/env python3
"""Definitions behind the statement of the main theorem (review aid, CLAUDE.md "Statement
faithfulness").

Computes, from the compiled Lean environment, every project declaration (module prefix
`Cohesivemodules.`) that the given root constants depend on: the types and, for definitions,
abbreviations, instances and structures, the bodies (proofs of theorems are not followed: they
cannot change the meaning of a statement). Instances the statement uses (e.g. the category
structure on `HoP`) are reached this way. Compiler-generated auxiliary declarations (and recursors,
`casesOn`, …) are followed but not listed.

Freeze rule (blueprint §11 v1.18, conventions §9): exactly the declarations above are frozen.
Other project instances *on* a reached type (an explicit argument of the class has a collected
type former as head, e.g. `HasShift (HoP 𝒜) ℤ`) are listed in a separate, informational section;
they are not followed and not frozen.

Writes a markdown sheet: for each declaration its kind, a link to its source line, the
`-- FROZEN` status of its file, and its docstring; then the Mathlib declarations used directly by
the listed project declarations (names only).

Usage:
  scripts/statement_defs.py [--out review/statement-defs.md] [ROOT ...]
    ROOT: fully qualified constant names. Default: the three statements (STATEMENT_ROOTS) if
    `Cohesive.MainStatement` exists, otherwise the roots that exist so far (see DEFAULT_ROOTS).
"""
import json
import os
import subprocess
import sys
import tempfile

ROOT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Constants the main statement is built from (blueprint §1, conventions §9). Those not yet
# defined are reported as missing.
STATEMENT_ROOTS = [
    'Cohesive.MainStatement', 'Cohesive.MainStatementConditional', 'Cohesive.MainStatementTwisted',
]

DEFAULT_ROOTS = [
    'Cohesive.MainStatement',
    'Cohesive.blockFunctor', 'Cohesive.dolbeault', 'Cohesive.holSheaf',
    'Cohesive.DolbeaultGrothendieck', 'Cohesive.LocalGaugeLemma',
    'Cohesive.HoP', 'Cohesive.Perf',
    # J for general pre-resolving data; `blockFunctor` (F15) will be J for the Dolbeault data.
    'Cohesive.PreResolvingData.J',
]

LEAN = r'''
import Cohesivemodules
open Lean Meta Elab Command

def roots : List Name := [ROOTS]

def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "Cohesivemodules"
  | none => false

def isAux (n : Name) : Bool :=
  n.isInternalDetail || isPrivateName n && (privateToUserName n).isInternalDetail ||
  (match n with
   | .str _ s => s ∈ ["rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "below",
       "brecOn", "binductionOn", "ibelow", "ctorIdx", "ofNat_toCtorIdx"]
   | _ => false)

/-- Constants occurring in the meaning of `n`: its type, and its value unless it is a theorem;
constructors of inductives. -/
def deps (env : Environment) (n : Name) : Array Name := Id.run do
  let some ci := env.find? n | return #[]
  let mut out := ci.type.getUsedConstants
  match ci with
  | .defnInfo d => out := out ++ d.value.getUsedConstants
  | .opaqueInfo d => out := out ++ d.value.getUsedConstants
  | .inductInfo d =>
    for c in d.ctors do
      out := out.push c
  | .ctorInfo d => out := out.push d.induct
  | _ => pure ()
  return out

/-- Indices of the explicit binders of a (class) type. -/
def explicitIdx : Expr → (i : Nat := 0) → List Nat
  | .forallE _ _ b bi, i => (if bi.isExplicit then [i] else []) ++ explicitIdx b (i + 1)
  | _, _ => []

def kindOf (ci : ConstantInfo) (inst : Bool) (struct : Bool) : String :=
  if inst then "instance" else if struct then "structure" else
  match ci with
  | .defnInfo d => if d.hints.isAbbrev then "abbrev" else "def"
  | .thmInfo _ => "theorem"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | _ => "other"

elab "#statementDeps" : command => do
  let env ← getEnv
  let mut missing : Array Name := #[]
  let mut todo : Array Name := #[]
  for r in roots do
    if env.contains r then todo := todo.push r else missing := missing.push r
  let mut seen : NameSet := {}
  let mut mathlib : NameSet := {}
  let mut types : NameSet := {}
  let mut infoInst : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    while h : todo.size > 0 do
      let n := todo.back
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      for m in deps env n do
        if isProject env m then
          unless seen.contains m do todo := todo.push m
        else if !isAux m then
          unless isProject env n && isAux n && false do mathlib := mathlib.insert m
      if let some ci := env.find? n then
        if (← liftTermElabM <| isProp ci.type) == false then
          if ci.type.getForallBody.isSort || ci.type.isSort then types := types.insert n
    -- project instances mentioning a collected type former
    for (n, ci) in env.constants.toList do
      if isProject env n && !seen.contains n && isInstanceCore env n then
        -- instances *on* a collected type: some explicit argument of the class in the
        -- conclusion has a collected type former as head (e.g. `Category (HoP 𝒜)`,
        -- `Linear k (HoP 𝒜)`, `Module _ (Tot 𝒜 Q)`); mentions in binders or implicit
        -- arguments do not count
        let body := ci.type.getForallBody
        let args := body.getAppArgs
        let expl := match body.getAppFn.constName? with
          | some cls => match env.find? cls with
            | some cci => explicitIdx cci.type
            | none => []
          | none => []
        let onType := expl.any fun i => match args[i]? with
          | some a => match a.getAppFn.constName? with
            | some h => types.contains h
            | none => false
          | none => false
        -- v1.18: informational only, not followed (so `changed` stays false)
        if onType then infoInst := infoInst.insert n
  for n in missing do
    logInfo m!"{Json.compress (Json.mkObj [("missing", toJson n.toString)])}"
  for (n, info) in seen.toList.map (·, false) ++ infoInst.toList.map (·, true) do
    if isAux n then continue
    let some ci := env.find? n | continue
    if ci matches .thmInfo _ then continue
    if ci matches .ctorInfo _ then continue
    let inst := isInstanceCore env n
    let struct := isStructure env n
    let rng ← findDeclarationRanges? n
    let line := match rng with | some r => r.range.pos.line | none => 0
    let modName := match env.getModuleIdxFor? n with
      | some idx => (env.header.moduleNames[idx.toNat]!).toString | none => ""
    let doc := (← findDocString? env n).getD ""
    logInfo m!"{Json.compress (Json.mkObj [("name", toJson n.toString),
      ("kind", toJson (kindOf ci inst struct)), ("module", toJson modName),
      ("line", toJson line), ("doc", toJson doc), ("info", toJson info)])}"
  for n in mathlib.toList do
    logInfo m!"{Json.compress (Json.mkObj [("mathlib", toJson n.toString)])}"

#statementDeps
'''


def run_lean(roots):
    src = LEAN.replace('ROOTS', ', '.join('`' + r for r in roots))
    with tempfile.NamedTemporaryFile('w', suffix='.lean', delete=False) as f:
        f.write(src)
        path = f.name
    try:
        out = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT_DIR, capture_output=True,
                             text=True)
    finally:
        os.unlink(path)
    recs, errors = [], []
    for line in (out.stdout + out.stderr).splitlines():
        i = line.find('{"')
        if i >= 0 and ': info:' in line[:i + 1] or line.startswith('{"'):
            try:
                recs.append(json.loads(line[i:]))
                continue
            except json.JSONDecodeError:
                pass
        if 'error' in line:
            errors.append(line)
    if errors and not recs:
        sys.exit('Lean failed:\n' + '\n'.join(errors[:20]))
    return recs


def frozen(path):
    try:
        with open(path) as f:
            return f.readline().startswith('-- FROZEN')
    except OSError:
        return False


def first_para(doc):
    return doc.strip().split('\n\n')[0].replace('\n', ' ')


def main(argv):
    out = os.path.join(ROOT_DIR, 'review', 'statement-defs.md')
    roots = []
    it = iter(argv)
    for a in it:
        if a == '--out':
            out = next(it)
        else:
            roots.append(a)
    if not roots:
        roots = DEFAULT_ROOTS
    recs = run_lean(roots)
    missing = [r['missing'] for r in recs if 'missing' in r]
    if 'Cohesive.MainStatement' not in missing and roots is DEFAULT_ROOTS:
        # The statements exist: list exactly their dependencies (all three roots, CLAUDE.md;
        # renamed 6 Nov 2026, blueprint §11 v1.22).
        roots = list(STATEMENT_ROOTS)
        recs = run_lean(roots)
        missing = [r['missing'] for r in recs if 'missing' in r]
    decls = [r for r in recs if 'name' in r and not r.get('info')]
    info = sorted((r for r in recs if 'name' in r and r.get('info')),
                  key=lambda r: (r['module'], r['line']))
    mathlib = sorted(r['mathlib'] for r in recs if 'mathlib' in r)
    by_mod = {}
    for d in decls:
        by_mod.setdefault(d['module'], []).append(d)
    lines = ['# Definitions behind the statement of the main theorem', '',
             'Generated by `scripts/statement_defs.py` from the compiled environment: every '
             'project declaration that the roots depend on (types, and bodies of definitions; '
             'proofs not followed). Review these for faithfulness; theorems are not listed. '
             'Freeze rule (blueprint §11 v1.18): every file in the main list is frozen; the '
             'instances in the last section are informational and not frozen.', '',
             'Roots: ' + ', '.join('`%s`' % r for r in roots if r not in missing), '']
    if missing:
        lines += ['Roots not defined yet (to be added in later phases): ' +
                  ', '.join('`%s`' % r for r in missing), '']
    lines += ['%d project declarations in %d files; %d Mathlib declarations used directly.' %
              (len(decls), len(by_mod), len(mathlib)), '']
    for mod in sorted(by_mod):
        rel = mod.replace('.', '/') + '.lean'
        fz = ' (FROZEN)' if frozen(os.path.join(ROOT_DIR, rel)) else ''
        lines += ['## `%s`%s' % (rel, fz), '']
        for d in sorted(by_mod[mod], key=lambda d: d['line']):
            link = '../%s#L%d' % (rel, d['line'])
            doc = first_para(d['doc']) if d['doc'] else '**(no docstring)**'
            lines.append('- [`%s`](%s) — %s. %s' % (d['name'], link, d['kind'], doc))
        lines.append('')
    lines += ['## Instances on reached types (informational, not frozen)', '']
    for d in info:
        rel = d['module'].replace('.', '/') + '.lean'
        fz = ' (file FROZEN)' if frozen(os.path.join(ROOT_DIR, rel)) else ''
        lines.append('- [`%s`](../%s#L%d) — %s%s.' % (d['name'], rel, d['line'], rel, fz))
    if not info:
        lines.append('None.')
    lines.append('')
    lines += ['## Mathlib declarations used directly', '',
              ', '.join('`%s`' % m for m in mathlib), '']
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w') as f:
        f.write('\n'.join(lines))
    print('wrote %s (%d declarations, missing roots: %s)' % (out, len(decls),
                                                              ', '.join(missing) or 'none'))


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
