# Documentation plan: doc-gen4 API docs and blueprint graph

Decided 6 Nov 2026, to be carried out after the maths is complete (Z2.g and the Z2 gate).
Nothing here changes the mathematics, the statements or any FROZEN file.

## 1. doc-gen4 (API documentation)

| # | Decision | Status |
| --- | --- | --- |
| D1 | Separate `docbuild/` sub-project (doc-gen4 README layout). The main `lakefile.toml`, `lake-manifest.json` and `lean-toolchain` stay untouched. | decided |
| D2 | doc-gen4 version: the tag matching our toolchain (Lean v4.35.0), not `main`. | decided |
| D3 | Output: a local-only HTML folder first; publish on GitHub Pages later (needs a push, ask first). | decided |
| D4 | Scope: the whole `Cohesivemodules` lib, including the `Checks*` files. `Scratch/` is not in the lib, so it is excluded automatically. | decided |
| D5 | Docstring math stays as it is (Unicode plus backticks); no mass edit. Mass edits would also touch FROZEN files. | decided |
| D6 | Higher-level explanations go in **hub modules** `Cohesivemodules/Hubs/*.lean`, one per mathematical unit (our files are too short to be the unit). A hub imports the unit's files and holds one Mathlib-style module docstring (like `Mathlib/Algebra/Homology/DerivedCategory/Basic`) and no declarations, with sections: Overview, Main definitions, Main results, **Conventions and signs** (stated explicitly, not only cited; own section when there are many), Implementation notes, Files, References. Links use fully qualified names (`Cohesive.…`); every linked name is checked with a `#check` probe. Hubs are imported from `Cohesivemodules.lean`. Per-file docstrings stay short and local. | decided (6 Nov 2026; sample hub 1 approved) |
| D7 | Hubs: (1) cohesive modules and Ho(P_A), A1–A13 (`Hubs/CohesiveModules.lean`, done); (2) triangulated structure, Z2 and K4, including the shift signs; (3) sheaves and perfect complexes, S1–S11; (4) Dolbeault algebra and O_X, F1–F12 and K7; (5) the functor J and Block's theorem, C0–C6, F14–F15, with `MainStatement`; (6) H1, Z4; (7) H2, Z5; (8) the twisted theorem, Z3, with `MainStatementTwisted`; (9) overview: the root `Cohesivemodules.lean` module docstring, with the three statements, how 1–8 depend on each other, and links to the hubs. | decided |
| D8 | Mathematical narrative (proof strategy) belongs in the blueprint chapters (leanblueprint); hubs describe what was built and how to use it. A landing page links "Blueprint" and "API docs". | decided |

### Notes from the doc-gen4 README (checked 6 Nov 2026)

- **Scope cannot be limited.** `lake build Cohesivemodules:docs` documents the library *and every
  module it imports* (all of Mathlib it reaches), plus `Lean`, `Init`, `Lake` and `Std` always.
  - The README has no option to restrict output to our own modules.
  - It also has no option to link to the online Mathlib docs instead of generating them.
  - Consequence: the first run is long and memory-heavy. On this machine (16 GB) run it overnight
    with nothing else running (no VS Code Lean server, no agents).
  - Later runs reuse the build artefacts.
- **`docbuild/lakefile.toml`** (from the README; library name filled in):
  ```toml
  name = "docbuild"
  reservoir = false
  version = "0.1.0"
  packagesDir = "../.lake/packages"

  [[require]]
  scope = "leanprover"
  name = "doc-gen4"
  rev = "v4.35.0"   # the tag matching lean-toolchain; check that it exists

  [[require]]
  name = "cohesivemodules"
  path = "../"
  ```
  Then, inside `docbuild/`, run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4`.
- **Risk: shared package checkout.** `packagesDir = "../.lake/packages"` shares the package checkout with the
  main project.
  - The update must not move Mathlib or any other shared package away from the versions pinned in
    the main `lake-manifest.json`.
  - Before and after the update, compare `docbuild/lake-manifest.json` with the main manifest for
    every shared package. Run `lake build` in the main project afterwards.
  - If a version would move, stop and ask.
- **Requirement.** The library must build, which is the same requirement as for committing.
- **Output** goes to `docbuild/.lake/build/doc/index.html`. It must be served over HTTP, because opening the
  files directly (`file://`) breaks search and navigation (same-origin policy):
  `cd docbuild/.lake/build/doc && python3 -m http.server`, then open `http://localhost:8000`.
  `DOCGEN_SRC=file` makes the source links point at local files (the default is GitHub links).
- **Publishing later.**
  - Commit `docbuild/lakefile.toml` and `docbuild/lake-manifest.json`, but not the output; add
    `docbuild/.lake/` to `.gitignore`.
  - For GitHub Pages, a CI workflow can build and deploy the HTML; CI also avoids the local memory
    limit.
  - Alternatively, push the generated folder to a `gh-pages` branch.
  - Either way this needs a push and a public repo or a Pages plan: ask first.

## 2. Blueprint dependency graph

| # | Decision | Status |
| --- | --- | --- |
| B1 | Tool: Massot's leanblueprint package alone (LaTeX plus plasTeX, `\lean{}`, `\leanok`, `\uses{}`, links into the doc-gen4 pages); no LeanArchitect and no annotations in the Lean files. | decided |
| B2 | Source of truth: the Markdown blueprints (`blueprint.md`, `-ll`, `-tw`, `-tr`, `-dg`) stay authoritative. A script generates the leanblueprint LaTeX from them, from `PROGRESS.md` (statuses) and from a mapping table of items to Lean names. | decided (B2 follows from B3) |
| B3 | Edges (`\uses{}`) come from the Markdown blueprints (the informal dependencies). A script checks them against the actual Lean term dependencies (as `scripts/statement_defs.py` computes them) and flags any Lean dependency between items that the Markdown does not mention. | decided |
| B4 | The checks (blueprint §9, `Checks*.lean`) are documented in doc-gen4 (D4) but left out of the blueprint graph. | decided |
| B5 | Granularity: one node per blueprint item (A1…, S1…, C0…, F1…, H1–H2, Z2.a…, Z3.a…, Z4/Z5…, K…), with `\lean{}` naming its main declarations. | decided |
| B6 | Status colours from `blueprint/status.md` (until 13 Nov 2026 from the item tables of `PROGRESS.md`, which is not published): todo → not formalized; stated → statement formalized (`\leanok` on the statement); proved → proved. Items with blueprint status HYP or LATER are not shown. | decided |
| B7 | One graph with chapters per sub-blueprint, roots `MainStatement`, `MainStatementConditional` and `MainStatementTwisted` (names since v1.22). | decided |
| B8 | `checkdecls` (leanblueprint) runs at each gate, next to `scripts/review.py`, so every `\lean{}` name exists. | decided |
| B9 | Prerequisites: Python with plasTeX and leanblueprint, Graphviz, and a TeX distribution if the PDF is wanted. Local first; CI together with D3. All wanted, PDF included. Installed (6 Nov 2026): TeX (MacTeX:
`pdflatex`, `xelatex`, `latexmk`) and Homebrew. Missing: Graphviz and pipx. Install with
`brew install graphviz pipx`, then
`CFLAGS="-I$(brew --prefix graphviz)/include" LDFLAGS="-L$(brew --prefix graphviz)/lib" pipx install leanblueprint`
(this pulls in plasTeX, plastexdepgraph and pygraphviz; the flags let pygraphviz find Graphviz). | decided |

Order: Z2 done and Z2 gate → doc-gen4 (D1–D5) → blueprint generator script and graph (B1–B9).

### Additions (decided by the human, 10 Nov 2026)

| # | Decision | Status |
| --- | --- | --- |
| B6′ | H1 and H2 are shown as proved statement nodes (proved by Z4.g and Z5.i, used by C0/F14), although `blueprint.md` still tags them HYP. B6's rule hides only items that are still LATER. | decided |
| B10 | Lean names: the generator seeds, per item, the public declarations whose docstring starts with the item's bold tag (`**A9**`, `**Z3.v.**`). The main agent picks the main declarations per item into a committed table `blueprint/lean-map.md` (human-reviewed); later runs flag tagged declarations missing from it. | decided |
| B11 | Node text: the full Markdown item (statement, proof, sub-items, Lean notes, ⚠ deviations), converted to LaTeX. Items listed in the tables of a sub-blueprint get the table row plus the proof sections it cites (e.g. blueprint-tw §3 A.2–A.4). | decided |
| B3′ | Lean is the arbiter of dependencies (replaces the "edges from the Markdown" part of B3). The Markdown mentions propose edges; for items with Lean code, `sync` keeps a mention only if it is a Lean dependency (possibly through other items) and adds the missing Lean dependencies, transitively reduced. A declaration belongs to the item of its docstring tag (lean-map only for untagged ones). Manual entries only for Lean cycles between items ("Cycle breaks", currently none) and "Owner overrides" (declarations whose tag names a later item than the first user; the three cycles S5/S9, F9/F10, C5/C7 had this cause). CLAUDE.md: tags name the earliest item; `check` at every gate. Items without Lean code keep their Markdown edges. `checkdecls` (B8) is not used: `blueprint_gen.py check` verifies the names against the declaration dump. | decided (human, 10 Nov 2026) |
| B13 | Not-needed open sub-items get a node of their own (generator `SPLITS`), so that they do not block the "fully proved" colour: A3.b beyond degree 0 is node A3.b′. | decided (human, 10 Nov 2026) |
| B12 | Layout: generated LaTeX in `blueprint/src/` (leanblueprint templates filled in by hand, not with `leanblueprint new`, which edits the lakefile). Opening chapter from `docs/formalization-summary.tex` §1–§2. `checkdecls` (B8) needs a `require` in `docbuild/lakefile.toml`: ask before adding it. | decided |
| B14 | Readable node statements (human, 10 Nov 2026: "make sure the [node] gives a precise, readable statement, the existing text is often cryptic"). Hand-written `blueprint/node-statements.md`, one `## ID` section per node, checked against the Lean declarations of the node; it is the statement shown on the node (graph panel, chapter page). The Markdown blueprint text stays authoritative and unedited, is printed below as "Blueprint notes" (inside the proof for theorems), and still drives the edges. `check` reports nodes without a section (`NO-TEXT`). The heading's title (`## ID — Title`) is the node's title. The legend of the graph gets two extra entries (dashed arrow: used in the statement; solid arrow: used only in the proof) from `blueprint/src/legend.js`. Amends B11. | decided |
