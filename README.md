# Block's theorem in Lean: cohesive modules and perfect complexes

A formalization, in Lean 4 and Mathlib, of J. Block's theorem comparing cohesive modules over the
Dolbeault algebra of a compact complex manifold with perfect complexes of holomorphic sheaves
([B, Thm 4.1.3], in the perfect form of [A, Thm 7.2.20]), and of its twisted form [A, Thm 7.4.3].

**Status: complete.** All three main theorems are proved. There is no `sorry`, and the theorems
depend only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. The project
has about 74,000 lines in about 300 files.

## The main results

Throughout, `X` is a compact Hausdorff complex manifold modelled on a finite-dimensional complex
normed space `E`. `A = 𝒜_X(X)` is the Dolbeault algebra of smooth `(0, q)`-forms with `∂̄`, and
`O_X` is the sheaf of holomorphic functions. A *cohesive module* over `A` is a bounded, finitely
generated projective graded `A⁰`-module with a flat `∂̄`-superconnection. `Ho(P_A)` is their
homotopy category.

| Statement (Lean name, file) | Proof | Content |
| --- | --- | --- |
| `Cohesive.MainStatement` (`Cohesivemodules/Statements.lean`) | `main_theorem` | **Block's theorem.** The functor `J : Ho(P_A) ⥤ D(O_X)`, `M ↦ α(M)`, is full and faithful, and its essential image is `D_perf(X, O_X)`. |
| `Cohesive.MainStatementConditional` (`StatementsConditional.lean`) | `main_theorem_conditional` | The same, with the Dolbeault–Grothendieck lemma (H1) and a local gauge lemma (H2) as hypotheses. This was formalized first. Both hypotheses are now theorems, so this is a corollary. |
| `Cohesive.MainStatementTwisted` (`StatementsTwisted.lean`) | `main_theorem_twisted` | **Twisted theorem.** For `∂̄`-closed `h ∈ 𝒜^{0,2}(X)` and a twist datum `T` for `h`, the functor `J_T` from `Ho(P)` of the curved algebra `(𝒜_X(X), ∂̄, h)` to the derived category of `ȟ`-twisted `O_X`-modules is full and faithful, with essential image the twisted perfect complexes. A twist datum exists for every `h`. At `h = 0` the statement gives back Block's theorem. |

The project also proves the triangulated structure on `Ho(P_A)`. It is not used by the statements.

## What to trust

- **The proofs** are checked by the Lean kernel.
- **The statements** are what needs reading. Each statement file imports only Mathlib and
  *frozen* definition files.
  - The definitions the statements depend on were computed by script: 276 declarations in 44
    files.
  - They are listed with their docstrings in `review/statement-defs.md`.
  - They were presented to a human at review gates and **checked in excerpts**. They were then
    marked `-- FROZEN`, and a hook refuses edits to them, so the meaning of the statements could
    not drift while proofs were written.
- **Axioms** are checked inside the build: `#print axioms` under `#guard_msgs` in
  `ChecksMain.lean` and `ChecksTwistedMain.lean`.
- **Non-vacuity and sanity checks** are in the `Checks*.lean` files. Examples:
  - H1 and H2 hold directly in dimension 0, and every definition has a satisfiable instance.
  - `∂̄` is compared with an independent definition transcribed from TauCeti.
  - Dolbeault cohomology is recovered as Hom sets in `Ho(P_A)`.
  - The twisted statement implies the untwisted one.

## Deviations from the sources

- **`D_perf` instead of Block's `D^b_coh`.** Their identification, which needs Oka's coherence
  theorem, is not formalized.
- **"Equivalence onto `D_perf`"** is stated as full, faithful, and essential image equal to
  `D_perf`. The form as an equivalence with the full subcategory is checked separately.
- **Left modules** instead of Block's right modules, so the curvature changes sign:
  `c = −c_Block`.
- **The twisted theorem** is stated for each twist datum.
  - Independence of the datum is not formalized.
  - Antweiler's data `(h⁰, h¹, h², exp)` are replaced by multiplicative data.
- **Errors found in the sources** are listed with their corrections in the audit tables at the
  start of each blueprint file.
  - Examples: a cocycle condition that does not typecheck, a typo `h⁰` for `h¹`, and a shift sign
    valid only for right modules.

## How it was made

The formalization was written with Claude (Anthropic's AI model, used through Claude Code) under
the supervision of Julian Holstein, in about three weeks (October–November 2026). The workflow:

- **Blueprint first.** An informal blueprint with every item, its proof and its deviations from
  the sources came before any Lean.
- **Statements fixed early.** The main statements were written and frozen before the proofs.
- **Gates between phases.** Each phase ended at a human gate with a review sheet generated from
  Lean.
- **Delegated proof work.** Separate agents filled proofs of fixed statements. A snapshot check
  ensured they never changed a statement.
- **External audits.** Fresh model instances audited the blueprint and the code.

The status of every blueprint item is in `blueprint/status.md`.

## Building

The project pins Lean `v4.35.0` (`lean-toolchain`) and Mathlib `v4.35.0` (`lake-manifest.json`).

```sh
lake exe cache get   # Mathlib build cache
lake build           # the whole project; a clean build takes a while
```

The blueprint (web pages with the dependency graph, and PDF) and the API documentation are
generated; how to build them is described in `blueprint/status.md`.

## Repository layout

| Path | Contents |
| --- | --- |
| `Cohesivemodules/` | The Lean library. `Algebra/`: cohesive modules over curved dgas. `Sheaf/`: sheaves of modules, perfect complexes, twisted sheaves. `Forms/`, `Analysis/`: the Dolbeault algebra and the proofs of H1, H2. `Comparison/`: the comparison theorem. `Hubs/`: overview pages. `Checks*.lean`: checks. |
| `Cohesivemodules.lean` | Root module; its docstring is the documentation landing page. |
| `blueprint/` | The informal blueprint (`blueprint.md` and the parts `-tr`, `-dg`, `-ll`, `-tw`), conventions and signs, the source numbering table, the item status (`status.md`), and the leanblueprint sources. |
| `docs/` | `formalization-summary.pdf`: a summary of the statements and the proof strategy. |
| `docbuild/` | Separate Lake project for the doc-gen4 API documentation. |
| `index.html` | Landing page linking the generated documentation. |
| `review/statement-defs.md` | The definitions the main statements depend on, with their docstrings. |
| `scripts/` | Blueprint generator (`blueprint_decls.py`, `blueprint_gen.py`) and the statement-closure script (`statement_defs.py`). |

Some docstrings and blueprint notes refer to working material that is not part of this release:
prototypes in `Scratch/`, the gate review sheets, and working notes (`PROGRESS`).

## References

- [B] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2.
- [A] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1.
- [CHL] J. Chuang, J. Holstein, A. Lazarev, *Maurer–Cartan moduli and theorems of
  Riemann–Hilbert type*, Appl. Categ. Struct. 29 (2021).

## License

Apache License 2.0 (`LICENSE`). Third-party material and attributions: `NOTICE`. It includes code
adapted from TauCeti (Apache 2.0).
