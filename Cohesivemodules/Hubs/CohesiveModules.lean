import Cohesivemodules.Algebra.Connection
import Cohesivemodules.Algebra.Cohesive
import Cohesivemodules.Algebra.Filtration
import Cohesivemodules.Algebra.BaseChange
import Cohesivemodules.Algebra.BaseChangeExt
import Cohesivemodules.Algebra.FromComplexDef
import Cohesivemodules.Algebra.LiftingCone
import Cohesivemodules.Algebra.TotalQuasiIso
import Cohesivemodules.Algebra.BlockBridge

set_option linter.style.header false

/-!
# Cohesive modules and the homotopy category `Ho(P_A)`

This page is an overview of the algebraic layer of the project (blueprint items A1–A13). It
contains no declarations; the links below point to the files where the definitions and theorems
live.

## Overview

Block's theorem compares two categories attached to a compact complex manifold `X`. On the
algebraic side, `A = 𝒜_X(X)` is the Dolbeault algebra of smooth `(0, q)`-forms, a commutative
differential graded algebra, and the category is `Ho(P_A)`, the homotopy category of
*cohesive modules* over `A`. Roughly, a cohesive module is a bounded, finitely generated
projective graded `A⁰`-module `Q` together with a flat `∂̄`-superconnection `𝕏` on `A ⊗_{A⁰} Q`.
The Dolbeault algebra itself is the subject of the *Dolbeault algebra* hub. Of the items A1–A13,
A8 (the homotopy criterion: a closed degree-`0` map is an isomorphism in `Ho(P_A)` iff its
`(0,0)`-component is a homotopy equivalence) is off the critical path and not formalized.

The setting is a `ℤ`-graded `k`-algebra `A` with grading `𝒜 : ℤ → Submodule k A`, bounded in
degrees `0 ≤ q ≤ N`, graded-commutative, with a differential `d` of degree `1`, `d ∘ d = 0`, and
a closed curvature `c ∈ A²` (`Cohesive.GCDga`). ⚠ Block's condition `d² = [c, −]` reduces to
`d² = 0` because we require `A` to be graded-commutative, as [[A][Antweiler], Rem 4.0.4] does
([[B][Block], Def 2.2.1]
does not). Boundedness in `q` is not in the sources' definitions (it holds for the Dolbeault
algebra and is used in A6 and A11), and `k` is any commutative ring (only `ℂ` is used later).

**Why curvature.** The project proves Block's theorem in two forms, and the definitions on this
page serve both.
* *Untwisted* (`Cohesive.MainStatement`; [[B][Block], Thm 4.1.3], [[A][Antweiler], Thm 7.2.20] at
  `h = 0`): `A` is the
  Dolbeault algebra `(𝒜_X(X), ∂̄)`, with `c = 0`, and `Ho(P_A)` is equivalent to perfect complexes
  of `O_X`-modules.
* *Twisted* (`Cohesive.MainStatementTwisted`; [[A][Antweiler], Thm 7.4.3], stated without proof in
  [[B][Block], Thm 4.2.1]): `A` is the curved Dolbeault algebra `(𝒜_X(X), ∂̄, h)` for a
  `∂̄`-closed form
  `h ∈ 𝒜^{0,2}(X)`, with `c = h`. Here `Ho(P_A)` embeds fully faithfully into the derived category
  of `ȟ`-twisted `O_X`-modules, and its essential image is the twisted perfect complexes. `ȟ` is
  the Čech 2-cocycle with values in `O_X^×` of a twist datum `T` for `h` (`Cohesive.TwistData`:
  a finite cover `U_α`, primitives `h⁰_α` of `h|U_α`, gluing units `u_αβ` and `ȟ`); the statement
  holds for every such `T`, and one always exists.

With `c = h ≠ 0` we have `𝕏 ∘ 𝕏 = h·(−)`, so the sheaf `α(M)` attached to a cohesive module is
no longer a complex. On an open `U_α` with `h|U_α = ∂̄h⁰_α`, the gauge change `𝕏 ↦ 𝕏 − h⁰_α`
makes it flat, and these local complexes glue only up to the twist `ȟ`. So
`Cohesive.CohesiveModule`, `Cohesive.HoP`, base change and the lifting theorem are defined and
proved once, for arbitrary curvature. Results that need `c = 0` take it as a hypothesis
`GCDga.c = 0`: A10 (`Cohesive.CohesiveModule.fromComplex` and its adjunction A10.a) and the total
complex of A12 (`Cohesive.totMap_quasiIso`, `Cohesive.lifting_quasiIso`). At `h = 0` the curved
Dolbeault algebra is definitionally the flat one, so the two theorems share their category
`Ho(P_A)`. Everything else on this page holds over an arbitrary (curved) dga.

* A **quasi-cohesive module** (`Cohesive.QuasiCohesive`) is a family of `A⁰`-modules `Q^p`
  (the generators) and an operator `𝕏` of total degree `1` on the total module
  `Tot Q = A ⊗_{A⁰} ⨁_p Q^p` (`Cohesive.Tot`), satisfying the Leibniz rule
  `𝕏(a·m) = da·m + (−1)^{|a|} a·𝕏m` and flatness `𝕏 ∘ 𝕏 = c·(−)`. It is **cohesive**
  (`Cohesive.CohesiveModule`) if only finitely many `Q^p` are nonzero and each is finitely
  generated projective.
* `𝕏` is determined by its restriction to the generators, and splits into components
  `𝕏^j : Q^p → A^j ⊗ Q^{p+1−j}`: `𝕏⁰` is an `A⁰`-linear differential (`Cohesive.QuasiCohesive.X0`),
  `𝕏¹` satisfies the Leibniz rule of a connection (`Cohesive.QuasiCohesive.comp_one_leibniz`;
  connections in general are `Cohesive.Connection`, A2), and the higher `𝕏^j` are `A⁰`-linear.
  Generator data (`Cohesive.GenData`, `Cohesive.QuasiCohesive.ofGenerators`) build a module from
  its restriction to the generators.
* The **Hom complex** `Hom^n(M₁, M₂)` (`Cohesive.Hom`) consists of the `k`-linear maps of degree
  `n` with `φ(a·m) = (−1)^{n|a|} a·φ(m)`, with differential `δφ = 𝕏₂ ∘ φ − (−1)^n φ ∘ 𝕏₁`
  (`Cohesive.δ`), which is Mathlib's sign convention for `CochainComplex.HomComplex.δ`.
* **`Ho(P_A)`** (`Cohesive.HoP`) has cohesive modules as objects and the degree-`0` cohomology
  `H⁰ = Z⁰ / B⁰` of the Hom complex as morphisms (`Cohesive.Z0`, `Cohesive.B0`, `Cohesive.H0`,
  composition `Cohesive.compH0`). It is a `k`-linear preadditive category; its triangulated
  structure is the subject of the *Triangulated structure* hub (Z2).

## Main definitions

* `Cohesive.GCDga`: bounded graded-commutative curved dgas (A1).
* `Cohesive.Connection`: connections on `A⁰`-modules (A2).
* `Cohesive.QuasiCohesive`, `Cohesive.CohesiveModule`: (quasi-)cohesive modules (A3).
* `Cohesive.Hom`, `Cohesive.δ`, `Cohesive.homComplex`: the Hom complex, also as a Mathlib cochain
  complex (A4).
* `Cohesive.HoP`: the homotopy category `Ho(P_A)` (A5).
* `Cohesive.filHom`: the form-degree filtration of the Hom complex (A6).
* `Cohesive.DgaHom`, `Cohesive.CohesiveModule.baseChange`, `Cohesive.bcHoFunctor`: base
  change along maps of (curved) dgas, used to restrict cohesive modules to open sets (A9).
* `Cohesive.CohesiveModule.fromComplex`: the cohesive module `A ⊗_R W`, `𝕏 = d ⊗ 1 + 1 ⊗ d_W`, of
  a bounded complex `W` of finitely generated projective `R`-modules, for a ring map
  `ρ : R → A⁰` with `d ∘ ρ = 0`; ⚠ only for curvature `c = 0` (A10).
* `Cohesive.BlockCohesive`: cohesive modules in Block's own convention, with right modules (A13).

## Main results

* `Cohesive.Connection.exists_connection`: every finitely generated projective `A⁰`-module has a
  connection (A2.a).
* `Cohesive.homEquivGen`: maps of degree `n` are determined by their restriction to generators,
  `Hom^n(M₁, M₂) ≅ ∏_p Hom_{A⁰}(Q₁^p, (A ⊗ Q₂)^{p+n})`, a finite product for cohesive `M₁`
  (A4.c).
* `Cohesive.quasiIso_of_finite_filtration`: a map of finitely filtered complexes that is a
  quasi-isomorphism on every graded piece is a quasi-isomorphism (A7). It replaces the spectral
  sequences of the sources.
* `Cohesive.lifting` (the **lifting theorem**, A11): if each `A^b` is flat over
  `A⁰`, then a quasi-isomorphism from a bounded complex of finitely generated projective
  `A⁰`-modules `(P, ∂)` to `(Q, 𝕏⁰)` lifts to a cohesive structure `𝔼` on `A ⊗ P` with `𝔼⁰ = ∂`
  and the same curvature `c`, and a closed degree-`0` map `e` into the quasi-cohesive module
  `(Q, 𝕏)` whose `(0,0)`-component is the given quasi-isomorphism. If moreover `c = 0` (only then
  is `(Tot, 𝕏)` a complex), the lift is a quasi-isomorphism of total complexes
  (`Cohesive.lifting_quasiIso`, A12); the general form, for any closed degree-`0` map whose
  `(0,0)`-component is a quasi-isomorphism, is `Cohesive.totMap_quasiIso`. This is the step that
  makes the functor `J` essentially surjective onto perfect complexes.
* A13: the left-module definition used here agrees with Block's right-module definition, with
  curvature `c ↔ −c`: a bijection on objects (`Cohesive.BlockQuasiCohesive.toLeft`,
  `Cohesive.QuasiCohesive.toBlock`) and an isomorphism of Hom complexes compatible with `δ` and
  composition (`Cohesive.BlockQuasiCohesive.blockHomEquiv`,
  `Cohesive.BlockQuasiCohesive.blockConj_δ`, `Cohesive.BlockQuasiCohesive.blockConj_comp`). This
  is a sanity check of the conventions, not used by the main theorem.

## Conventions and signs

These are binding for the whole project (`blueprint/conventions.md` §2–§5); `|x|` is the degree
of a homogeneous element.

**The algebra.**
* `A` is internally `ℤ`-graded: a `k`-algebra with `𝒜 : ℤ → Submodule k A` and
  `GradedAlgebra 𝒜`, with `A^q = 0` for `q < 0` and `q > N`. Equalities across degrees are checked
  in `A`, so there are no casts between `𝒜 (m + n)` and `𝒜 (n + m)`. Degrees are written `q + 1`,
  never `q - 1`. Signs are `Int.negOnePow`.
* Graded commutativity: `ab = (−1)^{pq} ba` for `a ∈ A^p`, `b ∈ A^q`. Hence `A⁰` is a commutative
  ring (`Cohesive.GCDga.commRing0`) and `A` an `A⁰`-algebra; tensor products over `A⁰` are
  Mathlib's.
* Leibniz rule: `d(ab) = da·b + (−1)^p a·db` for `a ∈ A^p`; `d ∘ d = 0`; `c ∈ A²` with `dc = 0`.

**Modules.**
* Left modules: the total module is `Tot Q = A ⊗_{A⁰} ⨁_p Q^p`, with `A` acting on the left
  factor; `a ⊗ e` with `a ∈ A^q`, `e ∈ Q^p` has total degree `p + q`.
* Superconnection: `𝕏` is `k`-linear of total degree `1` with
  `𝕏(a·m) = da·m + (−1)^{|a|} a·𝕏m` and flatness `𝕏 ∘ 𝕏 = c·(−)`.
* On generators, `𝕏(1 ⊗ e) = Σ_j 𝕏^j e` with `𝕏^j : Q^p → A^j ⊗ Q^{p+1−j}`. `𝕏⁰` is an
  `A⁰`-linear differential, `𝕏¹` is a connection `𝕏¹(fe) = df ⊗ e + f 𝕏¹e` with no sign, and
  `𝕏^j` for `j ≥ 2` is `A⁰`-linear.

**Maps.**
* `Hom^n(M₁, M₂)`: `k`-linear maps raising total degree by `n` with
  `φ(a·m) = (−1)^{n|a|} a·φ(m)`. Composition is composition of maps, with degrees adding.
* Hom differential: `δφ = 𝕏₂ ∘ φ − (−1)^n φ ∘ 𝕏₁`. This is Mathlib's
  `CochainComplex.HomComplex.δ`, `δz = z ≫ d + (−1)^{n+1} d ≫ z` in diagrammatic order, so
  `δ(ψ ∘ φ) = δψ ∘ φ + (−1)^{|ψ|} ψ ∘ δφ`.
* Extension from generators: a map `ψ : ⨁ Q₁ → Tot Q₂` of degree `n` extends to
  `ψ̂(a ⊗ e) = (−1)^{n|a|} a·ψ(e)`; for `n = 0` there is no sign: `ψ̂(a ⊗ e) = a·ψ(e)`.
* The shift `M[n]` and its signs are part of the triangulated structure (*Triangulated structure*
  hub).

**Translation to the sources.** Block and Antweiler write `𝔼` for the operator called `𝕏` here.

| | Block [[B][Block]] | Antweiler [[A][Antweiler]] | This project |
| --- | --- | --- | --- |
| Modules | right, `Q ⊗_{A⁰} A` | left, `A ⊗_{A⁰} Q` | left |
| `𝔼¹` on `Q^p` | a connection up to `(−1)^p` | the connection `∇` | a connection, no sign |
| Flatness | `𝔼(𝔼x) + x·c = 0` | `𝔼² = h` | `𝕏 ∘ 𝕏 = c·(−)` |
| Curvature | `c` (`B` in [[B][Block], §4.2]) | `h` | `c = −c_Block = h` |

There is no factor `2πi` anywhere. Block's right module `Q ⊗ A` becomes a left module through
`σ : e ⊗ a ↦ (−1)^{|e||a|} a ⊗ e`; `𝔼` is transported along `σ` with no extra sign
(`𝕏 = σ ∘ 𝔼 ∘ σ⁻¹`), and only the sign of the curvature changes, which is invisible at `c = 0`.
A13 proves that this translation is a bijection on objects and an isomorphism of Hom complexes
compatible with `δ` and composition (see Main results).

## Implementation notes

* **Encoding.** A cohesive module is encoded by its operator on the total module (encoding 1 of
  `blueprint/conventions.md` §4), not by generator maps. Generator maps appear through the
  linear equivalence `Cohesive.homEquivGen`.
* **`Tot` is a `def`** with its instances declared once in `Algebra/CohesiveDef.lean`: with an
  `abbrev`, instance search does not find the quotients of submodules of `Tot →ₗ[k] Tot` needed
  for `H⁰`.
* **Objects of `Ho(P_A)`** are cohesive modules wrapped in a structure (`Cohesive.HoP`), so that
  the category instance does not leak onto `CohesiveModule`.
* **Frozen files.** `Algebra/Dga.lean`, `Algebra/CohesiveDef.lean`, `Algebra/GeneratorsDef.lean`,
  `Algebra/GenHomDef.lean`, `Algebra/FromComplexDef.lean` and the base-change definition files
  `Algebra/BaseChangeDef.lean`, `Algebra/BaseChangeHomDef.lean`, `Algebra/BaseChangeResDef.lean`
  (and `Algebra/CurvedDga.lean`, for the twisted statement) enter the main statements and are
  frozen; they hold only definitions and basic API, and the theorems about them are in separate
  files.

## Files

* `Algebra/Dga.lean` (A1), `Algebra/Connection.lean` (A2).
* `Algebra/CohesiveDef.lean`, `Algebra/GeneratorsDef.lean`, `Algebra/Cohesive.lean` (A3–A5),
  `Algebra/GenHomDef.lean` (A4.c).
* `Algebra/Filtration.lean` (A6–A7).
* `Algebra/BaseChange*.lean` (A9, A9.a; the A10.a adjunction is in `BaseChange.lean`;
  `BaseChangeLift.lean` is C7.e), `Algebra/HomAlongT*.lean` (Hom complexes along a dga map, A10.a
  along a map; used by C4).
* `Algebra/FromComplexDef.lean` (A10); `Algebra/TotMap.lean` (C7, algebra part).
* `Algebra/Lifting*.lean`, `Algebra/TotalQuasiIso*.lean` (A11–A12).
* `Algebra/BlockDef.lean`, `Algebra/BlockBridge*.lean` (A13).

## References

* [[B][Block]] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2, §2–§3, Thm 4.1.3; the twisted form in §4.2.
* [[A][Antweiler]] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1, §3, Rem 4.0.4 and §7; the twisted form in §7.4.
* Blueprint: `blueprint/blueprint.md` §2 (items A1–A13); conventions: `blueprint/conventions.md`.
-/
