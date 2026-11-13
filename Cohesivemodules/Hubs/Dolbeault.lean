import Cohesivemodules.Forms.Dolbeault
import Cohesivemodules.ChecksK7

set_option linter.style.header false

/-!
# The Dolbeault algebra and `O_X`

This page is an overview of the layer of `(0, q)`-forms (blueprint items F1–F12, and the check
K7). It contains no declarations; the links below point to the files where the definitions and
theorems live.

## Overview

For a complex manifold `X` modelled on a finite-dimensional complex normed space `E`
(`n = dim_ℂ E`), this layer builds the two objects on which Block's theorem rests: the Dolbeault
algebra `𝒜_X(U)` of smooth `(0, q)`-forms with `∂̄`, a bounded graded-commutative dga in the
sense of the *Cohesive modules* hub (`Cohesive.GCDga`; cohesive modules are taken over
`A = 𝒜_X(X)`, `Cohesive.dolbeault`), and the sheaf `O_X` of holomorphic functions (perfect
complexes are complexes of `O_X`-modules), with the inclusion `ρ : O_X → 𝒜⁰`.
The functor `J` and the assembly of
the theorem are in the *Block's theorem* hub; the analytic hypotheses H1 and H2 on these objects,
and their proofs, are in the *Dolbeault–Grothendieck lemma* and *Local gauge lemma* hubs. The
curved Dolbeault algebra `(𝒜_X(X), ∂̄, h)` (Z3.c) is built on this layer and described in the
*Twisted theorem* hub.

The construction has three stages.
* **Linear algebra at a point (F2, F5).** The fibre `Λ^{0,q}(E; F)` (`Cohesive.DolbeaultFibre`)
  is the space of continuous `ℂ`-alternating maps on the conjugate space `Ē` (`Cohesive.Conj`),
  i.e. real alternating maps on `E` that are antilinear in each slot. The total fibre
  `Λ^{0,•}(E) = Π_{q ≤ n} Λ^{0,q}(E; ℂ)` (`Cohesive.TotFibre`) is a `ℂ`-algebra, with the wedge
  product transported from the exterior algebra `⋀_ℂ (Ē)^*`.
* **Analysis on open sets of `E` (F3–F8).** `∂̄α(x)` (`Cohesive.dbar`) is the alternation of the
  antilinear part of the real derivative of `α : E → Λ^{0,q}(E; F)`. It satisfies `∂̄∂̄ = 0`, the
  Leibniz rule, commutes with holomorphic pullback, and its kernel on functions is the
  holomorphic functions (Cauchy–Riemann).
* **Forms on the manifold (F9–F12).** A form on an open `U ⊆ X` is a function
  `α : U → Λ^{0,•}(E)` whose value at `y` is written in the chart `chartAt E y`, smooth in charts
  (`Cohesive.IsDolbeault`); `∂̄` is computed in charts (`Cohesive.dbarSec`). The forms on `U` are
  a `ℂ`-subalgebra (`Cohesive.dolbeaultSubalgebra`), graded by form degree, and form a dga for
  every `U`, with restriction maps that are maps of dgas.

## Main definitions

* `Cohesive.isManifold_real`, `Cohesive.contMDiffRing_real_complex`: the underlying real
  manifold and the real-smooth ring `ℂ`, theorems used as local instances (F1).
* `Cohesive.Conj`, `Cohesive.Conj.map`, `Cohesive.DolbeaultFibre`, `Cohesive.form0Equiv`,
  `Cohesive.extEquivFibre`: the conjugate space, the fibre `Λ^{0,q}(E; F)`, `Λ^{0,0} ≅ F`, and
  the bridge `Φ_q : ⋀^q_ℂ (Ē)^* ≃ Λ^{0,q}(E; ℂ)`, `φ₁ ∧ ⋯ ∧ φ_q ↦ (v ↦ det (φ_i (v_j)))` (F2).
  `Cohesive.dzbarBasis`: the basis `dz̄_I` (F2.c).
* `Cohesive.antiPart`, `Cohesive.dbarPart`, `Cohesive.dbar`: the antilinear part `L″`, `D″α(x)`
  and `∂̄α(x)` on `E` (F3). `Cohesive.DolbeaultFibre.toReal`: a `(0, q)`-form read as a real form.
* `Cohesive.TotFibre`, `Cohesive.TotFibre.ofDeg`, `Cohesive.TotFibre.deg`,
  `Cohesive.TotFibre.extEquivTotFibre`: the total fibre, its homogeneous components, and
  `Φ_tot : ⋀_ℂ (Ē)^* ≃ Λ^{0,•}(E)` along which the ring structure is transported (F5).
  `Cohesive.wedge`: the wedge product of a `p`- and a `q`-form (F6).
* `Cohesive.DolbeaultFibre.pull`, `Cohesive.TotFibre.pull`, `Cohesive.pullback`: pullback of
  forms along a `ℂ`-linear map at a point, and along a map `G : E → E` (F7).
* `Cohesive.chartTrans`, `Cohesive.chartExpr`, `Cohesive.IsDolbeault`, `Cohesive.dbarTot`,
  `Cohesive.dbarSec`, `Cohesive.IsOfDegree`, `Cohesive.projDeg`, `Cohesive.restrictForm`: forms
  on an open `U ⊆ X`, their chart expressions, the smoothness predicate, `∂̄`, degree and
  restriction (F9; `IsOfDegree` and `projDeg` are F10).
  `Cohesive.dolbeaultLocalPredicate`: the predicate as a
  `TopCat.LocalPredicate`.
* `Cohesive.dolbeaultSubalgebra`, `Cohesive.DolbeaultAlg`, `Cohesive.dolbeaultGrade`,
  `Cohesive.dbarL`: the total algebra `𝒜_X(U)`, its degree-`q` part `𝒜^{0,q}_X(U)`, and `∂̄` as a
  linear map; with these, `𝒜_X(U)` is a `Cohesive.GCDga` (F10).
* `Cohesive.dolbeault`: the Dolbeault algebra `A = 𝒜_X(X)` of the main theorem, as its grading
  `q ↦ 𝒜^{0,q}_X(X)` on `DolbeaultAlg E ⊤` (`dolbeaultGrade E ⊤`), which carries the `GCDga`
  instance (F10).
* `Cohesive.dolbeaultRes`: restriction `𝒜_X(U) → 𝒜_X(V)` as a map of dgas (F10, A9).
* `Cohesive.dolbeault0`: the sheaf of commutative rings `𝒜⁰`, `U ↦ 𝒜^{0,0}_X(U)` (F10).
* `Cohesive.holSheaf`, `Cohesive.holSec`, `Cohesive.funForm`, `Cohesive.dolbeaultRhoU`,
  `Cohesive.dolbeaultRho`: `O_X`, its sections as functions, functions as `0`-forms, and the ring
  map `ρ : O_X → 𝒜⁰` on sections and as a map of sheaves (F12).

## Main results

* `Cohesive.dolbeaultFibre_subsingleton`, `Cohesive.finrank_dolbeaultFibre`:
  `Λ^{0,q} = 0` for `q > n`, and `dim_ℂ Λ^{0,q}(E; ℂ) = C(n, q)` (F2.c).
* `Cohesive.dbar_congr`: `∂̄` is local (F3.b). `Cohesive.dbar_eq_extDeriv`: for `α`
  real-differentiable at `x`, `∂̄α(x)` is the `(0, q+1)`-part of Mathlib's `extDeriv` of `α` read
  as a real form (`Cohesive.DolbeaultFibre.toReal`):
  `∂̄α(x)(v̄) = 2^{-(q+1)} Σ_{S ⊆ {0,…,q}} i^{|S|} dα(x)(J_S v)`, where `v̄` is `v` viewed in `Ē`
  and `J_S` multiplies the slots in `S` by `i` (F3.c).
* `Cohesive.dbar_dbar`: `∂̄∂̄α(x) = 0` for `α` of class `C²` at `x` (F4).
* `Cohesive.TotFibre.ofDeg_mul_comm`: `α ∧ β = (−1)^{pq} β ∧ α`;
  `Cohesive.TotFibre.ofDeg_one_mul`: the Laplace formula
  `φ ∧ β = alternatizeUncurryFin (v ↦ φ(v) • β)`, i.e.
  `(φ ∧ β)(v₀, …, v_q) = Σ_i (−1)^i φ(v_i) β(…, v̂_i, …)`, for a `1`-form `φ`,
  which ties the product to the normalization of `∂̄` (F5, F5.a).
* `Cohesive.dbar_wedge`: `∂̄(α ∧ β) = ∂̄α ∧ β + (−1)^p α ∧ ∂̄β` (F6).
* `Cohesive.dbar_pullback`: `∂̄(G^*α)(x) = G^*(∂̄α)(x)` for `G` complex `C²` at `x` and `α`
  real-differentiable at `G x` (F7.a);
  `Cohesive.TotFibre.pull_mul`: pullback respects products (F7.b).
* `Cohesive.dbar_eq_zero_iff_contDiffOn` (**Cauchy–Riemann**, F8): for `f : E → F` real `C^∞` on
  an open `V`, `∂̄f = 0` on `V` iff `f` is complex `C^∞` on `V`.
* `Cohesive.IsDolbeault.contDiffAt_chartExpr`: a form is smooth in every atlas chart, not only in
  `chartAt` (F9.a). `Cohesive.dbarSec_dbarSec`, `Cohesive.dbarSec_mul`,
  `Cohesive.IsOfDegree.mul_comm`: `∂̄∂̄ = 0`, Leibniz and graded commutativity on `X` (F9.b with
  F4 and F6; graded commutativity is F10 with F5).
* `Cohesive.dolbeault_glue`, `Cohesive.isOfDegree_of_locally`: Dolbeault forms glue uniquely,
  and having degree `q` is local, i.e. `𝒜` and each `𝒜^{0,q}` are sheaves (F10).
* `Cohesive.isFine_dolbeault0`: on a compact Hausdorff `X`, `𝒜⁰` is fine (`Cohesive.IsFine`,
  *Sheaves and perfect complexes* hub), by smooth partitions of unity (F11).
* `Cohesive.dolbeault_locallyFree`: each `𝒜^{0,q}` has local frames of rank `C(n, q)` over `𝒜⁰`
  (`dz̄_I` in a chart): near every point, every form of degree `q` on a smaller open is uniquely
  `Σ_I f_I e_I` with `f_I` of degree `0` (F11).
* `Cohesive.dolbeaultRhoU_injective`, `Cohesive.dbar_dolbeaultRhoU`,
  `Cohesive.exists_dolbeaultRhoU_of_dbar_eq_zero`: `0 → O_X(U) → 𝒜⁰(U) → 𝒜¹(U)` is exact on every
  open `U` (F12, from F8).
* K7 (`Cohesivemodules/ChecksK7.lean`, outside the statement): `Cohesive.tcDelBar_toReal` says
  that a transcription `Cohesive.tcDelBar` of TauCeti's `delBar` (type projections from the
  `J`-derivation `Cohesive.tcDeriv`, `J = i·`, `Cohesive.tcJ`) agrees with `Cohesive.dbar` on
  `(0, q)`-forms read as real forms, at points where `α` is real-differentiable. The
  transcription is pointwise on the model space `E`, with Mathlib's `extDeriv` in place of
  TauCeti's manifold exterior derivative `mextDerivₗ`.
  Steps: `Cohesive.tcIsOfType_toReal` (`toReal α` has type
  `(0, q)`, `Cohesive.tcIsOfType`), `Cohesive.tcDelBar_of_isOfType`,
  `Cohesive.tcTypeProjection_zero_apply` (formula for `π^{0,n}`, `Cohesive.tcTypeProjection`),
  and the example `Cohesive.tcDelBar_conj` (on `E = ℂ`, `tcDelBar` of `z ↦ z̄` is `v ↦ v̄`, i.e.
  `dz̄`). The transcription itself
  (blueprint §6, K7′ (a)) is the part that rests on human review; it was checked in excerpts and approved at gate 13
  (blueprint §11 v1.21).

## Conventions and signs

These are binding for the whole project (`blueprint/conventions.md` §6–§7).

**Spaces, universes, smoothness.**
* `E : Type` and `X : Type`, `E` finite-dimensional over `ℂ`, `n = dim_ℂ E`. The real structure
  of `E` is `NormedSpace.complexToReal`; `J` is multiplication by `i`.
* `X` is a complex manifold: `ChartedSpace E X` and `IsManifold 𝓘(ℂ, E) ∞ X`. The exponent `∞` is
  `C^∞`; `⊤ = ω` (analytic) is never used for smoothness. Forms are real `C^∞` in charts
  (`ContDiffAt ℝ ∞`), holomorphic means complex `C^∞` (`ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞`).
* The underlying real manifold `IsManifold 𝓘(ℝ, E) ∞ X` and `ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ` are
  theorems (`Cohesive.isManifold_real`, `Cohesive.contMDiffRing_real_complex`) used only as
  `attribute [local instance]`, never as global instances; the `ChartedSpace` instance is shared.

**Forms at a point.**
* `Ē = Conj E` is a `def` type synonym of `E` with `c • v := c̄ • v` and the same norm.
  Antilinear maps on `E` are `ℂ`-linear on `Ē`; a `ℂ`-linear `T : E → E` is also `ℂ`-linear on
  `Ē` (`Cohesive.Conj.map`).
* `Λ^{0,q}(E; F) = Conj E [⋀^Fin q]→L[ℂ] F`. Only `F = ℂ` enters the algebra; `F` is general
  where it is free (F2–F4, F7, F8).
* Antilinear part: `L″ v = ½ (L v + i·L(i v))`. On `E = ℂ`, `D″f(1) = ∂f/∂z̄`, and
  `dz̄ = (v ↦ v̄)`.
* `∂̄α(x) = alternatizeUncurryFin (D″α(x))` over `ℂ` on `Ē`
  (`ContinuousAlternatingMap.alternatizeUncurryFin`):
  `∂̄α(x; v₀, …, v_q) = Σ_i (−1)^i D″_{v_i} α(x; …, v̂_i, …)`. No factorials; this is the
  normalization of Mathlib's `extDeriv`.
* Product: transported along `Φ_q : φ₁ ∧ ⋯ ∧ φ_q ↦ (v ↦ det (φ_i (v_j)))`; so for `1`-forms
  `(φ₁ ∧ ⋯ ∧ φ_q)(v) = det (φ_i (v_j))`, the shuffle product without factorials.
  Graded commutativity has sign `(−1)^{pq}`; the Leibniz rule has sign `(−1)^p` for a `p`-form.
* The total fibre is indexed by `Fin (n + 1)`; nothing is lost since `Λ^{0,q} = 0` for `q > n`.
  The degree `q` of a form on `X` is an integer (`IsOfDegree q`, `dolbeaultGrade E U q`), and
  only `0` has degree `q < 0` or `q > n`. Degrees are written `q + 1`, never `q - 1`.

**Forms on `X`.**
* A form `α : U → Λ^{0,•}(E)` has its value at `y` written in `chartAt E y`. Its expression in a
  chart `e` is `z ↦ α(y) ∘ D(chartAt y ∘ e⁻¹)(z)` with `y = e⁻¹ z` (`Cohesive.chartExpr`), junk
  `0` where `e⁻¹ z ∉ U`. `α` is a Dolbeault form if, for each `x ∈ U`, its expression in
  `chartAt E x` is real `C^∞` at `chartAt E x x`. `∂̄α(x)` is `∂̄` of that expression evaluated at
  `chartAt E x x`, and is again written in `chartAt E x`.
* `𝒜_X(U)` is a dga with `N = n`, `d = ∂̄`, curvature `c = 0`; `𝒜^{0,q}_X(U)` is the subtype of
  forms of degree `q` (v1.9), so the `A⁰` of the main theorem is `↥(dolbeault E X 0)` with
  `Cohesive.GCDga.commRing0`, the same type as the global sections of `Cohesive.dolbeault0`
  (`Cohesive.dolbeault0_obj`).
* `O_X = smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ, ℂ) X ℂ` (Mathlib's `smoothSheafCommRing`), and
  `ρ f = f` as a `0`-form; by F8 its image is the kernel of `∂̄ : 𝒜⁰ → 𝒜¹`.

## Implementation notes

* **Junk values.** `Cohesive.dbar` is defined on all functions `E → Λ^{0,q}(E; F)` and is `0`
  where `fderiv` is (at points of non-differentiability). Statements about `∂̄` on `E` carry the
  differentiability they need; on `X`, `∂̄` is applied only to Dolbeault forms, smooth by
  definition. Locality (`Cohesive.dbar_congr`) gives `∂̄` on open subsets.
* **Dependence on `chartAt`** (blueprint §11 v1.18, item 4; `blueprint/conventions.md` §6).
  Because values are written in `chartAt E y`, the carrier `Cohesive.DolbeaultAlg E U` depends on
  the `chartAt` function of the `ChartedSpace` instance, not only on the maximal atlas (the
  sections of Mathlib's `smoothSheaf` are `ContMDiff` functions, a condition invariant under
  change of chart within the maximal atlas).
  F9.a shows the smoothness condition is chart-independent; the theorem is
  quantified over the given instance.
* **`TotFibre` is a `def`**, so that its transported ring structure is not an instance on a bare
  Pi type; the additive structure is the product one, so there is no diamond.
* **Fibres via `Conj E`.** On `Λ^{0,q}` the `ℝ`-structure found by instance search agrees with
  `NormedSpace.complexToReal`; nothing takes `fderiv` on `Conj E` (`D″` is built pointwise from
  the real derivative on `E`).
* **Local freeness** (F11) is stated sectionwise, as a local frame, not as Mathlib's locally
  free sheaf of modules: the pre-resolving data of the comparison ask for exactly this
  sectionwise frame (field `locFrame`, filled by F14, `Cohesive.dolbeaultPreData`). C0 derives the
  module sheaves `𝒜^{0,q}` over `𝒜⁰` from the presheaf of dgas and deduces that they are locally
  direct summands of finite free modules (*Block's theorem* hub).
* **Frozen files.** `Forms/FibreDef.lean`, `Forms/DbarDef.lean`, `Forms/ProductDef.lean`,
  `Forms/PullbackDef.lean`, `Forms/SheafPred.lean`, `Forms/SheafDef.lean` and
  `Forms/Holomorphic.lean` enter the main statement and are frozen (gate 3); the theorems about
  them are in separate files.
* **Non-vacuity.** `Cohesivemodules/ChecksForms.lean` checks on `X = ℂ` that `z̄` is a Dolbeault
  form whose `∂̄`, computed through the charts, is `dz̄` (`Cohesive.Checks.dbarSec_conjForm`); so
  `𝒜¹ ≠ 0`, `z̄` is not in the image of `ρ`, and `𝒜⁰(ℂ)` is a nontrivial ring. The same file
  holds K1 (H1 and H2 in dimension `0`) and K5. `Cohesivemodules/Checks.lean` (K2, K3) checks the
  normalization of `∂̄` and `∧` on `ℂ` and `ℂ²`.

**Deviations from the sources** (⚠ in the blueprint or in the module docstrings).
* ⚠ F2: `Λ^{0,q}` is `Conj E [⋀^Fin q]→L[ℂ] F`, not a subtype of real alternating maps that are
  antilinear in each slot (the same maps).
* ⚠ F5: the product is transported from the exterior algebra, not a hand-built shuffle product
  (whose associativity Mathlib does not have).
* ⚠ F10: forms take values in the total fibre, replacing the direct sum of the `𝒜^{0,q}` of
  [[B][Block], §4] and [[A][Antweiler], §7.1]; the ring axioms then hold pointwise. The sum is
  finite, so they agree.
* ⚠ F8: Cauchy–Riemann is proved by induction on the order of ℂ-linear symmetric derivatives,
  avoiding several-variable Cauchy or Osgood theory, which Mathlib does not have.
* ⚠ F11: fineness needs `X` Hausdorff and compact (for partitions of unity); the sources assume
  `X` compact.
* F2.c: the dimension and the basis `dz̄_I` are stated only for `F = ℂ`. F7: pullback is along
  `G : E → E` with pointwise hypotheses rather than `G : V → V′` (equivalent by locality).
* F5.b (`F`-valued forms as a module over `Λ^{0,•}(E)`) is not built; forms on `X` are
  `ℂ`-valued.

## Files

* `Forms/Realify.lean` (F1).
* `Forms/FibreDef.lean`, `Forms/Fibre.lean` (F2).
* `Forms/DbarDef.lean`, `Forms/Dbar.lean` (F3–F4).
* `Forms/ProductDef.lean`, `Forms/Product.lean` (F5), `Forms/Leibniz.lean` (F6).
* `Forms/PullbackDef.lean`, `Forms/Pullback.lean` (F7), `Forms/CauchyRiemann.lean` (F8).
* `Forms/SheafPred.lean`, `Forms/ChartAuxBasic.lean`, `Forms/ChartAux.lean`,
  `Forms/SheafBasic.lean`, `Forms/Sheaf.lean` (F9).
* `Forms/SheafDef.lean` (F10), `Forms/Holomorphic.lean` (F12).
* `Forms/DolbeaultFine.lean`, `Forms/DolbeaultFree.lean`, `Forms/Dolbeault.lean` (F10 gluing,
  F11, F12 exactness).
* `ChecksK7.lean` (K7).

## References

* [[B][Block]] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2, §4.1.
* [[A][Antweiler]] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1, §7.1.
* TauCeti (`TauCetiProject/TauCeti`, Apache-2.0, not a dependency): `delBar` and type
  projections, transcribed for K7.
* Blueprint: `blueprint/blueprint.md` §5 (items F1–F12), §6 (K7, K7′), §9 (K1–K3);
  conventions: `blueprint/conventions.md` §6–§7.
-/
