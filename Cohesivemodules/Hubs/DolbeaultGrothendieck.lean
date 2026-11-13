import Cohesivemodules.MainH1
import Cohesivemodules.Statements

set_option linter.style.header false

/-!
# The Dolbeault–Grothendieck lemma H1 and its proof

This page is an overview of the hypothesis H1 of Block's theorem and of its proof (blueprint
items H1 and Z4, Z4.a–Z4.h). It contains no declarations; the links below point to the files
where the definitions and theorems live.

## Overview

The proof of Block's theorem relies on two analytic facts about the complex manifold `X`: H1,
the Dolbeault–Grothendieck lemma, and H2, the local gauge lemma (*Local gauge lemma* hub). The
project first formalized the theorem in a conditional version, with H1 and H2 as hypotheses
(`Cohesive.MainStatementConditional`). Both are `Prop`-valued definitions in `Hypotheses.lean`
(frozen at gate 3), and both are now proved (`Cohesive.dolbeaultGrothendieck`,
`Cohesive.localGaugeLemma`). This hub is about H1.

**What H1 says in Lean.** `Cohesive.DolbeaultGrothendieck E X` is, verbatim,
```
∀ (U : Opens X) (q : ℕ) (x : X), x ∈ U →
  ∀ α ∈ dolbeaultGrade E U ((q : ℤ) + 1), GCDga.d (𝒜 := dolbeaultGrade E U) α = 0 →
    ∃ (U' : Opens X) (h : U' ≤ U), x ∈ U' ∧
      ∃ η ∈ dolbeaultGrade E U' (q : ℤ),
        GCDga.d (𝒜 := dolbeaultGrade E U') η = (dolbeaultRes E h).toAlgHom α
```
Here `Cohesive.dolbeaultGrade E U` is the grading of the Dolbeault algebra `𝒜^{0,•}_X(U)` of
smooth `(0, q)`-forms on `U` (*Dolbeault algebra* hub, F9–F10), `Cohesive.GCDga.d` is its
differential `∂̄`, and `Cohesive.dolbeaultRes` is restriction along `U′ ≤ U`. In words: a
`∂̄`-closed `(0, q+1)`-form on an open `U` is `∂̄`-exact near every point of `U`, with a primitive
of degree `q` on a smaller open `U′ ∋ x`. Nothing is said about the size of `U′`.
Together with F12 (`ρ : O_X → 𝒜⁰_X` is
injective, and its image is the `∂̄`-closed functions) this says exactly that the Dolbeault complex
`O_X → 𝒜^{0,0}_X → 𝒜^{0,1}_X → ⋯` is a resolution of sheaves.

**What is proved.** `Cohesive.dolbeaultGrothendieck : DolbeaultGrothendieck E X` (Z4.g) holds on
every complex manifold `X` modelled on a finite-dimensional `E`
(`IsManifold 𝓘(ℂ, E) ∞ X`), with no compactness or Hausdorff assumption. It comes from a flat
lemma on open subsets of `E` (Z4.e, `Cohesive.exists_dbar_eq`): for an open `U ⊆ E`, `x ∈ U` and
`β : E → Λ^{0,q+1}(E)` that is real `C^∞` on `U` with `∂̄β = 0` on `U`, there are an open `U′`
with `x ∈ U′ ⊆ U` and `η : E → Λ^{0,q}(E)`, real `C^∞` on all of `E`, with `∂̄η = β` on `U′`.
Here `Λ^{0,q}(E) = Cohesive.DolbeaultFibre E q ℂ` is the space of `ℂ`-linear alternating maps on
`Ē = Conj E`. This is the local (germ) form of the `∂̄`-Poincaré lemma; it is not the statement
that `∂̄` is solvable on a whole polydisc or ball, and no estimates are proved here. Smoothness is
always real (`ContDiff ℝ`, never `ℂ`): forms are `C^∞` (`ContDiff ℝ ∞`, `ContDiffOn ℝ ∞`), and
the one-variable results need only `C¹`.

**How it is used.** In `Cohesive.dolbeaultData` (F14, C0.b) H1 is the field `exactq` of
`Cohesive.ResolvingData`, and `Cohesive.ResolvingData.quasiIso_ρhat` turns it, with F12, into
the quasi-isomorphism `O_X → 𝒜^•_X` used by the comparison (*Block's theorem* hub). The twisted
theorem (*Twisted theorem* hub) uses H1 through `Cohesive.dolbeaultData` in the same way. In
addition, `Forms/TwistCover.lean` applies `Cohesive.dolbeaultGrothendieck` directly to closed
forms of degree 2 and 1 (`q = 1` and `q = 0`) to show that every `∂̄`-closed `h ∈ 𝒜^{0,2}(X)` has
a twist datum (`Cohesive.exists_twistData`, which makes the twisted statement non-vacuous): it
writes `h` locally as `∂̄h⁰_α` and finds primitives `η_αβ` of `h⁰_β − h⁰_α`, from which `ȟ` is
built (`Forms/TwistFromPrimitives.lean`).

**Proof in brief** ([Hörmander][Hormander1990], Thm 2.3.3;
[Griffiths–Harris][GriffithsHarris1978], p. 25; details in
`blueprint/blueprint-dg.md` with its audit). One complex variable: the Cauchy transform solves
`∂̄u = h` for compactly supported `C¹` `h` (Cauchy–Pompeiu, Z4.b). With parameters: the solver
along the complex lines `z + ℂv` (Z4.c). Several variables: induction on the number of basis
directions that the closed form `β` involves (Z4.d–Z4.e). If `β` involves only
`dz̄_0, …, dz̄_k`, the step contracts `β` with `conjBasis E k`, cuts the contraction off, solves
along `e_k`, and subtracts `∂̄` of the solution `G`; near `x`, `β − ∂̄G` then involves only
`dz̄_0, …, dz̄_{k−1}`. On `X`:
write `α` in the chart `chartAt E x`, solve there, and carry the primitive back as a Dolbeault
form (Z4.f–Z4.g).

## Main definitions

* `Cohesive.DolbeaultGrothendieck`: the hypothesis H1 (frozen).
* `Cohesive.cauchyTransform`: `cauchyTransform h w = π⁻¹ ∫ t⁻¹ • h (w − t) dA(t)` on `ℂ` (Z4.b).
* `Cohesive.cauchySolve`: the parametric solver
  `cauchySolve v F z = π⁻¹ ∫_ℂ t⁻¹ • F (z − t • v) dA(t)` on `E` (Z4.c).
* `Cohesive.ctr`: contraction `Λ^{0,q+1} → Λ^{0,q}` with a vector `v ∈ Ē`, Mathlib's
  `curryLeft` (Z4.d).
* `Cohesive.InvolvesOnly`: `a` involves only `dz̄_0, …, dz̄_{k−1}` relative to a basis of `Ē`
  (Z4.d).
* `Cohesive.conjBasis`: the basis `Module.finBasis ℂ E`, viewed in `Ē` (Z4.e).
* `Cohesive.chartOpen`, `Cohesive.chartForm`: the form on
  `(chartAt E x).source ∩ (chartAt E x)⁻¹' W` whose expression in `chartAt E x` is a given flat
  form `η` on `W ⊆ (chartAt E x).target`; it is a Dolbeault form when `η` is `C^∞` on `W` (Z4.f).
* `Cohesive.flatExpr`: the degree-`r` component of the expression of a form in `chartAt E x`
  (Z4.g).

## Main results

* `Cohesive.locallyIntegrable_inv_complex`: `t ↦ t⁻¹` is locally integrable on `ℂ` (Z4.a).
* `Cohesive.dbar_cauchyTransform`: for `h` compactly supported and `C¹` with values in a complex
  Banach space, `½ (Du(w) 1 + i Du(w) i) = h w` for `u = cauchyTransform h` (Z4.b).
* `Cohesive.contDiff_cauchySolve`, `Cohesive.hasFDerivAt_cauchySolve`,
  `Cohesive.map_cauchySolve`, `Cohesive.dbar_cauchySolve` (Z4.c), for `v ≠ 0` and compactly
  supported `F`: the solver is `C^∞` if `F` is; for `C¹` `F` its derivative is the solver of
  `DF` and `½ (Du(z) v + i Du(z)(i v)) = F z`; and it commutes with continuous `ℂ`-linear maps
  (`F` continuous).
* `Cohesive.ctr_dbar`: `ι_v ∂̄ω(z) = D″ω(z)(v) − ∂̄(ι_v ω)(z)` for `ω` of degree `q + 1`
  differentiable at `z`, and `Cohesive.ctr_dbar_zero`: `ι_v ∂̄ω = D″_v ω` in degree 0;
  `Cohesive.dbarPart_eq_zero_of_dbar_eq_zero`: a closed form involving only the first `k`
  directions is holomorphic in the directions `j ≥ k` (Z4.d).
* `Cohesive.exists_cutoff`, `Cohesive.exists_step`, `Cohesive.exists_dbar_eq_of_involvesOnly`:
  cutoff, induction step and induction of the flat lemma (Z4.e).
* `Cohesive.exists_dbar_eq`: the flat Dolbeault–Grothendieck lemma on open subsets of `E` (Z4.e).
* `Cohesive.chartExpr_chartForm`, `Cohesive.isDolbeault_chartForm`,
  `Cohesive.isOfDegree_chartForm`, `Cohesive.chartExpr_dbarSec_chartForm`,
  `Cohesive.eq_of_chartExpr_eq`: `chartForm η` is a Dolbeault form of degree `q` with expression
  `η` and `∂̄`-expression `∂̄η`, and a form is determined by its chart expression (Z4.f).
* `Cohesive.dolbeaultGrothendieck`: **H1 holds** on every complex manifold (Z4.g).
* `Cohesive.blockPerf_of_localGaugeLemma`, `main_theorem_of_localGaugeLemma`: Block's theorem
  with H1 discharged, assuming only H2 (Z4.h). Superseded by the unconditional `main_theorem` now
  that H2 is proved (*Block's theorem* and *Local gauge lemma* hubs), but kept.
* Trivial cases, in `Hypotheses.lean` next to H1: `Cohesive.dolbeaultGrothendieck_of_lt` (the
  conclusion of H1 for a form of degree `q + 1 > dim_ℂ E`, which is `0`; check K5) and
  `Cohesive.dolbeaultGrothendieck_of_finrank_eq_zero` (H1 when `dim_ℂ E = 0`; check K1).

## Conventions and signs

Binding conventions are in `blueprint/conventions.md` §6 and blueprint §11 v1.14 item 3.

**Smoothness and junk values.**
* Forms on open subsets of `E` are real `C^∞`, written `ContDiff ℝ ∞` / `ContDiffOn ℝ ∞ · U`
  (`∞`, never `⊤`, which means analytic). `X` is `IsManifold 𝓘(ℂ, E) ∞ X`.
* `Cohesive.dbar` uses `fderiv`, which is `0` where the form is not differentiable. So
  `Cohesive.exists_dbar_eq` assumes `ContDiffOn ℝ ∞ β U` and closedness only on `U`, and
  concludes `dbar η z = β z` only for `z ∈ U′`. On `X` the issue does not arise: sections of
  `dolbeaultGrade` are smooth by construction.

**Normalisation of `∂̄`.**
* Antilinear part of an `ℝ`-linear `L : E → G`: `L″ v = ½ (L v + i L (i v))`
  (`Cohesive.antiPart`), a `ℂ`-linear map on `Ē = Conj E`; on `E = ℂ`, `D″f(1) = ∂f/∂z̄`.
* `D″ω(z) = antiPart (fderiv ℝ ω z)` (`Cohesive.dbarPart`), and `∂̄ω(z)` is
  `alternatizeUncurryFin (D″ω(z))`, `∂̄ω(z; v₀, …, v_q) = Σ_i (−1)^i D″_{v_i}ω(z; …, v̂_i, …)`,
  without factorials (Mathlib's `extDeriv` normalisation).
* `∂̄` along `v` is `D″ω(z)(v)`, i.e. `½ (D_v + i D_{iv})`; the solver theorems
  (`Cohesive.dbar_cauchyTransform`, `Cohesive.dbar_cauchySolve`) are stated in this form.
* The Cauchy transform is `π⁻¹ ∫ t⁻¹ h(w − t) dA(t)`, twice TauCeti's `(2π)⁻¹`-transform
  (`Cohesive.cauchyTransform_eq`); TauCeti's results are stated for
  `Du(w) 1 + i Du(w) i = 2∂̄u`, and the factor 2 is converted in `Cohesive.dbar_cauchyTransform`.

**Coordinates.**
* No coordinates `Fin n → ℂ`: `E` is any finite-dimensional complex normed space, with basis
  `e = Module.finBasis ℂ E`; `Cohesive.conjBasis E` is the same vectors in `Ē`, and
  `∂̄_j = D″(·)(conjBasis E j)`. `dz̄_j` is the dual basis.
* Contraction acts on the first slot: `(ctr v a)(w) = a(v, w)`.
* On `X`, a form `ω` has `ω(y)` written in `chartAt E y` (F9). `Cohesive.chartForm` pulls `η`
  back along the transition `chartAt E x ∘ (chartAt E y)⁻¹`, so that its expression in
  `chartAt E x` is `η`. The expression `chartExpr E α φ` of a form `α` on `U` in a chart `φ` is
  meaningful only on `φ.target ∩ φ.symm⁻¹' U` (elsewhere it is a junk value).

## Implementation notes

* **H1 is a `def`, not an axiom.** It stays a hypothesis of the frozen
  `Cohesive.MainStatementConditional`; `Cohesive.dolbeaultGrothendieck` is a theorem about it. The
  proof `main_theorem : Cohesive.MainStatement` (`MainH2.lean`, *Block's theorem* hub) applies it
  to discharge H1.
* **Global cutoff** (audit S2). The cutoff is applied before solving, so the solver acts on
  functions compactly supported on all of `E` and every statement of Z4.c is global; the cutoff
  is constant in the directions `e_j`, `j ≠ k`, on a slab stable under `z ↦ z − t e_k`, so that
  near `x` the solution stays holomorphic in the directions `e_j`, `j > k`, in which the
  contraction of `β` is holomorphic.
* **No chart transport.** The full chart transport F13 (an isomorphism of presheaves of dgas)
  stays LATER; Z4.f builds only the chart forms that Z4.g needs.
* The induction step of Z4.e splits on `q = 0` and `q ≥ 1` (audit B.2), because the solution `G`
  has degree `q`: for `q = 0` contractions of `G` are undefined and the step uses
  `Cohesive.ctr_dbar_zero`, with no `∂̄(ι_v G)` term; for `q ≥ 1` it uses `Cohesive.ctr_dbar`.
* The phase-7 proof of H2 (*Local gauge lemma* hub) reuses the parametric solver and the Z4.e
  cutoff lemmas (`Analysis/CauchySolveDeriv.lean`, `Analysis/KernelEstimate.lean` are Z5 items).
* **Deviations from the sources.**
  ⚠ H1 is stated on `X`, not on open subsets of `E` (keeps F13 off the critical path; the
  standard sheaf-theoretic form of the lemma). The flat lemma is proved for any
  finite-dimensional `E` instead of `Fin n → ℂ` with polydiscs, with the cutoff applied before
  solving and `η` smooth on all of `E` (audit S2, S3), and the solver works along any direction
  `v ≠ 0`.
* **Attribution.** Z4.b is a port of TauCeti `Pompeiu.lean` (Apache License 2.0; attribution
  paragraph in the module docstring of `Analysis/Pompeiu.lean`); Z4.a replaces TauCeti's
  kernel file by Mathlib's `MeasureTheory.locallyIntegrable_of_norm_le_rpow`.

## Files

* `Hypotheses.lean` (H1 and its trivial cases; frozen).
* `Analysis/CauchyKernel.lean` (Z4.a), `Analysis/Pompeiu.lean` (Z4.b),
  `Analysis/CauchySolve.lean` (Z4.c).
* `Forms/Contraction.lean` (Z4.d), `Forms/FlatGrothendieck.lean` (Z4.e),
  `Forms/ChartForm.lean` (Z4.f), `Forms/DolbeaultGrothendieck.lean` (Z4.g).
* `MainH1.lean` (Z4.h); axiom checks in `ChecksMain.lean`; `ChecksForms.lean` (checks K1, K5).

## References

* [[B][Block]] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2, §4.1.
* [[A][Antweiler]] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1, §7.1.
* [L. Hörmander][Hormander1990], *An introduction to complex analysis in several variables*,
  Thms 1.2.1–1.2.2 and 2.3.3; [P. Griffiths, J. Harris][GriffithsHarris1978], *Principles of
  algebraic geometry*, p. 25.
* TauCeti, `TauCeti/Analysis/Complex/Pompeiu.lean`, with helper lemmas from
  `TauCeti/MeasureTheory/Integral/IntegralEqImproper.lean` and
  `TauCeti/LinearAlgebra/Complex/Module.lean` (branch `main`, fetched 1 Nov 2026; Apache License
  2.0).
* Blueprint: `blueprint/blueprint.md` H1 (§5), Z4 (§6) and §11 v1.14; `blueprint/blueprint-dg.md`
  with its audit; conventions: `blueprint/conventions.md` §6.
-/
