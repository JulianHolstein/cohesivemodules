import Cohesivemodules.Analysis.CauchyKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

set_option linter.style.header false

/-!
# Z4.b: the one-variable `∂̄`-equation (Cauchy–Pompeiu)

Blueprint item Z4.b (§11, v1.14). For a compactly supported `C¹` map `h : ℂ → F` into a complex
Banach space, the Cauchy transform `cauchyTransform h w = π⁻¹ ∫ t⁻¹ • h (w - t)` solves
`∂̄ u = h`, where `∂̄ u (w) = ½ (Du(w) 1 + i Du(w) i)` (the normalization of F3, conventions §6).

Proof (Hörmander, Thms 1.2.1–1.2.2): the Cauchy–Pompeiu formula
`u w = (2π)⁻¹ ∫ (w - z)⁻¹ • (Du(z) 1 + i Du(z) i)` by polar coordinates about `w` (the angular term
integrates to zero over each circle, the radial term to `-u w` along each ray); the derivative of
the transform is the transform of the derivative (Mathlib's convolution derivative); together they
give the converse.

## Attribution
Adapted from TauCeti (Apache License 2.0; "Copyright (c) 2026 The Tau Ceti contributors"):
`TauCeti/Analysis/Complex/Pompeiu.lean`, the lemma `HasCompactSupport.integral_Ioi_fderiv_apply_ray`
of `TauCeti/MeasureTheory/Integral/IntegralEqImproper.lean`, and
`LinearMap.apply_eq_re_smul_one_add_im_smul_I`, `LinearMap.conj_smul_apply_one_add_I_smul_apply_I`
of `TauCeti/LinearAlgebra/Complex/Module.lean` (branch `main`, fetched 1 Nov 2026).
Modified: module syntax removed; names moved into `Cohesive`; local integrability of the kernel
from Mathlib (Z4.a) instead of TauCeti's `CauchyKernel.lean`; `cauchyTransform` and
`dbar_cauchyTransform` (our normalization) added.

## Deviations
* None from the mathematics; TauCeti's `D = 2∂̄` and `(2π)⁻¹` transform are kept internally and
  converted in `dbar_cauchyTransform`.
-/

open MeasureTheory Complex Set Filter ComplexConjugate
open scoped Real Topology Convolution

namespace Cohesive

/-! ## Helpers (adapted from TauCeti `Module.lean`, `IntegralEqImproper.lean`) -/

/-- Z4.b helper. A real-linear map out of `ℂ` evaluated in the real basis `(1, i)`. -/
theorem apply_eq_re_smul_one_add_im_smul_I {F : Type*} [AddCommMonoid F] [Module ℝ F]
    (L : ℂ →ₗ[ℝ] F) (z : ℂ) : L z = z.re • L 1 + z.im • L Complex.I := by
  calc
    L z = L (z.re • (1 : ℂ) + z.im • Complex.I) :=
      congrArg L (by simp [Complex.real_smul])
    _ = _ := by simp only [map_add, map_smul]

/-- Z4.b helper. For a real-linear `L : ℂ → F`, `e ↦ L e + i L(i e)` is conjugate-linear:
`conj e • (L 1 + i L i) = L e + i L(i e)`. -/
theorem conj_smul_apply_one_add_I_smul_apply_I {F : Type*} [AddCommGroup F] [Module ℂ F]
    (L : ℂ →ₗ[ℝ] F) (e : ℂ) :
    conj e • (L 1 + I • L I) = L e + I • L (I * e) := by
  have hL (z : ℂ) : L z = (z.re : ℂ) • L 1 + (z.im : ℂ) • L I := by
    simpa only [Complex.coe_smul] using apply_eq_re_smul_one_add_im_smul_I L z
  have he : conj e = (e.re : ℂ) - e.im * I := by
    apply Complex.ext <;> simp
  rw [hL e, hL (I * e), he]
  simp only [mul_re, I_re, I_im, mul_im, zero_mul, one_mul, zero_sub, zero_add, ofReal_neg]
  match_scalars
  · ring
  · linear_combination -(e.im : ℂ) * I_sq

/-- Z4.b helper. Integrating the derivative of a compactly supported `C¹` map `u` along the ray
from `w` in a nonzero direction `e` gives `-u w`. -/
theorem integral_Ioi_fderiv_apply_ray {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {u : E → F}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) (w : E) {e : E} (he : e ≠ 0) :
    ∫ r in Ioi (0 : ℝ), fderiv ℝ u (w + r • e) e = -u w := by
  have hline : HasCompactSupport fun r : ℝ => u (w + r • e) :=
    hc.comp_isClosedEmbedding
      ((Homeomorph.addLeft w).isClosedEmbedding.comp (isClosedEmbedding_smul_left he))
  have hderiv : ∀ r : ℝ, deriv (fun r : ℝ => u (w + r • e)) r = fderiv ℝ u (w + r • e) e :=
    fun r => by
      have h : HasDerivAt (fun r : ℝ => w + r • e) e r := by
        simpa using ((hasDerivAt_id r).smul_const e).const_add w
      exact (((hu.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt r h).deriv
  have h := hline.integral_Ioi_deriv_eq (f := fun r : ℝ => u (w + r • e))
    (hu.comp (by fun_prop : ContDiff ℝ 1 fun r : ℝ => w + r • e)) 0
  simpa only [hderiv, zero_smul, add_zero] using h

/-! ## The Cauchy–Pompeiu formula (adapted from TauCeti `Pompeiu.lean`) -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

section Polar

/-- The unit vector `e^{iθ}`, written as in `Complex.polarCoord_symm_apply`. -/
private noncomputable abbrev expI (θ : ℝ) : ℂ := Real.cos θ + Real.sin θ * I

private lemma norm_expI (θ : ℝ) : ‖expI θ‖ = 1 := by
  simpa only [expI, ← ofReal_cos, ← ofReal_sin] using Complex.norm_cos_add_sin_mul_I θ

private lemma hasDerivAt_expI (θ : ℝ) : HasDerivAt expI (I * expI θ) θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp
  simp only [id_eq, ofReal_one, one_mul, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin] at h
  exact h.congr_deriv (mul_comm _ _)

/-- In polar coordinates `(r, θ)` about `w`, `r • (r e^{iθ})⁻¹ • (L 1 + I • L I)` is
`L e^{iθ} + I • L (I e^{iθ})`. -/
private lemma smul_polarCoord_symm_inv_smul {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace ℂ G] (L : ℂ →L[ℝ] G) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    r • ((Complex.polarCoord.symm (r, θ))⁻¹ • (L 1 + I • L I)) =
      L (expI θ) + I • L (I * expI θ) := by
  have hinv : (r : ℂ) * ((r : ℂ) * expI θ)⁻¹ = conj (expI θ) := by
    calc
      (r : ℂ) * ((r : ℂ) * expI θ)⁻¹ = (expI θ)⁻¹ := by field_simp [ofReal_ne_zero.2 hr]
      _ = conj (expI θ) := Complex.inv_eq_conj (norm_expI θ)
  rw [Complex.polarCoord_symm_apply, ← Complex.coe_smul, smul_smul, hinv]
  simpa only [ContinuousLinearMap.coe_coe] using
    conj_smul_apply_one_add_I_smul_apply_I L.toLinearMap _

variable {u : ℂ → F}

/-- The derivative of a compactly supported `C¹` map, in polar coordinates about `w` and applied
to a continuous direction, is integrable over `polarCoord.target`. -/
private lemma integrableOn_polarCoord_target_fderiv (hc : HasCompactSupport u)
    (hu : ContDiff ℝ 1 u) (w : ℂ) {v : ℝ → ℂ} (hv : Continuous v) :
    IntegrableOn (fun p : ℝ × ℝ => fderiv ℝ u (w + p.1 * expI p.2) (v p.2))
      polarCoord.target := by
  obtain ⟨R, -, hR⟩ := ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft w)).exists_pos_le_norm
  have hcont : Continuous fun p : ℝ × ℝ => fderiv ℝ u (w + p.1 * expI p.2) (v p.2) :=
    ((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (hv.comp continuous_snd)
  refine (hcont.continuousOn.integrableOn_compact
    ((isCompact_Icc (a := 0) (b := R)).prod (isCompact_Icc (a := -π) (b := π))))
    |>.of_forall_sdiff_eq_zero (polarCoord_target ▸ measurableSet_Ioi.prod measurableSet_Ioo) ?_
  rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hK⟩
  have hRr : R ≤ ‖r * expI θ‖ := by
    rw [norm_mul, norm_expI, mul_one, norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    by_contra h
    exact hK ⟨⟨le_of_lt hr, (not_le.1 h).le⟩, ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩⟩
  have := hR _ hRr
  simp only [Function.comp_apply, Homeomorph.coe_addLeft] at this
  simp [this]

variable [CompleteSpace F]

/-- Integrating the angular derivative of a `C¹` map around a circle about `w` gives zero. -/
private lemma integral_Ioo_fderiv_apply_circle (hu : ContDiff ℝ 1 u) (w : ℂ) {r : ℝ}
    (hr : r ≠ 0) :
    ∫ θ in Ioo (-π) π, fderiv ℝ u (w + r * expI θ) (I * expI θ) = 0 := by
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => u (w + r * expI θ))
      (r • fderiv ℝ u (w + r * expI θ) (I * expI θ)) θ := fun θ => by
    have h : HasDerivAt (fun θ : ℝ => w + r * expI θ) (r * (I * expI θ)) θ :=
      ((hasDerivAt_expI θ).const_mul (r : ℂ)).const_add w
    have hsm : fderiv ℝ u (w + r * expI θ) ((r : ℂ) * (I * expI θ)) =
        r • fderiv ℝ u (w + r * expI θ) (I * expI θ) := by
      rw [← map_smul, real_smul]
    exact hsm ▸ ((hu.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt θ h
  have hcont : Continuous fun θ : ℝ => r • fderiv ℝ u (w + r * expI θ) (I * expI θ) :=
    (((hu.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply
      (by fun_prop)).const_smul r
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    (hcont.intervalIntegrable (-π) π)
  have hends : expI π = expI (-π) := by simp [expI]
  rw [hends, sub_self, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo, integral_smul] at hFTC
  exact (smul_eq_zero.1 hFTC).resolve_left hr

end Polar

variable [CompleteSpace F]

/-- **Z4.b (Cauchy–Pompeiu formula).** [Hörmander, Thm 1.2.1]. A compactly supported `C¹` map
`u : ℂ → F` is the Cauchy transform of `Du(z) 1 + i Du(z) i = 2∂̄u(z)`:
`u w = (2π)⁻¹ ∫ (w - z)⁻¹ • (Du(z) 1 + i Du(z) i)`, the integral over the whole plane. -/
theorem two_pi_inv_smul_integral_sub_inv_smul_fderiv {u : ℂ → F}
    (hc : HasCompactSupport u) (hu : ContDiff ℝ 1 u) (w : ℂ) :
    (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • (fderiv ℝ u z 1 + I • fderiv ℝ u z I) = u w := by
  set G : ℂ → F := fun z => fderiv ℝ u z 1 + I • fderiv ℝ u z I with hG
  have hcentre : ∫ z, (w - z)⁻¹ • G z = -∫ z, z⁻¹ • G (w + z) := by
    rw [← integral_neg, ← integral_add_left_eq_self (fun z => (w - z)⁻¹ • G z) w]
    congr 1 with z
    rw [sub_add_cancel_left, inv_neg, neg_smul]
  rw [hcentre, ← Complex.integral_comp_polarCoord_symm]
  set A : ℝ × ℝ → F := fun p => fderiv ℝ u (w + p.1 * expI p.2) (expI p.2) with hA
  set B : ℝ × ℝ → F := fun p => fderiv ℝ u (w + p.1 * expI p.2) (I * expI p.2) with hB
  have hmeas : MeasurableSet (polarCoord.target) := by
    rw [polarCoord_target]
    exact measurableSet_Ioi.prod measurableSet_Ioo
  have hAB : EqOn (fun p : ℝ × ℝ => p.1 • ((Complex.polarCoord.symm p)⁻¹ •
      G (w + Complex.polarCoord.symm p))) (fun p => A p + I • B p) polarCoord.target := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have h := smul_polarCoord_symm_inv_smul (fderiv ℝ u (w + Complex.polarCoord.symm (r, θ)))
      (ne_of_gt hr) θ
    simp only [Complex.polarCoord_symm_apply, hA, hB, hG] at h ⊢
    exact h
  have hAi : IntegrableOn A polarCoord.target :=
    integrableOn_polarCoord_target_fderiv hc hu w (v := expI) (by fun_prop)
  have hBi : IntegrableOn B polarCoord.target :=
    integrableOn_polarCoord_target_fderiv hc hu w (v := fun θ => I * expI θ) (by fun_prop)
  have hprod : (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
    rw [polarCoord_target, Measure.volume_eq_prod, Measure.prod_restrict]
  have hAval : ∫ p in polarCoord.target, A p = -((2 * π) • u w) := by
    rw [hprod, integral_prod_symm _ (by rw [← hprod]; exact hAi)]
    simp only [hA]
    rw [setIntegral_congr_fun measurableSet_Ioo fun θ _ => by
      simpa only [real_smul] using integral_Ioi_fderiv_apply_ray hc hu w
        (e := expI θ) (norm_ne_zero_iff.1 (by rw [norm_expI]; exact one_ne_zero))]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_neg]
    ring_nf
  have hBval : ∫ p in polarCoord.target, B p = 0 := by
    rw [hprod, integral_prod _ (by rw [← hprod]; exact hBi)]
    refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
    exact integral_Ioo_fderiv_apply_circle hu w (ne_of_gt hr)
  rw [setIntegral_congr_fun hmeas hAB,
    integral_add (g := fun p => I • B p) hAi (hBi.smul I), integral_smul, hAval, hBval]
  simp only [smul_zero, add_zero, neg_neg, ← Complex.coe_smul, smul_smul]
  push_cast
  field_simp [Real.pi_ne_zero]
  simp

omit [CompleteSpace F] in
/-- **Z4.b.** The transform `w ↦ ∫ (w - z)⁻¹ • f z` of a compactly supported `C¹` map is
differentiable, with derivative the transform of the derivative. -/
theorem hasFDerivAt_integral_sub_inv_smul {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    HasFDerivAt (fun w => ∫ z, (w - z)⁻¹ • f z) (∫ z, (w - z)⁻¹ • fderiv ℝ f z) w := by
  convert hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℂ)
    locallyIntegrable_inv_complex hf w using 1
  · funext z
    simp only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply]
  · rw [convolution_eq_swap]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ext v
    simp

/-- **Z4.b (converse).** [Hörmander, Thm 1.2.2]. For a compactly supported `C¹` map `f`,
`T f w = (2π)⁻¹ ∫ (w - z)⁻¹ • f z` satisfies `D(Tf)(w) 1 + i D(Tf)(w) i = f w` (`2∂̄ (T f) = f`). -/
theorem fderiv_two_pi_inv_smul_integral_sub_inv_smul {f : ℂ → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ 1 f) (w : ℂ) :
    fderiv ℝ (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) w 1 +
      I • fderiv ℝ (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z) w I = f w := by
  have hk : Integrable fun t => t⁻¹ • fderiv ℝ f (w - t) :=
    locallyIntegrable_inv_complex.integrable_smul_right_of_hasCompactSupport
      ((hf.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id))
      ((hc.fderiv ℝ).comp_homeomorph (Homeomorph.subLeft w))
  have hintL : Integrable fun z => (w - z)⁻¹ • fderiv ℝ f z := by
    simpa only [sub_sub_cancel] using hk.comp_sub_left w
  have hint (v : ℂ) : Integrable fun z => (w - z)⁻¹ • fderiv ℝ f z v := by
    simpa only [smul_apply] using hintL.apply_continuousLinearMap v
  have hT : HasFDerivAt (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • f z)
      ((2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • fderiv ℝ f z) w :=
    (hasFDerivAt_integral_sub_inv_smul hc hf w).const_smul _
  rw [hT.fderiv]
  simp only [smul_apply, ContinuousLinearMap.integral_apply hintL]
  rw [smul_comm I, ← smul_add, ← integral_smul,
    ← integral_add (g := fun z => I • (w - z)⁻¹ • fderiv ℝ f z I) (hint 1) ((hint I).smul I)]
  conv_rhs =>
    rw [← two_pi_inv_smul_integral_sub_inv_smul_fderiv hc hf w]
  congr 2 with z
  rw [smul_add, smul_comm I]

/-! ## Our normalization -/

/-- **Z4.b.** The Cauchy transform in the normalization of the project:
`cauchyTransform h w = π⁻¹ ∫ t⁻¹ • h (w - t)` (twice TauCeti's `(2π)⁻¹`-transform). -/
noncomputable def cauchyTransform (h : ℂ → F) (w : ℂ) : F :=
  (π⁻¹ : ℂ) • ∫ t : ℂ, t⁻¹ • h (w - t)

omit [CompleteSpace F] in
/-- Z4.b: `cauchyTransform h` is twice TauCeti's transform `(2π)⁻¹ ∫ (w - z)⁻¹ • h z`
(substitution `z = w - t`). -/
theorem cauchyTransform_eq (h : ℂ → F) :
    cauchyTransform h = fun w => (2 : ℂ) • ((2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • h z) := by
  funext w
  have hsub : ∫ t : ℂ, t⁻¹ • h (w - t) = ∫ z, (w - z)⁻¹ • h z := by
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self (fun z => (w - z)⁻¹ • h z) (μ := volume) w
  rw [cauchyTransform, hsub, smul_smul]
  congr 1
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]

/-- **Z4.b (one-variable `∂̄`-equation).** [Hörmander, Thm 1.2.2], [B, §4.1]. For a compactly
supported `C¹` map `h : ℂ → F` into a complex Banach space, `u = cauchyTransform h` satisfies
`∂̄u = h`: `½ (Du(w) 1 + i Du(w) i) = h w` for every `w` (the `antiPart` normalization of F3). -/
theorem dbar_cauchyTransform {h : ℂ → F} (hc : HasCompactSupport h) (hh : ContDiff ℝ 1 h)
    (w : ℂ) :
    (2 : ℂ)⁻¹ • (fderiv ℝ (cauchyTransform h) w 1 + I • fderiv ℝ (cauchyTransform h) w I) =
      h w := by
  have hT : HasFDerivAt (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • h z)
      (fderiv ℝ (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • h z) w) w :=
    ((hasFDerivAt_integral_sub_inv_smul hc hh w).const_smul _).differentiableAt.hasFDerivAt
  have hT2 : HasFDerivAt (fun w => (2 : ℂ) • ((2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • h z))
      ((2 : ℂ) • fderiv ℝ (fun w => (2 * π : ℂ)⁻¹ • ∫ z, (w - z)⁻¹ • h z) w) w :=
    hT.const_smul (2 : ℂ)
  rw [cauchyTransform_eq, hT2.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply]
  rw [smul_comm I (2 : ℂ), ← smul_add, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  exact fderiv_two_pi_inv_smul_integral_sub_inv_smul hc hh w

end Cohesive
