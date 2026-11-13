import Cohesivemodules.Analysis.Pompeiu
import Mathlib.Analysis.Normed.Module.HahnBanach

set_option linter.style.header false

/-!
# Z4.c: the parametric one-variable `∂̄`-solver

Blueprint item Z4.c (§11, v1.14; audit of `blueprint/blueprint-dg.md`, simplification S2). For a
finite-dimensional complex `E`, a direction `v ≠ 0` and a smooth compactly supported
`F : E → Λ` (Λ a complex Banach space),
`cauchySolve v F z = π⁻¹ ∫_ℂ t⁻¹ • F (z - t • v) dA(t)`
is the one-variable Cauchy transform (Z4.b) along the complex lines `z + ℂ v`, with `z` as
parameter. Results:
* (i) `contDiff_cauchySolve`: `cauchySolve v F` is `C^∞` on all of `E`;
  `hasFDerivAt_cauchySolve`: its derivative is the solver of the derivative of `F`.
* (ii) `map_cauchySolve`: it commutes with continuous `ℂ`-linear maps.
* (iii) `dbar_cauchySolve`: `½ (D(cauchySolve v F)(z) v + i D(cauchySolve v F)(z) (i v)) = F z`,
  i.e. `∂̄` along `v` (F3 normalization) of the solver is `F`.

## Deviations
* blueprint-dg's solver has a cutoff in the `k`-th variable only and lives on a polydisc; here the
  cutoff is applied beforehand (Z4.e), so `F` is compactly supported on all of `E` and every
  statement is global (audit S2). `v` is any nonzero vector, not a coordinate vector.
-/

open MeasureTheory Complex Set Filter
open scoped Real Topology Convolution ContDiff

namespace Cohesive

variable {E Λ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] [CompleteSpace Λ]

/-- **Z4.c.** [Hörmander, Thm 2.3.3 (proof)], [Griffiths–Harris, p. 25]. The parametric Cauchy
transform along the direction `v`: `cauchySolve v F z = π⁻¹ ∫ t⁻¹ • F (z - t • v)` over `t ∈ ℂ`.
For `F` smooth with compact support and `v ≠ 0` it solves `∂̄_v u = F` (`dbar_cauchySolve`). -/
noncomputable def cauchySolve (v : E) (F : E → Λ) (z : E) : Λ :=
  (π⁻¹ : ℂ) • ∫ t : ℂ, t⁻¹ • F (z - t • v)

/-- Z4.c: the family on the complex lines through `z` in direction `v`, in the absolute coordinate
given by a functional `ℓ` (with `ℓ v = 1` in use). -/
def lineFam (ℓ : E →L[ℂ] ℂ) (v : E) (F : E → Λ) (z : E) (ζ : ℂ) : Λ :=
  F (z + (ζ - ℓ z) • v)

omit [FiniteDimensional ℂ E] [CompleteSpace Λ] in
/-- Z4.c: the solver as a Mathlib convolution with a parameter, evaluated at `ℓ z`. -/
theorem cauchySolve_eq_convolution (ℓ : E →L[ℂ] ℂ) (v : E) (F : E → Λ) (z : E) :
    cauchySolve v F z = (π⁻¹ : ℂ) •
      ((fun t : ℂ => t⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] lineFam ℓ v F z) (ℓ z) := by
  unfold cauchySolve
  congr 1
  rw [convolution_def]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [lineFam, ContinuousLinearMap.lsmul_apply, sub_sub_cancel_left, neg_smul,
    ← sub_eq_add_neg]

omit [FiniteDimensional ℂ E] in
/-- Z4.c: a continuous `ℂ`-linear functional with `ℓ v = 1` (Hahn–Banach),for `v ≠ 0`. -/
theorem exists_clm_apply_eq_one (v : E) (hv : v ≠ 0) : ∃ ℓ : E →L[ℂ] ℂ, ℓ v = 1 := by
  obtain ⟨g, -, hg⟩ := exists_dual_vector ℂ v (norm_ne_zero_iff.2 hv)
  have h0 : g v ≠ 0 := by rw [hg]; simpa using hv
  exact ⟨(g v)⁻¹ • g, by simp [h0]⟩

omit [FiniteDimensional ℂ E] [CompleteSpace Λ] in
/-- **Z4.c (i).** For `v ≠ 0` and `F` smooth with compact support, the solver is `C^∞` on `E`
(Mathlib's `contDiffOn_convolution_right_with_param_comp`, kernel `t⁻¹` locally integrable by
Z4.a). -/
theorem contDiff_cauchySolve {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) : ContDiff ℝ ∞ (cauchySolve v F) := by
  obtain ⟨ℓ, hℓ⟩ := exists_clm_apply_eq_one v hv
  have hk : IsCompact (ℓ '' tsupport F) := hc.isCompact.image ℓ.continuous
  have hgs : ∀ p : E, ∀ ζ : ℂ, p ∈ (univ : Set E) → ζ ∉ ℓ '' tsupport F →
      lineFam ℓ v F p ζ = 0 := by
    intro p ζ _ hζ
    by_contra h
    apply hζ
    refine ⟨p + (ζ - ℓ p) • v, subset_tsupport _ h, ?_⟩
    simp [hℓ]
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (↿(lineFam ℓ v F)) (univ ×ˢ univ) := by
    refine ContDiff.contDiffOn ?_
    have hl : ContDiff ℝ ∞ (ℓ.restrictScalars ℝ) := (ℓ.restrictScalars ℝ).contDiff
    unfold lineFam
    exact hF.comp (contDiff_fst.add ((contDiff_snd.sub (hl.comp contDiff_fst)).smul
      contDiff_const))
  have h := contDiffOn_convolution_right_with_param_comp (μ := volume) (n := ⊤)
    (ContinuousLinearMap.lsmul ℝ ℂ) (v := fun z : E => ℓ z)
    ((ℓ.restrictScalars ℝ).contDiff.contDiffOn) isOpen_univ hk hgs locallyIntegrable_inv_complex hg
  have h2 : ContDiff ℝ ∞ fun z : E => ((fun t : ℂ => t⁻¹) ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume]
      lineFam ℓ v F z) (ℓ z) := contDiffOn_univ.1 h
  have h3 := h2.const_smul (π⁻¹ : ℂ)
  convert h3 using 1
  funext z
  exact cauchySolve_eq_convolution ℓ v F z

omit [FiniteDimensional ℂ E] [CompleteSpace Λ] in
/-- Z4.c: for `v ≠ 0` and `F` continuous with compact support, the integrand
`t ↦ t⁻¹ • F (z - t • v)` is integrable (kernel locally integrable, `t ↦ F (z - t • v)`
continuous with compact support). -/
theorem integrable_cauchySolve {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : Continuous F)
    (hc : HasCompactSupport F) (z : E) : Integrable fun t : ℂ => t⁻¹ • F (z - t • v) := by
  have hemb : Topology.IsClosedEmbedding fun t : ℂ => z - t • v :=
    (Homeomorph.subLeft z).isClosedEmbedding.comp (isClosedEmbedding_smul_left hv)
  exact locallyIntegrable_inv_complex.integrable_smul_right_of_hasCompactSupport
    (hF.comp hemb.continuous) (hc.comp_isClosedEmbedding hemb)

omit [FiniteDimensional ℂ E] in
/-- **Z4.c (ii).** The solver commutes with continuous `ℂ`-linear maps:
`L (cauchySolve v F z) = cauchySolve v (L ∘ F) z` (`ContinuousLinearMap.integral_comp_comm`).
So every closed subspace that is the kernel of such maps (`InvolvesOnly`, Z4.d) is preserved. -/
theorem map_cauchySolve {Λ' : Type} [NormedAddCommGroup Λ'] [NormedSpace ℂ Λ']
    [CompleteSpace Λ'] (L : Λ →L[ℂ] Λ') {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : Continuous F)
    (hc : HasCompactSupport F) (z : E) :
    L (cauchySolve v F z) = cauchySolve v (fun y => L (F y)) z := by
  unfold cauchySolve
  rw [map_smul, ← L.integral_comp_comm (integrable_cauchySolve hv hF hc z)]
  simp only [map_smul]

omit [FiniteDimensional ℂ E] [CompleteSpace Λ] in
/-- **Z4.c (i′).** For `v ≠ 0` and `F` of class `C¹` with compact support, the derivative of the
solver at `z` is the solver of the derivative of `F`:
`D(cauchySolve v F)(z) = cauchySolve v (DF) z` (differentiation under the integral). -/
theorem hasFDerivAt_cauchySolve {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (z : E) :
    HasFDerivAt (cauchySolve v F) (cauchySolve v (fderiv ℝ F) z) z := by
  have hF1 : Continuous F := hF.continuous
  have hD : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hDc : HasCompactSupport (fderiv ℝ F) := hc.fderiv ℝ
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : E)
  obtain ⟨C, hC⟩ := hD.bounded_above_of_compact_support hDc
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set T : ℝ := (‖z‖ + 1 + R) / ‖v‖ with hT
  have hbd : ∀ x ∈ Metric.ball z 1, ∀ t : ℂ, T < ‖t‖ → fderiv ℝ F (x - t • v) = 0 := by
    intro x hx t ht
    apply fderiv_of_notMem_tsupport
    intro hmem
    have h1 := mem_closedBall_zero_iff.1 (hR hmem)
    have hx' : ‖x‖ ≤ ‖z‖ + 1 := by
      have := Metric.mem_ball.1 hx
      rw [dist_eq_norm] at this
      linarith [norm_sub_norm_le x z]
    have h2 : ‖t • v‖ ≤ ‖x‖ + ‖x - t • v‖ := by
      calc ‖t • v‖ = ‖x - (x - t • v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - t • v‖ := norm_sub_le _ _
    rw [norm_smul] at h2
    rw [hT, div_lt_iff₀ hvpos] at ht
    linarith
  have hint : Integrable (fun t : ℂ => (Set.indicator (Metric.closedBall (0 : ℂ) T)
      (fun t : ℂ => C * ‖t⁻¹‖) t)) := by
    refine IntegrableOn.integrable_indicator ?_ Metric.isClosed_closedBall.measurableSet
    exact (locallyIntegrable_inv_complex.integrableOn_isCompact
      (isCompact_closedBall 0 T)).norm.const_mul C
  have hF'int := integrable_cauchySolve (Λ := E →L[ℝ] Λ) hv hD hDc z
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume)
    (F := fun (x : E) (t : ℂ) => t⁻¹ • F (x - t • v))
    (F' := fun (x : E) (t : ℂ) => t⁻¹ • fderiv ℝ F (x - t • v))
    (x₀ := z) (s := Metric.ball z 1) (bound := fun t : ℂ => (Set.indicator
      (Metric.closedBall (0 : ℂ) T) (fun t : ℂ => C * ‖t⁻¹‖) t))
    (Metric.ball_mem_nhds z one_pos)
    (Filter.Eventually.of_forall fun x => (integrable_cauchySolve hv hF1 hc x).aestronglyMeasurable)
    (integrable_cauchySolve hv hF1 hc z) hF'int.aestronglyMeasurable
    (ae_of_all _ fun t x hx => ?_) hint
    (ae_of_all _ fun t x hx => ?_)
  · have := h.const_smul (π⁻¹ : ℂ)
    exact this
  · by_cases ht : T < ‖t‖
    · rw [hbd x hx t ht]
      simp only [smul_zero, norm_zero]
      exact Set.indicator_nonneg (fun s _ => mul_nonneg hC0 (norm_nonneg _)) t
    · rw [Set.indicator_of_mem (by simpa using not_lt.1 ht), norm_smul, norm_inv]
      calc ‖t‖⁻¹ * ‖fderiv ℝ F (x - t • v)‖ ≤ ‖t‖⁻¹ * C :=
            mul_le_mul_of_nonneg_left (hC _) (by positivity)
        _ = C * ‖t‖⁻¹ := mul_comm _ _
  · have h1 : HasFDerivAt (fun x : E => x - t • v) (ContinuousLinearMap.id ℝ E) x :=
      (hasFDerivAt_id x).sub_const _
    have h2 : HasFDerivAt F (fderiv ℝ F (x - t • v)) (x - t • v) :=
      ((hF.differentiable one_ne_zero) _).hasFDerivAt
    have h3 := (h2.comp x h1).const_smul t⁻¹
    simp only [ContinuousLinearMap.comp_id] at h3
    exact h3

omit [FiniteDimensional ℂ E] in
/-- **Z4.c (iii).** [Hörmander, Thm 2.3.3 (proof)]. For `v ≠ 0` and `F` of class `C¹` with
compact support, `∂̄` along `v` of the solver is `F`:
`½ (D(cauchySolve v F)(z) v + i D(cauchySolve v F)(z) (i v)) = F z` (the F3 normalization:
`antiPart L (toConj v) = ½ (L v + i L (i v))`). Proof: the slice `w ↦ cauchySolve v F (z + w • v)`
is `cauchyTransform` of `ζ ↦ F (z + ζ • v)` (Z4.b, `dbar_cauchyTransform` at `w = 0`). -/
theorem dbar_cauchySolve {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (z : E) :
    (2 : ℂ)⁻¹ • (fderiv ℝ (cauchySolve v F) z v + I • fderiv ℝ (cauchySolve v F) z (I • v)) =
      F z := by
  set h : ℂ → Λ := fun ζ => F (z + ζ • v) with hh
  have hemb : Topology.IsClosedEmbedding fun ζ : ℂ => z + ζ • v :=
    (Homeomorph.addLeft z).isClosedEmbedding.comp (isClosedEmbedding_smul_left hv)
  have hhc : HasCompactSupport h := hc.comp_isClosedEmbedding hemb
  have hh1 : ContDiff ℝ 1 h := hF.comp (by fun_prop : ContDiff ℝ 1 fun ζ : ℂ => z + ζ • v)
  have hslice : cauchyTransform h = cauchySolve v F ∘ fun w : ℂ => z + w • v := by
    funext w
    simp only [cauchyTransform, cauchySolve, Function.comp, hh]
    congr 3 with t
    rw [sub_smul, add_sub_assoc]
  set L : ℂ →L[ℝ] E := (ContinuousLinearMap.toSpanSingleton ℂ v).restrictScalars ℝ with hL
  have hg : HasFDerivAt (fun w : ℂ => z + w • v) L 0 := L.hasFDerivAt.const_add z
  have hS : HasFDerivAt (cauchySolve v F) (fderiv ℝ (cauchySolve v F) z) (z + (0 : ℂ) • v) := by
    rw [zero_smul, add_zero]
    exact (hasFDerivAt_cauchySolve hv hF hc z).differentiableAt.hasFDerivAt
  have hcomp := hS.comp 0 hg
  have hd : fderiv ℝ (cauchyTransform h) 0 = (fderiv ℝ (cauchySolve v F) z).comp L := by
    rw [hslice]
    exact hcomp.fderiv
  have := dbar_cauchyTransform hhc hh1 0
  rw [hd] at this
  simpa [hL, hh] using this

end Cohesive
