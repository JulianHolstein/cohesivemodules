import Cohesivemodules.Analysis.CauchySolve

set_option linter.style.header false

/-!
# Z5.a: sup bound for the parametric solver

Blueprint item Z5.a (`blueprint/blueprint-ll.md` §4 C.1; §11 v1.15). The Cauchy kernel integrates
over a disc of radius `ρ` to at most `3πρ`, wherever the disc is:
`∫_{B(c,ρ)} |t|⁻¹ dA(t) ≤ ∫_{B(0,ρ)} |t|⁻¹ dA(t) + π ρ² / ρ = 2πρ + πρ = 3πρ`
(polar coordinates for the centred disc; `|t|⁻¹ ≤ ρ⁻¹` off `B(0,ρ)`). Hence the solver
`cauchySolve v G` of a function `G` whose support meets every complex line `z + ℂ v` in a disc of
radius `ρ` (in the coordinate `ℓ` with `ℓ v = 1`) is bounded by `3ρ · sup ‖G‖`. This is the
contraction estimate of the Neumann series in Z5.c ([DK, p. 52]: `∫_D |1/z| ≤ 2π` on the unit disc).

## Deviations
* [DK] uses the centred disc; for parameters the disc is centred at `ℓ(z) − c`, hence `3πρ`
  instead of `2πρ` (no rearrangement inequality needed).
-/

open MeasureTheory Complex Set Metric
open scoped Real

namespace Cohesive

/-- **Z5.a.** `∫_{B(0,ρ)} |t|⁻¹ dA(t) = 2πρ` (polar coordinates). -/
theorem integral_inv_norm_ball_zero {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ t in ball (0 : ℂ) ρ, ‖t‖⁻¹ = 2 * π * ρ := by
  have h1 : ∫ t in ball (0 : ℂ) ρ, ‖t‖⁻¹ =
      ∫ t : ℂ, (ball (0 : ℂ) ρ).indicator (fun t => ‖t‖⁻¹) t := by
    rw [integral_indicator measurableSet_ball]
  rw [h1, ← Complex.integral_comp_polarCoord_symm]
  have h2 : ∀ p ∈ (polarCoord.target : Set (ℝ × ℝ)),
      p.1 • (ball (0 : ℂ) ρ).indicator (fun t : ℂ => ‖t‖⁻¹) (Complex.polarCoord.symm p)
        = {p : ℝ × ℝ | p.1 < ρ}.indicator (fun _ => (1 : ℝ)) p := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases h : p.1 < ρ
    · have : Complex.polarCoord.symm p ∈ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff, hn]; exact h
      simp only [indicator_of_mem this, indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < ρ} from h),
        hn, smul_eq_mul]
      field_simp
    · have : Complex.polarCoord.symm p ∉ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff, hn]; exact h
      simp only [indicator_of_notMem this,
        indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < ρ} from h), smul_zero]
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < ρ} :=
    measurableSet_lt measurable_fst measurable_const
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet h2, integral_indicator hS]
  have h3 : {p : ℝ × ℝ | p.1 < ρ} ∩ polarCoord.target = Ioo 0 ρ ×ˢ Ioo (-π) π := by
    ext p
    have ht : (polarCoord.target : Set (ℝ × ℝ)) = Ioi 0 ×ˢ Ioo (-π) π := rfl
    rw [ht]
    simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h2, h1⟩, h3⟩, fun ⟨⟨h2, h1⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply hS, h3,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- Helper: the area of the disc `B(0,ρ)` in `ℂ` is `πρ²` (polar coordinates; the Mathlib lemma
`Complex.volume_ball` is not imported here). -/
private theorem toReal_volume_ball_zero {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume (ball (0 : ℂ) ρ)).toReal = π * ρ ^ 2 := by
  have h1 : (volume (ball (0 : ℂ) ρ)).toReal =
      ∫ t : ℂ, (ball (0 : ℂ) ρ).indicator (fun _ => (1 : ℝ)) t := by
    rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul, mul_one]; rfl
  rw [h1, ← Complex.integral_comp_polarCoord_symm]
  have h2 : ∀ p ∈ (polarCoord.target : Set (ℝ × ℝ)),
      p.1 • (ball (0 : ℂ) ρ).indicator (fun _ : ℂ => (1 : ℝ)) (Complex.polarCoord.symm p)
        = {p : ℝ × ℝ | p.1 < ρ}.indicator (fun p => p.1) p := by
    intro p hp
    have hp1 : 0 < p.1 := hp.1
    have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
    by_cases h : p.1 < ρ
    · have : Complex.polarCoord.symm p ∈ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff, hn]; exact h
      simp only [indicator_of_mem this, indicator_of_mem (show p ∈ {p : ℝ × ℝ | p.1 < ρ} from h),
        smul_eq_mul, mul_one]
    · have : Complex.polarCoord.symm p ∉ ball (0 : ℂ) ρ := by
        rw [mem_ball_zero_iff, hn]; exact h
      simp only [indicator_of_notMem this,
        indicator_of_notMem (show p ∉ {p : ℝ × ℝ | p.1 < ρ} from h), smul_zero]
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 < ρ} :=
    measurableSet_lt measurable_fst measurable_const
  rw [setIntegral_congr_fun polarCoord.open_target.measurableSet h2, integral_indicator hS]
  have h3 : {p : ℝ × ℝ | p.1 < ρ} ∩ polarCoord.target = Ioo 0 ρ ×ˢ Ioo (-π) π := by
    ext p
    have ht : (polarCoord.target : Set (ℝ × ℝ)) = Ioi 0 ×ˢ Ioo (-π) π := rfl
    rw [ht]
    simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h2, h1⟩, h3⟩, fun ⟨⟨h2, h1⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
  have h4 : (Measure.restrict volume polarCoord.target).restrict {p : ℝ × ℝ | p.1 < ρ}
      = volume.restrict (Ioo 0 ρ ×ˢ Ioo (-π) π) := by
    rw [Measure.restrict_restrict hS, h3]
  have hint : IntegrableOn (fun x : ℝ × ℝ => x.1) (Ioo 0 ρ ×ˢ Ioo (-π) π) (volume.prod volume) :=
    ((continuous_fst.continuousOn.integrableOn_compact
      ((isCompact_Icc (a := (0 : ℝ)) (b := ρ)).prod (isCompact_Icc (a := -π) (b := π)))
      (μ := volume.prod volume))).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  rw [h4, Measure.volume_eq_prod, setIntegral_prod _ hint]
  simp only [setIntegral_const, smul_eq_mul]
  rw [Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ, integral_id]
  ring

/-- Helper: the area of every disc of radius `ρ` in `ℂ` is `πρ²`. -/
private theorem toReal_volume_ball {ρ : ℝ} (c : ℂ) (hρ : 0 ≤ ρ) :
    (volume (ball c ρ)).toReal = π * ρ ^ 2 := by
  have : ball c ρ = (fun x => -c + x) ⁻¹' ball (0 : ℂ) ρ := by
    ext x; simp
  rw [this, measure_preimage_add]
  exact toReal_volume_ball_zero hρ

/-- Helper: `t ↦ ‖t‖⁻¹` is integrable on every closed disc. -/
private theorem integrableOn_inv_norm_closedBall (c : ℂ) (ρ : ℝ) :
    IntegrableOn (fun t : ℂ => ‖t‖⁻¹) (closedBall c ρ) := by
  have h := (locallyIntegrable_inv_complex.integrableOn_isCompact
    (isCompact_closedBall c ρ)).norm
  simpa only [norm_inv, IntegrableOn] using h

/-- **Z5.a.** `t ↦ |t|⁻¹` is integrable on every disc of `ℂ`. -/
theorem integrableOn_inv_norm_ball (c : ℂ) (ρ : ℝ) :
    IntegrableOn (fun t : ℂ => ‖t‖⁻¹) (ball c ρ) :=
  (integrableOn_inv_norm_closedBall c ρ).mono_set ball_subset_closedBall

/-- **Z5.a.** `∫_{B(c,ρ)} |t|⁻¹ dA(t) ≤ 3πρ` for every centre `c`. -/
theorem integral_inv_norm_ball_le (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ t in ball c ρ, ‖t‖⁻¹ ≤ 3 * π * ρ := by
  rcases hρ.eq_or_lt with h0 | hpos
  · subst h0
    simp
  have hnn : ∀ t : ℂ, 0 ≤ ‖t‖⁻¹ := fun t => inv_nonneg.2 (norm_nonneg t)
  have hsplit : (∫ t in ball c ρ ∩ ball 0 ρ, ‖t‖⁻¹) + ∫ t in ball c ρ \ ball 0 ρ, ‖t‖⁻¹ =
      ∫ t in ball c ρ, ‖t‖⁻¹ :=
    integral_inter_add_sdiff measurableSet_ball (integrableOn_inv_norm_ball c ρ)
  have h1 : ∫ t in ball c ρ ∩ ball 0 ρ, ‖t‖⁻¹ ≤ 2 * π * ρ := by
    rw [← integral_inv_norm_ball_zero hρ]
    exact setIntegral_mono_set (integrableOn_inv_norm_ball 0 ρ)
      (ae_of_all _ hnn) (ae_of_all _ inter_subset_right)
  have h2 : ∫ t in ball c ρ \ ball 0 ρ, ‖t‖⁻¹ ≤ π * ρ := by
    have hb : ∀ t ∈ ball c ρ \ ball 0 ρ, ‖t‖⁻¹ ≤ ρ⁻¹ := by
      intro t ht
      have : ρ ≤ ‖t‖ := by
        have := ht.2
        rw [mem_ball_zero_iff, not_lt] at this
        exact this
      exact inv_anti₀ hpos this
    have hfin : volume (ball c ρ \ ball 0 ρ) < ⊤ :=
      lt_of_le_of_lt (measure_mono sdiff_subset) measure_ball_lt_top
    have := setIntegral_mono_on ((integrableOn_inv_norm_ball c ρ).mono_set sdiff_subset)
      (integrableOn_const hfin.ne) (measurableSet_ball.diff measurableSet_ball) hb
    rw [setIntegral_const, smul_eq_mul, Measure.real] at this
    have hv : (volume (ball c ρ \ ball 0 ρ)).toReal ≤ ρ ^ 2 * π := by
      have h3 : (volume (ball c ρ \ ball 0 ρ)).toReal ≤ (volume (ball c ρ)).toReal :=
        ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono sdiff_subset)
      rw [toReal_volume_ball c hρ] at h3
      linarith
    calc _ ≤ _ := this
      _ ≤ (ρ ^ 2 * π) * ρ⁻¹ := by gcongr
      _ = π * ρ := by field_simp
  linarith

/-- Helper: the closed-disc version of `integral_inv_norm_ball_le`. -/
private theorem integral_inv_norm_closedBall_le (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∫ t in closedBall c ρ, ‖t‖⁻¹ ≤ 3 * π * ρ := by
  have hnn : ∀ t : ℂ, 0 ≤ ‖t‖⁻¹ := fun t => inv_nonneg.2 (norm_nonneg t)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hρ' : 0 ≤ ρ + ε / (3 * π) := by positivity
  calc ∫ t in closedBall c ρ, ‖t‖⁻¹ ≤ ∫ t in ball c (ρ + ε / (3 * π)), ‖t‖⁻¹ :=
        setIntegral_mono_set (integrableOn_inv_norm_ball c _) (ae_of_all _ hnn)
          (ae_of_all _ (closedBall_subset_ball (by simp [Real.pi_pos, hε])))
    _ ≤ 3 * π * (ρ + ε / (3 * π)) := integral_inv_norm_ball_le c hρ'
    _ = 3 * π * ρ + ε := by field_simp

variable {E Λ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **Z5.a (C.1).** If `ℓ v = 1` and `G` vanishes outside `{w | ‖ℓ w − c‖ ≤ ρ}` and is bounded by
`C`, then `‖cauchySolve v G z‖ ≤ 3ρC` for every `z`. -/
theorem norm_cauchySolve_le {v : E} (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {G : E → Λ} {c : ℂ}
    {ρ C : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, G w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hG : ∀ w, ‖G w‖ ≤ C)
    (z : E) : ‖cauchySolve v G z‖ ≤ 3 * ρ * C := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hG 0)
  set B : Set ℂ := closedBall (ℓ z - c) ρ with hB
  have hbound : ∀ t : ℂ, ‖t⁻¹ • G (z - t • v)‖ ≤ B.indicator (fun t => C * ‖t‖⁻¹) t := by
    intro t
    by_cases ht : t ∈ B
    · rw [indicator_of_mem ht, norm_smul, norm_inv]
      have := mul_le_mul_of_nonneg_left (hG (z - t • v)) (inv_nonneg.2 (norm_nonneg t))
      linarith
    · rw [indicator_of_notMem ht]
      have : G (z - t • v) = 0 := by
        by_contra hne
        apply ht
        have h := hsupp _ hne
        rw [map_sub, map_smul, hℓ, smul_eq_mul, mul_one] at h
        rw [hB, mem_closedBall, dist_eq_norm, ← norm_neg]
        convert h using 2
        ring
      rw [this, smul_zero, norm_zero]
  have h0 : IntegrableOn (fun t : ℂ => C * ‖t‖⁻¹) B :=
    (integrableOn_inv_norm_closedBall _ _).const_mul C
  have hint : Integrable (B.indicator (fun t => C * ‖t‖⁻¹)) :=
    h0.integrable_indicator measurableSet_closedBall
  have h1 : ‖∫ t : ℂ, t⁻¹ • G (z - t • v)‖ ≤ 3 * π * ρ * C := by
    refine (norm_integral_le_of_norm_le hint (ae_of_all _ hbound)).trans ?_
    rw [integral_indicator measurableSet_closedBall, integral_const_mul]
    calc C * ∫ t in B, ‖t‖⁻¹ ≤ C * (3 * π * ρ) :=
          mul_le_mul_of_nonneg_left (integral_inv_norm_closedBall_le _ hρ) hC
      _ = 3 * π * ρ * C := by ring
  unfold cauchySolve
  rw [norm_smul]
  have hpi : ‖(π⁻¹ : ℂ)‖ = π⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hpi]
  calc π⁻¹ * ‖∫ t : ℂ, t⁻¹ • G (z - t • v)‖ ≤ π⁻¹ * (3 * π * ρ * C) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 3 * ρ * C := by field_simp

end Cohesive
