import Cohesivemodules.Forms.Dbar

set_option linter.style.header false

/-!
# F8: Cauchy–Riemann

Blueprint item F8 (conventions §6). For `f : E → F` real `C^∞` on an open set `V`:
`∂̄f = 0` on `V` iff `f` is complex `C^∞` on `V`. This identifies the holomorphic functions
(complex `ContMDiff`, used for `O_X` in F12) with the real-smooth `∂̄`-closed functions.

Proof plan (blueprint): `∂̄f(x) = 0` means `Df(x)` is `ℂ`-linear (`antiPart_eq_zero_iff`); a
symmetric `ℝ`-bilinear map that is `ℂ`-linear in one slot is `ℂ`-linear in both, so the
derivative of `fderiv ℂ f` is again `ℂ`-linear; induct on the order. ⚠ This avoids
several-variable Cauchy or Osgood theory, which Mathlib does not have.
-/

noncomputable section

namespace Cohesive

open scoped ContDiff

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `antiPart L = 0` gives `L (i v) = i L v`. -/
private theorem comm_of_antiPart_eq_zero {L : E →L[ℝ] F} (h : antiPart L = 0) (v : E) :
    L (Complex.I • v) = Complex.I • L v := by
  have h1 := congrArg (fun T : Conj E →L[ℂ] F => T (Conj.toConj v)) h
  simp only [antiPart_apply, zero_apply, smul_eq_zero, inv_eq_zero,
    OfNat.ofNat_ne_zero, false_or] at h1
  have h2 := congrArg (fun w => Complex.I • w) h1
  simp only [smul_add, smul_smul, Complex.I_mul_I, neg_smul, one_smul, smul_zero] at h2
  have h3 : Complex.I • L v = L (Complex.I • v) := by
    have := sub_eq_zero.mp (by simpa only [← sub_eq_add_neg] using h2)
    exact this
  exact h3.symm

/-- `L (i v) = i L v` for all `v` gives `antiPart L = 0`. -/
private theorem antiPart_eq_zero_of_comm {L : E →L[ℝ] F}
    (h : ∀ v, L (Complex.I • v) = Complex.I • L v) : antiPart L = 0 := by
  ext v
  simp only [antiPart_apply, h, smul_smul, Complex.I_mul_I, neg_smul, one_smul, zero_apply]
  simp

/-- F8: the antilinear part of an `ℝ`-linear map vanishes iff the map is `ℂ`-linear. -/
theorem antiPart_eq_zero_iff (L : E →L[ℝ] F) :
    antiPart L = 0 ↔ ∃ T : E →L[ℂ] F, T.restrictScalars ℝ = L := by
  constructor
  · intro h
    have hI := comm_of_antiPart_eq_zero h
    refine ⟨{ toFun := L, map_add' := L.map_add, map_smul' := ?_, cont := L.continuous }, rfl⟩
    intro c v
    rw [RingHom.id_apply, realLinear_complex_smul, hI, ← mul_smul, ← add_smul]
    rw [Complex.re_add_im]
  · rintro ⟨T, rfl⟩
    exact antiPart_restrictScalars T

/-- F8: for `f` real-differentiable at `x`, `∂̄f(x) = 0` iff `D″f(x) = 0`. -/
theorem dbar_form0_eq_zero_iff {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) :
    dbar (form0 f) x = 0 ↔ antiPart (fderiv ℝ f x) = 0 := by
  rw [dbar_form0 hf]
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := F)
    (ι := Fin 1) 0).map_eq_zero_iff

/-- A continuous `ℝ`-linear left inverse of `T ↦ T.restrictScalars ℝ`
(`L ↦ (v ↦ ½ (L v - i L (i v)))`). -/
private theorem exists_leftInv_restrictScalars :
    ∃ P : (E →L[ℝ] F) →L[ℝ] (E →L[ℂ] F), ∀ T : E →L[ℂ] F, P (T.restrictScalars ℝ) = T := by
  let Q : (E →L[ℝ] F) → (E →L[ℂ] F) := fun L =>
    { toFun := fun v => (2 : ℂ)⁻¹ • (L v - Complex.I • L (Complex.I • v))
      map_add' := fun v w => by
        simp only [map_add, smul_add, smul_sub]
        abel
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [smul_smul Complex.I c, realLinear_complex_smul L c,
          realLinear_complex_smul L (Complex.I * c)]
        simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          zero_sub, zero_add, Complex.ofReal_neg]
        conv_rhs => rw [← Complex.re_add_im c]
        match_scalars <;> ring_nf; simp [Complex.I_sq]; ring
      cont := by
        have h1 : Continuous fun v : E => L v := L.continuous
        have h2 : Continuous fun v : E => L (Complex.I • v) :=
          L.continuous.comp (continuous_const_smul (Complex.I : ℂ))
        exact (h1.sub (h2.const_smul Complex.I)).const_smul _ }
  have hQ : ∀ (L : E →L[ℝ] F) (v : E),
      Q L v = (2 : ℂ)⁻¹ • (L v - Complex.I • L (Complex.I • v)) := fun _ _ => rfl
  refine ⟨LinearMap.mkContinuous
    { toFun := Q
      map_add' := fun L L' => by
        ext v
        simp only [hQ, add_apply, smul_add, smul_sub]
        abel
      map_smul' := fun r L => by
        ext v
        simp only [hQ, smul_apply, RingHom.id_apply,
          ← Complex.coe_smul, smul_sub]
        rw [smul_comm Complex.I (r : ℂ) (L (Complex.I • v)),
          smul_comm (2 : ℂ)⁻¹ (r : ℂ) (L v),
          smul_comm (2 : ℂ)⁻¹ (r : ℂ) (Complex.I • L (Complex.I • v))] }
    1 (fun L => ?_), fun T => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    have h1 : ‖L v‖ ≤ ‖L‖ * ‖v‖ := L.le_opNorm v
    have h2 : ‖Complex.I • L (Complex.I • v)‖ ≤ ‖L‖ * ‖v‖ := by
      have := L.le_opNorm (Complex.I • v)
      simpa [norm_smul] using this
    show ‖(2 : ℂ)⁻¹ • (L v - Complex.I • L (Complex.I • v))‖ ≤ _
    rw [norm_smul]
    have h3 := norm_sub_le (L v) (Complex.I • L (Complex.I • v))
    have : ‖(2 : ℂ)⁻¹‖ = 2⁻¹ := by simp
    rw [this]
    linarith
  · ext v
    show (2 : ℂ)⁻¹ • (T v - Complex.I • T (Complex.I • v)) = T v
    simp only [map_smul, smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]
    rw [← two_smul ℂ (T v), smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- `∂̄g = 0` at `x` gives complex differentiability, with `fderiv ℝ` the restriction. -/
private theorem differentiableAt_of_antiPart_eq_zero {g : E → F} {x : E}
    (hg : DifferentiableAt ℝ g x) (h : antiPart (fderiv ℝ g x) = 0) :
    DifferentiableAt ℂ g x ∧ fderiv ℝ g x = (fderiv ℂ g x).restrictScalars ℝ := by
  have hd : DifferentiableAt ℂ g x := by
    rw [differentiableAt_iff_restrictScalars ℝ hg]
    exact (antiPart_eq_zero_iff _).1 h
  exact ⟨hd, hd.fderiv_restrictScalars ℝ⟩

/-- Inductive step: if `g` is real `C^∞` with `∂̄g = 0` on open `V`, then so is `fderiv ℂ g`
in the sense of `ℝ`-smoothness, and `∂̄ (fderiv ℂ g) = 0` on `V`. -/
private theorem step_dbar {g : E → F} {V : Set E} (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V)
    (h0 : ∀ x ∈ V, antiPart (fderiv ℝ g x) = 0) :
    ContDiffOn ℝ ∞ (fderiv ℂ g) V ∧ ∀ x ∈ V, antiPart (fderiv ℝ (fderiv ℂ g) x) = 0 := by
  obtain ⟨P, hP⟩ := exists_leftInv_restrictScalars (E := E) (F := F)
  have hD : ∀ x ∈ V, DifferentiableAt ℝ g x := fun x hx =>
    (hg.contDiffAt (hV.mem_nhds hx)).differentiableAt (by simp)
  have hC2 : ∀ x ∈ V, fderiv ℝ g x = (fderiv ℂ g x).restrictScalars ℝ := fun x hx =>
    (differentiableAt_of_antiPart_eq_zero (hD x hx) (h0 x hx)).2
  have hEq : Set.EqOn (fderiv ℂ g) (fun y => P (fderiv ℝ g y)) V := fun y hy => by
    simp only [hC2 y hy, hP]
  have hF : ContDiffOn ℝ ∞ (fderiv ℝ g) V := hg.fderiv_of_isOpen hV (by simp)
  refine ⟨(P.contDiff.comp_contDiffOn hF).congr hEq, fun x hx => ?_⟩
  have hF1 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hF.contDiffAt (hV.mem_nhds hx)).differentiableAt (by simp)
  have hev : fderiv ℂ g =ᶠ[nhds x] fun y => P (fderiv ℝ g y) :=
    hEq.eventuallyEq_of_mem (hV.mem_nhds hx)
  have hg' : HasFDerivAt (fderiv ℂ g) (P.comp (fderiv ℝ (fderiv ℝ g) x)) x :=
    (P.hasFDerivAt.comp x hF1.hasFDerivAt).congr_of_eventuallyEq hev
  set ψ : (E →L[ℂ] F) →L[ℝ] (E →L[ℝ] F) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ E F ℝ ℝ).toContinuousLinearMap with hψ
  have hev2 : (fun y => ψ (fderiv ℂ g y)) =ᶠ[nhds x] fderiv ℝ g := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact (hC2 y hy).symm
  have h2 : HasFDerivAt (fderiv ℝ g) (ψ.comp (P.comp (fderiv ℝ (fderiv ℝ g) x))) x :=
    (ψ.hasFDerivAt.comp x hg').congr_of_eventuallyEq hev2.symm
  have hlin : ∀ u, fderiv ℝ (fderiv ℝ g) x u =
      (P (fderiv ℝ (fderiv ℝ g) x u)).restrictScalars ℝ := fun u => by
    have := congrArg (fun L => L u) (hF1.hasFDerivAt.unique h2)
    exact this
  rw [hg'.fderiv]
  have hsymm : IsSymmSndFDerivAt ℝ g x :=
    (hg.contDiffAt (hV.mem_nhds hx)).isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField])
  have hPv : ∀ u v,
      P (fderiv ℝ (fderiv ℝ g) x u) v = fderiv ℝ (fderiv ℝ g) x u v := fun u v => by
    exact (congrArg (fun L => L v) (hlin u)).symm
  have hI : ∀ u v, fderiv ℝ (fderiv ℝ g) x u (Complex.I • v) =
      Complex.I • fderiv ℝ (fderiv ℝ g) x u v := fun u v => by
    conv_lhs => rw [hlin u]
    conv_rhs => rw [hlin u]
    exact map_smul (P (fderiv ℝ (fderiv ℝ g) x u)) Complex.I v
  refine antiPart_eq_zero_of_comm (fun w => ?_)
  ext v
  simp only [ContinuousLinearMap.comp_apply, hPv, smul_apply]
  rw [hsymm, hI, hsymm]

/-- Induction: real `C^∞` with `∂̄ = 0` on an open set gives `C^n` over `ℂ` for every `n : ℕ`. -/
private theorem contDiffOn_nat_of_antiPart {V : Set E} (hV : IsOpen V) (n : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] (g : E → G),
      ContDiffOn ℝ ∞ g V → (∀ x ∈ V, antiPart (fderiv ℝ g x) = 0) →
        ContDiffOn ℂ (n : WithTop ℕ∞) g V := by
  induction n with
  | zero =>
    intro G _ _ g hg _
    exact contDiffOn_zero.2 hg.continuousOn
  | succ n ih =>
    intro G _ _ g hg h0
    obtain ⟨h1, h2⟩ := step_dbar hV hg h0
    have hdiff : DifferentiableOn ℂ g V := fun x hx =>
      (differentiableAt_of_antiPart_eq_zero
        ((hg.contDiffAt (hV.mem_nhds hx)).differentiableAt (by simp)) (h0 x hx)).1
        |>.differentiableWithinAt
    have := (contDiffOn_succ_iff_fderiv_of_isOpen (n := (n : WithTop ℕ∞)) hV).2
      ⟨hdiff, by simp, ih (fderiv ℂ g) h1 h2⟩
    exact_mod_cast this

/-- **F8 (Cauchy–Riemann).** For `f : E → F` real `C^∞` on an open set `V`, `∂̄f = 0` on `V` iff
`f` is complex `C^∞` on `V`. [B, §4.1] uses this identification implicitly
(`O_X ⊆ 𝒜^{0,0}_X` as the kernel of `∂̄`).

Deviation: none; the real smoothness hypothesis is the one the blueprint states (it is needed
for `⇒`; `⇐` holds for any complex-differentiable `f`). -/
theorem dbar_eq_zero_iff_contDiffOn {f : E → F} {V : Set E} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f V) :
    (∀ x ∈ V, dbar (form0 f) x = 0) ↔ ContDiffOn ℂ ∞ f V := by
  have hD : ∀ x ∈ V, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hV.mem_nhds hx)).differentiableAt (by simp)
  constructor
  · intro h
    exact contDiffOn_infty.2 fun n =>
      contDiffOn_nat_of_antiPart hV n f hf fun x hx => (dbar_form0_eq_zero_iff (hD x hx)).1 (h x hx)
  · intro h x hx
    rw [dbar_form0_eq_zero_iff (hD x hx)]
    have hc : DifferentiableAt ℂ f x :=
      (h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hx)
    rw [hc.fderiv_restrictScalars ℝ]
    exact antiPart_restrictScalars _

end Cohesive
