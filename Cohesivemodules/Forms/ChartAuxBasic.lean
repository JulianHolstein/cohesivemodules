import Cohesivemodules.Forms.SheafPred
import Cohesivemodules.Forms.Leibniz
import Cohesivemodules.Forms.Pullback
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option linter.style.header false
-- The statements fix the section variables (`ChartedSpace`, `FiniteDimensional`), so many
-- lemmas carry unused instances.
set_option linter.unusedSectionVars false

/-!
# Chart-transport and smoothness helpers (blueprint F9, F11, F12 support)

Helpers shared by `Forms/Sheaf.lean` and `Forms/Dolbeault.lean`, about the definitions of
`Forms/SheafPred.lean`:

* grading facts on the total fibre `TotFibre E` (support in one degree, products);
* chart expressions and transition maps (`chartExpr_of_symm_eq`, `mem_transition_source`,
  `contDiffOn_atlas_transition`, `TotFibre.pull_pull`);
* real smoothness and differentiability of functions into `TotFibre E` (componentwise, products,
  pullbacks `contDiffAt_totPull`);
* `∂̄` on the total fibre (`dbarTot`): locality, linearity, pullback, smoothness, `∂̄∂̄ = 0`,
  degree shift, and the Leibniz rule `dbarTot_mul_of_support`.

No new mathematics; these are the support lemmas of F9.a–F9.c, F11 and F12.

Part 1 of 2 of the original `Forms/ChartAux.lean`, split for size; continued in
`Forms/ChartAux.lean`.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]

variable {E} {U : Opens X}

/-! ## Grading helpers on the total fibre -/

/-- F9 helper: a total-fibre element supported in degree `p ≤ n` is `ofDeg p` of its degree-`p`
part. -/
theorem totDeg_eq_ofDeg {x : TotFibre E} {p : ℕ} (hp : p ≤ Module.finrank ℂ E)
    (h : ∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ (p : ℤ) → x i = 0) :
    x = TotFibre.ofDeg p (TotFibre.deg p x) := by
  funext i
  by_cases hi : p = (i : ℕ)
  · have hp' : p < Module.finrank ℂ E + 1 := by omega
    have : i = ⟨p, hp'⟩ := Fin.ext hi.symm
    subst this
    show _ = (if h : p = p then DolbeaultFibre.cast h (TotFibre.deg p x) else 0)
    simp only [↓reduceDIte, DolbeaultFibre.cast_rfl, TotFibre.deg, LinearMap.coe_mk,
      AddHom.coe_mk, hp']
  · rw [h i (by omega)]
    show _ = (if h : p = (i : ℕ) then DolbeaultFibre.cast h (TotFibre.deg p x) else 0)
    simp only [hi, ↓reduceDIte]

/-- F9 helper: `(-1)^n` for the units-of-`ℤ` sign acts on `TotFibre E` as the complex scalar
`(-1)^n`. -/
theorem negOnePow_smul_totFibre (n : ℕ) (z : TotFibre E) :
    ((n : ℤ).negOnePow) • z = (-1 : ℂ) ^ n • z := by
  rw [Units.smul_def, Int.negOnePow_def, zpow_natCast, Units.val_pow_eq_pow_val,
    ← Int.cast_smul_eq_zsmul ℂ]
  push_cast
  rfl

/-- F9 helper: components of `ofDeg p a` in other degrees vanish. -/
theorem ofDeg_apply_ne {p : ℕ} (a : DolbeaultFibre E p ℂ)
    (i : Fin (Module.finrank ℂ E + 1)) (h : ((i : ℕ) : ℤ) ≠ (p : ℤ)) :
    (TotFibre.ofDeg p a : TotFibre E) i = 0 := by
  show (if h : p = (i : ℕ) then DolbeaultFibre.cast h a else 0) = 0
  have : ¬ p = (i : ℕ) := by omega
  simp only [this, ↓reduceDIte]

/-- F9 helper: an element supported in a degree outside `[0, n]` is zero. -/
theorem totDeg_eq_zero {x : TotFibre E} {q : ℤ}
    (hq : q < 0 ∨ (Module.finrank ℂ E : ℤ) < q)
    (h : ∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ q → x i = 0) : x = 0 := by
  funext i
  have := i.2
  exact h i (by omega)

/-- F9 helper: the product of elements supported in degrees `p` and `q` is supported in degree
`p + q`. -/
theorem totDeg_mul {x y : TotFibre E} {p q : ℤ}
    (hx : ∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ p → x i = 0)
    (hy : ∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ q → y i = 0) :
    ∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ p + q → (x * y) i = 0 := by
  by_cases hp : 0 ≤ p ∧ p ≤ Module.finrank ℂ E
  · by_cases hq : 0 ≤ q ∧ q ≤ Module.finrank ℂ E
    · obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp.1
      obtain ⟨q', rfl⟩ := Int.eq_ofNat_of_zero_le hq.1
      rw [totDeg_eq_ofDeg (by omega) hx, totDeg_eq_ofDeg (by omega) hy,
        TotFibre.ofDeg_mul_ofDeg]
      intro i hi
      exact ofDeg_apply_ne _ i (by exact_mod_cast hi)
    · rw [totDeg_eq_zero (by omega) hy, mul_zero]
      intro i _; rfl
  · rw [totDeg_eq_zero (by omega) hx, zero_mul]
    intro i _; rfl

/-- F9 helper: graded commutativity for elements supported in degrees `p` and `q`. -/
theorem totDeg_mul_comm {x y : TotFibre E} {p q : ℤ}
    (hx : ∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ p → x i = 0)
    (hy : ∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ q → y i = 0) :
    x * y = (p * q).negOnePow • (y * x) := by
  by_cases hp : 0 ≤ p ∧ p ≤ Module.finrank ℂ E
  · by_cases hq : 0 ≤ q ∧ q ≤ Module.finrank ℂ E
    · obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp.1
      obtain ⟨q', rfl⟩ := Int.eq_ofNat_of_zero_le hq.1
      rw [totDeg_eq_ofDeg (by omega) hx, totDeg_eq_ofDeg (by omega) hy,
        TotFibre.ofDeg_mul_comm, ← Nat.cast_mul, negOnePow_smul_totFibre]
    · rw [totDeg_eq_zero (by omega) hy]
      simp only [mul_zero, zero_mul, smul_zero]
  · rw [totDeg_eq_zero (by omega) hx]
    simp only [mul_zero, zero_mul, smul_zero]

/-- F9 helper: the degree-`p` component as an evaluation, for `p ≤ n`. -/
theorem TotFibre.deg_eq_apply (x : TotFibre E) {p : ℕ} (h : p < Module.finrank ℂ E + 1) :
    TotFibre.deg p x = (x ⟨p, h⟩ : DolbeaultFibre E p ℂ) := by
  simp only [TotFibre.deg, LinearMap.coe_mk, AddHom.coe_mk, h, ↓reduceDIte]

/-- F9 helper: multiplying on the left by `x = ofDeg p a` decomposes the product by the degrees
of the right factor. -/
theorem ofDeg_mul_decomp (x y : TotFibre E) {p : ℕ} (a : DolbeaultFibre E p ℂ)
    (hx : x = TotFibre.ofDeg p a) :
    x * y = ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
      TotFibre.ofDeg (p + q) (wedge a (TotFibre.deg q y)) := by
  calc x * y = TotFibre.ofDeg p a * ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
        TotFibre.ofDeg q (TotFibre.deg q y) := by rw [TotFibre.sum_ofDeg_deg, hx]
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => (ofDeg_wedge a (TotFibre.deg q y)).symm

/-! ## Chart expressions and transition maps -/

/-- F9 helper: pulling back twice composes the maps in the opposite order. -/
theorem TotFibre.pull_pull (T S : E →L[ℂ] E) (a : TotFibre E) :
    TotFibre.pull T (TotFibre.pull S a) = TotFibre.pull (S.comp T) a := by
  funext i
  ext v
  rfl

/-- F9 helper: the chart expression at `z`, when `e.symm z = y ∈ U`. -/
theorem chartExpr_of_symm_eq (α : U → TotFibre E) (e : OpenPartialHomeomorph X E) {z : E}
    {y : X} (hy : e.symm z = y) (hyU : y ∈ U) :
    chartExpr E α e z = TotFibre.pull (chartTrans E e y z) (α ⟨y, hyU⟩) := by
  subst hy
  simp only [chartExpr, hyU, ↓reduceDIte]

/-- F9 helper: the chart expression vanishes where `e.symm z ∉ U`. -/
theorem chartExpr_of_not_mem (α : U → TotFibre E) (e : OpenPartialHomeomorph X E) {z : E}
    (h : e.symm z ∉ U) : chartExpr E α e z = 0 := by
  simp only [chartExpr, h, ↓reduceDIte]

/-- F9 helper: the natural domain of the transition map `e' ∘ e.symm`. -/
theorem mem_transition_source {e e' : OpenPartialHomeomorph X E} {w : E} :
    w ∈ (e.symm.trans e').source ↔ w ∈ e.target ∧ e.symm w ∈ e'.source := by
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage]

/-- F9 helper: transition maps between atlas charts are complex `C^∞` on their natural domain. -/
theorem contDiffOn_atlas_transition [IsManifold 𝓘(ℂ, E) ∞ X]
    {e e' : OpenPartialHomeomorph X E} (he : e ∈ atlas E X) (he' : e' ∈ atlas E X) :
    ContDiffOn ℂ ∞ (e' ∘ e.symm) (e.symm.trans e').source := by
  have h := (contDiffGroupoid ∞ 𝓘(ℂ, E)).compatible he he'
  have h2 := h.1
  simpa [contDiffGroupoid, contDiffPregroupoid] using h2

/-! ## Smoothness of functions into the total fibre -/

/-- F9 helper: `Conj.map` as a continuous real-linear map. -/
theorem exists_conjMap_realCLM :
    ∃ Cm : (E →L[ℂ] E) →L[ℝ] (Conj E →L[ℂ] Conj E), ∀ T, Cm T = Conj.map T := by
  refine ⟨LinearMap.mkContinuous
    { toFun := Conj.map
      map_add' := fun S T => by ext v; rfl
      map_smul' := fun r T => by
        ext v
        simp only [Conj.map_apply, _root_.smul_apply, RingHom.id_apply]
        rw [← Complex.coe_smul, ← Complex.coe_smul, Conj.toConj_smul, Complex.conj_ofReal] }
    1 (fun T => ?_), fun T => rfl⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  show ‖Conj.toConj (T (Conj.ofConj v))‖ ≤ 1 * ‖T‖ * ‖v‖
  have := T.le_opNorm (Conj.ofConj v)
  rw [one_mul]
  exact this

/-- F9 helper: `(L, a) ↦ a ∘ L` is real `C^∞` (it is polynomial). -/
theorem contDiff_compContinuousLinearMap_pair (q : ℕ) :
    ContDiff ℝ ∞ (fun p : (Conj E →L[ℂ] Conj E) × DolbeaultFibre E q ℂ =>
      p.2.compContinuousLinearMap p.1) := by
  have h1 : ContDiff ℂ ∞ (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (Conj E →L[ℂ] Conj E) → (DolbeaultFibre E q ℂ) →L[ℂ] (DolbeaultFibre E q ℂ)) := by
    rw [← contDiffOn_univ]
    exact (ContinuousAlternatingMap.cpolynomialOn_compContinuousLinearMapCLM _).contDiffOn
  have h2 : ContDiff ℂ ∞ (fun p : (Conj E →L[ℂ] Conj E) × DolbeaultFibre E q ℂ =>
      p.2.compContinuousLinearMap p.1) :=
    (h1.comp contDiff_fst).clm_apply contDiff_snd
  exact h2.restrict_scalars ℝ

/-- F9 helper: smoothness of a function into `TotFibre E` is componentwise. -/
theorem contDiffAt_tot_iff {f : E → TotFibre E} {z : E} {n : WithTop ℕ∞} :
    ContDiffAt ℝ n f z ↔ ∀ i, ContDiffAt ℝ n (fun w => f w i) z :=
  contDiffAt_pi (Φ := fun w i => f w i)

/-- F9 helper: `w ↦ pull (T w) (β w)` is real `C^∞` if `T` and `β` are. -/
theorem contDiffAt_totPull {β : E → TotFibre E} {T : E → (E →L[ℂ] E)} {z : E}
    (hβ : ContDiffAt ℝ ∞ β z) (hT : ContDiffAt ℝ ∞ T z) :
    ContDiffAt ℝ ∞ (fun w => TotFibre.pull (T w) (β w)) z := by
  obtain ⟨Cm, hCm⟩ := exists_conjMap_realCLM (E := E)
  have hT' : ContDiffAt ℝ ∞ (fun w => Cm (T w)) z := Cm.contDiff.contDiffAt.comp z hT
  rw [contDiffAt_tot_iff]
  intro i
  have hβi : ContDiffAt ℝ ∞ (fun w => β w i) z := (contDiffAt_tot_iff.1 hβ) i
  have := (contDiff_compContinuousLinearMap_pair (E := E) i).contDiffAt.comp z (hT'.prodMk hβi)
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, hCm]
  rfl

/-- F9 helper: the product of real-`C^∞` functions into `TotFibre E` is real `C^∞`. -/
theorem contDiffAt_mul_tot {f g : E → TotFibre E} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
    ContDiffAt ℝ ∞ (f * g) z := by
  let B : TotFibre E →L[ℝ] TotFibre E →L[ℝ] TotFibre E :=
    (ContinuousLinearMap.restrictScalarsL ℂ (TotFibre E) (TotFibre E) ℝ ℝ).comp
      ((TotFibre.mulCLM E).restrictScalars ℝ)
  exact (B.isBoundedBilinearMap.contDiff.contDiffAt.comp z (hf.prodMk hg) :)

/-- F9 helper: real differentiability of a function into `TotFibre E` is componentwise. -/
theorem differentiableAt_tot_iff {f : E → TotFibre E} {z : E} :
    DifferentiableAt ℝ f z ↔ ∀ i, DifferentiableAt ℝ (fun w => f w i) z :=
  differentiableAt_pi (Φ := fun w i => f w i)

/-- F9 helper: the product of real-differentiable functions into `TotFibre E` is
differentiable. -/
theorem differentiableAt_mul_tot {f g : E → TotFibre E} {z : E}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    DifferentiableAt ℝ (f * g) z := by
  let B : TotFibre E →L[ℝ] TotFibre E →L[ℝ] TotFibre E :=
    (ContinuousLinearMap.restrictScalarsL ℂ (TotFibre E) (TotFibre E) ℝ ℝ).comp
      ((TotFibre.mulCLM E).restrictScalars ℝ)
  have hc : ContDiffAt ℝ ∞ (fun p : TotFibre E × TotFibre E => B p.1 p.2) (f z, g z) :=
    B.isBoundedBilinearMap.contDiff.contDiffAt
  have h2 := (hc.differentiableAt (by simp)).comp z (hf.prodMk hg)
  exact h2

/-- F9 helper: a linear map on the total fibre, composed with a differentiable function. -/
theorem differentiableAt_lin_of_tot {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (L : TotFibre E →ₗ[ℂ] V) {f : E → TotFibre E} {z : E}
    (hf : DifferentiableAt ℝ f z) : DifferentiableAt ℝ (fun w => L (f w)) z :=
  ((LinearMap.toContinuousLinearMap L).restrictScalars ℝ).differentiableAt.comp z hf

/-- F9 helper: a linear map into the total fibre, composed with a differentiable function. -/
theorem differentiableAt_lin_to_tot {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (L : V →ₗ[ℂ] TotFibre E) {f : E → V} {z : E}
    (hf : DifferentiableAt ℝ f z) : DifferentiableAt ℝ (fun w => L (f w)) z :=
  ((LinearMap.toContinuousLinearMap L).restrictScalars ℝ).differentiableAt.comp z hf

end Cohesive
end
