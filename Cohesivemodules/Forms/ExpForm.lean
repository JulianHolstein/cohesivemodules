import Cohesivemodules.Forms.LocalFree

set_option linter.style.header false

/-!
# Z3.d: the exponential of a degree-0 form

Blueprint item Z3.d (`blueprint/blueprint-tw.md` §3 B.4; blueprint §11 v1.19). For a degree-0
Dolbeault form `α` on `U` (a smooth function in charts), `expForm α = exp ∘ α`, again a degree-0
Dolbeault form; `exp (α + β) = exp α · exp β`, so `expUnit α` is a unit of `𝒜⁰(U)`, and
`∂̄ (exp α) = exp α · ∂̄ α` (chain rule; the holomorphic factor `exp α` passes through the
antilinear part). Used to build the gluing units `u = exp η` of a twist datum (Z3.d).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- Z3.d: `y ↦ exp (α y)` is a Dolbeault form (smooth in charts: `ContDiff.cexp`). -/
theorem isDolbeault_expFun {U : Opens X} (α : dolbeaultGrade E U 0) :
    IsDolbeault E (funForm E fun y : U ↦ Complex.exp (evalForm0 E y α)) := by
  classical
  intro x
  set e := chartAt E (x : X)
  have hxs : (x : X) ∈ e.source := mem_chart_source E (x : X)
  set g : E → ℂ :=
    fun z ↦ coef0 E (chartExpr E ((α : DolbeaultAlg E U) : U → TotFibre E) e z)
  have hg : ContDiffAt ℝ ∞ g (e x) :=
    ((coef0 E).restrictScalars ℝ).contDiff.contDiffAt.comp _ (α.1.2 x)
  have hev : ∀ᶠ z in nhds (e x), e.symm z ∈ U := by
    have hcs : ContinuousAt e.symm (e x) := e.continuousAt_symm (mem_chart_target E (x : X))
    exact hcs.eventually_mem (U.isOpen.mem_nhds (by rw [e.left_inv hxs]; exact x.2))
  have hev' : ∀ᶠ z in nhds (e x), z ∈ e.target :=
    e.open_target.mem_nhds (mem_chart_target E (x : X))
  refine ((hg.cexp).smul (contDiffAt_const (c := (1 : TotFibre E)))).congr_of_eventuallyEq ?_
  filter_upwards [hev, hev'] with z hz hzt
  rw [chartExpr_funForm]
  simp only [hz, ↓reduceDIte]
  congr 2
  have := coef0_chartExpr_form0 E α e ⟨e.symm z, hz⟩ (e.map_target hzt)
  simp only [e.right_inv hzt] at this
  exact this.symm

/-- **Z3.d.** The exponential `exp ∘ α` of a degree-0 Dolbeault form, as a degree-0 form. -/
def expForm {U : Opens X} (α : dolbeaultGrade E U 0) : dolbeaultGrade E U 0 :=
  ⟨⟨funForm E fun y : U ↦ Complex.exp (evalForm0 E y α), isDolbeault_expFun E α⟩,
    isOfDegree_funForm E _⟩

/-- Z3.d: two degree-0 forms with the same values are equal. -/
private theorem ext0 {U : Opens X} (a b : ↥(dolbeaultGrade E U 0))
    (h : ∀ y, evalForm0 E y a = evalForm0 E y b) : a = b := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [form0_eq_funForm E a, form0_eq_funForm E b]
  congr 1
  funext y
  exact h y

/-- Z3.d: `(exp α)(y) = exp (α(y))`. -/
theorem evalForm0_expForm {U : Opens X} (α : dolbeaultGrade E U 0) (y : U) :
    evalForm0 E y (expForm E α) = Complex.exp (evalForm0 E y α) := by
  rw [evalForm0_apply]
  show coef0 E (funForm E (fun y : U ↦ Complex.exp (evalForm0 E y α)) y) = _
  rw [funForm, ofDeg0_eq_smul_one, coef0_smul_one]

/-- Z3.d: `exp (α + β) = exp α · exp β`. -/
theorem expForm_add {U : Opens X} (α β : dolbeaultGrade E U 0) :
    expForm E (α + β) = expForm E α * expForm E β := by
  refine ext0 E _ _ fun y ↦ ?_
  rw [evalForm0_expForm, (evalForm0 E y).map_mul, evalForm0_expForm, evalForm0_expForm,
    (evalForm0 E y).map_add, Complex.exp_add]

/-- Z3.d: `exp 0 = 1`. -/
theorem expForm_zero {U : Opens X} : expForm E (0 : dolbeaultGrade E U 0) = 1 := by
  refine ext0 E _ _ fun y ↦ ?_
  rw [evalForm0_expForm, (evalForm0 E y).map_zero, (evalForm0 E y).map_one, Complex.exp_zero]

/-- Z3.d: `exp α · exp (−α) = 1`. (Stated separately: `AddGroup ↥(dolbeaultGrade E U 0)` times
out in instance search, PROGRESS trap.) -/
theorem expForm_mul_neg {U : Opens X} (α : dolbeaultGrade E U 0) :
    expForm E α * expForm E (-α) = 1 := by
  refine ext0 E _ _ fun y ↦ ?_
  have hn : evalForm0 E y (-α) = - evalForm0 E y α := (evalForm0 E y).map_neg α
  rw [(evalForm0 E y).map_mul, evalForm0_expForm, evalForm0_expForm, hn,
    (evalForm0 E y).map_one, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- Z3.d: `exp (−α) · exp α = 1`. -/
theorem expForm_neg_mul {U : Opens X} (α : dolbeaultGrade E U 0) :
    expForm E (-α) * expForm E α = 1 := by
  refine ext0 E _ _ fun y ↦ ?_
  have hn : evalForm0 E y (-α) = - evalForm0 E y α := (evalForm0 E y).map_neg α
  rw [(evalForm0 E y).map_mul, evalForm0_expForm, evalForm0_expForm, hn,
    (evalForm0 E y).map_one, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- **Z3.d.** `exp α` as a unit of `𝒜⁰(U)`, with inverse `exp (−α)`. -/
def expUnit {U : Opens X} (α : dolbeaultGrade E U 0) : (↥(dolbeaultGrade E U 0))ˣ where
  val := expForm E α
  inv := expForm E (-α)
  val_inv := expForm_mul_neg E α
  inv_val := expForm_neg_mul E α

/-- Z3.d helper: `(c • 1) j = 0` in positive degree. -/
private theorem smul_one_apply_ne' (c : ℂ) (j : Fin (Module.finrank ℂ E + 1))
    (hj : (j : ℕ) ≠ 0) : (c • (1 : TotFibre E)) j = 0 := by
  rw [← ofDeg0_eq_smul_one]
  show (if h : 0 = (j : ℕ) then DolbeaultFibre.cast h (form0Equiv E ℂ c) else 0) = 0
  simp only [Ne.symm hj, ↓reduceDIte]

/-- Z3.d helper: the degree-`0` component of `c • 1` is the constant `0`-form `c`. -/
private theorem smul_one_apply_zero' (c : ℂ) (h : 0 < Module.finrank ℂ E + 1) :
    ((c • (1 : TotFibre E)) ⟨0, h⟩ : DolbeaultFibre E 0 ℂ) = form0Equiv E ℂ c := by
  rw [← ofDeg0_eq_smul_one]
  show (if h : 0 = ((⟨0, h⟩ : Fin (Module.finrank ℂ E + 1)) : ℕ) then
    DolbeaultFibre.cast h (form0Equiv E ℂ c) else 0) = _
  simp only [↓reduceDIte, DolbeaultFibre.cast_rfl]

/-- Z3.d helper: `∂̄` of `c • 1` depends linearly on `antiPart (fderiv ℝ c z)`. -/
private theorem dbarTot_smul_one_smul (c c' : E → ℂ) (k : ℂ) (z : E)
    (hc : DifferentiableAt ℝ c z) (hc' : DifferentiableAt ℝ c' z)
    (h : antiPart (fderiv ℝ c' z) = k • antiPart (fderiv ℝ c z)) :
    dbarTot E (fun w ↦ c' w • (1 : TotFibre E)) z =
      k • dbarTot E (fun w ↦ c w • (1 : TotFibre E)) z := by
  unfold dbarTot
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  by_cases hq : (q : ℕ) = 0
  · obtain ⟨q, hk⟩ := q
    simp only at hq
    subst hq
    have h1 : (fun w ↦ ((c w • (1 : TotFibre E)) ⟨0, hk⟩ : DolbeaultFibre E 0 ℂ)) = form0 c :=
      funext fun w ↦ smul_one_apply_zero' E (c w) hk
    have h2 : (fun w ↦ ((c' w • (1 : TotFibre E)) ⟨0, hk⟩ : DolbeaultFibre E 0 ℂ)) = form0 c' :=
      funext fun w ↦ smul_one_apply_zero' E (c' w) hk
    show TotFibre.ofDeg (0 + 1) (dbar (fun w ↦ ((c' w • (1 : TotFibre E)) ⟨0, hk⟩ :
      DolbeaultFibre E 0 ℂ)) z) = k • TotFibre.ofDeg (0 + 1) (dbar (fun w ↦ ((c w •
        (1 : TotFibre E)) ⟨0, hk⟩ : DolbeaultFibre E 0 ℂ)) z)
    have h3 : ∀ A : Conj E →L[ℂ] ℂ, ContinuousAlternatingMap.ofSubsingleton ℂ (Conj E) ℂ
        (0 : Fin 1) (k • A) = k • ContinuousAlternatingMap.ofSubsingleton ℂ (Conj E) ℂ
        (0 : Fin 1) A := fun A ↦
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ)
        (0 : Fin 1)).map_smul k A
    rw [h1, h2, dbar_form0 hc, dbar_form0 hc', h, h3, map_smul]
  · have h1 : (fun w ↦ ((c w • (1 : TotFibre E)) q : DolbeaultFibre E q ℂ)) = fun _ ↦ 0 :=
      funext fun w ↦ smul_one_apply_ne' E (c w) q hq
    have h2 : (fun w ↦ ((c' w • (1 : TotFibre E)) q : DolbeaultFibre E q ℂ)) = fun _ ↦ 0 :=
      funext fun w ↦ smul_one_apply_ne' E (c' w) q hq
    show TotFibre.ofDeg ((q : ℕ) + 1) (dbar (fun w ↦ ((c' w • (1 : TotFibre E)) q :
      DolbeaultFibre E q ℂ)) z) = k • TotFibre.ofDeg ((q : ℕ) + 1) (dbar (fun w ↦ ((c w •
        (1 : TotFibre E)) q : DolbeaultFibre E q ℂ)) z)
    rw [h1, h2, dbar_zero_fn, map_zero, smul_zero]

/-- **Z3.d (B.4).** `∂̄ (exp α) = exp α · ∂̄ α` (chain rule; `dbarPart_comp_clm`). -/
theorem dbar_expForm {U : Opens X} (α : dolbeaultGrade E U 0) :
    GCDga.d (𝒜 := dolbeaultGrade E U) ((expForm E α : dolbeaultGrade E U 0) : DolbeaultAlg E U) =
      ((expForm E α : dolbeaultGrade E U 0) : DolbeaultAlg E U) *
        GCDga.d (𝒜 := dolbeaultGrade E U) ((α : dolbeaultGrade E U 0) : DolbeaultAlg E U) := by
  classical
  refine Subtype.ext (funext fun x ↦ ?_)
  show dbarSec E ((expForm E α : DolbeaultAlg E U) : U → TotFibre E) x =
    ((expForm E α : DolbeaultAlg E U) : U → TotFibre E) x *
      dbarSec E ((α : DolbeaultAlg E U) : U → TotFibre E) x
  set e := chartAt E (x : X)
  have hxs : (x : X) ∈ e.source := mem_chart_source E (x : X)
  have hdeg : ∀ (β : dolbeaultGrade E U 0) (z : E), chartExpr E
      ((β : DolbeaultAlg E U) : U → TotFibre E) e z =
        coef0 E (chartExpr E ((β : DolbeaultAlg E U) : U → TotFibre E) e z) • 1 :=
    fun β z ↦ eq_coef0_smul_one E _ fun i hi ↦ chartExpr_support β.2 e z i hi
  set g : E → ℂ :=
    fun z ↦ coef0 E (chartExpr E ((α : DolbeaultAlg E U) : U → TotFibre E) e z)
  have hg : ContDiffAt ℝ ∞ g (e x) :=
    ((coef0 E).restrictScalars ℝ).contDiff.contDiffAt.comp _ (α.1.2 x)
  have hgd : DifferentiableAt ℝ g (e x) := hg.differentiableAt (by simp)
  have hged : DifferentiableAt ℝ (fun z ↦ Complex.exp (g z)) (e x) := hgd.cexp
  have hev : ∀ᶠ z in nhds (e x), e.symm z ∈ U := by
    have hcs : ContinuousAt e.symm (e x) := e.continuousAt_symm (mem_chart_target E (x : X))
    exact hcs.eventually_mem (U.isOpen.mem_nhds (by rw [e.left_inv hxs]; exact x.2))
  have hev' : ∀ᶠ z in nhds (e x), z ∈ e.target :=
    e.open_target.mem_nhds (mem_chart_target E (x : X))
  have hloc : chartExpr E ((expForm E α : DolbeaultAlg E U) : U → TotFibre E) e =ᶠ[nhds (e x)]
      fun z ↦ Complex.exp (g z) • (1 : TotFibre E) := by
    filter_upwards [hev, hev'] with z hz hzt
    rw [hdeg (expForm E α) z]
    have h1 := coef0_chartExpr_form0 E (expForm E α) e ⟨e.symm z, hz⟩ (e.map_target hzt)
    have h2 := coef0_chartExpr_form0 E α e ⟨e.symm z, hz⟩ (e.map_target hzt)
    simp only [e.right_inv hzt] at h1 h2
    rw [h1, evalForm0_expForm]
    simp only [g, h2]
  have hanti : antiPart (fderiv ℝ (fun z ↦ Complex.exp (g z)) (e x)) =
      Complex.exp (g (e x)) • antiPart (fderiv ℝ g (e x)) := by
    rw [hgd.hasFDerivAt.cexp.fderiv, antiPart_smul]
  have hL : dbarSec E ((expForm E α : DolbeaultAlg E U) : U → TotFibre E) x =
      Complex.exp (g (e x)) • dbarTot E (fun z ↦ g z • (1 : TotFibre E)) (e x) := by
    unfold dbarSec
    rw [dbarTot_congr hloc]
    exact dbarTot_smul_one_smul E g _ _ _ hgd hged hanti
  have hR : dbarSec E ((α : DolbeaultAlg E U) : U → TotFibre E) x =
      dbarTot E (fun z ↦ g z • (1 : TotFibre E)) (e x) := by
    unfold dbarSec
    congr 1
    funext z
    exact hdeg α z
  rw [hL, hR, form0_apply_eq E (expForm E α) x, ← evalForm0_apply, evalForm0_expForm,
    smul_mul_assoc, one_mul]
  simp only [g, coef0_chartExpr_form0 E α e x hxs]

/-- Z3.d: the exponential commutes with restriction. -/
theorem dolbeaultRes_expForm {U V : Opens X} (h : V ≤ U) (α : dolbeaultGrade E U 0) :
    (dolbeaultRes E h).f0 (expForm E α) = expForm E ((dolbeaultRes E h).f0 α) := by
  refine ext0 E _ _ fun y ↦ ?_
  rw [evalForm0_res, evalForm0_expForm, evalForm0_expForm, evalForm0_res]

end Cohesive
