import Cohesivemodules.Forms.SheafBasic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# F9: Dolbeault forms on a complex manifold (lemmas, part 2)

Blueprint items F9.b–F9.c and F10 (§5): `∂̄∂̄ = 0`, degree facts, the graded Leibniz rule
for `∂̄`, degree projections and the grading (`IsOfDegree`). Split from `Forms/Sheaf.lean`
for size; the first part is `Forms/SheafBasic.lean`.
-/

noncomputable section
namespace Cohesive
open TopologicalSpace Manifold
open scoped ContDiff
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
variable {E} {U V : Opens X}

/-- The chart expression of a form of degree `q` is supported in degree `q`. -/
theorem chartExpr_support {q : ℤ} {α : U → TotFibre E} (hα : IsOfDegree E q α)
    (e : OpenPartialHomeomorph X E) (w : E) (j : Fin (Module.finrank ℂ E + 1))
    (hj : ((j : ℕ) : ℤ) ≠ q) : chartExpr E α e w j = 0 := by
  by_cases h : (e.symm w : X) ∈ U
  · simp only [chartExpr, h, ↓reduceDIte]
    show DolbeaultFibre.pull _ (α ⟨_, h⟩ j) = 0
    rw [hα _ j hj]
    rfl
  · simp only [chartExpr, h, ↓reduceDIte]
    rfl

/-- **F9.b.** `∂̄` raises the degree by one. -/
theorem IsOfDegree.dbarSec {q : ℤ} {α : U → TotFibre E} (hα : IsOfDegree E q α) :
    IsOfDegree E (q + 1) (dbarSec E α) := fun _ i hi ↦
  dbarTot_support (chartExpr_support hα _) _ i hi

/-- In the chart at `x`, the expression of `α` at `chartAt x x` is the value `α x`. -/
private theorem chartExpr_self (α : U → TotFibre E) (x : U) :
    chartExpr E α (chartAt E (x : X)) (chartAt E (x : X) x) = α x := by
  have hmem := mem_chart_target E (x : X)
  have hy : (chartAt E (x : X)).symm (chartAt E (x : X) x) = (x : X) :=
    (chartAt E (x : X)).left_inv (mem_chart_source E (x : X))
  rw [chartExpr_of_symm_eq α _ hy x.2]
  have hev : (chartAt E (x : X) ∘ (chartAt E (x : X)).symm) =ᶠ[nhds (chartAt E (x : X) x)] id := by
    filter_upwards [(chartAt E (x : X)).open_target.mem_nhds hmem] with w hw
    exact (chartAt E (x : X)).right_inv hw
  have hT : chartTrans E (chartAt E (x : X)) (x : X) (chartAt E (x : X) x) =
      ContinuousLinearMap.id ℂ E := by
    unfold chartTrans
    rw [hev.fderiv_eq, fderiv_id]
  rw [hT]
  funext i
  ext v
  rfl

/-- `∂̄` of the zero form is zero. -/
private theorem dbarSec_zero : dbarSec E (0 : U → TotFibre E) = 0 := by
  funext x
  show dbarTot E (chartExpr E (0 : U → TotFibre E) (chartAt E (x : X))) _ = 0
  rw [chartExpr_zero]
  exact dbarTot_zero _

/-- **F9.b with F6** (graded Leibniz rule). [B, §4]. For `α` of degree `p` and any `β`,
`∂̄(α ∧ β) = ∂̄α ∧ β + (-1)^p α ∧ ∂̄β`, the sign as in A1 (`GCDga.leibniz`). -/
theorem dbarSec_mul [IsManifold 𝓘(ℂ, E) ∞ X] {p : ℤ} {α β : U → TotFibre E}
    (hα : IsDolbeault E α) (hβ : IsDolbeault E β) (hp : IsOfDegree E p α) :
    dbarSec E (α * β) = dbarSec E α * β + p.negOnePow • (α * dbarSec E β) := by
  by_cases hp0 : 0 ≤ p ∧ p ≤ Module.finrank ℂ E
  · obtain ⟨p', rfl⟩ := Int.eq_ofNat_of_zero_le hp0.1
    funext x
    show dbarTot E (chartExpr E (α * β) (chartAt E (x : X))) (chartAt E (x : X) x) =
      dbarTot E (chartExpr E α (chartAt E (x : X))) (chartAt E (x : X) x) * β x +
        ((p' : ℤ).negOnePow) • (α x * dbarTot E (chartExpr E β (chartAt E (x : X)))
          (chartAt E (x : X) x))
    rw [chartExpr_mul, dbarTot_mul_of_support (by omega)
      ((hα x).differentiableAt (by norm_num)) ((hβ x).differentiableAt (by norm_num))
      (fun w j hj => chartExpr_support hp _ w j hj), chartExpr_self, chartExpr_self,
      negOnePow_smul_totFibre]
  · have hα0 : α = 0 := funext fun y ↦ totDeg_eq_zero (by omega) (hp y)
    subst hα0
    rw [zero_mul, dbarSec_zero]
    simp only [zero_mul, smul_zero, add_zero]

/-! ## F9.c / F10: grading -/

/-- Components of the chart expression of `projDeg q α`. -/
private theorem chartExpr_projDeg_apply (q : ℤ) (α : U → TotFibre E)
    (e : OpenPartialHomeomorph X E) (z : E) (i : Fin (Module.finrank ℂ E + 1)) :
    chartExpr E (projDeg E q α) e z i =
      if ((i : ℕ) : ℤ) = q then chartExpr E α e z i else 0 := by
  by_cases h : (e.symm z : X) ∈ U
  · simp only [chartExpr, h, ↓reduceDIte]
    show DolbeaultFibre.pull _ (projDeg E q α ⟨_, h⟩ i) =
      if ((i : ℕ) : ℤ) = q then DolbeaultFibre.pull _ (α ⟨_, h⟩ i) else 0
    by_cases hi : ((i : ℕ) : ℤ) = q
    · simp only [hi, ↓reduceIte]
      show DolbeaultFibre.pull _ (if ((i : ℕ) : ℤ) = q then α ⟨_, h⟩ i else 0) = _
      simp only [hi, ↓reduceIte]
    · simp only [hi, ↓reduceIte]
      show DolbeaultFibre.pull _ (if ((i : ℕ) : ℤ) = q then α ⟨_, h⟩ i else 0) = 0
      simp only [hi, ↓reduceIte]
      rfl
  · simp only [chartExpr, h, ↓reduceDIte]
    split_ifs <;> rfl

/-- F10: the degree-`q` part of a Dolbeault form is a Dolbeault form (pullbacks preserve
degrees, F7.b). -/
theorem IsDolbeault.projDeg (q : ℤ) {α : U → TotFibre E} (hα : IsDolbeault E α) :
    IsDolbeault E (projDeg E q α) := by
  intro x
  rw [contDiffAt_tot_iff]
  intro i
  simp only [chartExpr_projDeg_apply]
  by_cases hi : ((i : ℕ) : ℤ) = q
  · simp only [hi, ↓reduceIte]
    exact (contDiffAt_tot_iff.1 (hα x)) i
  · simp only [hi, ↓reduceIte]
    exact contDiffAt_const

/-- F10: the degree-`q` part has degree `q`. -/
theorem isOfDegree_projDeg (q : ℤ) (α : U → TotFibre E) : IsOfDegree E q (projDeg E q α) := by
  intro y i hi
  show (if ((i : ℕ) : ℤ) = q then α y i else 0) = 0
  simp only [hi, ↓reduceIte]

/-- F10: the degree-`q` part of a form of degree `q` is the form itself. -/
theorem IsOfDegree.projDeg_self {q : ℤ} {α : U → TotFibre E} (hα : IsOfDegree E q α) :
    projDeg E q α = α := by
  funext y i
  show (if ((i : ℕ) : ℤ) = q then α y i else 0) = α y i
  by_cases hi : ((i : ℕ) : ℤ) = q
  · simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte, hα y i hi]

/-- F10: the degree-`p` part of a form of degree `q ≠ p` is `0`. -/
theorem IsOfDegree.projDeg_ne {p q : ℤ} (hpq : p ≠ q) {α : U → TotFibre E}
    (hα : IsOfDegree E q α) : projDeg E p α = 0 := by
  funext y i
  show (if ((i : ℕ) : ℤ) = p then α y i else 0) = 0
  by_cases hi : ((i : ℕ) : ℤ) = p
  · simp only [hi, ↓reduceIte]
    exact hα y i (by omega)
  · simp only [hi, ↓reduceIte]

/-- F10: a form is the sum of its parts of degrees `0, …, n`. -/
theorem sum_projDeg (α : U → TotFibre E) :
    ∑ q ∈ Finset.range (Module.finrank ℂ E + 1), projDeg E (q : ℤ) α = α := by
  funext y i
  have h1 : (∑ q ∈ Finset.range (Module.finrank ℂ E + 1), projDeg E (q : ℤ) α) y =
      ∑ q ∈ Finset.range (Module.finrank ℂ E + 1), projDeg E (q : ℤ) α y :=
    Finset.sum_apply y _ _
  rw [h1]
  have h2 : (∑ q ∈ Finset.range (Module.finrank ℂ E + 1), projDeg E (q : ℤ) α y) i =
      ∑ q ∈ Finset.range (Module.finrank ℂ E + 1), projDeg E (q : ℤ) α y i :=
    Finset.sum_apply i _ _
  rw [h2, Finset.sum_eq_single (i : ℕ)]
  · show (if ((i : ℕ) : ℤ) = ((i : ℕ) : ℤ) then α y i else 0) = α y i
    simp only [↓reduceIte]
  · intro q _ hq
    show (if ((i : ℕ) : ℤ) = (q : ℤ) then α y i else 0) = 0
    have : ¬ ((i : ℕ) : ℤ) = (q : ℤ) := by omega
    simp only [this, ↓reduceIte]
  · intro h
    exact absurd (Finset.mem_range.2 i.2) h

/-- F10: a form of degree `q < 0` or `q > n` is `0`. -/
theorem IsOfDegree.eq_zero {q : ℤ} (hq : q < 0 ∨ (Module.finrank ℂ E : ℤ) < q)
    {α : U → TotFibre E} (hα : IsOfDegree E q α) : α = 0 := by
  funext y
  exact totDeg_eq_zero hq (hα y)

/-- F10: forms of degree `q` are closed under `0`, `+` and complex scalars. -/
theorem isOfDegree_zero (q : ℤ) : IsOfDegree E q (0 : U → TotFibre E) := fun _ _ _ ↦ rfl

/-- F10: see `isOfDegree_zero`. -/
theorem IsOfDegree.add {q : ℤ} {α β : U → TotFibre E} (hα : IsOfDegree E q α)
    (hβ : IsOfDegree E q β) : IsOfDegree E q (α + β) := by
  intro y i hi
  show α y i + β y i = 0
  rw [hα y i hi, hβ y i hi, add_zero]

/-- F10: see `isOfDegree_zero`. -/
theorem IsOfDegree.smul {q : ℤ} (c : ℂ) {α : U → TotFibre E} (hα : IsOfDegree E q α) :
    IsOfDegree E q (c • α) := by
  intro y i hi
  show c • α y i = 0
  rw [hα y i hi, smul_zero]

/-- F10: `1` has degree `0`. -/
theorem isOfDegree_one : IsOfDegree E 0 (1 : U → TotFibre E) := by
  intro y i hi
  show (1 : TotFibre E) i = 0
  rw [TotFibre.one_eq]
  exact ofDeg_apply_ne _ i (by exact_mod_cast hi)

/-- F10 with F5: the product of forms of degrees `p` and `q` has degree `p + q`. -/
theorem IsOfDegree.mul {p q : ℤ} {α β : U → TotFibre E} (hα : IsOfDegree E p α)
    (hβ : IsOfDegree E q β) : IsOfDegree E (p + q) (α * β) :=
  fun y ↦ totDeg_mul (hα y) (hβ y)

/-- F10 with F5 (graded commutativity, `ofDeg_mul_comm`): for forms of degrees `p` and `q`,
`α ∧ β = (-1)^{pq} β ∧ α`, the sign as in A1 (`GCDga.gcomm`). -/
theorem IsOfDegree.mul_comm {p q : ℤ} {α β : U → TotFibre E} (hα : IsOfDegree E p α)
    (hβ : IsOfDegree E q β) : α * β = (p * q).negOnePow • (β * α) :=
  funext fun y ↦ totDeg_mul_comm (hα y) (hβ y)

/-- F10: restriction preserves degrees. -/
theorem IsOfDegree.restrictForm {q : ℤ} (h : V ≤ U) {α : U → TotFibre E}
    (hα : IsOfDegree E q α) : IsOfDegree E q (restrictForm E h α) :=
  fun y i hi ↦ hα ⟨y, h y.2⟩ i hi

end Cohesive
