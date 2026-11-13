import Cohesivemodules.Forms.FrameModel
import Cohesivemodules.Algebra.FrameBaseChange
import Cohesivemodules.Forms.Dolbeault
import Cohesivemodules.Algebra.BaseChangeComp

set_option linter.style.header false

/-!
# Z5.i (chart part): transport between `frameDom` and forms on `U`

Blueprint item Z5.i, E.3–E.4 (`blueprint/blueprint-ll.md` §4 E; §11 v1.15). For an open `U`
inside the source of `φ = chartAt x`, forms on `U` correspond to functions on `V = frameDom U x`:
* `eq_of_chartExpr_eq_frameDom`: a form is determined by its chart expression on `V`;
* `exists_form_of_chartExpr`: every smooth `η : V → Λ` of form degree `q` is the chart expression
  of a Dolbeault form of degree `q` (F9.a converse, Z4.f);
* `exists_hol_of_chartExpr`: if moreover `q = 0` and `∂̄η = 0`, it is the chart expression of
  `ρ(f)` for a holomorphic `f ∈ O(U)` (F12);
* chart expressions of sums, products and `1` of Dolbeault forms;
* restriction: `chartExpr_dolbeaultRes`, `frameOp_baseChange` (the frame model of `N|V` in the
  restricted frame is that of `N` on `frameDom V x`), `frameDom_chartOpen`, `chartOpen_le`,
  `dolbeaultRes_comp`.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold Opposite
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X] {r : ℕ}

/-! ## Opens and restriction -/

variable (E) in
/-- Z5.i: restrictions compose: `(V → W) ∘ (U → V) = (U → W)`. -/
theorem dolbeaultRes_comp {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) :
    (dolbeaultRes E h₂).comp (dolbeaultRes E h₁) = dolbeaultRes E (h₂.trans h₁) := by
  rfl

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Z5.i: for `W ⊆ φ.target`, the frame domain of `chartOpen x W` is `W`. -/
theorem frameDom_chartOpen (x : X) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (chartAt E x).target) : frameDom E (chartOpen E x hW) x = W := by
  ext z
  constructor
  · rintro ⟨hz, hz2⟩
    have h2 : (chartAt E x) ((chartAt E x).symm z) ∈ W := hz2.2
    rwa [(chartAt E x).right_inv hz] at h2
  · intro hz
    have hzt := hWt hz
    refine ⟨hzt, (chartAt E x).map_target hzt, ?_⟩
    show (chartAt E x) ((chartAt E x).symm z) ∈ W
    rwa [(chartAt E x).right_inv hzt]

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Z5.i: `chartOpen x W ≤ U` when `W ⊆ frameDom U x`. -/
theorem chartOpen_le {U : Opens X} {x : X} {W : Set E} (hW : IsOpen W)
    (hWU : W ⊆ frameDom E U x) : chartOpen E x hW ≤ U := by
  intro y hy
  have h := (hWU hy.2).2
  have h2 : (chartAt E x).symm ((chartAt E x) y) ∈ (U : Set X) := h
  rwa [(chartAt E x).left_inv hy.1] at h2

/-- Z5.i: the chart expression of a restricted form agrees with that of the form at points of
the smaller open. -/
theorem chartExpr_dolbeaultRes {U V : Opens X} (h : V ≤ U) (α : DolbeaultAlg E U)
    (e : OpenPartialHomeomorph X E) {z : E} (hz : e.symm z ∈ V) :
    chartExpr E ((dolbeaultRes E h α : DolbeaultAlg E V) : V → TotFibre E) e z =
      chartExpr E (α : U → TotFibre E) e z := by
  have hU : e.symm z ∈ U := h hz
  simp only [chartExpr, hz, hU, ↓reduceDIte]
  rfl

/-- **Z5.i.** The frame model of the restriction `N|V` in the restricted frame `1 ⊗ ẽ` is the frame
model of `N` on `frameDom V x` (`mat_baseChange`, `chartExpr_dolbeaultRes`). -/
theorem frameOp_baseChange {U V : Opens X} (h : V ≤ U) {N : QuasiCohesive (dolbeaultGrade E U)}
    {F : GradedFrame (dolbeaultGrade E U) N.Q r}
    {F' : GradedFrame (dolbeaultGrade E V) (BCGen (dolbeaultRes E h) N.Q) r}
    (hF : ∀ i, F'.basis i = bcι (dolbeaultRes E h) N.Q (F.basis i)) (x : X) {z : E}
    (hz : z ∈ frameDom E V x) :
    frameOp (N := N.baseChange (dolbeaultRes E h)) F' x z = frameOp F x z := by
  refine ContinuousLinearMap.ext fun t => funext fun j => ?_
  refine (frameOp_apply (N := N.baseChange (dolbeaultRes E h)) F' x z t j).trans ?_
  rw [frameOp_apply F x z t j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mat_baseChange hF j i]
  exact congrArg _ (chartExpr_dolbeaultRes h _ _ hz.2)

/-! ## Chart expressions of algebra operations -/

variable {U : Opens X}

/-- Z5.i: chart expressions are additive. -/
theorem chartExpr_alg_add (α β : DolbeaultAlg E U) (e : OpenPartialHomeomorph X E) (z : E) :
    chartExpr E ((α + β : DolbeaultAlg E U) : U → TotFibre E) e z =
      chartExpr E (α : U → TotFibre E) e z + chartExpr E (β : U → TotFibre E) e z := by
  by_cases h : (e.symm z : X) ∈ U
  · simp only [chartExpr, h, ↓reduceDIte, Subalgebra.coe_add, Pi.add_apply, map_add]
  · simp only [chartExpr, h, ↓reduceDIte, add_zero]

/-- Z5.i: chart expressions of finite sums. -/
theorem chartExpr_alg_sum {ι : Type} (s : Finset ι) (α : ι → DolbeaultAlg E U)
    (e : OpenPartialHomeomorph X E) (z : E) :
    chartExpr E ((∑ i ∈ s, α i : DolbeaultAlg E U) : U → TotFibre E) e z =
      ∑ i ∈ s, chartExpr E (α i : U → TotFibre E) e z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact congrFun (chartExpr_zero (U := U) e) z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, chartExpr_alg_add, ih]

/-- Z5.i: chart expressions are multiplicative. -/
theorem chartExpr_alg_mul (α β : DolbeaultAlg E U) (e : OpenPartialHomeomorph X E) (z : E) :
    chartExpr E ((α * β : DolbeaultAlg E U) : U → TotFibre E) e z =
      chartExpr E (α : U → TotFibre E) e z * chartExpr E (β : U → TotFibre E) e z := by
  exact congrFun (chartExpr_mul (α : U → TotFibre E) (β : U → TotFibre E) e) z

/-- Z5.i: the chart expression of `1` on the frame domain. -/
theorem chartExpr_alg_one {x : X} {z : E} (hz : z ∈ frameDom E U x) :
    chartExpr E ((1 : DolbeaultAlg E U) : U → TotFibre E) (chartAt E x) z = 1 := by
  have hzU : (chartAt E x).symm z ∈ U := hz.2
  simp only [chartExpr, hzU, ↓reduceDIte, Subalgebra.coe_one, Pi.one_apply, TotFibre.pull_one]

/-- Z5.i: the chart expression of `0`. -/
theorem chartExpr_alg_zero (e : OpenPartialHomeomorph X E) (z : E) :
    chartExpr E ((0 : DolbeaultAlg E U) : U → TotFibre E) e z = 0 := by
  exact congrFun (chartExpr_zero (U := U) e) z

/-! ## Forms from functions on the frame domain -/

/-- **Z5.i.** If `U ⊆ φ.source`, a form on `U` is determined by its chart expression on
`frameDom U x` (`eq_of_chartExpr_eq`). -/
theorem eq_of_chartExpr_eq_frameDom {x : X} (hUs : (U : Set X) ⊆ (chartAt E x).source)
    {α β : DolbeaultAlg E U}
    (h : ∀ z ∈ frameDom E U x, chartExpr E (α : U → TotFibre E) (chartAt E x) z =
      chartExpr E (β : U → TotFibre E) (chartAt E x) z) : α = β := by
  refine Subtype.ext (funext fun y => ?_)
  have hys := hUs y.2
  refine eq_of_chartExpr_eq (chart_mem_atlas E x) y hys (h _ ⟨(chartAt E x).map_source hys, ?_⟩)
  show (chartAt E x).symm ((chartAt E x) y) ∈ (U : Set X)
  rw [(chartAt E x).left_inv hys]
  exact y.2

/-- Z5.i helper: pullback along the identity is the identity. -/
private theorem pull_id_aux' (a : TotFibre E) :
    TotFibre.pull (ContinuousLinearMap.id ℂ E) a = a := by
  funext i
  ext v
  rfl

/-- Z5.i helper: the function `y ↦ pull (D(φ ∘ ψ_y⁻¹)) (η (φ y))` has chart expression `η`. -/
private theorem chartExpr_pullForm {x : X} (_hUs : (U : Set X) ⊆ (chartAt E x).source)
    (η : E → TotFibre E) {z : E} (hz : z ∈ frameDom E U x) :
    chartExpr E (fun y : U => TotFibre.pull (fderiv ℂ (chartAt E x ∘ (chartAt E (y : X)).symm)
      (chartAt E (y : X) y)) (η (chartAt E x y))) (chartAt E x) z = η z := by
  set φ := chartAt E x with hφ
  have hzt : z ∈ φ.target := hz.1
  have hyU : φ.symm z ∈ U := hz.2
  rw [chartExpr_of_symm_eq _ φ rfl hyU]
  set y := φ.symm z with hy
  have hφz : φ y = z := φ.right_inv hzt
  have hinv := fderiv_transition_inv E (chart_mem_atlas E x) (chart_mem_atlas E y) hzt
    (mem_chart_source E y)
  show TotFibre.pull (chartTrans E φ y z) (TotFibre.pull (fderiv ℂ (φ ∘ (chartAt E y).symm)
    (chartAt E y y)) (η (φ y))) = _
  rw [TotFibre.pull_pull, hφz]
  have h2 : (fderiv ℂ (φ ∘ (chartAt E y).symm) (chartAt E y y)).comp (chartTrans E φ y z) =
      ContinuousLinearMap.id ℂ E := hinv
  rw [h2, pull_id_aux']

/-- **Z5.i.** If `U ⊆ φ.source`, a smooth `η : frameDom U x → Λ` of form degree `q` is the chart
expression of a Dolbeault form of degree `q` on `U` (degreewise `chartForm`, Z4.f; or directly
`y ↦ pull (D(φ ∘ (chartAt y)⁻¹)(chartAt y y)) (η (φ y))` with `isDolbeault_of_chartExpr`). -/
theorem exists_form_of_chartExpr {x : X} (hUs : (U : Set X) ⊆ (chartAt E x).source)
    {η : E → TotFibre E} (hη : ContDiffOn ℝ ∞ η (frameDom E U x)) {q : ℤ}
    (hq : ∀ z (i : Fin (Module.finrank ℂ E + 1)), ((i : ℕ) : ℤ) ≠ q → η z i = 0) :
    ∃ α : DolbeaultAlg E U, α ∈ dolbeaultGrade E U q ∧
      ∀ z ∈ frameDom E U x, chartExpr E (α : U → TotFibre E) (chartAt E x) z = η z := by
  set f : U → TotFibre E := fun y => TotFibre.pull (fderiv ℂ (chartAt E x ∘
    (chartAt E (y : X)).symm) (chartAt E (y : X) y)) (η (chartAt E x y)) with hf
  have hV : ∀ y : U, chartAt E x y ∈ frameDom E U x := fun y => by
    refine ⟨(chartAt E x).map_source (hUs y.2), ?_⟩
    show (chartAt E x).symm ((chartAt E x) y) ∈ (U : Set X)
    rw [(chartAt E x).left_inv (hUs y.2)]
    exact y.2
  have hdol : IsDolbeault E f := by
    refine isDolbeault_of_chartExpr (chart_mem_atlas E x) hUs fun y => ?_
    have h1 := hη.contDiffAt ((isOpen_frameDom E U x).mem_nhds (hV y))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_frameDom E U x).mem_nhds (hV y)] with w hw
    exact chartExpr_pullForm hUs η hw
  refine ⟨⟨f, hdol⟩, ?_, fun z hz => chartExpr_pullForm hUs η hz⟩
  intro y i hi
  show DolbeaultFibre.pull _ (η (chartAt E x y) i) = 0
  rw [hq _ i hi]
  ext v
  rfl

/-- **Z5.i (E.3).** If `x ∈ U ⊆ φ.source`, a smooth `η : frameDom U x → Λ⁰` with `∂̄η = 0` is the
chart expression of `ρ(f)` for a holomorphic `f ∈ O(U)` (`exists_form_of_chartExpr`,
`chartExpr_d`, `exists_dolbeaultRhoU_of_dbar_eq_zero`). -/
theorem exists_hol_of_chartExpr {x : X} (hx : x ∈ U) (hUs : (U : Set X) ⊆ (chartAt E x).source)
    {η : E → TotFibre E} (hη : ContDiffOn ℝ ∞ η (frameDom E U x))
    (h0 : ∀ z (i : Fin (Module.finrank ℂ E + 1)), (i : ℕ) ≠ 0 → η z i = 0)
    (hdbar : ∀ z ∈ frameDom E U x, dbarTot E η z = 0) :
    ∃ f : (holSheaf E X).obj.obj (op U), ∀ z ∈ frameDom E U x,
      chartExpr E (((dolbeaultRhoU E U f : dolbeaultGrade E U 0) : DolbeaultAlg E U) :
        U → TotFibre E) (chartAt E x) z = η z := by
  obtain ⟨α, hα, hαη⟩ := exists_form_of_chartExpr hUs hη (q := 0) fun z i hi =>
    h0 z i (fun h => hi (by rw [h]; rfl))
  have hd : GCDga.d (𝒜 := dolbeaultGrade E U) (α : DolbeaultAlg E U) = 0 := by
    refine eq_of_chartExpr_eq_frameDom hUs fun z hz => ?_
    rw [chartExpr_d hx α hz, chartExpr_alg_zero]
    rw [← hdbar z hz]
    refine dbarTot_congr ?_
    filter_upwards [(isOpen_frameDom E U x).mem_nhds hz] with w hw
    exact hαη w hw
  obtain ⟨f, hf⟩ :=
    exists_dolbeaultRhoU_of_dbar_eq_zero E (⟨α, hα⟩ : dolbeaultGrade E U 0) hd
  refine ⟨f, fun z hz => ?_⟩
  rw [hf]
  exact hαη z hz

end Cohesive
