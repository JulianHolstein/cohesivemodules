import Cohesivemodules.Forms.Dolbeault

set_option linter.style.header false

/-!
# Z4.f: Dolbeault forms on `X` from flat forms in a chart

Blueprint item Z4.f (§11, v1.14; audit of `blueprint/blueprint-dg.md`, A4: replaces layers 3–4 and
F13). For `x : X`, `φ = chartAt E x`, an open `W ⊆ φ.target` and a flat form
`η : E → Λ^{0,q}(E)`, `chartForm E x hW η` is the form on `U′ = φ.source ∩ φ⁻¹(W)` whose value at
`y`, written in `chartAt E y` (F9 convention), is the pullback of `η(φ y)` along the transition
`φ ∘ (chartAt y)⁻¹`. Results:
* `chartExpr_chartForm`: its expression in `φ` is `η` on `W` (cocycle rule for transitions).
* `isDolbeault_of_chartExpr` (converse of F9.a): smooth in one atlas chart ⇒ Dolbeault form.
* `isDolbeault_chartForm`, `isOfDegree_chartForm`: it is a Dolbeault form of degree `q`.
* `eq_of_chartExpr_eq`: a form is determined at `y` by its chart expression at `e y`.
* `chartExpr_dbarSec_chartForm`: the expression of `∂̄(chartForm η)` in `φ` is `∂̄η` on `W`.

## Deviations
* Not the full chart transport F13 (an isomorphism of presheaves of dgas), only what Z4.g needs.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **Z4.f.** The open set `U′ = (chartAt E x).source ∩ (chartAt E x)⁻¹' W` of `X`. -/
def chartOpen (x : X) {W : Set E} (hW : IsOpen W) : Opens X :=
  ⟨(chartAt E x).source ∩ chartAt E x ⁻¹' W, (chartAt E x).isOpen_inter_preimage hW⟩

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Z4.f: membership in `chartOpen` (rfl). -/
theorem mem_chartOpen (x : X) {W : Set E} (hW : IsOpen W) (y : X) :
    y ∈ chartOpen E x hW ↔ y ∈ (chartAt E x).source ∧ chartAt E x y ∈ W := Iff.rfl

/-- **Z4.f.** The form on `chartOpen E x hW` with expression `η` in `φ = chartAt E x`: at `y` it is
`η(φ y)` (degree `q`, `TotFibre.ofDeg`) pulled back along `D(φ ∘ (chartAt y)⁻¹)(chartAt y y)`,
i.e. written in `chartAt E y` as F9 requires. -/
def chartForm (x : X) {W : Set E} (hW : IsOpen W) {q : ℕ} (η : E → DolbeaultFibre E q ℂ) :
    chartOpen E x hW → TotFibre E :=
  fun y => TotFibre.pull (fderiv ℂ (chartAt E x ∘ (chartAt E (y : X)).symm) (chartAt E (y : X) y))
    (TotFibre.ofDeg q (η (chartAt E x y)))

variable {E}

/-- Z4.f helper: pullback along the identity is the identity. -/
private theorem pull_id_aux (a : TotFibre E) :
    TotFibre.pull (ContinuousLinearMap.id ℂ E) a = a := by
  funext i
  ext v
  rfl

/-- **Z4.f.** On `W ⊆ φ.target`, the expression of `chartForm η` in `φ = chartAt E x` is `η`
(cocycle rule `fderiv_transition_cocycle`, `fderiv_transition_inv`). -/
theorem chartExpr_chartForm (x : X) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (chartAt E x).target) {q : ℕ} (η : E → DolbeaultFibre E q ℂ) {z : E}
    (hz : z ∈ W) :
    chartExpr E (chartForm E x hW η) (chartAt E x) z = TotFibre.ofDeg q (η z) := by
  set φ := chartAt E x with hφ
  have hzt : z ∈ φ.target := hWt hz
  have hyW : φ.symm z ∈ chartOpen E x hW :=
    ⟨φ.map_target hzt, by rw [Set.mem_preimage, φ.right_inv hzt]; exact hz⟩
  rw [chartExpr_of_symm_eq _ φ rfl hyW]
  set y := φ.symm z with hy
  have hφz : φ y = z := φ.right_inv hzt
  have hinv := fderiv_transition_inv E (chart_mem_atlas E x) (chart_mem_atlas E y) hzt
    (mem_chart_source E y)
  show TotFibre.pull (chartTrans E φ y z) (TotFibre.pull (fderiv ℂ (φ ∘ (chartAt E y).symm)
    (chartAt E y y)) (TotFibre.ofDeg q (η (φ y)))) = _
  rw [TotFibre.pull_pull, hφz]
  have h2 : (fderiv ℂ (φ ∘ (chartAt E y).symm) (chartAt E y y)).comp (chartTrans E φ y z) =
      ContinuousLinearMap.id ℂ E := hinv
  rw [h2, pull_id_aux]

/-- **Z4.f (converse of F9.a).** If `U ⊆ e.source` for an atlas chart `e` and the expression of
`α` in `e` is real `C^∞` at `e y` for every `y ∈ U`, then `α` is a Dolbeault form (chart change
`chartExpr_eq_pullback`, `contDiffAt_pullback_transition`). -/
theorem isDolbeault_of_chartExpr {U : Opens X} {e : OpenPartialHomeomorph X E}
    (he : e ∈ atlas E X) (hU : (U : Set X) ⊆ e.source) {α : U → TotFibre E}
    (h : ∀ y : U, ContDiffAt ℝ ∞ (chartExpr E α e) (e y)) : IsDolbeault E α := by
  intro x'
  set e' := chartAt E (x' : X) with he'
  have he'a : e' ∈ atlas E X := chart_mem_atlas E (x' : X)
  have hx's : (x' : X) ∈ e'.source := mem_chart_source E (x' : X)
  have hw : e' x' ∈ (e'.symm.trans e).source :=
    mem_transition_source.2 ⟨e'.map_source hx's, by rw [e'.left_inv hx's]; exact hU x'.2⟩
  have h1 := contDiffAt_pullback_transition he'a he hw (β := chartExpr E α e)
    (by simpa [Function.comp_apply, e'.left_inv hx's] using h x')
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(e'.symm.trans e).open_source.mem_nhds hw] with w' hw'
  exact chartExpr_eq_pullback α he'a he hw'

/-- **Z4.f.** For `η` real `C^∞` on `W ⊆ φ.target`, `chartForm η` is a Dolbeault form. -/
theorem isDolbeault_chartForm (x : X) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (chartAt E x).target) {q : ℕ} {η : E → DolbeaultFibre E q ℂ}
    (hη : ContDiffOn ℝ ∞ η W) : IsDolbeault E (chartForm E x hW η) := by
  have hU : ((chartOpen E x hW : Opens X) : Set X) ⊆ (chartAt E x).source := fun y hy => hy.1
  refine isDolbeault_of_chartExpr (chart_mem_atlas E x) hU fun y => ?_
  have hyW : chartAt E x y ∈ W := y.2.2
  have hL : ContDiffAt ℝ ∞ (fun w => TotFibre.ofDeg q (η w)) (chartAt E x y) :=
    (((LinearMap.toContinuousLinearMap (TotFibre.ofDeg q : DolbeaultFibre E q ℂ →ₗ[ℂ]
      TotFibre E)).restrictScalars ℝ).contDiff.contDiffAt).comp _
      (hη.contDiffAt (hW.mem_nhds hyW))
  refine hL.congr_of_eventuallyEq ?_
  filter_upwards [hW.mem_nhds hyW] with w hw
  exact chartExpr_chartForm x hW hWt η hw

omit [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- **Z4.f.** `chartForm η` has degree `q` (`pull_ofDeg`). -/
theorem isOfDegree_chartForm (x : X) {W : Set E} (hW : IsOpen W) {q : ℕ}
    (η : E → DolbeaultFibre E q ℂ) : IsOfDegree E (q : ℤ) (chartForm E x hW η) := by
  intro y i hi
  show TotFibre.pull _ (TotFibre.ofDeg q _) i = 0
  rw [TotFibre.pull_ofDeg]
  exact ofDeg_apply_ne _ i hi

/-- **Z4.f.** A form is determined at `y ∈ e.source` by its expression in the atlas chart `e` at
`e y` (the transition derivative `chartTrans e y (e y)` is invertible). -/
theorem eq_of_chartExpr_eq {U : Opens X} {e : OpenPartialHomeomorph X E} (he : e ∈ atlas E X)
    {α β : U → TotFibre E} (y : U) (hy : (y : X) ∈ e.source)
    (h : chartExpr E α e (e y) = chartExpr E β e (e y)) : α y = β y := by
  have hψ := chart_mem_atlas E (y : X)
  have hl : (chartAt E (y : X)).symm (chartAt E (y : X) y) = y :=
    (chartAt E (y : X)).left_inv (mem_chart_source E _)
  rw [chartExpr_of_symm_eq α e (e.left_inv hy) y.2,
    chartExpr_of_symm_eq β e (e.left_inv hy) y.2] at h
  have hinv := fderiv_transition_inv E hψ he (z := chartAt E (y : X) y)
    ((chartAt E (y : X)).map_source (mem_chart_source E _)) (by rw [hl]; exact hy)
  rw [hl] at hinv
  have key : ∀ a : TotFibre E, TotFibre.pull (fderiv ℂ (e ∘ (chartAt E (y : X)).symm)
      (chartAt E (y : X) y)) (TotFibre.pull (chartTrans E e y (e y)) a) = a := fun a => by
    rw [TotFibre.pull_pull]
    have : (chartTrans E e y (e y)).comp (fderiv ℂ (e ∘ (chartAt E (y : X)).symm)
      (chartAt E (y : X) y)) = ContinuousLinearMap.id ℂ E := hinv
    rw [this, pull_id_aux]
  have h2 := congrArg (TotFibre.pull (fderiv ℂ (e ∘ (chartAt E (y : X)).symm)
    (chartAt E (y : X) y))) h
  rw [key, key] at h2
  exact h2

/-- **Z4.f.** If `φ x ∈ W` (so `x ∈ U′`) and `η` is `C^∞` on `W ⊆ φ.target`, the expression of
`∂̄(chartForm η)` in `φ = chartAt E x` is `∂̄η` on `W` (`chartExpr_dbarSec_eq`, `dbarTot_ofDeg`). -/
theorem chartExpr_dbarSec_chartForm (x : X) {W : Set E} (hW : IsOpen W)
    (hWt : W ⊆ (chartAt E x).target) {q : ℕ} {η : E → DolbeaultFibre E q ℂ}
    (hη : ContDiffOn ℝ ∞ η W) (hx : chartAt E x x ∈ W) {z : E} (hz : z ∈ W) :
    chartExpr E (dbarSec E (chartForm E x hW η)) (chartAt E x) z =
      TotFibre.ofDeg (q + 1) (dbar η z) := by
  have hxU : x ∈ chartOpen E x hW := ⟨mem_chart_source E x, hx⟩
  have hdol := isDolbeault_chartForm x hW hWt hη
  have hzt : z ∈ (chartAt E x).target := hWt hz
  have hsU : (chartAt E (((⟨x, hxU⟩ : chartOpen E x hW)) : X)).symm z ∈ chartOpen E x hW :=
    ⟨(chartAt E x).map_target hzt, by
      rw [Set.mem_preimage, (chartAt E x).right_inv hzt]; exact hz⟩
  rw [chartExpr_dbarSec_eq hdol ⟨x, hxU⟩ hzt hsU]
  rw [← dbarTot_ofDeg q η z]
  refine dbarTot_congr ?_
  filter_upwards [hW.mem_nhds hz] with w hw
  exact chartExpr_chartForm x hW hWt η hw

end Cohesive
