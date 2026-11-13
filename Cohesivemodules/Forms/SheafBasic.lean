import Cohesivemodules.Forms.ChartAux

set_option linter.style.header false
-- The statements fix the section variables (`ChartedSpace`, `FiniteDimensional`), so many
-- lemmas carry unused instances.
set_option linter.unusedSectionVars false

/-!
# F9: Dolbeault forms on a complex manifold (lemmas)

Blueprint items F9.a–F9.c and the facts F10 needs (§5), about the definitions of
`Forms/SheafPred.lean`.

* Algebra: Dolbeault forms are closed under `0`, `1`, `+`, `*`, scalars, restriction, and
  degree projection; locality (`isDolbeault_of_locally`), so `dolbeaultLocalPredicate` is a
  `TopCat.LocalPredicate`.
* F9.a `IsDolbeault.contDiffAt_chartExpr`: the expression in every atlas chart is smooth.
* F9.b `IsDolbeault.dbarSec`: `∂̄` of a form is a form; `∂̄` is additive, `ℂ`-linear, local
  (`dbarSec_restrictForm`), `∂̄∂̄ = 0`, raises the degree by one, and satisfies the graded
  Leibniz rule.
* F9.c / F10: grading facts (`IsOfDegree`), graded commutativity, the decomposition into
  degree parts.

## Deviations
* Smoothness is `C^∞` over `ℝ` in the charts (`IsManifold 𝓘(ℂ, E) ∞ X` gives holomorphic, hence
  real-smooth, transition maps; F1).

First part of the original `Forms/Sheaf.lean`, split for size; continued in `Forms/Sheaf.lean`.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]

variable {E} {U V : Opens X}

/-! ## Chart expressions: pointwise algebra and locality -/

/-- `chartExpr` of `0` is `0`. -/
theorem chartExpr_zero (e : OpenPartialHomeomorph X E) :
    chartExpr E (0 : U → TotFibre E) e = 0 := by
  funext z
  unfold chartExpr
  split_ifs <;> simp only [Pi.zero_apply, map_zero]

/-- F9: `chartExpr` is additive. -/
theorem chartExpr_add (α β : U → TotFibre E) (e : OpenPartialHomeomorph X E) :
    chartExpr E (α + β) e = chartExpr E α e + chartExpr E β e := by
  funext z
  by_cases h : (e.symm z : X) ∈ U
  · simp only [chartExpr, h, ↓reduceDIte, Pi.add_apply, map_add]
  · simp only [chartExpr, h, ↓reduceDIte, Pi.add_apply, add_zero]

/-- F9: `chartExpr` commutes with complex scalars. -/
theorem chartExpr_smul (c : ℂ) (α : U → TotFibre E) (e : OpenPartialHomeomorph X E) :
    chartExpr E (c • α) e = c • chartExpr E α e := by
  funext z
  by_cases h : (e.symm z : X) ∈ U
  · simp only [chartExpr, h, ↓reduceDIte, Pi.smul_apply, map_smul]
  · simp only [chartExpr, h, ↓reduceDIte, Pi.smul_apply, smul_zero]

/-- `chartExpr` is multiplicative (pullbacks are algebra maps, F7.b). -/
theorem chartExpr_mul (α β : U → TotFibre E) (e : OpenPartialHomeomorph X E) :
    chartExpr E (α * β) e = chartExpr E α e * chartExpr E β e := by
  funext z
  by_cases h : (e.symm z : X) ∈ U
  · simp only [chartExpr, h, ↓reduceDIte, Pi.mul_apply, TotFibre.pull_mul]
  · simp only [chartExpr, h, ↓reduceDIte, Pi.mul_apply, mul_zero]

/-- F9: near `w ∈ e.target` with `e.symm w ∈ V`, `e.symm` lands in the open set `V`. -/
theorem eventually_symm_mem (e : OpenPartialHomeomorph X E) {w : E}
    (hw : w ∈ e.target) (hV : e.symm w ∈ V) : ∀ᶠ w' in nhds w, e.symm w' ∈ V :=
  (e.continuousAt_symm hw).eventually_mem (V.isOpen.mem_nhds hV)

/-- F9: restricting a form does not change its chart expression near a point of `V`. -/
theorem chartExpr_restrict_eventuallyEq (h : V ≤ U) (α : U → TotFibre E)
    (e : OpenPartialHomeomorph X E) {w : E} (hw : w ∈ e.target) (hV : e.symm w ∈ V) :
    chartExpr E (restrictForm E h α) e =ᶠ[nhds w] chartExpr E α e := by
  filter_upwards [eventually_symm_mem e hw hV] with w' hw'
  simp only [chartExpr, hw', h hw', ↓reduceDIte, restrictForm]

/-- F9: near a point with `e.symm w ∈ U`, the chart expression of `1` is the constant `1`. -/
theorem chartExpr_one_eventuallyEq (e : OpenPartialHomeomorph X E) {w : E}
    (hw : w ∈ e.target) (hU : e.symm w ∈ U) :
    chartExpr E (1 : U → TotFibre E) e =ᶠ[nhds w] fun _ => (1 : TotFibre E) := by
  filter_upwards [eventually_symm_mem e hw hU] with w' hw'
  simp only [chartExpr, hw', ↓reduceDIte, Pi.one_apply, TotFibre.pull_one]

/-! ## Algebra -/

/-- F10: `0` is a Dolbeault form. -/
theorem isDolbeault_zero : IsDolbeault E (0 : U → TotFibre E) := by
  intro x
  rw [chartExpr_zero]
  exact contDiffAt_const

/-- F10: the constant `1` is a Dolbeault form (`1` is fixed by pullbacks, F7.b). -/
theorem isDolbeault_one [IsManifold 𝓘(ℂ, E) ∞ X] : IsDolbeault E (1 : U → TotFibre E) := by
  intro x
  exact contDiffAt_const.congr_of_eventuallyEq
    (chartExpr_one_eventuallyEq _ (mem_chart_target E (x : X)) (by
      rw [(chartAt E (x : X)).left_inv (mem_chart_source E (x : X))]; exact x.2))

/-- F10: Dolbeault forms are closed under addition. -/
theorem IsDolbeault.add {α β : U → TotFibre E} (hα : IsDolbeault E α) (hβ : IsDolbeault E β) :
    IsDolbeault E (α + β) := by
  intro x
  rw [chartExpr_add]
  exact (hα x).add (hβ x)

/-- F10: Dolbeault forms are closed under multiplication (F9.c: the product is pointwise, and
pullbacks are algebra maps, F7.b). -/
theorem IsDolbeault.mul {α β : U → TotFibre E} (hα : IsDolbeault E α) (hβ : IsDolbeault E β) :
    IsDolbeault E (α * β) := by
  intro x
  rw [chartExpr_mul]
  exact contDiffAt_mul_tot (hα x) (hβ x)

/-- F10: Dolbeault forms are closed under complex scalars. -/
theorem IsDolbeault.smul (c : ℂ) {α : U → TotFibre E} (hα : IsDolbeault E α) :
    IsDolbeault E (c • α) := by
  intro x
  rw [chartExpr_smul]
  exact (hα x).const_smul c

/-- F10: constants `algebraMap ℂ _ c = c • 1` are Dolbeault forms. -/
theorem isDolbeault_algebraMap [IsManifold 𝓘(ℂ, E) ∞ X] (c : ℂ) :
    IsDolbeault E (algebraMap ℂ (U → TotFibre E) c) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (isDolbeault_one).smul c

/-- F9: the restriction of a Dolbeault form to an open `V ≤ U` is a Dolbeault form. -/
theorem IsDolbeault.restrictForm (h : V ≤ U) {α : U → TotFibre E} (hα : IsDolbeault E α) :
    IsDolbeault E (restrictForm E h α) := by
  intro x
  exact (hα ⟨x, h x.2⟩).congr_of_eventuallyEq
    (chartExpr_restrict_eventuallyEq h α _ (mem_chart_target E (x : X)) (by
      rw [(chartAt E (x : X)).left_inv (mem_chart_source E (x : X))]; exact x.2))

/-- F9 (locality): a function on `U` that is a Dolbeault form near every point is a Dolbeault
form. -/
theorem isDolbeault_of_locally {α : U → TotFibre E}
    (hα : ∀ x : U, ∃ (V : Opens X) (h : V ≤ U), (x : X) ∈ V ∧ IsDolbeault E (restrictForm E h α)) :
    IsDolbeault E α := by
  intro x
  obtain ⟨V, h, hxV, hd⟩ := hα x
  exact (hd ⟨x, hxV⟩).congr_of_eventuallyEq
    (chartExpr_restrict_eventuallyEq h α _ (mem_chart_target E (x : X)) (by
      rw [(chartAt E (x : X)).left_inv (mem_chart_source E (x : X))]; exact hxV)).symm

variable (E X) in
/-- **F9.** `IsDolbeault` as a `TopCat.LocalPredicate` on `X`, with constant fibre
`Λ^{0,•}(E)` (as Mathlib builds `smoothSheaf`). -/
def dolbeaultLocalPredicate : TopCat.LocalPredicate fun _ : TopCat.of X ↦ TotFibre E where
  pred {U} α := IsDolbeault E α
  res := fun {_ _} i _ hα ↦ IsDolbeault.restrictForm (CategoryTheory.leOfHom i) hα
  locality := fun {_} _ h ↦ isDolbeault_of_locally fun x ↦ by
    obtain ⟨V, hx, i, hV⟩ := h x
    exact ⟨V, CategoryTheory.leOfHom i, hx, hV⟩

/-! ## F9.a: chart independence -/

/-- **Chart change.** In `w ∈ e.target` with `e.symm w ∈ e'.source`, the expression of `α` in `e`
is the holomorphic pullback along `e' ∘ e.symm` of its expression in `e'` (F7.c). -/
theorem chartExpr_eq_pullback [IsManifold 𝓘(ℂ, E) ∞ X] (α : U → TotFibre E)
    {e e' : OpenPartialHomeomorph X E} (he : e ∈ atlas E X) (he' : e' ∈ atlas E X) {w : E}
    (hw : w ∈ (e.symm.trans e').source) :
    chartExpr E α e w =
      TotFibre.pull (fderiv ℂ (e' ∘ e.symm) w) (chartExpr E α e' ((e' ∘ e.symm) w)) := by
  obtain ⟨hw1, hw2⟩ := mem_transition_source.1 hw
  have hsymm : e'.symm (e' (e.symm w)) = e.symm w := e'.left_inv hw2
  by_cases hU : e.symm w ∈ U
  · have hG : DifferentiableAt ℂ (e' ∘ e.symm) w :=
      ((contDiffOn_atlas_transition he he').contDiffAt
        ((e.symm.trans e').open_source.mem_nhds hw)).differentiableAt (by norm_num)
    have hy : e.symm w ∈ (chartAt E (e.symm w)).source := mem_chart_source E _
    have hw' : e' (e.symm w) ∈ (e'.symm.trans (chartAt E (e.symm w))).source :=
      mem_transition_source.2 ⟨e'.map_source hw2, by rw [hsymm]; exact hy⟩
    have hH : DifferentiableAt ℂ (chartAt E (e.symm w) ∘ e'.symm) (e' (e.symm w)) :=
      ((contDiffOn_atlas_transition he' (chart_mem_atlas E (e.symm w))).contDiffAt
        ((e'.symm.trans (chartAt E (e.symm w))).open_source.mem_nhds hw')).differentiableAt
        (by norm_num)
    have hev : (chartAt E (e.symm w) ∘ e.symm) =ᶠ[nhds w]
        (chartAt E (e.symm w) ∘ e'.symm) ∘ (e' ∘ e.symm) := by
      filter_upwards [(e.symm.trans e').open_source.mem_nhds hw] with w' hw''
      obtain ⟨-, hw3⟩ := mem_transition_source.1 hw''
      simp only [Function.comp_apply, e'.left_inv hw3]
    rw [chartExpr_of_symm_eq α e rfl hU, Function.comp_apply,
      chartExpr_of_symm_eq α e' hsymm hU, TotFibre.pull_pull]
    congr 1
    unfold chartTrans
    rw [hev.fderiv_eq, fderiv_comp w hH hG]
    rfl
  · have hU' : e'.symm ((e' ∘ e.symm) w) ∉ U := by
      rw [Function.comp_apply, hsymm]
      exact hU
    rw [chartExpr_of_not_mem α e hU, chartExpr_of_not_mem α e' hU', map_zero]

/-- The pullback along a transition map of a function smooth at the image point is smooth. -/
theorem contDiffAt_pullback_transition [IsManifold 𝓘(ℂ, E) ∞ X]
    {e e' : OpenPartialHomeomorph X E} (he : e ∈ atlas E X) (he' : e' ∈ atlas E X) {w : E}
    (hw : w ∈ (e.symm.trans e').source) {β : E → TotFibre E}
    (hβ : ContDiffAt ℝ ∞ β ((e' ∘ e.symm) w)) :
    ContDiffAt ℝ ∞ (fun w' => TotFibre.pull (fderiv ℂ (e' ∘ e.symm) w')
      (β ((e' ∘ e.symm) w'))) w := by
  have hs := (e.symm.trans e').open_source
  have hon := contDiffOn_atlas_transition he he'
  have hG : ContDiffAt ℝ ∞ (e' ∘ e.symm) w :=
    ((hon.contDiffAt (hs.mem_nhds hw))).restrict_scalars ℝ
  have hD : ContDiffAt ℝ ∞ (fderiv ℂ (e' ∘ e.symm)) w :=
    ((hon.fderiv_of_isOpen hs (m := ∞) (by simp)).contDiffAt (hs.mem_nhds hw)).restrict_scalars ℝ
  exact contDiffAt_totPull (hβ.comp w hG) hD

/-- **F9.a.** [B, §4], [A, §7.1]. If `α` is a Dolbeault form on `U`, its expression in any atlas
chart `e` is real `C^∞` at `e x`, for every `x ∈ U ∩ e.source`. Proof: the expressions in `e`
and in `chartAt x` differ near `e x` by the holomorphic transition map (F7, `pullback`, and the
chain rule for the transition derivatives). -/
theorem IsDolbeault.contDiffAt_chartExpr [IsManifold 𝓘(ℂ, E) ∞ X] {α : U → TotFibre E}
    (hα : IsDolbeault E α) {e : OpenPartialHomeomorph X E} (he : e ∈ atlas E X) (x : U)
    (hx : (x : X) ∈ e.source) : ContDiffAt ℝ ∞ (chartExpr E α e) (e x) := by
  have hw : e x ∈ (e.symm.trans (chartAt E (x : X))).source :=
    mem_transition_source.2 ⟨e.map_source hx, by
      rw [e.left_inv hx]; exact mem_chart_source E _⟩
  have h1 := contDiffAt_pullback_transition he (chart_mem_atlas E (x : X)) hw
    (β := chartExpr E α (chartAt E (x : X))) (by simpa [e.left_inv hx] using hα x)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [(e.symm.trans (chartAt E (x : X))).open_source.mem_nhds hw] with w' hw'
  exact chartExpr_eq_pullback α he (chart_mem_atlas E (x : X)) hw'

/-! ## F9.b: `∂̄` on forms -/

/-- **Chart change for `∂̄`.** Near `φ x` (`φ = chartAt x`), the expression of `∂̄α` in `φ` is
`∂̄` of the expression of `α` in `φ` (F7.a with the chart change). -/
theorem chartExpr_dbarSec_eq [IsManifold 𝓘(ℂ, E) ∞ X] {α : U → TotFibre E}
    (hα : IsDolbeault E α) (x : U) {z : E} (hz : z ∈ (chartAt E (x : X)).target)
    (hzU : (chartAt E (x : X)).symm z ∈ U) :
    chartExpr E (dbarSec E α) (chartAt E (x : X)) z =
      dbarTot E (chartExpr E α (chartAt E (x : X))) z := by
  set φ := chartAt E (x : X) with hφ
  set y := φ.symm z with hy
  have hψ : chartAt E y ∈ atlas E X := chart_mem_atlas E y
  have hφa : φ ∈ atlas E X := chart_mem_atlas E (x : X)
  have hzs : z ∈ (φ.symm.trans (chartAt E y)).source :=
    mem_transition_source.2 ⟨hz, mem_chart_source E y⟩
  have hon := contDiffOn_atlas_transition hφa hψ
  have hG : ContDiffAt ℂ 2 (chartAt E y ∘ φ.symm) z :=
    ((hon.contDiffAt ((φ.symm.trans (chartAt E y)).open_source.mem_nhds hzs))).of_le
      (by norm_num)
  have hβ : DifferentiableAt ℝ (chartExpr E α (chartAt E y)) ((chartAt E y ∘ φ.symm) z) :=
    ((hα ⟨y, hzU⟩).differentiableAt (by norm_num) :)
  have h1 : chartExpr E α φ =ᶠ[nhds z] fun w => TotFibre.pull
      (fderiv ℂ (chartAt E y ∘ φ.symm) w)
      (chartExpr E α (chartAt E y) ((chartAt E y ∘ φ.symm) w)) := by
    filter_upwards [(φ.symm.trans (chartAt E y)).open_source.mem_nhds hzs] with w hw
    exact chartExpr_eq_pullback α hφa hψ hw
  rw [chartExpr_of_symm_eq (dbarSec E α) φ hy.symm hzU, dbarTot_congr h1,
    dbarTot_pullback hβ hG]
  rfl

/-- F9.b: where `chartAt x` is the chart, the chart expressions of `∂̄α` and `∂̄` of that of `α`
agree near `chartAt x x`. -/
theorem chartExpr_dbarSec_eventuallyEq [IsManifold 𝓘(ℂ, E) ∞ X] {α : U → TotFibre E}
    (hα : IsDolbeault E α) (x : U) :
    chartExpr E (dbarSec E α) (chartAt E (x : X)) =ᶠ[nhds (chartAt E (x : X) x)]
      dbarTot E (chartExpr E α (chartAt E (x : X))) := by
  have hmem := mem_chart_target E (x : X)
  have hU : (chartAt E (x : X)).symm (chartAt E (x : X) x) ∈ U := by
    rw [(chartAt E (x : X)).left_inv (mem_chart_source E (x : X))]; exact x.2
  filter_upwards [(chartAt E (x : X)).open_target.mem_nhds hmem,
    eventually_symm_mem (chartAt E (x : X)) hmem hU] with z hz hzU
  exact chartExpr_dbarSec_eq hα x hz hzU

/-- **F9.b.** [B, §4], [A, §7.1]. `∂̄` of a Dolbeault form is a Dolbeault form. Proof: in the
chart `e = chartAt x`, the expression of `∂̄α` near `e x` is `∂̄` of the expression of `α`
(F7.a, `dbar_pullback`, with F9.a), which is smooth (`contDiffOn_dbar_infty`). -/
theorem IsDolbeault.dbarSec [IsManifold 𝓘(ℂ, E) ∞ X] {α : U → TotFibre E}
    (hα : IsDolbeault E α) : IsDolbeault E (dbarSec E α) := fun x ↦
  (contDiffAt_dbarTot (hα x)).congr_of_eventuallyEq (chartExpr_dbarSec_eventuallyEq hα x)

/-- **F9.b.** `∂̄` is additive on Dolbeault forms. -/
theorem dbarSec_add [IsManifold 𝓘(ℂ, E) ∞ X] {α β : U → TotFibre E} (hα : IsDolbeault E α)
    (hβ : IsDolbeault E β) : dbarSec E (α + β) = dbarSec E α + dbarSec E β := by
  funext x
  show dbarTot E (chartExpr E (α + β) (chartAt E (x : X))) (chartAt E (x : X) x) =
    dbarTot E (chartExpr E α (chartAt E (x : X))) (chartAt E (x : X) x) +
      dbarTot E (chartExpr E β (chartAt E (x : X))) (chartAt E (x : X) x)
  rw [chartExpr_add]
  exact dbarTot_add ((hα x).differentiableAt (by norm_num)) ((hβ x).differentiableAt (by norm_num))

/-- **F9.b.** `∂̄` is `ℂ`-linear on Dolbeault forms. -/
theorem dbarSec_smul [IsManifold 𝓘(ℂ, E) ∞ X] (c : ℂ) {α : U → TotFibre E}
    (hα : IsDolbeault E α) : dbarSec E (c • α) = c • dbarSec E α := by
  funext x
  show dbarTot E (chartExpr E (c • α) (chartAt E (x : X))) (chartAt E (x : X) x) =
    c • dbarTot E (chartExpr E α (chartAt E (x : X))) (chartAt E (x : X) x)
  rw [chartExpr_smul]
  exact dbarTot_smul c ((hα x).differentiableAt (by norm_num))

/-- **F9.b.** `∂̄` commutes with restriction to an open `V ≤ U` (locality of `∂̄`, `dbar_congr`). -/
theorem dbarSec_restrictForm [IsManifold 𝓘(ℂ, E) ∞ X] (h : V ≤ U) {α : U → TotFibre E}
    (hα : IsDolbeault E α) : dbarSec E (restrictForm E h α) = restrictForm E h (dbarSec E α) := by
  funext x
  show dbarTot E (chartExpr E (restrictForm E h α) (chartAt E (x : X))) (chartAt E (x : X) x) =
    dbarTot E (chartExpr E α (chartAt E (x : X))) (chartAt E (x : X) x)
  refine dbarTot_congr (chartExpr_restrict_eventuallyEq h α _ (mem_chart_target E (x : X)) ?_)
  rw [(chartAt E (x : X)).left_inv (mem_chart_source E (x : X))]
  exact x.2

/-- **F9.b with F4.** [B, §4]. `∂̄∂̄ = 0` on Dolbeault forms (`dbar_dbar` in each chart, with
F9.a to compute the expression of `∂̄α` in `chartAt x`). -/
theorem dbarSec_dbarSec [IsManifold 𝓘(ℂ, E) ∞ X] {α : U → TotFibre E} (hα : IsDolbeault E α) :
    dbarSec E (dbarSec E α) = 0 := by
  funext x
  show dbarTot E (chartExpr E (dbarSec E α) (chartAt E (x : X))) (chartAt E (x : X) x) = 0
  rw [dbarTot_congr (chartExpr_dbarSec_eventuallyEq hα x)]
  exact dbarTot_dbarTot ((hα x).of_le (by norm_num))

end Cohesive
end
