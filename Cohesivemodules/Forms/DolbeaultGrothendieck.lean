import Cohesivemodules.Forms.FlatGrothendieck
import Cohesivemodules.Forms.ChartForm
import Cohesivemodules.Hypotheses

set_option linter.style.header false

/-!
# Z4.g: the Dolbeault–Grothendieck lemma on `X` (H1 holds)

Blueprint item Z4.g (§11, v1.14; `blueprint/blueprint-dg.md`, "Transfer to X", with the audit's
A4: our own chart machinery instead of TauCeti). `dolbeaultGrothendieck : DolbeaultGrothendieck
E X`: the hypothesis H1 (`Hypotheses.lean`, frozen) holds on every complex manifold `X`
modelled on a finite-dimensional `E`. No compactness or Hausdorff assumption is needed.

Proof. Given `α` of degree `q + 1` on `U` with `∂̄α = 0` and `x ∈ U`: if `q + 1 > n` there is
nothing to do (`dolbeaultGrothendieck_of_lt`). Otherwise let `φ = chartAt E x` and
`V = φ.target ∩ φ⁻¹'U`. The flat expression `flatExpr E x (q+1) α` (the degree-`(q+1)` component
of the expression of `α` in `φ`) is `C^∞` on `V` (F9.a) and `∂̄`-closed there (F9.b chart change,
`chartExpr_dbarSec_eq`). The flat lemma (Z4.e) gives `W ∋ φ x` and `η` with `∂̄η = flatExpr` on
`W`; `chartForm E x hW η` (Z4.f) on `U′ = φ.source ∩ φ⁻¹'W ⊆ U` has degree `q` and
`∂̄(chartForm η) = α|U′`, checked through the chart expression in `φ` (`eq_of_chartExpr_eq`).

## Deviations
* None: the statement is the frozen `DolbeaultGrothendieck E X` with only the instances of its
  definition (`IsManifold 𝓘(ℂ, E) ∞ X`).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **Z4.g.** The flat expression of degree `r` of a form `α` on `U` in the chart `chartAt E x`:
the degree-`r` component of `chartExpr E α (chartAt E x)`. -/
def flatExpr {U : Opens X} (x : X) (r : ℕ) (α : U → TotFibre E) : E → DolbeaultFibre E r ℂ :=
  fun z => TotFibre.deg r (chartExpr E α (chartAt E x) z)

variable {E}

omit [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Z4.g: for `α` of degree `r`, the chart expression is `ofDeg r` of the flat expression
(`chartExpr_support`, `eq_ofDeg_deg_aux`). -/
theorem chartExpr_eq_ofDeg_flatExpr {U : Opens X} {r : ℕ} {α : U → TotFibre E}
    (hα : IsOfDegree E (r : ℤ) α) (x : X) (z : E) :
    chartExpr E α (chartAt E x) z = TotFibre.ofDeg r (flatExpr E x r α z) :=
  eq_ofDeg_deg_aux E r _ (fun i hi => chartExpr_support hα _ _ i (by exact_mod_cast hi))

/-- Z4.g: the flat expression of a Dolbeault form is `C^∞` on
`V = φ.target ∩ φ⁻¹'U`, `φ = chartAt E x` (F9.a, `IsDolbeault.contDiffAt_chartExpr`). -/
theorem contDiffOn_flatExpr {U : Opens X} {α : U → TotFibre E} (hα : IsDolbeault E α) (x : X)
    (r : ℕ) :
    ContDiffOn ℝ ∞ (flatExpr E x r α)
      ((chartAt E x).target ∩ (chartAt E x).symm ⁻¹' (U : Set X)) := by
  intro z hz
  have hy : (chartAt E x).symm z ∈ (chartAt E x).source := (chartAt E x).map_target hz.1
  have h1 := hα.contDiffAt_chartExpr (chart_mem_atlas E x) ⟨_, hz.2⟩ hy
  rw [show chartAt E x ((chartAt E x).symm z) = z from (chartAt E x).right_inv hz.1] at h1
  have hL : ContDiff ℝ ∞ (LinearMap.toContinuousLinearMap (TotFibre.deg r : TotFibre E →ₗ[ℂ]
      DolbeaultFibre E r ℂ)|>.restrictScalars ℝ) := ContinuousLinearMap.contDiff _
  exact (hL.contDiffAt.comp z h1).contDiffWithinAt

/-- Z4.g: if `∂̄α = 0` on `U` and `x ∈ U`, the flat expression of `α` (any degree `r`) in
`chartAt E x` is `∂̄`-closed on `V` (`chartExpr_dbarSec_eq`, `dbarTot_apply_succ`; for `r = n`
the target fibre is zero, `dolbeaultFibre_subsingleton`). -/
theorem dbar_flatExpr_eq_zero {U : Opens X} {α : U → TotFibre E} (hα : IsDolbeault E α)
    (hd : dbarSec E α = 0) (x : U) (r : ℕ) {z : E} (hz : z ∈ (chartAt E (x : X)).target)
    (hzU : (chartAt E (x : X)).symm z ∈ U) : dbar (flatExpr E (x : X) r α) z = 0 := by
  by_cases h : r + 1 < Module.finrank ℂ E + 1
  · have h1 := dbarTot_apply_succ (chartExpr E α (chartAt E (x : X))) z h
    rw [← chartExpr_dbarSec_eq hα x hz hzU, hd, chartExpr_zero] at h1
    have h2 : (fun w => (chartExpr E α (chartAt E (x : X)) w ⟨r, by omega⟩ :
        DolbeaultFibre E r ℂ)) = flatExpr E (x : X) r α := by
      funext w
      simp only [flatExpr, TotFibre.deg, LinearMap.coe_mk, AddHom.coe_mk, (by omega :
        r < Module.finrank ℂ E + 1), ↓reduceDIte]
    rw [h2] at h1
    exact h1.symm
  · have :=dolbeaultFibre_subsingleton (E := E) (F := ℂ) (q := r + 1) (by omega)
    exact Subsingleton.elim _ _

variable (E X) in
/-- **Z4.g. H1 holds: the Dolbeault–Grothendieck lemma.** [Hörmander, Thm 2.3.3],
[Griffiths–Harris, p. 25], [B, §4.1]. On every complex manifold `X` modelled on a
finite-dimensional `E`: for every open `U`, `q : ℕ`, `x ∈ U` and Dolbeault form `α` of degree
`q + 1` on `U` with `∂̄α = 0`, there are an open `U′ ∋ x` inside `U` and a Dolbeault form `η` of
degree `q` on `U′` with `∂̄η = α|U′`. -/
theorem dolbeaultGrothendieck : DolbeaultGrothendieck E X := by
  intro U q x hx α hα hd
  by_cases hq : Module.finrank ℂ E < q + 1
  · exact dolbeaultGrothendieck_of_lt E X U q hq x hx α hα hd
  have hdol : IsDolbeault E α.1 := α.2
  have hdeg : IsOfDegree E ((q + 1 : ℕ) : ℤ) α.1 := by
    have : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; ring
    rw [this]; exact hα
  have hd' : dbarSec E α.1 = 0 := congrArg Subtype.val hd
  set φ := chartAt E x with hφ
  have hVo : IsOpen (φ.target ∩ φ.symm ⁻¹' (U : Set X)) :=
    φ.continuousOn_symm.isOpen_inter_preimage φ.open_target U.isOpen
  have hxV : φ x ∈ φ.target ∩ φ.symm ⁻¹' (U : Set X) :=
    ⟨φ.map_source (mem_chart_source E x), by
      rw [Set.mem_preimage, φ.left_inv (mem_chart_source E x)]; exact hx⟩
  obtain ⟨W, hWV, hWo, hxW, η, hη, hηW⟩ := exists_dbar_eq (q := q) hVo hxV
    (flatExpr E x (q + 1) α.1) (contDiffOn_flatExpr hdol x (q + 1))
    (fun z hz => dbar_flatExpr_eq_zero hdol hd' ⟨x, hx⟩ (q + 1) hz.1 hz.2)
  have hWt : W ⊆ φ.target := fun z hz => (hWV hz).1
  have hle : chartOpen E x hWo ≤ U := by
    intro y hy
    have h1 := (hWV hy.2).2
    rwa [Set.mem_preimage, φ.left_inv hy.1] at h1
  have hxU' : x ∈ chartOpen E x hWo := ⟨mem_chart_source E x, hxW⟩
  have hηo : ContDiffOn ℝ ∞ η W := hη.contDiffOn
  refine ⟨chartOpen E x hWo, hle, hxU',
    ⟨chartForm E x hWo η, isDolbeault_chartForm x hWo hWt hηo⟩,
    isOfDegree_chartForm x hWo η, ?_⟩
  apply Subtype.ext
  funext y
  refine eq_of_chartExpr_eq (chart_mem_atlas E x) y y.2.1 ?_
  have hyW : φ y ∈ W := y.2.2
  show chartExpr E (dbarSec E (chartForm E x hWo η)) φ (φ y) =
    chartExpr E (restrictForm E hle α.1) φ (φ y)
  rw [chartExpr_dbarSec_chartForm x hWo hWt hηo hxW hyW, hηW _ hyW,
    ← chartExpr_eq_ofDeg_flatExpr hdeg x (φ y)]
  have hs : φ.symm (φ y) = y := φ.left_inv y.2.1
  have hyU : (y : X) ∈ U := hle y.2
  rw [chartExpr_of_symm_eq α.1 φ hs hyU,
    chartExpr_of_symm_eq (restrictForm E hle α.1) φ hs y.2]
  rfl

end Cohesive
