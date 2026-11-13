import Cohesivemodules.Algebra.Frame
import Cohesivemodules.Forms.GaugeInduction
import Cohesivemodules.Forms.ChartForm

set_option linter.style.header false

/-!
# Z5.h: the frame model of a cohesive module in a chart

Blueprint item Z5.h, E.2 (`blueprint/blueprint-ll.md` §4 E; §11 v1.15). Let `N` be a
quasi-cohesive module over `𝒜_X(U)` with a graded frame `ẽ₁ … ẽ_r` (`GradedFrame`, E.1), and let
`φ = chartAt x₀`. On `V = frameDom U x₀ = φ(U ∩ φ.source)`:
* `chartCoef x z = (chartExpr xᵢ (z))ᵢ ∈ Fib E r`: the chart expression of the coefficients of `x`
  in the frame;
* `frameOp z ∈ FibOp E r`: `𝒜(z)(t)ⱼ = Σᵢ σ(tᵢ)·Ωⱼᵢ(z)` with `Ωⱼᵢ = chartExpr ωⱼᵢ` (the
  connection matrix `GradedFrame.mat`) and `σ` the grade involution (`matOp`);
* `chartCoef_X`: `chartCoef (𝕏x) = ∂̄(chartCoef x) + 𝒜·chartCoef x` on `V`. This is the
  generator-level sign identification of `𝕏(a ⊗ e) = da ⊗ e + σ(a)𝕏(1 ⊗ e)` with `∂̄ + 𝒜`;
* `isFlatSuperconn_frameOp`: `𝒜` is smooth, of total degree `1`, odd and Maurer–Cartan on `V`
  (the hypotheses of the gauge induction Z5.f).

## Deviations
* ⚠ Maurer–Cartan is proved from `𝕏² = 0` on the frame vectors (`chartCoef_vec`: their chart
  expressions are the constant unit vectors) and the Λ-linearity of `mcOp`, instead of on all
  smooth sections via `chartForm` (blueprint-ll E.2). Same statement.
* `chartCoef_X` and `mcOp_frameOp` assume `x₀ ∈ U` (the chart of `∂̄` on `U` is `chartAt x₀`).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **Z5.h (E.2).** The domain of the frame model: `φ(U ∩ φ.source)` for `φ = chartAt x₀`,
written as `φ.target ∩ φ⁻¹⁻¹(U)`. -/
def frameDom (U : Opens X) (x₀ : X) : Set E :=
  (chartAt E x₀).target ∩ (chartAt E x₀).symm ⁻¹' (U : Set X)

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Z5.h: the frame domain is open. -/
theorem isOpen_frameDom (U : Opens X) (x₀ : X) : IsOpen (frameDom E U x₀) :=
  (chartAt E x₀).isOpen_inter_preimage_symm U.isOpen

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Z5.h: `φ x₀ ∈ frameDom U x₀` when `x₀ ∈ U`. -/
theorem mem_frameDom {U : Opens X} {x₀ : X} (hx₀ : x₀ ∈ U) :
    chartAt E x₀ x₀ ∈ frameDom E U x₀ :=
  ⟨(chartAt E x₀).map_source (mem_chart_source E x₀), by
    show (chartAt E x₀).symm (chartAt E x₀ x₀) ∈ (U : Set X)
    rw [(chartAt E x₀).left_inv (mem_chart_source E x₀)]
    exact hx₀⟩

variable {E} {r : ℕ}

/-! ## Matrix operators -/

/-- **Z5.h (E.2).** The fibre operator of a matrix `Ω` of forms: `(matOp Ω t)ⱼ = Σᵢ σ(tᵢ)·Ωⱼᵢ`
(`σ` the grade involution `sgnTot`, the product in `Λ`). -/
def matOp (Ω : Fin r → Fin r → TotFibre E) : FibOp E r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t j => ∑ i, sgnTot E (t i) * Ω j i
      map_add' := fun s t => by
        funext j
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c t => by
        funext j
        simp only [Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum,
          RingHom.id_apply] }

/-- Z5.h: formula for `matOp` (rfl). -/
theorem matOp_apply (Ω : Fin r → Fin r → TotFibre E) (t : Fib E r) (j : Fin r) :
    matOp Ω t j = ∑ i, sgnTot E (t i) * Ω j i := rfl

/-- Z5.h: `matOp` of a smooth matrix is smooth (`matOp` is linear in `Ω`). -/
theorem contDiffOn_matOp {Ω : E → Fin r → Fin r → TotFibre E} {s : Set E}
    (h : ∀ j i, ContDiffOn ℝ ∞ (fun z => Ω z j i) s) :
    ContDiffOn ℝ ∞ (fun z => matOp (Ω z)) s := by
  let L : (Fin r → Fin r → TotFibre E) →ₗ[ℂ] FibOp E r :=
    { toFun := matOp
      map_add' := fun Ω Ω' => by
        refine ContinuousLinearMap.ext fun t => funext fun j => ?_
        simp only [matOp_apply, add_apply, Pi.add_apply, mul_add,
          Finset.sum_add_distrib]
      map_smul' := fun c Ω => by
        refine ContinuousLinearMap.ext fun t => funext fun j => ?_
        simp only [matOp_apply, smul_apply, Pi.smul_apply, RingHom.id_apply,
          mul_smul_comm, Finset.smul_sum] }
  have hL : ContDiff ℝ ∞ (LinearMap.toContinuousLinearMap L) :=
    (LinearMap.toContinuousLinearMap L).contDiff.restrict_scalars ℝ
  exact hL.comp_contDiffOn (contDiffOn_pi.2 fun j => contDiffOn_pi.2 fun i => h j i)

/-- Z5.h: `matOp Ω` anticommutes with every `εⱼ` (`σ(dz̄ⱼ t) = −dz̄ⱼ σ(t)`). -/
theorem matOp_odd (Ω : Fin r → Fin r → TotFibre E) (j : Fin (Module.finrank ℂ E)) :
    epsOp j * matOp Ω = -(matOp Ω * epsOp j) := by
  refine ContinuousLinearMap.ext fun t => funext fun k => ?_
  have hs : ∀ s : TotFibre E, sgnTot E (dzbarTot E j * s) = -(dzbarTot E j * sgnTot E s) := by
    intro s
    have h := congrArg (fun T : FibOp E 1 => T (fun _ => s) 0) (sgnOp_epsOp (E := E) (r := 1) j)
    exact h
  simp only [mul_apply_eq_comp, neg_apply, Pi.neg_apply,
    matOp_apply]
  show dzbarTot E j * matOp Ω t k = -∑ i, sgnTot E (dzbarTot E j * t i) * Ω k i
  simp only [matOp_apply, hs, neg_mul, Finset.sum_neg_distrib, neg_neg, Finset.mul_sum,
    mul_assoc]

/-- Helper: `t ∈ Λ` is homogeneous of form degree `a ∈ ℤ` (all other components vanish). -/
private def HasDeg (a : ℤ) (t : TotFibre E) : Prop :=
  ∀ q : Fin (Module.finrank ℂ E + 1), ((q : ℕ) : ℤ) ≠ a → t q = 0

/-- Helper: `0` is homogeneous of every degree. -/
private theorem hasDeg_zero (a : ℤ) : HasDeg a (0 : TotFibre E) := fun _ _ => rfl

omit [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Helper: `ofDeg k γ` is homogeneous of degree `k`. -/
private theorem hasDeg_ofDeg (k : ℕ) (γ : DolbeaultFibre E k ℂ) :
    HasDeg (k : ℤ) (TotFibre.ofDeg k γ) := by
  intro q hq
  have h : ¬ k = (q : ℕ) := fun h => hq (by rw [h])
  show (if h : k = (q : ℕ) then DolbeaultFibre.cast h γ else 0 : DolbeaultFibre E q ℂ) = 0
  simp only [h, ↓reduceDIte]

/-- Helper: a homogeneous element of negative degree is zero. -/
private theorem eq_zero_of_hasDeg_neg {a : ℤ} (ha : a < 0) {t : TotFibre E}
    (h : HasDeg a t) : t = 0 :=
  funext fun q => h q (by omega)

omit [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Helper: the `q`-th component of `t` is `t q` for `q < n + 1`. -/
private theorem deg_of_lt' {q : ℕ} (hq : q < Module.finrank ℂ E + 1) (t : TotFibre E) :
    TotFibre.deg q t = t ⟨q, hq⟩ := by
  simp only [TotFibre.deg, LinearMap.coe_mk, AddHom.coe_mk, hq, ↓reduceDIte]

omit [FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Helper: the `q`-th component of `t` is zero for `q ≥ n + 1`. -/
private theorem deg_of_ge' {q : ℕ} (hq : ¬ q < Module.finrank ℂ E + 1) (t : TotFibre E) :
    TotFibre.deg q t = 0 := by
  simp only [TotFibre.deg, LinearMap.coe_mk, AddHom.coe_mk, hq, ↓reduceDIte]

/-- Helper: a homogeneous element of degree `p ∈ ℕ` is `ofDeg p` of its component. -/
private theorem eq_ofDeg_of_hasDeg (p : ℕ) {t : TotFibre E} (h : HasDeg (p : ℤ) t) :
    t = TotFibre.ofDeg p (TotFibre.deg p t) := by
  conv_lhs => rw [← TotFibre.sum_ofDeg_deg t]
  by_cases hp : p < Module.finrank ℂ E + 1
  · rw [Finset.sum_eq_single p]
    · intro q hq hqp
      have : TotFibre.deg q t = 0 := by
        rw [deg_of_lt' (Finset.mem_range.1 hq)]
        exact h ⟨q, Finset.mem_range.1 hq⟩ (by simpa using hqp)
      rw [this, map_zero]
    · intro hnot
      exact absurd (Finset.mem_range.2 hp) hnot
  · have h0 : TotFibre.deg p t = 0 := deg_of_ge' hp t
    rw [h0, map_zero]
    refine Finset.sum_eq_zero fun q hq => ?_
    have : TotFibre.deg q t = 0 := by
      rw [deg_of_lt' (Finset.mem_range.1 hq)]
      exact h ⟨q, Finset.mem_range.1 hq⟩ (by
        have := Finset.mem_range.1 hq
        omega)
    rw [this, map_zero]

/-- Helper: products of homogeneous elements are homogeneous, degrees add. -/
private theorem hasDeg_mul {a b : ℤ} {s t : TotFibre E} (hs : HasDeg a s) (ht : HasDeg b t) :
    HasDeg (a + b) (s * t) := by
  by_cases ha : a < 0
  · rw [eq_zero_of_hasDeg_neg ha hs, zero_mul]
    exact hasDeg_zero _
  by_cases hb : b < 0
  · rw [eq_zero_of_hasDeg_neg hb ht, mul_zero]
    exact hasDeg_zero _
  lift a to ℕ using (not_lt.1 ha)
  lift b to ℕ using (not_lt.1 hb)
  rw [eq_ofDeg_of_hasDeg a hs, eq_ofDeg_of_hasDeg b ht, TotFibre.ofDeg_mul_ofDeg]
  have := hasDeg_ofDeg (E := E) (a + b)
    (TotFibre.deg (a + b) (TotFibre.ofDeg a (TotFibre.deg a s) *
      TotFibre.ofDeg b (TotFibre.deg b t) : TotFibre E))
  push_cast at this
  exact this

/-- Helper: `σ` preserves homogeneity. -/
private theorem hasDeg_sgnTot {a : ℤ} {t : TotFibre E} (h : HasDeg a t) :
    HasDeg a (sgnTot E t) := by
  intro q hq
  show (-1 : ℂ) ^ (q : ℕ) • t q = 0
  rw [h q hq, smul_zero]

/-- Z5.h: `matOp Ω` has total degree `1` if `Ωⱼᵢ` has form degree `deg i + 1 − deg j`. -/
theorem isOfTotDeg_matOp (deg : Fin r → ℤ) {Ω : Fin r → Fin r → TotFibre E}
    (h : ∀ j i (q : Fin (Module.finrank ℂ E + 1)), ((q : ℕ) : ℤ) ≠ deg i + 1 - deg j →
      Ω j i q = 0) :
    IsOfTotDeg deg 1 (matOp Ω) := by
  intro m s hs j q hq
  have hs' : ∀ i, HasDeg (m - deg i) (s i) := fun i q' hq' => hs i q' (by omega)
  have hterm : ∀ i, HasDeg (m + 1 - deg j) (sgnTot E (s i) * Ω j i) := by
    intro i
    have := hasDeg_mul (hasDeg_sgnTot (hs' i)) (h j i : HasDeg (deg i + 1 - deg j) (Ω j i))
    have e : m - deg i + (deg i + 1 - deg j) = m + 1 - deg j := by omega
    rw [e] at this
    exact this
  refine (Finset.sum_apply (M := fun i : Fin (Module.finrank ℂ E + 1) => DolbeaultFibre E i ℂ) q
    Finset.univ (fun i => (show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from
      sgnTot E (s i) * Ω j i))).trans ?_
  exact Finset.sum_eq_zero fun i _ => hterm i q (by omega)

/-! ## Chart expressions of `σ` and `d` -/

variable {U : Opens X}

/-- Helper: a sum in `Λ` is computed componentwise. -/
private theorem totFibre_sum_apply {ι : Type} (s : Finset ι) (f : ι → TotFibre E)
    (q : Fin (Module.finrank ℂ E + 1)) : (∑ a ∈ s, f a) q = ∑ a ∈ s, f a q :=
  Finset.sum_apply (M := fun i : Fin (Module.finrank ℂ E + 1) => DolbeaultFibre E i ℂ) q s
    (fun a => (show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from f a))

/-- Helper: pointwise formula for the grade involution `σ` of the Dolbeault algebra. -/
private theorem sigma_apply_pt (α : DolbeaultAlg E U) (y : U)
    (i : Fin (Module.finrank ℂ E + 1)) :
    ((GCDga.sigma (dolbeaultGrade E U) α : DolbeaultAlg E U) : U → TotFibre E) y i =
      (-1 : ℂ) ^ (i : ℕ) • ((α : U → TotFibre E) y i) := by
  have hα : α = ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
      (projDegAlg E U (q : ℤ) α : DolbeaultAlg E U) := by
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    exact (sum_projDeg _).symm
  have key : ∀ q ∈ Finset.range (Module.finrank ℂ E + 1),
      (((GCDga.sigma (dolbeaultGrade E U) (projDegAlg E U (q : ℤ) α : DolbeaultAlg E U) :
        DolbeaultAlg E U) : U → TotFibre E) y) i =
      if (i : ℕ) = q then (-1 : ℂ) ^ (i : ℕ) • ((α : U → TotFibre E) y i) else 0 := by
    intro q _
    have hs := GCDga.sigma_of_mem (dolbeaultGrade E U) (projDegAlg E U (q : ℤ) α).2
    rw [hs, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
    show ((((q : ℤ).negOnePow : ℤ) : ℂ) • (if ((i : ℕ) : ℤ) = (q : ℤ) then
        (α : U → TotFibre E) y i else 0)) = _
    by_cases h : (i : ℕ) = q
    · subst h
      simp
    · have h' : ¬ ((i : ℕ) : ℤ) = (q : ℤ) := by exact_mod_cast h
      simp [h, h']
  conv_lhs => rw [hα, map_sum]
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, totFibre_sum_apply]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq]
  simp only [Finset.mem_range, i.2, ↓reduceIte]

omit [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Helper: the `i`-th component of a chart expression at a point of `U`. -/
private theorem chartExpr_apply_of_mem (f : U → TotFibre E) (e : OpenPartialHomeomorph X E)
    (z : E) (h : e.symm z ∈ U) (i : Fin (Module.finrank ℂ E + 1)) :
    chartExpr E f e z i =
      DolbeaultFibre.pull (chartTrans E e (e.symm z) z) (f ⟨_, h⟩ i) := by
  simp only [chartExpr, h, ↓reduceDIte]
  rfl

/-- Z5.h: the chart expression of `σ(α)` is `σ` of the chart expression of `α` (pullbacks preserve
form degrees). -/
theorem chartExpr_sigma (α : DolbeaultAlg E U) (e : OpenPartialHomeomorph X E) (z : E) :
    chartExpr E ((GCDga.sigma (dolbeaultGrade E U) α : DolbeaultAlg E U) : U → TotFibre E) e z =
      sgnTot E (chartExpr E (α : U → TotFibre E) e z) := by
  funext i
  by_cases h : e.symm z ∈ U
  · refine (chartExpr_apply_of_mem _ _ _ h i).trans ?_
    rw [sigma_apply_pt]
    show _ = (-1 : ℂ) ^ (i : ℕ) • chartExpr E (α : U → TotFibre E) e z i
    rw [chartExpr_apply_of_mem _ _ _ h i]
    rfl
  · simp only [chartExpr, h, ↓reduceDIte]
    show _ = (-1 : ℂ) ^ (i : ℕ) • (0 : DolbeaultFibre E i ℂ)
    rw [smul_zero]
    rfl

/-- Z5.h: on `frameDom U x₀`, the chart expression of `dα = ∂̄α` is `∂̄` of the chart expression of
`α` (`chartExpr_dbarSec_eq`). -/
theorem chartExpr_d {x₀ : X} (hx₀ : x₀ ∈ U) (α : DolbeaultAlg E U) {z : E}
    (hz : z ∈ frameDom E U x₀) :
    chartExpr E ((GCDga.d (𝒜 := dolbeaultGrade E U) α : DolbeaultAlg E U) : U → TotFibre E)
        (chartAt E x₀) z =
      dbarTot E (chartExpr E (α : U → TotFibre E) (chartAt E x₀)) z :=
  chartExpr_dbarSec_eq (x := ⟨x₀, hx₀⟩) α.2 hz.1 hz.2

/-! ## The frame model -/

variable {N : QuasiCohesive (dolbeaultGrade E U)} (F : GradedFrame (dolbeaultGrade E U) N.Q r)
  (x₀ : X)

/-- **Z5.h (E.2).** The chart expression of an element of the total module in the frame:
`z ↦ (chartExpr xᵢ (z))ᵢ`, in the chart `chartAt x₀`. -/
def chartCoef (x : N.T) (z : E) : Fib E r :=
  fun i => chartExpr E ((F.coefTot x i : DolbeaultAlg E U) : U → TotFibre E) (chartAt E x₀) z

/-- **Z5.h (E.2).** The transported connection: `𝒜(z) = matOp (chartExpr ωⱼᵢ (z))`, `ω` the
connection matrix of `N` in the frame (`GradedFrame.mat`). -/
def frameOp (z : E) : FibOp E r :=
  matOp fun j i => chartExpr E ((F.mat j i : DolbeaultAlg E U) : U → TotFibre E) (chartAt E x₀) z

/-- Z5.h: formula for `frameOp` (rfl). -/
theorem frameOp_apply (z : E) (t : Fib E r) (j : Fin r) :
    frameOp F x₀ z t j = ∑ i, sgnTot E (t i) *
      chartExpr E ((F.mat j i : DolbeaultAlg E U) : U → TotFibre E) (chartAt E x₀) z := rfl

/-- **Z5.h (E.2).** On `frameDom`, the chart expression of the frame vector `1 ⊗ ẽᵢ` is the unit
vector `eᵢ` (with value `1 ∈ Λ`). -/
theorem chartCoef_vec (i : Fin r) {z : E} (hz : z ∈ frameDom E U x₀) :
    chartCoef F x₀ (F.vec i) z = Pi.single i 1 := by
  funext j
  have hzU : (chartAt E x₀).symm z ∈ U := hz.2
  have h1 : ∀ a : DolbeaultAlg E U, a = 1 →
      chartExpr E (a : U → TotFibre E) (chartAt E x₀) z = 1 := by
    rintro a rfl
    simp only [chartExpr, hzU, ↓reduceDIte, Subalgebra.coe_one, Pi.one_apply, TotFibre.pull_one]
  have h0 : chartExpr E ((0 : DolbeaultAlg E U) : U → TotFibre E) (chartAt E x₀) z = 0 := by
    simp only [ZeroMemClass.coe_zero]
    exact congrFun (chartExpr_zero _) z
  show chartExpr E ((F.coefTot (F.vec i) j : DolbeaultAlg E U) : U → TotFibre E)
    (chartAt E x₀) z = (Pi.single i 1 : Fib E r) j
  rw [GradedFrame.coefTot_vec, Pi.single_apply]
  by_cases hji : j = i
  · simp only [hji, ↓reduceIte]
    exact h1 _ rfl
  · simp only [hji, ↓reduceIte]
    exact h0

/-- Helper: the chart expression of a Dolbeault form is smooth on the frame domain. -/
private theorem contDiffOn_chartExpr_frameDom (α : DolbeaultAlg E U) (x₀ : X) :
    ContDiffOn ℝ ∞ (chartExpr E (α : U → TotFibre E) (chartAt E x₀)) (frameDom E U x₀) := by
  intro z hz
  have hy : (chartAt E x₀).symm z ∈ U := hz.2
  have hs : (chartAt E x₀).symm z ∈ (chartAt E x₀).source := (chartAt E x₀).map_target hz.1
  have h := IsDolbeault.contDiffAt_chartExpr α.2 (chart_mem_atlas E x₀) ⟨_, hy⟩ hs
  have hr : (chartAt E x₀) ((chartAt E x₀).symm z) = z := (chartAt E x₀).right_inv hz.1
  exact (hr ▸ h : ContDiffAt ℝ ∞ (chartExpr E (α : U → TotFibre E) (chartAt E x₀)) z)
    |>.contDiffWithinAt

/-- **Z5.h (E.2).** The chart expression of an element of the total module is smooth on the frame
domain. -/
theorem contDiffOn_chartCoef (x : N.T) : ContDiffOn ℝ ∞ (chartCoef F x₀ x) (frameDom E U x₀) :=
  contDiffOn_pi.2 fun i => contDiffOn_chartExpr_frameDom (F.coefTot x i) x₀

omit [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Helper: `chartExpr` is additive, pointwise. -/
private theorem chartExpr_add_apply (f g : U → TotFibre E) (e : OpenPartialHomeomorph X E)
    (z : E) : chartExpr E (f + g) e z = chartExpr E f e z + chartExpr E g e z := by
  by_cases h : (e.symm z : X) ∈ U
  · simp only [chartExpr, h, ↓reduceDIte, Pi.add_apply, map_add]
  · simp only [chartExpr, h, ↓reduceDIte, add_zero]

omit [IsManifold 𝓘(ℂ, E) ∞ X] in
/-- Helper: `chartExpr` commutes with finite sums, pointwise. -/
private theorem chartExpr_sum_apply {ι : Type} (s : Finset ι) (f : ι → U → TotFibre E)
    (e : OpenPartialHomeomorph X E) (z : E) :
    chartExpr E (∑ i ∈ s, f i) e z = ∑ i ∈ s, chartExpr E (f i) e z := by
  by_cases h : (e.symm z : X) ∈ U
  · simp only [chartExpr, h, ↓reduceDIte, Finset.sum_apply, map_sum]
  · simp only [chartExpr, h, ↓reduceDIte, Finset.sum_const_zero]

/-- **Z5.h (E.2).** The sign identification: on `frameDom U x₀`,
`chartCoef (𝕏x) = ∂̄(chartCoef x) + 𝒜·(chartCoef x)`, i.e. `𝕏` is `∂̄ + 𝒜` in the chart. From
`coefTot_X`, `chartExpr_d`, `chartExpr_sigma` and `chartExpr_mul`. -/
theorem chartCoef_X {x₀ : X} (hx₀ : x₀ ∈ U) (x : N.T) {z : E} (hz : z ∈ frameDom E U x₀) :
    chartCoef F x₀ (N.X x) z =
      dbarFib (chartCoef F x₀ x) z + frameOp F x₀ z (chartCoef F x₀ x z) := by
  funext j
  show chartExpr E ((F.coefTot (N.X x) j : DolbeaultAlg E U) : U → TotFibre E)
      (chartAt E x₀) z =
    dbarTot E (chartExpr E ((F.coefTot x j : DolbeaultAlg E U) : U → TotFibre E)
      (chartAt E x₀)) z +
    ∑ i, sgnTot E (chartExpr E ((F.coefTot x i : DolbeaultAlg E U) : U → TotFibre E)
      (chartAt E x₀) z) *
      chartExpr E ((F.mat j i : DolbeaultAlg E U) : U → TotFibre E) (chartAt E x₀) z
  rw [GradedFrame.coefTot_X]
  simp only [Subalgebra.coe_add, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
  rw [chartExpr_add_apply, chartExpr_sum_apply, chartExpr_d hx₀ _ hz]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartExpr_mul, Pi.mul_apply, chartExpr_sigma]

/-- **Z5.h (E.2).** `𝒜` is smooth on the frame domain (F9.a). -/
theorem contDiffOn_frameOp : ContDiffOn ℝ ∞ (frameOp F x₀) (frameDom E U x₀) :=
  contDiffOn_matOp fun j i => contDiffOn_chartExpr_frameDom (F.mat j i) x₀

/-- **Z5.h (E.2).** `𝒜(z)` has total degree `1` (`ωⱼᵢ` has form degree `deg i + 1 − deg j`). -/
theorem isOfTotDeg_frameOp (z : E) : IsOfTotDeg F.deg 1 (frameOp F x₀ z) :=
  isOfTotDeg_matOp F.deg fun j i q hq =>
    chartExpr_support ((mem_dolbeaultGrade E).1 (F.mat_mem j i)) _ _ q hq

/-- **Z5.h (E.2).** `𝒜(z)` is odd: it anticommutes with every `εⱼ`. -/
theorem frameOp_odd (z : E) (j : Fin (Module.finrank ℂ E)) :
    epsOp j * frameOp F x₀ z = -(frameOp F x₀ z * epsOp j) :=
  matOp_odd _ j

/-- Helper: `pdbar` of a constant function is zero. -/
private theorem pdbar_const_zero' (v z : E) {c : FibOp E r} :
    pdbar v (fun _ : E => c) z = 0 := by
  unfold pdbar
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, smul_zero,
    add_zero]

/-- Helper: `pdbar` of a function anticommuting pointwise with `e` anticommutes with `e`. -/
private theorem pdbar_anticomm (e : FibOp E r) {g : E → FibOp E r} (z v : E)
    (h : ∀ w, e * g w = -(g w * e)) : e * pdbar v g z = -(pdbar v g z * e) := by
  by_cases hd : DifferentiableAt ℝ g z
  · let Φ : FibOp E r →L[ℂ] FibOp E r :=
      ContinuousLinearMap.mul ℂ (FibOp E r) e + (ContinuousLinearMap.mul ℂ (FibOp E r)).flip e
    have hΦ : ∀ T, Φ T = e * T + T * e := fun T => rfl
    have h1 := pdbar_comp_clm Φ v hd
    have h2 : (fun w => Φ (g w)) = fun _ => 0 :=
      funext fun w => by rw [hΦ, h w, neg_add_cancel]
    rw [h2, pdbar_const_zero', hΦ] at h1
    exact eq_neg_of_add_eq_zero_left h1.symm
  · have : fderiv ℝ g z = 0 := fderiv_zero_of_not_differentiableAt hd
    unfold pdbar
    rw [this]
    simp only [zero_apply, smul_zero, add_zero, mul_zero, zero_mul, neg_zero]

/-- Helper: `(-a) b = -(a b)` for fibre operators. -/
private theorem neg_mul_op' (a b : FibOp E r) : -a * b = -(a * b) :=
  ContinuousLinearMap.neg_comp a b

/-- Helper: `a (-b) = -(a b)` for fibre operators. -/
private theorem mul_neg_op' (a b : FibOp E r) : a * -b = -(a * b) :=
  ContinuousLinearMap.comp_neg a b

/-- Helper: for an odd family, every `εₖ` commutes with the Maurer–Cartan expression. -/
private theorem eps_comm_mcOp {𝒜 : E → FibOp E r}
    (hodd : ∀ w j, epsOp j * 𝒜 w = -(𝒜 w * epsOp j)) (z : E)
    (k : Fin (Module.finrank ℂ E)) : epsOp k * mcOp 𝒜 z = mcOp 𝒜 z * epsOp k := by
  have hP : ∀ j, epsOp k * pdbar (Module.finBasis ℂ E j) 𝒜 z =
      -(pdbar (Module.finBasis ℂ E j) 𝒜 z * epsOp k) :=
    fun j => pdbar_anticomm _ z _ (fun w => hodd w k)
  unfold mcOp
  rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, epsOp_mul_comm k j, neg_mul_op', mul_assoc, hP j, mul_neg_op', neg_neg,
      ← mul_assoc]
  · rw [← mul_assoc, hodd z k, neg_mul_op', mul_assoc, hodd z k, mul_neg_op', neg_neg,
      ← mul_assoc]

/-- **Z5.h (E.2).** Maurer–Cartan: `mcOp 𝒜 = 0` on the frame domain, from `𝕏² = 0` (the
curvature of `𝒜_X(U)` is `0`) applied to the frame vectors (`chartCoef_X` twice,
`dbarFib_add_sq`, `chartCoef_vec`) and the Λ-linearity of `mcOp 𝒜`. -/
theorem mcOp_frameOp {x₀ : X} (hx₀ : x₀ ∈ U) {z : E} (hz : z ∈ frameDom E U x₀) :
    mcOp (frameOp F x₀) z = 0 := by
  have hV : frameDom E U x₀ ∈ nhds z := (isOpen_frameDom E U x₀).mem_nhds hz
  have hA : ContDiffAt ℝ ∞ (frameOp F x₀) z := (contDiffOn_frameOp F x₀).contDiffAt hV
  have hodd := frameOp_odd F x₀
  have hvec : ∀ i, mcOp (frameOp F x₀) z (Pi.single i 1) = 0 := by
    intro i
    have hsm : ContDiffAt ℝ ∞ (chartCoef F x₀ (F.vec i)) z :=
      (contDiffOn_chartCoef F x₀ (F.vec i)).contDiffAt hV
    have h1 : ∀ᶠ w in nhds z, chartCoef F x₀ (N.X (F.vec i)) w =
        dbarFib (chartCoef F x₀ (F.vec i)) w +
          frameOp F x₀ w (chartCoef F x₀ (F.vec i) w) :=
      Filter.eventually_of_mem hV fun w hw => chartCoef_X F hx₀ _ hw
    have h2 : dbarFib (chartCoef F x₀ (N.X (F.vec i))) z = dbarFib (fun w =>
        dbarFib (chartCoef F x₀ (F.vec i)) w +
          frameOp F x₀ w (chartCoef F x₀ (F.vec i) w)) z :=
      funext fun k => dbarTot_congr (h1.mono fun w hw => congrFun hw k)
    have h3 := chartCoef_X F hx₀ (N.X (F.vec i)) hz
    rw [h2, h1.self_of_nhds] at h3
    have h4 : chartCoef F x₀ (N.X (N.X (F.vec i))) z = 0 := by
      have hc : GCDga.c (𝒜 := dolbeaultGrade E U) = 0 := rfl
      have h0 : ∀ k, F.coefTot (0 : N.T) k = 0 := fun k => by rw [map_zero]; rfl
      rw [N.flat, hc, zero_smul]
      funext k
      simp only [chartCoef, h0, ZeroMemClass.coe_zero]
      exact congrFun (chartExpr_zero _) z
    have h5 := dbarFib_add_sq (hA.of_le (by norm_num)) (hsm.of_le (by norm_num)) (hodd z)
    rw [chartCoef_vec F x₀ i hz] at h5
    rw [← h5]
    rw [h4] at h3
    rw [chartCoef_vec F x₀ i hz] at h3
    exact h3.symm
  have hcomm : ∀ k, epsOp k * mcOp (frameOp F x₀) z = mcOp (frameOp F x₀) z * epsOp k :=
    eps_comm_mcOp (fun w j => hodd w j) z
  refine ContinuousLinearMap.ext fun t => ?_
  have ht : t = ∑ i, (mulLeftOp (t i) : FibOp E r) (Pi.single i 1) := by
    funext k
    rw [Finset.sum_apply]
    simp only [Pi.single_apply, mulLeftOp, compOp_apply, LinearMap.mulLeft_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hz0 : ∀ i, mcOp (frameOp F x₀) z ((mulLeftOp (t i) : FibOp E r) (Pi.single i 1)) = 0 := by
    intro i
    have h := congrArg (fun T : FibOp E r => T (Pi.single i 1))
      (commute_mulLeftOp_of_eps hcomm (t i))
    simp only [mul_apply_eq_comp, hvec i, map_zero] at h
    exact h.symm
  rw [zero_apply]
  conv_lhs => rw [ht]
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => hz0 i

/-- **Z5.h (E.2).** The frame model is a flat ∂̄-superconnection on the frame domain, the input of
the gauge induction `exists_gauge_holomorphic` (Z5.f). -/
theorem isFlatSuperconn_frameOp {x₀ : X} (hx₀ : x₀ ∈ U) :
    IsFlatSuperconn F.deg (frameDom E U x₀) (frameOp F x₀) where
  smooth := contDiffOn_frameOp F x₀
  deg_one z _ := isOfTotDeg_frameOp F x₀ z
  odd z _ := frameOp_odd F x₀ z
  flat _ hz := mcOp_frameOp F hx₀ hz

/-- **Z5.h (E.2).** If `U` lies in the chart source, an element of the total module is determined
by its chart expression on the frame domain (`eq_of_chartExpr_eq`, `ext_coefTot`). -/
theorem eq_of_chartCoef_eq (hU : (U : Set X) ⊆ (chartAt E x₀).source) {x y : N.T}
    (h : ∀ z ∈ frameDom E U x₀, chartCoef F x₀ x z = chartCoef F x₀ y z) : x = y := by
  refine F.ext_coefTot fun i => Subtype.ext (funext fun y' => ?_)
  have hs : (y' : X) ∈ (chartAt E x₀).source := hU y'.2
  have hz : chartAt E x₀ y' ∈ frameDom E U x₀ :=
    ⟨(chartAt E x₀).map_source hs, by
      show (chartAt E x₀).symm (chartAt E x₀ y') ∈ (U : Set X)
      rw [(chartAt E x₀).left_inv hs]
      exact y'.2⟩
  exact eq_of_chartExpr_eq (chart_mem_atlas E x₀) y' hs (congrFun (h _ hz) i)

end Cohesive
