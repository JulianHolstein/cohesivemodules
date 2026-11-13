import Cohesivemodules.Forms.DolbeaultFree

set_option linter.style.header false

/-!
# F10–F12: gluing, fineness, local freeness, and `0 → O → 𝒜⁰ → 𝒜¹` (part 3 of 3)

Split from `Forms/Dolbeault.lean` for size;
continues `Forms/DolbeaultFree.lean`.
-/

noncomputable section
namespace Cohesive
open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
attribute [local instance] isManifold_real contMDiffRing_real_complex

/-! ## F12: `0 → O → 𝒜⁰ → 𝒜¹` -/

/-! ## F12 helpers -/

/-- Components of `c • 1` in positive degree vanish. -/
private theorem smul_one_apply_ne (c : ℂ) (j : Fin (Module.finrank ℂ E + 1))
    (hj : (j : ℕ) ≠ 0) :
    (c • (1 : TotFibre E)) j = 0 := by
  rw [← ofDeg0_eq_smul_one]
  show (if h : 0 = (j : ℕ) then DolbeaultFibre.cast h (form0Equiv E ℂ c) else 0) = 0
  simp only [Ne.symm hj, ↓reduceDIte]

/-- The degree-`0` component of `c • 1` is the constant `0`-form `c`. -/
private theorem smul_one_apply_zero (c : ℂ) (h : 0 < Module.finrank ℂ E + 1) :
    ((c • (1 : TotFibre E)) ⟨0, h⟩ : DolbeaultFibre E 0 ℂ) = form0Equiv E ℂ c := by
  rw [← ofDeg0_eq_smul_one]
  show (if h : 0 = ((⟨0, h⟩ : Fin (Module.finrank ℂ E + 1)) : ℕ) then
    DolbeaultFibre.cast h (form0Equiv E ℂ c) else 0) = _
  simp only [↓reduceDIte, DolbeaultFibre.cast_rfl]

/-- `∂̄` of `c • 1` vanishes where `c` is complex-differentiable (F8, ⇐). -/
private theorem dbarTot_smul_one (c : E → ℂ) (z : E) (hc : DifferentiableAt ℂ c z) :
    dbarTot E (fun w ↦ c w • (1 : TotFibre E)) z = 0 := by
  unfold dbarTot
  refine Finset.sum_eq_zero fun q _ ↦ ?_
  by_cases hq : (q : ℕ) = 0
  · obtain ⟨k, hk⟩ := q
    simp only at hq
    subst hq
    have : (fun w ↦ ((c w • (1 : TotFibre E)) ⟨0, hk⟩ : DolbeaultFibre E 0 ℂ)) = form0 c :=
      funext fun w ↦ smul_one_apply_zero E (c w) hk
    show TotFibre.ofDeg (0 + 1) (dbar (fun w ↦ ((c w • (1 : TotFibre E)) ⟨0, hk⟩ :
      DolbeaultFibre E 0 ℂ)) z) = 0
    rw [this, (dbar_form0_eq_zero_iff (hc.restrictScalars ℝ)).2 (by
      rw [hc.fderiv_restrictScalars ℝ]; exact antiPart_restrictScalars _), map_zero]
  · have : (fun w ↦ ((c w • (1 : TotFibre E)) q : DolbeaultFibre E q ℂ)) = fun _ ↦ 0 :=
      funext fun w ↦ smul_one_apply_ne E (c w) q hq
    rw [this, dbar_zero_fn, map_zero]

open Classical in
/-- A holomorphic function is complex-smooth in every chart. -/
private theorem contDiffAt_chart_comp {U : Opens X} (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, ℂ), ℂ⟯)
    (e : OpenPartialHomeomorph X E) (he : e ∈ atlas E X) {x : U} (hx : (x : X) ∈ e.source) :
    ContDiffAt ℂ ∞ (fun z ↦ if h : e.symm z ∈ U then f ⟨e.symm z, h⟩ else 0) (e x) := by
  classical
  let f' : X → ℂ := fun y ↦ if h : y ∈ U then f ⟨y, h⟩ else 0
  have hf' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ f' (x : X) := by
    have h1 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (fun y : U ↦ f' y) x := by
      have : (fun y : U ↦ f' y) = f := by
        funext y
        simp only [f', y.2, ↓reduceDIte]
      rw [this]
      exact f.contMDiff x
    exact contMDiffAt_subtype_iff.1 h1
  have hex : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e.symm (e x) :=
    (contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓘(ℂ, E)) (n := ∞)
      (StructureGroupoid.subset_maximalAtlas _ he)).contMDiffAt
      (e.open_target.mem_nhds (e.map_source hx))
  have hsymm : e.symm (e x) = x := e.left_inv hx
  have hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (f' ∘ e.symm) (e x) := by
    refine ContMDiffAt.comp (e x) ?_ hex
    rw [hsymm]
    exact hf'
  exact hg.contDiffAt

/-- Converse of `dbarTot_smul_one` at a point of real differentiability. -/
private theorem antiPart_eq_zero_of_dbarTot (c : E → ℂ) (w : E) (hc : DifferentiableAt ℝ c w)
    (h : dbarTot E (fun w ↦ c w • (1 : TotFibre E)) w = 0) :
    antiPart (fderiv ℝ c w) = 0 := by
  by_cases hn : 1 ≤ Module.finrank ℂ E
  · have h1 := congrArg (TotFibre.deg 1) h
    unfold dbarTot at h1
    rw [map_sum, Finset.sum_eq_single ⟨0, by omega⟩] at h1
    · have h2 : (fun w ↦ ((c w • (1 : TotFibre E)) ⟨0, by omega⟩ : DolbeaultFibre E 0 ℂ)) =
          form0 c := funext fun w ↦ smul_one_apply_zero E (c w) _
      rw [TotFibre.deg_ofDeg_self hn, h2] at h1
      rw [← dbar_form0_eq_zero_iff hc]
      rw [map_zero] at h1
      exact h1
    · intro q _ hq
      refine TotFibre.deg_ofDeg_ne ?_ _
      intro hc'
      exact hq (Fin.ext (by simpa using hc'.symm))
    · intro hr
      exact absurd (Finset.mem_univ _) hr
  · have hz : Module.finrank ℂ E = 0 := by omega
    have : Subsingleton E := Module.finrank_zero_iff.1 hz
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have h0 : Conj.ofConj v = 0 := Subsingleton.elim _ _
    simp only [antiPart_apply, h0, smul_zero, map_zero, add_zero, zero_apply]

open Classical in
/-- F8 (⇒) globally: a `0`-form `f0` with `∂̄ = 0` is complex `C^∞`. -/
private theorem contMDiff_of_dbarSec_funForm {U : Opens X} (f0 : U → ℂ)
    (hα : IsDolbeault E (funForm E f0)) (hd : dbarSec E (funForm E f0) = 0) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ f0 := by
  obtain ⟨φ, hφ1, -⟩ := exists_coef0 (E := E)
  set cE : OpenPartialHomeomorph X E → E → ℂ :=
    fun e z ↦ if h : e.symm z ∈ U then f0 ⟨e.symm z, h⟩ else 0 with hcE
  have hexpr : ∀ e, chartExpr E (funForm E f0) e = fun z ↦ cE e z • (1 : TotFibre E) :=
    fun e ↦ funext (chartExpr_funForm E f0 e)
  have hcφ : ∀ e z, cE e z = φ (chartExpr E (funForm E f0) e z) := fun e z ↦ by
    rw [hexpr]; exact (hφ1 _).symm
  have hR : ∀ e ∈ atlas E X, ∀ z ∈ e.target, e.symm z ∈ U → ContDiffAt ℝ ∞ (cE e) z := by
    intro e he z hz hzU
    have h1 := hα.contDiffAt_chartExpr he ⟨e.symm z, hzU⟩ (e.map_target hz)
    have h2 : e ((⟨e.symm z, hzU⟩ : U) : X) = z := e.right_inv hz
    rw [h2] at h1
    have : cE e = fun z ↦ φ (chartExpr E (funForm E f0) e z) := funext (hcφ e)
    rw [this]
    exact (φ.restrictScalars ℝ).contDiff.contDiffAt.comp z h1
  have hanti : ∀ y : U,
      antiPart (fderiv ℝ (cE (chartAt E (y : X))) (chartAt E (y : X) y)) = 0 := by
    intro y
    have hy : dbarTot E (chartExpr E (funForm E f0) (chartAt E (y : X)))
      (chartAt E (y : X) y) = 0 := congrFun hd y
    rw [hexpr] at hy
    refine antiPart_eq_zero_of_dbarTot E _ _ ?_ hy
    refine (hR _ (chart_mem_atlas E (y : X)) _ (mem_chart_target E (y : X)) ?_).differentiableAt
      (by simp)
    rw [(chartAt E (y : X)).left_inv (mem_chart_source E (y : X))]
    exact y.2
  have hC : ∀ e ∈ atlas E X, ∀ z ∈ e.target, e.symm z ∈ U → DifferentiableAt ℂ (cE e) z := by
    intro e he z hz hzU
    set y : U := ⟨e.symm z, hzU⟩ with hy
    set e' := chartAt E (y : X) with he'
    have hyz : e' (y : X) = e' (e.symm z) := rfl
    have hdiff : DifferentiableAt ℝ (cE e') (e' y) :=
      (hR e' (chart_mem_atlas E (y : X)) _ (mem_chart_target E (y : X)) (by
        rw [e'.left_inv (mem_chart_source E (y : X))]; exact y.2)).differentiableAt (by simp)
    obtain ⟨T, hT⟩ := (antiPart_eq_zero_iff _).1 (hanti y)
    have hD' : DifferentiableAt ℂ (cE e') (e' y) :=
      (differentiableAt_iff_restrictScalars ℝ hdiff).2 ⟨T, hT⟩
    have hmem : z ∈ (e.symm.trans e').source :=
      mem_transition_source.2 ⟨hz, mem_chart_source E (y : X)⟩
    have hτ : DifferentiableAt ℂ (e' ∘ e.symm) z :=
      ((contDiffOn_atlas_transition he (chart_mem_atlas E (y : X))).contDiffAt
        ((e.symm.trans e').open_source.mem_nhds hmem)).differentiableAt (by norm_num)
    have heq : cE e =ᶠ[nhds z] cE e' ∘ (e' ∘ e.symm) := by
      filter_upwards [(e.symm.trans e').open_source.mem_nhds hmem] with w hw
      obtain ⟨-, hw2⟩ := mem_transition_source.1 hw
      simp only [hcE, Function.comp_apply, e'.left_inv hw2]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    exact DifferentiableAt.comp z hD' hτ
  have hV : ∀ e : OpenPartialHomeomorph X E, IsOpen (e.target ∩ e.symm ⁻¹' (U : Set X)) :=
    fun e ↦ e.continuousOn_symm.isOpen_inter_preimage e.open_target U.isOpen
  have hD : ∀ e ∈ atlas E X, ContDiffOn ℂ ∞ (cE e) (e.target ∩ e.symm ⁻¹' (U : Set X)) := by
    intro e he
    have hreal : ContDiffOn ℝ ∞ (cE e) (e.target ∩ e.symm ⁻¹' (U : Set X)) :=
      fun z hz ↦ (hR e he z hz.1 hz.2).contDiffWithinAt
    refine (dbar_eq_zero_iff_contDiffOn (hV e) hreal).1 fun z hz ↦ ?_
    have hz' := (hreal.contDiffAt ((hV e).mem_nhds hz)).differentiableAt (by simp)
    rw [dbar_form0_eq_zero_iff hz', (hC e he z hz.1 hz.2).fderiv_restrictScalars ℝ]
    exact antiPart_restrictScalars _
  intro x
  set e := chartAt E (x : X) with he
  let f' : X → ℂ := fun y ↦ if h : y ∈ U then f0 ⟨y, h⟩ else 0
  have hf0 : f0 = fun y : U ↦ f' y := by
    funext y
    simp only [f', y.2, ↓reduceDIte]
  rw [hf0]
  refine contMDiffAt_subtype_iff.2 ?_
  have hxs : (x : X) ∈ e.source := mem_chart_source E (x : X)
  have hxU : e.symm (e x) ∈ U := by rw [e.left_inv hxs]; exact x.2
  have hcd : ContDiffAt ℂ ∞ (cE e) (e x) :=
    (hD e (chart_mem_atlas E (x : X))).contDiffAt ((hV e).mem_nhds ⟨e.map_source hxs, hxU⟩)
  have hes : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e x :=
    (contMDiffOn_of_mem_maximalAtlas (I := 𝓘(ℂ, E)) (n := ∞)
      (StructureGroupoid.subset_maximalAtlas _ (chart_mem_atlas E (x : X)))).contMDiffAt
      (e.open_source.mem_nhds hxs)
  refine (hcd.contMDiffAt.comp (x : X) hes).congr_of_eventuallyEq ?_
  filter_upwards [e.open_source.mem_nhds hxs] with y hy
  simp only [f', hcE, Function.comp_apply, e.left_inv hy]


/-- **F12.** `ρ_U : O_X(U) → 𝒜⁰(U)` is injective. -/
theorem dolbeaultRhoU_injective (U : Opens X) : Function.Injective (dolbeaultRhoU E U) := by
  intro f g hfg
  have h1 := congrArg (fun a : ↥(dolbeaultGrade E U 0) ↦
    ((a : DolbeaultAlg E U) : U → TotFibre E)) hfg
  refine ContMDiffMap.ext (f := holSec E f) (g := holSec E g) fun y ↦ ?_
  have h3 := congrArg (TotFibre.deg 0) (congrFun h1 y)
  simp only [coe_dolbeaultRhoU, funForm, TotFibre.deg_ofDeg_self (Nat.zero_le _)] at h3
  exact (form0Equiv E ℂ).injective h3

open Classical in
/-- **F12** (`d ∘ ρ = 0`). [B, §4]. `∂̄` of a holomorphic function is `0` (F8, ⇐). -/
theorem dbar_dolbeaultRhoU (U : Opens X) (f : (holSheaf E X).obj.obj (op U)) :
    GCDga.d (𝒜 := dolbeaultGrade E U) (dolbeaultRhoU E U f : DolbeaultAlg E U) = 0 := by
  refine Subtype.ext (funext fun x ↦ ?_)
  show dbarSec E (funForm E (holSec E f)) x = 0
  unfold dbarSec
  have h1 : chartExpr E (funForm E (holSec E f)) (chartAt E (x : X)) =
      fun w ↦ (if h : (chartAt E (x : X)).symm w ∈ U then holSec E f
        ⟨(chartAt E (x : X)).symm w, h⟩ else 0) • (1 : TotFibre E) :=
    funext (chartExpr_funForm E _ _)
  rw [h1]
  refine dbarTot_smul_one E _ _ ?_
  exact (contDiffAt_chart_comp E (holSec E f) _ (chart_mem_atlas E (x : X))
    (mem_chart_source E (x : X))).differentiableAt (by simp)

/-- **F12** (exactness at `𝒜⁰`). [B, §4]. A form of degree `0` on `U` with `∂̄α = 0` is a
holomorphic function (F8, ⇒: Cauchy–Riemann in each chart). With `dolbeaultRhoU_injective` and
`dbar_dolbeaultRhoU`: `0 → O_X(U) → 𝒜⁰(U) → 𝒜¹(U)` is exact for every open `U`. -/
theorem exists_dolbeaultRhoU_of_dbar_eq_zero {U : Opens X} (α : dolbeaultGrade E U 0)
    (hα : GCDga.d (𝒜 := dolbeaultGrade E U) (α : DolbeaultAlg E U) = 0) :
    ∃ f : (holSheaf E X).obj.obj (op U), dolbeaultRhoU E U f = α := by
  obtain ⟨φ, -, hφ2⟩ := exists_coef0 (E := E)
  have hfun : ((α : DolbeaultAlg E U) : U → TotFibre E) = funForm E fun y ↦ φ (α.1.1 y) :=
    funext fun y ↦ (hφ2 _ (α.2 y)).trans (ofDeg0_eq_smul_one E _).symm
  have hdb : dbarSec E ((α : DolbeaultAlg E U) : U → TotFibre E) = 0 :=
    congrArg (fun a : DolbeaultAlg E U ↦ (a : U → TotFibre E)) hα
  have hcm := contMDiff_of_dbarSec_funForm E (fun y : U ↦ φ (α.1.1 y))
    (by rw [← hfun]; exact α.1.2) (by rw [← hfun]; exact hdb)
  refine ⟨(⟨fun y : U ↦ φ (α.1.1 y), hcm⟩ : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, ℂ), ℂ⟯), ?_⟩
  exact Subtype.ext (Subtype.ext hfun.symm)

end Cohesive
