import Cohesivemodules.Forms.DolbeaultFine

set_option linter.style.header false

/-!
# F10–F12: gluing, fineness, local freeness, and `0 → O → 𝒜⁰ → 𝒜¹` (part 2 of 3)

Split from `Forms/Dolbeault.lean` for size;
continues `Forms/DolbeaultFine.lean`.
-/

noncomputable section
namespace Cohesive
open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
attribute [local instance] isManifold_real contMDiffRing_real_complex

/-- The coefficient of `1` is a continuous linear map, and detects degree-`0` elements. -/
theorem exists_coef0 : ∃ φ : TotFibre E →L[ℂ] ℂ, (∀ c : ℂ, φ (c • 1) = c) ∧
    ∀ t : TotFibre E, (∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ 0 → t i = 0) →
      t = φ t • 1 := by
  let L : TotFibre E →ₗ[ℂ] ℂ :=
    (form0Equiv E ℂ).symm.toLinearEquiv.toLinearMap ∘ₗ TotFibre.deg 0
  have hL : ∀ t, L t = (form0Equiv E ℂ).symm (TotFibre.deg 0 t) := fun t ↦ rfl
  refine ⟨LinearMap.toContinuousLinearMap L, fun c ↦ ?_, fun t ht ↦ ?_⟩
  · show L (c • 1) = c
    rw [hL, ← ofDeg0_eq_smul_one, TotFibre.deg_ofDeg_self (Nat.zero_le _)]
    exact (form0Equiv E ℂ).symm_apply_apply c
  · show t = L t • 1
    rw [hL, ← ofDeg0_eq_smul_one, LinearIsometryEquiv.apply_symm_apply]
    funext i
    by_cases hi : (i : ℕ) = 0
    · obtain ⟨k, hk⟩ := i
      simp only at hi
      subst hi
      have h1 : (TotFibre.deg 0 t : DolbeaultFibre E 0 ℂ) = t ⟨0, hk⟩ := by
        simp only [TotFibre.deg, LinearMap.coe_mk, AddHom.coe_mk, hk, ↓reduceDIte]
      rw [h1]
      show _ = (if h : 0 = ((⟨0, hk⟩ : Fin (Module.finrank ℂ E + 1)) : ℕ) then
        DolbeaultFibre.cast h (t ⟨0, hk⟩) else 0)
      simp only [↓reduceDIte, DolbeaultFibre.cast_rfl]
    · rw [ht i (by exact_mod_cast hi)]
      show _ = (if h : 0 = (i : ℕ) then DolbeaultFibre.cast h (TotFibre.deg 0 t) else 0)
      simp only [Ne.symm hi, ↓reduceDIte]

/-- Transition maps are complex-differentiable at points of their domain. -/
theorem differentiableAt_transition {e e' : OpenPartialHomeomorph X E}
    (he : e ∈ atlas E X) (he' : e' ∈ atlas E X) {z : E} (hz : z ∈ e.target)
    (h : e.symm z ∈ e'.source) : DifferentiableAt ℂ (e' ∘ e.symm) z :=
  ((contDiffOn_atlas_transition he he').contDiffAt
    ((e.symm.trans e').open_source.mem_nhds (mem_transition_source.2 ⟨hz, h⟩))
    ).differentiableAt (by norm_num)

/-- The cocycle (chain) rule for derivatives of transition maps. -/
theorem fderiv_transition_cocycle {e e' e'' : OpenPartialHomeomorph X E}
    (he : e ∈ atlas E X) (he' : e' ∈ atlas E X) (he'' : e'' ∈ atlas E X) {z : E}
    (hz : z ∈ e.target) (h1 : e.symm z ∈ e'.source) (h2 : e.symm z ∈ e''.source) :
    fderiv ℂ (e'' ∘ e.symm) z =
      (fderiv ℂ (e'' ∘ e'.symm) (e' (e.symm z))).comp (fderiv ℂ (e' ∘ e.symm) z) := by
  have hg := differentiableAt_transition E he he' hz h1
  have hh : DifferentiableAt ℂ (e'' ∘ e'.symm) (e' (e.symm z)) :=
    differentiableAt_transition E he' he'' (e'.map_source h1) (by rw [e'.left_inv h1]; exact h2)
  have heq : (e'' ∘ e.symm) =ᶠ[nhds z] (e'' ∘ e'.symm) ∘ (e' ∘ e.symm) := by
    filter_upwards [(e.symm.trans e').open_source.mem_nhds
      (mem_transition_source.2 ⟨hz, h1⟩)] with w hw
    obtain ⟨-, hw2⟩ := mem_transition_source.1 hw
    simp only [Function.comp_apply, e'.left_inv hw2]
  rw [heq.fderiv_eq]
  exact fderiv_comp z hh hg

/-- The derivative of a transition map composed with the inverse transition map is the
identity. -/
theorem fderiv_transition_inv {e e' : OpenPartialHomeomorph X E}
    (he : e ∈ atlas E X) (he' : e' ∈ atlas E X) {z : E}
    (hz : z ∈ e.target) (h1 : e.symm z ∈ e'.source) :
    (fderiv ℂ (e ∘ e'.symm) (e' (e.symm z))).comp (fderiv ℂ (e' ∘ e.symm) z) =
      ContinuousLinearMap.id ℂ E := by
  have h := fderiv_transition_cocycle E he he' he hz h1 (e.map_target hz)
  rw [← h]
  have : (e ∘ e.symm) =ᶠ[nhds z] id := by
    filter_upwards [e.open_target.mem_nhds hz] with w hw
    exact e.right_inv hw
  rw [this.fderiv_eq, fderiv_id]

/-- The frame forms `y ↦ pull (D(e0 ∘ φ_y⁻¹)(φ_y y)) ε` are Dolbeault forms on `U ⊆ e0.source`. -/
private theorem isDolbeault_frame {e0 : OpenPartialHomeomorph X E} (he0 : e0 ∈ atlas E X)
    (U : Opens X) (hU : (U : Set X) ⊆ e0.source) (ε : TotFibre E) :
    IsDolbeault E (fun y : U ↦ TotFibre.pull (fderiv ℂ (e0 ∘ (chartAt E (y : X)).symm)
      (chartAt E (y : X) y)) ε) := by
  intro x'
  set e' := chartAt E (x' : X) with he'
  have he'a : e' ∈ atlas E X := chart_mem_atlas E (x' : X)
  have hV : IsOpen (e'.target ∩ e'.symm ⁻¹' (U : Set X)) :=
    e'.continuousOn_symm.isOpen_inter_preimage e'.open_target U.isOpen
  have hx's : (x' : X) ∈ e'.source := mem_chart_source E (x' : X)
  have hz0 : e' x' ∈ e'.target ∩ e'.symm ⁻¹' (U : Set X) :=
    ⟨e'.map_source hx's, by rw [Set.mem_preimage, e'.left_inv hx's]; exact x'.2⟩
  have hcongr : ∀ z ∈ e'.target ∩ e'.symm ⁻¹' (U : Set X),
      chartExpr E (fun y : U ↦ TotFibre.pull (fderiv ℂ (e0 ∘ (chartAt E (y : X)).symm)
        (chartAt E (y : X) y)) ε) e' z =
        TotFibre.pull (fderiv ℂ (e0 ∘ e'.symm) z) ε := by
    intro z hz
    have hzU : e'.symm z ∈ U := hz.2
    rw [chartExpr, dif_pos hzU]
    have hcoc := fderiv_transition_cocycle E he'a (chart_mem_atlas E (e'.symm z)) he0 hz.1
      (mem_chart_source E _) (hU hzU)
    show TotFibre.pull (chartTrans E e' (e'.symm z) z) (TotFibre.pull (fderiv ℂ (e0 ∘
      (chartAt E (e'.symm z)).symm) (chartAt E (e'.symm z) (e'.symm z))) ε) = _
    rw [TotFibre.pull_pull, hcoc]
    rfl
  have hon := contDiffOn_atlas_transition he'a he0
  have hs := (e'.symm.trans e0).open_source
  have hw : e' x' ∈ (e'.symm.trans e0).source :=
    mem_transition_source.2 ⟨hz0.1, hU hz0.2⟩
  have hD : ContDiffAt ℝ ∞ (fderiv ℂ (e0 ∘ e'.symm)) (e' x') :=
    ((hon.fderiv_of_isOpen hs (m := ∞) (by simp)).contDiffAt (hs.mem_nhds hw)).restrict_scalars ℝ
  have h1 := contDiffAt_totPull (contDiffAt_const (c := ε)) hD
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hV.mem_nhds hz0] with z hz
  exact hcongr z hz

/-- A degree-`q` element of the total fibre is `ofDeg q` of its degree-`q` component. -/
theorem eq_ofDeg_deg_aux (q : ℕ) (t : TotFibre E)
    (ht : ∀ i : Fin (Module.finrank ℂ E + 1), (i : ℕ) ≠ q → t i = 0) :
    t = TotFibre.ofDeg q (TotFibre.deg q t) := by
  funext i
  by_cases hi : (i : ℕ) = q
  · obtain ⟨k, hk⟩ := i
    simp only at hi
    subst hi
    have h1 : (TotFibre.deg k t : DolbeaultFibre E k ℂ) = t ⟨k, hk⟩ := by
      simp only [TotFibre.deg, LinearMap.coe_mk, AddHom.coe_mk, hk, ↓reduceDIte]
    rw [h1]
    show _ = (if h : k = ((⟨k, hk⟩ : Fin (Module.finrank ℂ E + 1)) : ℕ) then
      DolbeaultFibre.cast h (t ⟨k, hk⟩) else 0)
    simp only [↓reduceDIte, DolbeaultFibre.cast_rfl]
  · rw [ht i hi]
    show _ = (if h : q = (i : ℕ) then DolbeaultFibre.cast h (TotFibre.deg q t) else 0)
    simp only [Ne.symm hi, ↓reduceDIte]

/-- Pointwise linear algebra of the local frame `pull S (dz̄_I)`. -/
private theorem frame_coeffs_aux (q : ℕ)
    (B : Module.Basis {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} ℂ
      (DolbeaultFibre E q ℂ))
    (T S : E →L[ℂ] E) (hST : S.comp T = ContinuousLinearMap.id ℂ E)
    (hTS : T.comp S = ContinuousLinearMap.id ℂ E) (t : TotFibre E)
    (ht : ∀ i : Fin (Module.finrank ℂ E + 1), (i : ℕ) ≠ q → t i = 0) :
    (t = ∑ I, B.repr (TotFibre.deg q (TotFibre.pull T t)) I •
        TotFibre.pull S (TotFibre.ofDeg q (B I))) ∧
    ∀ c' : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} → ℂ,
      t = ∑ I, c' I • TotFibre.pull S (TotFibre.ofDeg q (B I)) →
        c' = fun I ↦ B.repr (TotFibre.deg q (TotFibre.pull T t)) I := by
  have hq : ∀ I : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q},
      q ≤ Module.finrank ℂ E := fun I ↦ by
    have := Finset.card_le_univ I.1
    rwa [I.2, Fintype.card_fin] at this
  have hTt := eq_ofDeg_deg_aux E q t ht
  constructor
  · by_cases hn : q ≤ Module.finrank ℂ E
    · have h1 : TotFibre.pull T t =
          TotFibre.ofDeg q (DolbeaultFibre.pull T (TotFibre.deg q t)) := by
        conv_lhs => rw [hTt]
        exact TotFibre.pull_ofDeg T _
      have h2 : TotFibre.deg q (TotFibre.pull T t) = DolbeaultFibre.pull T (TotFibre.deg q t) := by
        rw [h1]; exact TotFibre.deg_ofDeg_self hn _
      have h3 : TotFibre.pull T t = TotFibre.ofDeg q (TotFibre.deg q (TotFibre.pull T t)) := by
        rw [h2]; exact h1
      have h4 : TotFibre.pull S (TotFibre.pull T t) = t := by
        rw [TotFibre.pull_pull, hTS]; rfl
      calc t = TotFibre.pull S (TotFibre.pull T t) := h4.symm
        _ = TotFibre.pull S (TotFibre.ofDeg q (TotFibre.deg q (TotFibre.pull T t))) := by
          rw [← h3]
        _ = _ := by
          rw [show TotFibre.ofDeg q (TotFibre.deg q (TotFibre.pull T t)) = TotFibre.ofDeg q
            (∑ I, B.repr (TotFibre.deg q (TotFibre.pull T t)) I • B I) from by
              rw [B.sum_repr]]
          simp only [map_sum, map_smul]
    · have hI : IsEmpty {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} :=
        ⟨fun I ↦ hn (hq I)⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      funext i
      exact ht i (by have := i.2; omega)
  · intro c' hc'
    funext I
    have h1 : TotFibre.pull T t = ∑ J, c' J • TotFibre.ofDeg q (B J) := by
      rw [hc']
      simp only [map_sum, map_smul, TotFibre.pull_pull, hST]
      rfl
    have h2 : TotFibre.deg q (TotFibre.pull T t) = ∑ J, c' J • B J := by
      rw [h1]
      simp only [map_sum, map_smul]
      exact Finset.sum_congr rfl fun J _ ↦ by rw [TotFibre.deg_ofDeg_self (hq J)]
    rw [h2]
    exact (congrFun (B.repr_sum_self c') I).symm


/-- **F11.** [B, §4], [A, §7.1]. `𝒜^{0,q}` is locally free of rank `C(n, q)` over `𝒜⁰`: every
point has an open neighbourhood `U` with forms `e_I` of degree `q` (`I ⊆ {0, …, n-1}`,
`|I| = q`; `dz̄_I` in a chart, F2.c) such that on every open `V ≤ U` every form `β` of degree `q`
is uniquely `Σ_I f_I · e_I|V` with `f_I` of degree `0`. -/
theorem dolbeault_locallyFree (q : ℕ) (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U)
      (e : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} → dolbeaultGrade E U q),
      ∀ (V : Opens X) (h : V ≤ U), ∀ β ∈ dolbeaultGrade E V q,
        ∃! f : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} → dolbeaultGrade E V 0,
          β = ∑ I, (f I : DolbeaultAlg E V) * (dolbeaultRes E h).toAlgHom (e I) := by
  classical
  set e0 := chartAt E x with he0
  have he0a : e0 ∈ atlas E X := chart_mem_atlas E x
  let U : Opens X := ⟨e0.source, e0.open_source⟩
  have hU : (U : Set X) ⊆ e0.source := fun _ h ↦ h
  let B : Module.Basis {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} ℂ
    (DolbeaultFibre E q ℂ) := dzbarBasis (Module.finBasis ℂ E) q
  let Sfn : X → (E →L[ℂ] E) := fun y ↦
    fderiv ℂ (e0 ∘ (chartAt E y).symm) (chartAt E y y)
  let Tfn : X → (E →L[ℂ] E) := fun y ↦ chartTrans E e0 y (e0 y)
  have hST : ∀ y ∈ e0.source, (Sfn y).comp (Tfn y) = ContinuousLinearMap.id ℂ E := by
    intro y hy
    have := fderiv_transition_inv E he0a (chart_mem_atlas E y) (e0.map_source hy)
      (by rw [e0.left_inv hy]; exact mem_chart_source E y)
    rw [e0.left_inv hy] at this
    exact this
  have hTS : ∀ y ∈ e0.source, (Tfn y).comp (Sfn y) = ContinuousLinearMap.id ℂ E := by
    intro y hy
    have hya := (chartAt E y).map_source (mem_chart_source E y)
    have := fderiv_transition_inv E (chart_mem_atlas E y) he0a hya
      (by rw [(chartAt E y).left_inv (mem_chart_source E y)]; exact hy)
    rw [(chartAt E y).left_inv (mem_chart_source E y)] at this
    exact this
  have hxU : x ∈ U := mem_chart_source E x
  have hfd : ∀ I, IsDolbeault E (fun y : U ↦ TotFibre.pull (Sfn y) (TotFibre.ofDeg q (B I))) :=
    fun I ↦ isDolbeault_frame E he0a U hU _
  have hfdeg : ∀ I, IsOfDegree E (q : ℤ)
      (fun y : U ↦ TotFibre.pull (Sfn y) (TotFibre.ofDeg q (B I))) := by
    intro I y i hi
    show TotFibre.pull (Sfn y) (TotFibre.ofDeg q (B I)) i = 0
    rw [TotFibre.pull_ofDeg]
    exact ofDeg_apply_ne _ i hi
  let eI : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} → dolbeaultGrade E U q :=
    fun I ↦ ⟨⟨_, hfd I⟩, hfdeg I⟩
  refine ⟨U, hxU, eI, ?_⟩
  intro V hVU β hβ
  obtain ⟨φ, hφ1, hφ2⟩ := exists_coef0 (E := E)
  let ℓ : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} → TotFibre E →L[ℂ] ℂ := fun I ↦
    LinearMap.toContinuousLinearMap (B.coord I ∘ₗ TotFibre.deg q)
  have hℓ : ∀ I t, ℓ I t = B.repr (TotFibre.deg q t) I := fun I t ↦ rfl
  have hβd : IsOfDegree E (q : ℤ) (β : V → TotFibre E) := hβ
  have hβdol : IsDolbeault E (β : V → TotFibre E) := β.2
  have hVs : ∀ y : V, (y : X) ∈ e0.source := fun y ↦ hVU y.2
  have hce : ∀ y : V, chartExpr E (β : V → TotFibre E) e0 (e0 y) =
      TotFibre.pull (Tfn y) ((β : V → TotFibre E) y) := fun y ↦
    chartExpr_of_symm_eq _ e0 (e0.left_inv (hVs y)) y.2
  let cfun : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} → V → ℂ := fun I y ↦
    ℓ I (chartExpr E (β : V → TotFibre E) e0 (e0 y))
  have hdolf : ∀ I, IsDolbeault E (funForm E (cfun I)) := by
    intro I x'
    set e' := chartAt E (x' : X) with he'
    have he'a : e' ∈ atlas E X := chart_mem_atlas E (x' : X)
    have hx's : (x' : X) ∈ e'.source := mem_chart_source E (x' : X)
    have hV : IsOpen (e'.target ∩ e'.symm ⁻¹' (V : Set X)) :=
      e'.continuousOn_symm.isOpen_inter_preimage e'.open_target V.isOpen
    have hz0 : e' x' ∈ e'.target ∩ e'.symm ⁻¹' (V : Set X) :=
      ⟨e'.map_source hx's, by rw [Set.mem_preimage, e'.left_inv hx's]; exact x'.2⟩
    have hc0 := hβdol.contDiffAt_chartExpr he0a x' (hVs x')
    have hw : e' x' ∈ (e'.symm.trans e0).source :=
      mem_transition_source.2 ⟨hz0.1, by rw [e'.left_inv hx's]; exact hVs x'⟩
    have htr : ContDiffAt ℝ ∞ (e0 ∘ e'.symm) (e' x') :=
      ((contDiffOn_atlas_transition he'a he0a).contDiffAt
        ((e'.symm.trans e0).open_source.mem_nhds hw)).restrict_scalars ℝ
    have hc1 : ContDiffAt ℝ ∞ (chartExpr E (β : V → TotFibre E) e0) ((e0 ∘ e'.symm) (e' x')) := by
      rw [Function.comp_apply, e'.left_inv hx's]; exact hc0
    have hg : ContDiffAt ℝ ∞ (fun z ↦ ℓ I (chartExpr E (β : V → TotFibre E) e0 ((e0 ∘ e'.symm) z)))
        (e' x') :=
      ((ℓ I).restrictScalars ℝ).contDiff.contDiffAt.comp (e' x') (hc1.comp (e' x') htr)
    have h2 : chartExpr E (funForm E (cfun I)) e' =
        fun z ↦ (if h : e'.symm z ∈ V then cfun I ⟨e'.symm z, h⟩ else 0) • (1 : TotFibre E) :=
      funext (chartExpr_funForm E _ e')
    rw [h2]
    have hgs := hg.smul (contDiffAt_const (c := (1 : TotFibre E)))
    refine hgs.congr_of_eventuallyEq ?_
    filter_upwards [hV.mem_nhds hz0] with z hz
    have hzV : e'.symm z ∈ V := hz.2
    simp only [hzV, ↓reduceDIte, cfun, Function.comp_apply]
    rfl
  let fI : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} → dolbeaultGrade E V 0 :=
    fun I ↦ ⟨⟨funForm E (cfun I), hdolf I⟩, isOfDegree_funForm E _⟩
  have hsum : ∀ (g : {I : Finset (Fin (Module.finrank ℂ E)) // I.card = q} →
      dolbeaultGrade E V 0) (y : V),
      ((∑ I, (g I : DolbeaultAlg E V) * (dolbeaultRes E hVU).toAlgHom (eI I) :
        DolbeaultAlg E V) : V → TotFibre E) y =
      ∑ I, φ (((g I : DolbeaultAlg E V) : V → TotFibre E) y) •
        TotFibre.pull (Sfn y) (TotFibre.ofDeg q (B I)) := by
    intro g y
    rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun I _ ↦ ?_
    have h0 := hφ2 (((g I : DolbeaultAlg E V) : V → TotFibre E) y)
      (fun i hi ↦ (g I).2 y i (by exact_mod_cast hi))
    show ((g I : DolbeaultAlg E V) : V → TotFibre E) y * TotFibre.pull (Sfn y)
      (TotFibre.ofDeg q (B I)) = _
    conv_lhs => rw [h0]
    rw [smul_mul_assoc, one_mul]
  have hcoef : ∀ (y : V), ∀ I, φ (funForm E (cfun I) y) = cfun I y := fun y I ↦ by
    have : funForm E (cfun I) y = cfun I y • (1 : TotFibre E) :=
      ofDeg0_eq_smul_one E _
    rw [this, hφ1]
  have hP := fun y : V ↦ frame_coeffs_aux E q B (Tfn y) (Sfn y) (hST y (hVs y)) (hTS y (hVs y))
    ((β : V → TotFibre E) y) (fun i hi ↦ hβd y i (by exact_mod_cast hi))
  have hcy : ∀ (y : V) I, cfun I y = B.repr (TotFibre.deg q (TotFibre.pull (Tfn y)
      ((β : V → TotFibre E) y))) I := fun y I ↦ by
    show ℓ I (chartExpr E (β : V → TotFibre E) e0 (e0 y)) = _
    rw [hce y, hℓ]
  refine ⟨fI, ?_, fun g hg ↦ funext fun I ↦ ?_⟩
  · refine Subtype.ext (funext fun y ↦ ?_)
    rw [hsum fI y]
    have h1 := (hP y).1
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun J _ ↦ ?_
    show _ • _ = φ (funForm E (cfun J) y) • _
    rw [hcoef, hcy]
  · refine Subtype.ext (Subtype.ext (funext fun y ↦ ?_))
    have hy := congrArg (fun a : DolbeaultAlg E V ↦ (a : V → TotFibre E) y) hg
    rw [hsum g y] at hy
    have h2 := (hP y).2 (fun J ↦ φ (((g J : DolbeaultAlg E V) : V → TotFibre E) y)) hy
    have h3 := congrFun h2 I
    have h4 := hφ2 (((g I : DolbeaultAlg E V) : V → TotFibre E) y)
      (fun i hi ↦ (g I).2 y i (by exact_mod_cast hi))
    show ((g I : DolbeaultAlg E V) : V → TotFibre E) y = funForm E (cfun I) y
    rw [h4, h3, ← hcy]
    exact (ofDeg0_eq_smul_one E _).symm

end Cohesive
end
