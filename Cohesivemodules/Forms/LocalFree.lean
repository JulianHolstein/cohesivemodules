import Cohesivemodules.Forms.Dolbeault
import Cohesivemodules.Algebra.CohesiveDef
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module

set_option linter.style.header false

/-!
# Z5.g: the generators of a cohesive module are free near every point

Blueprint item Z5.g (`blueprint/blueprint-ll.md` §4.A, §5), [B, proof of Lemma 4.1.5] (local
triviality of the bundles `Q^p`, used there without proof).

* `coef0`, `evalForm0`: a degree-`0` form is a function `U → ℂ`; evaluation at `y` is a ring
  homomorphism `𝒜⁰(U) →+* ℂ`.
* `continuous_evalForm0`: degree-`0` forms are continuous functions.
* `isUnit_of_evalForm0_ne_zero`: a nowhere-vanishing degree-`0` form is a unit of `𝒜⁰(U)`.
* `exists_free_away`, `free_baseChange_of_isUnit`: ring theory (f.g. projective modules are
  free over a basic open containing a given prime).
* `exists_free_baseChange`: for a cohesive module `M` over `𝒜_X(X)` and `x ∈ X`, there is an
  open `U′ ∋ x` inside the chart at `x` over which every `𝒜⁰(U′) ⊗_{𝒜⁰(X)} Q^p` is free.

## Deviations
* The proof differs from blueprint-ll A.1–A.3 (idempotent matrices, minors, Cramer's rule): we
  localize at the maximal ideal `𝔪_x = ker (ev_x)`, where `Q^p` is free (Mathlib,
  `Module.free_of_flat_of_isLocalRing`), spread freeness to a basic open `D(r_p)`, `r_p(x) ≠ 0`
  (`Module.FinitePresentation.exists_free_localizedModule_powers`), and take `U′` where all
  `r_p` (finitely many `p`) do not vanish; there `r_p` is a unit, so `𝒜⁰(X) → 𝒜⁰(U′)` factors
  through `𝒜⁰(X)[r_p⁻¹]`. The statement is the one of blueprint-ll §5.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold TensorProduct
open scoped ContDiff

/-! ## Ring theory -/

section RingTheory

variable {R : Type*} [CommRing R] {Q : Type*} [AddCommGroup Q] [Module R Q]

/-- **Z5.g** (ring theory). A finitely generated projective module `Q` over a commutative ring
`R` is free over a basic open `D(r)` containing a given prime `𝔪`: there is `r ∉ 𝔪` with
`Q[r⁻¹]` free over `R[r⁻¹]`. ([Stacks, Tag 00NX]; Mathlib's free-locus results.) -/
theorem exists_free_away [Module.Finite R Q] [Module.Projective R Q] (m : Ideal R)
    [m.IsPrime] :
    ∃ r ∉ m, Module.Free (Localization.Away r) (LocalizedModule.Away r Q) := by
  have : Module.FinitePresentation R Q := Module.finitePresentation_of_projective R Q
  have : Module.Free (Localization.AtPrime m) (LocalizedModule m.primeCompl Q) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    m.primeCompl (LocalizedModule.mkLinearMap m.primeCompl Q) (Localization.AtPrime m)
  exact ⟨r, hr, hfree⟩

/-- **Z5.g** (ring theory). If `Q[r⁻¹]` is free over `R[r⁻¹]` and `r` becomes a unit in the
`R`-algebra `S`, then `S ⊗_R Q` is free over `S` (`S ⊗_R Q ≅ S ⊗_{R[r⁻¹]} Q[r⁻¹]`). -/
theorem free_baseChange_of_isUnit (S : Type*) [CommRing S] [Algebra R S] (r : R)
    (hr : IsUnit (algebraMap R S r))
    [Module.Free (Localization.Away r) (LocalizedModule.Away r Q)] :
    Module.Free S (S ⊗[R] Q) := by
  let : Algebra (Localization.Away r) S :=
    (IsLocalization.Away.lift r hr : Localization.Away r →+* S).toAlgebra
  have : IsScalarTower R (Localization.Away r) S := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsLocalization.Away.lift_eq r hr x).symm
  let e1 := (IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) Q)).equiv
  let e : S ⊗[Localization.Away r] LocalizedModule.Away r Q ≃ₗ[S] S ⊗[R] Q :=
    (LinearEquiv.baseChange (Localization.Away r) S _ _ e1.symm).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away r) S S Q)
  exact Module.Free.of_equiv e

/-- Z5.g (ring theory): `S ⊗_R Q = 0` when `Q = 0`. -/
theorem subsingleton_tensor_right {S : Type*} [AddCommGroup S] [Module R S] [Subsingleton Q] :
    Subsingleton (S ⊗[R] Q) := by
  refine subsingleton_iff_forall_eq 0 |>.2 fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul s q => rw [Subsingleton.elim q 0, TensorProduct.tmul_zero]
  | add t t' ht ht' => rw [ht, ht', add_zero]

end RingTheory

section BCGen

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  (f : DgaHom 𝒜 ℬ) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- Z5.g: the base-changed generators `B⁰ ⊗_{A⁰} Q^p` are free over `B⁰` if `Q^p[r⁻¹]` is free
over `A⁰[r⁻¹]` and `f(r)` is a unit of `B⁰`. -/
theorem free_bcGen_of_isUnit (p : ℤ) (r : 𝒜 0)
    [Module.Free (Localization.Away r) (LocalizedModule.Away r (Q p))] (hr : IsUnit (f.f0 r)) :
    Module.Free (ℬ 0) (BCGen f Q p) :=
  free_baseChange_of_isUnit (Q := Q p) f.B0 r hr

/-- Z5.g: `B⁰ ⊗_{A⁰} Q^p` is free (zero) if `Q^p = 0`. -/
theorem free_bcGen_of_subsingleton (p : ℤ) [Subsingleton (Q p)] :
    Module.Free (ℬ 0) (BCGen f Q p) :=
  have : Subsingleton (BCGen f Q p) :=
    subsingleton_tensor_right (R := 𝒜 0) (S := f.B0) (Q := Q p)
  Module.Free.of_subsingleton _ _

end BCGen

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-! ## Degree-`0` forms as functions -/

/-- **Z5.g.** The coefficient of `1 ∈ Λ^{0,•}(E)`: a continuous linear map `Λ^{0,•}(E) → ℂ`
with `coef0 (c • 1) = c` (chosen from `exists_coef0`). -/
def coef0 : TotFibre E →L[ℂ] ℂ := (exists_coef0 E).choose

/-- Z5.g: `coef0 (c • 1) = c`. -/
theorem coef0_smul_one (c : ℂ) : coef0 E (c • 1) = c := (exists_coef0 E).choose_spec.1 c

/-- Z5.g: an element of the total fibre concentrated in degree `0` is `coef0 t • 1`. -/
theorem eq_coef0_smul_one (t : TotFibre E)
    (ht : ∀ i : Fin (Module.finrank ℂ E + 1), ((i : ℕ) : ℤ) ≠ 0 → t i = 0) :
    t = coef0 E t • 1 :=
  (exists_coef0 E).choose_spec.2 t ht

/-- Z5.g: the value of a degree-`0` form at `y` is `coef0 (α y) • 1`. -/
theorem form0_apply_eq {U : Opens X} (α : dolbeaultGrade E U 0) (y : U) :
    ((α : DolbeaultAlg E U) : U → TotFibre E) y =
      coef0 E (((α : DolbeaultAlg E U) : U → TotFibre E) y) • 1 :=
  eq_coef0_smul_one E _ (α.2 y)

/-- **Z5.g.** Evaluation of degree-`0` forms at `y ∈ U`, a ring homomorphism
`𝒜⁰(U) →+* ℂ`, `α ↦ α(y)` (the coefficient of `1`). -/
def evalForm0 {U : Opens X} (y : U) : dolbeaultGrade E U 0 →+* ℂ where
  toFun α := coef0 E (((α : DolbeaultAlg E U) : U → TotFibre E) y)
  map_one' := by
    show coef0 E (1 : TotFibre E) = 1
    simpa using coef0_smul_one E 1
  map_mul' α β := by
    show coef0 E (((α : DolbeaultAlg E U) : U → TotFibre E) y *
      ((β : DolbeaultAlg E U) : U → TotFibre E) y) = _
    rw [form0_apply_eq E α y, form0_apply_eq E β y, smul_mul_smul_comm, one_mul,
      coef0_smul_one, coef0_smul_one, coef0_smul_one]
  map_zero' := map_zero (coef0 E)
  map_add' α β := map_add (coef0 E) _ _

/-- Z5.g: formula for `evalForm0` (rfl). -/
theorem evalForm0_apply {U : Opens X} (y : U) (α : dolbeaultGrade E U 0) :
    evalForm0 E y α = coef0 E (((α : DolbeaultAlg E U) : U → TotFibre E) y) :=
  rfl

/-- Z5.g: evaluating a restricted form is evaluating the form (rfl). -/
theorem evalForm0_res {U V : Opens X} (h : V ≤ U) (α : dolbeaultGrade E U 0) (y : V) :
    evalForm0 E y ((dolbeaultRes E h).f0 α) = evalForm0 E (U := U) ⟨y, h y.2⟩ α :=
  rfl

/-- Z5.g: a degree-`0` form is the `0`-form of the function `y ↦ α(y)`. -/
theorem form0_eq_funForm {U : Opens X} (α : dolbeaultGrade E U 0) :
    ((α : DolbeaultAlg E U) : U → TotFibre E) = funForm E fun y ↦ evalForm0 E y α :=
  funext fun y ↦ (form0_apply_eq E α y).trans (ofDeg0_eq_smul_one E _).symm

/-- Z5.g: in a chart `e` around `y ∈ U`, the coefficient of the chart expression of a degree-`0`
form is its value: `coef0 (chartExpr α e (e y)) = α(y)` (pullbacks fix degree `0`). -/
theorem coef0_chartExpr_form0 {U : Opens X} (α : dolbeaultGrade E U 0)
    (e : OpenPartialHomeomorph X E) (y : U) (hy : (y : X) ∈ e.source) :
    coef0 E (chartExpr E ((α : DolbeaultAlg E U) : U → TotFibre E) e (e y)) =
      evalForm0 E y α := by
  rw [chartExpr_of_symm_eq _ e (e.left_inv hy) y.2, form0_apply_eq E α, map_smul,
    TotFibre.pull_one, coef0_smul_one]
  rfl

/-- **Z5.g.** A degree-`0` form on `U` is a continuous function `U → ℂ` (its expression in the
chart at each point is smooth). -/
theorem continuous_evalForm0 {U : Opens X} (α : dolbeaultGrade E U 0) :
    Continuous fun y : U ↦ evalForm0 E y α := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  set e := chartAt E (y : X)
  have hc : ContinuousAt
      (fun z ↦ coef0 E (chartExpr E ((α : DolbeaultAlg E U) : U → TotFibre E) e z)) (e y) :=
    (coef0 E).continuous.continuousAt.comp (α.1.2 y).continuousAt
  have he : ContinuousAt (fun y' : U ↦ e y') y :=
    (e.continuousAt (mem_chart_source E (y : X))).comp continuous_subtype_val.continuousAt
  refine (hc.comp (x := y) he).congr ?_
  filter_upwards [(e.open_source.preimage continuous_subtype_val).mem_nhds
    (mem_chart_source E (y : X))] with y' hy'
  exact coef0_chartExpr_form0 E α e y' hy'

/-- **Z5.g.** A nowhere-vanishing degree-`0` form is a unit of `𝒜⁰(U)`: `y ↦ α(y)⁻¹` is again
a Dolbeault form (inverses of non-vanishing smooth functions are smooth). -/
theorem isUnit_of_evalForm0_ne_zero {U : Opens X} (α : dolbeaultGrade E U 0)
    (h : ∀ y, evalForm0 E y α ≠ 0) : IsUnit α := by
  classical
  have hβ : IsDolbeault E (funForm E fun y : U ↦ (evalForm0 E y α)⁻¹) := by
    intro x
    set e := chartAt E (x : X)
    have hxs : (x : X) ∈ e.source := mem_chart_source E (x : X)
    set g : E → ℂ :=
      fun z ↦ coef0 E (chartExpr E ((α : DolbeaultAlg E U) : U → TotFibre E) e z)
    have hg : ContDiffAt ℝ ∞ g (e x) :=
      ((coef0 E).restrictScalars ℝ).contDiff.contDiffAt.comp _ (α.1.2 x)
    have hgx : g (e x) ≠ 0 := by
      simp only [g, coef0_chartExpr_form0 E α e x hxs]
      exact h x
    have hev : ∀ᶠ z in nhds (e x), e.symm z ∈ U := by
      have hcs : ContinuousAt e.symm (e x) := e.continuousAt_symm (mem_chart_target E (x : X))
      exact hcs.eventually_mem (U.isOpen.mem_nhds (by rw [e.left_inv hxs]; exact x.2))
    have hev' : ∀ᶠ z in nhds (e x), z ∈ e.target :=
      e.open_target.mem_nhds (mem_chart_target E (x : X))
    refine ((hg.inv hgx).smul (contDiffAt_const (c := (1 : TotFibre E)))).congr_of_eventuallyEq
      ?_
    filter_upwards [hev, hev'] with z hz hzt
    rw [chartExpr_funForm]
    simp only [hz, ↓reduceDIte]
    congr 2
    have := coef0_chartExpr_form0 E α e ⟨e.symm z, hz⟩ (e.map_target hzt)
    simp only [e.right_inv hzt] at this
    exact this.symm
  let β : dolbeaultGrade E U 0 := ⟨⟨_, hβ⟩, isOfDegree_funForm E _⟩
  have hαβ : α * β = 1 := Subtype.ext (Subtype.ext (funext fun y ↦ ?_))
  · exact ⟨⟨α, β, hαβ,
      Subtype.ext ((GCDga.central _ β.2 α).trans (congrArg Subtype.val hαβ))⟩, rfl⟩
  show ((α : DolbeaultAlg E U) : U → TotFibre E) y * funForm E (fun y ↦ (evalForm0 E y α)⁻¹) y =
    (1 : TotFibre E)
  rw [form0_apply_eq E α y, funForm, ofDeg0_eq_smul_one, smul_mul_smul_comm, one_mul]
  rw [← evalForm0_apply, mul_inv_cancel₀ (h y), one_smul]

/-! ## Local freeness of the generators -/

/-- Z5.g: the kernel of evaluation at `x`, a prime ideal of `𝒜⁰(X)`. -/
instance isPrime_ker_evalForm0 (x : (⊤ : Opens X)) :
    (RingHom.ker (evalForm0 E x)).IsPrime :=
  RingHom.ker_isPrime _

/-- **Z5.g. Local freeness.** [B, proof of Lemma 4.1.5] (implicit), blueprint-ll A.
For a cohesive module `M` over `A = 𝒜_X(X)` and `x ∈ X`, there is an open `U′ ∋ x` contained in
the source of the chart at `x` such that, for every `p`, the base-changed generators
`𝒜⁰(U′) ⊗_{𝒜⁰(X)} Q^p` (`BCGen` along the restriction `dolbeaultRes`, A9) form a free
`𝒜⁰(U′)`-module.

Deviation: proof by localization instead of idempotent matrices (module docstring). -/
theorem exists_free_baseChange (M : CohesiveModule (dolbeault E X)) (x : X) :
    ∃ U' : Opens X, x ∈ U' ∧ (U' : Set X) ⊆ (chartAt E x).source ∧
      ∀ p, Module.Free ↥(dolbeaultGrade E U' 0)
        (BCGen (dolbeaultRes E (le_top : U' ≤ ⊤)) M.Q p) := by
  have hfree : ∀ p, ∃ r ∉ RingHom.ker (evalForm0 E (⟨x, trivial⟩ : (⊤ : Opens X))),
      Module.Free (Localization.Away r) (LocalizedModule.Away r (M.Q p)) := by
    intro p
    have := M.finite p
    have := M.projective p
    exact exists_free_away (R := ↥(dolbeault E X 0)) (Q := M.Q p) _
  choose r hr hrfree using hfree
  obtain ⟨a, b, hab⟩ := M.bounded
  set e := chartAt E x
  let V : Set X := e.source ∩ ⋂ p ∈ Finset.Icc a b,
    {y | ∃ hy : y ∈ (⊤ : Opens X), evalForm0 E ⟨y, hy⟩ (r p) ≠ 0}
  have hV : IsOpen V := by
    refine e.open_source.inter (isOpen_biInter_finset fun p _ ↦ ?_)
    have hc := (continuous_evalForm0 E (r p)).isOpen_preimage {0}ᶜ isOpen_compl_singleton
    have : {y : X | ∃ hy : y ∈ (⊤ : Opens X), evalForm0 E ⟨y, hy⟩ (r p) ≠ 0} =
        Subtype.val '' ((fun y : (⊤ : Opens X) ↦ evalForm0 E y (r p)) ⁻¹' {0}ᶜ) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      exact ⟨fun ⟨hy, h⟩ ↦ ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨y', h, hy'⟩ ↦ hy' ▸ ⟨y'.2, h⟩⟩
    rw [this]
    exact (⊤ : Opens X).isOpen.isOpenMap_subtype_val _ hc
  have hxV : x ∈ V := by
    refine ⟨mem_chart_source E x, Set.mem_iInter₂.2 fun p _ ↦ ⟨trivial, ?_⟩⟩
    exact fun h0 ↦ hr p (RingHom.mem_ker.2 h0)
  have hVe : V ⊆ e.source := Set.inter_subset_left
  refine ⟨⟨V, hV⟩, hxV, hVe, fun p ↦ ?_⟩
  by_cases hp : p < a ∨ b < p
  · have := hab p hp
    exact free_bcGen_of_subsingleton _ M.Q p
  · have hpI : p ∈ Finset.Icc a b := Finset.mem_Icc.2 (by omega)
    have := hrfree p
    refine free_bcGen_of_isUnit _ M.Q p (r p) ?_
    refine isUnit_of_evalForm0_ne_zero E _ fun y ↦ ?_
    obtain ⟨hy, h⟩ := Set.mem_iInter₂.1 (y.2 : (y : X) ∈ V).2 p hpI
    exact h

end Cohesive
