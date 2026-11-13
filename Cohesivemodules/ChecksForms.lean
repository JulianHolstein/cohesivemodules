import Cohesivemodules.Hypotheses
import Cohesivemodules.Checks
import Cohesivemodules.Forms.DolbeaultCohomology

set_option linter.style.header false

/-!
# Phase-3 checks: K1, K5, and non-vacuity of the Dolbeault sheaf

Blueprint §9 checks for phase 3 (the K2/K3 normalizations are in `Checks.lean`).

* **K1** (dimension zero): for `E = Fin 0 → ℂ`, H1 and H2 hold on every `X`; in particular the
  hypothesis bundle is satisfied by an actual complex manifold (the point `Fin 0 → ℂ`), over
  whose Dolbeault algebra cohesive modules exist (so H2 does not hold vacuously).
* **K5**: H1 for `q + 1 > n`.
* **Non-vacuity of F9, F10, F12** on `X = ℂ`: the form `z̄` is a Dolbeault form, its `∂̄` computed
  through the chart machinery (`dbarSec`) is `dz̄` (K2 survives F9), so `𝒜¹_ℂ(ℂ) ≠ 0`; `z̄` is not
  in the image of `ρ`; `𝒜⁰_ℂ(ℂ)` is a nontrivial ring.

## Deviations
* The unconditional corollary of K1 for finite discrete `X` needs the main theorem (phase 5) and
  a `ChartedSpace (Fin 0 → ℂ) X` instance for discrete `X`; it is deferred to phase 5.
-/

noncomputable section

namespace Cohesive.Checks

open TopologicalSpace Manifold CategoryTheory Opposite ComplexConjugate
open scoped ContDiff

/-! ## K1: dimension zero -/

/-- K1: the model space `Fin 0 → ℂ` has complex dimension `0`. -/
theorem finrank_fin_zero : Module.finrank ℂ (Fin 0 → ℂ) = 0 := by
  simp

/-- **K1 (H1).** On every complex manifold of dimension `0`, H1 holds. -/
theorem K1_dolbeaultGrothendieck (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 0 → ℂ) X]
    [IsManifold 𝓘(ℂ, Fin 0 → ℂ) ∞ X] : DolbeaultGrothendieck (Fin 0 → ℂ) X :=
  dolbeaultGrothendieck_of_finrank_eq_zero _ _ finrank_fin_zero

/-- **K1 (H2).** On every complex manifold of dimension `0`, H2 holds. -/
theorem K1_localGaugeLemma (X : Type) [TopologicalSpace X] [ChartedSpace (Fin 0 → ℂ) X]
    [IsManifold 𝓘(ℂ, Fin 0 → ℂ) ∞ X] : LocalGaugeLemma (Fin 0 → ℂ) X :=
  localGaugeLemma_of_finrank_eq_zero _ _ finrank_fin_zero

/-- **K1 (satisfiable).** The point `Fin 0 → ℂ`, a compact Hausdorff complex manifold, satisfies
both hypotheses. -/
theorem K1_point :
    CompactSpace (Fin 0 → ℂ) ∧ DolbeaultGrothendieck (Fin 0 → ℂ) (Fin 0 → ℂ) ∧
      LocalGaugeLemma (Fin 0 → ℂ) (Fin 0 → ℂ) :=
  ⟨inferInstance, K1_dolbeaultGrothendieck _, K1_localGaugeLemma _⟩

/-- K1 (H2 is not vacuous): there is a cohesive module over the Dolbeault algebra of the point
(the unit module, `c = 0`). -/
theorem K1_nonempty_cohesive : Nonempty (CohesiveModule (dolbeault (Fin 0 → ℂ) (Fin 0 → ℂ))) :=
  ⟨unitCohesive _ rfl⟩

/-! ## K5: trivial case of H1 -/

/-- **K5.** H1 for `q + 1 > n`: a `∂̄`-closed form of degree `q + 1 > n` is `∂̄`-exact (it is
`0`), on every open set of every complex manifold. -/
theorem K5 {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
    (U : Opens X) (q : ℕ) (hq : Module.finrank ℂ E < q + 1) (x : X) (hx : x ∈ U)
    (α : DolbeaultAlg E U) (hα : α ∈ dolbeaultGrade E U ((q : ℤ) + 1))
    (hd : GCDga.d (𝒜 := dolbeaultGrade E U) α = 0) :
    ∃ (U' : Opens X) (h : U' ≤ U), x ∈ U' ∧
      ∃ η ∈ dolbeaultGrade E U' (q : ℤ),
        GCDga.d (𝒜 := dolbeaultGrade E U') η = (dolbeaultRes E h).toAlgHom α :=
  dolbeaultGrothendieck_of_lt E X U q hq x hx α hα hd

/-! ## Non-vacuity of F9, F10, F12 on `X = ℂ` -/

/-- The function `z ↦ z̄` on `X = ℂ` as a form of degree `0`. -/
def conjForm : (⊤ : Opens ℂ) → TotFibre ℂ :=
  fun y ↦ TotFibre.ofDeg 0 (form0Equiv ℂ ℂ (conj (y : ℂ)))

/-- On `X = ℂ` the chart expression of `conjForm` in any chart `chartAt ℂ x` is `z ↦ z̄`. -/
private theorem chartExpr_conjForm (x : (⊤ : Opens ℂ)) :
    chartExpr ℂ conjForm (chartAt ℂ (x : ℂ)) =
      fun z : ℂ ↦ TotFibre.ofDeg 0 (form0Equiv ℂ ℂ (conj z)) := by
  funext z
  have hc : chartAt ℂ (x : ℂ) = OpenPartialHomeomorph.refl ℂ := chartAt_self_eq
  rw [chartExpr_of_symm_eq conjForm _ (y := z) (by rw [hc]; rfl) trivial]
  have hT : chartTrans ℂ (chartAt ℂ (x : ℂ)) z z = ContinuousLinearMap.id ℂ ℂ := by
    unfold chartTrans
    rw [hc]
    exact fderiv_id
  rw [hT]
  have hp : ∀ a : TotFibre ℂ, TotFibre.pull (ContinuousLinearMap.id ℂ ℂ) a = a := by
    intro a
    funext i
    ext v
    rfl
  rw [hp]
  rfl

/-- F9 non-vacuity: `z̄` is a Dolbeault form on `ℂ`. -/
theorem isDolbeault_conjForm : IsDolbeault ℂ conjForm := by
  intro x
  rw [chartExpr_conjForm]
  let L : ℂ →ₗ[ℂ] TotFibre ℂ := TotFibre.ofDeg 0 ∘ₗ (form0Equiv ℂ ℂ).toLinearMap
  let L' : ℂ →L[ℂ] TotFibre ℂ := LinearMap.toContinuousLinearMap L
  have h1 : ContDiff ℝ ∞ (fun z : ℂ ↦ L' (conj z)) :=
    (L'.restrictScalars ℝ).contDiff.comp (Complex.conjCLE.contDiff)
  exact h1.contDiffAt

/-- **F9 normalization:** `∂̄ z̄ = dz̄` at every point, computed by `dbarSec` (charts, `fderiv`
transition factors): K2 (i) survives the passage to the manifold. -/
theorem dbarSec_conjForm (y : (⊤ : Opens ℂ)) : dbarSec ℂ conjForm y = TotFibre.ofDeg 1 dzbar := by
  unfold dbarSec
  rw [chartExpr_conjForm]
  have h := dbarTot_ofDeg (E := ℂ) 0 (form0 (fun z : ℂ ↦ conj z)) (chartAt ℂ (y : ℂ) y)
  rw [K2_conj] at h
  exact h

/-- `dz̄ ≠ 0`. -/
theorem dzbar_ne_zero : dzbar ≠ 0 := by
  intro h
  have h1 := congrArg (fun a : DolbeaultFibre ℂ 1 ℂ ↦ a (fun _ ↦ Conj.toConj (1 : ℂ))) h
  simp only [dzbar, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    conjCLM_apply, Conj.ofConj_toConj, map_one] at h1
  exact one_ne_zero h1

/-- `z̄` as an element of the Dolbeault algebra of `ℂ`. -/
private def conjAlg : DolbeaultAlg ℂ (⊤ : Opens ℂ) := ⟨conjForm, isDolbeault_conjForm⟩

/-- `z̄` has degree `0`. -/
private theorem isOfDegree_conjForm : IsOfDegree ℂ 0 conjForm := by
  intro y i hi
  have hi' : (0 : ℕ) ≠ (i : ℕ) := fun h ↦ hi (by simp only [← h, Nat.cast_zero])
  show (TotFibre.ofDeg 0 (form0Equiv ℂ ℂ (conj (y : ℂ))) : TotFibre ℂ) i = 0
  show (if h : 0 = (i : ℕ) then DolbeaultFibre.cast h _ else 0) = 0
  simp only [hi', ↓reduceDIte]

/-- `ofDeg 1 dz̄ ≠ 0` in the total fibre of `ℂ`. -/
private theorem ofDeg_one_dzbar_ne_zero : (TotFibre.ofDeg 1 dzbar : TotFibre ℂ) ≠ 0 := by
  intro h
  have h1 := congrArg (TotFibre.deg 1) h
  rw [TotFibre.deg_ofDeg_self (by rw [Module.finrank_self]), map_zero] at h1
  exact dzbar_ne_zero h1

/-- F10 non-vacuity: `𝒜^{0,1}_ℂ(ℂ) ≠ 0`. -/
theorem dolbeaultGrade_one_ne_bot : dolbeaultGrade ℂ (⊤ : Opens ℂ) 1 ≠ ⊥ := by
  rw [Ne, Submodule.eq_bot_iff]
  intro h
  have hmem : GCDga.d (𝒜 := dolbeaultGrade ℂ (⊤ : Opens ℂ)) conjAlg ∈
      dolbeaultGrade ℂ (⊤ : Opens ℂ) 1 := by
    have h0 : conjAlg ∈ dolbeaultGrade ℂ (⊤ : Opens ℂ) 0 := isOfDegree_conjForm
    simpa only [zero_add] using GCDga.d_mem (𝒜 := dolbeaultGrade ℂ (⊤ : Opens ℂ)) h0
  have h2 := h _ hmem
  have h3 := congrFun (congrArg Subtype.val h2) ⟨0, trivial⟩
  exact ofDeg_one_dzbar_ne_zero ((dbarSec_conjForm ⟨0, trivial⟩).symm.trans h3)

/-- F12 non-vacuity: `z̄` is a smooth function of degree `0` that is not holomorphic, i.e. not in
the image of `ρ_ℂ : O(ℂ) → 𝒜⁰(ℂ)`. -/
theorem conjForm_not_mem_range (f : (holSheaf ℂ ℂ).obj.obj (op ⊤)) :
    ((dolbeaultRhoU ℂ ⊤ f : ↥(dolbeaultGrade ℂ ⊤ 0)) : DolbeaultAlg ℂ ⊤).val ≠ conjForm := by
  intro h
  have hd := dbar_dolbeaultRhoU ℂ ⊤ f
  have ha : ((dolbeaultRhoU ℂ ⊤ f : ↥(dolbeaultGrade ℂ ⊤ 0)) : DolbeaultAlg ℂ ⊤) = conjAlg :=
    Subtype.ext h
  rw [ha] at hd
  have h3 := congrFun (congrArg Subtype.val hd) ⟨0, trivial⟩
  exact ofDeg_one_dzbar_ne_zero ((dbarSec_conjForm ⟨0, trivial⟩).symm.trans h3)

/-- F10 non-vacuity: the ring `𝒜⁰_ℂ(ℂ)` of global sections of `dolbeault0` is nontrivial. -/
theorem nontrivial_dolbeault0 : Nontrivial ((dolbeault0 ℂ ℂ).obj.obj (op ⊤)) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  have h1 : (1 : TotFibre ℂ) = 0 :=
    congrFun (congrArg Subtype.val (congrArg Subtype.val h)) ⟨0, trivial⟩
  rw [TotFibre.one_eq] at h1
  have h2 := congrArg (TotFibre.deg 0) h1
  rw [TotFibre.deg_ofDeg_self (Nat.zero_le _), map_zero] at h2
  exact one_ne_zero ((form0Equiv ℂ ℂ).map_eq_zero_iff.1 h2)

/-! ## K4: maps from `𝒜` to its shifts are Dolbeault cohomology (phase 7, K4.b) -/

section K4

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **K4** (blueprint §9; `blueprint/blueprint-tr.md` §4). [B, §2.4, §4.1]. For the unit module
`𝒜` over the Dolbeault algebra of any complex manifold `X` and every `n : ℤ`,
`Hom_{Ho(P_A)}(𝒜, 𝒜⟦n⟧) ≅ H^{0,n}_∂̄(X)` as `ℂ`-vector spaces, with the shift of Z2.b. A check
of the shift: no hypotheses on `X`. -/
theorem K4 (n : ℤ) :
    Nonempty ((dolbeaultUnit E X ⟶
      (shiftFunctor (HoP (dolbeault E X)) n).obj (dolbeaultUnit E X)) ≃ₗ[ℂ]
        dolbeaultCohomology E X n) :=
  ⟨k4Equiv E X n⟩

/-- K4 (sanity): there are no nonzero maps `𝒜 ⟶ 𝒜⟦n⟧` in `Ho(P_A)` for `n < 0`. -/
theorem K4_of_neg {n : ℤ} (hn : n < 0) :
    Subsingleton (dolbeaultUnit E X ⟶
      (shiftFunctor (HoP (dolbeault E X)) n).obj (dolbeaultUnit E X)) :=
  have := subsingleton_dolbeaultCohomology_of_neg E X hn
  (k4Equiv E X n).toEquiv.subsingleton

/-- K4 (sanity): there are no nonzero maps `𝒜 ⟶ 𝒜⟦n⟧` in `Ho(P_A)` for `n > dim_ℂ X`. -/
theorem K4_of_gt {n : ℤ} (hn : (Module.finrank ℂ E : ℤ) < n) :
    Subsingleton (dolbeaultUnit E X ⟶
      (shiftFunctor (HoP (dolbeault E X)) n).obj (dolbeaultUnit E X)) :=
  have := subsingleton_dolbeaultCohomology_of_gt E X hn
  (k4Equiv E X n).toEquiv.subsingleton

/-- K4 (sanity, `n = 0`): `Hom_{Ho(P_A)}(𝒜, 𝒜⟦0⟧)` is in bijection with the holomorphic
functions `O(X)` (F12). -/
theorem K4_zero :
    Nonempty ((dolbeaultUnit E X ⟶
      (shiftFunctor (HoP (dolbeault E X)) (0 : ℤ)).obj (dolbeaultUnit E X)) ≃
        (holSheaf E X).obj.obj (Opposite.op ⊤)) :=
  ⟨k4ZeroEquiv E X⟩

end K4

/-- info: 'Cohesive.Checks.K4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms K4

/-- info: 'Cohesive.Checks.K4_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms K4_zero

end Cohesive.Checks
