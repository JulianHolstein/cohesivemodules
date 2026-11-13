-- FROZEN (gate 3, 26 Oct 2026; F10 Dolbeault dga and 𝒜⁰, in the main statement). Do not edit without approval.
import Cohesivemodules.Forms.Sheaf
import Cohesivemodules.Algebra.BaseChangeDef
import Cohesivemodules.Sheaf.Basic
import Mathlib.Algebra.Category.Ring.Limits

set_option linter.style.header false

/-!
# F10: the Dolbeault dga of an open set, and the sheaf `𝒜⁰`

Blueprint item F10 (§5), C0 "one carrier for A⁰" (v1.9), conventions §5. These definitions
enter the main statement; they are frozen at gate 3.

* `dolbeaultSubalgebra E U`: the Dolbeault forms on `U` (F9), a `ℂ`-subalgebra of
  `U → Λ^{0,•}(E)` (pointwise product, F5). `DolbeaultAlg E U` is its carrier type, the total
  algebra 𝒜_X(U).
* `dolbeaultGrade E U q`: the forms of degree `q`, i.e. `𝒜^{0,q}_X(U)` (v1.9: the component
  sheaves are these subtypes). `GradedAlgebra` instance by the degree parts.
* `GCDga (dolbeaultGrade E U)`: top degree `n = dim_ℂ E`, `d = ∂̄` (`dbarL`), curvature `0`.
* `dolbeault E X := dolbeaultGrade E ⊤`: the Dolbeault algebra `A = 𝒜_X(X)` of the main theorem.
* `dolbeaultRes E h`: restriction along `V ≤ U`, a map of dgas (A9's `DgaHom`).
* `dolbeault0 E X`: the sheaf of commutative rings `U ↦ CommRingCat.of ↥(𝒜_U 0)` (C0, one carrier
  for `A⁰`): its global sections are `↥(dolbeault E X 0)` with `GCDga.commRing0`.

## Deviations
* ⚠ The total fibre replaces the direct-sum construction (blueprint F10, conventions §5): the
  ring axioms hold pointwise. The `q`-th component sheaf is the degree-`q` subtype.
* The curvature is `0` (the Dolbeault algebra is a dga, [B, §4.1]).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **F10.** [B, §4], [A, §7.1]. The Dolbeault forms on `U` (F9, `IsDolbeault`), a
`ℂ`-subalgebra of `U → Λ^{0,•}(E)` with the pointwise product of the total fibre (F5). -/
def dolbeaultSubalgebra (U : Opens X) : Subalgebra ℂ (U → TotFibre E) where
  carrier := {α | IsDolbeault E α}
  mul_mem' := fun ha hb ↦ IsDolbeault.mul ha hb
  one_mem' := isDolbeault_one
  add_mem' := fun ha hb ↦ IsDolbeault.add ha hb
  zero_mem' := isDolbeault_zero
  algebraMap_mem' := isDolbeault_algebraMap

/-- **F10.** The total Dolbeault algebra `𝒜_X(U)` of an open `U` (carrier type). -/
abbrev DolbeaultAlg (U : Opens X) : Type := ↥(dolbeaultSubalgebra E U)

/-- **F10.** `𝒜^{0,q}_X(U)`: the forms of degree `q` (`IsOfDegree`), a `ℂ`-submodule of
`𝒜_X(U)`; `⊥` for `q < 0` and `q > n`. -/
def dolbeaultGrade (U : Opens X) (q : ℤ) : Submodule ℂ (DolbeaultAlg E U) where
  carrier := {α | IsOfDegree E q (α : U → TotFibre E)}
  add_mem' := fun ha hb ↦ IsOfDegree.add ha hb
  zero_mem' := isOfDegree_zero q
  smul_mem' := fun c _ ha ↦ IsOfDegree.smul c ha

/-- F10: membership in `dolbeaultGrade` (rfl). -/
theorem mem_dolbeaultGrade {U : Opens X} {q : ℤ} {α : DolbeaultAlg E U} :
    α ∈ dolbeaultGrade E U q ↔ IsOfDegree E q (α : U → TotFibre E) :=
  Iff.rfl

/-- F10: the degree-`q` part of a form in `𝒜_X(U)`. -/
def projDegAlg (U : Opens X) (q : ℤ) (α : DolbeaultAlg E U) : dolbeaultGrade E U q :=
  ⟨⟨projDeg E q α, IsDolbeault.projDeg q α.2⟩, isOfDegree_projDeg q _⟩

instance (U : Opens X) : SetLike.GradedMonoid (dolbeaultGrade E U) where
  one_mem := isOfDegree_one
  mul_mem := fun _ _ _ _ ha hb ↦ IsOfDegree.mul ha hb

/-- `projDegAlg` is additive. -/
private theorem projDegAlg_add (U : Opens X) (q : ℤ) (α β : DolbeaultAlg E U) :
    projDegAlg E U q (α + β) = projDegAlg E U q α + projDegAlg E U q β := by
  refine Subtype.ext (Subtype.ext (funext fun y ↦ funext fun i ↦ ?_))
  show (if ((i : ℕ) : ℤ) = q then (α : U → TotFibre E) y i + (β : U → TotFibre E) y i else 0) =
    (if ((i : ℕ) : ℤ) = q then (α : U → TotFibre E) y i else 0) +
      (if ((i : ℕ) : ℤ) = q then (β : U → TotFibre E) y i else 0)
  split_ifs <;> simp

/-- `projDegAlg` of `0` is `0`. -/
private theorem projDegAlg_zero (U : Opens X) (q : ℤ) : projDegAlg E U q 0 = 0 := by
  refine Subtype.ext (Subtype.ext (funext fun y ↦ funext fun i ↦ ?_))
  show (if ((i : ℕ) : ℤ) = q then (0 : TotFibre E) i else 0) = 0
  split_ifs <;> rfl

/-- `projDegAlg` of a form of degree `i` in degree `q`. -/
private theorem projDegAlg_of_mem (U : Opens X) {i q : ℤ} {x : DolbeaultAlg E U}
    (hx : x ∈ dolbeaultGrade E U i) :
    (projDegAlg E U q x : DolbeaultAlg E U) = if q = i then x else 0 := by
  split_ifs with h
  · subst h
    exact Subtype.ext (IsOfDegree.projDeg_self hx)
  · exact Subtype.ext (IsOfDegree.projDeg_ne h hx)

instance (U : Opens X) : DirectSum.Decomposition (dolbeaultGrade E U) where
  decompose' α := ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
    DirectSum.of (fun i ↦ ↥(dolbeaultGrade E U i)) (q : ℤ) (projDegAlg E U q α)
  left_inv := fun α ↦ by
    refine Subtype.ext ?_
    have h : (DirectSum.coeAddMonoidHom (dolbeaultGrade E U)) (∑ q ∈
        Finset.range (Module.finrank ℂ E + 1),
        DirectSum.of (fun i ↦ ↥(dolbeaultGrade E U i)) (q : ℤ) (projDegAlg E U q α)) =
        ∑ q ∈ Finset.range (Module.finrank ℂ E + 1), ((projDegAlg E U q α : _) :
          DolbeaultAlg E U) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [DirectSum.coeAddMonoidHom_of]
    rw [h]
    conv_rhs => rw [← sum_projDeg (α : U → TotFibre E)]
    rw [AddSubmonoidClass.coe_finsetSum]
    rfl
  right_inv := fun a ↦ by
    induction a using DirectSum.induction_on with
    | zero =>
      simp only [map_zero, projDegAlg_zero, Finset.sum_const_zero, map_zero]
    | of i x =>
      rw [DirectSum.coeAddMonoidHom_of]
      beta_reduce
      by_cases hi : i ∈ ((Finset.range (Module.finrank ℂ E + 1)).image ((↑) : ℕ → ℤ))
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
        rw [Finset.sum_eq_single j]
        · congr 1
          exact Subtype.ext (by rw [projDegAlg_of_mem E U x.2, if_pos rfl])
        · intro b _ hb
          have : ((b : ℕ) : ℤ) ≠ j := fun h ↦ hb (Nat.cast_injective h)
          rw [show projDegAlg E U b x = 0 from
            Subtype.ext (by rw [projDegAlg_of_mem E U x.2, if_neg this]; rfl), map_zero]
        · intro h; exact absurd hj h
      · have hx : (x : DolbeaultAlg E U) = 0 := by
          refine Subtype.ext (IsOfDegree.eq_zero ?_ x.2)
          by_contra hc
          simp only [not_or, not_lt, not_le] at hc
          exact hi (Finset.mem_image.2 ⟨i.toNat, Finset.mem_range.2 (by omega), by omega⟩)
        have hx' : x = 0 := Subtype.ext hx
        rw [hx']
        simp only [ZeroMemClass.coe_zero, projDegAlg_zero, Finset.sum_const_zero, map_zero]
    | add a b ha hb =>
      simp only [map_add, projDegAlg_add, Finset.sum_add_distrib] at ha hb ⊢
      rw [ha, hb]

/-- **F10.** The grading of `𝒜_X(U)` by form degree. -/
instance (U : Opens X) : GradedAlgebra (dolbeaultGrade E U) where

/-- **F10 with F9.b.** `∂̄` on `𝒜_X(U)`, a `ℂ`-linear map (`dbarSec`). -/
def dbarL (U : Opens X) : DolbeaultAlg E U →ₗ[ℂ] DolbeaultAlg E U where
  toFun α := ⟨dbarSec E α, IsDolbeault.dbarSec α.2⟩
  map_add' α β := Subtype.ext (dbarSec_add α.2 β.2)
  map_smul' c α := Subtype.ext (dbarSec_smul c α.2)

/-- F10: `dbarL` is `dbarSec` on the underlying forms (rfl). -/
theorem coe_dbarL {U : Opens X} (α : DolbeaultAlg E U) :
    ((dbarL E U α : DolbeaultAlg E U) : U → TotFibre E) = dbarSec E α :=
  rfl

/-- **F10. The Dolbeault dga of `U`.** [B, §4.1], [A, §7.1]. `𝒜_X(U)` is a bounded
graded-commutative dga (A1): top degree `n = dim_ℂ E`, graded commutativity of the wedge product
(F5), `d = ∂̄` (F9.b) with the graded Leibniz rule (F6) and `∂̄∂̄ = 0` (F4), curvature `c = 0`. -/
instance (U : Opens X) : GCDga (dolbeaultGrade E U) where
  N := Module.finrank ℂ E
  zero_of_neg := fun _ hq ↦ (Submodule.eq_bot_iff _).2 fun _ hx ↦
    Subtype.ext (IsOfDegree.eq_zero (Or.inl hq) hx)
  zero_of_gt := fun _ hq ↦ (Submodule.eq_bot_iff _).2 fun _ hx ↦
    Subtype.ext (IsOfDegree.eq_zero (Or.inr hq) hx)
  gcomm := fun ha hb ↦ Subtype.ext (IsOfDegree.mul_comm ha hb)
  d := dbarL E U
  d_mem := fun ha ↦ IsOfDegree.dbarSec ha
  leibniz := fun {_ a} ha b ↦ Subtype.ext (dbarSec_mul a.2 b.2 ha)
  d_d := fun a ↦ Subtype.ext (dbarSec_dbarSec a.2)
  c := 0
  c_mem := Submodule.zero_mem _
  d_c := map_zero _

variable (X) in
/-- **F10. The Dolbeault algebra** `A = 𝒜_X(X)` of `X` (blueprint §1), graded by form degree. -/
abbrev dolbeault : ℤ → Submodule ℂ (DolbeaultAlg E (⊤ : Opens X)) :=
  dolbeaultGrade E ⊤

/-- **F10.** Restriction of forms along `V ≤ U`, as a map of dgas `𝒜_X(U) → 𝒜_X(V)` (A9):
an algebra map preserving degrees, `∂̄` (F9.b, locality) and the curvature `0`. -/
def dolbeaultRes {U V : Opens X} (h : V ≤ U) :
    DgaHom (dolbeaultGrade E U) (dolbeaultGrade E V) where
  toAlgHom :=
    { toFun := fun α ↦ ⟨restrictForm E h α, IsDolbeault.restrictForm h α.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  map_mem := fun ha ↦ IsOfDegree.restrictForm h ha
  map_d := fun α ↦ Subtype.ext (dbarSec_restrictForm h α.2).symm
  map_c := rfl

/-- F10: `dolbeaultRes` is `restrictForm` on the underlying forms (rfl). -/
theorem coe_dolbeaultRes {U V : Opens X} (h : V ≤ U) (α : DolbeaultAlg E U) :
    ((dolbeaultRes E h).toAlgHom α : V → TotFibre E) = restrictForm E h α :=
  rfl

variable (X) in
/-- The local predicate "Dolbeault form of degree `0`" on functions `U → Λ^{0,•}(E)`. -/
private def degZeroPredicate : TopCat.LocalPredicate fun _ : TopCat.of X ↦ TotFibre E where
  pred {U} α := IsDolbeault E α ∧ IsOfDegree E 0 α
  res := fun {_ _} i _ hα ↦
    ⟨IsDolbeault.restrictForm (CategoryTheory.leOfHom i) hα.1,
      IsOfDegree.restrictForm (CategoryTheory.leOfHom i) hα.2⟩
  locality := fun {U} α h ↦ by
    refine ⟨(dolbeaultLocalPredicate E X).locality α fun x ↦ ?_, fun x j hj ↦ ?_⟩
    · obtain ⟨V, hx, i, hV⟩ := h x
      exact ⟨V, hx, i, hV.1⟩
    · obtain ⟨V, hx, i, hV⟩ := h x
      exact hV.2 ⟨x, hx⟩ j hj

variable (X) in
/-- The presheaf of commutative rings underlying `dolbeault0`. -/
private def dolbeault0Pre : (Opens X)ᵒᵖ ⥤ CommRingCat.{0} where
  obj U := CommRingCat.of ↥(dolbeaultGrade E U.unop 0)
  map f := CommRingCat.ofHom (dolbeaultRes E (leOfHom f.unop)).f0
  map_id U := by
    refine CommRingCat.hom_ext (RingHom.ext fun α ↦ Subtype.ext (Subtype.ext rfl))
  map_comp f g := by
    refine CommRingCat.hom_ext (RingHom.ext fun α ↦ Subtype.ext (Subtype.ext rfl))

variable (X) in
/-- After forgetting to types, `dolbeault0Pre` is the subpresheaf of `degZeroPredicate`. -/
private def dolbeault0PreIso :
    dolbeault0Pre E X ⋙ forget CommRingCat ≅
      TopCat.subpresheafToTypes (degZeroPredicate E X).toPrelocalPredicate :=
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso
      { toFun := fun α ↦ ⟨(α.1.1 : _ → TotFibre E), α.1.2, α.2⟩
        invFun := fun f ↦ ⟨⟨f.1, f.2.1⟩, f.2.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })
    (fun _ ↦ rfl)

variable (X) in
/-- The presheaf underlying `dolbeault0` is a sheaf. -/
private theorem isSheaf_dolbeault0Pre :
    TopCat.Presheaf.IsSheaf (X := TopCat.of X) (dolbeault0Pre E X) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat)]
  exact TopCat.Presheaf.isSheaf_of_iso (dolbeault0PreIso E X).symm
    (TopCat.subpresheafToTypes.isSheaf (degZeroPredicate E X))

variable (X) in
/-- **F10, C0 (one carrier for `A⁰`).** The sheaf of commutative rings `𝒜⁰` on `X`:
`𝒜⁰(U) = CommRingCat.of ↥(𝒜_U 0)` with `GCDga.commRing0`, restriction `(dolbeaultRes h).f0`.
Its global sections are `↥(dolbeault E X 0)`, the `A⁰` of the Dolbeault algebra (same type and
ring structure). The sheaf condition: Dolbeault forms of degree `0` glue (F9, locality). -/
def dolbeault0 : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0} where
  obj :=
    { obj := fun U ↦ CommRingCat.of ↥(dolbeaultGrade E U.unop 0)
      map := fun f ↦ CommRingCat.ofHom (dolbeaultRes E (leOfHom f.unop)).f0
      map_id := fun U ↦ by
        refine CommRingCat.hom_ext (RingHom.ext fun α ↦ Subtype.ext (Subtype.ext rfl))
      map_comp := fun f g ↦ by
        refine CommRingCat.hom_ext (RingHom.ext fun α ↦ Subtype.ext (Subtype.ext rfl)) }
  property := isSheaf_dolbeault0Pre E X

/-- F10: sections of `dolbeault0 E X` over `U` are `↥(𝒜_U 0)` (rfl). -/
theorem dolbeault0_obj (U : Opens X) :
    ((dolbeault0 E X).obj.obj (op U) : Type) = ↥(dolbeaultGrade E U 0) :=
  rfl

end Cohesive
