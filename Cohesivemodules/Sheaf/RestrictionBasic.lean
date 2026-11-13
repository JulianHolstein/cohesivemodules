import Cohesivemodules.Sheaf.Fine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

set_option linter.style.header false

/-!
# S5–S6: restriction, extension by zero, locality

Blueprint items S5–S6 (§3), with the restriction API decided in P3 (conventions §7,
`Scratch/P3_Restriction.lean`).

* S5.a `restr R U` (in `Sheaf/Basic.lean`) has adjoints on both sides (named instances below),
  so it is exact and preserves quasi-isomorphisms; it maps free modules to free modules.
* S5.b `extZero R U = j_!`, the left adjoint of restriction; exact; `(j_! M)|U ≅ M` (the unit is
  an isomorphism); sections of `j_! M` vanish near every point outside `U` (the stalk-free form
  of `(j_! M)_x = 0` for `x ∉ U`).
* S5.c restriction preserves injective objects.
* S6 exactness and quasi-isomorphisms are local: exactness of a short complex is checked on
  sections locally; a complex that is acyclic on the members of an open cover is acyclic; a map
  of complexes that is a quasi-isomorphism on the members of an open cover is one; a map of
  complexes that is a quasi-isomorphism on sections over every object of the site is one (any
  site: it is applied on over-sites `Over U`).

## Deviations
* The stalk formula of S5.b is replaced by its two stalk-free consequences above (no stalks of
  sheaves of modules are needed elsewhere).
* S6's last clause ("a sectionwise homotopy equivalence of presheaves of complexes induces a
  quasi-isomorphism of the associated sheaf complexes") is stated for sheaf complexes and
  sectionwise quasi-isomorphisms, which covers sectionwise homotopy equivalences (C4 applies it
  to maps of sheaf complexes).

Part 1 of 2 of the original `Sheaf/Restriction.lean`, split for size; continued in
`Sheaf/Restriction.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

variable {X : Type} [TopologicalSpace X] (R : RingSheaf X) (U : Opens X)

/-! ## S5.a Restriction -/

/-- **S5.a.** Restriction has a right adjoint (pushforward along `Over.star U`, i.e. `j_*`).
Mathlib's instance is stated for `pushforward (𝟙 _)`; `overFunctor` is a `def`. -/
instance restr_isLeftAdjoint : (restr R U).IsLeftAdjoint :=
  inferInstanceAs (SheafOfModules.pushforward.{0} (𝟙 (R.over U))).IsLeftAdjoint

/-- **S5.a.** Restriction has a left adjoint (`j_!`, S5.b). Instance search does not find the
presheaf pullback for the over-site, so it is passed explicitly (P3). -/
instance restr_isRightAdjoint : (restr R U).IsRightAdjoint :=
  @SheafOfModules.instIsRightAdjointPushforward _ _ _ _ _ _ _ _ _ _ (𝟙 (R.over U))
    (PresheafOfModules.instIsRightAdjointPushforward (F := Over.forget U)
      (R := R.obj) (S := (R.over U).obj) (𝟙 _)) _ _

/-- **S5.a.** Restriction is exact; in particular it preserves quasi-isomorphisms of complexes
(Mathlib's `quasiIso_map_of_preservesHomology`, found by instance search). -/
example : PreservesFiniteLimits (restr R U) := inferInstance
example : PreservesFiniteColimits (restr R U) := inferInstance
example {K L : CochainComplex (Mod R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := inferInstance

/-- **S5.a.** Restriction of a free module is free on the same index type. -/
def restrFreeIso (I : Type) :
    (restr R U).obj (SheafOfModules.free I) ≅ SheafOfModules.free (R := R.over U) I :=
  (SheafOfModules.mapFreeIso (restr R U) I (Iso.refl _)).symm

/-- **S5.a.** Restriction of a direct summand of a finite free module is one. -/
theorem IsFinFreeSummand.restr {M : Mod R} (hM : IsFinFreeSummand M) :
    IsFinFreeSummand ((restr R U).obj M) := by
  obtain ⟨m, i, p, hip⟩ := hM
  refine ⟨m, (Cohesive.restr R U).map i ≫ (restrFreeIso R U (Fin m)).hom,
    (restrFreeIso R U (Fin m)).inv ≫ (Cohesive.restr R U).map p, ?_⟩
  rw [Category.assoc, ← Category.assoc (restrFreeIso R U (Fin m)).hom,
    Iso.hom_inv_id, Category.id_comp, ← Functor.map_comp, hip,
    CategoryTheory.Functor.map_id]

/-! ## Helpers (sheaf-level locality, used in S5.b and S6) -/

section Helpers

variable {R}

/-- Evaluation of sheaves of modules at an object is additive. -/
instance evaluation_additive {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{0}} (V : Cᵒᵖ) : (SheafOfModules.evaluation.{0} S V).Additive where
  map_add := rfl

/-- Two morphisms of sheaves of modules that agree locally on all sections are equal. -/
lemma eq_of_locally_eq {M N : Mod R} (φ ψ : M ⟶ N)
    (h : ∀ (V : Opens X) (s : M.val.obj (op V)), ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V),
      x ∈ W ∧ φ.val.app (op W) (mres M hW s) = ψ.val.app (op W) (mres M hW s)) : φ = ψ := by
  have key : ∀ (V : Opens X) (s : M.val.obj (op V)),
      φ.val.app (op V) s = ψ.val.app (op V) s := by
    intro V s
    have hsep := Presheaf.IsSheaf.isSeparated N.isSheaf
    obtain ⟨y, hy⟩ : ∃ y : N.val.presheaf.obj (op V), y = φ.val.app (op V) s := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : N.val.presheaf.obj (op V), z = ψ.val.app (op V) s := ⟨_, rfl⟩
    rw [← hy, ← hz]
    refine hsep V
      ⟨fun {Y} f => N.val.presheaf.map f.op y = N.val.presheaf.map f.op z, ?_⟩ ?_ y z ?_
    · intro Y Z f hf g
      simp only at hf ⊢
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hf]
      rfl
    · intro x hx
      obtain ⟨W, hW, hxW, hw⟩ := h V s x hx
      refine ⟨W, homOfLE hW, ?_, hxW⟩
      have h1 := congr(ModuleCat.Hom.hom $(φ.val.naturality (homOfLE hW).op) s)
      have h2 := congr(ModuleCat.Hom.hom $(ψ.val.naturality (homOfLE hW).op) s)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
      show N.val.map (homOfLE hW).op y = N.val.map (homOfLE hW).op z
      rw [hy, hz, ← h1, ← h2]; exact hw
    · intro Y f hf
      exact hf
  ext V s
  exact key V.unop s

end Helpers
end Cohesive
end
