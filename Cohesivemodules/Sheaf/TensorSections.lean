import Cohesivemodules.Sheaf.Flat.Tensor

set_option linter.style.header false

/-!
# S4.d: sections of a tensor product with a summand of a finite free module

Blueprint item S4.d (§3): for `P̃` a direct summand of a finite free module and any module `N`,
`Γ(P̃ ⊗ N) = Γ(P̃) ⊗_{R(X)} Γ(N)`. Used in C5 step 4 (quasi-cohesive structure on
`Γ(𝒜 ⊗_R K′)`, blueprint C5.a, v1.9).

The tensor product of sheaves of modules (S8.a, `tensorBifunctor`) is the sheafification of the
sectionwise tensor product. S4.d says that for `M` a direct summand of a finite free module the
sectionwise tensor product `U ↦ M(U) ⊗_{R(U)} N(U)` is already a sheaf: the unit of
sheafification is an isomorphism. Its component at `U` is the canonical map
`M(U) ⊗_{R(U)} N(U) ⟶ (M ⊗ N)(U)`, `m ⊗ n ↦ m ⊗ n`.

* `tensorSectionsMap R M N U`: the canonical map `M(U) ⊗_{R(U)} N(U) ⟶ (M ⊗ N)(U)`.
* `isIso_unit_tensorObj` (S4.d, presheaf form): for `M` a summand of a finite free module, the
  unit of sheafification at the sectionwise tensor product `M ⊗ N` is an isomorphism.
* `isIso_tensorSectionsMap` (S4.d): the canonical map is an isomorphism over every object `U`;
  at `U = ⊤` on a space this is the blueprint statement.

## Deviations
* Any site and any object `U`, not only global sections over a compact space; no fineness is
  needed. The ring is a sheaf of commutative rings `R : Sheaf J CommRingCat` (as in S8), the
  module `M` a summand of a finite free `ringOf R`-module (`IsFinFreeSummand`).
* The blueprint's `P ⊗_{S(X)} Γ(N)` with `P = Γ(P̃)` is the domain of `tensorSectionsMap` at
  `⊤`: the tensor product in `ModuleCat` over the commutative ring `R(⊤)` (Mathlib's monoidal
  structure on presheaves of modules over a presheaf of commutative rings is sectionwise).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  (R : Sheaf J CommRingCat.{0})

/-- The sectionwise tensor product `U ↦ M(U) ⊗_{R(U)} N(U)` of two sheaves of modules, as a
presheaf of `ringOf R`-modules (Mathlib's monoidal structure on presheaves of modules over a
presheaf of commutative rings). `tensorBifunctor R` is its sheafification. -/
abbrev preTensor (M N : Mod (ringOf R)) : PresheafOfModules.{0} (ringOf R).obj :=
  MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj) M.val N.val

/-- The tensor product of sheaves of modules is the sheafification of `preTensor`. -/
lemma tensorBifunctor_obj_obj_eq (M N : Mod (ringOf R)) :
    ((tensorBifunctor R).obj M).obj N = (sheafifyF R).obj (preTensor R M N) :=
  rfl

/-- The unit of sheafification at the sectionwise tensor product: the canonical map
`preTensor R M N ⟶ M ⊗ N` of presheaves of modules. -/
def tensorUnit (M N : Mod (ringOf R)) :
    preTensor R M N ⟶
      (SheafOfModules.forget (ringOf R)).obj (((tensorBifunctor R).obj M).obj N) :=
  (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app
    (preTensor R M N)

/-- **S4.d.** The canonical map `M(U) ⊗_{R(U)} N(U) ⟶ (M ⊗ N)(U)` (the component at `U` of the
unit of sheafification). -/
def tensorSectionsMap (M N : Mod (ringOf R)) (U : Cᵒᵖ) :
    (preTensor R M N).obj U ⟶ (((tensorBifunctor R).obj M).obj N).val.obj U :=
  (tensorUnit R M N).app U

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- The domain of `tensorSectionsMap` is the tensor product of the sections, in `ModuleCat` over
the commutative ring `R(U)`. -/
lemma preTensor_obj (M N : Mod (ringOf R)) (U : Cᵒᵖ) :
    (preTensor R M N).obj U =
      MonoidalCategory.tensorObj (C := ModuleCat.{0} (R.obj.obj U))
        (M.val.obj U : ModuleCat.{0} (R.obj.obj U)) (N.val.obj U) :=
  rfl

/-- Sectionwise `- ⊗ N` on presheaves of `ringOf R`-modules. -/
private def tR (N : PresheafOfModules.{0} (ringOf R).obj) :
    PresheafOfModules.{0} (ringOf R).obj ⥤ PresheafOfModules.{0} (ringOf R).obj :=
  tensorRight (C := PresheafOfModulesOfCommRing.{0} R.obj)
    (N : PresheafOfModulesOfCommRing.{0} R.obj)

private def asPM (N : PresheafOfModules.{0} (ringOf R).obj) :
    PresheafOfModulesOfCommRing.{0} R.obj := N

private instance tR_pres (N : PresheafOfModules.{0} (ringOf R).obj) (m : ℕ) :
    PreservesColimitsOfShape (Discrete (Fin m)) (tR R N) :=
  inferInstanceAs (PreservesColimitsOfShape (Discrete (Fin m))
    (tensorRight (C := PresheafOfModulesOfCommRing.{0} R.obj) (asPM R N)))

/-- The left unitor, `R ⊗ N ≅ N`, as presheaves of modules. -/
private def leftU (N : PresheafOfModules.{0} (ringOf R).obj) :
    (tR R N).obj (SheafOfModules.unit (ringOf R)).val ≅ N :=
  @leftUnitor (PresheafOfModulesOfCommRing.{0} R.obj) _ _ N

/-- The unit of sheafification is iso on `F ⊗ N` for `F` finite free. -/
private lemma isIso_unit_free (m : ℕ) (N : Mod (ringOf R)) :
    IsIso ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app
      ((tR R N.val).obj
        ((SheafOfModules.forget (ringOf R)).obj (SheafOfModules.free (Fin m))))) := by
  have h1 : PreservesColimitsOfShape (Discrete (Fin m)) (SheafOfModules.forget (ringOf R)) :=
    inferInstance
  let c1 :=
    asIso (sigmaComparison (SheafOfModules.forget (ringOf R))
        (fun _ : Fin m => SheafOfModules.unit (ringOf R)))
  let c2 :=
    asIso (sigmaComparison (tR R N.val)
        (fun _ : Fin m => (SheafOfModules.unit (ringOf R)).val))
  let c4 : ∐ (fun _ : Fin m => (SheafOfModules.forget (ringOf R)).obj N) ≅
      (SheafOfModules.forget (ringOf R)).obj (∐ fun _ : Fin m => N) :=
    asIso (sigmaComparison (SheafOfModules.forget (ringOf R)) (fun _ : Fin m => N))
  have e : (tR R N.val).obj
      ((SheafOfModules.forget (ringOf R)).obj (SheafOfModules.free (Fin m))) ≅
    (SheafOfModules.forget (ringOf R)).obj (∐ fun _ : Fin m => N) :=
    (tR R N.val).mapIso c1.symm ≪≫ c2.symm ≪≫ Sigma.mapIso (fun _ => leftU R N.val) ≪≫
      c4
  exact Adjunction.isIso_unit_app_of_iso _ e

/-- The map `M ⊗ N ⟶ M' ⊗ N` of sectionwise tensor products. -/
private abbrev whisk {M M' : Mod (ringOf R)} (f : M ⟶ M') (N : Mod (ringOf R)) :
    preTensor R M N ⟶ preTensor R M' N :=
  MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} R.obj)
    ((SheafOfModules.forget (ringOf R)).map f) N.val

/-- Naturality of `tensorUnit` in the first variable. -/
private lemma tensorUnit_naturality {M M' : Mod (ringOf R)} (f : M ⟶ M') (N : Mod (ringOf R)) :
    whisk R f N ≫ tensorUnit R M' N = tensorUnit R M N ≫
      (SheafOfModules.forget (ringOf R)).map ((sheafifyF R).map (whisk R f N)) :=
  (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.naturality
    (whisk R f N)

/-- Abstract retract argument: a morphism that is a retract of an isomorphism is an
isomorphism. -/
private lemma isIso_of_retract_aux {D : Type*} [Category D] {X F Y Z : D} (a : X ⟶ F)
    (b : F ⟶ X)
    (hab : a ≫ b = 𝟙 X) (tX : X ⟶ Y) (tF : F ⟶ Z) (ga : Y ⟶ Z) (gb : Z ⟶ Y)
    (hg : ga ≫ gb = 𝟙 Y)
    (n1 : a ≫ tF = tX ≫ ga) (n2 : b ≫ tX = tF ≫ gb) [IsIso tF] : IsIso tX := by
  refine ⟨⟨ga ≫ inv tF ≫ b, ?_, ?_⟩⟩
  · rw [← Category.assoc, ← Category.assoc, ← n1]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact hab
  · simp only [Category.assoc]
    rw [n2, IsIso.inv_hom_id_assoc]
    exact hg

/-- A retract of an isomorphism `tensorUnit` is one. -/
private lemma isIso_tensorUnit_of_retract {M F : Mod (ringOf R)} (i : M ⟶ F) (p : F ⟶ M)
    (hip : i ≫ p = 𝟙 M) (N : Mod (ringOf R)) (h : IsIso (tensorUnit R F N)) :
    IsIso (tensorUnit R M N) := by
  have hw : whisk R i N ≫ whisk R p N = 𝟙 _ := by
    have h := (MonoidalCategory.comp_whiskerRight (C := PresheafOfModulesOfCommRing.{0} R.obj)
      ((SheafOfModules.forget (ringOf R)).map i) ((SheafOfModules.forget (ringOf R)).map p)
      N.val).symm
    have hid : (SheafOfModules.forget (ringOf R)).map i ≫
        (SheafOfModules.forget (ringOf R)).map p = 𝟙 _ := by
      rw [← Functor.map_comp, hip]
      exact (SheafOfModules.forget (ringOf R)).map_id _
    exact h.trans ((congrArg (fun g => MonoidalCategory.whiskerRight
      (C := PresheafOfModulesOfCommRing.{0} R.obj) g N.val) hid).trans
      (MonoidalCategory.id_whiskerRight (C := PresheafOfModulesOfCommRing.{0} R.obj) _ _))
  have hg : (SheafOfModules.forget (ringOf R)).map ((sheafifyF R).map (whisk R i N)) ≫
      (SheafOfModules.forget (ringOf R)).map ((sheafifyF R).map (whisk R p N)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, hw, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
  exact @isIso_of_retract_aux _ _ _ _ _ _ (whisk R i N) (whisk R p N) hw (tensorUnit R M N)
    (tensorUnit R F N) _ _ hg (tensorUnit_naturality R i N) (tensorUnit_naturality R p N) h

/-- **S4.d, presheaf form.** If `M` is a direct summand of a finite free module, the sectionwise
tensor product `M ⊗ N` is already a sheaf: the unit of sheafification is an isomorphism.
Proof: true for `M = R` (`R(U) ⊗ N(U) ≅ N(U)`), for finite free `M` (finite biproducts are
sectionwise and commute with `⊗`), and for retracts by naturality of the unit in `M`. -/
theorem isIso_tensorUnit {M : Mod (ringOf R)} (hM : IsFinFreeSummand M) (N : Mod (ringOf R)) :
    IsIso (tensorUnit R M N) := by
  obtain ⟨m, i, p, hip⟩ := hM
  exact isIso_tensorUnit_of_retract R i p hip N
    (show IsIso (tensorUnit R (SheafOfModules.free (Fin m)) N) from isIso_unit_free R m N)

/-- **S4.d.** [A, proof of Lemma 7.2.7] If `M` is a direct summand of a finite free module, then
for every module `N` and every object `U` the canonical map
`M(U) ⊗_{R(U)} N(U) ⟶ (M ⊗ N)(U)` is an isomorphism. At `U = ⊤` on a space this is
`Γ(P̃ ⊗ N) = Γ(P̃) ⊗_{R(X)} Γ(N)`. -/
theorem isIso_tensorSectionsMap {M : Mod (ringOf R)} (hM : IsFinFreeSummand M)
    (N : Mod (ringOf R)) (U : Cᵒᵖ) : IsIso (tensorSectionsMap R M N U) := by
  have := isIso_tensorUnit R hM N
  exact (PresheafOfModules.evaluation _ U).map_isIso (tensorUnit R M N)

end Cohesive
