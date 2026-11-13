import Cohesivemodules.Sheaf.Hom

set_option linter.style.header false

/-!
# C4 helpers: morphisms between restrictions to `⊤`

`M.over ⊤ ⟶ N.over ⊤` is the same as `M ⟶ N` on `Opens X` (`⊤` is terminal), used for audit G4
(`exists_cochain_overTop_equiv` in `Comparison/FullyFaithful.lean`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

/-- A morphism `M.over ⊤ ⟶ N.over ⊤` as a morphism `M ⟶ N`: components at `Over.mk (V ≤ ⊤)`. -/
def overTopApp {M N : Mod R} (g : M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X))
    (V : (Opens X)ᵒᵖ) : M.val.presheaf.obj V ⟶ N.val.presheaf.obj V :=
  (PresheafOfModules.toPresheaf _ |>.map g.val).app (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤))))

/-- Naturality of `overTopApp`. -/
theorem overTopApp_naturality {M N : Mod R} (g : M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X))
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    M.val.presheaf.map f ≫ overTopApp g W = overTopApp g V ≫ N.val.presheaf.map f :=
  (PresheafOfModules.toPresheaf _ |>.map g.val).naturality
    (Over.homMk f.unop : Over.mk (homOfLE (le_top : W.unop ≤ ⊤)) ⟶ Over.mk (homOfLE le_top)).op

def overTopHom {M N : Mod R} (g : M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X)) : M ⟶ N :=
  ⟨PresheafOfModules.homMk (M₁ := M.val) (M₂ := N.val)
    { app := overTopApp g
      naturality := fun {_ _} f ↦ overTopApp_naturality g f }
    (fun V r m ↦ (g.val.app (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤))))).hom.map_smul r m)⟩

/-- Components of `overTopHom`. -/
theorem overTopHom_app_apply {M N : Mod R} (g : M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X))
    (V : (Opens X)ᵒᵖ) (m : M.val.obj V) :
    ((overTopHom g).val.app V).hom m =
      (g.val.app (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤))))).hom m := by
  unfold overTopHom overTopApp
  rfl

/-- `overTopHom` is a left inverse of restriction. -/
theorem overTopHom_over {M N : Mod R} (f : M ⟶ N) : overTopHom (f.over (⊤ : Opens X)) = f := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun m ↦ ?_
  rfl

/-- `overTopHom` is a right inverse of restriction. -/
theorem over_overTopHom {M N : Mod R} (g : M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X)) :
    (overTopHom g).over (⊤ : Opens X) = g := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun m ↦ ?_
  rfl

/-- `overTopHom` is additive. -/
theorem overTopHom_add {M N : Mod R} (g g' : M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X)) :
    overTopHom (g + g') = overTopHom g + overTopHom g' := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun m ↦ ?_
  rfl

/-- Morphisms between the restrictions to `⊤` are morphisms (`⊤` is terminal). -/
def overTopEquiv (M N : Mod R) :
    (M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X)) ≃+ (M ⟶ N) where
  toFun := overTopHom
  invFun f := f.over (⊤ : Opens X)
  left_inv := over_overTopHom
  right_inv := overTopHom_over
  map_add' := overTopHom_add

/-- `overTopHom` is natural in the target. -/
theorem overTopHom_comp_over {M N N' : Mod R} (g : M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X))
    (f : N ⟶ N') : overTopHom (g ≫ f.over (⊤ : Opens X)) = overTopHom g ≫ f := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun m ↦ ?_
  rfl

/-- `overTopHom` is natural in the source. -/
theorem overTopHom_over_comp {M M' N : Mod R} (f : M' ⟶ M)
    (g : M.over (⊤ : Opens X) ⟶ N.over (⊤ : Opens X)) :
    overTopHom (f.over (⊤ : Opens X) ≫ g) = f ≫ overTopHom g := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun m ↦ ?_
  rfl

end Cohesive
