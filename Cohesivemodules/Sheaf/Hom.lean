import Cohesivemodules.Sheaf.HomSheafComplex

set_option linter.style.header false

/-!
# S7: Hom sheaves (Hom complexes) (part 2 of 2)

Split from `Sheaf/Hom.lean` for size; continues `Sheaf/HomSheafComplex.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite Limits
variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}}

/-- `R` commutative implies `R.over X` commutative. -/
lemma IsCommSheaf.over (hR : IsCommSheaf R) (X : C) : IsCommSheaf (R.over X) :=
  fun _ a b ↦ hR _ a b

/-- Morphisms `M|Z ⟶ N|Z` give morphisms `(M|X)|Z ⟶ (N|X)|Z` for `Z : Over X`, reindexing
along `Over (Z ⟶ X) ≃ Over Z`: the component at `W ⟶ Z` is that at the underlying map. -/
private def overOverFwd {X : C} (Z : Over X) {M N : Mod R} (φ : M.over Z.left ⟶ N.over Z.left) :
    (M.over X).over Z ⟶ (N.over X).over Z where
  val :=
    { app := fun W ↦ ModuleCat.ofHom
        (X := ((M.over X).over Z).val.obj W) (Y := ((N.over X).over Z).val.obj W)
        { toFun := fun m ↦ (φ.val.app (op (Over.mk W.unop.hom.left))).hom m
          map_add' := fun m m' ↦ map_add (φ.val.app (op (Over.mk W.unop.hom.left))).hom m m'
          map_smul' := fun r m ↦
            (φ.val.app (op (Over.mk W.unop.hom.left))).hom.map_smul r m }
      naturality := fun {W W'} g ↦ by
        ext m
        exact congrArg (fun f ↦ f.hom m) (φ.val.naturality
          (Over.homMk g.unop.left.left (by
            have h := congrArg (fun f ↦ f.left) (Over.w g.unop)
            simp only [Over.comp_left] at h
            exact h) :
            Over.mk W'.unop.hom.left ⟶ Over.mk W.unop.hom.left).op) }

/-- The object of `Over Z` (for `Z : Over X`) lying over `V ∈ Over Z.left`. -/
private def overOverObj {X : C} (Z : Over X) (V : Over Z.left) : Over Z :=
  Over.mk (Over.homMk V.hom : Over.mk (V.hom ≫ Z.hom) ⟶ Z)

/-- Inverse of `overOverFwd`: the component at `V ⟶ Z.left` is that at the corresponding
object of `Over Z`. -/
private def overOverBwd {X : C} (Z : Over X) {M N : Mod R}
    (ψ : (M.over X).over Z ⟶ (N.over X).over Z) : M.over Z.left ⟶ N.over Z.left where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := (M.over Z.left).val.obj V) (Y := (N.over Z.left).val.obj V)
        { toFun := fun m ↦ (ψ.val.app (op (overOverObj Z V.unop))).hom m
          map_add' := fun m m' ↦ map_add (ψ.val.app (op (overOverObj Z V.unop))).hom m m'
          map_smul' := fun r m ↦ (ψ.val.app (op (overOverObj Z V.unop))).hom.map_smul r m }
      naturality := fun {V V'} g ↦ by
        ext m
        exact congrArg (fun f ↦ f.hom m) (ψ.val.naturality
          (Over.homMk (Over.homMk g.unop.left (by
            show g.unop.left ≫ (V.unop.hom ≫ Z.hom) = V'.unop.hom ≫ Z.hom
            rw [← Category.assoc, Over.w g.unop]) :
              (overOverObj Z V'.unop).left ⟶ (overOverObj Z V.unop).left) (by
            apply Over.OverMorphism.ext
            exact Over.w g.unop) : overOverObj Z V'.unop ⟶ overOverObj Z V.unop).op) }

/-- `overOverObj` is inverse to `W ↦ Over.mk W.hom.left`. -/
private lemma overOverObj_mk {X : C} (Z : Over X) (W : Over Z) :
    overOverObj Z (Over.mk W.hom.left) = W := by
  have key : ∀ (l : C) (h : l ⟶ X) (f : l ⟶ Z.left) (w : f ≫ Z.hom = h),
      overOverObj Z (Over.mk f) = Over.mk (Over.homMk (U := Over.mk h) (V := Z) f w) := by
    intro l h f w
    subst w
    rfl
  exact key _ _ _ (Over.w W.hom)

/-- Components of a morphism of sheaves of modules at equal objects agree (up to `HEq`). -/
private lemma val_app_congr {C' : Type} [SmallCategory C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{0}} {M N : Mod R'} (ψ : M ⟶ N) {W W' : C'ᵒᵖ} (h : W = W') :
    HEq (ψ.val.app W) (ψ.val.app W') := by
  subst h; rfl

/-- `overOverFwd` is a left inverse of `overOverBwd`. -/
private lemma overOverFwd_bwd {X : C} (Z : Over X) {M N : Mod R}
    (ψ : (M.over X).over Z ⟶ (N.over X).over Z) :
    overOverFwd Z (overOverBwd Z ψ) = ψ :=
  hom_ext_pt fun W m ↦ by
    obtain ⟨W⟩ := W
    exact congrArg (fun f ↦ ModuleCat.Hom.hom f m)
      (eq_of_heq (val_app_congr ψ (congrArg op (overOverObj_mk Z W))))

/-- `overOverBwd` is a left inverse of `overOverFwd`. -/
private lemma overOverBwd_fwd {X : C} (Z : Over X) {M N : Mod R}
    (φ : M.over Z.left ⟶ N.over Z.left) :
    overOverBwd Z (overOverFwd Z φ) = φ :=
  hom_ext_pt fun _ _ ↦ rfl

/-- Sections of `𝓗om(M, N)|X` over `Z` and of `𝓗om(M|X, N|X)` over `Z` agree: this is the
isomorphism of modules over `R(Z.left)`. -/
private def homOverSecIso (hR : IsCommSheaf R) (M N : Mod R) {X : C} (Z : (Over X)ᵒᵖ) :
    ((homSheaf hR M N).over X).val.obj Z ≅
      (homSheaf (hR.over X) (M.over X) (N.over X)).val.obj Z where
  hom := ModuleCat.ofHom
    (X := ((homSheaf hR M N).over X).val.obj Z)
    (Y := (homSheaf (hR.over X) (M.over X) (N.over X)).val.obj Z)
    { toFun := fun φ ↦ overOverFwd Z.unop φ
      map_add' := fun φ ψ ↦ hom_ext_pt fun W m ↦ rfl
      map_smul' := fun r φ ↦ hom_ext_pt fun W m ↦ rfl }
  inv := ModuleCat.ofHom
    (X := (homSheaf (hR.over X) (M.over X) (N.over X)).val.obj Z)
    (Y := ((homSheaf hR M N).over X).val.obj Z)
    { toFun := fun ψ ↦ overOverBwd Z.unop ψ
      map_add' := fun φ ψ ↦ hom_ext_pt fun W m ↦ rfl
      map_smul' := fun r φ ↦ hom_ext_pt fun W m ↦ rfl }
  hom_inv_id := by
    ext φ
    exact overOverBwd_fwd Z.unop φ
  inv_hom_id := by
    ext ψ
    exact overOverFwd_bwd Z.unop ψ

/-- **S7. Compatibility with restriction.** `𝓗om(M, N)|X ≅ 𝓗om(M|X, N|X)` (sections over
`Z ⟶ X` on both sides are morphisms `M|Z ⟶ N|Z`, through `Over Z ≌ Over (Z ⟶ X)`). -/
def homSheafOverIso (hR : IsCommSheaf R) (M N : Mod R) (X : C) :
    (homSheaf hR M N).over X ≅ homSheaf (hR.over X) (M.over X) (N.over X) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (homOverSecIso hR M N) (fun {Z Z'} g ↦ by
      ext φ
      exact hom_ext_pt fun W m ↦ rfl))

/-- Pointwise extensionality for morphisms of sheaves of modules on any site. -/
private lemma hom_ext_pt' {C' : Type} [SmallCategory C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{0}} {A B : Mod R'} {f g : A ⟶ B}
    (h : ∀ (Z : C'ᵒᵖ) (m : A.val.obj Z), (f.val.app Z).hom m = (g.val.app Z).hom m) :
    f = g := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext m
  exact h Z m

/-- Restriction to `Over X` preserves products (checked on sections over every object, since
`evaluation` jointly reflects isomorphisms). -/
private lemma isIso_piComparison_over {ι : Type} (F : ι → Mod R) (X : C) :
    IsIso (piComparison (SheafOfModules.overFunctor.{0} R X) F) := by
  have h3 : IsIso ((SheafOfModules.toSheaf _).map
      (piComparison (SheafOfModules.overFunctor.{0} R X) F)) := by
    have h2 : IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf _).map
        (piComparison (SheafOfModules.overFunctor.{0} R X) F))) := by
      refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun Z => ?_
      have hcomp : (SheafOfModules.evaluation.{0} (R.over X) Z).map
          (piComparison (SheafOfModules.overFunctor.{0} R X) F) ≫
          piComparison (SheafOfModules.evaluation.{0} (R.over X) Z)
            (fun i ↦ (SheafOfModules.overFunctor.{0} R X).obj (F i)) =
          piComparison (SheafOfModules.evaluation.{0} R (op Z.unop.left)) F := by
        apply Pi.hom_ext
        intro i
        rw [Category.assoc, piComparison_comp_π, ← Functor.map_comp, piComparison_comp_π]
        exact (piComparison_comp_π (SheafOfModules.evaluation.{0} R (op Z.unop.left)) F i).symm
      have hcomp' : IsIso ((SheafOfModules.evaluation.{0} (R.over X) Z).map
          (piComparison (SheafOfModules.overFunctor.{0} R X) F) ≫
          piComparison (SheafOfModules.evaluation.{0} (R.over X) Z)
            (fun i ↦ (SheafOfModules.overFunctor.{0} R X).obj (F i))) := by
        rw [hcomp]
        exact (inferInstance : IsIso (piComparison
          (SheafOfModules.evaluation.{0} R (op Z.unop.left)) F))
      have hiso : IsIso ((SheafOfModules.evaluation.{0} (R.over X) Z).map
          (piComparison (SheafOfModules.overFunctor.{0} R X) F)) :=
        IsIso.of_isIso_comp_right _ (piComparison (SheafOfModules.evaluation.{0} (R.over X) Z)
            (fun i ↦ (SheafOfModules.overFunctor.{0} R X).obj (F i)))
      exact Functor.map_isIso (forget₂ (ModuleCat ↑((R.over X).obj.obj Z)) AddCommGrpCat)
        ((SheafOfModules.evaluation.{0} (R.over X) Z).map
          (piComparison (SheafOfModules.overFunctor.{0} R X) F))
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

open CochainComplex.HomComplex in
/-- Degreewise isomorphism for `homComplexOverIso`: restriction commutes with the product, and
factorwise by `homSheafOverIso`. -/
private def homComplexOverX (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (X : C)
    (n : ℤ) : (SheafOfModules.overFunctor.{0} R X).obj (homComplexX hR K L n) ≅
      homComplexX (hR.over X) ((overC X).obj K) ((overC X).obj L) n :=
  haveI := isIso_piComparison_over
    (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)) X
  asIso (piComparison (SheafOfModules.overFunctor.{0} R X)
    (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q))) ≪≫
    Pi.mapIso (fun T : Triplet n ↦ homSheafOverIso hR (K.X T.p) (L.X T.q) X)

open CochainComplex.HomComplex in
/-- `homComplexOverX` commutes with the differentials. -/
private lemma homComplexOverX_comm (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ)
    (X : C) (n : ℤ) :
    (homComplexOverX hR K L X n).hom ≫
        homComplexD (hR.over X) ((overC X).obj K) ((overC X).obj L) n =
      (SheafOfModules.overFunctor.{0} R X).map (homComplexD hR K L n) ≫
        (homComplexOverX hR K L X (n + 1)).hom := by
  have hπ : ∀ (m : ℤ) (T' : Triplet m),
      (homComplexOverX hR K L X m).hom ≫ Pi.π (fun T : Triplet m ↦
        homSheaf (hR.over X) (((overC X).obj K).X T.p) (((overC X).obj L).X T.q)) T' =
      (SheafOfModules.overFunctor.{0} R X).map (Pi.π (fun T : Triplet m ↦
        homSheaf hR (K.X T.p) (L.X T.q)) T') ≫
        (homSheafOverIso hR (K.X T'.p) (L.X T'.q) X).hom := by
    intro m T'
    unfold homComplexOverX
    simp only [Iso.trans_hom, asIso_hom, Category.assoc]
    show _ ≫ Limits.Pi.map
      (fun T : Triplet m ↦ (homSheafOverIso hR (K.X T.p) (L.X T.q) X).hom) ≫ _ = _
    erw [Limits.Pi.map_π]
    rw [← Category.assoc, piComparison_comp_π]
  apply Pi.hom_ext
  intro T
  have e1 : ∀ {A B : Mod R} (z : ℤˣ) (f : A ⟶ B),
      (SheafOfModules.overFunctor.{0} R X).map (z • f) =
        z • (SheafOfModules.overFunctor.{0} R X).map f := fun z f ↦ by
    rw [Units.smul_def, Units.smul_def]
    exact Functor.map_zsmul _
  simp only [Category.assoc]
  rw [hπ (n + 1) T, homComplexD_π (hR.over X) ((overC X).obj K) ((overC X).obj L) n T,
    ← Functor.map_comp_assoc, homComplexD_π hR K L n T]
  rw [Preadditive.comp_add, Linear.comp_units_smul, Functor.map_add, e1,
    Preadditive.add_comp, Linear.units_smul_comp]
  congr 1
  · rw [← Category.assoc, hπ n, Category.assoc, Functor.map_comp, Category.assoc]
    congr 1
  · congr 1
    rw [← Category.assoc, hπ n, Category.assoc, Functor.map_comp, Category.assoc]
    congr 1

/-- **S7. Compatibility with restriction**, for complexes: `𝓗om(K, L)|X ≅ 𝓗om(K|X, L|X)`. -/
def homComplexOverIso (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (X : C) :
    (overC X).obj (homSheafComplex hR K L) ≅
      homSheafComplex (hR.over X) ((overC X).obj K) ((overC X).obj L) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ homComplexOverX hR K L X n) (fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    have e : ((overC X).obj (homSheafComplex hR K L)).d i (i + 1) =
        (SheafOfModules.overFunctor.{0} R X).map (homComplexD hR K L i) := by
      rw [Functor.mapHomologicalComplex_obj_d, homComplex_d]
      rfl
    rw [homComplex_d, e]
    exact homComplexOverX_comm hR K L X i)

/-! ## On a space (S7.b, S7.c are in `Sheaf/HomAcyclic.lean`) -/

section Space

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

/-- `IsComm` (S1) is `IsCommSheaf` on `Opens X`. -/
lemma IsComm.isCommSheaf {R : RingSheaf X} (hR : ∀ (U : TopologicalSpace.Opens X)
    (a b : R.obj.obj (op U)), a * b = b * a) : IsCommSheaf R :=
  fun U a b ↦ hR U.unop a b

end Space

end Cohesive
