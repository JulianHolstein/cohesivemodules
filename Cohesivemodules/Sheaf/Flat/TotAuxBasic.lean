import Cohesivemodules.Sheaf.Flat.TensorLoc

set_option linter.style.header false

/-!
# S8 (part 2): total complexes of bifunctors

Blueprint item S8 (§3). Split from `Sheaf/Flat.lean` for size only (CLAUDE.md: "New work goes in
small new files"); no mathematical change. Generic facts about
`HomologicalComplex.mapBifunctor` over `ComplexShape.up ℤ`.

Part 1 of 2 of the original `Sheaf/Flat/TotAux.lean`, split for size; continued in
`Sheaf/Flat/TotAux.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace

/-! ### Total complexes of bifunctors: abstract lemmas

Generic facts about `HomologicalComplex.mapBifunctor` over `ComplexShape.up ℤ`, used for the
tensor product of complexes: tensoring with a complex concentrated in degree `0`, and invariance
under natural isomorphisms of bifunctors. -/

section TotAux

open HomologicalComplex

/-- The sum condition for the total complex of two `up ℤ` complexes. -/
private lemma up_π_eq (p q n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    (ComplexShape.up ℤ) (p, q) = n) : p + q = n := h

section Single

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasZeroObject C₁]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  (A : C₁) (L : CochainComplex C₂ ℤ)
  [((single C₁ (ComplexShape.up ℤ) 0).obj A).HasMapBifunctor L F (ComplexShape.up ℤ)]

/-- Degreewise isomorphism `(A[0] ⊗ L)^n ≅ F(A)(L^n)`. -/
private noncomputable def singleTotX (n : ℤ) :
    (((single C₁ (ComplexShape.up ℤ) 0).obj A).mapBifunctor L F (ComplexShape.up ℤ)).X n ≅
      (F.obj A).obj (L.X n) where
  hom := mapBifunctorDesc (fun p q h =>
    if hp : p = 0 then
      (F.map (singleObjXIsoOfEq (ComplexShape.up ℤ) 0 A p hp).hom).app (L.X q) ≫
        (F.obj A).map (eqToHom (congrArg L.X (by have := up_π_eq p q n h; omega)))
    else 0)
  inv := (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 A).inv).app (L.X n) ≫
    ιMapBifunctor _ L F (ComplexShape.up ℤ) 0 n n (by simp [ComplexShape.π])
  hom_inv_id := by
    refine mapBifunctor.hom_ext fun p q h => ?_
    have hpq := up_π_eq p q n h
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = n := by omega
      simp [singleObjXSelf]
    · have hz : IsZero ((F.obj (((single C₁ (ComplexShape.up ℤ) 0).obj A).X p)).obj (L.X q)) :=
        ((evaluation C₂ D).obj (L.X q)).map_isZero
          (F.map_isZero (isZero_single_obj_X _ 0 A p hp))
      exact hz.eq_of_src _ _
  inv_hom_id := by
    simp [singleObjXSelf]

/-- `A[0] ⊗ L` is `F(A)` applied termwise to `L`. -/
noncomputable def singleTotIso :
    ((single C₁ (ComplexShape.up ℤ) 0).obj A).mapBifunctor L F (ComplexShape.up ℤ) ≅
      ((F.obj A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
  Hom.isoOfComponents (fun n => singleTotX F A L n) (fun n m hnm => by
    refine mapBifunctor.hom_ext fun p q h => ?_
    have hpq := up_π_eq p q n h
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = n := by omega
      have hm : (0 : ℤ) + (q + 1) = m := by have := hnm; simp at this; omega
      have hRel : (ComplexShape.up ℤ).Rel q m := hnm
      have hm' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (0, m) = m := by simp [ComplexShape.π]
      rw [mapBifunctor.d_eq, Preadditive.add_comp,
        Preadditive.comp_add, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc,
        mapBifunctor.d₂_eq _ _ _ _ _ hRel _ hm']
      have hd₁ : mapBifunctor.d₁ ((single C₁ (ComplexShape.up ℤ) 0).obj A) L F
          (ComplexShape.up ℤ) 0 q m = 0 := by
        rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
        simp
      have hι : ((single C₁ (ComplexShape.up ℤ) 0).obj A).ιMapBifunctor L F (ComplexShape.up ℤ)
          0 q q h ≫ (singleTotX F A L q).hom =
          (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 A).hom).app (L.X q) := by
        simp [singleTotX, singleObjXSelf]
      have hι' : ((single C₁ (ComplexShape.up ℤ) 0).obj A).ιMapBifunctor L F (ComplexShape.up ℤ)
          0 m m hm' ≫ (singleTotX F A L m).hom =
          (F.map (singleObjXSelf (ComplexShape.up ℤ) 0 A).hom).app (L.X m) := by
        simp [singleTotX, singleObjXSelf]
      rw [hd₁, zero_comp, zero_add, ← Category.assoc, hι]
      simp [Category.assoc, hι']
    · have hz : IsZero ((F.obj (((single C₁ (ComplexShape.up ℤ) 0).obj A).X p)).obj (L.X q)) :=
        ((evaluation C₂ D).obj (L.X q)).map_isZero
          (F.map_isZero (isZero_single_obj_X _ 0 A p hp))
      exact hz.eq_of_src _ _)

end Single

section Congr

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D] {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
  (F G : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive] [G.Additive]
  [∀ X, (G.obj X).Additive] (α : F ≅ G)
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [K₁.HasMapBifunctor K₂ F c] [K₁.HasMapBifunctor K₂ G c]

/-- A natural isomorphism of bifunctors induces an isomorphism of total complexes. -/
noncomputable def mapBifunctorNatIso :
    K₁.mapBifunctor K₂ F c ≅ K₁.mapBifunctor K₂ G c :=
  HomologicalComplex₂.total.mapIso (HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex.Hom.isoOfComponents
      (fun q => (α.app (K₁.X p)).app (K₂.X q))
      (fun q q' _ => ((α.hom.app (K₁.X p)).naturality (K₂.d q q')).symm))
    (fun p p' _ => by
      ext q
      exact (NatTrans.congr_app (α.hom.naturality (K₁.d p p')) (K₂.X q)).symm)) c

/-- `mapBifunctorNatIso` on summands. -/
private lemma ι_mapBifunctorNatIso_hom (i₁ : I₁) (i₂ : I₂) (j : J)
    (h : ComplexShape.π c₁ c₂ c (i₁, i₂) = j) :
    ιMapBifunctor K₁ K₂ F c i₁ i₂ j h ≫ (mapBifunctorNatIso K₁ K₂ F G α c).hom.f j =
      (α.hom.app (K₁.X i₁)).app (K₂.X i₂) ≫ ιMapBifunctor K₁ K₂ G c i₁ i₂ j h := by
  simp only [mapBifunctorNatIso, HomologicalComplex₂.total.mapIso]
  erw [HomologicalComplex₂.ιTotal_map]
  rfl

/-- Naturality of `mapBifunctorNatIso`. -/
private lemma mapBifunctorNatIso_hom_naturality {L₁ : HomologicalComplex C₁ c₁}
    {L₂ : HomologicalComplex C₂ c₂} [L₁.HasMapBifunctor L₂ F c] [L₁.HasMapBifunctor L₂ G c]
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂) :
    mapBifunctorMap f₁ f₂ F c ≫ (mapBifunctorNatIso L₁ L₂ F G α c).hom =
      (mapBifunctorNatIso K₁ K₂ F G α c).hom ≫ mapBifunctorMap f₁ f₂ G c := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  refine mapBifunctor.hom_ext fun i₁ i₂ h => ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc, ← Category.assoc,
    ι_mapBifunctorMap, ι_mapBifunctorNatIso_hom]
  simp only [Category.assoc]
  rw [ι_mapBifunctorNatIso_hom, ι_mapBifunctorMap]
  have n1 := (α.hom.app (L₁.X i₁)).naturality (f₂.f i₂)
  have n2 : (F.map (f₁.f i₁)).app (K₂.X i₂) ≫ (α.hom.app (L₁.X i₁)).app (K₂.X i₂) =
      (α.hom.app (K₁.X i₁)).app (K₂.X i₂) ≫ (G.map (f₁.f i₁)).app (K₂.X i₂) :=
    NatTrans.congr_app (α.hom.naturality (f₁.f i₁)) (K₂.X i₂)
  rw [reassoc_of% n1, reassoc_of% n2]

/-- Naturality of the symmetry isomorphism built from a symmetry `F ≅ F.flip`. -/
lemma symIso_naturality {C₀ : Type*} [Category C₀] [Preadditive C₀]
    (E : C₀ ⥤ C₀ ⥤ D) [E.Additive] [∀ X, (E.obj X).Additive] (β : E ≅ E.flip)
    [E.flip.Additive] [∀ X, (E.flip.obj X).Additive]
    {K K' L : HomologicalComplex C₀ c₁} [TotalComplexShape c₁ c₁ c]
    [TotalComplexShape c₁ c₁ c] [TotalComplexShapeSymmetry c₁ c₁ c]
    [K.HasMapBifunctor L E c] [K'.HasMapBifunctor L E c] [K.HasMapBifunctor L E.flip c]
    [K'.HasMapBifunctor L E.flip c] [L.HasMapBifunctor K E c] [L.HasMapBifunctor K' E c]
    [L.HasMapBifunctor K E.flip c] [L.HasMapBifunctor K' E.flip c]
    (f : K ⟶ K') :
    mapBifunctorMap f (𝟙 L) E c ≫ (mapBifunctorNatIso K' L E E.flip β c ≪≫
        HomologicalComplex.mapBifunctorFlipIso L K' E c).hom =
      (mapBifunctorNatIso K L E E.flip β c ≪≫
        HomologicalComplex.mapBifunctorFlipIso L K E c).hom ≫ mapBifunctorMap (𝟙 L) f E c := by
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
    mapBifunctorNatIso_hom_naturality K L E E.flip β c f (𝟙 L), Category.assoc,
    HomologicalComplex.mapBifunctorFlipIso_hom_naturality (𝟙 L) f E c, Category.assoc]

end Congr

end TotAux
end Cohesive
end
