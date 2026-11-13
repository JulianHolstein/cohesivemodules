import Cohesivemodules.Sheaf.Flat.Brutal
import Cohesivemodules.Sheaf.RingOfDef

set_option linter.style.header false

/-!
# S8 (part 4): the tensor bifunctor, `IsFlat`, `IsKFlat`

Blueprint item S8 (§3), S8.a (tensor part) and the start of S8.b. Split from `Sheaf/Flat.lean`
for size only (CLAUDE.md: "New work goes in small new files"); no mathematical change. See the
module doc of `Sheaf/Flat.lean` for conventions and deviations.

* `sheafifyF R` (`ringOf R` is in `Sheaf/RingOfDef.lean`), `tensorBifunctor R`, the total complex `tensorC R K L` with its
  functoriality, symmetry, unit and cone isomorphisms.
* `IsFlat R M`, `IsKFlat R K`; `isFlat_unit`; the comparison `∐ (M i ⊗ A) ⟶ (∐ M) ⊗ A`
  (preparation for `isFlat_sigma`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

variable (R : Sheaf J CommRingCat.{0})

/-- Sheafification of presheaves of `ringOf R`-modules (Mathlib's
`PresheafOfModules.sheafification` along the identity). -/
abbrev sheafifyF : PresheafOfModules.{0} (ringOf R).obj ⥤ Mod (ringOf R) :=
  PresheafOfModules.sheafification.{0} (𝟙 (ringOf R).obj)

/-- **S8.a. Tensor product** of sheaves of `R`-modules: `M ⊗ N` is the sheafification of the
presheaf `X ↦ M(X) ⊗_{R(X)} N(X)` (Mathlib's monoidal structure on presheaves of modules over a
presheaf of commutative rings). -/
def tensorBifunctor : Mod (ringOf R) ⥤ Mod (ringOf R) ⥤ Mod (ringOf R) :=
  SheafOfModules.forget _ ⋙
    (curriedTensor (PresheafOfModulesOfCommRing.{0} R.obj) :
      PresheafOfModules.{0} (ringOf R).obj ⥤ PresheafOfModules.{0} (ringOf R).obj ⥤
        PresheafOfModules.{0} (ringOf R).obj) ⋙
    (Functor.whiskeringLeft _ _ _).obj (SheafOfModules.forget _) ⋙
    (Functor.whiskeringRight _ _ _).obj (sheafifyF R)

/-- The tensor product, object level: the sheafification of the sectionwise tensor product. -/
lemma tensorBifunctor_obj_obj (M N : Mod (ringOf R)) :
    ((tensorBifunctor R).obj M).obj N = (sheafifyF R).obj
      (MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj) M.val N.val) :=
  rfl

/-- Sheafification inverts a morphism of presheaves of modules that is locally bijective on the
underlying presheaves of abelian groups. -/
lemma isIso_sheafifyF_map_of_locallyBijective {P Q : PresheafOfModules.{0} (ringOf R).obj}
    (f : P ⟶ Q) [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)] :
    IsIso ((sheafifyF R).map f) := by
  have hW : J.W ((PresheafOfModules.toPresheaf _).map f) := J.W_of_isLocallyBijective _
  have h : IsIso ((SheafOfModules.toSheaf (ringOf R)).map ((sheafifyF R).map f)) :=
    (J.W_iff _).1 hW
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf (ringOf R))

/-- **S8.a. Tensor products commute with sheafification.** For presheaves of modules `P`, `N`,
the map `P ⊗ N ⟶ (a P) ⊗ N` induced by the unit `P ⟶ a P` of sheafification becomes an
isomorphism after sheafification: `a (P ⊗ N) ≅ a ((a P) ⊗ N)`. Proof: `P ⟶ a P` is locally
bijective, and `- ⊗ N` (sectionwise) preserves locally bijective maps, being right exact
sectionwise with locally zero kernel and cokernel. The basic input for `isFlat_sigma`,
`restrTensorIso`, `IsFlat.restr`. -/
theorem isIso_sheafifyF_map_whiskerRight (P N : PresheafOfModules.{0} (ringOf R).obj) :
    IsIso ((sheafifyF R).map (MonoidalCategory.whiskerRight
      (C := PresheafOfModulesOfCommRing.{0} R.obj)
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P) N)) := by
  have hi : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat)).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P)) :=
    (inferInstance : Presheaf.IsLocallyInjective J (toSheafify J P.presheaf))
  have hs : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf
      (R.obj ⋙ forget₂ CommRingCat RingCat)).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P)) :=
    (inferInstance : Presheaf.IsLocallySurjective J (toSheafify J P.presheaf))
  have h1 := tensor_locInj (R₀ := R.obj) J N
    ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P)
  have h2 := tensor_locSurj (R₀ := R.obj) J N
    ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P)
  exact @isIso_sheafifyF_map_of_locallyBijective _ _ _ _ _ R _ _ _ h1 h2

/-- The sectionwise tensor product `M ⊗ -` of presheaves of modules is additive. -/
private lemma curriedTensor_obj_additive (M : PresheafOfModulesOfCommRing.{0} R.obj) :
    ((curriedTensor (PresheafOfModulesOfCommRing.{0} R.obj)).obj M).Additive where
  map_add {N N' f g} := by
    show M ◁ (f + g) = M ◁ f + M ◁ g
    ext X : 1
    simp only [PresheafOfModulesOfCommRing.whiskerLeft_app]
    have h1 : (M ◁ f + M ◁ g).app X = (M ◁ f).app X + (M ◁ g).app X := rfl
    have h2 : PresheafOfModules.Hom.app' (f + g) X = f.app' X + g.app' X := rfl
    rw [h1, h2, MonoidalPreadditive.whiskerLeft_add]
    rfl

/-- Sheafification of presheaves of `ringOf R`-modules is additive (left exact). -/
private lemma sheafifyF_additive : (sheafifyF R).Additive := by
  have : (sheafifyF R).PreservesZeroMorphisms := inferInstance
  exact Functor.additive_of_preserves_binary_products _

instance tensorBifunctor_additive (M : Mod (ringOf R)) : ((tensorBifunctor R).obj M).Additive := by
  have h1 := curriedTensor_obj_additive R M.val
  have h2 := sheafifyF_additive R
  let T : PresheafOfModules.{0} (ringOf R).obj ⥤ PresheafOfModules.{0} (ringOf R).obj :=
    (curriedTensor (PresheafOfModulesOfCommRing.{0} R.obj)).obj M.val
  have h1' : T.Additive := h1
  show (SheafOfModules.forget _ ⋙ T ⋙ sheafifyF R).Additive
  infer_instance

/-- Right whiskering by the sectionwise tensor product is additive. -/
private lemma whiskerRight_add' (M M' : PresheafOfModulesOfCommRing.{0} R.obj) (f g : M ⟶ M')
    (N : PresheafOfModulesOfCommRing.{0} R.obj) : (f + g) ▷ N = f ▷ N + g ▷ N := by
  ext X : 1
  simp only [PresheafOfModulesOfCommRing.whiskerRight_app]
  have h1 : (f ▷ N + g ▷ N).app X = (f ▷ N).app X + (g ▷ N).app X := rfl
  have h2 : PresheafOfModules.Hom.app' (f + g) X = f.app' X + g.app' X := rfl
  rw [h1, h2, MonoidalPreadditive.add_whiskerRight]
  rfl

instance tensorBifunctor_additive': (tensorBifunctor R).Additive where
  map_add {M M' f g} := by
    have h2 := sheafifyF_additive R
    ext N : 2
    have key := whiskerRight_add' R M.val M'.val f.val g.val N.val
    exact (congrArg (sheafifyF R).map key).trans (Functor.map_add _)

/-- **S8.a.** The tensor product `K ⊗ L` of complexes of sheaves of `R`-modules: the total
complex of the double complex `Kᵖ ⊗ L^q` (Mathlib's `mapBifunctor`; Koszul sign on the second
differential, as in Mathlib's `ComplexShape.up ℤ` total complex). -/
def tensorC (K L : CochainComplex (Mod (ringOf R)) ℤ) : CochainComplex (Mod (ringOf R)) ℤ :=
  K.mapBifunctor L (tensorBifunctor R) (ComplexShape.up ℤ)

/-- **S8.a.** Functoriality of `K ⊗ L` in `L`. -/
def tensorCMap₂ (K : CochainComplex (Mod (ringOf R)) ℤ)
    {L L' : CochainComplex (Mod (ringOf R)) ℤ} (g : L ⟶ L') : tensorC R K L ⟶ tensorC R K L' :=
  HomologicalComplex.mapBifunctorMap (𝟙 K) g (tensorBifunctor R) (ComplexShape.up ℤ)

/-- **S8.a.** Functoriality of `K ⊗ L` in `K`. -/
def tensorCMap₁ {K K' : CochainComplex (Mod (ringOf R)) ℤ} (f : K ⟶ K')
    (L : CochainComplex (Mod (ringOf R)) ℤ) : tensorC R K L ⟶ tensorC R K' L :=
  HomologicalComplex.mapBifunctorMap f (𝟙 L) (tensorBifunctor R) (ComplexShape.up ℤ)

/-- **S8.a.** The tensor product of complexes commutes with mapping cones in the second variable:
`K ⊗ cone(g) ≅ cone(K ⊗ g)` (degreewise `K^p ⊗ (L^{q+1} ⊞ L'^q)`; the comparison twists the
`L`-part by the Koszul sign `(-1)^p`). -/
def tensorCConeIso₂ (K : CochainComplex (Mod (ringOf R)) ℤ)
    {L L' : CochainComplex (Mod (ringOf R)) ℤ} (g : L ⟶ L') :
    tensorC R K (CochainComplex.mappingCone g) ≅
      CochainComplex.mappingCone (tensorCMap₂ R K g) :=
  coneIso₂ (tensorBifunctor R) K g

/-- The braiding of the sectionwise tensor product of presheaves of modules. -/
private noncomputable def braidPre (X Y : PresheafOfModulesOfCommRing.{0} R.obj) :
    MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj) X Y ≅
      MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj) Y X :=
  β_ X Y

/-- Naturality of `braidPre` in the first variable. -/
private lemma braidPre_naturality_left {X X' : PresheafOfModulesOfCommRing.{0} R.obj} (g : X ⟶ X')
    (Y : PresheafOfModulesOfCommRing.{0} R.obj) :
    MonoidalCategory.whiskerRight g Y ≫ (braidPre R X' Y).hom =
      (braidPre R X Y).hom ≫ MonoidalCategory.whiskerLeft Y g :=
  BraidedCategory.braiding_naturality_left g Y

/-- Naturality of `braidPre` in the second variable. -/
private lemma braidPre_naturality_right (X : PresheafOfModulesOfCommRing.{0} R.obj)
    {Y Y' : PresheafOfModulesOfCommRing.{0} R.obj} (g : Y ⟶ Y') :
    MonoidalCategory.whiskerLeft X g ≫ (braidPre R X Y').hom =
      (braidPre R X Y).hom ≫ MonoidalCategory.whiskerRight g X :=
  BraidedCategory.braiding_naturality_right X g

/-- The tensor bifunctor is symmetric: `(tensorBifunctor R).flip ≅ tensorBifunctor R`
(the braiding of presheaves of modules, sheafified). -/
noncomputable def tensorBifunctorFlipIso : (tensorBifunctor R).flip ≅ tensorBifunctor R :=
  NatIso.ofComponents (fun a => NatIso.ofComponents
    (fun b => (sheafifyF R).mapIso (braidPre R b.val a.val))
    (fun {b b'} g => by
      exact ((sheafifyF R).map_comp _ _).symm.trans
        ((congrArg (sheafifyF R).map (braidPre_naturality_left R g.val a.val)).trans
          ((sheafifyF R).map_comp _ _))))
    (fun {a a'} f => by
      refine NatTrans.ext (funext fun b => ?_)
      exact ((sheafifyF R).map_comp _ _).symm.trans
        ((congrArg (sheafifyF R).map (braidPre_naturality_right R b.val f.val)).trans
          ((sheafifyF R).map_comp _ _)))

/-- **S8.a.** Symmetry of the tensor product of complexes, `K ⊗ L ≅ L ⊗ K` (the braiding of
presheaves of modules, sheafified, with the Koszul sign `(-1)^{pq}` on `Kᵖ ⊗ L^q`). -/
def tensorCSymIso (K L : CochainComplex (Mod (ringOf R)) ℤ) : tensorC R K L ≅ tensorC R L K :=
  haveI : (tensorBifunctor R).flip.Additive := { }
  haveI : ∀ X, ((tensorBifunctor R).flip.obj X).Additive := fun X => { }
  mapBifunctorNatIso K L (tensorBifunctor R) (tensorBifunctor R).flip
    (tensorBifunctorFlipIso R).symm (ComplexShape.up ℤ) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K (tensorBifunctor R) (ComplexShape.up ℤ)

/-- Naturality of the symmetry iso of `tensorC` in the first variable. -/
private lemma tensorCSymIso_naturality₁ {K K' : CochainComplex (Mod (ringOf R)) ℤ} (f : K ⟶ K')
    (L : CochainComplex (Mod (ringOf R)) ℤ) :
    tensorCMap₁ R f L ≫ (tensorCSymIso R K' L).hom =
      (tensorCSymIso R K L).hom ≫ tensorCMap₂ R L f := by
  haveI : (tensorBifunctor R).flip.Additive := { }
  haveI : ∀ X, ((tensorBifunctor R).flip.obj X).Additive := fun X => { }
  exact symIso_naturality (c := ComplexShape.up ℤ) (tensorBifunctor R)
    (tensorBifunctorFlipIso R).symm f

/-- **S8.a.** Tensoring with a module placed in degree `0`: `A[0] ⊗ L` is `A ⊗ -` applied
termwise to `L`. -/
def tensorCSingleIso (A : Mod (ringOf R)) (L : CochainComplex (Mod (ringOf R)) ℤ) :
    tensorC R ((HomologicalComplex.single (Mod (ringOf R)) (ComplexShape.up ℤ) 0).obj A) L ≅
      (((tensorBifunctor R).obj A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
  singleTotIso (tensorBifunctor R) A L

/-- **S8.a.** The tensor product of complexes commutes with mapping cones in the first variable:
`cone(f) ⊗ L ≅ cone(f ⊗ L)`. (Declared after `tensorCSymIso`, from which it is derived.) -/
def tensorCConeIso₁ {K K' : CochainComplex (Mod (ringOf R)) ℤ} (f : K ⟶ K')
    (L : CochainComplex (Mod (ringOf R)) ℤ) :
    tensorC R (CochainComplex.mappingCone f) L ≅
      CochainComplex.mappingCone (tensorCMap₁ R f L) :=
  have w : (tensorCSymIso R _ L).inv ≫ tensorCMap₁ R f L =
      tensorCMap₂ R L f ≫ (tensorCSymIso R _ L).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact tensorCSymIso_naturality₁ R f L
  tensorCSymIso R _ L ≪≫ tensorCConeIso₂ R L f ≪≫
    HomologicalComplex.homotopyCofiber.mapArrowIso (tensorCMap₂ R L f) (tensorCMap₁ R f L)
      (fun j => ⟨j - 1, by simp⟩)
      (Arrow.isoMk (tensorCSymIso R _ L).symm (tensorCSymIso R _ L).symm w)

/-- **S8.b. Flat modules.** `M` is flat if `M ⊗ -` preserves monomorphisms (it is right exact,
as a composite of left adjoints and the right exact presheaf tensor product). -/
def IsFlat (M : Mod (ringOf R)) : Prop :=
  ((tensorBifunctor R).obj M).PreservesMonomorphisms

/-- **S8. K-flat complexes.** `K` is K-flat if `K ⊗ L` is acyclic for every acyclic `L`
[Stacks, section on K-flat complexes of modules on ringed sites]. -/
def IsKFlat (K : CochainComplex (Mod (ringOf R)) ℤ) : Prop :=
  ∀ L : CochainComplex (Mod (ringOf R)) ℤ, L.Acyclic → (tensorC R K L).Acyclic

/-- A map between acyclic complexes is a quasi-isomorphism. -/
private lemma quasiIso_of_acyclic {A B : CochainComplex (Mod (ringOf R)) ℤ} (hA : A.Acyclic)
    (hB : B.Acyclic) (f : A ⟶ B) : QuasiIso f where
  quasiIsoAt i := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact IsZero.isIso ((hA i).isZero_homology) ((hB i).isZero_homology) _

/-- **S8.** The mapping cone of a map between K-flat complexes is K-flat:
`cone(f) ⊗ L ≅ cone(f ⊗ L)` (`tensorCConeIso₁`), the cone of a map between acyclic complexes. -/
theorem IsKFlat.mappingCone {K K' : CochainComplex (Mod (ringOf R)) ℤ} (hK : IsKFlat R K)
    (hK' : IsKFlat R K') (f : K ⟶ K') : IsKFlat R (CochainComplex.mappingCone f) := by
  intro L hL
  have hc := (tensorCConeIso₁ R f L)
  have hA := hK L hL
  have hB := hK' L hL
  have hq : QuasiIso (tensorCMap₁ R f L) :=
    quasiIso_of_acyclic R hA hB _
  have hcone := (quasiIso_iff_acyclic_mappingCone (tensorCMap₁ R f L)).1 hq
  exact fun i => (hcone i).of_iso (tensorCConeIso₁ R f L).symm

/-- Tensoring a monomorphism of presheaves of modules with the unit gives a monomorphism. -/
private lemma unit_whiskerLeft_mono {A B : PresheafOfModulesOfCommRing.{0} R.obj} (f : A ⟶ B)
    (hf : Mono f) : Mono ((𝟙_ (PresheafOfModulesOfCommRing.{0} R.obj)) ◁ f) := by
  have : (𝟙_ (PresheafOfModulesOfCommRing.{0} R.obj)) ◁ f = (λ_ A).hom ≫ f ≫ (λ_ B).inv := by
    rw [← cancel_mono (λ_ B).hom, MonoidalCategory.leftUnitor_naturality]
    simp
  rw [this]
  infer_instance

/-- **S8.b.** The unit module `R` is flat. -/
theorem isFlat_unit : IsFlat R (SheafOfModules.unit (ringOf R)) := by
  refine ⟨fun {N N'} f hf => ?_⟩
  have := hf
  have h1 : Mono ((SheafOfModules.forget (ringOf R)).map f) := inferInstance
  have h2 : ((tensorBifunctor R).obj (SheafOfModules.unit (ringOf R))).map f =
      (sheafifyF R).map ((𝟙_ (PresheafOfModulesOfCommRing.{0} R.obj)) ◁
        ((SheafOfModules.forget (ringOf R)).map f : _)) := rfl
  have h3 := unit_whiskerLeft_mono R
    (A := (SheafOfModules.forget (ringOf R)).obj N) (B := (SheafOfModules.forget (ringOf R)).obj N')
    ((SheafOfModules.forget (ringOf R)).map f) h1
  rw [h2]
  exact @Functor.map_mono _ _ _ _ (sheafifyF R) _ _ _ _ h3

/-- Evaluation, with the commutative-ring module category as target. -/
private noncomputable abbrev evalC {C : Type} [SmallCategory C] (R₀ : Cᵒᵖ ⥤ CommRingCat.{0})
    (X : Cᵒᵖ) :
    PresheafOfModulesOfCommRing.{0} R₀ ⥤ ModuleCat.{0} (R₀.obj X) :=
  PresheafOfModules.evaluation (R₀ ⋙ forget₂ CommRingCat RingCat) X

/-- Sectionwise tensoring on the right preserves colimits of presheaves of modules. -/
private noncomputable instance tensorRight_preserves {C : Type} [SmallCategory C]
    (R₀ : Cᵒᵖ ⥤ CommRingCat.{0}) {J : Type} [SmallCategory J]
    (N : PresheafOfModulesOfCommRing.{0} R₀) :
    PreservesColimitsOfShape J (tensorRight N) where
  preservesColimit {F} := by
    refine preservesColimit_of_preserves_colimit_cocone
      (PresheafOfModules.isColimitColimitCocone F) ?_
    refine PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X => ?_)
    have h1 : IsColimit ((evalC R₀ X).mapCocone (PresheafOfModules.colimitCocone F)) :=
      isColimitOfPreserves (PresheafOfModules.evaluation (R₀ ⋙ forget₂ CommRingCat RingCat) X)
        (PresheafOfModules.isColimitColimitCocone F)
    have : PreservesColimit (F ⋙ evalC R₀ X)
        (tensorRight (PresheafOfModulesOfCommRing.obj N X)) := inferInstance
    have h2 : IsColimit ((tensorRight (PresheafOfModulesOfCommRing.obj N X)).mapCocone
        ((evalC R₀ X).mapCocone (PresheafOfModules.colimitCocone F))) :=
      isColimitOfPreserves _ h1
    exact h2

/-- Sectionwise `- ⊗ N` as an endofunctor of presheaves of `ringOf R`-modules. -/
private noncomputable def tensR (N : PresheafOfModules.{0} (ringOf R).obj) :
    PresheafOfModules.{0} (ringOf R).obj ⥤ PresheafOfModules.{0} (ringOf R).obj :=
  tensorRight (C := PresheafOfModulesOfCommRing.{0} R.obj) N

/-- `tensR R N` preserves colimits. -/
private noncomputable instance tensR_pres (N : PresheafOfModules.{0} (ringOf R).obj)
    (K : Type) [SmallCategory K] : PreservesColimitsOfShape K (tensR R N) :=
  tensorRight_preserves R.obj N

/-- `a(- ⊗ N)` on presheaves of modules. -/
noncomputable def PsiF (N : PresheafOfModules.{0} (ringOf R).obj) :
    PresheafOfModules.{0} (ringOf R).obj ⥤ Mod (ringOf R) :=
  tensR R N ⋙ sheafifyF R

/-- `a(- ⊗ N)` preserves colimits. -/
private noncomputable instance PsiF_pres (N : PresheafOfModules.{0} (ringOf R).obj) (K : Type)
    [SmallCategory K] : PreservesColimitsOfShape K (PsiF R N) := by
  unfold PsiF
  have h2 : PreservesColimitsOfShape K (sheafifyF R) := inferInstance
  infer_instance

/-- The canonical map from the presheaf coproduct of the underlying presheaves of sheaves
to the underlying presheaf of the coproduct. -/
private noncomputable def piComp {ι : Type} (M : ι → Mod (ringOf R)) :
    ∐ (fun i => (SheafOfModules.forget (ringOf R)).obj (M i)) ⟶
      (SheafOfModules.forget (ringOf R)).obj (∐ M) :=
  sigmaComparison (SheafOfModules.forget (ringOf R)) M

/-- The adjoint transpose of `piComp`. -/
private noncomputable def phiPi {ι : Type} (M : ι → Mod (ringOf R)) :
    (sheafifyF R).obj (∐ (fun i => (SheafOfModules.forget (ringOf R)).obj (M i))) ⟶ ∐ M :=
  (sheafifyF R).map (piComp R M) ≫
    (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit.app (∐ M)

/-- The adjoint transpose of `piComp` is an isomorphism. -/
private lemma isIso_phiPi {ι : Type} (M : ι → Mod (ringOf R)) : IsIso (phiPi R M) := by
  set adj := PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj) with hadj
  have hs : IsIso (sigmaComparison (sheafifyF R)
      (fun i => (SheafOfModules.forget (ringOf R)).obj (M i))) := inferInstance
  have ht : IsIso (Limits.Sigma.map (fun i => adj.counit.app (M i))) :=
    have : ∀ i, IsIso (adj.counit.app (M i)) := fun i => NatIso.isIso_app_of_isIso adj.counit _
    inferInstance
  have key : sigmaComparison (sheafifyF R)
      (fun i => (SheafOfModules.forget (ringOf R)).obj (M i)) ≫ phiPi R M =
      Limits.Sigma.map (fun i => adj.counit.app (M i)) := by
    refine Sigma.hom_ext _ _ (fun i => ?_)
    unfold phiPi
    have e : (sheafifyF R).map (Sigma.ι (fun b => (SheafOfModules.forget (ringOf R)).obj (M b)) i)
        ≫ (sheafifyF R).map (piComp R M) =
        (sheafifyF R).map ((SheafOfModules.forget (ringOf R)).map (Sigma.ι M i)) := by
      rw [← Functor.map_comp]
      unfold piComp
      rw [ι_comp_sigmaComparison]
    rw [ι_comp_sigmaComparison_assoc]
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)
    exact (adj.counit_naturality (Sigma.ι M i)).trans
      (Sigma.ι_map (fun i => adj.counit.app (M i)) i).symm
  have : IsIso (sigmaComparison (sheafifyF R)
      (fun i => (SheafOfModules.forget (ringOf R)).obj (M i)) ≫ phiPi R M) := by
    rw [key]; exact ht
  exact IsIso.of_isIso_comp_left (sigmaComparison (sheafifyF R)
      (fun i => (SheafOfModules.forget (ringOf R)).obj (M i))) _

/-- `piComp` factors through the unit of sheafification. -/
private lemma piComp_eq {ι : Type} (M : ι → Mod (ringOf R)) :
    (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app _ ≫
      (SheafOfModules.forget (ringOf R)).map (phiPi R M) = piComp R M := by
  set adj := PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj) with hadj
  unfold phiPi
  have h1 := adj.right_triangle_components (∐ M)
  have h2 := adj.unit.naturality (piComp R M)
  have h3 : adj.unit.app (∐ fun i => (SheafOfModules.forget (ringOf R)).obj (M i)) ≫
      (SheafOfModules.forget (ringOf R)).map ((sheafifyF R).map (piComp R M)) =
      piComp R M ≫ adj.unit.app ((SheafOfModules.forget (ringOf R)).obj (∐ M)) := h2.symm
  exact (congrArg (adj.unit.app _ ≫ ·) (Functor.map_comp (SheafOfModules.forget (ringOf R))
    ((sheafifyF R).map (piComp R M)) (adj.counit.app (∐ M)))).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h3).trans
    ((Category.assoc _ _ _).trans ((congrArg (piComp R M ≫ ·) h1).trans (Category.comp_id _)))))

/-- Sectionwise tensoring with `N` followed by sheafification inverts `piComp`. -/
private lemma isIso_PsiF_map_piComp {ι : Type} (M : ι → Mod (ringOf R))
    (N : PresheafOfModules.{0} (ringOf R).obj) : IsIso ((PsiF R N).map (piComp R M)) := by
  have := isIso_phiPi R M
  have h1 : IsIso ((PsiF R N).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app
        (∐ fun i => (SheafOfModules.forget (ringOf R)).obj (M i)))) :=
    isIso_sheafifyF_map_whiskerRight R
      (∐ fun i => (SheafOfModules.forget (ringOf R)).obj (M i)) N
  have h2 : IsIso ((PsiF R N).map ((SheafOfModules.forget (ringOf R)).map (phiPi R M))) :=
    Functor.map_isIso _ _
  rw [← piComp_eq R M]
  erw [Functor.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- The comparison `∐ (M i ⊗ A) ⟶ (∐ M) ⊗ A`. -/
noncomputable def cSigma {ι : Type} (M : ι → Mod (ringOf R)) (A : Mod (ringOf R)) :
    ∐ (fun i => ((tensorBifunctor R).obj (M i)).obj A) ⟶ ((tensorBifunctor R).obj (∐ M)).obj A :=
  sigmaComparison (PsiF R ((SheafOfModules.forget (ringOf R)).obj A))
    (fun i => (SheafOfModules.forget (ringOf R)).obj (M i)) ≫
    (PsiF R ((SheafOfModules.forget (ringOf R)).obj A)).map (piComp R M)

/-- The comparison `∐ (M i ⊗ A) ⟶ (∐ M) ⊗ A` is an isomorphism. -/
private instance isIso_cSigma {ι : Type} (M : ι → Mod (ringOf R)) (A : Mod (ringOf R)) :
    IsIso (cSigma R M A) := by
  unfold cSigma
  have h1 := isIso_PsiF_map_piComp R M ((SheafOfModules.forget (ringOf R)).obj A)
  have h2 : IsIso (sigmaComparison (PsiF R ((SheafOfModules.forget (ringOf R)).obj A))
    (fun i => (SheafOfModules.forget (ringOf R)).obj (M i))) := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1

/-- Naturality of `cSigma` in the second variable. -/
lemma cSigma_naturality {ι : Type} (M : ι → Mod (ringOf R)) {A B : Mod (ringOf R)}
    (f : A ⟶ B) :
    Limits.Sigma.map (fun i => ((tensorBifunctor R).obj (M i)).map f) ≫ cSigma R M B =
      cSigma R M A ≫ ((tensorBifunctor R).obj (∐ M)).map f := by
  refine Sigma.hom_ext _ _ (fun i => ?_)
  have hι : ∀ X : Mod (ringOf R), Sigma.ι (fun i => ((tensorBifunctor R).obj (M i)).obj X) i ≫
      cSigma R M X = (sheafifyF R).map (MonoidalCategory.whiskerRight
        (C := PresheafOfModulesOfCommRing.{0} R.obj)
        ((SheafOfModules.forget (ringOf R)).map (Sigma.ι M i))
        ((SheafOfModules.forget (ringOf R)).obj X)) := by
    intro X
    unfold cSigma
    have e : (PsiF R ((SheafOfModules.forget (ringOf R)).obj X)).map (Sigma.ι (fun b =>
        (SheafOfModules.forget (ringOf R)).obj (M b)) i) ≫
        (PsiF R ((SheafOfModules.forget (ringOf R)).obj X)).map (piComp R M) =
        (PsiF R ((SheafOfModules.forget (ringOf R)).obj X)).map
          ((SheafOfModules.forget (ringOf R)).map (Sigma.ι M i)) := by
      rw [← Functor.map_comp]
      unfold piComp
      rw [ι_comp_sigmaComparison]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (ι_comp_sigmaComparison (PsiF R ((SheafOfModules.forget (ringOf R)).obj X))
        (fun b => (SheafOfModules.forget (ringOf R)).obj (M b)) i)).trans e)
  rw [← Category.assoc, Sigma.ι_map, Category.assoc, hι B, ← Category.assoc, hι A]
  have hw := MonoidalCategory.whisker_exchange (C := PresheafOfModulesOfCommRing.{0} R.obj)
    ((SheafOfModules.forget (ringOf R)).map (Sigma.ι M i))
    ((SheafOfModules.forget (ringOf R)).map f)
  show (sheafifyF R).map (MonoidalCategory.whiskerLeft
      (C := PresheafOfModulesOfCommRing.{0} R.obj) ((SheafOfModules.forget (ringOf R)).obj (M i))
      ((SheafOfModules.forget (ringOf R)).map f)) ≫ (sheafifyF R).map
      (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} R.obj)
      ((SheafOfModules.forget (ringOf R)).map (Sigma.ι M i))
      ((SheafOfModules.forget (ringOf R)).obj B)) = (sheafifyF R).map
      (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} R.obj)
      ((SheafOfModules.forget (ringOf R)).map (Sigma.ι M i))
      ((SheafOfModules.forget (ringOf R)).obj A)) ≫ (sheafifyF R).map
      (MonoidalCategory.whiskerLeft
      (C := PresheafOfModulesOfCommRing.{0} R.obj) ((SheafOfModules.forget (ringOf R)).obj (∐ M))
      ((SheafOfModules.forget (ringOf R)).map f))
  exact ((sheafifyF R).map_comp _ _).symm.trans ((congrArg (sheafifyF R).map hw).trans
    ((sheafifyF R).map_comp _ _))

end Site

end Cohesive
