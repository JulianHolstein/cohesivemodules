import Cohesivemodules.Sheaf.BaseChangeBasic

set_option linter.style.header false

/-!
# S8.a (second half), S8.g: base change of sheaves of modules (part 2 of 2)

Split from `Sheaf/BaseChange.lean` for size;
continues `Sheaf/BaseChangeBasic.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite Limits
open scoped ChangeOfRings TensorProduct
variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R S : Sheaf J CommRingCat.{0}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- S8.a: comparison `a_R (P|_R) ⟶ (a_S P)|_R` between restriction of scalars and
sheafification (adjoint to `P|_R ⟶ (a_S P)|_R`, the restriction of the unit). -/
def rsSheafifyComp (P : PMod S) :
    (sheafifyF R).obj ((PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj P) ⟶
      (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj ((sheafifyF S).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf R).obj)).symm
    ((PresheafOfModules.restrictScalars (ringHomOf φ).hom).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app P))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison `rsSheafifyComp` is an isomorphism: on underlying sheaves of abelian groups
it is the identity of the sheafification of `P.presheaf`. -/
instance isIso_rsSheafifyComp (P : PMod S) : IsIso (rsSheafifyComp φ P) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (ringOf R))]
  have h := PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm
    (𝟙 (ringOf R).obj)
    (P := (PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj P)
    (F := (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj ((sheafifyF S).obj P))
    ((PresheafOfModules.restrictScalars (ringHomOf φ).hom).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app P))
  have key : (SheafOfModules.toSheaf (ringOf R)).map (rsSheafifyComp φ P) =
      ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{0}).homEquiv
          ((PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj P).presheaf
          ((SheafOfModules.toSheaf (ringOf R)).obj
            ((SheafOfModules.restrictScalars (ringHomOf φ)).obj ((sheafifyF S).obj P)))).symm
      ((PresheafOfModules.toPresheaf (ringOf R).obj).map
        ((PresheafOfModules.restrictScalars (ringHomOf φ).hom).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringOf S).obj)).unit.app P))) := h
  rw [key]
  have h4 : ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{0}).homEquiv P.presheaf
      ((presheafToSheaf J AddCommGrpCat.{0}).obj P.presheaf)).symm
      ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{0}).unit.app P.presheaf) =
      𝟙 _ := by
    rw [Adjunction.homEquiv_counit]
    exact (CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{0}).left_triangle_components _
  exact h4.symm ▸ (inferInstance : IsIso (𝟙 ((presheafToSheaf J AddCommGrpCat.{0}).obj
    P.presheaf)))

set_option backward.isDefEq.respectTransparency false in
/-- S8.a: sectionwise, `(S ⊗_R M)|_R` and `S|_R ⊗_R M` have the same underlying type
`S(X) ⊗_{R(X)} M(X)`; this is the identity, compatible with the restriction maps. -/
def bcTensorIso (M : PMod R) :
    (PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj (presheafBC φ M) ≅
      MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj)
        ((PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj
          (PresheafOfModules.unit (ringOf S).obj)) M :=
  PresheafOfModules.isoMk (fun X => Iso.refl _) (fun X Y f => by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul s m => exact bcMap_tmul φ M f s m
    | add z z' hz hz' =>
      exact (map_add _ z z').trans ((congrArg₂ _ hz hz').trans (map_add _ z z').symm))

set_option backward.isDefEq.respectTransparency false in
/-- S8.a: naturality of `bcTensorIso` in `M`. -/
lemma bcTensorIso_naturality {M M' : PMod R} (g : M ⟶ M') :
    (PresheafOfModules.restrictScalars (ringHomOf φ).hom).map (presheafBCMap φ g) ≫
        (bcTensorIso φ M').hom =
      (bcTensorIso φ M).hom ≫ MonoidalCategory.whiskerLeft
        (C := PresheafOfModulesOfCommRing.{0} R.obj)
        ((PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj
          (PresheafOfModules.unit (ringOf S).obj)) g := by
  ext X : 1
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul s m => rfl
  | add z z' hz hz' =>
    exact (map_add _ z z').trans ((congrArg₂ _ hz hz').trans (map_add _ z z').symm)

/-- **S8.a.** As an `R`-module, the base change `S ⊗_R M` is the tensor product of `S`
(restricted to `R`) with `M`: both are sheafifications of `X ↦ S(X) ⊗_{R(X)} M(X)`. -/
def sheafBCRestrictIso (M : Mod (ringOf R)) :
    (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj ((sheafBC φ).obj M) ≅
      ((tensorBifunctor R).obj ((SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj
        (SheafOfModules.unit (ringOf S)))).obj M :=
  (asIso (rsSheafifyComp φ ((presheafBCFunctor φ).obj ((SheafOfModules.forget _).obj M)))).symm
    ≪≫ (sheafifyF R).mapIso (bcTensorIso φ ((SheafOfModules.forget _).obj M))

/-- An additive faithful functor reflects acyclicity of cochain complexes. -/
private lemma acyclic_of_map_acyclic {A B : Type*} [Category A] [Category B] [Abelian A]
    [Abelian B] (F : A ⥤ B) [F.Additive] [F.Faithful] (K : CochainComplex A ℤ)
    (h : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic) : K.Acyclic := by
  intro i
  rw [K.exactAt_iff' (i - 1) i (i + 1) (by simp) (by simp)]
  have := (HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)).1 (h i)
  exact F.reflects_exact_of_faithful _ this

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `rsSheafifyComp` in `P`. -/
private lemma rsSheafifyComp_naturality {P P' : PMod S} (h : P ⟶ P') :
    (sheafifyF R).map ((PresheafOfModules.restrictScalars (ringHomOf φ).hom).map h) ≫
        rsSheafifyComp φ P' =
      rsSheafifyComp φ P ≫
        (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).map ((sheafifyF S).map h) := by
  apply ((PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf R).obj)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [PresheafOfModules.sheafificationAdjunction_homEquiv_apply]
  have e1 : ∀ Q : PMod S, (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf R).obj))
      (rsSheafifyComp φ Q) =
      (PresheafOfModules.restrictScalars (ringHomOf φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app Q) :=
    fun Q => Equiv.apply_symm_apply _ _
  rw [e1, e1, ← Functor.map_comp]
  exact (congrArg (PresheafOfModules.restrictScalars (ringHomOf φ).hom).map
    ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.naturality
      h)).trans
    (Functor.map_comp _ _ _)

/-- Acyclicity of cochain complexes is invariant under isomorphism. -/
private lemma acyclic_of_iso {A : Type*} [Category A] [Abelian A] {K L : CochainComplex A ℤ}
    (e : K ≅ L) (h : K.Acyclic) : L.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (h i)).of_iso
    ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) i).mapIso e).symm

set_option backward.isDefEq.respectTransparency false in
/-- `sheafBCRestrictIso` is natural in `M`. -/
private def rsBCIso : sheafBC φ ⋙ SheafOfModules.restrictScalars.{0} (ringHomOf φ) ≅
    (tensorBifunctor R).obj ((SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj
      (SheafOfModules.unit (ringOf S))) :=
  NatIso.ofComponents (fun M => sheafBCRestrictIso φ M) (fun {M M'} g => by
    have hn := rsSheafifyComp_naturality φ (R := R) (S := S)
      (presheafBCMap φ ((SheafOfModules.forget _).map g))
    simp only [sheafBCRestrictIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, Functor.mapIso_hom,
      Functor.comp_map]
    have key : ∀ {a b c d : Mod (ringOf R)} (Ψ : a ⟶ b) (Ψ' : c ⟶ d) [IsIso Ψ] [IsIso Ψ']
        (u : a ⟶ c) (v : b ⟶ d), u ≫ Ψ' = Ψ ≫ v → v ≫ inv Ψ' = inv Ψ ≫ u := by
      intro a b c d Ψ Ψ' _ _ u v hn
      rw [IsIso.comp_inv_eq, Category.assoc, hn, IsIso.inv_hom_id_assoc]
    erw [← Category.assoc, key _ _ _ _ hn, Category.assoc, Category.assoc, ← Functor.map_comp]
    congr 1
    erw [← Functor.map_comp]
    exact congrArg (sheafifyF R).map (bcTensorIso_naturality φ _))

/-- Base change of a K-flat acyclic complex is acyclic: restriction of scalars reflects
acyclicity, `rs (S ⊗_R L) ≅ S[0] ⊗ L ≅ L ⊗ S[0]`, acyclic by S8.e. -/
private lemma acyclic_sheafBC_of_isKFlat {L : CochainComplex (Mod (ringOf R)) ℤ}
    (hL : IsKFlat R L) (hLa : L.Acyclic) :
    (((sheafBC φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic := by
  have hfaith : (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).Faithful :=
    haveI : (SheafOfModules.restrictScalars.{0} (ringHomOf φ) ⋙
        SheafOfModules.forget (ringOf R)).Faithful :=
      inferInstanceAs ((SheafOfModules.forget (ringOf S) ⋙
        PresheafOfModules.restrictScalars (ringHomOf φ).hom).Faithful)
    Functor.Faithful.of_comp (SheafOfModules.restrictScalars.{0} (ringHomOf φ))
      (SheafOfModules.forget (ringOf R))
  refine acyclic_of_map_acyclic (SheafOfModules.restrictScalars.{0} (ringHomOf φ)) _ ?_
  set A := (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj (SheafOfModules.unit (ringOf S))
  have h1 : (tensorC R L ((HomologicalComplex.single (Mod (ringOf R)) (ComplexShape.up ℤ)
      0).obj A)).Acyclic := acyclic_tensorC_of_isKFlat R hL hLa _ 0
  have e : (tensorC R L ((HomologicalComplex.single (Mod (ringOf R)) (ComplexShape.up ℤ)
      0).obj A)) ≅ ((SheafOfModules.restrictScalars.{0} (ringHomOf φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((sheafBC φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    tensorCSymIso R L _ ≪≫ tensorCSingleIso R A L ≪≫
      ((NatIso.mapHomologicalComplex (rsBCIso φ).symm (ComplexShape.up ℤ)).app L)
  exact acyclic_of_iso e h1

/-- **S8.g.** Base change maps a quasi-isomorphism between K-flat complexes to a
quasi-isomorphism: the mapping cone is K-flat and acyclic, so `S ⊗ cone` is acyclic (S8.e with
`L = S`, `sheafBCRestrictIso`), and restriction of scalars reflects acyclicity. -/
theorem quasiIso_sheafBC_of_isKFlat {K K' : CochainComplex (Mod (ringOf R)) ℤ}
    (hK : IsKFlat R K) (hK' : IsKFlat R K') (f : K ⟶ K') [QuasiIso f] :
    QuasiIso (((sheafBC φ).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  rw [quasiIso_iff_acyclic_mappingCone]
  have hf : (CochainComplex.mappingCone f).Acyclic :=
    (quasiIso_iff_acyclic_mappingCone f).1 inferInstance
  exact acyclic_of_iso
    (HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f (sheafBC φ))
    (acyclic_sheafBC_of_isKFlat φ (IsKFlat.mappingCone R hK hK' f) hf)

/-- The restriction of `φ` to the over-site `Over X`. -/
abbrev overHom (X : C) : R.over X ⟶ S.over X :=
  (J.overPullback CommRingCat X).map φ

set_option backward.isDefEq.respectTransparency false in
/-- Base change of presheaves commutes with restriction along `Over.forget X` (sectionwise the
same object). -/
private def overBCPre (X : C) (M : Mod (ringOf R)) :
    presheafBC (overHom φ X) ((SheafOfModules.overFunctor.{0} (ringOf R) X).obj M).val ≅
      (PresheafOfModules.pushforward.{0} (F := Over.forget X) (R := (ringOf S).obj)
      (S := ((ringOf S).over X).obj) (𝟙 _)).obj (presheafBC φ M.val) :=
  PresheafOfModules.isoMk (fun Y => Iso.refl _) (fun Y Z f => by
    ext z
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      refine Eq.trans ?_ (bcMap_tmul φ M.val (Over.forget X |>.op.map f) s m).symm
      exact bcMap_tmul (overHom φ X) ((SheafOfModules.overFunctor.{0} (ringOf R) X).obj M).val
        f s m
    | add z z' hz hz' =>
      exact (map_add _ z z').trans ((congrArg₂ _ hz hz').trans (map_add _ z z').symm))

set_option backward.isDefEq.respectTransparency false in
/-- Comparison `S|X ⊗_{R|X} M|X ⟶ (S ⊗_R M)|X`, adjoint to the restriction of the unit
`S ⊗_R M ⟶ a(S ⊗_R M)` of sheafification. -/
private def overBCComp (X : C) (M : Mod (ringOf R)) :
    (sheafBC (overHom φ X)).obj ((SheafOfModules.overFunctor.{0} (ringOf R) X).obj M) ⟶
      (SheafOfModules.overFunctor.{0} (ringOf S) X).obj ((sheafBC φ).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (S.over X)).obj)).symm
    ((overBCPre φ X M).hom ≫ (PresheafOfModules.pushforward.{0} (F := Over.forget X)
      (R := (ringOf S).obj) (S := ((ringOf S).over X).obj) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
        ((presheafBCFunctor φ).obj M.val)))

-- raised: unifying sheaf-level morphism types (pushforward vs sheafification) is expensive
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison `overBCComp` is an isomorphism: on underlying sheaves of abelian groups it is
Mathlib's compatibility of pushforward along `Over.forget X` with sheafification. -/
private instance isIso_overBCComp (X : C) (M : Mod (ringOf R)) : IsIso (overBCComp φ X M) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (ringOf (S.over X)))]
  have h := PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm
    (𝟙 (ringOf (S.over X)).obj)
    (P := (presheafBC (overHom φ X) ((SheafOfModules.overFunctor.{0} (ringOf R) X).obj M).val))
    (F := (SheafOfModules.overFunctor.{0} (ringOf S) X).obj ((sheafBC φ).obj M))
    ((overBCPre φ X M).hom ≫ (PresheafOfModules.pushforward.{0} (F := Over.forget X)
      (R := (ringOf S).obj) (S := ((ringOf S).over X).obj) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
        ((presheafBCFunctor φ).obj M.val)))
  have key : (SheafOfModules.toSheaf (ringOf (S.over X))).map (overBCComp φ X M) =
      ((Over.forget X).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{0}
        (J.over X) J).hom.app (PresheafOfModules.presheaf (presheafBC φ M.val)) := by
    refine Sheaf.hom_ext ?_
    rw [Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom]
    exact congrArg (fun k => k.hom) h
  rw [key]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of `overBCPre` in `M`. -/
private lemma overBCPre_naturality (X : C) {M M' : Mod (ringOf R)} (g : M ⟶ M') :
    (overBCPre φ X M).hom ≫ (PresheafOfModules.pushforward.{0} (F := Over.forget X)
      (R := (ringOf S).obj) (S := ((ringOf S).over X).obj) (𝟙 _)).map
        (presheafBCMap φ g.val) =
      presheafBCMap (overHom φ X) ((SheafOfModules.overFunctor.{0} (ringOf R) X).map g).val ≫
        (overBCPre φ X M').hom := by
  ext Y : 1
  refine ModuleCat.ExtendScalars.hom_ext (fun m => ?_)
  rfl

/-- A commuting square of two isomorphisms gives the commuting square of their inverses. -/
private lemma iso_square_aux {A : Type*} [Category A] {a b a' b' : A} (c : a ⟶ b) (c' : a' ⟶ b')
    (u : a ⟶ a') (v : b ⟶ b') (h : c ≫ v = u ≫ c') (hc : IsIso c) (hc' : IsIso c') :
    v ≫ inv c' = inv c ≫ u := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Postcomposing a commuting square with a morphism. -/
private lemma comp_square_aux {A : Type*} [Category A] {a b c d e : A} (p : a ⟶ b)
    (pf : b ⟶ c) (k : a ⟶ d) (p' : d ⟶ c) (h2 : p ≫ pf = k ≫ p') (q : c ⟶ e) :
    k ≫ (p' ≫ q) = p ≫ (pf ≫ q) := by
  rw [← Category.assoc, ← h2, Category.assoc]

/-- A commuting square on the right-adjoint side gives one on the left-adjoint side. -/
private lemma adj_symm_square {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {G : B ⥤ A}
    (adj : L ⊣ G) {P P' : A} {F F' : B} (a : P ⟶ G.obj F) (a' : P' ⟶ G.obj F') (k : P ⟶ P')
    (h : F ⟶ F') (w : a ≫ G.map h = k ≫ a') :
    (adj.homEquiv P F).symm a ≫ h = L.map k ≫ (adj.homEquiv P' F').symm a' := by
  rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_left_symm, w]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the comparison `overBCComp` in `M`. -/
private lemma overBCComp_naturality (X : C) {M M' : Mod (ringOf R)} (g : M ⟶ M') :
    overBCComp φ X M ≫ (SheafOfModules.overFunctor.{0} (ringOf S) X).map ((sheafBC φ).map g) =
      (sheafBC (overHom φ X)).map ((SheafOfModules.overFunctor.{0} (ringOf R) X).map g) ≫
        overBCComp φ X M' := by
  unfold overBCComp
  have e1 : (sheafBC (overHom φ X)).map ((SheafOfModules.overFunctor.{0} (ringOf R) X).map g) =
      (PresheafOfModules.sheafification.{0} (𝟙 (ringOf (S.over X)).obj)).map
        (presheafBCMap (overHom φ X) ((SheafOfModules.overFunctor.{0} (ringOf R) X).map g).val) :=
    rfl
  have e2 : ∀ {P : PresheafOfModules.{0} (ringOf (S.over X)).obj}
      {F : SheafOfModules.{0} (ringOf (S.over X))}
      (a : P ⟶ (PresheafOfModules.restrictScalars.{0} (𝟙 (ringOf (S.over X)).obj)).obj
        ((SheafOfModules.forget _).obj F)),
      (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (S.over X)).obj)).symm a =
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf (S.over X)).obj)).homEquiv
        P F).symm a := fun {P F} a => by
    apply ((PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf (S.over X)).obj)).homEquiv P F).injective
    rw [Equiv.apply_symm_apply, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
      Equiv.apply_symm_apply]
  rw [e1, e2, e2]
  exact adj_symm_square (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (S.over X)).obj))
    (P := presheafBC (overHom φ X) ((SheafOfModules.overFunctor.{0} (ringOf R) X).obj M).val)
    (P' := presheafBC (overHom φ X) ((SheafOfModules.overFunctor.{0} (ringOf R) X).obj M').val)
    (F := (SheafOfModules.overFunctor.{0} (ringOf S) X).obj ((sheafBC φ).obj M))
    (F' := (SheafOfModules.overFunctor.{0} (ringOf S) X).obj ((sheafBC φ).obj M'))
    ((overBCPre φ X M).hom ≫ (PresheafOfModules.pushforward.{0} (F := Over.forget X)
      (R := (ringOf S).obj) (S := ((ringOf S).over X).obj) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
        ((presheafBCFunctor φ).obj M.val)))
    ((overBCPre φ X M').hom ≫ (PresheafOfModules.pushforward.{0} (F := Over.forget X)
      (R := (ringOf S).obj) (S := ((ringOf S).over X).obj) (𝟙 _)).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
        ((presheafBCFunctor φ).obj M'.val)))
    (presheafBCMap (overHom φ X) ((SheafOfModules.overFunctor.{0} (ringOf R) X).map g).val)
    ((SheafOfModules.overFunctor.{0} (ringOf S) X).map ((sheafBC φ).map g)) (by
    have hu := (PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf S).obj)).unit.naturality (presheafBCMap φ g.val)
    have h1 := congrArg (PresheafOfModules.pushforward.{0} (F := Over.forget X)
      (R := (ringOf S).obj) (S := ((ringOf S).over X).obj) (𝟙 _)).map hu
    rw [Functor.map_comp, Functor.map_comp] at h1
    rw [Functor.id_map] at h1
    exact (congrArg (_ ≫ ·) h1.symm).trans
      (comp_square_aux _ _ _ _ (overBCPre_naturality φ X g) _).symm)

/-- **S8.a.** Base change commutes with restriction: `(S ⊗_R M)|X ≅ S|X ⊗_{R|X} M|X`. -/
def sheafBCOverIso (X : C) (M : Mod (ringOf R)) :
    (SheafOfModules.overFunctor.{0} (ringOf S) X).obj ((sheafBC φ).obj M) ≅
      (sheafBC (overHom φ X)).obj ((SheafOfModules.overFunctor.{0} (ringOf R) X).obj M) :=
  (asIso (overBCComp φ X M)).symm

/-- **S8.a.** Naturality of `sheafBCOverIso` in `M`: for `g : M ⟶ M'`, restricting `S ⊗ g` and
then identifying with `S|X ⊗ M'|X` equals identifying first and then applying `S|X ⊗ g|X`.
(Used in C5 step 2 to restrict base-changed complexes.) -/
theorem sheafBCOverIso_hom_naturality (X : C) {M M' : Mod (ringOf R)} (g : M ⟶ M') :
    (SheafOfModules.overFunctor.{0} (ringOf S) X).map ((sheafBC φ).map g) ≫
        (sheafBCOverIso φ X M').hom =
      (sheafBCOverIso φ X M).hom ≫
        (sheafBC (overHom φ X)).map ((SheafOfModules.overFunctor.{0} (ringOf R) X).map g) := by
  exact iso_square_aux (overBCComp φ X M) (overBCComp φ X M') _ _
    (overBCComp_naturality φ X g) (isIso_overBCComp φ X M) (isIso_overBCComp φ X M')

end Cohesive
