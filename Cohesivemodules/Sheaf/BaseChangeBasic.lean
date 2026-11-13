import Cohesivemodules.Sheaf.FlatResolution
import Cohesivemodules.Sheaf.PerfectDef
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

set_option linter.style.header false

/-!
# S8.a (second half), S8.g: base change of sheaves of modules

Blueprint item S8 (§3): base change along a morphism `φ : R ⟶ S` of sheaves of commutative
rings. Split of blueprint §7's `Flat.lean` (size only).

* `presheafBC φ M`: the presheaf `X ↦ S(X) ⊗_{R(X)} M(X)` of `S`-modules (Mathlib's
  `ModuleCat.extendScalars` sectionwise; restriction maps adjoint to `m ↦ 1 ⊗ M.map f m`).
* `sheafBC φ : Mod R ⥤ Mod S`, the sheafification of `presheafBC φ`; left adjoint to
  restriction of scalars (`sheafBCAdj`); maps `R` to `S` and free modules to free modules, hence
  strictly perfect complexes to strictly perfect complexes.
* `sheafBCRestrictIso`: as an `R`-module, `S ⊗_R M` is the tensor product (S8.a) of `S`
  (restricted to `R`) and `M`.
* S8.g base change maps quasi-isomorphisms between K-flat complexes to quasi-isomorphisms (the
  cone is K-flat and acyclic, so `S ⊗ cone` is acyclic by S8.e).
* Compatibility with restriction to opens (`sheafBCOverIso`), for C5 step 2.

## Deviations
* S8.g is stated for a quasi-isomorphism `K ⟶ K'` between K-flat complexes; the roof form of
  the blueprint follows by resolving the middle term (S8.d).

Part 1 of 2 of the original `Sheaf/BaseChange.lean`, split for size; continued in
`Sheaf/BaseChange.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits
open scoped ChangeOfRings TensorProduct

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R S : Sheaf J CommRingCat.{0}} (φ : R ⟶ S)

/-- Presheaves of modules over the underlying presheaf of rings of `R` (definitionally the
presheaves of modules over `(ringOf R).obj`). -/
abbrev PMod (R : Sheaf J CommRingCat.{0}) :=
  PresheafOfModules.{0} (R.obj ⋙ forget₂ CommRingCat RingCat)

/-- `M(X)` as a module over the commutative ring `R(X)` (the same object, retyped: a `def`, so
that `ModuleCat.extendScalars` sees the commutative ring). -/
def secC (M : PMod R) (X : Cᵒᵖ) : ModuleCat.{0} (R.obj.obj X) :=
  M.obj X

/-- **S8.a.** The sectionwise base change `S(X) ⊗_{R(X)} M(X)` (`ModuleCat.extendScalars`). -/
abbrev bcObj (M : PMod R) (X : Cᵒᵖ) :
    ModuleCat.{0} (S.obj.obj X) :=
  (ModuleCat.extendScalars (φ.hom.app X).hom).obj (secC M X)

set_option backward.isDefEq.respectTransparency false in
/-- `1 ⊗ (a • n) = g a • (1 ⊗ n)` in the extension of scalars along `g`. -/
private lemma tmul_smul_aux {R' S' : Type} [CommRing R'] [CommRing S'] (g : R' →+* S')
    {N : ModuleCat.{0} R'} (a : R') (n : N) :
    ((1 : S') ⊗ₜ[R', g] (a • n : N) : (ModuleCat.extendScalars g).obj N) =
      (g a) • ((1 : S') ⊗ₜ[R', g] n : (ModuleCat.extendScalars g).obj N) := by
  have := ModuleCat.ExtendScalars.smul_tmul (M := N) g (g a) 1 n
  rw [mul_one] at this
  rw [this]
  let := g.toAlgebra
  refine (TensorProduct.smul_tmul (R := R') a (1 : S') (n : N)).symm.trans ?_
  congr 1
  exact Algebra.smul_def a (1 : S') |>.trans (by rw [mul_one]; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- **S8.a.** The restriction maps of the base change: the `S(X)`-linear map
`S(X) ⊗ M(X) → S(Y) ⊗ M(Y)` adjoint to `m ↦ 1 ⊗ M.map f m`. -/
def bcMap (M : PMod R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    bcObj φ M X ⟶ (ModuleCat.restrictScalars (S.obj.map f).hom).obj (bcObj φ M Y) :=
  (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (φ.hom.app X).hom).symm
    (ModuleCat.ofHom (X := secC M X) (Y := (ModuleCat.restrictScalars (φ.hom.app X).hom).obj
        ((ModuleCat.restrictScalars (S.obj.map f).hom).obj (bcObj φ M Y)))
      { toFun := fun m ↦ ((1 : S.obj.obj Y) ⊗ₜ[R.obj.obj Y] (M.map f m : secC M Y) :
          bcObj φ M Y)
        map_add' := by
          intro x y
          exact (congrArg (fun m : secC M Y =>
            ((1 : S.obj.obj Y) ⊗ₜ[R.obj.obj Y] m : bcObj φ M Y))
            (map_add (M.map f).hom x y)).trans (TensorProduct.tmul_add _ _ _)
        map_smul' := by
          intro r x
          have h := PresheafOfModules.map_smul M f r x
          have hn : (S.obj.map f).hom ((φ.hom.app X).hom r) =
              (φ.hom.app Y).hom ((R.obj.map f).hom r) :=
            congrArg (fun g => g.hom r) (φ.hom.naturality f).symm
          have h2 := tmul_smul_aux (φ.hom.app Y).hom ((R.obj.map f).hom r)
            (((M.map f).hom x : secC M Y))
          change ((1 : S.obj.obj Y) ⊗ₜ[R.obj.obj Y, (φ.hom.app Y).hom]
              ((M.map f).hom (r • x) : secC M Y) : bcObj φ M Y) =
            ((S.obj.map f).hom ((φ.hom.app X).hom r)) •
              ((1 : S.obj.obj Y) ⊗ₜ[R.obj.obj Y, (φ.hom.app Y).hom]
                ((M.map f).hom x : secC M Y) : bcObj φ M Y)
          rw [hn, ← h2]
          exact congrArg (fun m : secC M Y =>
            ((1 : S.obj.obj Y) ⊗ₜ[R.obj.obj Y, (φ.hom.app Y).hom] m : bcObj φ M Y)) h })

set_option backward.isDefEq.respectTransparency false in
/-- S8.a: the adjunction hom-equivalence inverse evaluated on `1 ⊗ n`. -/
lemma homEquiv_symm_one_tmul {R' S' : Type} [CommRing R'] [CommRing S'] (g : R' →+* S')
    {N : ModuleCat.{0} R'} {Y : ModuleCat.{0} S'} (k : N ⟶ (ModuleCat.restrictScalars g).obj Y)
    (n : N) :
    ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv g).symm k).hom ((1 : S') ⊗ₜ[R', g] n) =
      k.hom n :=
  congrArg (fun k => k.hom n) (Equiv.apply_symm_apply
    (ModuleCat.ExtendRestrictScalarsAdj.homEquiv g) k)

set_option backward.isDefEq.respectTransparency false in
omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- S8.a: `bcMap` on `1 ⊗ m` is `1 ⊗ M.map f m`. -/
lemma bcMap_one_tmul (M : PMod R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : secC M X) :
    (bcMap φ M f).hom ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m) =
      ((1 : S.obj.obj Y) ⊗ₜ[R.obj.obj Y, (φ.hom.app Y).hom] ((M.map f).hom m : secC M Y) :
        bcObj φ M Y) := by
  exact homEquiv_symm_one_tmul (φ.hom.app X).hom _ m

set_option backward.isDefEq.respectTransparency false in
omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- S8.a: `bcMap` on `s ⊗ m` is `S.map f s ⊗ M.map f m`. -/
lemma bcMap_tmul (M : PMod R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : S.obj.obj X)
    (m : secC M X) :
    (bcMap φ M f).hom ((s ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m : bcObj φ M X)) =
      (((S.obj.map f).hom s) ⊗ₜ[R.obj.obj Y, (φ.hom.app Y).hom]
        ((M.map f).hom m : secC M Y) : bcObj φ M Y) := by
  have e : (s ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m : bcObj φ M X) =
      s • ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m : bcObj φ M X) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [e, (bcMap φ M f).hom.map_smul, bcMap_one_tmul]
  exact (ModuleCat.ExtendScalars.smul_tmul (φ.hom.app Y).hom ((S.obj.map f).hom s) 1
    ((M.map f).hom m : secC M Y)).trans (by rw [mul_one])

set_option backward.isDefEq.respectTransparency false in
omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- **S8.a.** The base change presheaf of `S`-modules `X ↦ S(X) ⊗_{R(X)} M(X)`. -/
def presheafBC (M : PMod R) :
    PMod S where
  obj X := bcObj φ M X
  map f := bcMap φ M f
  map_id X := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    erw [bcMap_one_tmul]
    have h : (M.map (𝟙 X)).hom m = m := by rw [M.map_id]; rfl
    rw [h]
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    erw [bcMap_one_tmul]
    have h : (M.map (f ≫ g)).hom m = (M.map g).hom ((M.map f).hom m) := by
      rw [M.map_comp]; rfl
    rw [h]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [bcMap_one_tmul φ M f m]
    erw [bcMap_one_tmul φ M g]

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- **S8.a.** Base change of a morphism, sectionwise `1 ⊗ g`. -/
def presheafBCMap {M M' : PMod R} (g : M ⟶ M') :
    presheafBC φ M ⟶ presheafBC φ M' where
  app X := (ModuleCat.extendScalars (φ.hom.app X).hom).map (g.app X)
  naturality {X Y} f := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g f m
    refine Eq.trans (b := ((1 : S.obj.obj Y) ⊗ₜ[R.obj.obj Y, (φ.hom.app Y).hom]
      ((g.app Y).hom ((M.map f).hom m) : secC M' Y) : bcObj φ M' Y)) ?_
      (Eq.trans (congrArg (fun m' : secC M' Y => ((1 : S.obj.obj Y) ⊗ₜ[R.obj.obj Y,
        (φ.hom.app Y).hom] m' : bcObj φ M' Y)) h) ?_)
    · exact congrArg (fun z => ((ModuleCat.extendScalars (φ.hom.app Y).hom).map (g.app Y)).hom z)
        (bcMap_one_tmul φ M f m)
    · exact (bcMap_one_tmul φ M' f ((g.app X).hom m)).symm

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- **S8.a.** Base change of presheaves of modules, as a functor. -/
def presheafBCFunctor :
    PMod R ⥤ PMod S where
  obj := presheafBC φ
  map := presheafBCMap φ
  map_id M := by
    ext X : 1
    exact (ModuleCat.extendScalars (φ.hom.app X).hom).map_id (secC M X)
  map_comp g g' := by
    ext X : 1
    exact (ModuleCat.extendScalars (φ.hom.app X).hom).map_comp (g.app X) (g'.app X)

/-- The morphism of sheaves of rings underlying `φ`. -/
abbrev ringHomOf : ringOf R ⟶ ringOf S :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map φ

/-- **S8.a. Base change** `S ⊗_R -` of sheaves of modules along `φ : R ⟶ S`: sheafification of
the sectionwise base change. -/
def sheafBC : Mod (ringOf R) ⥤ Mod (ringOf S) :=
  SheafOfModules.forget _ ⋙ presheafBCFunctor φ ⋙ sheafifyF S

set_option backward.isDefEq.respectTransparency false in
/-- Presheaf-level adjunction, forward direction: `S ⊗ M ⟶ N` gives `M ⟶ N|_R`, sectionwise
`m ↦ f (1 ⊗ m)`. -/
private def adjToFun {M : PMod R} {N : PMod S} (f : presheafBC φ M ⟶ N) :
    M ⟶ (PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj N where
  app X := ModuleCat.ExtendRestrictScalarsAdj.homEquiv (φ.hom.app X).hom
    (X := secC M X) (Y := secC N X) (f.app X)
  naturality {X Y} g := by
    ext m
    exact (congrArg (fun z => (f.app Y).hom z) (bcMap_one_tmul φ M g m).symm).trans
      (PresheafOfModules.naturality_apply f g ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X,
        (φ.hom.app X).hom] m : bcObj φ M X))

set_option backward.isDefEq.respectTransparency false in
/-- Presheaf-level adjunction, backward direction: `M ⟶ N|_R` gives `S ⊗ M ⟶ N`, sectionwise
`s ⊗ m ↦ s • g m`. -/
private def adjInvFun {M : PMod R} {N : PMod S}
    (g : M ⟶ (PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj N) :
    presheafBC φ M ⟶ N where
  app X := (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (φ.hom.app X).hom
    (X := secC M X) (Y := secC N X)).symm (g.app X)
  naturality {X Y} h := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    refine (congrArg (fun z => ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv
      (φ.hom.app Y).hom (X := secC M Y) (Y := secC N Y)).symm (g.app Y)).hom z)
      (bcMap_one_tmul φ M h m)).trans
      ((homEquiv_symm_one_tmul (φ.hom.app Y).hom (g.app Y) _).trans
      ((PresheafOfModules.naturality_apply g h m).trans ?_))
    exact congrArg (fun z => (N.map h).hom z) (homEquiv_symm_one_tmul (φ.hom.app X).hom (g.app X)
      m).symm

set_option backward.isDefEq.respectTransparency false in
/-- Presheaf-level adjunction `S ⊗_R - ⊣` restriction of scalars. -/
private def presheafBCAdj :
    presheafBCFunctor φ ⊣ PresheafOfModules.restrictScalars (ringHomOf φ).hom :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N =>
        { toFun := adjToFun φ
          invFun := adjInvFun φ
          left_inv := fun f => by
            ext X : 1
            exact Equiv.symm_apply_apply
              (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (φ.hom.app X).hom) (f.app X)
          right_inv := fun g => by
            ext X : 1
            exact Equiv.apply_symm_apply
              (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (φ.hom.app X).hom) (g.app X) }
      homEquiv_naturality_left_symm := fun {M' M N} f g => by
        show adjInvFun φ (f ≫ g) = (presheafBCFunctor φ).map f ≫ adjInvFun φ g
        ext X : 1
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        refine (homEquiv_symm_one_tmul (φ.hom.app X).hom ((f ≫ g).app X) m).trans ?_
        exact (homEquiv_symm_one_tmul (φ.hom.app X).hom (g.app X) ((f.app X).hom m)).symm
      homEquiv_naturality_right := fun {M N N'} f g => by
        show adjToFun φ (f ≫ g) = adjToFun φ f ≫ _
        ext X : 1
        ext m
        rfl }

/-- **S8.a.** Base change is left adjoint to restriction of scalars. -/
def sheafBCAdj : sheafBC φ ⊣ SheafOfModules.restrictScalars.{0} (ringHomOf φ) :=
  ((presheafBCAdj φ).comp (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf S).obj))).restrictFullyFaithful (iC := SheafOfModules.forget _) (iD := 𝟭 _)
    (SheafOfModules.fullyFaithfulForget _) (Functor.FullyFaithful.id _) (Iso.refl _)
    (NatIso.ofComponents (fun N => Iso.refl _) (fun f => by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl))

instance : (sheafBC φ).Additive := by
  have : (sheafBC φ).IsLeftAdjoint := (sheafBCAdj φ).isLeftAdjoint
  have : (sheafBC φ).PreservesZeroMorphisms := inferInstance
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (sheafBC φ)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Morphisms out of `S` correspond to morphisms out of `S ⊗_R R`: both are sections (Yoneda for
`unit`, adjunction `sheafBCAdj`). -/
private def unitEquiv (Z : Mod (ringOf S)) :
    (SheafOfModules.unit (ringOf S) ⟶ Z) ≃
      ((sheafBC φ).obj (SheafOfModules.unit (ringOf R)) ⟶ Z) :=
  (SheafOfModules.unitHomEquiv Z).trans
    ((Equiv.refl Z.sections : Z.sections ≃
        ((SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj Z).sections).trans
      ((SheafOfModules.unitHomEquiv ((SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj Z)
        ).symm.trans ((sheafBCAdj φ).homEquiv _ _).symm))

/-- **S8.a.** Base change maps `R` to `S`. -/
def sheafBCUnitIso :
    (sheafBC φ).obj (SheafOfModules.unit (ringOf R)) ≅ SheafOfModules.unit (ringOf S) :=
  Coyoneda.ext _ _ (fun {Z} f => (unitEquiv φ Z).symm f) (fun {Z} f => unitEquiv φ Z f)
    (fun {Z} f => (unitEquiv φ Z).apply_symm_apply f)
    (fun {Z} f => (unitEquiv φ Z).symm_apply_apply f)
    (fun {Z Z'} f g => by
      simp only [unitEquiv, Equiv.trans_apply]
      rw [SheafOfModules.unitHomEquiv_comp_apply]
      have h := SheafOfModules.unitHomEquiv_symm_comp
        (M := (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj Z)
        (N := (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj Z')
        (Z.unitHomEquiv f) ((SheafOfModules.restrictScalars.{0} (ringHomOf φ)).map g)
      exact (congrArg ((sheafBCAdj φ).homEquiv _ Z').symm h.symm).trans
        (Adjunction.homEquiv_naturality_right_symm _ _ _))

/-- **S8.a.** Base change maps free modules to free modules. -/
def sheafBCFreeIso (I : Type) :
    (sheafBC φ).obj (SheafOfModules.free (R := ringOf R) I) ≅
      SheafOfModules.free (R := ringOf S) I :=
  haveI : (sheafBC φ).IsLeftAdjoint := (sheafBCAdj φ).isLeftAdjoint
  (SheafOfModules.mapFreeIso (sheafBC φ) I (sheafBCUnitIso φ).symm).symm

/-- **S8.a.** Base change preserves direct summands of finite free modules. -/
theorem IsFinFreeSummand.sheafBC {M : Mod (ringOf R)} (hM : IsFinFreeSummand M) :
    IsFinFreeSummand ((sheafBC φ).obj M) := by
  obtain ⟨m, i, p, hip⟩ := hM
  refine ⟨m, (Cohesive.sheafBC φ).map i ≫ (sheafBCFreeIso φ (Fin m)).hom,
    (sheafBCFreeIso φ (Fin m)).inv ≫ (Cohesive.sheafBC φ).map p, ?_⟩
  rw [Category.assoc, ← Category.assoc (sheafBCFreeIso φ (Fin m)).hom,
    Iso.hom_inv_id, Category.id_comp, ← CategoryTheory.Functor.map_comp, hip,
    CategoryTheory.Functor.map_id]

/-- **S8.a.** Base change preserves strictly perfect complexes. -/
theorem IsStrictlyPerfect.sheafBC {P : CochainComplex (Mod (ringOf R)) ℤ}
    (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect (((sheafBC φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  obtain ⟨⟨a, b, hGE, hLE⟩, hP'⟩ := hP
  refine ⟨⟨a, b, ?_, ?_⟩, fun n => IsFinFreeSummand.sheafBC φ (hP' n)⟩
  · refine (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi => ?_
    exact Functor.map_isZero (Cohesive.sheafBC φ) (P.isZero_of_isStrictlyGE a i hi)
  · refine (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi => ?_
    exact Functor.map_isZero (Cohesive.sheafBC φ) (P.isZero_of_isStrictlyLE b i hi)

end Cohesive
end
