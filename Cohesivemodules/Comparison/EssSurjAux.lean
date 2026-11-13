import Cohesivemodules.Sheaf.TensorSections
import Cohesivemodules.Sheaf.Flat
import Cohesivemodules.Sheaf.FlatResolution
import Cohesivemodules.Sheaf.BaseChange
import Cohesivemodules.Sheaf.PerfectDef

set_option linter.style.header false

/-!
# C5 auxiliary: the unit tensor functor

`unit ⊗ - ≅ 𝟭` on sheaves of modules, from `isIso_tensorUnit` (the unit is a summand of a
finite free module) and the left unitor of presheaves of modules.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  (R : Sheaf J CommRingCat.{0})

/-- The unit module is a direct summand of a finite free module. -/
theorem isFinFreeSummand_unit : IsFinFreeSummand (SheafOfModules.unit (ringOf R)) :=
  ⟨1, Sigma.ι (fun _ : Fin 1 => SheafOfModules.unit (ringOf R)) 0,
    Sigma.desc (fun _ => 𝟙 _), Sigma.ι_comp_desc _ _⟩

/-- Presheaf-level iso `unit ⊗ N ≅ N`. -/
def unitTensorPre (N : Mod (ringOf R)) :
    (SheafOfModules.forget (ringOf R)).obj (((tensorBifunctor R).obj
      (SheafOfModules.unit (ringOf R))).obj N) ≅ (SheafOfModules.forget (ringOf R)).obj N :=
  haveI := isIso_tensorUnit R (isFinFreeSummand_unit R) N
  (asIso (tensorUnit R (SheafOfModules.unit (ringOf R)) N)).symm ≪≫
    @leftUnitor (PresheafOfModulesOfCommRing.{0} R.obj) _ _ N.val

/-- The left unitor `unit ⊗ N ⟶ N` of presheaves of modules. -/
def leftU' (N : Mod (ringOf R)) :
    preTensor R (SheafOfModules.unit (ringOf R)) N ⟶ (SheafOfModules.forget (ringOf R)).obj N :=
  (@leftUnitor (PresheafOfModulesOfCommRing.{0} R.obj) _ _ N.val).hom

/-- `unit ◁ f` on presheaves of modules. -/
def whiskL {N N' : Mod (ringOf R)} (f : N ⟶ N') :
    preTensor R (SheafOfModules.unit (ringOf R)) N ⟶
      preTensor R (SheafOfModules.unit (ringOf R)) N' :=
  MonoidalCategory.whiskerLeft (C := PresheafOfModulesOfCommRing.{0} R.obj)
    (SheafOfModules.unit (ringOf R)).val f.val

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- Naturality of the left unitor. -/
lemma leftU'_naturality {N N' : Mod (ringOf R)} (f : N ⟶ N') :
    whiskL R f ≫ leftU' R N' = leftU' R N ≫ (SheafOfModules.forget (ringOf R)).map f :=
  leftUnitor_naturality (C := PresheafOfModulesOfCommRing.{0} R.obj) f.val

/-- Naturality of `unitTensorPre` in `N` (presheaf level). -/
lemma unitTensorPre_naturality {N N' : Mod (ringOf R)} (f : N ⟶ N') :
    (SheafOfModules.forget (ringOf R)).map (((tensorBifunctor R).obj
      (SheafOfModules.unit (ringOf R))).map f) ≫ (unitTensorPre R N').hom =
      (unitTensorPre R N).hom ≫ (SheafOfModules.forget (ringOf R)).map f := by
  have := isIso_tensorUnit R (isFinFreeSummand_unit R) N
  have := isIso_tensorUnit R (isFinFreeSummand_unit R) N'
  have hn : tensorUnit R (SheafOfModules.unit (ringOf R)) N ≫
      (SheafOfModules.forget (ringOf R)).map (((tensorBifunctor R).obj
        (SheafOfModules.unit (ringOf R))).map f) =
      whiskL R f ≫ tensorUnit R (SheafOfModules.unit (ringOf R)) N' :=
    ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.naturality
      (whiskL R f)).symm
  have e1 : (unitTensorPre R N).hom =
      inv (tensorUnit R (SheafOfModules.unit (ringOf R)) N) ≫ leftU' R N := rfl
  have e2 : (unitTensorPre R N').hom =
      inv (tensorUnit R (SheafOfModules.unit (ringOf R)) N') ≫ leftU' R N' := rfl
  have h2 : (SheafOfModules.forget (ringOf R)).map (((tensorBifunctor R).obj
        (SheafOfModules.unit (ringOf R))).map f) ≫
      inv (tensorUnit R (SheafOfModules.unit (ringOf R)) N') =
      inv (tensorUnit R (SheafOfModules.unit (ringOf R)) N) ≫ whiskL R f := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hn
  rw [e1, e2, ← Category.assoc, h2, Category.assoc, leftU'_naturality, Category.assoc]

/-- **C5.** `unit ⊗ - ≅ 𝟭` on sheaves of modules. -/
def unitTensorIso : (tensorBifunctor R).obj (SheafOfModules.unit (ringOf R)) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun N => (SheafOfModules.forget (ringOf R)).preimageIso (unitTensorPre R N))
    (fun f => by
      apply (SheafOfModules.forget (ringOf R)).map_injective
      simp only [Functor.id_map, Functor.map_comp, Functor.preimageIso_hom,
        Functor.map_preimage]
      exact unitTensorPre_naturality R f)

/-- A direct summand of a flat module is flat. -/
theorem isFlat_of_retract {M F : Mod (ringOf R)} (i : M ⟶ F) (p : F ⟶ M) (hip : i ≫ p = 𝟙 M)
    (hF : IsFlat R F) : IsFlat R M := by
  refine ⟨fun {N' N} f hf => ?_⟩
  have h1 : Mono (((tensorBifunctor R).obj F).map f) := hF.preserves f
  have hsplit : ((tensorBifunctor R).map i).app N' ≫ ((tensorBifunctor R).map p).app N' =
      𝟙 _ := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, hip,
      CategoryTheory.Functor.map_id]
    rfl
  have h2 : Mono (((tensorBifunctor R).map i).app N') := mono_of_mono_fac hsplit
  have h3 : Mono (((tensorBifunctor R).map i).app N' ≫ ((tensorBifunctor R).obj F).map f) :=
    mono_comp _ _
  have hnat := ((tensorBifunctor R).map i).naturality f
  rw [← hnat] at h3
  exact mono_of_mono _ (((tensorBifunctor R).map i).app N)

/-- Direct summands of finite free modules are flat. -/
theorem isFlat_of_isFinFreeSummand {M : Mod (ringOf R)} (hM : IsFinFreeSummand M) :
    IsFlat R M := by
  obtain ⟨m, i, p, hip⟩ := hM
  exact isFlat_of_retract R i p hip
    (isFlat_sigma R (fun _ : Fin m => SheafOfModules.unit (ringOf R)) fun _ => isFlat_unit R)

/-- Strictly perfect complexes are K-flat. -/
theorem isKFlat_of_isStrictlyPerfect {P : CochainComplex (Mod (ringOf R)) ℤ}
    (hP : IsStrictlyPerfect P) : IsKFlat R P := by
  obtain ⟨⟨a, b, -, hb⟩, hfree⟩ := hP
  exact isKFlat_of_isFlat R P b fun n => isFlat_of_isFinFreeSummand R (hfree n)

end Site

section Space

open TopologicalSpace

variable {X : Type} [TopologicalSpace X]
  {R S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} (φ : R ⟶ S) (U : Opens X)

/-- Naturality of the iso `sheafBCOverIso`, `(S ⊗_R M)|U ≅ S|U ⊗_{R|U} M|U`, in `M`. (Needs the
private definition `overBCComp` of `Sheaf/BaseChange.lean`; to be proved there.) -/
theorem sheafBCOverIso_natural {M M' : Mod (ringOf R)} (g : M ⟶ M') :
    (restr (ringOf S) U).map ((sheafBC φ).map g) ≫ (sheafBCOverIso φ U M').hom =
      (sheafBCOverIso φ U M).hom ≫
        (sheafBC (overHom φ U)).map ((restr (ringOf R) U).map g) :=
  sheafBCOverIso_hom_naturality φ U g

/-- The restriction of a base change is the base change of the restriction, as complexes. -/
def overBCComplexIso (K : CochainComplex (Mod (ringOf R)) ℤ) :
    ((restr (ringOf S) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((sheafBC φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
    ((sheafBC (overHom φ U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((restr (ringOf R) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => sheafBCOverIso φ U (K.X n))
    (fun i j _ => by
      exact (sheafBCOverIso_natural φ U (K.d i j)).symm)

/-- Composing a quasi-isomorphism with the inverse of an isomorphism of complexes. -/
theorem quasiIso_comp_inv {A : Type*} [Category A] [Abelian A] {K L M : CochainComplex A ℤ}
    (f : K ⟶ L) (e : M ≅ L) [hf : QuasiIso f] : QuasiIso (f ≫ e.inv) :=
  have : IsIso e.inv := Iso.isIso_inv e
  quasiIso_comp f e.inv

/-- Restriction to `U` preserves strict boundedness above. -/
instance isStrictlyLE_restr (K : CochainComplex (Mod (ringOf R)) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE
      (((restr (ringOf R) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) b :=
  (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
    Functor.map_isZero (restr (ringOf R) U) (K.isZero_of_isStrictlyLE b i hi)

/-- **C5 step 2, local part.** A local roof `K|U ← L → P` with `K` bounded above, termwise flat
and `P` strictly perfect gives a roof for the base change of `K`. -/
theorem exists_roof_sheafBC (K : CochainComplex (Mod (ringOf R)) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hflat : ∀ n, IsFlat R (K.X n))
    (L P : CochainComplex (Mod ((ringOf R).over U)) ℤ)
    (f : L ⟶ ((restr (ringOf R) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (g : L ⟶ P) [QuasiIso f] [QuasiIso g] (hP : IsStrictlyPerfect P) :
    ∃ (L' P' : CochainComplex (Mod ((ringOf S).over U)) ℤ)
      (f' : L' ⟶ ((restr (ringOf S) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((sheafBC φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) (g' : L' ⟶ P'),
      QuasiIso f' ∧ QuasiIso g' ∧ IsStrictlyPerfect P' := by
  obtain ⟨⟨a, bP, -, hbP⟩, -⟩ := id hP
  have := isStrictlyLE_restr (R := R) U K b
  have hKU : IsKFlat (R.over U)
      (((restr (ringOf R) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    @isKFlat_of_isFlat _ _ _ _ _ (R.over U)
      (((restr (ringOf R) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) b this
      fun n => IsFlat.restr R (hflat n) U
  have hPK : IsKFlat (R.over U) P := isKFlat_of_isStrictlyPerfect (R.over U) hP
  have hLE : L.IsLE bP := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    have := ‹QuasiIso g›.quasiIsoAt i
    exact (exactAt_iff_of_quasiIsoAt g i).2 (P.exactAt_of_isLE bP i hi)
  have : (L.truncLE bP).IsStrictlyLE bP := by
    unfold CochainComplex.IsStrictlyLE
    infer_instance
  obtain ⟨F, h, hFle, hFflat, hh⟩ : ∃ (F : CochainComplex (Mod ((ringOf R).over U)) ℤ)
      (h : F ⟶ L.truncLE bP), F.IsStrictlyLE bP ∧ (∀ n, IsFlat (R.over U) (F.X n)) ∧
      QuasiIso h :=
    @exists_quasiIso_flat_site _ _ _ _ _ (R.over U) (L.truncLE bP) bP this
  have hF : IsKFlat (R.over U) F :=
    @isKFlat_of_isFlat _ _ _ _ _ (R.over U) F bP hFle hFflat
  have i1 : QuasiIso (L.ιTruncLE bP) := inferInstance
  have h01 : QuasiIso (L.ιTruncLE bP ≫ f) := inferInstance
  have h02 : QuasiIso (L.ιTruncLE bP ≫ g) := inferInstance
  have h1 : QuasiIso (h ≫ L.ιTruncLE bP ≫ f) := quasiIso_comp h (L.ιTruncLE bP ≫ f)
  have h2 : QuasiIso (h ≫ L.ιTruncLE bP ≫ g) := quasiIso_comp h (L.ιTruncLE bP ≫ g)
  have q1 := @quasiIso_sheafBC_of_isKFlat _ _ _ _ _ _ _ (overHom φ U) _ _ hF hKU
    (h ≫ L.ιTruncLE bP ≫ f) h1
  have q2 := @quasiIso_sheafBC_of_isKFlat _ _ _ _ _ _ _ (overHom φ U) _ _ hF hPK
    (h ≫ L.ιTruncLE bP ≫ g) h2
  refine ⟨_, _, ((sheafBC (overHom φ U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (h ≫ L.ιTruncLE bP ≫ f) ≫ (overBCComplexIso φ U K).inv,
    ((sheafBC (overHom φ U)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (h ≫ L.ιTruncLE bP ≫ g), quasiIso_comp_inv _ (overBCComplexIso φ U K) (hf := q1), q2,
    IsStrictlyPerfect.sheafBC (overHom φ U) hP⟩

end Space

end Cohesive
