import Cohesivemodules.Sheaf.Flat
import Cohesivemodules.Sheaf.Resolution
import Mathlib.RingTheory.Flat.CategoryTheory

set_option linter.style.header false

/-!
# S8.d–e: flat resolutions

Blueprint item S8 (§3), the resolution part of S8.d and S8.e, split off from `Flat.lean`.

* `isFlat_of_isZero`: zero modules are flat.
* `exists_epi_flat`: on any site, every module is a quotient of a flat module (a coproduct of
  sheafified free modules on representables). This is the general-site form of S8.c, which
  `Flat.lean` proves on `Opens X` with the modules `j_! R|U` (`exists_epi_sigma_extZero`).
* S8.d `exists_quasiIso_flat_site` (any site) and `exists_quasiIso_flat` (on `Opens X`): flat
  resolutions of complexes strictly zero above some degree (`exists_quasiIso_of_enough`).
* S8.e `acyclic_tensorC_of_isKFlat`.

## Deviations
* S8.e is stated for bounded-above `L` (as in `Flat.lean`).
* `exists_quasiIso_flat_site` is the general-site form of `exists_quasiIso_flat`, needed because
  S8.e is used on general sites (`BaseChange.lean`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace

/-- Tensoring with a free module preserves monomorphisms of modules. -/
private lemma mono_whiskerLeft_free {A : Type} [CommRing A] (S : Type)
    {N N' : ModuleCat.{0} A} (g : N ⟶ N') [Mono g] :
    Mono (((ModuleCat.free A).obj S) ◁ g) := by
  have : Module.Flat A ((ModuleCat.free A).obj S) := by
    show Module.Flat A (S →₀ A)
    infer_instance
  exact (inferInstance : Mono ((tensorLeft ((ModuleCat.free A).obj S)).map g))

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  (R : Sheaf J CommRingCat.{0})

/-- **S8.b.** A zero module is flat (`M ⊗ -` is then zero). -/
theorem isFlat_of_isZero {M : Mod (ringOf R)} (hM : IsZero M) : IsFlat R M := by
  refine ⟨fun {N N'} f _ => ?_⟩
  have hz : IsZero (((tensorBifunctor R).obj M).obj N) :=
    Functor.map_isZero ((tensorBifunctor R).flip.obj N) hM
  exact ⟨fun g h _ => hz.eq_of_tgt _ _⟩

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- Sectionwise free presheaves of modules are flat for presheaf monomorphisms. -/
private lemma mono_whiskerLeft_freeObj (F : Cᵒᵖ ⥤ Type)
    {N N' : PresheafOfModulesOfCommRing.{0} R.obj} (g : N ⟶ N') [Mono g] :
    Mono ((PresheafOfModules.freeObj (R := R.obj ⋙ forget₂ CommRingCat RingCat) F :
      PresheafOfModulesOfCommRing.{0} R.obj) ◁ g) := by
  refine PresheafOfModules.mono_of_injective fun X => ?_
  have h1 : Mono (g.app' X) := inferInstanceAs (Mono (g.app X))
  have h : Mono (((ModuleCat.free (R.obj.obj X)).obj (F.obj X)) ◁ g.app' X) :=
    mono_whiskerLeft_free _ _
  exact (ModuleCat.mono_iff_injective _).1 h

/-- The sheafification of a presheaf `P` with `P ⊗ -` preserving monos is flat. -/
private lemma isFlat_sheafifyF_obj (P : PresheafOfModules.{0} (ringOf R).obj)
    (hP : ∀ {N N' : PresheafOfModulesOfCommRing.{0} R.obj} (g : N ⟶ N') [Mono g],
      Mono (MonoidalCategory.whiskerLeft (C := PresheafOfModulesOfCommRing.{0} R.obj) P g)) :
    IsFlat R ((sheafifyF R).obj P) := by
  refine ⟨fun {N N'} f hf => ?_⟩
  have := hf
  have h1 : Mono ((SheafOfModules.forget (ringOf R)).map f) := inferInstance
  have h2 : ((tensorBifunctor R).obj ((sheafifyF R).obj P)).map f =
      (sheafifyF R).map (MonoidalCategory.whiskerLeft
        (C := PresheafOfModulesOfCommRing.{0} R.obj) ((sheafifyF R).obj P).val
        ((SheafOfModules.forget (ringOf R)).map f : _)) := rfl
  have h3 : IsIso ((sheafifyF R).map (MonoidalCategory.whiskerRight
      (C := PresheafOfModulesOfCommRing.{0} R.obj)
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P)
        N.val)) :=
    isIso_sheafifyF_map_whiskerRight R P N.val
  have h4 : IsIso ((sheafifyF R).map (MonoidalCategory.whiskerRight
      (C := PresheafOfModulesOfCommRing.{0} R.obj)
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P)
        N'.val)) :=
    isIso_sheafifyF_map_whiskerRight R P N'.val
  rw [h2]
  set η := (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P
  have h5 : Mono (MonoidalCategory.whiskerLeft (C := PresheafOfModulesOfCommRing.{0} R.obj) P
      ((SheafOfModules.forget (ringOf R)).map f : _)) := @hP _ _ _ h1
  have h6 : Mono ((sheafifyF R).map (MonoidalCategory.whiskerLeft
      (C := PresheafOfModulesOfCommRing.{0} R.obj) P
      ((SheafOfModules.forget (ringOf R)).map f : _))) :=
    @Functor.map_mono _ _ _ _ (sheafifyF R) _ _ _ _ h5
  have key : (sheafifyF R).map (MonoidalCategory.whiskerRight
      (C := PresheafOfModulesOfCommRing.{0} R.obj) η N.val) ≫
      (sheafifyF R).map (MonoidalCategory.whiskerLeft
        (C := PresheafOfModulesOfCommRing.{0} R.obj) ((sheafifyF R).obj P).val
        ((SheafOfModules.forget (ringOf R)).map f : _)) =
      (sheafifyF R).map (MonoidalCategory.whiskerLeft
        (C := PresheafOfModulesOfCommRing.{0} R.obj) P
        ((SheafOfModules.forget (ringOf R)).map f : _)) ≫
      (sheafifyF R).map (MonoidalCategory.whiskerRight
        (C := PresheafOfModulesOfCommRing.{0} R.obj) η N'.val) := by
    have hx := (MonoidalCategory.whisker_exchange (C := PresheafOfModulesOfCommRing.{0} R.obj)
      η ((SheafOfModules.forget (ringOf R)).map f : _)).symm
    exact ((sheafifyF R).map_comp _ _).symm.trans ((congrArg (sheafifyF R).map hx).trans
      ((sheafifyF R).map_comp _ _))
  have h7 : Mono ((sheafifyF R).map (MonoidalCategory.whiskerRight
      (C := PresheafOfModulesOfCommRing.{0} R.obj) η N.val) ≫
      (sheafifyF R).map (MonoidalCategory.whiskerLeft
        (C := PresheafOfModulesOfCommRing.{0} R.obj) ((sheafifyF R).obj P).val
        ((SheafOfModules.forget (ringOf R)).map f : _))) := by
    rw [key]
    have h8 := @IsIso.mono_of_iso _ _ _ _ _ h4
    exact @mono_comp _ _ _ _ _ _ h6 _ h8
  have e := IsIso.inv_hom_id_assoc ((sheafifyF R).map (MonoidalCategory.whiskerRight
      (C := PresheafOfModulesOfCommRing.{0} R.obj) η N.val))
    ((sheafifyF R).map (MonoidalCategory.whiskerLeft
        (C := PresheafOfModulesOfCommRing.{0} R.obj) ((sheafifyF R).obj P).val
        ((SheafOfModules.forget (ringOf R)).map f : _)))
  erw [← e]
  have h9 := @IsIso.mono_of_iso _ _ _ _ _ (inferInstance : IsIso (inv ((sheafifyF R).map
    (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} R.obj) η N.val))))
  exact @mono_comp _ _ _ _ _ _ h9 _ h7

/-- **S8.c (any site).** Every module `M` is a quotient of a flat module. Proof: the sheafified
free module on a representable `yoneda.obj Y` is flat (sectionwise it is free; as for
`isFlat_unit`), and `M` is a quotient of a coproduct of these, one for each section of `M`
(`isFlat_sigma`). -/
theorem exists_epi_flat (M : Mod (ringOf R)) :
    ∃ (F : Mod (ringOf R)) (f : F ⟶ M), IsFlat R F ∧ Epi f := by
  let P : PresheafOfModules.{0} (ringOf R).obj := (SheafOfModules.forget (ringOf R)).obj M
  let G : P.Elements → Mod (ringOf R) := fun m => (sheafifyF R).obj m.freeYoneda
  have hG : ∀ m, IsFlat R (G m) := fun m =>
    isFlat_sheafifyF_obj R _ (fun {N N'} g hg => mono_whiskerLeft_freeObj R _ g)
  refine ⟨∐ G, ?_, isFlat_sigma R G hG, ?_⟩
  · exact sigmaComparison (sheafifyF R) _ ≫ (sheafifyF R).map P.fromFreeYonedaCoproduct ≫
      (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit.app M
  · have : IsIso (sigmaComparison (sheafifyF R) (fun m : P.Elements => m.freeYoneda)) :=
      inferInstance
    have h1 : Epi ((sheafifyF R).map P.fromFreeYonedaCoproduct) := inferInstance
    have h2 : IsIso ((PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf R).obj)).counit.app M) := inferInstance
    have h3 := @IsIso.epi_of_iso _ _ _ _ _ h2
    have h4 := @epi_comp _ _ _ _ _ _ h1 _ h3
    exact @epi_comp _ _ _ _ _ _ inferInstance _ h4


/-- **S8.d (any site).** Every complex strictly zero above degree `b` receives a
quasi-isomorphism from a complex of flat modules strictly zero above degree `b`
(`exists_quasiIso_of_enough` with `exists_epi_flat`). -/
theorem exists_quasiIso_flat_site (K : CochainComplex (Mod (ringOf R)) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] :
    ∃ (F : CochainComplex (Mod (ringOf R)) ℤ) (f : F ⟶ K),
      F.IsStrictlyLE b ∧ (∀ n, IsFlat R (F.X n)) ∧ QuasiIso f :=
  exists_quasiIso_of_enough (fun M => IsFlat R M) (exists_epi_flat R)
    (fun _ h => isFlat_of_isZero R h) K b

/-- **S8.e.** For `K` K-flat and acyclic, `K ⊗ L` is acyclic for every bounded-above `L`:
resolve `L' → L` by flat modules (S8.d); `K ⊗ L' ≅ L' ⊗ K` is acyclic as `L'` is K-flat, and
`K ⊗ L' → K ⊗ L` is a quasi-isomorphism as `K` is K-flat. -/
theorem acyclic_tensorC_of_isKFlat {K : CochainComplex (Mod (ringOf R)) ℤ} (hK : IsKFlat R K)
    (hKa : K.Acyclic) (L : CochainComplex (Mod (ringOf R)) ℤ) (b : ℤ) [L.IsStrictlyLE b] :
    (tensorC R K L).Acyclic := by
  obtain ⟨F, f, hFb, hF, hq⟩ := exists_quasiIso_flat_site R L b
  have hFa : (tensorC R K F).Acyclic :=
    fun i => ((isKFlat_of_isFlat R F b hF) K hKa i).of_iso (tensorCSymIso R K F).symm
  have := quasiIso_tensorCMap₂ R hK f
  intro i
  have := this.quasiIsoAt i
  exact (exactAt_iff_of_quasiIsoAt (tensorCMap₂ R K f) i).1 (hFa i)

end Site

section Space

variable {X : Type} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})

/-- **S8.d. Flat resolutions.** Every complex strictly zero above degree `b` receives a
quasi-isomorphism from a complex of flat modules strictly zero above degree `b` (S8.c degree by
degree, as for projective resolutions). [Stacks, chapter *Cohomology of Sheaves*, K-flat
complexes] -/
theorem exists_quasiIso_flat (K : CochainComplex (Mod (ringOf R)) ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (F : CochainComplex (Mod (ringOf R)) ℤ) (f : F ⟶ K),
      F.IsStrictlyLE b ∧ (∀ n, IsFlat R (F.X n)) ∧ QuasiIso f :=
  exists_quasiIso_flat_site R K b

end Space

end Cohesive
