import Cohesivemodules.Sheaf.Restriction
import Mathlib.Algebra.Homology.SingleHomology

set_option linter.style.header false

/-!
# C0 (auxiliary): sectionwise criteria for quasi-isomorphisms of sheaf complexes

Generic lemmas used by `Comparison/Setup.lean` (`quasiIso_ρhat`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits Opposite

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {S : Sheaf J RingCat.{0}}

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A sheaf of modules all of whose sections are subsingletons is zero. -/
theorem isZero_of_sections_subsingleton {M : Mod S}
    (h : ∀ V : Cᵒᵖ, Subsingleton (M.val.obj V)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  ext V s
  exact Subsingleton.elim _ _

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A morphism of sheaves of modules that is injective on sections is mono. -/
theorem mono_of_sections_injective {M N : Mod S} (f : M ⟶ N)
    (hf : ∀ V : Cᵒᵖ, Function.Injective (f.val.app V)) : Mono f := by
  refine ⟨fun g h hgh => ?_⟩
  ext V s
  apply hf V
  exact congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V) hgh)) s)

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A morphism of sheaves of modules that is surjective on sections is epi. -/
theorem epi_of_sections_surjective' {M N : Mod S} (f : M ⟶ N)
    (hf : ∀ V : Cᵒᵖ, Function.Surjective (f.val.app V)) : Epi f := by
  refine ⟨fun g h hgh => ?_⟩
  ext V s
  obtain ⟨t, rfl⟩ := hf V s
  exact congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V) hgh)) t)

omit [HasWeakSheafify J AddCommGrpCat.{0}] in
/-- Sections of a kernel are computed sectionwise. -/
theorem kernel_sections' {M N : Mod S} (g : M ⟶ N) (V : Cᵒᵖ) :
    Function.Injective ((kernel.ι g).val.app V) ∧
      ∀ s : M.val.obj V, g.val.app V s = 0 → ∃ u, (kernel.ι g).val.app V u = s := by
  have hex := ShortComplex.exact_kernel g
  have hex' := hex.map_of_mono_of_preservesKernel (SheafOfModules.evaluation.{0} S V)
    inferInstance inferInstance
  refine ⟨?_, (ShortComplex.moduleCat_exact_iff _).1 hex'⟩
  have : Mono ((SheafOfModules.evaluation.{0} S V).map (kernel.ι g)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

omit [HasWeakSheafify J AddCommGrpCat.{0}] in
/-- If `ρ : A → T.X₂` is a sectionwise kernel of `T.g`, then the induced map
`A → T.cycles` is an isomorphism. -/
theorem isIso_liftCycles_of_sections (T : ShortComplex (Mod S)) {A : Mod S}
    (ρ : A ⟶ T.X₂) (hρ : ρ ≫ T.g = 0)
    (hinj : ∀ V : Cᵒᵖ, Function.Injective (ρ.val.app V))
    (hsurj : ∀ (V : Cᵒᵖ) (s : T.X₂.val.obj V), T.g.val.app V s = 0 →
      ∃ r, ρ.val.app V r = s) :
    IsIso (T.liftCycles ρ hρ) := by
  let κ : A ⟶ kernel T.g := kernel.lift T.g ρ hρ
  have hκι : κ ≫ kernel.ι T.g = ρ := kernel.lift_ι _ _ _
  have happ : ∀ (V : Cᵒᵖ) (a : A.val.obj V),
      (kernel.ι T.g).val.app V (κ.val.app V a) = ρ.val.app V a := fun V a =>
    congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V) hκι)) a)
  have : Mono κ := mono_of_sections_injective κ fun V a b hab =>
    hinj V (by rw [← happ V a, ← happ V b, hab])
  have : Epi κ := epi_of_sections_surjective' κ fun V u => by
    obtain ⟨hι, -⟩ := kernel_sections' T.g V
    have hg : T.g.val.app V ((kernel.ι T.g).val.app V u) = 0 :=
      congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V) (kernel.condition T.g))) u)
    obtain ⟨r, hr⟩ := hsurj V _ hg
    exact ⟨r, hι (by rw [happ, hr])⟩
  have : IsIso κ := isIso_of_mono_of_epi κ
  let e : T.cycles ≅ kernel T.g :=
    IsLimit.conePointUniqueUpToIso T.cyclesIsKernel (limit.isLimit (parallelPair T.g 0))
  have he : e.hom ≫ kernel.ι T.g = T.iCycles :=
    IsLimit.conePointUniqueUpToIso_hom_comp T.cyclesIsKernel
      (limit.isLimit (parallelPair T.g 0)) WalkingParallelPair.zero
  have hfac : T.liftCycles ρ hρ ≫ e.hom = κ := by
    rw [← cancel_mono (kernel.ι T.g), Category.assoc, he, ShortComplex.liftCycles_i, hκι]
  have : T.liftCycles ρ hρ = κ ≫ e.inv := by
    rw [← cancel_mono e.hom, Category.assoc, e.inv_hom_id, Category.comp_id, hfac]
  rw [this]
  infer_instance

omit [HasWeakSheafify J AddCommGrpCat.{0}] in
/-- **Criterion.** `ρ̂ : single A 0 ⟶ L` is a quasi-isomorphism of complexes of sheaves of modules
if `L` is exact away from degree `0`, `L^i = 0` for `i < 0`, and `ρ : A → L⁰` is sectionwise the
kernel of `d⁰`. -/
theorem quasiIso_mkHomFromSingle {L : CochainComplex (Mod S) ℤ} {A : Mod S} (ρ : A ⟶ L.X 0)
    (hρ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → ρ ≫ L.d 0 k = 0)
    (hneg : ∀ i : ℤ, i < 0 → IsZero (L.X i))
    (hinj : ∀ V : Cᵒᵖ, Function.Injective (ρ.val.app V))
    (hsurj : ∀ (V : Cᵒᵖ) (s : (L.X 0).val.obj V), (L.d 0 1).val.app V s = 0 →
      ∃ r, ρ.val.app V r = s)
    (hpos : ∀ i : ℤ, 0 < i → L.ExactAt i) :
    QuasiIso (HomologicalComplex.mkHomFromSingle ρ hρ) := by
  refine ⟨fun i => ?_⟩
  by_cases hi : i = 0
  · subst hi
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp),
      ShortComplex.quasiIso_iff_isIso_liftCycles]
    · have hτ : ((HomologicalComplex.shortComplexFunctor' (Mod S) (ComplexShape.up ℤ) (-1) 0 1).map
          (HomologicalComplex.mkHomFromSingle ρ hρ)).τ₂ =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).hom ≫ ρ :=
        HomologicalComplex.mkHomFromSingle_f ρ hρ
      let e := HomologicalComplex.singleObjXSelf (V := Mod S) (ComplexShape.up ℤ) 0 A
      have h1 : ∀ (V : Cᵒᵖ) (x), e.hom.val.app V (e.inv.val.app V x) = x := fun V x =>
        congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V) e.inv_hom_id)) x)
      have h2 : ∀ (V : Cᵒᵖ) (x), e.inv.val.app V (e.hom.val.app V x) = x := fun V x =>
        congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V) e.hom_inv_id)) x)
      refine isIso_liftCycles_of_sections _ _ _ ?_ ?_
      · intro V a b hab
        rw [hτ] at hab
        have := hinj V hab
        rw [← h2 V a, ← h2 V b]
        exact congrArg _ this
      · intro V s hs
        obtain ⟨r, hr⟩ := hsurj V s hs
        refine ⟨e.inv.val.app V r, ?_⟩
        rw [hτ]
        show ρ.val.app V (e.hom.val.app V (e.inv.val.app V r)) = s
        rw [h1, hr]
    · rfl
    · rfl
    · exact (hneg (-1) (by omega)).eq_of_src _ _
  · rw [quasiIsoAt_iff_exactAt _ i
      (HomologicalComplex.exactAt_single_obj (ComplexShape.up ℤ) 0 A i hi)]
    rcases lt_or_gt_of_ne hi with h | h
    · exact ShortComplex.exact_of_isZero_X₂ _ (hneg i h)
    · exact hpos i h

end Site

end Cohesive
