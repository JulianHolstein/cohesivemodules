import Cohesivemodules.Main
import Cohesivemodules.MainH1
import Cohesivemodules.MainH2
import Cohesivemodules.ChecksForms

set_option linter.style.header false

/-!
# Checks of the main theorem (blueprint §9: K1 corollary, K6)

* K1 (corollary): in complex dimension `0` (`E = Fin 0 → ℂ`) H1 and H2 hold outright (K1 in
  `ChecksForms.lean`), so the main theorem holds unconditionally for every compact Hausdorff
  `X` modelled on `Fin 0 → ℂ` (e.g. a finite discrete space).
* K6: "full, faithful, essential image `P`" is equivalent to "`F` lands in `P` and its
  corestriction to `P` is an equivalence", for any property `P` closed under isomorphism
  (`full_faithful_essImage_iff`). Applied to `blockFunctor` and `Perf` (closed under
  isomorphism by definition): the corestriction `Ho(P_A) ⥤ D_perf(X)` is an equivalence
  (`isEquivalence_blockFunctor_lift`), and conversely the corestriction form implies the shape of
  `MainStatement` (`blockFunctor_iff`). Also `#print axioms` of `blockPerf` and
  `main_theorem_conditional`.
* Z4.g/Z4.h (phase 6): `#print axioms` of `dolbeaultGrothendieck` (H1 proved) and of the
  H1-free corollaries `blockPerf_of_localGaugeLemma`, `main_theorem_of_localGaugeLemma`.
* Z5.i/Z5.j (phase 7): `#print axioms` of `localGaugeLemma` (H2 proved) and of the unconditional
  `blockPerf_unconditional`, `main_theorem : MainStatement` (the names were
  `main_theorem_unconditional : MainStatementUnconditional` until 6 Nov 2026, §11 v1.22).
-/

universe w

namespace Cohesive.Checks

open CategoryTheory Manifold
open scoped ContDiff

/-! ## K6: the shape of the main statement -/

section Shape

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- **K6 (general).** For a functor `F : C ⥤ D` and a property `P` of objects of `D` closed under
isomorphism: `F` is full and faithful with essential image exactly `P` if and only if every
`F.obj X` satisfies `P` and the corestriction `C ⥤ P.FullSubcategory` is an equivalence. -/
theorem full_faithful_essImage_iff (F : C ⥤ D) (P : ObjectProperty D)
    [P.IsClosedUnderIsomorphisms] :
    (F.Full ∧ F.Faithful ∧ F.essImage = P) ↔
      ∃ hF : ∀ X, P (F.obj X), (P.lift F hF).IsEquivalence := by
  constructor
  · rintro ⟨hfull, hfaith, hess⟩
    have hF : ∀ X, P (F.obj X) := fun X => by
      rw [← hess]; exact F.obj_mem_essImage X
    refine ⟨hF, ?_⟩
    have : (P.lift F hF).EssSurj := ⟨fun Y => by
      have : F.essImage Y.obj := by rw [hess]; exact Y.property
      obtain ⟨X, ⟨e⟩⟩ := this
      exact ⟨X, ⟨P.ι.preimageIso e⟩⟩⟩
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨hF, hE⟩
    have : F.Full := Functor.Full.of_iso (P.liftCompιIso F hF)
    have : F.Faithful := Functor.Faithful.of_iso (P.liftCompιIso F hF)
    refine ⟨inferInstance, inferInstance, ?_⟩
    ext Y
    constructor
    · rintro ⟨X, ⟨e⟩⟩
      exact P.prop_of_iso e (hF X)
    · intro h
      have := hE.essSurj
      exact ⟨_, ⟨P.ι.mapIso ((P.lift F hF).objObjPreimageIso ⟨Y, h⟩)⟩⟩

end Shape

/-- K6: `D_perf(X, R)` is closed under isomorphism (by definition: objects isomorphic to `Q K`,
`K` perfect). -/
instance perf_isClosedUnderIsomorphisms {X : Type} [TopologicalSpace X] (R : RingSheaf X)
    [HasDerivedCategory.{w} (Mod R)] : (Perf R).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨K, hK, ⟨e'⟩⟩
    exact ⟨K, hK, ⟨e.symm ≪≫ e'⟩⟩

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **K6 (corollary).** Under H1 and H2, `blockFunctor E X` lands in `D_perf(X, O_X)` and its
corestriction `Ho(P_A) ⥤ D_perf(X, O_X)` is an equivalence of categories. -/
theorem isEquivalence_blockFunctor_lift [HasDerivedCategory.{w} (Mod (ringOf (holSheaf E X)))]
    (h₁ : DolbeaultGrothendieck E X) (h₂ : LocalGaugeLemma E X) :
    ∃ hF : ∀ M, Perf (ringOf (holSheaf E X)) ((blockFunctor E X).obj M),
      ((Perf (ringOf (holSheaf E X))).lift (blockFunctor E X) hF).IsEquivalence :=
  (full_faithful_essImage_iff _ _).1 (blockPerf E X h₁ h₂)

/-- **K6 (converse).** The conclusion of `MainStatement` for `blockFunctor E X` is equivalent to
the corestriction form: `blockFunctor E X` lands in `D_perf` and its corestriction is an
equivalence. So the shape of M (§1) is equivalent to "Ho(P_A) ≃ D_perf(X) via J". -/
theorem blockFunctor_iff [HasDerivedCategory.{w} (Mod (ringOf (holSheaf E X)))] :
    ((blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
        (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X))) ↔
      ∃ hF : ∀ M, Perf (ringOf (holSheaf E X)) ((blockFunctor E X).obj M),
        ((Perf (ringOf (holSheaf E X))).lift (blockFunctor E X) hF).IsEquivalence :=
  full_faithful_essImage_iff _ _

/-! ## K1: the unconditional case of complex dimension `0` -/

/-- **K1 (corollary).** For every compact Hausdorff complex manifold `X` of dimension `0`
(modelled on `Fin 0 → ℂ`, e.g. a finite discrete space), the main theorem holds with no
hypothesis: H1 and H2 are proved outright in dimension `0` (K1). -/
theorem blockPerf_dim_zero (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (Fin 0 → ℂ) X] [IsManifold 𝓘(ℂ, Fin 0 → ℂ) ∞ X]
    [HasDerivedCategory.{w} (Mod (ringOf (holSheaf (Fin 0 → ℂ) X)))] :
    (blockFunctor (Fin 0 → ℂ) X).Full ∧ (blockFunctor (Fin 0 → ℂ) X).Faithful ∧
      (blockFunctor (Fin 0 → ℂ) X).essImage = Perf (ringOf (holSheaf (Fin 0 → ℂ) X)) :=
  blockPerf _ X (K1_dolbeaultGrothendieck X) (K1_localGaugeLemma X)

/-- K1 (corollary) for the point `Fin 0 → ℂ` itself: the hypotheses of the main theorem are
satisfiable and its conclusion holds. -/
example [HasDerivedCategory.{w} (Mod (ringOf (holSheaf (Fin 0 → ℂ) (Fin 0 → ℂ))))] :
    (blockFunctor (Fin 0 → ℂ) (Fin 0 → ℂ)).Full :=
  (blockPerf_dim_zero (Fin 0 → ℂ)).1

end Cohesive.Checks

/-! ## K6: axioms -/

/-- info: 'main_theorem_conditional' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms main_theorem_conditional

/-- info: 'Cohesive.blockPerf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.blockPerf

/-! ## Z4.g, Z4.h: H1 proved; axioms -/

/-- info: 'Cohesive.dolbeaultGrothendieck' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.dolbeaultGrothendieck

/-- info: 'Cohesive.blockPerf_of_localGaugeLemma' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.blockPerf_of_localGaugeLemma

/-- info: 'main_theorem_of_localGaugeLemma' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms main_theorem_of_localGaugeLemma

/-- info: 'Cohesive.localGaugeLemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.localGaugeLemma

/-- info: 'Cohesive.blockPerf_unconditional' depends on axioms: [propext, Classical.choice,
Quot.sound] -/
#guard_msgs in
#print axioms Cohesive.blockPerf_unconditional

/-- info: 'main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_theorem
