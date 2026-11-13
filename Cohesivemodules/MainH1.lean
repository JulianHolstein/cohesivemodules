import Cohesivemodules.Main
import Cohesivemodules.Forms.DolbeaultGrothendieck

set_option linter.style.header false

/-!
# Z4.h: Block's theorem with H1 proved

Blueprint item Z4.h (§11, v1.14). H1 holds on every complex manifold (Z4.g,
`dolbeaultGrothendieck`), so Block's theorem in its perfect form (`blockPerf`,
`main_theorem_conditional`) needs only the local gauge lemma H2. Theorems only:
`MainStatementConditional` (frozen) is unchanged, and no new statement is frozen (human, 1 Nov
2026: a new main statement follows after H2 is proved, Z5).
* `blockPerf_of_localGaugeLemma`: `blockPerf` without the hypothesis H1.
* `main_theorem_of_localGaugeLemma`: the statement of `MainStatementConditional` without H1, for
  `HasDerivedCategory.standard`.

## Deviations
* None beyond those of `MainStatementConditional` and `blockPerf`.
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **Z4.h. Block's theorem, perfect form, with H1 proved.** [B, Thm 4.1.3], [A, Thm 7.2.20,
Thm 7.4.3 at h = 0]. For a compact Hausdorff complex manifold `X` satisfying the local gauge lemma
(H2), `blockFunctor E X : Ho(P_A) ⥤ D(O_X)` is full and faithful with essential image
`D_perf(X, O_X)`, for any `HasDerivedCategory` instance. H1 is `dolbeaultGrothendieck` (Z4.g). -/
theorem blockPerf_of_localGaugeLemma [h : HasDerivedCategory.{w} (Mod (ringOf (holSheaf E X)))]
    (h₂ : LocalGaugeLemma E X) :
    (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
      (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X)) :=
  blockPerf (h := h) E X (dolbeaultGrothendieck E X) h₂

end Cohesive

open CategoryTheory Manifold Cohesive
open scoped ContDiff

/-- **Z4.h. The main theorem with H1 proved.** `MainStatementConditional` without its hypothesis H1: for
every finite-dimensional complex `E` and every compact Hausdorff complex manifold `X` modelled on
`E` satisfying the local gauge lemma (H2), `blockFunctor E X` is full and faithful with essential
image `D_perf(X, O_X)` (derived category `HasDerivedCategory.standard`). -/
theorem main_theorem_of_localGaugeLemma :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
      (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
      [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X],
      LocalGaugeLemma E X →
        letI := HasDerivedCategory.standard (Mod (ringOf (holSheaf E X)))
        (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
          (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X)) := by
  intro E _ _ _ X _ _ _ _ _ h₂
  exact main_theorem_conditional E X (dolbeaultGrothendieck E X) h₂
