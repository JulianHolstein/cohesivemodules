import Cohesivemodules.MainH1
import Cohesivemodules.Forms.LocalGauge
import Cohesivemodules.Statements

set_option linter.style.header false

/-!
# Z5.j: Block's theorem without hypotheses

Blueprint item Z5.j (§11 v1.15). H1 (`dolbeaultGrothendieck`, Z4.g) and H2 (`localGaugeLemma`,
Z5.i) hold on every complex manifold, so Block's theorem in its perfect form holds
unconditionally.
* `blockPerf_unconditional`: `blockPerf` without hypotheses, for any `HasDerivedCategory`.
* `main_theorem : MainStatement`, the main theorem of the project (named
  `main_theorem_unconditional : MainStatementUnconditional` until 6 Nov 2026, blueprint §11 v1.22).

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

/-- **Z5.j. Block's theorem, perfect form, unconditional.** [B, Thm 4.1.3], [A, Thm 7.2.20,
Thm 7.4.3 at h = 0]. For a compact Hausdorff complex manifold `X`, `blockFunctor E X : Ho(P_A) ⥤
D(O_X)` is full and faithful with essential image `D_perf(X, O_X)`, for any `HasDerivedCategory`
instance. -/
theorem blockPerf_unconditional [h : HasDerivedCategory.{w} (Mod (ringOf (holSheaf E X)))] :
    (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
      (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X)) :=
  blockPerf (h := h) E X (dolbeaultGrothendieck E X) (localGaugeLemma E X)

end Cohesive

open Cohesive

/-- **Z5.j. The main theorem** (without hypotheses): `MainStatement` holds. -/
theorem main_theorem : MainStatement := by
  intro E _ _ _ X _ _ _ _ _
  exact main_theorem_conditional E X (dolbeaultGrothendieck E X) (localGaugeLemma E X)
