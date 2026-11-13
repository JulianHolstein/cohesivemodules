-- FROZEN (gate 7; renamed 6 Nov 2026, v1.22, content unchanged). Do not edit.
import Cohesivemodules.BlockFunctorDef
import Cohesivemodules.Sheaf.PerfectDef

set_option linter.style.header false

/-!
# The main statement

Without hypotheses. Named `MainStatementUnconditional` in `StatementsUnconditional.lean` until
6 Nov 2026; renamed with content unchanged (blueprint §11 v1.22).

Blueprint item Z5.j (§11 v1.15: a new main statement without H1 and H2, frozen at the phase-7
gate). J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
Thm 4.1.3, in the perfect form of P. Antweiler, Thm 7.2.20 / 7.4.3 at h = 0. Imports only frozen
files. This is `MainStatementConditional` (`StatementsConditional.lean`) with the hypotheses
`DolbeaultGrothendieck E X`
(H1) and `LocalGaugeLemma E X` (H2) removed; everything else is verbatim.

## Deviations
* D_perf instead of D^b_coh (the step D_perf = D^b_coh is Z1, LATER).
* "Equivalence onto D_perf" is stated as: full, faithful, essential image = `Perf` (as in
  `MainStatementConditional`; the equivalent corestriction form is K6).
-/

namespace Cohesive

open CategoryTheory Manifold
open scoped ContDiff

/-- **The main statement** (Z5.j; formerly `MainStatementUnconditional`). For every
finite-dimensional complex normed space `E` and every compact Hausdorff complex manifold `X`
modelled on `E` (complex `C^∞` charts, i.e. holomorphic), the functor `blockFunctor E X : Ho(P_A) ⥤ D(O_X)`, `M ↦ α(M)`, from the homotopy
category of cohesive modules over the Dolbeault algebra `A = 𝒜_X(X)` to the derived category of
sheaves of `O_X`-modules, is full and faithful, and its essential image is exactly
`D_perf(X, O_X)`. The derived category is Mathlib's `HasDerivedCategory.standard`, the same for
`blockFunctor` and `Perf`. -/
def MainStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X],
      letI := HasDerivedCategory.standard (Mod (ringOf (holSheaf E X)))
      (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
        (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X))

end Cohesive
