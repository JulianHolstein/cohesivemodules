-- FROZEN (gate 5; renamed 6 Nov 2026, v1.22, content unchanged). Do not edit.
import Cohesivemodules.BlockFunctorDef
import Cohesivemodules.Sheaf.PerfectDef
import Cohesivemodules.Hypotheses

set_option linter.style.header false

/-!
# The main statement, conditional on H1 and H2

Named `MainStatement` in `Statements.lean` until 6 Nov 2026; renamed with content unchanged
(blueprint §11 v1.22). The canonical statement is now `MainStatement` (`Statements.lean`), which is
this one without H1 and H2.

Blueprint §1 (item M), conventions §9. J. Block, *Duality and equivalence of module categories in
noncommutative geometry*, Thm 4.1.3, in the perfect form of P. Antweiler, Thm 7.2.20 / 7.4.3 at
h = 0. Imports only frozen files; frozen at gate 5.

## Deviations
* D_perf instead of D^b_coh (the step D_perf = D^b_coh is Z1, LATER).
* "Equivalence onto D_perf" is stated as: full, faithful, essential image = `Perf` (§1 ⚠: a
  functor into D_perf cannot be defined before H2); the equivalent corestriction form is K6.
* H1 and H2 are hypotheses on `X`, not proved (Z4, Z5).
-/

namespace Cohesive

open CategoryTheory Manifold
open scoped ContDiff

/-- **The main statement, conditional** (blueprint §1, M; formerly `MainStatement`). For every
finite-dimensional complex normed space `E` and every compact Hausdorff complex manifold `X`
modelled on `E` (complex `C^∞` charts, i.e. holomorphic), if `X` satisfies the Dolbeault–Grothendieck lemma (H1) and the local gauge lemma in
its weak form (H2), then the functor `blockFunctor E X : Ho(P_A) ⥤ D(O_X)`, `M ↦ α(M)`, from the
homotopy category of cohesive modules over the Dolbeault algebra `A = 𝒜_X(X)` to the derived
category of sheaves of `O_X`-modules, is full and faithful, and its essential image is exactly
`D_perf(X, O_X)`. The derived category is Mathlib's `HasDerivedCategory.standard`, the same for
`blockFunctor` and `Perf`. -/
def MainStatementConditional : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X],
    DolbeaultGrothendieck E X → LocalGaugeLemma E X →
      letI := HasDerivedCategory.standard (Mod (ringOf (holSheaf E X)))
      (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
        (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X))

end Cohesive
