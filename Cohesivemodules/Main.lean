import Cohesivemodules.StatementsConditional
import Cohesivemodules.Comparison.Equivalence

set_option linter.style.header false

/-!
# F14 (C0.b part), F15: Block's theorem, perfect form

Blueprint items F14, F15 (§5) and M (§1). With H1 and H2 the Dolbeault pre-resolving data
(`BlockFunctorDef.lean`) complete to resolving data (C0.b): F12 gives `ρ` injective and exactness
in degree 0, H1 is exactness in degrees `q + 1`, H2 is the local lifting LL. C6 then gives
`blockPerf`, and `main_theorem_conditional : MainStatementConditional` (named `main_theorem :
MainStatement` until 6 Nov 2026, blueprint §11 v1.22; the unconditional `main_theorem` is in
`MainH2.lean`).

## Deviations
* `blockPerf` holds for every `HasDerivedCategory` instance; `MainStatementConditional` fixes
  `HasDerivedCategory.standard`.
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **F14 (C0.b).** [A, Assumptions 7.2 at h = 0], [B, Lemma 4.1.5]. Given H1 and H2, the
Dolbeault data are resolving data: `ρ : O_X → 𝒜⁰` is injective and `O_X → 𝒜⁰ → 𝒜¹` is exact
(F12), the Dolbeault complex is exact in degrees `≥ 1` (H1), and local lifting holds (H2). -/
def dolbeaultData (h₁ : DolbeaultGrothendieck E X) (h₂ : LocalGaugeLemma E X) :
    ResolvingData X :=
  { dolbeaultPreData E X with
    ρ_injective := dolbeaultRhoU_injective E
    exact0 := fun _ a ha ↦ exists_dolbeaultRhoU_of_dbar_eq_zero E a ha
    exactq := h₁
    LL := h₂ }

/-- F14: the resolving data extend the pre-resolving data of `blockFunctor` (rfl). -/
theorem dolbeaultData_toPreResolvingData (h₁ : DolbeaultGrothendieck E X)
    (h₂ : LocalGaugeLemma E X) :
    (dolbeaultData E X h₁ h₂).toPreResolvingData = dolbeaultPreData E X := rfl

/-- **F15. Block's theorem, perfect form** (blueprint §1, M). [B, Thm 4.1.3], [A, Thm 7.2.20,
Thm 7.4.3 at h = 0]. For a compact Hausdorff complex manifold `X` satisfying H1 and H2, the functor
`blockFunctor E X : Ho(P_A) ⥤ D(O_X)` (`A = 𝒜_X(X)`) is full and faithful with essential image
`D_perf(X, O_X)`. Deviation: stated for any `HasDerivedCategory` instance (`MainStatementConditional` uses
the standard one). -/
theorem blockPerf [h : HasDerivedCategory.{w} (Mod (ringOf (holSheaf E X)))]
    (h₁ : DolbeaultGrothendieck E X) (h₂ : LocalGaugeLemma E X) :
    (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
      (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X)) :=
  @ResolvingData.comparison _ _ (dolbeaultData E X h₁ h₂) _ _ h

end Cohesive

/-- **The main theorem, conditional** (blueprint §1, M): `MainStatementConditional` holds. -/
theorem main_theorem_conditional : Cohesive.MainStatementConditional := by
  intro E _ _ _ X _ _ _ _ _ h₁ h₂
  exact Cohesive.blockPerf (h := HasDerivedCategory.standard _) E X h₁ h₂
