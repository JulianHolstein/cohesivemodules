import Cohesivemodules.Main

set_option linter.style.header false

/-!
# Non-vacuity of the layer-C definitions (CLAUDE.md §7)

* `K_C0_pre`: the Dolbeault data satisfy every field of `PreResolvingData` (C0.a), with no
  hypothesis beyond compact Hausdorff `X` (`dolbeaultPreData`, F14).
* `K_C0`: with H1 and H2, they satisfy `ResolvingData` (C0.b) (`dolbeaultData`, F14); the fields
  `exactq` and `LL` are H1 and H2 verbatim.
-/

noncomputable section

namespace Cohesive.Checks

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  [T2Space X] [CompactSpace X]

/-- **Non-vacuity of C0.a.** The Dolbeault data are pre-resolving data. -/
def K_C0_pre : PreResolvingData X := dolbeaultPreData E X

/-- **Non-vacuity of C0.b.** With H1 and H2 the Dolbeault data are resolving data; `exactq` and
`LL` are H1 and H2 verbatim. -/
def K_C0 (h1 : DolbeaultGrothendieck E X) (h2 : LocalGaugeLemma E X) : ResolvingData X :=
  dolbeaultData E X h1 h2

/-- The fields `exactq` and `LL` of `K_C0` are the hypotheses H1 and H2 (rfl). -/
example (h1 : DolbeaultGrothendieck E X) (h2 : LocalGaugeLemma E X) :
    (K_C0 E X h1 h2).exactq = h1 ∧ (K_C0 E X h1 h2).LL = h2 := ⟨rfl, rfl⟩

end Cohesive.Checks
