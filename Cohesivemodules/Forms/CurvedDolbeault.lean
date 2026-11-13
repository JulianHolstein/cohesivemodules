-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Comparison.CurvedPresheaf
import Cohesivemodules.BlockFunctorDef

set_option linter.style.header false

/-!
# Z3.c: the curved Dolbeault algebra

Blueprint item Z3.c (`blueprint/blueprint-tw.md` §2.1; blueprint §11 v1.19). For a `∂̄`-closed
`h ∈ 𝒜^{0,2}(X)` (`DolbeaultClosed2 E X`):
* `curvedDolbeaultPresheaf E X h`: the Dolbeault presheaf (F14) with curvature `h|U` on every `U`;
* `curvedDolbeault E X h = (𝒜_X(X), ∂̄, h)`, the curved Dolbeault algebra of [A, §7.4], [B, §4.2].
At `h = 0` the curved instance is definitionally the frozen one (`curvedDolbeault_zero_inst`,
prototype P15).

## Deviations
* Left modules: cohesive modules over `curvedDolbeault E X h` satisfy `𝕏² = h·`, so
  `h = h_[A]` ([A, Rem 4.0.4]) and `h = −B` for Block's `B` ([B, §4.2], right modules; A13).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **Z3.c.** [A, §7.4], [B, §4.2]. The `∂̄`-closed forms of degree `2` on `X` (global Dolbeault
forms of bidegree `(0,2)`): the possible curvatures of the curved Dolbeault algebra. -/
def DolbeaultClosed2 : Type :=
  {h : DolbeaultAlg E (⊤ : Opens X) //
    h ∈ dolbeault E X 2 ∧ GCDga.d (𝒜 := dolbeault E X) h = 0}

/-- Z3.c: the zero form is closed. -/
instance : Zero (DolbeaultClosed2 E X) := ⟨⟨0, Submodule.zero_mem _, map_zero _⟩⟩

/-- Z3.c: the underlying form of `0` is `0` (rfl). -/
theorem DolbeaultClosed2.coe_zero : (0 : DolbeaultClosed2 E X).1 = 0 := rfl

variable {E X} in
/-- **Z3.c.** [A, §7.2–7.4]. The Dolbeault presheaf of dgas `U ↦ (𝒜_X(U), ∂̄, h|U)` with
curvature the restriction of `h`. -/
def curvedDolbeaultPresheaf (h : DolbeaultClosed2 E X) : DgaPresheaf X :=
  (dolbeaultPresheaf E X).withCurvature h.1 h.2.1 h.2.2

variable {E X} in
/-- **Z3.c.** [A, §7.4], [B, §4.2]. The curved Dolbeault algebra `(𝒜_X(X), ∂̄, h)`, graded by form
degree. Its `GCDga` instance (found through `DgaPresheaf.dga`) has `c = h`. -/
abbrev curvedDolbeault (h : DolbeaultClosed2 E X) : ℤ → Submodule ℂ (DolbeaultAlg E (⊤ : Opens X)) :=
  (curvedDolbeaultPresheaf h).𝒜 ⊤

/-- Z3.c: the grading of the curved Dolbeault algebra (that of `dolbeault E X`). Declared
explicitly: instance search does not see `DolbeaultAlg E ⊤` as `(curvedDolbeaultPresheaf h).A ⊤`. -/
instance (h : DolbeaultClosed2 E X) : GradedAlgebra (curvedDolbeault h) :=
  (curvedDolbeaultPresheaf h).graded ⊤

/-- Z3.c: the curved `GCDga` instance (`c = h`), from the curved presheaf. -/
instance (h : DolbeaultClosed2 E X) : GCDga (curvedDolbeault h) :=
  (curvedDolbeaultPresheaf h).dga ⊤

/-- Z3.c: the curvature of the curved Dolbeault algebra is `h` (rfl). -/
theorem curvedDolbeault_c (h : DolbeaultClosed2 E X) :
    GCDga.c (𝒜 := curvedDolbeault h) = h.1 := rfl

/-- Z3.c: the differential of the curved Dolbeault algebra is `∂̄` (rfl). -/
theorem curvedDolbeault_d (h : DolbeaultClosed2 E X) :
    GCDga.d (𝒜 := curvedDolbeault h) = GCDga.d (𝒜 := dolbeault E X) := rfl

/-- Z3.c (P15): at `h = 0` the curved instance is the frozen Dolbeault instance (rfl). -/
theorem curvedDolbeault_zero_inst (U : Opens X) :
    (curvedDolbeaultPresheaf (0 : DolbeaultClosed2 E X)).dga U =
      (dolbeaultPresheaf E X).dga U := rfl

/-- Z3.c (P15): at `h = 0`, `Ho(P_{curvedDolbeault 0})` is `Ho(P_A)` of the main statement (rfl). -/
theorem hoP_curvedDolbeault_zero :
    HoP (curvedDolbeault (0 : DolbeaultClosed2 E X)) = HoP (dolbeault E X) := rfl

end Cohesive
