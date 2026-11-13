import Cohesivemodules.Forms.TwistCover
import Cohesivemodules.Forms.TwistFromPrimitives

set_option linter.style.header false

/-!
# Z3.d: every closed `(0,2)`-form has a twist datum

Blueprint item Z3.d (`blueprint/blueprint-tw.md` §3 B.1–B.6; blueprint §11 v1.19, check K8/K14
generalized). `exists_cover_primitives` (B.1–B.3) and `twistData_of_primitives` (B.4–B.6).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **Z3.d.** [A, Def 7.2.2] (multiplicative form, without the Leray hypothesis). On a compact
Hausdorff complex manifold every `∂̄`-closed `h ∈ 𝒜^{0,2}(X)` has a twist datum, so the twisted
main statement (quantified over twist data) is not vacuous. -/
theorem exists_twistData [T2Space X] [CompactSpace X] (h : DolbeaultClosed2 E X) :
    Nonempty (TwistData E X h) := by
  obtain ⟨ι, _, U, hU, h0, h0_mem, d_h0, η, d_η, η_self, η_symm⟩ :=
    exists_cover_primitives E h
  exact twistData_of_primitives E h ι U hU h0 h0_mem d_h0 η d_η η_self η_symm

end Cohesive
