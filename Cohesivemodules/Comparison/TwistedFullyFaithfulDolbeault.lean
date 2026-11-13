import Cohesivemodules.Comparison.TwistedFullyFaithful
import Cohesivemodules.Comparison.TwistedPerfect

set_option linter.style.header false

/-!
# Z3.s: C4^tw for the Dolbeault data

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F, F′ (k); [A, Prop 7.2.19]). For a compact
Hausdorff complex manifold `X`, a `∂̄`-closed `h ∈ 𝒜^{0,2}(X)` and a twist datum `T` for `h`, the
twisted functor `J_T : Ho(P_{(𝒜(X), h)}) ⥤ D(X, ȟ)` is fully faithful:
* `llOpen_dolbeault`: LL over opens for the Dolbeault resolving data (Z3.e, `localGaugeLemmaOpen`);
* `full_twistedJ_dolbeault`, `faithful_twistedJ_dolbeault`: C4^tw (`full_twistedJ`,
  `faithful_twistedJ`) for the Dolbeault resolving data built from H1 and H2 (phases 6–7).

## Deviations
* As C4: `X` compact Hausdorff. H1 and H2 are the theorems `dolbeaultGrothendieck`,
  `localGaugeLemma`, not hypotheses.
-/

noncomputable section

universe w

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  [T2Space X] [CompactSpace X]

/-- **Z3.s.** LL over opens (`LLOpen`) for the Dolbeault resolving data: Z3.e's
`localGaugeLemmaOpen`. -/
theorem llOpen_dolbeault :
    LLOpen (dolbeaultData E X (dolbeaultGrothendieck E X) (localGaugeLemma E X)) :=
  fun _ N _ hx => localGaugeLemmaOpen E N hx

variable {E X}

/-- **Z3.s (C4^tw, Dolbeault).** [A, Prop 7.2.19 (full faithfulness)]. For a `∂̄`-closed
`h ∈ 𝒜^{0,2}(X)` and a twist datum `T` for `h`, `J_T` is full. -/
theorem full_twistedJ_dolbeault (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    [HasDerivedCategory.{w} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)] :
    (T.twistedJ h.2.1 h.2.2).Full := by
  have key := @full_twistedJ.{w} X _ _ _
    (dolbeaultData E X (dolbeaultGrothendieck E X) (localGaugeLemma E X)) _ T h.2.1 h.2.2
    (llOpen_dolbeault E X)
    ‹HasDerivedCategory.{w} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)›
  exact key

/-- **Z3.s (C4^tw, Dolbeault).** [A, Prop 7.2.19 (full faithfulness)]. For a `∂̄`-closed
`h ∈ 𝒜^{0,2}(X)` and a twist datum `T` for `h`, `J_T` is faithful. -/
theorem faithful_twistedJ_dolbeault (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    [HasDerivedCategory.{w} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)] :
    (T.twistedJ h.2.1 h.2.2).Faithful := by
  have key := @faithful_twistedJ.{w} X _ _ _
    (dolbeaultData E X (dolbeaultGrothendieck E X) (localGaugeLemma E X)) _ T h.2.1 h.2.2
    (llOpen_dolbeault E X)
    ‹HasDerivedCategory.{w} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)›
  exact key

end Cohesive
