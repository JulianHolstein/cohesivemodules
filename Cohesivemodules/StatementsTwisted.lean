-- FROZEN (gate 12, 6 Nov 2026; MainStatementTwisted, the twisted statement). Do not edit.
import Cohesivemodules.TwistedBlockFunctorDef
import Cohesivemodules.Sheaf.Twisted.PerfectDef

set_option linter.style.header false

/-!
# The twisted main statement

Blueprint item Z3.v (`blueprint/blueprint-tw.md` §2.4; blueprint §11 v1.19). P. Antweiler,
arXiv 2411.19595v1, Thm 7.4.3 (the twisted form of J. Block, Thm 4.1.3): for a compact complex
manifold `X` and a `∂̄`-closed `h ∈ 𝒜^{0,2}(X)`, `J_T : Ho(P_{(𝒜_X(X), ∂̄, h)}) ⥤ D(TwMod O_X U ȟ)`
is full and faithful with essential image the twisted perfect complexes.

## Deviations (⚠, blueprint-tw §2.4)
* Stated for every twist datum `T` for `h` (finite cover, normalized `ȟ`, antisymmetric `u`,
  multiplicative `(h⁰, u, ȟ)` instead of [A]'s `(h⁰, h¹, h², exp_ℛ)`); one exists for every `h`
  (`exists_twistData`); independence of `T` is LATER.
* Twisted `O_X`-modules only, no intermediate cdg-module category; left modules,
  `c = h_[A] = −B_[B]`, no `2πi`; the generic gauge assumes `IsUnit (2 : k)`.
* `D_perf` (`TwPerf`) instead of `D^b_coh`; "equivalence onto" as full, faithful, essential image.
* `O_X` is spelled `(dolbeaultPreData E X).toSheafData.O`, equal to `holSheaf E X` by `rfl`
  (`dolbeaultPreData_toSheafData_O`; the cocycle `T.ch` is typed over this spelling).
-/

namespace Cohesive

open CategoryTheory Manifold
open scoped ContDiff

/-- **The twisted main statement** (Z3.v). For every finite-dimensional complex normed space `E`,
every compact Hausdorff complex manifold `X` modelled on `E`, every `∂̄`-closed form
`h ∈ 𝒜^{0,2}(X)` and every twist datum `T` for `h`, the functor
`twistedBlockFunctor h T : Ho(P_A) ⥤ D(TwMod O_X U ȟ)` from the homotopy category of cohesive
modules over the curved Dolbeault algebra `A = (𝒜_X(X), ∂̄, h)` to the derived category of
`ȟ`-twisted sheaves of `O_X`-modules on the cover `U` of `T` is full and faithful, and its
essential image is exactly the twisted perfect complexes `TwPerf`. The derived category is
Mathlib's `HasDerivedCategory.standard`, the same for the functor and `TwPerf`. -/
def MainStatementTwisted : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X] (h : DolbeaultClosed2 E X) (T : TwistData E X h),
      letI := HasDerivedCategory.standard (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)
      (twistedBlockFunctor h T).Full ∧ (twistedBlockFunctor h T).Faithful ∧
        (twistedBlockFunctor h T).essImage = TwPerf (dolbeaultPreData E X).toSheafData.O T.U T.ch

end Cohesive
