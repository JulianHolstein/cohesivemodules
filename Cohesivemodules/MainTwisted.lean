import Cohesivemodules.StatementsTwisted
import Cohesivemodules.Comparison.TwistedFullyFaithfulDolbeault
import Cohesivemodules.Comparison.TwistedEssSurj
import Cohesivemodules.MainH2

set_option linter.style.header false

/-!
# Z3.v: the twisted main theorem

Blueprint item Z3.v (`blueprint/blueprint-tw.md` §3 H.1–H.2), [A, Thm 7.4.3]. For the Dolbeault
resolving data (H1 and H2 proved, phases 6–7):
* `twistedBlockFunctor h T` is full and faithful (Z3.s, `full_twistedJ_dolbeault`,
  `faithful_twistedJ_dolbeault`);
* its essential image is `TwPerf`: `J_T(M)` is twisted perfect (Z3.p,
  `twIsPerfect_twistedSheafOf`), and every twisted perfect object is some `J_T(M)` (Z3.u,
  `exists_twistedJ_obj_iso`);
* `main_theorem_twisted : MainStatementTwisted`.

## Deviations
* Those of `MainStatementTwisted` (blueprint-tw §2.4).
-/

universe w

namespace Cohesive

open CategoryTheory Manifold
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  [T2Space X] [CompactSpace X]

/-- **Z3.v (H.2).** [A, Thm 7.4.3]. The essential image of `twistedBlockFunctor h T` is the
class of twisted perfect complexes. -/
theorem essImage_twistedBlockFunctor (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    [hD : HasDerivedCategory.{w} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)] :
    (twistedBlockFunctor h T).essImage = TwPerf (dolbeaultPreData E X).toSheafData.O T.U T.ch := by
  funext K
  apply propext
  constructor
  · rintro ⟨M, ⟨i⟩⟩
    exact ⟨_, twIsPerfect_twistedSheafOf h T M.as, ⟨i.symm⟩⟩
  · intro hK
    exact @exists_twistedJ_obj_iso.{w} X _ _ (dolbeaultData E X (dolbeaultGrothendieck E X)
      (localGaugeLemma E X)) _ T h.2.1 h.2.2 hD K hK

/-- **Z3.v. The twisted main theorem.** [A, Thm 7.4.3], blueprint-tw H.2. For every compact
Hausdorff complex manifold `X`, every `∂̄`-closed `h ∈ 𝒜^{0,2}(X)` and every twist datum `T` for
`h`, `J_T : Ho(P_{(𝒜_X(X), ∂̄, h)}) ⥤ D(TwMod O_X U ȟ)` is full and faithful with essential image
`TwPerf`. -/
theorem main_theorem_twisted : MainStatementTwisted := by
  intro E _ _ _ X _ _ _ _ _ h T
  let _ := HasDerivedCategory.standard (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)
  exact ⟨full_twistedJ_dolbeault h T, faithful_twistedJ_dolbeault h T,
    essImage_twistedBlockFunctor h T⟩

end Cohesive
