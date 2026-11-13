import Cohesivemodules.Forms.CurvedRestrictDef
import Cohesivemodules.Forms.LocalGaugeOpen

set_option linter.style.header false

/-!
# Z3.e: the curved local lifting lemma LL^h

Blueprint item Z3.e (`blueprint/blueprint-tw.md` §3 E.1; audit a14, decision D7). [A, §7.4]
attributes the curved local lifting to [Blo09, 4.1.5], which is stated for flat algebras only;
here it is reduced to the flat case: gauge the restriction by `h⁰_α` (`gaugedRestrict`), then apply
H2 over the open `U_α` (`localGaugeLemmaOpen`).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  [T2Space X] [CompactSpace X]

/-- **Z3.e (LL^h).** [A, §7.4], [B, Lemma 4.1.5], blueprint-tw E.1. For a closed `h ∈ 𝒜^{0,2}(X)`,
a twist datum `T` of `h`, an index `α`, a cohesive module `M` over the curved Dolbeault algebra
`(𝒜_X(X), ∂̄, h)` and `x ∈ U_α`, there are an open `U′ ≤ U_α` containing `x`, a bounded complex
`W` of finitely generated projective `O_X(U′)`-modules and an isomorphism in `Ho(P_{𝒜_X(U′)})`
between `gauge_{h⁰_α}(M|U_α)|U′` and `𝒜_X(U′) ⊗_{O(U′)} W` (A10).

Deviation: [A] states this for the curved module `M|U′` itself; here it is stated after the gauge
by `h⁰_α`, which is an equivalence `Ho(P_{(𝒜_X(U_α), h|U_α)}) ≌ Ho(P_{𝒜_X(U_α)})` (Z3.b,
`gaugeHoP`), so the two forms are equivalent. -/
theorem curvedLL (h : DolbeaultClosed2 E X) (T : TwistData E X h) (α : T.ι)
    (M : CohesiveModule (curvedDolbeault h)) {x : X} (hx : x ∈ T.U α) :
    ∃ (U' : Opens X) (hU' : U' ≤ T.U α), x ∈ U' ∧
      ∃ (W : CochainComplex (ModuleCat.{0} ((holSheaf E X).obj.obj (op U'))) ℤ)
        (hW : IsBoundedFGProj ((holSheaf E X).obj.obj (op U')) W),
        Nonempty (HoP.mk ((gaugedRestrict h T α M).baseChange (dolbeaultRes E hU')) ≅
          HoP.mk (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E U') W
            (dbar_dolbeaultRhoU E U') rfl hW)) :=
  localGaugeLemmaOpen E (gaugedRestrict h T α M) hx

end Cohesive
