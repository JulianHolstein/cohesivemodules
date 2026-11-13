-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Comparison.TwistedFunctorDef
import Cohesivemodules.Sheaf.Twisted.Abelian

set_option linter.style.header false

/-!
# The functor of the twisted main theorem

Blueprint item Z3.v (`blueprint/blueprint-tw.md` §2.4, §3 H.2), [A, Def 7.2.3, Thm 7.4.3]. For a
compact complex manifold `X`, a `∂̄`-closed `h ∈ 𝒜^{0,2}(X)` and a twist datum `T` for `h`
(`TwistData E X h`), `twistedBlockFunctor h T : Ho(P_{(𝒜_X(X), ∂̄, h)}) ⥤ D(TwMod O_X U ȟ)` is the
functor `J_T` (Z3.n) of the Dolbeault data: `M ↦` the complex of `ȟ`-twisted sheaves with
components `(𝒜_X ⊗ M)|U_α`, differential `𝕏 − h⁰_α` and gluing `u_αβ·`.

The ring sheaf is spelled `(dolbeaultPreData E X).toSheafData.O`, which is `holSheaf E X` (`O_X`)
by `rfl` (`dolbeaultPreData_toSheafData_O`): the cocycle `T.ch` is typed over that spelling, and
instance search for `Category (TwMod R T.U T.ch)` needs `R` to match it syntactically.

## Deviations (⚠, blueprint-tw §2.4)
* The functor depends on a twist datum `T` (finite cover, normalized `ȟ`, antisymmetric `u`,
  multiplicative `(h⁰, u, ȟ)` instead of [A]'s `(h⁰, h¹, h², exp_ℛ)`); independence of `T` is
  LATER. Twisted `O_X`-modules only (no intermediate cdg-module category); left modules,
  `c = h_[A] = −B_[B]`, no `2πi`.
-/

universe w

namespace Cohesive

open CategoryTheory Manifold
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  [T2Space X] [CompactSpace X]

variable (E X) in
/-- Z3.v: the ring sheaf of the Dolbeault data is `O_X` (rfl). -/
theorem dolbeaultPreData_toSheafData_O : (dolbeaultPreData E X).toSheafData.O = holSheaf E X :=
  rfl

/-- **Z3.v. The functor of the twisted main theorem.** [A, Def 7.2.3, Thm 7.4.3], [B, §4.2].
For a `∂̄`-closed `h ∈ 𝒜^{0,2}(X)` and a twist datum `T` for `h`,
`J_T : Ho(P_A) ⥤ D(TwMod O_X U ȟ)` for the curved Dolbeault algebra `A = (𝒜_X(X), ∂̄, h)`
(Z3.n `twistedJ` of the Dolbeault data; `O_X` spelled `(dolbeaultPreData E X).toSheafData.O`).
⚠ Depends on `T` (blueprint-tw §2.4). -/
noncomputable def twistedBlockFunctor (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    [hD : HasDerivedCategory.{w} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)] :
    HoP (curvedDolbeault h) ⥤
      DerivedCategory (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch) :=
  T.twistedJ h.2.1 h.2.2

/-- Z3.v: `twistedBlockFunctor` is `twistedJ` of the Dolbeault data (rfl). -/
theorem twistedBlockFunctor_eq (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    [hD : HasDerivedCategory.{w} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)] :
    twistedBlockFunctor h T = T.twistedJ h.2.1 h.2.2 := rfl

end Cohesive
