-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Algebra.Dga

set_option linter.style.header false

/-!
# Z3.a: changing the curvature of a gc dga

Blueprint item Z3.a (`blueprint/blueprint-tw.md` §2.1; blueprint §11 v1.19, decision D1). The same
bounded graded-commutative dga with a different closed curvature `c'` of degree `2`:
`GCDga.withC i c' hc hd`, the structure update of the fields `c`, `c_mem`, `d_c`. All other
fields, hence `d`, `N`, `A⁰ = commRing0` and everything built from them (`Tot`, `Hom`, `δ`), agree
with those of `i` by `rfl`.

## Lean notes
* `@[reducible]` (prototype P15): with the default transparency, instance checks of the form
  `i =?= withC i …` on modules over `𝒜 0` fail.
* Never an instance. Two instances on the same term `𝒜` (the gauge, Z3.b) are handled with
  explicit projections; at the Dolbeault level the curved algebra is a different term (Z3.c).
-/

namespace Cohesive

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- **Z3.a.** [A, Rem 4.0.4], [B, §2.7]. The gc dga `i` with its curvature replaced by `c'`, a
closed element of degree `2`. A `def`, never an instance; reducible (P15). -/
@[reducible] def GCDga.withC (i : GCDga 𝒜) (c' : A) (hc : c' ∈ 𝒜 2) (hd : i.d c' = 0) :
    GCDga 𝒜 :=
  { i with c := c', c_mem := hc, d_c := hd }

variable (i : GCDga 𝒜) (c' : A) (hc : c' ∈ 𝒜 2) (hd : i.d c' = 0)

/-- Z3.a: the differential is unchanged (rfl). -/
theorem GCDga.withC_d : (i.withC c' hc hd).d = i.d := rfl

/-- Z3.a: the curvature of `withC i c'` is `c'` (rfl). -/
theorem GCDga.withC_c : (i.withC c' hc hd).c = c' := rfl

/-- Z3.a: the top degree is unchanged (rfl). -/
theorem GCDga.withC_N : (i.withC c' hc hd).N = i.N := rfl

/-- Z3.a: the ring `A⁰` is unchanged (rfl). -/
theorem GCDga.withC_commRing0 :
    @GCDga.commRing0 k _ A _ _ 𝒜 _ (i.withC c' hc hd) = @GCDga.commRing0 k _ A _ _ 𝒜 _ i := rfl

/-- Z3.a: replacing the curvature by itself gives back `i` (rfl, structure eta). -/
theorem GCDga.withC_self : i.withC i.c i.c_mem i.d_c = i := rfl

end Cohesive
