-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites

set_option linter.style.header false

/-!
# Z3.c: normalized Čech 2-cocycles of units on a finite cover

Blueprint item Z3.c (`blueprint/blueprint-tw.md` §2.2; blueprint §11 v1.19, decisions D2, D3).
For a sheaf of commutative rings `R` on `X`: a finite open cover `U : ι → Opens X` and units
`ch α β γ ∈ R(U_α ∩ U_β ∩ U_γ)ˣ`, normalized and satisfying the Čech cocycle condition. The
twisted category `TwMod` (Z3.g) depends only on this datum. `ȟ` of the sources is written `ch`.

## Deviations
* Finite cover, normalized cocycle ([A, Def 7.1.1] allows arbitrary covers); the cocycle
  condition is stated on every open `W` contained in the four members (equivalent to the
  condition on the quadruple intersection, and avoids rewriting intersections).
-/

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})

/-- Z3.c: restriction of units of `R` along `W' ≤ W`. -/
def unitRes {W W' : Opens X} (h : W' ≤ W) : (R.obj.obj (op W))ˣ →* (R.obj.obj (op W'))ˣ :=
  Units.map (R.obj.map (homOfLE h).op).hom.toMonoidHom

/-- **Z3.c.** [A, Def 7.1.1], [Căldăraru, Def 1.2.1]. A normalized Čech 2-cocycle of units of `R`
on a finite open cover: an index type `ι` (finite), opens `U α` covering `X`, units
`ch α β γ ∈ R(U_α ∩ U_β ∩ U_γ)ˣ` equal to `1` when two indices coincide, with
`ch_βγδ · ch_αγδ⁻¹ · ch_αβδ · ch_αβγ⁻¹ = 1` on every open contained in `U_α, U_β, U_γ, U_δ`. -/
structure TwistCocycle : Type 1 where
  /-- The index type of the cover. -/
  ι : Type
  [fin : Fintype ι]
  /-- The members of the cover. -/
  U : ι → Opens X
  iSup_eq : ⨆ i, U i = ⊤
  /-- The cocycle `ȟ`. -/
  ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ
  normalized : ∀ α β γ, (α = β ∨ β = γ ∨ α = γ) → ch α β γ = 1
  cocycle : ∀ α β γ δ (W : Opens X) (hα : W ≤ U α) (hβ : W ≤ U β) (hγ : W ≤ U γ)
    (hδ : W ≤ U δ),
    unitRes R (le_inf (le_inf hβ hγ) hδ) (ch β γ δ) *
      (unitRes R (le_inf (le_inf hα hγ) hδ) (ch α γ δ))⁻¹ *
      unitRes R (le_inf (le_inf hα hβ) hδ) (ch α β δ) *
      (unitRes R (le_inf (le_inf hα hβ) hγ) (ch α β γ))⁻¹ = 1

attribute [instance] TwistCocycle.fin

end Cohesive
