-- FROZEN (gate 4, 29 Oct 2026; S8 ringOf, in the main statement). Do not edit.
import Cohesivemodules.Sheaf.Basic
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.Whiskering

set_option linter.style.header false

/-!
# `ringOf`: the sheaf of rings of a sheaf of commutative rings

Conventions §7. Moved verbatim from `Sheaf/Flat/Tensor.lean` (phase 4, no change): `ringOf`
enters the main statement (`Perf (ringOf (holSheaf E X))`, blueprint §1 v1.10) and the C0
structure, so it lives in a definitions-only file, to be frozen at gate 4.
-/

noncomputable section

namespace Cohesive

open CategoryTheory

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- The sheaf of rings underlying a sheaf of commutative rings (`forget₂`, conventions §7). -/
abbrev ringOf (R : Sheaf J CommRingCat.{0}) : Sheaf J RingCat.{0} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

end Cohesive
