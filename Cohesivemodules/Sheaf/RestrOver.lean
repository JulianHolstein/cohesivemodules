import Cohesivemodules.Sheaf.RestrOverDef
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

set_option linter.style.header false

/-!
# Z3.f: API of the restriction between over-sites

Blueprint item Z3.f (`blueprint/blueprint-tw.md` §3 C.2, C.4–C.5; prototype P17).
* `restrOverAdj : restrOver R h ⊣ overPullback` (Mathlib's `overMapPushforwardAdj`);
* `restrOver` is additive and has a left adjoint (extension by zero), so it is exact;
* `restr_restrOver : restr R U ⋙ restrOver R h ≅ restr R V` (Mathlib's `overFunctorMap`);
* the right adjoint `overPullback` preserves injective objects.

## Lean notes
The left adjoint is passed explicitly, as for `restr_isRightAdjoint` (P3): instance search does
not find the presheaf pullback along `Over.map`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace

variable {X : Type} [TopologicalSpace X] (R : RingSheaf X)

/-- **Z3.f.** [Stacks 03DH]. Restriction between over-sites is left adjoint to Mathlib's
`SheafOfModules.overPullback` (pushforward along `Over.map`). -/
def restrOverAdj {U V : Opens X} (h : V ≤ U) :
    restrOver R h ⊣ SheafOfModules.overPullback.{0} R (homOfLE h) :=
  SheafOfModules.overMapPushforwardAdj R (homOfLE h)

/-- **Z3.f.** Restricting to `U` and then to `V ≤ U` is restricting to `V` (Mathlib's
`SheafOfModules.overFunctorMap`). -/
def restr_restrOver {U V : Opens X} (h : V ≤ U) : restr R U ⋙ restrOver R h ≅ restr R V :=
  SheafOfModules.overFunctorMap R (homOfLE h)

/-- Z3.f: restriction between over-sites has a left adjoint (extension by zero), passed
explicitly as in `restr_isRightAdjoint` (P3, P17). -/
instance restrOver_isRightAdjoint {U V : Opens X} (h : V ≤ U) : (restrOver R h).IsRightAdjoint :=
  @SheafOfModules.instIsRightAdjointPushforward _ _ _ _ _ _ _ _ _ _
    (Sheaf.pushforwardOverMapIso R (homOfLE h)).inv
    (PresheafOfModules.instIsRightAdjointPushforward (F := Over.map (homOfLE h))
      (R := (R.over U).obj) (S := (R.over V).obj) _) _ _

/-- Z3.f: restriction between over-sites preserves finite limits (right adjoint). -/
instance restrOver_preservesFiniteLimits {U V : Opens X} (h : V ≤ U) :
    PreservesFiniteLimits (restrOver R h) := inferInstance

/-- Z3.f: restriction between over-sites preserves colimits (left adjoint). -/
instance restrOver_preservesColimits {U V : Opens X} (h : V ≤ U) :
    PreservesColimitsOfSize.{0, 0} (restrOver R h) :=
  (restrOverAdj R h).leftAdjoint_preservesColimits

/-- **Z3.f.** blueprint-tw C.4–C.5. The right adjoint `overPullback` of `restrOver` preserves
injective objects (its left adjoint `restrOver` is exact). -/
instance overPullback_preservesInjectiveObjects {U V : Opens X} (h : V ≤ U) :
    (SheafOfModules.overPullback.{0} R (homOfLE h)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (restrOverAdj R h)

end Cohesive
