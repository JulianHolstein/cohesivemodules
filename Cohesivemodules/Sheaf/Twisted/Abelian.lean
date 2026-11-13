-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Sheaf.Twisted.Kernels
import Cohesivemodules.Sheaf.Twisted.Cokernels
import Cohesivemodules.Sheaf.Twisted.Biprod
import Cohesivemodules.Sheaf.Twisted.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

set_option linter.style.header false

/-!
# Z3.h: twisted sheaves form an abelian category

Blueprint item Z3.h (`blueprint/blueprint-tw.md` §3 C.2). `TwMod R U ch` is preadditive, has
kernels, cokernels (componentwise, `Kernels.lean`, `Cokernels.lean`) and finite products (zero
object and binary biproducts, `Biprod.lean`). The coimage-image comparison of `f` is an
isomorphism: each component functor preserves kernels and cokernels, so it maps the comparison of
`f` to the comparison of `f.f α` in the abelian category `Mod (R.over U_α)`
(`PreservesCoimageImageComparison.iso`), and a morphism with isomorphic components is an
isomorphism (`TwMod.isIso_of_isIso_f`). Then `Abelian.ofCoimageImageComparisonIsIso`.

## Deviations
[Căldăraru, §1.2] asserts that twisted sheaves form an abelian category; [A, §7.1] uses it.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

namespace TwMod

/-- Z3.h: twisted sheaves have finite products (zero object and binary biproducts). -/
instance : HasFiniteProducts (TwMod R U ch) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- **Z3.h.** The coimage-image comparison of a morphism of twisted sheaves is an isomorphism:
componentwise it is the comparison of `f.f α` in `Mod (R.over U_α)`. -/
theorem isIso_coimageImageComparison {M N : TwMod R U ch} (f : M ⟶ N) :
    IsIso (Abelian.coimageImageComparison f) := by
  have (α : ι) : IsIso ((Abelian.coimageImageComparison f).f α) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Abelian.PreservesCoimageImageComparison.iso (TwMod.comp R U ch α) f)).2
      (inferInstanceAs (IsIso (Abelian.coimageImageComparison (f.f α))))
  exact isIso_of_isIso_f _

/-- **Z3.h.** [Căldăraru, §1.2]. `ȟ`-twisted sheaves of modules form an abelian category. -/
instance : Abelian (TwMod R U ch) :=
  @Abelian.ofCoimageImageComparisonIsIso _ _ _ _ _ (fun f => isIso_coimageImageComparison f) _

end TwMod

end Cohesive
