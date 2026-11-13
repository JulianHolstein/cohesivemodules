-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Sheaf.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

set_option linter.style.header false

/-!
# Z3.f: restriction between over-sites

Blueprint item Z3.f (`blueprint/blueprint-tw.md` §2.3; blueprint §11 v1.19, prototype P17). For a
sheaf of rings `R` on `X` and opens `V ≤ U`, restriction of sheaves of modules from the over-site
`Over U` to `Over V`: Mathlib's `SheafOfModules.overMap` along `V ⟶ U`, with the module universe
fixed to `0` (conventions §7). The twisted category (Z3.g) and twisted perfectness (Z3.j) are
stated with it; its API (adjoints, exactness, compatibility with `restr`) is in
`Sheaf/RestrOver.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- **Z3.f.** [A, §7.1], [Căldăraru, §1.2]. Restriction `M ↦ M|V` of sheaves of modules on the
over-site `Over U` to the over-site `Over V`, for `V ≤ U`: Mathlib's `SheafOfModules.overMap`
along `homOfLE h`, module universe `0`. For `U = ⊤` and `R.over ⊤` this is `restr R V` up to the
isomorphism `restr_restrOver`. -/
abbrev restrOver (R : RingSheaf X) {U V : Opens X} (h : V ≤ U) :
    Mod (R.over U) ⥤ Mod (R.over V) :=
  SheafOfModules.overMap.{0} R (homOfLE h)

/-- Z3.f: restriction between over-sites is additive (here, not in `RestrOver.lean`, because
twisted perfectness (Z3.j) applies `restrOver` to complexes in its definition). -/
instance restrOver_additive (R : RingSheaf X) {U V : Opens X} (h : V ≤ U) :
    (restrOver R h).Additive where
  map_add := rfl

end Cohesive
