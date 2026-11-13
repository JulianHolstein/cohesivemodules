-- FROZEN (23 Oct 2026; S4/S5.a/S9 vocabulary, enters Perf). Do not edit without approval.
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Topology.Sheaves.Sheaf

set_option linter.style.header false

/-!
# Sheaves of modules on a space: abbreviations

Shared vocabulary of layer S (blueprint §3; conventions §7, §8). Every Mathlib constant with a
free module universe is used through an abbreviation fixing it to `0` (conventions §7,
"Abbreviation rule").

* `RingSheaf X`: sheaves of rings on `Opens X` with the standard topology.
* `Mod R = SheafOfModules.{0} R`.
* `restr R U = SheafOfModules.overFunctor.{0} R U`, restriction `M ↦ M|U` to an open `U`, with
  values in modules over `R.over U` on the over-site `Over U` (decided in P3).
* `globalSections R`: `Γ(X, -)`, evaluation at `⊤`, with values in `R(X)`-modules.
* `IsFinFreeSummand M`: `M` is a direct summand of a finite free module (S9.a, S4).
* `IsLocallyFinFreeSummand M`: every point has an open neighbourhood `U` with `M|U` a direct
  summand of a finite free `R.over U`-module (S4.b).

This file enters the main statement through the definition of perfect complexes (S9), so it is
frozen (23 Oct 2026, by the human's rule: everything the main statement depends on is frozen).
-/

universe u v

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

/-- Sheaves of rings on `Opens X` with the standard Grothendieck topology (blueprint §3,
conventions §7). Values in `RingCat.{0}`, as `SheafOfModules` needs; sheaves of commutative
rings are converted with `forget₂`. -/
abbrev RingSheaf (X : Type) [TopologicalSpace X] :=
  Sheaf (Opens.grothendieckTopology X) RingCat.{0}

/-- Sheaves of modules over a sheaf of rings `R` on any site, with the module universe fixed to
`0` (conventions §7). -/
abbrev Mod {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{0}) :=
  SheafOfModules.{0} R

variable {X : Type} [TopologicalSpace X]

/-- **S5.a.** Restriction `M ↦ M|U` to an open `U` (conventions §7, decided in P3): Mathlib's
`SheafOfModules.overFunctor` with the module universe fixed to `0`. The result is a sheaf of
modules over `R.over U` on the over-site `Over U`. -/
abbrev restr (R : RingSheaf X) (U : Opens X) : Mod R ⥤ Mod (R.over U) :=
  SheafOfModules.overFunctor.{0} R U

instance (R : RingSheaf X) (U : Opens X) : (restr R U).Additive where
  map_add := rfl

/-- Global sections `Γ(X, -)`: evaluation at the top open, with values in modules over the ring
`R(X)` of global sections of `R` (blueprint S2–S4). -/
abbrev globalSections (R : RingSheaf X) : Mod R ⥤ ModuleCat.{0} (R.obj.obj (op ⊤)) :=
  SheafOfModules.evaluation.{0} R (op ⊤)

instance (R : RingSheaf X) : (globalSections R).Additive where
  map_add := rfl

/-- **S9.a, S4.** `M` is a direct summand of a finite free module: there are `m` and maps
`i : M ⟶ Rᵐ`, `p : Rᵐ ⟶ M` with `i ≫ p = 𝟙 M` (Mathlib's `SheafOfModules.free (Fin m)` is the
coproduct of `m` copies of `R`). [A, Def 7.2.11] -/
def IsFinFreeSummand {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {R : Sheaf J RingCat.{0}} (M : Mod R) : Prop :=
  ∃ (m : ℕ) (i : M ⟶ SheafOfModules.free (Fin m)) (p : SheafOfModules.free (Fin m) ⟶ M),
    i ≫ p = 𝟙 M

/-- **S4.b.** `M` is locally a direct summand of a finite free module: every point `x` has an
open neighbourhood `U` such that `M|U` is a direct summand of a finite free `R.over U`-module.
This is "locally finitely generated and locally projective" of blueprint S4.b ([A, Lemma
7.2.15]) in the form in which it is produced (S10) and used. -/
def IsLocallyFinFreeSummand {R : RingSheaf X} (M : Mod R) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsFinFreeSummand ((restr R U).obj M)

end Cohesive
