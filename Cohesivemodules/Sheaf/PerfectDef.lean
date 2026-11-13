-- FROZEN (23 Oct 2026; S9.a–c, in the main statement). Do not edit without approval.
import Cohesivemodules.Sheaf.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex

set_option linter.style.header false

/-!
# S9: strictly perfect and perfect complexes, `D_perf`

Blueprint item S9.a–S9.c (§3; conventions §8). Definitions only, with their docstrings: this
file enters the main statement (`Perf`) and is frozen (23 Oct 2026) together with
`Sheaf/Basic.lean`. Theorems about these notions (S9.c invariance, S9.d) are in
`Sheaf/Perfect.lean`, S10 in `Sheaf/Globalize.lean`.

* `IsStrictlyPerfect P`: `P` is bounded (strictly zero outside `[a, b]`) and each term is a
  direct summand of a finite free module. Any site, so that it applies on over-sites `Over U`.
* `IsPerfect K`: every point `x` has an open neighbourhood `U` with a roof of
  quasi-isomorphisms `K|U ← L → P` (complexes of `R.over U`-modules), `P` strictly perfect.
* `Perf R`: the objects of `D(R) = DerivedCategory (Mod R)` isomorphic to `Q K` for a perfect
  complex `K`.

## Deviations
* "Perfect" is defined by a roof of quasi-isomorphisms on each `U`, not by an isomorphism
  `Q(K|U) ≅ Q(P)` in `D(R|U)` (blueprint S9.b): the two are equivalent, and the roof avoids a
  derived category for every open set.
* `Perf` takes the `HasDerivedCategory` instance as an argument (any universe); the project uses
  `HasDerivedCategory.standard` (conventions §7).
-/

universe w

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

/-- **S9.a. Strictly perfect complexes.** A cochain complex `P` of sheaves of `R`-modules is
strictly perfect if it is bounded (there are `a, b` with `Pⁿ = 0` for `n < a` and for `n > b`,
Mathlib's `IsStrictlyGE a`, `IsStrictlyLE b`) and every term `Pⁿ` is a direct summand of a
finite free `R`-module (`IsFinFreeSummand`). [A, Def 7.2.11] Any site. -/
def IsStrictlyPerfect {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {R : Sheaf J RingCat.{0}} (P : CochainComplex (Mod R) ℤ) : Prop :=
  (∃ a b : ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧ ∀ n : ℤ, IsFinFreeSummand (P.X n)

variable {X : Type} [TopologicalSpace X]

/-- **S9.b. Perfect complexes.** A cochain complex `K` of sheaves of `R`-modules on `X` is
perfect if every point `x` has an open neighbourhood `U` with complexes `L`, `P` of
`R.over U`-modules, `P` strictly perfect, and quasi-isomorphisms `K|U ← L → P` (restriction
`restr R U` applied termwise). [A, Def 7.2.11], [TT, §2] ⚠ roof of quasi-isomorphisms instead
of an isomorphism in `D(R|U)`; equivalent. -/
def IsPerfect {R : RingSheaf X} (K : CochainComplex (Mod R) ℤ) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    ∃ (L P : CochainComplex (Mod (R.over U)) ℤ)
      (f : L ⟶ ((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) (g : L ⟶ P),
      QuasiIso f ∧ QuasiIso g ∧ IsStrictlyPerfect P

/-- **S9.c. `D_perf(X, R)`.** The full subcategory (as an `ObjectProperty`) of the derived
category `D(R) = DerivedCategory (Mod R)` on the objects isomorphic to `Q K` for some perfect
complex `K`. Closed under isomorphism by construction. -/
def Perf (R : RingSheaf X) [HasDerivedCategory.{w} (Mod R)] :
    ObjectProperty (DerivedCategory (Mod R)) :=
  fun D ↦ ∃ K : CochainComplex (Mod R) ℤ, IsPerfect K ∧ Nonempty (D ≅ DerivedCategory.Q.obj K)

end Cohesive
