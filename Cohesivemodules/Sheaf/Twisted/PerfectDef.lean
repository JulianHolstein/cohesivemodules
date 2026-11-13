-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Sheaf.PerfectDef
import Cohesivemodules.Sheaf.RestrOverDef
import Cohesivemodules.Sheaf.Twisted.Abelian

set_option linter.style.header false

/-!
# Z3.j: twisted perfect complexes, `D_perf(X, ȟ)`

Blueprint item Z3.j (`blueprint/blueprint-tw.md` §2.3, §3 C.6; decision D12). Definitions only:
they enter the twisted main statement (`TwPerf`) and are freeze candidates (gate G2/G5). Theorems
(invariance under quasi-isomorphism, twisted S9.d) are in `Sheaf/Twisted/PerfectOver.lean` and
`Sheaf/Twisted/Perfect.lean`.

* `IsPerfectOver K`: S9.b on the over-site `Over V`: every point `x ∈ V` has an open
  neighbourhood `W ≤ V` with a roof of quasi-isomorphisms `K|W ← L → P`, `P` strictly perfect
  (restriction `restrOver R (W ≤ V)` applied termwise).
* `TwIsPerfect K`: a complex of twisted sheaves is perfect if each component complex `K_α` on
  `Over U_α` is (D12).
* `TwPerf R U ch`: the objects of `D(X, ȟ) = DerivedCategory (TwMod R U ch)` isomorphic to `Q K`
  for a twisted perfect complex `K`.

## Deviations
* As in S9.b, a roof of quasi-isomorphisms instead of an isomorphism in `D(R|W)` (equivalent).
* `TwIsPerfect` is componentwise ([A, Def 7.2.11] for twisted complexes, [Căldăraru, §2]): each
  `K_α` is a complex of untwisted sheaves on `U_α`, so the untwisted notion applies to it.
-/

universe w

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- **Z3.j. Perfect complexes on an over-site.** [A, Def 7.2.11], [TT, §2]. A cochain complex `K`
of sheaves of `R.over V`-modules (sheaves on the open `V`) is perfect if every point `x ∈ V` has an
open neighbourhood `W ≤ V` with complexes `L`, `P` of `R.over W`-modules, `P` strictly perfect,
and quasi-isomorphisms `K|W ← L → P` (restriction `restrOver R hW` applied termwise). This is S9.b
(`IsPerfect`) with `restrOver` in place of `restr`; for `V = ⊤` and `K = K'|⊤` it is equivalent to
`IsPerfect K'` (`isPerfectOver_restr_top_iff`). ⚠ Roof of quasi-isomorphisms instead of an
isomorphism in `D(R|W)`; equivalent. -/
def IsPerfectOver {R : RingSheaf X} {V : Opens X} (K : CochainComplex (Mod (R.over V)) ℤ) :
    Prop :=
  ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧
    ∃ (L P : CochainComplex (Mod (R.over W)) ℤ)
      (f : L ⟶ ((restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) (g : L ⟶ P),
      QuasiIso f ∧ QuasiIso g ∧ IsStrictlyPerfect P

variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} {ι : Type}
  {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- **Z3.j. Twisted perfect complexes.** [A, Def 7.2.11], [Căldăraru, §2], blueprint-tw D12. A
cochain complex `K` of `ȟ`-twisted sheaves is perfect if, for every `α`, its component complex
`K_α = comp_α(K)` (a complex of sheaves of `O|U_α`-modules on `Over U_α`) is perfect
(`IsPerfectOver`). ⚠ Componentwise definition; the gluing maps play no role. -/
def TwIsPerfect (K : CochainComplex (TwMod R U ch) ℤ) : Prop :=
  ∀ α : ι,
    IsPerfectOver (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

variable (R U ch) in
/-- **Z3.j. `D_perf(X, ȟ)`.** The full subcategory (as an `ObjectProperty`) of the derived
category `D(X, ȟ) = DerivedCategory (TwMod R U ch)` on the objects isomorphic to `Q K` for some
twisted perfect complex `K`; the twisted analogue of `Perf` (S9.c). Closed under isomorphism by
construction. The derived category is taken with respect to the abelian structure of Z3.h. -/
def TwPerf [HasDerivedCategory.{w} (TwMod R U ch)] :
    ObjectProperty (DerivedCategory (TwMod R U ch)) :=
  fun D ↦ ∃ K : CochainComplex (TwMod R U ch) ℤ, TwIsPerfect K ∧
    Nonempty (D ≅ DerivedCategory.Q.obj K)

end Cohesive
