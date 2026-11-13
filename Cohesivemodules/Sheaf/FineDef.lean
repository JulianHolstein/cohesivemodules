-- FROZEN (gate 4, 29 Oct 2026; S1 fine sheaves of rings, in the main statement). Do not edit.
import Cohesivemodules.Sheaf.Basic

set_option linter.style.header false

/-!
# S1: fine sheaves of rings (definitions)

Blueprint item S1 (§3). Moved verbatim from `Sheaf/Fine.lean` (phase 4, no change): `IsFine`
enters the C0 structure (`PreResolvingData.isFine0`), so it lives in a definitions-only file, to
be frozen at gate 4. Theorems (S1.a, S2) stay in `Sheaf/Fine.lean`; see its module docstring for
the stalk-free notion of support and the deviations (⚠ finite covers only).

* `rres R h`, `mres M h`: restriction of sections of a sheaf of rings / of modules.
* `IsComm R`: all rings of sections are commutative.
* `SupportedIn ρ U`, `IsFine R` (S1).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- Restriction of sections of the sheaf of rings `R` along `V ≤ U`, as a ring map. -/
abbrev rres (R : RingSheaf X) {U V : Opens X} (h : V ≤ U) :
    R.obj.obj (op U) →+* R.obj.obj (op V) :=
  (R.obj.map (homOfLE h).op).hom

/-- Restriction of sections of the sheaf of modules `M` along `V ≤ U`. -/
abbrev mres {R : RingSheaf X} (M : Mod R) {U V : Opens X} (h : V ≤ U)
    (t : M.val.obj (op U)) : M.val.obj (op V) :=
  (M.val.map (homOfLE h).op).hom t

/-- `R` is a sheaf of commutative rings: all rings of sections are commutative (blueprint §3).
Sheaves of `CommRingCat` composed with `forget₂` satisfy it by `mul_comm`. -/
def IsComm (R : RingSheaf X) : Prop :=
  ∀ (U : Opens X) (a b : R.obj.obj (op U)), a * b = b * a

/-- **S1.** `ρ ∈ R(X)` is supported in the open `U`: there is an open `V` with `U ∪ V = X` and
`ρ|V = 0`. Equivalent to `supp ρ ⊆ U` for the support `supp ρ` (the closed set of points where
the germ of `ρ` is nonzero); see the module docstring. -/
def SupportedIn {R : RingSheaf X} (ρ : R.obj.obj (op ⊤)) (U : Opens X) : Prop :=
  ∃ V : Opens X, U ⊔ V = ⊤ ∧ rres R (le_top : V ≤ ⊤) ρ = 0

/-- **S1. Fine sheaves of rings.** For every finite open cover `(U i)` of `X` there are global
sections `ρ i` with `∑ ρ i = 1` and `supp ρ i ⊆ U i` (`SupportedIn`).
⚠ Finite covers only (blueprint S1, §9 deviation 2); this is the usual notion when `X` is
compact. ✗ in Mathlib. -/
def IsFine (R : RingSheaf X) : Prop :=
  ∀ (ι : Type) [Fintype ι] (U : ι → Opens X), (⨆ i, U i) = ⊤ →
    ∃ ρ : ι → R.obj.obj (op ⊤), ∑ i, ρ i = 1 ∧ ∀ i, SupportedIn (ρ i) (U i)

end Cohesive
