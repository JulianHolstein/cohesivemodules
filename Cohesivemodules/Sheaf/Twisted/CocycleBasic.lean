import Cohesivemodules.Sheaf.Twisted.CocycleDef

set_option linter.style.header false

/-!
# Z3.i: identities of twist cocycles

Blueprint item Z3.i (`blueprint/blueprint-tw.md` §3 B.6, C.4′(a)). For a twist cocycle `T`, on
every open `W` contained in the relevant members of the cover:
* normalization: `ȟ_αβγ|W = 1` if two indices coincide;
* the cocycle condition in the form `ȟ_βγδ ȟ_αβδ = ȟ_αγδ ȟ_αβγ`;
* cyclic symmetry `ȟ_βγα = ȟ_αβγ` (cocycle at `(α, β, γ, α)` and normalization).
-/

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  (T : TwistCocycle R)

/-- Z3.i: in a commutative group, `a c⁻¹ b d⁻¹ = 1` gives `a b = c d`. -/
private theorem eq_of_cocycle_form {G : Type*} [CommGroup G] {a b c d : G}
    (h : a * c⁻¹ * b * d⁻¹ = 1) : a * b = c * d := by
  have e : a * c⁻¹ * b * d⁻¹ = (a * b) * (c * d)⁻¹ := by
    rw [mul_inv_rev]; simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [e, mul_inv_eq_one] at h
  exact h

/-- **Z3.i.** Normalization on `W`: `ȟ_αβγ|W = 1` if two of the indices coincide. -/
theorem TwistCocycle.unitRes_normalized {α β γ : T.ι} (hn : α = β ∨ β = γ ∨ α = γ)
    {W : Opens X} (h : W ≤ T.U α ⊓ T.U β ⊓ T.U γ) : unitRes R h (T.ch α β γ) = 1 := by
  rw [T.normalized α β γ hn, map_one]

/-- **Z3.i.** [A, Def 7.1.1]. The cocycle condition on `W`: `ȟ_βγδ ȟ_αβδ = ȟ_αγδ ȟ_αβγ`. -/
theorem TwistCocycle.unitRes_cocycle (α β γ δ : T.ι) {W : Opens X} (hα : W ≤ T.U α)
    (hβ : W ≤ T.U β) (hγ : W ≤ T.U γ) (hδ : W ≤ T.U δ) :
    unitRes R (le_inf (le_inf hβ hγ) hδ) (T.ch β γ δ) *
        unitRes R (le_inf (le_inf hα hβ) hδ) (T.ch α β δ) =
      unitRes R (le_inf (le_inf hα hγ) hδ) (T.ch α γ δ) *
        unitRes R (le_inf (le_inf hα hβ) hγ) (T.ch α β γ) :=
  eq_of_cocycle_form (T.cocycle α β γ δ W hα hβ hγ hδ)

/-- **Z3.i.** blueprint-tw B.6. Cyclic symmetry on `W`: `ȟ_βγα = ȟ_αβγ`. -/
theorem TwistCocycle.unitRes_cyclic (α β γ : T.ι) {W : Opens X} (hα : W ≤ T.U α)
    (hβ : W ≤ T.U β) (hγ : W ≤ T.U γ) :
    unitRes R (le_inf (le_inf hβ hγ) hα) (T.ch β γ α) =
      unitRes R (le_inf (le_inf hα hβ) hγ) (T.ch α β γ) := by
  have h := T.unitRes_cocycle α β γ α hα hβ hγ hα
  rw [T.unitRes_normalized (Or.inr (Or.inr rfl)) (le_inf (le_inf hα hγ) hα),
    T.unitRes_normalized (Or.inr (Or.inr rfl)) (le_inf (le_inf hα hβ) hα), mul_one, one_mul] at h
  exact h

end Cohesive
