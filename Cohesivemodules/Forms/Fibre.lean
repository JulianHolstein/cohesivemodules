import Cohesivemodules.Forms.FibreDef
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

set_option linter.style.header false

/-!
# F2: the conjugate space and the fibre `Λ^{0,q}(E; F)`

Blueprint item F2 (conventions §6; prototype `Scratch/P2_Fibres.lean`, decision: keep `Conj E`).
The definitions (and their basic API) are in `Cohesivemodules/Forms/FibreDef.lean`.

* `Conj E`: `E` with the conjugate `ℂ`-action `c • v = c̄ • v` and the same norm, a `def` type
  synonym (not an `abbrev`), so that `E`'s own `ℂ`-action never leaks onto it. `ℂ`-linear maps
  on `Conj E` are the antilinear maps on `E`.
* `DolbeaultFibre E q F = Conj E [⋀^Fin q]→L[ℂ] F`, the `(0,q)`-forms at a point with values in
  `F`. On it the `ℝ`-structure found by instance search is `NormedSpace.complexToReal` at instance
  transparency (checked in P2), so `fderiv ℝ` of `DolbeaultFibre`-valued maps is unambiguous.
* F2.a `Λ^{0,0}(E; F) ≅ F`; F2.b the exterior-algebra bridge
  `Φ_q : ⋀^q_ℂ (Ē)^* ≃ Λ^{0,q}(E; ℂ)`, `φ₁ ∧ ⋯ ∧ φ_q ↦ (v ↦ det (φ_i (v_j)))`;
  F2.c vanishing above the dimension, dimension `C(n, q)`, the basis `dz̄_I`.

## Deviations
* ⚠ (blueprint F2) `Λ^{0,q}` is `Conj E [⋀^Fin q]→L[ℂ] F`, not a subtype of `ℝ`-alternating maps
  antilinear in each slot (the same maps).
* F2.c: the dimension formula and the basis are stated for `F = ℂ` (the only case on the
  critical path); vanishing for `q > n` for every `F`.
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap ComplexConjugate

open Conj

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ## F2.b: the exterior-algebra bridge -/

section Bridge

variable [FiniteDimensional ℂ E]

/-- F2.b: `Φ_q (φ₁ ∧ ⋯ ∧ φ_q) (v₁, …, v_q) = det (φ_j (v_i))` (Mathlib's index order; the
determinant of a matrix and of its transpose agree). -/
theorem extToFibre_ιMulti {q : ℕ} (φ : Fin q → Module.Dual ℂ (Conj E)) (v : Fin q → Conj E) :
    extToFibre E q (exteriorPower.ιMulti ℂ q φ) v = (Matrix.of fun i j => φ j (v i)).det := by
  show exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual ℂ (Conj E) q (exteriorPower.ιMulti ℂ q φ)) v = _
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.pairingDual_ιMulti_ιMulti]

/-! ## F2.c: dimension and the basis `dz̄_I` -/

/-- **F2.c.** The basis `dz̄_I` of `Λ^{0,q}(E; ℂ)`, indexed by the `q`-element subsets `I` of
the index set of a basis `b` of `E`: `dz̄_I = Φ_q (dz̄_{i₁} ∧ ⋯ ∧ dz̄_{i_q})` with
`dz̄_i` the dual basis of the basis `b` of `Ē`. -/
def dzbarBasis {ι : Type} [LinearOrder ι] [Fintype ι] (b : Module.Basis ι ℂ E) (q : ℕ) :
    Module.Basis (Set.powersetCard ι q) ℂ (DolbeaultFibre E q ℂ) :=
  ((Conj.basis b).dualBasis.exteriorPower q).map (extEquivFibre E q)

/-- **F2.c.** `dim_ℂ Λ^{0,q}(E; ℂ) = C(n, q)`, `n = dim_ℂ E`. -/
theorem finrank_dolbeaultFibre (q : ℕ) :
    Module.finrank ℂ (DolbeaultFibre E q ℂ) = (Module.finrank ℂ E).choose q := by
  rw [← (extEquivFibre E q).finrank_eq, exteriorPower.finrank_eq, Subspace.dual_finrank_eq,
    Conj.finrank_eq]

end Bridge

end Cohesive
