import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option linter.style.header false

/-!
# Z4.a: the Cauchy kernel is locally integrable

Blueprint item Z4.a (§11, v1.14). The kernel `t ↦ t⁻¹` of the Cauchy transform is locally
integrable on `ℂ` for Lebesgue measure: `‖t⁻¹‖ = ‖t‖^(-1)` and `1 < 2 = dim_ℝ ℂ`
(Mathlib's `locallyIntegrable_of_norm_le_rpow`).

## Deviations
* Replaces TauCeti's `Complex.locallyIntegrable_inv` (`TauCeti/Analysis/Complex/CauchyKernel.lean`),
  which is not a dependency of this project; same statement, proof from Mathlib alone.
-/

namespace Cohesive

open MeasureTheory

/-- **Z4.a.** [Hörmander, Thm 1.2.2]. The Cauchy kernel `t ↦ t⁻¹` is locally integrable on `ℂ`
(Lebesgue measure). -/
theorem locallyIntegrable_inv_complex : LocallyIntegrable (fun t : ℂ => t⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (μ := volume) (by simp [Complex.finrank_real_complex])
    (C := 1) (α := 1) (by simp [Complex.finrank_real_complex]) (ae_of_all _ fun z => ?_)
    (measurable_inv.aestronglyMeasurable)
  rw [norm_inv, one_mul, Real.rpow_neg_one]

end Cohesive
