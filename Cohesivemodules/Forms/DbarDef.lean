-- FROZEN (gate 3, 26 Oct 2026; F3 definitions, in the main statement). Do not edit without approval.
import Cohesivemodules.Forms.FibreDef
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option linter.style.header false

/-!
# F3: the operator `∂̄` on open subsets of `E` (definitions)

Blueprint item F3 (conventions §6; prototype `Scratch/P2_Fibres.lean`, Parts B–D).
This file holds the definitions of F3 that the main statement depends on, with their basic API
and the declarations their constructions need; it will be frozen at gate 3. The results (F3.b,
F3.c, F4) are in `Cohesivemodules/Forms/Dbar.lean`.

Definitions: `antiPart`, `dbarPart`, `dbar`.

## Deviations
* ∂̄ is defined on all functions `E → Λ^{0,q}(E; F)` (not only on open subsets); locality
  (`dbar_congr`) makes it depend only on the germ, which gives ∂̄ on open subsets.
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap Complex ComplexConjugate Conj Filter Topology
open scoped ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-! ## The antilinear part (F3.a) -/

/-- An `ℝ`-linear map applied to `c • v`, `c ∈ ℂ`. -/
theorem realLinear_complex_smul (L : E →L[ℝ] G) (c : ℂ) (v : E) :
    L (c • v) = (c.re : ℂ) • L v + (c.im : ℂ) • L (I • v) := by
  conv_lhs => rw [← re_add_im c]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul, map_add, map_smul, map_smul,
    Complex.coe_smul, Complex.coe_smul]

/-- **F3.a.** The antilinear part `L″ v = ½ (L v + i·L (i v))` of an `ℝ`-linear map `L : E → G`,
as a `ℂ`-linear map on `Ē` (conventions §6). -/
def antiPart (L : E →L[ℝ] G) : Conj E →L[ℂ] G where
  toFun v := (2 : ℂ)⁻¹ • (L (ofConj v) + I • L (I • ofConj v))
  map_add' v w := by
    simp only [ofConj_add, map_add, smul_add]
    abel
  map_smul' c v := by
    simp only [ofConj_smul, RingHom.id_apply]
    rw [smul_smul I (conj c), realLinear_complex_smul L (conj c),
      realLinear_complex_smul L (I * conj c)]
    simp only [conj_re, conj_im, mul_re, mul_im, I_re, I_im, zero_mul, one_mul, zero_sub,
      zero_add, neg_neg, ofReal_neg]
    conv_rhs => rw [← re_add_im c]
    match_scalars <;> ring_nf; simp [I_sq]; ring
  cont := by
    have h1 : Continuous fun v : Conj E => L (ofConj v) := L.continuous.comp continuous_id
    have h2 : Continuous fun v : Conj E => L (I • ofConj v) :=
      L.continuous.comp (continuous_const_smul (I : ℂ) |>.comp continuous_id)
    exact (h1.add (h2.const_smul I)).const_smul _

/-- F3.a: formula for `antiPart`. -/
@[simp] theorem antiPart_apply (L : E →L[ℝ] G) (v : Conj E) :
    antiPart L v = (2 : ℂ)⁻¹ • (L (ofConj v) + I • L (I • ofConj v)) := rfl

/-! ## `D″` and `∂̄` (F3) -/

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {q : ℕ}

/-- **F3.** `D″α(x)`, the antilinear part of the real derivative of `α : E → Λ^{0,q}(E; F)`, as a
`ℂ`-linear map `Ē → Λ^{0,q}(E; F)` (conventions §6). Junk (`0`) where `α` is not
differentiable. -/
def dbarPart (α : E → DolbeaultFibre E q F) (x : E) :
    Conj E →L[ℂ] DolbeaultFibre E q F := antiPart (fderiv ℝ α x)

/-- **F3.** `∂̄α(x) = alternatizeUncurryFin (D″α(x))` over `ℂ` on `Ē`:
`∂̄α(x; v₀, …, v_q) = Σ_i (-1)^i D″_{v_i} α(x; …, v̂_i, …)`, Mathlib's `extDeriv` normalization
(conventions §6). [B, §4.1], [A, §7.1]. Junk where `α` is not differentiable. -/
def dbar (α : E → DolbeaultFibre E q F) (x : E) : DolbeaultFibre E (q + 1) F :=
  alternatizeUncurryFin (dbarPart α x)

end Cohesive
