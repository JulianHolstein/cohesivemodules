import Cohesivemodules.Analysis.CauchySolve

set_option linter.style.header false

/-!
# Z5.b: derivatives of the parametric solver, for any codomain

Blueprint item Z5.b (`blueprint/blueprint-ll.md` §4 C.2, design decision L3; §11 v1.15).
* `pdbar v f z = ½ (Df(z) v + i Df(z)(i v))`: `∂̄` along `v` of a function with values in any
  complex normed space (the F3 normalization; for form-valued `f` it is `dbarPart f z (toConj v)`).
* `iteratedFDeriv_cauchySolve`: all derivatives commute with the solver, for `F` smooth with compact
  support.
* `pdbar_cauchySolve`: `∂̄_v (cauchySolve v F) = F` (Z4.c (iii) restated with `pdbar`).
* `pdbar_cauchySolve_comm`: `∂̄_w (cauchySolve v F) = cauchySolve v (∂̄_w F)` for every `w`.

## Deviations
* Z4.c states these for the derivative and for `∂̄_v` only; here `∂̄_w` for any `w` and all
  orders, as needed by the Neumann-series bounds of Z5.c.
-/

open MeasureTheory Complex Set
open scoped Real ContDiff

namespace Cohesive

variable {E Λ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]

/-- **Z5.b.** `∂̄` along `v` of `f : E → Λ` at `z`: `½ (Df(z) v + i Df(z)(i v))` (F3
normalization, conventions §6). Junk where `f` is not differentiable. -/
noncomputable def pdbar (v : E) (f : E → Λ) (z : E) : Λ :=
  (2 : ℂ)⁻¹ • (fderiv ℝ f z v + I • fderiv ℝ f z (I • v))

/-- Z5.b: `pdbar` is `ℂ`-linear in the function at differentiable points. -/
theorem pdbar_add (v : E) {f g : E → Λ} {z : E} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : pdbar v (f + g) z = pdbar v f z + pdbar v g z := by
  unfold pdbar
  rw [fderiv_add hf hg]
  simp only [add_apply, smul_add]
  abel

/-- Z5.b: `pdbar` commutes with continuous `ℂ`-linear maps. -/
theorem pdbar_comp_clm {Λ' : Type} [NormedAddCommGroup Λ'] [NormedSpace ℂ Λ']
    (L : Λ →L[ℂ] Λ') (v : E) {f : E → Λ} {z : E} (hf : DifferentiableAt ℝ f z) :
    pdbar v (fun y => L (f y)) z = L (pdbar v f z) := by
  unfold pdbar
  have h := ((L.restrictScalars ℝ).hasFDerivAt.comp z hf.hasFDerivAt).fderiv
  have h' : fderiv ℝ (fun y => L (f y)) z = (L.restrictScalars ℝ).comp (fderiv ℝ f z) := h
  rw [h']
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, map_add]

/-- Z5.b: `pdbar` depends only on the germ. -/
theorem pdbar_congr (v : E) {f g : E → Λ} {z : E} (h : f =ᶠ[nhds z] g) :
    pdbar v f z = pdbar v g z := by
  unfold pdbar
  rw [h.fderiv_eq]

variable [FiniteDimensional ℂ E] [CompleteSpace Λ]

omit [FiniteDimensional ℂ E] in
/-- A `ℂ`-homogeneous real-linear isometric equivalence commutes with the solver. -/
private theorem equiv_cauchySolve {Λ' : Type} [NormedAddCommGroup Λ'] [NormedSpace ℂ Λ']
    [CompleteSpace Λ'] (T : Λ ≃ₗᵢ[ℝ] Λ') (hT : ∀ (c : ℂ) (x : Λ), T (c • x) = c • T x)
    {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : Continuous F) (hc : HasCompactSupport F) (z : E) :
    T (cauchySolve v F z) = cauchySolve v (fun y => T (F y)) z := by
  let L : Λ →L[ℂ] Λ' :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := hT
      cont := T.continuous }
  exact map_cauchySolve L hv hF hc z

/-- **Z5.b (C.2).** For `v ≠ 0` and `F` smooth with compact support, every derivative of the
solver is the solver of that derivative of `F`. -/
theorem iteratedFDeriv_cauchySolve {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (m : ℕ) (z : E) :
    iteratedFDeriv ℝ m (cauchySolve v F) z = cauchySolve v (iteratedFDeriv ℝ m F) z := by
  have key : ∀ m : ℕ, iteratedFDeriv ℝ m (cauchySolve v F) =
      cauchySolve v (iteratedFDeriv ℝ m F) := by
    intro m
    induction m with
    | zero =>
      funext z
      rw [iteratedFDeriv_zero_eq_comp]
      exact equiv_cauchySolve (continuousMultilinearCurryFin0 ℝ E Λ).symm
        (fun c x => by ext; rfl) hv hF.continuous hc z
    | succ m ih =>
      funext z
      have hG : ContDiff ℝ 1 (iteratedFDeriv ℝ m F) :=
        hF.iteratedFDeriv_right (m := 1) (i := m) (by exact_mod_cast le_top)
      have hGc : HasCompactSupport (iteratedFDeriv ℝ m F) := hc.iteratedFDeriv m
      have hd : fderiv ℝ (cauchySolve v (iteratedFDeriv ℝ m F)) =
          cauchySolve v (fderiv ℝ (iteratedFDeriv ℝ m F)) := by
        funext y
        exact (hasFDerivAt_cauchySolve hv hG hGc y).fderiv
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih, hd,
        iteratedFDeriv_succ_eq_comp_left]
      exact equiv_cauchySolve (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => E) Λ).symm (fun c x => by ext; rfl) hv
        (hG.continuous_fderiv one_ne_zero) (hGc.fderiv ℝ) z
  exact congrFun (key m) z

/-- **Z5.b (C.2).** `∂̄_v (cauchySolve v F) = F` for `v ≠ 0`, `F` of class `C¹` with compact
support (`dbar_cauchySolve`). -/
theorem pdbar_cauchySolve {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (z : E) : pdbar v (cauchySolve v F) z = F z := by
  exact dbar_cauchySolve hv hF hc z

/-- **Z5.b (C.2).** `∂̄_w (cauchySolve v F) = cauchySolve v (∂̄_w F)` for every direction `w`
(`hasFDerivAt_cauchySolve`, `map_cauchySolve`). -/
theorem pdbar_cauchySolve_comm {v : E} (hv : v ≠ 0) {F : E → Λ} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (w z : E) :
    pdbar w (cauchySolve v F) z = cauchySolve v (pdbar w F) z := by
  let Φ : (E →L[ℝ] Λ) →L[ℂ] Λ :=
    { toFun := fun A => (2 : ℂ)⁻¹ • (A w + I • A (I • w))
      map_add' := fun A B => by
        simp only [add_apply, smul_add]
        abel
      map_smul' := fun c A => by
        simp only [smul_apply, RingHom.id_apply, smul_add, smul_comm I c,
          smul_comm (2 : ℂ)⁻¹ c]
      cont := by fun_prop }
  have h1 : pdbar w (cauchySolve v F) z = Φ (cauchySolve v (fderiv ℝ F) z) := by
    unfold pdbar
    rw [(hasFDerivAt_cauchySolve hv hF hc z).fderiv]
    rfl
  rw [h1, map_cauchySolve Φ hv (hF.continuous_fderiv one_ne_zero) (hc.fderiv ℝ) z]
  rfl

end Cohesive
