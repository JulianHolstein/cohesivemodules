import Cohesivemodules.Forms.FibreOps
import Cohesivemodules.Analysis.CauchySolveDeriv
import Cohesivemodules.Forms.ChartAux

set_option linter.style.header false

/-!
# Z5.e: flat ∂̄-superconnections on an open subset of `E`

Blueprint item Z5.e (`blueprint/blueprint-ll.md` §4 B.1–B.7, design decisions L1–L2; §11 v1.15).
In a frame of `r` generators the cohesive operator is `𝕏 = ∂̄ + 𝒜` on sections `s : E → Fib E r`,
with `𝒜 : E → FibOp E r` odd (anticommutes with every `εⱼ`) and of total degree `1`.
* `dbarFib s z`: `∂̄` of a section, componentwise `dbarTot` (F9); B.1 `dbarFib_eq_sum`:
  `∂̄ s = Σⱼ εⱼ ∂ⱼ s` with `∂ⱼ = pdbar (finBasis j)`.
* `mcOp 𝒜 = Σⱼ εⱼ ∂ⱼ𝒜 + 𝒜²`; B.2 `dbarFib_add_sq`: `(∂̄ + 𝒜)² s = mcOp 𝒜 · s`.
* `gaugeOp g 𝒜 = g𝒜g⁻¹ − (Σⱼ εⱼ ∂ⱼg) g⁻¹`; B.3: conjugation formula, `mcOp` transforms by
  conjugation, composition law.
* `aCoef i 𝒜 = ιᵢ𝒜 + 𝒜ιᵢ` (the `dz̄ᵢ`-coefficient); B.4 contracted MC; B.5 step algebra; B.6
  properties of `a_k`; B.7 the end of the induction.

## Deviations
* Block works with matrices of forms on a trivialised bundle; here with fibre operators (no
  sign-twisted matrix products). Block's p-degree separation is replaced by B.4 (audit a4).
-/

noncomputable section

namespace Cohesive

open Complex Set Filter Topology
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {r : ℕ}

/-- **Z5.e.** `∂̄` of a section `s : E → Fib E r`, componentwise (`dbarTot`, F9). -/
def dbarFib (s : E → Fib E r) (z : E) : Fib E r := fun i => dbarTot E (fun w => s w i) z

/-- Helper: `dz̄_j` as a `1`-form with the expected coefficient functional. -/
private theorem dzbarTot_eq_ofDeg (j : Fin (Module.finrank ℂ E)) :
    ∃ φ : DolbeaultFibre E 1 ℂ, dzbarTot E j = TotFibre.ofDeg 1 φ ∧
      (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ)
        (0 : Fin 1)).symm φ = LinearMap.toContinuousLinearMap (dualConjBasis E j) := by
  refine ⟨extToFibre E 1 (exteriorPower.ιMulti ℂ 1 ![dualConjBasis E j]), ?_, ?_⟩
  · rw [← TotFibre.extEquivTotFibre_of_mem]
    unfold dzbarTot
    congr 1
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
    simp only [ExteriorAlgebra.ιMulti_zero_apply, mul_one, Matrix.cons_val_zero, Matrix.tail_cons]
  · rw [LinearIsometryEquiv.symm_apply_eq]
    ext v
    rw [extToFibre_ιMulti]
    simp only [Matrix.det_unique, Matrix.of_apply, ContinuousAlternatingMap.ofSubsingletonLIE_apply]
    rfl

/-- Helper: degreewise coordinate formula `∂̄α = Σⱼ dz̄ⱼ ∧ ∂ⱼα`. -/
private theorem ofDeg_dbar_eq_sum {q : ℕ} (α : E → DolbeaultFibre E q ℂ) (z : E) :
    TotFibre.ofDeg (q + 1) (dbar α z) =
      ∑ j, dzbarTot E j * TotFibre.ofDeg q (pdbar (Module.finBasis ℂ E j) α z) := by
  let b := Conj.basis (Module.finBasis ℂ E)
  let A : Conj E →L[ℂ] DolbeaultFibre E q ℂ := antiPart (fderiv ℝ α z)
  have hA : A = ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (A (b i)) := by
    ext v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply]
  have h1 : dbar α z = ContinuousAlternatingMap.alternatizeUncurryFin A := rfl
  have h4 : ContinuousAlternatingMap.alternatizeUncurryFin (∑ i, (LinearMap.toContinuousLinearMap
      (b.coord i)).smulRight (A (b i))) = ∑ i, ContinuousAlternatingMap.alternatizeUncurryFin
        ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (A (b i))) :=
    map_sum (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (Conj E) ℂ) _ _
  rw [h1, hA, h4, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨φ, hφ1, hφ2⟩ := dzbarTot_eq_ofDeg (E := E) j
  have h2 := TotFibre.ofDeg_one_mul φ (A (b j))
  rw [hφ2] at h2
  have h3 : dualConjBasis E j = b.coord j := by
    rw [dualConjBasis, Module.Basis.coe_dualBasis]
  rw [h3] at h2
  have h5 : A (b j) = pdbar (Module.finBasis ℂ E j) α z := by
    simp only [A, b, antiPart_apply, Conj.basis_apply, pdbar]
    rfl
  rw [hφ1, ← h5, ← h2]

/-- Helper: `∂ⱼ` of the degree-`q` component is the degree-`q` component of `∂ⱼ`. -/
private theorem pdbar_apply_component {f : E → TotFibre E} {z : E}
    (hf : DifferentiableAt ℝ f z) (v : E) (q : Fin (Module.finrank ℂ E + 1)) :
    pdbar v (fun w => (f w q : DolbeaultFibre E q ℂ)) z =
      (pdbar v f z q : DolbeaultFibre E q ℂ) := by
  have h := pdbar_comp_clm (LinearMap.toContinuousLinearMap (TotFibre.deg (E := E) (q : ℕ))) v hf
  have e : ∀ x : TotFibre E, (x q : DolbeaultFibre E q ℂ) = TotFibre.deg (q : ℕ) x :=
    fun x => (TotFibre.deg_eq_apply x q.2).symm
  simp only [LinearMap.coe_toContinuousLinearMap'] at h
  simp only [e]
  exact h

/-- Helper: a total-fibre element is the sum of its homogeneous components (indexed by `Fin`). -/
private theorem sum_fin_ofDeg (x : TotFibre E) :
    ∑ q : Fin (Module.finrank ℂ E + 1), TotFibre.ofDeg (q : ℕ) (x q : DolbeaultFibre E q ℂ) =
      x := by
  have e : ∀ q : Fin (Module.finrank ℂ E + 1),
      TotFibre.ofDeg (q : ℕ) (x q : DolbeaultFibre E q ℂ) =
        TotFibre.ofDeg (q : ℕ) (TotFibre.deg (q : ℕ) x) :=
    fun q => by rw [TotFibre.deg_eq_apply x q.2]
  simp only [e]
  rw [Fin.sum_univ_eq_sum_range (fun q => TotFibre.ofDeg q (TotFibre.deg q x))
    (Module.finrank ℂ E + 1)]
  exact TotFibre.sum_ofDeg_deg x

/-- Helper: the coordinate formula on the total fibre. -/
private theorem dbarTot_eq_sum {f : E → TotFibre E} {z : E} (hf : DifferentiableAt ℝ f z) :
    dbarTot E f z = ∑ j, dzbarTot E j * pdbar (Module.finBasis ℂ E j) f z := by
  unfold dbarTot
  simp only [ofDeg_dbar_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  simp only [pdbar_apply_component hf]
  exact sum_fin_ofDeg _

/-- **Z5.e (B.1).** Coordinate formula: `∂̄ s = Σⱼ εⱼ ∂ⱼ s` where `s` is differentiable. -/
theorem dbarFib_eq_sum {s : E → Fib E r} {z : E} (hs : DifferentiableAt ℝ s z) :
    dbarFib s z = ∑ j, epsOp j (pdbar (Module.finBasis ℂ E j) s z) := by
  funext i
  have hi : DifferentiableAt ℝ (fun w => s w i) z := differentiableAt_pi.1 hs i
  have h1 : dbarFib s z i = ∑ j, dzbarTot E j *
      pdbar (Module.finBasis ℂ E j) (fun w => s w i) z := dbarTot_eq_sum hi
  rw [h1, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := pdbar_comp_clm (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => TotFibre E) i)
    (Module.finBasis ℂ E j) hs
  simp only [ContinuousLinearMap.proj_apply] at h2
  rw [h2]
  rfl

omit [FiniteDimensional ℂ E] in
/-- Helper: `pdbar` of a `C^{n+1}` function is `C^n`. -/
private theorem contDiffAt_pdbar {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] (v : E)
    {f : E → Λ} {z : E} {n : ℕ} (hf : ContDiffAt ℝ (n + 1 : ℕ) f z) :
    ContDiffAt ℝ n (fun w => pdbar v f w) z := by
  have h1 : ContDiffAt ℝ n (fderiv ℝ f) z := hf.fderiv_right (by norm_cast)
  have h2 : ContDiffAt ℝ n (fun w => fderiv ℝ f w v) z := h1.clm_apply contDiffAt_const
  have h3 : ContDiffAt ℝ n (fun w => fderiv ℝ f w (I • v)) z := h1.clm_apply contDiffAt_const
  unfold pdbar
  exact (h2.add (h3.const_smul I)).const_smul _

/-- Helper: `dbarFib` only depends on the germ. -/
private theorem dbarFib_congr {f g : E → Fib E r} {z : E} (h : f =ᶠ[nhds z] g) :
    dbarFib f z = dbarFib g z :=
  funext fun i => dbarTot_congr (h.mono fun w hw => by simp only [hw])

/-- Helper: `∂̄∂̄ = 0` on sections of class `C²`. -/
private theorem dbarFib_dbarFib {s : E → Fib E r} {z : E} (hs : ContDiffAt ℝ 2 s z) :
    dbarFib (dbarFib s) z = 0 :=
  funext fun i => dbarTot_dbarTot (f := fun w => s w i) (contDiffAt_pi.1 hs i)

/-- Helper: `∂̄ s` is `C¹` at `z` when `s` is `C²` at `z`. -/
private theorem contDiffAt_dbarFib {s : E → Fib E r} {z : E} (hs : ContDiffAt ℝ 2 s z) :
    ContDiffAt ℝ 1 (dbarFib s) z := by
  have hev : ∀ᶠ w in nhds z, ContDiffAt ℝ 2 s w := hs.eventually (by simp)
  have h1 : dbarFib s =ᶠ[nhds z] fun w => ∑ j, epsOp j (pdbar (Module.finBasis ℂ E j) s w) :=
    hev.mono fun w hw => dbarFib_eq_sum (hw.differentiableAt (by norm_num))
  refine ContDiffAt.congr_of_eventuallyEq ?_ h1
  refine ContDiffAt.sum fun j _ => ?_
  have h2 : ContDiffAt ℝ 1 (fun w => pdbar (Module.finBasis ℂ E j) s w) z :=
    contDiffAt_pdbar _ (n := 1) hs
  exact ((epsOp j : FibOp E r).restrictScalars ℝ).contDiff.contDiffAt.comp z h2

/-- Helper: the product rule for `pdbar` in the algebra of fibre operators. -/
private theorem pdbar_mul_op (v : E) {h g : E → FibOp E r} {z : E} (hh : DifferentiableAt ℝ h z)
    (hg : DifferentiableAt ℝ g z) :
    pdbar v (fun w => h w * g w) z = pdbar v h z * g z + h z * pdbar v g z := by
  unfold pdbar
  rw [fderiv_fun_mul' hh hg]
  simp only [add_apply, smul_apply, smul_eq_mul, smul_add, add_mul, mul_add]
  simp only [op_smul_eq_mul, smul_mul_assoc, mul_smul_comm]
  abel

/-- Helper: derivative of the inverse in the algebra of fibre operators. -/
private theorem pdbar_ringInverse (v : E) {g : E → FibOp E r} {z : E}
    (hg : DifferentiableAt ℝ g z) (hu : IsUnit (g z)) :
    pdbar v (fun w => Ring.inverse (g w)) z =
      -(Ring.inverse (g z) * pdbar v g z * Ring.inverse (g z)) := by
  obtain ⟨u, hu'⟩ := hu
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu'] at h1
  have h2 := h1.comp z hg.hasFDerivAt
  have h3 : Ring.inverse (g z) = ↑u⁻¹ := by rw [← hu', Ring.inverse_unit]
  have h4 : fderiv ℝ (fun w => Ring.inverse (g w)) z = _ := h2.fderiv
  unfold pdbar
  rw [h4, h3]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_add, smul_neg, neg_add]

/-- Helper: `w ↦ P w (s w)` is differentiable when `P` and `s` are. -/
private theorem differentiableAt_apply_op {P : E → FibOp E r} {s : E → Fib E r} {z : E}
    (hP : DifferentiableAt ℝ P z) (hs : DifferentiableAt ℝ s z) :
    DifferentiableAt ℝ (fun w => P w (s w)) z := by
  let R : FibOp E r →L[ℝ] (Fib E r →L[ℝ] Fib E r) :=
    ContinuousLinearMap.restrictScalarsL ℂ (Fib E r) (Fib E r) ℝ ℝ
  exact (R.differentiableAt.comp z hP).clm_apply hs

/-- Helper: the product rule for `pdbar` of `w ↦ P w (s w)`. -/
private theorem pdbar_apply_op (v : E) {P : E → FibOp E r} {s : E → Fib E r} {z : E}
    (hP : DifferentiableAt ℝ P z) (hs : DifferentiableAt ℝ s z) :
    pdbar v (fun w => P w (s w)) z = P z (pdbar v s z) + pdbar v P z (s z) := by
  let R : FibOp E r →L[ℝ] (Fib E r →L[ℝ] Fib E r) :=
    ContinuousLinearMap.restrictScalarsL ℂ (Fib E r) (Fib E r) ℝ ℝ
  have hc : DifferentiableAt ℝ (fun w => R (P w)) z := R.differentiableAt.comp z hP
  have h1 := fderiv_clm_apply hc hs
  have h2 : fderiv ℝ (fun w => R (P w)) z = R.comp (fderiv ℝ P z) :=
    (R.hasFDerivAt.comp z hP.hasFDerivAt).fderiv
  rw [h2] at h1
  have h3 : fderiv ℝ (fun w => P w (s w)) z = _ := h1
  unfold pdbar
  rw [h3]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, R, ContinuousLinearMap.coe_restrict_scalarsL',
    ContinuousLinearMap.coe_restrictScalars', smul_apply, smul_add]
  simp only [map_add, map_smul]
  abel

/-- **Z5.e.** The Maurer–Cartan expression `Σⱼ εⱼ ∂ⱼ𝒜 + 𝒜²`. -/
def mcOp (𝒜 : E → FibOp E r) (z : E) : FibOp E r :=
  (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) 𝒜 z) + 𝒜 z * 𝒜 z

/-- **Z5.e (B.2).** Curvature: for `𝒜` odd near `z` and `s` of class `C²` near `z`,
`(∂̄ + 𝒜)((∂̄ + 𝒜) s) = mcOp 𝒜 · s` at `z`. -/
theorem dbarFib_add_sq {𝒜 : E → FibOp E r} {s : E → Fib E r} {z : E}
    (h𝒜 : ContDiffAt ℝ 1 𝒜 z) (hs : ContDiffAt ℝ 2 s z)
    (hodd : ∀ j, epsOp j * 𝒜 z = -(𝒜 z * epsOp j)) :
    dbarFib (fun w => dbarFib s w + 𝒜 w (s w)) z + 𝒜 z (dbarFib s z + 𝒜 z (s z)) =
      mcOp 𝒜 z (s z) := by
  have hs1 : DifferentiableAt ℝ s z := hs.differentiableAt (by norm_num)
  have hA1 : DifferentiableAt ℝ 𝒜 z := h𝒜.differentiableAt (by norm_num)
  have hD1 : DifferentiableAt ℝ (dbarFib s) z :=
    (contDiffAt_dbarFib hs).differentiableAt (by norm_num)
  have hAs : DifferentiableAt ℝ (fun w => 𝒜 w (s w)) z := differentiableAt_apply_op hA1 hs1
  have hS : DifferentiableAt ℝ (fun w => dbarFib s w + 𝒜 w (s w)) z := hD1.add hAs
  rw [dbarFib_eq_sum hS]
  have e1 : ∀ j, pdbar (Module.finBasis ℂ E j) (fun w => dbarFib s w + 𝒜 w (s w)) z =
      pdbar (Module.finBasis ℂ E j) (dbarFib s) z +
        pdbar (Module.finBasis ℂ E j) (fun w => 𝒜 w (s w)) z :=
    fun j => pdbar_add _ hD1 hAs
  have e2 : ∑ j, epsOp j (pdbar (Module.finBasis ℂ E j) (dbarFib s) z) = 0 := by
    rw [← dbarFib_eq_sum hD1]
    exact dbarFib_dbarFib hs
  have e3 : ∀ j, pdbar (Module.finBasis ℂ E j) (fun w => 𝒜 w (s w)) z =
      𝒜 z (pdbar (Module.finBasis ℂ E j) s z) + pdbar (Module.finBasis ℂ E j) 𝒜 z (s z) :=
    fun j => pdbar_apply_op _ hA1 hs1
  have e4 : ∑ j, epsOp j (𝒜 z (pdbar (Module.finBasis ℂ E j) s z)) = -𝒜 z (dbarFib s z) := by
    rw [dbarFib_eq_sum hs1, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := congrArg (fun T : FibOp E r => T (pdbar (Module.finBasis ℂ E j) s z)) (hodd j)
    simpa only [mul_apply_eq_comp, neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, map_neg] using h
  simp only [e1, e3, map_add, Finset.sum_add_distrib, e2, e4]
  simp only [mcOp, add_apply, sum_apply, mul_apply_eq_comp]
  abel

omit [FiniteDimensional ℂ E] in
/-- Helper: `pdbar` of a constant function is zero. -/
private theorem pdbar_const_zero {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] (v z : E)
    {c : Λ} : pdbar v (fun _ : E => c) z = 0 := by
  unfold pdbar
  simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, smul_zero, add_zero]

/-- Helper: an operator commuting with a unit commutes with its `Ring.inverse`. -/
private theorem commute_ringInverse {e g : FibOp E r} (hg : IsUnit g) (h : e * g = g * e) :
    e * Ring.inverse g = Ring.inverse g * e := by
  obtain ⟨u, rfl⟩ := hg
  rw [Ring.inverse_unit]
  exact (Commute.units_inv_right (show Commute e u from h)).eq

/-- Helper: `pdbar` of a function commuting with `e` commutes with `e`. -/
private theorem pdbar_commute (e : FibOp E r) {g : E → FibOp E r} (z : E) (v : E)
    (h : ∀ w, e * g w = g w * e) : e * pdbar v g z = pdbar v g z * e := by
  by_cases hd : DifferentiableAt ℝ g z
  · let Φ : FibOp E r →L[ℂ] FibOp E r :=
      ContinuousLinearMap.mul ℂ (FibOp E r) e - (ContinuousLinearMap.mul ℂ (FibOp E r)).flip e
    have hΦ : ∀ T, Φ T = e * T - T * e := fun T => rfl
    have h1 := pdbar_comp_clm Φ v hd
    have h2 : (fun w => Φ (g w)) = fun _ => 0 := funext fun w => by rw [hΦ, h w, sub_self]
    rw [h2] at h1
    rw [pdbar_const_zero _ z, hΦ] at h1
    exact (sub_eq_zero.1 h1.symm)
  · have : fderiv ℝ g z = 0 := fderiv_zero_of_not_differentiableAt hd
    unfold pdbar
    rw [this]
    simp only [zero_apply, smul_zero, add_zero, mul_zero, zero_mul]

/-- **Z5.e.** The gauge action `g·𝒜 = g𝒜g⁻¹ − (Σⱼ εⱼ ∂ⱼg) g⁻¹`. -/
def gaugeOp (g 𝒜 : E → FibOp E r) (z : E) : FibOp E r :=
  g z * 𝒜 z * Ring.inverse (g z) -
    (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) g z) * Ring.inverse (g z)

/-- Helper: `(-a) b = -(a b)` for fibre operators. -/
private theorem neg_mul_op (a b : FibOp E r) : -a * b = -(a * b) :=
  ContinuousLinearMap.neg_comp a b

/-- Helper: `a (-b) = -(a b)` for fibre operators. -/
private theorem mul_neg_op (a b : FibOp E r) : a * -b = -(a * b) :=
  ContinuousLinearMap.comp_neg a b

/-- **Z5.e (B.3).** Conjugation: for `g` differentiable, invertible and commuting with every `εⱼ`,
`g (∂̄ + 𝒜)(g⁻¹ s) = (∂̄ + g·𝒜) s` at `z`. -/
theorem gauge_conj {g 𝒜 : E → FibOp E r} {s : E → Fib E r} {z : E} (hg : ContDiffAt ℝ 1 g z)
    (hs : DifferentiableAt ℝ s z) (hunit : ∀ w, IsUnit (g w))
    (hcomm : ∀ w j, epsOp j * g w = g w * epsOp j) :
    g z (dbarFib (fun w => Ring.inverse (g w) (s w)) z + 𝒜 z (Ring.inverse (g z) (s z))) =
      dbarFib s z + gaugeOp g 𝒜 z (s z) := by
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hP : DifferentiableAt ℝ (fun w => Ring.inverse (g w)) z :=
    DifferentiableAt.inverse hgd (hunit z)
  have hPs : DifferentiableAt ℝ (fun w => Ring.inverse (g w) (s w)) z :=
    differentiableAt_apply_op hP hs
  have hGi : g z * Ring.inverse (g z) = 1 := Ring.mul_inverse_cancel _ (hunit z)
  have hj : ∀ j, g z (epsOp j (pdbar (Module.finBasis ℂ E j) (fun w => Ring.inverse (g w) (s w))
      z)) = epsOp j (pdbar (Module.finBasis ℂ E j) s z) -
        epsOp j (pdbar (Module.finBasis ℂ E j) g z (Ring.inverse (g z) (s z))) := by
    intro j
    rw [pdbar_apply_op _ hP hs, pdbar_ringInverse _ hgd (hunit z), map_add, map_add]
    have hOp1 : g z * epsOp j * Ring.inverse (g z) = epsOp j := by
      rw [← hcomm z j, mul_assoc, hGi, mul_one]
    have hOp2 : g z * epsOp j * (-(Ring.inverse (g z) * pdbar (Module.finBasis ℂ E j) g z *
        Ring.inverse (g z))) = -(epsOp j * pdbar (Module.finBasis ℂ E j) g z *
          Ring.inverse (g z)) := by
      rw [← hcomm z j, mul_neg_op]
      congr 1
      calc epsOp j * g z * (Ring.inverse (g z) * pdbar (Module.finBasis ℂ E j) g z *
            Ring.inverse (g z)) = epsOp j * (g z * Ring.inverse (g z)) *
              pdbar (Module.finBasis ℂ E j) g z * Ring.inverse (g z) := by noncomm_ring
        _ = _ := by rw [hGi, mul_one]
    have e1 : g z (epsOp j (Ring.inverse (g z) (pdbar (Module.finBasis ℂ E j) s z))) =
        epsOp j (pdbar (Module.finBasis ℂ E j) s z) :=
      congrArg (fun T : FibOp E r => T (pdbar (Module.finBasis ℂ E j) s z)) hOp1
    have e2 : g z (epsOp j ((-(Ring.inverse (g z) * pdbar (Module.finBasis ℂ E j) g z *
        Ring.inverse (g z))) (s z))) = -(epsOp j ((pdbar (Module.finBasis ℂ E j) g z)
          (Ring.inverse (g z) (s z)))) :=
      congrArg (fun T : FibOp E r => T (s z)) hOp2
    rw [e1, e2]
    abel
  have hS : (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) g z : FibOp E r)
      (Ring.inverse (g z) (s z)) =
      ∑ j, epsOp j (pdbar (Module.finBasis ℂ E j) g z (Ring.inverse (g z) (s z))) := by
    rw [sum_apply]
    rfl
  rw [dbarFib_eq_sum hPs, dbarFib_eq_sum hs, map_add, map_sum]
  simp only [hj, Finset.sum_sub_distrib]
  simp only [gaugeOp, sub_apply]
  have h2 : ((∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) g z : FibOp E r) *
      Ring.inverse (g z)) (s z) = (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) g z : FibOp E r)
        (Ring.inverse (g z) (s z)) := rfl
  rw [h2, hS]
  show _ = _ + ((g z * 𝒜 z * Ring.inverse (g z)) (s z) - _)
  abel

/-- Helper: ring-theoretic core of `gaugeOp_odd`. -/
private theorem alg_odd {R : Type} [Ring R] (e G A Gi S : R) (h1 : e * G = G * e)
    (h2 : e * Gi = Gi * e) (h3 : e * A = -(A * e)) (h4 : e * S = -(S * e)) :
    e * (G * A * Gi - S * Gi) = -((G * A * Gi - S * Gi) * e) := by
  have h1' : e * G - G * e = 0 := sub_eq_zero.2 h1
  have h2' : e * Gi - Gi * e = 0 := sub_eq_zero.2 h2
  have h3' : e * A + A * e = 0 := by rw [h3]; abel
  have h4' : e * S + S * e = 0 := by rw [h4]; abel
  have key : e * (G * A * Gi - S * Gi) + (G * A * Gi - S * Gi) * e =
      (e * G - G * e) * A * Gi + G * (e * A + A * e) * Gi - G * A * (e * Gi - Gi * e)
        - (e * S + S * e) * Gi + S * (e * Gi - Gi * e) := by noncomm_ring
  rw [h1', h2', h3', h4'] at key
  simp only [zero_mul, mul_zero, add_zero, sub_self] at key
  exact eq_neg_of_add_eq_zero_left key

/-- Helper: `Σᵢ εᵢ ∂ᵢg` anticommutes with `εⱼ` when `g` commutes with every `εⱼ`. -/
private theorem eps_mul_sum_pdbar {g : E → FibOp E r} {z : E}
    (hcomm : ∀ w j, epsOp j * g w = g w * epsOp j) (j : Fin (Module.finrank ℂ E)) :
    epsOp j * (∑ i, epsOp i * pdbar (Module.finBasis ℂ E i) g z) =
      -((∑ i, epsOp i * pdbar (Module.finBasis ℂ E i) g z) * epsOp j) := by
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := pdbar_commute (epsOp j : FibOp E r) z (Module.finBasis ℂ E i) (hcomm · j)
  rw [← mul_assoc, epsOp_mul_comm, neg_mul_op, mul_assoc, h1, ← mul_assoc]

/-- **Z5.e (B.3).** On an open set, `g·𝒜` is again odd, and `mcOp (g·𝒜) = g (mcOp 𝒜) g⁻¹`. -/
theorem gaugeOp_odd {g 𝒜 : E → FibOp E r} {z : E} (hunit : IsUnit (g z))
    (hcomm : ∀ w j, epsOp j * g w = g w * epsOp j)
    (hodd : ∀ j, epsOp j * 𝒜 z = -(𝒜 z * epsOp j)) :
    ∀ j, epsOp j * gaugeOp g 𝒜 z = -(gaugeOp g 𝒜 z * epsOp j) := by
  intro j
  exact alg_odd _ _ _ _ _ (hcomm z j) (commute_ringInverse hunit (hcomm z j)) (hodd j)
    (eps_mul_sum_pdbar hcomm j)

/-- Helper: `Ring.inverse ∘ g` is `C^n` where `g` is and `g z` is a unit. -/
private theorem contDiffAt_ringInverse_comp {n : WithTop ℕ∞} {g : E → FibOp E r} {z : E}
    (hg : ContDiffAt ℝ n g z) (hu : IsUnit (g z)) :
    ContDiffAt ℝ n (fun w => Ring.inverse (g w)) z := by
  obtain ⟨u, hu'⟩ := hu
  have h := contDiffAt_ringInverse ℝ (n := n) u
  rw [hu'] at h
  exact h.comp z hg

/-- Helper: `w ↦ P w (s w)` is `C^n` when `P` and `s` are. -/
private theorem contDiffAt_apply_op {n : WithTop ℕ∞} {P : E → FibOp E r} {s : E → Fib E r}
    {z : E} (hP : ContDiffAt ℝ n P z) (hs : ContDiffAt ℝ n s z) :
    ContDiffAt ℝ n (fun w => P w (s w)) z := by
  let R : FibOp E r →L[ℝ] (Fib E r →L[ℝ] Fib E r) :=
    ContinuousLinearMap.restrictScalarsL ℂ (Fib E r) (Fib E r) ℝ ℝ
  exact (R.contDiff.contDiffAt.comp z hP).clm_apply hs

/-- Helper: `∂̄` of a constant section vanishes. -/
private theorem dbarFib_const (v : Fib E r) (w : E) : dbarFib (fun _ => v) w = 0 := by
  rw [dbarFib_eq_sum (differentiableAt_const v)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [pdbar_const_zero, map_zero]

/-- Helper: the gauge action of a `C²` gauge on a `C¹` coefficient is `C¹`. -/
private theorem contDiffAt_gaugeOp {g 𝒜 : E → FibOp E r} {z : E} (hg : ContDiffAt ℝ 2 g z)
    (h𝒜 : ContDiffAt ℝ 1 𝒜 z) (hu : IsUnit (g z)) : ContDiffAt ℝ 1 (gaugeOp g 𝒜) z := by
  have hg1 : ContDiffAt ℝ 1 g z := hg.of_le (by norm_num)
  have hGi : ContDiffAt ℝ 1 (fun w => Ring.inverse (g w)) z := contDiffAt_ringInverse_comp hg1 hu
  have hD : ∀ j, ContDiffAt ℝ 1 (fun w => pdbar (Module.finBasis ℂ E j) g w) z :=
    fun j => contDiffAt_pdbar _ (n := 1) hg
  have h1 := (hg1.mul h𝒜).mul hGi
  have h2 := (ContDiffAt.sum fun j (_ : j ∈ Finset.univ) =>
    (contDiffAt_const (c := (epsOp j : FibOp E r))).mul (hD j)).mul hGi
  exact h1.sub h2

/-- **Z5.e (B.3).** `mcOp (g·𝒜) = g (mcOp 𝒜) g⁻¹` on an open set where `g`, `𝒜` are smooth. -/
theorem mcOp_gaugeOp {U : Set E} (hU : IsOpen U) {g 𝒜 : E → FibOp E r}
    (hg : ContDiffOn ℝ ∞ g U) (h𝒜 : ContDiffOn ℝ ∞ 𝒜 U) (hunit : ∀ w, IsUnit (g w))
    (hcomm : ∀ w j, epsOp j * g w = g w * epsOp j)
    (hodd : ∀ w ∈ U, ∀ j, epsOp j * 𝒜 w = -(𝒜 w * epsOp j)) :
    ∀ z ∈ U, mcOp (gaugeOp g 𝒜) z = g z * mcOp 𝒜 z * Ring.inverse (g z) := by
  intro z hz
  have hzU : U ∈ nhds z := hU.mem_nhds hz
  have hgC : ∀ w ∈ U, ContDiffAt ℝ ∞ g w := fun w hw => hg.contDiffAt (hU.mem_nhds hw)
  have hAC : ∀ w ∈ U, ContDiffAt ℝ ∞ 𝒜 w := fun w hw => h𝒜.contDiffAt (hU.mem_nhds hw)
  have hg2 : ContDiffAt ℝ 2 g z := (hgC z hz).of_le (by norm_num)
  have hA1 : ContDiffAt ℝ 1 𝒜 z := (hAC z hz).of_le (by norm_num)
  have hA'1 : ContDiffAt ℝ 1 (gaugeOp g 𝒜) z := contDiffAt_gaugeOp hg2 hA1 (hunit z)
  have hodd' := gaugeOp_odd (hunit z) hcomm (hodd z hz)
  refine ContinuousLinearMap.ext fun v => ?_
  -- the section `u = g⁻¹ v` and its twisted derivative
  set u : E → Fib E r := fun w => Ring.inverse (g w) v with hu
  have hu2 : ContDiffAt ℝ 2 u z :=
    contDiffAt_apply_op (contDiffAt_ringInverse_comp hg2 (hunit z)) contDiffAt_const
  have hF4 : ∀ w ∈ U, dbarFib u w + 𝒜 w (u w) = Ring.inverse (g w) (gaugeOp g 𝒜 w v) := by
    intro w hw
    have h := gauge_conj (𝒜 := 𝒜) (s := fun _ => v) ((hgC w hw).of_le (by norm_num))
      (differentiableAt_const v) hunit hcomm
    rw [dbarFib_const, zero_add] at h
    have e : ∀ x, Ring.inverse (g w) (g w x) = x := fun x =>
      congrArg (fun T : FibOp E r => T x) (Ring.inverse_mul_cancel (g w) (hunit w))
    rw [← h, e]
  have h5 := gauge_conj (𝒜 := 𝒜) (s := fun w => gaugeOp g 𝒜 w v) (z := z)
    (hg2.of_le (by norm_num)) (differentiableAt_apply_op (hA'1.differentiableAt (by norm_num))
      (differentiableAt_const v)) hunit hcomm
  have h6 := dbarFib_add_sq (𝒜 := gaugeOp g 𝒜) (s := fun _ => v) (z := z) hA'1
    contDiffAt_const hodd'
  simp only [dbarFib_const, zero_add] at h6
  have h7 : dbarFib (fun w => Ring.inverse (g w) (gaugeOp g 𝒜 w v)) z =
      dbarFib (fun w => dbarFib u w + 𝒜 w (u w)) z :=
    dbarFib_congr (Filter.eventually_of_mem hzU fun w hw => (hF4 w hw).symm)
  have h8 := dbarFib_add_sq (s := u) hA1 hu2 (hodd z hz)
  rw [← h6, ← h5, h7, ← hF4 z hz, h8]
  rfl

/-- Helper: ring-theoretic core of `gaugeOp_mul`. -/
private theorem alg_mul {R : Type} [Ring R] (h g A Gi Hi Sh Sg : R) (hg : g * Gi = 1) :
    h * g * A * (Gi * Hi) - (Sh * g + h * Sg) * (Gi * Hi) =
      h * (g * A * Gi - Sg * Gi) * Hi - Sh * Hi := by
  have key : h * g * A * (Gi * Hi) - (Sh * g + h * Sg) * (Gi * Hi) -
      (h * (g * A * Gi - Sg * Gi) * Hi - Sh * Hi) = -(Sh * (g * Gi - 1)) * Hi := by noncomm_ring
  rw [hg, sub_self, mul_zero, neg_zero, zero_mul] at key
  exact sub_eq_zero.1 key

/-- **Z5.e (B.3).** Composition: `(h g)·𝒜 = h·(g·𝒜)`. -/
theorem gaugeOp_mul {g h 𝒜 : E → FibOp E r} {z : E} (hg : DifferentiableAt ℝ g z)
    (hh : DifferentiableAt ℝ h z) (hgu : ∀ w, IsUnit (g w)) (hhu : ∀ w, IsUnit (h w))
    (hgc : ∀ w j, epsOp j * g w = g w * epsOp j) (hhc : ∀ w j, epsOp j * h w = h w * epsOp j) :
    gaugeOp (fun w => h w * g w) 𝒜 z = gaugeOp h (gaugeOp g 𝒜) z := by
  have _ := hgc
  have hI : Ring.inverse (h z * g z) = Ring.inverse (g z) * Ring.inverse (h z) :=
    Ring.inverse_mul (Or.inl (hhu z))
  have hS : ∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) (fun w => h w * g w) z =
      (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) h z) * g z +
        h z * ∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) g z := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pdbar_mul_op _ hh hg, mul_add, ← mul_assoc, ← mul_assoc (h z), ← hhc z j, mul_assoc,
      mul_assoc]
  simp only [gaugeOp]
  rw [hI, hS]
  exact alg_mul _ _ _ _ _ _ _ (Ring.mul_inverse_cancel _ (hgu z))

/-- **Z5.e.** The `dz̄ᵢ`-coefficient `aᵢ = ιᵢ𝒜 + 𝒜ιᵢ`. -/
def aCoef (i : Fin (Module.finrank ℂ E)) (𝒜 : E → FibOp E r) (z : E) : FibOp E r :=
  iotaOp i * 𝒜 z + 𝒜 z * iotaOp i

/-- Helper: ring-theoretic core of `iota_mcOp` (one summand). -/
private theorem alg_iota_term {R : Type} [Ring R] (i e D c : R) (hc : i * e + e * i = c) :
    i * (e * D) - (e * D) * i = c * D - e * (i * D + D * i) := by
  have key : i * (e * D) - (e * D) * i - (c * D - e * (i * D + D * i)) =
      (i * e + e * i - c) * D := by noncomm_ring
  rw [hc, sub_self, zero_mul] at key
  exact sub_eq_zero.1 key

/-- Helper: ring-theoretic core of `iota_mcOp` (the square). -/
private theorem alg_iota_sq {R : Type} [Ring R] (i A : R) :
    i * (A * A) - (A * A) * i = (i * A + A * i) * A - A * (i * A + A * i) := by
  noncomm_ring

/-- Helper: `∂ⱼ aᵢ = ιᵢ ∂ⱼ𝒜 + ∂ⱼ𝒜 ιᵢ`. -/
private theorem pdbar_aCoef (i : Fin (Module.finrank ℂ E)) (v : E) {𝒜 : E → FibOp E r} {z : E}
    (h𝒜 : DifferentiableAt ℝ 𝒜 z) :
    pdbar v (aCoef i 𝒜) z = iotaOp i * pdbar v 𝒜 z + pdbar v 𝒜 z * iotaOp i := by
  let Ψ : FibOp E r →L[ℂ] FibOp E r :=
    ContinuousLinearMap.mul ℂ (FibOp E r) (iotaOp i) +
      (ContinuousLinearMap.mul ℂ (FibOp E r)).flip (iotaOp i)
  have h := pdbar_comp_clm Ψ v h𝒜
  exact h

/-- **Z5.e (B.4).** Contracted Maurer–Cartan: for `𝒜` differentiable at `z`,
`ιᵢ mc − mc ιᵢ = ∂ᵢ𝒜 − Σⱼ εⱼ ∂ⱼaᵢ + aᵢ𝒜 − 𝒜aᵢ`. -/
theorem iota_mcOp (i : Fin (Module.finrank ℂ E)) {𝒜 : E → FibOp E r} {z : E}
    (h𝒜 : DifferentiableAt ℝ 𝒜 z) :
    iotaOp i * mcOp 𝒜 z - mcOp 𝒜 z * iotaOp i =
      pdbar (Module.finBasis ℂ E i) 𝒜 z -
        (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) (aCoef i 𝒜) z) +
        aCoef i 𝒜 z * 𝒜 z - 𝒜 z * aCoef i 𝒜 z := by
  have hcoef : ∀ j, pdbar (Module.finBasis ℂ E j) (aCoef i 𝒜) z =
      iotaOp i * pdbar (Module.finBasis ℂ E j) 𝒜 z + pdbar (Module.finBasis ℂ E j) 𝒜 z * iotaOp i :=
    fun j => pdbar_aCoef i _ h𝒜
  simp only [hcoef]
  have hterm : ∀ j, iotaOp i * (epsOp j * pdbar (Module.finBasis ℂ E j) 𝒜 z) -
      (epsOp j * pdbar (Module.finBasis ℂ E j) 𝒜 z) * iotaOp i =
      (if i = j then 1 else 0) * pdbar (Module.finBasis ℂ E j) 𝒜 z -
        epsOp j * (iotaOp i * pdbar (Module.finBasis ℂ E j) 𝒜 z +
          pdbar (Module.finBasis ℂ E j) 𝒜 z * iotaOp i) :=
    fun j => alg_iota_term _ _ _ _ (iotaOp_epsOp i j)
  have hsum : iotaOp i * (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) 𝒜 z) -
      (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) 𝒜 z) * iotaOp i =
      pdbar (Module.finBasis ℂ E i) 𝒜 z - ∑ j, epsOp j *
        (iotaOp i * pdbar (Module.finBasis ℂ E j) 𝒜 z +
          pdbar (Module.finBasis ℂ E j) 𝒜 z * iotaOp i) := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp only [hterm, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  have e : iotaOp i * (𝒜 z * 𝒜 z) - 𝒜 z * 𝒜 z * iotaOp i =
      aCoef i 𝒜 z * 𝒜 z - 𝒜 z * aCoef i 𝒜 z := alg_iota_sq (iotaOp i : FibOp E r) (𝒜 z)
  have hsplit : ∀ S T : FibOp E r, iotaOp i * (S + T) - (S + T) * iotaOp i =
      (iotaOp i * S - S * iotaOp i) + (iotaOp i * T - T * iotaOp i) := fun S T => by
    noncomm_ring
  unfold mcOp
  rw [hsplit, hsum, e]
  abel

/-- **Z5.e (B.4, corollary).** If `mcOp 𝒜 = 0` and `aᵢ = 0` on an open `U`, then `∂ᵢ𝒜 = 0` on
`U`. -/
theorem pdbar_eq_zero_of_aCoef {U : Set E} (hU : IsOpen U) {𝒜 : E → FibOp E r}
    (h𝒜 : ContDiffOn ℝ 1 𝒜 U) (hmc : ∀ z ∈ U, mcOp 𝒜 z = 0) (i : Fin (Module.finrank ℂ E))
    (ha : ∀ z ∈ U, aCoef i 𝒜 z = 0) : ∀ z ∈ U, pdbar (Module.finBasis ℂ E i) 𝒜 z = 0 := by
  intro z hz
  have hzU : U ∈ nhds z := hU.mem_nhds hz
  have hdiff : DifferentiableAt ℝ 𝒜 z := (h𝒜.contDiffAt hzU).differentiableAt (by norm_num)
  have h := iota_mcOp i hdiff
  have h0 : ∀ j, pdbar (Module.finBasis ℂ E j) (aCoef i 𝒜) z = 0 := fun j => by
    rw [pdbar_congr (g := fun _ => (0 : FibOp E r)) _
      (Filter.eventually_of_mem hzU fun w hw => ha w hw)]
    exact pdbar_const_zero _ z
  simp only [hmc z hz, ha z hz, h0, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero,
    add_zero, sub_self] at h
  exact h.symm

/-- Helper: ring-theoretic core of `aCoef_gaugeOp`. -/
private theorem alg_iota_gauge {R : Type} [Ring R] (i G A Gi S D : R) (h1 : i * G = G * i)
    (h2 : i * Gi = Gi * i) (hS : i * S + S * i = D) :
    i * (G * A * Gi - S * Gi) + (G * A * Gi - S * Gi) * i =
      G * (i * A + A * i) * Gi - D * Gi := by
  have key : i * (G * A * Gi - S * Gi) + (G * A * Gi - S * Gi) * i -
      (G * (i * A + A * i) * Gi - D * Gi) = (i * G - G * i) * A * Gi - G * A * (i * Gi - Gi * i)
        - (i * S + S * i - D) * Gi + S * (i * Gi - Gi * i) := by noncomm_ring
  rw [sub_eq_zero.2 h1, sub_eq_zero.2 h2, hS, sub_self] at key
  simp only [zero_mul, mul_zero, sub_self, add_zero] at key
  exact sub_eq_zero.1 key

/-- Helper: ring-theoretic core of `aCoef_gaugeOp` (one summand). -/
private theorem alg_iota_term2 {R : Type} [Ring R] (i e D c : R) (hc : i * e + e * i = c)
    (hD : i * D = D * i) : i * (e * D) + (e * D) * i = c * D := by
  rw [← hc, add_mul, ← mul_assoc, mul_assoc e D i, ← hD, ← mul_assoc]

/-- **Z5.e (B.5).** Step algebra: if `g` commutes with `ιᵢ` and `εⱼ`, is invertible and
differentiable at `z`, then `aᵢ(g·𝒜) = g aᵢ g⁻¹ − (∂ᵢg) g⁻¹`. -/
theorem aCoef_gaugeOp (i : Fin (Module.finrank ℂ E)) {g 𝒜 : E → FibOp E r} {z : E}
    (hg : DifferentiableAt ℝ g z) (hunit : ∀ w, IsUnit (g w))
    (hcomm : ∀ w j, epsOp j * g w = g w * epsOp j) (hiota : ∀ w, iotaOp i * g w = g w * iotaOp i) :
    aCoef i (gaugeOp g 𝒜) z =
      g z * aCoef i 𝒜 z * Ring.inverse (g z) -
        pdbar (Module.finBasis ℂ E i) g z * Ring.inverse (g z) := by
  have _ := hg
  have _ := hcomm
  have hD : ∀ j, iotaOp i * pdbar (Module.finBasis ℂ E j) g z =
      pdbar (Module.finBasis ℂ E j) g z * iotaOp i :=
    fun j => pdbar_commute (iotaOp i : FibOp E r) z _ hiota
  have hS : iotaOp i * (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) g z) +
      (∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) g z) * iotaOp i =
      pdbar (Module.finBasis ℂ E i) g z := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    simp only [alg_iota_term2 _ _ _ _ (iotaOp_epsOp i _) (hD _), ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold aCoef gaugeOp
  exact alg_iota_gauge _ _ _ _ _ _ (hiota z) (commute_ringInverse (hunit z) (hiota z)) hS

/-- Helper: ring-theoretic core of `aCoef_comm` (commutation with `εⱼ`). -/
private theorem alg_comm_eps {R : Type} [Ring R] (e i A d : R) (h1 : e * A = -(A * e))
    (h2 : i * e + e * i = d) (hd : d * A = A * d) :
    e * (i * A + A * i) = (i * A + A * i) * e := by
  have h1' : e * A + A * e = 0 := by rw [h1]; abel
  have key : e * (i * A + A * i) - (i * A + A * i) * e =
      (i * e + e * i - d) * A - A * (i * e + e * i - d) + (d * A - A * d)
        - i * (e * A + A * e) + (e * A + A * e) * i := by noncomm_ring
  rw [h1', h2, sub_self, hd, sub_self] at key
  simp only [zero_mul, mul_zero, sub_self, add_zero] at key
  exact sub_eq_zero.1 key

/-- Helper: ring-theoretic core of `aCoef_comm` (commutation with `ιᵢ`, `i < k`). -/
private theorem alg_comm_iota_lt {R : Type} [Ring R] (i k A : R) (h1 : i * k + k * i = 0)
    (h2 : i * A + A * i = 0) : i * (k * A + A * k) = (k * A + A * k) * i := by
  have key : i * (k * A + A * k) - (k * A + A * k) * i =
      (i * k + k * i) * A - A * (i * k + k * i) + (i * A + A * i) * k - k * (i * A + A * i) := by
    noncomm_ring
  rw [h1, h2] at key
  simp only [zero_mul, mul_zero, sub_self, add_zero] at key
  exact sub_eq_zero.1 key

/-- Helper: ring-theoretic core of `aCoef_comm` (commutation with `ι_k`). -/
private theorem alg_comm_iota_eq {R : Type} [Ring R] (k A : R) (h1 : k * k = 0) :
    k * (k * A + A * k) = (k * A + A * k) * k := by
  have key : k * (k * A + A * k) - (k * A + A * k) * k = (k * k) * A - A * (k * k) := by
    noncomm_ring
  rw [h1] at key
  simp only [zero_mul, mul_zero, sub_self] at key
  exact sub_eq_zero.1 key

/-- **Z5.e (B.6).** If `𝒜` is odd and `aᵢ = 0` for `i < k` at `z`, then `a_k` commutes with every
`εⱼ` and with `ιᵢ` for `i ≤ k`. -/
theorem aCoef_comm {k : Fin (Module.finrank ℂ E)} {𝒜 : E → FibOp E r} {z : E}
    (hodd : ∀ j, epsOp j * 𝒜 z = -(𝒜 z * epsOp j)) (ha : ∀ i < k, aCoef i 𝒜 z = 0) :
    (∀ j, epsOp j * aCoef k 𝒜 z = aCoef k 𝒜 z * epsOp j) ∧
      ∀ i ≤ k, iotaOp i * aCoef k 𝒜 z = aCoef k 𝒜 z * iotaOp i := by
  refine ⟨fun j => ?_, fun i hi => ?_⟩
  · exact alg_comm_eps _ _ _ (if k = j then 1 else 0) (hodd j) (iotaOp_epsOp k j)
      (by split_ifs <;> simp only [one_mul, mul_one, zero_mul, mul_zero])
  · rcases hi.lt_or_eq with hlt | rfl
    · refine alg_comm_iota_lt _ _ _ ?_ (ha i hlt)
      rw [iotaOp_mul_comm i k]
      abel
    · exact alg_comm_iota_eq _ _ (iotaOp_mul_self _)

/-- Helper: contraction kills the unit of `Λ`. -/
private theorem ctrTot_one (j : Fin (Module.finrank ℂ E)) : ctrTot E j (1 : TotFibre E) = 0 := by
  have h1 : (1 : TotFibre E) = TotFibre.extEquivTotFibre E 1 := rfl
  have h2 : (1 : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) =
      algebraMap ℂ (ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) 1 := (map_one _).symm
  rw [h1]
  simp only [ctrTot, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [h2, CliffordAlgebra.contractLeft_algebraMap, map_zero]

/-- Helper: contraction kills forms of degree `0`. -/
private theorem ctrTot_ofDeg_zero' (j : Fin (Module.finrank ℂ E))
    (β : DolbeaultFibre E 0 ℂ) : ctrTot E j (TotFibre.ofDeg 0 β) = 0 := by
  have h1 : β = (form0Equiv E ℂ) ((form0Equiv E ℂ).symm β) :=
    ((form0Equiv E ℂ).apply_symm_apply β).symm
  have h2 : TotFibre.ofDeg 0 β = ((form0Equiv E ℂ).symm β) • (1 : TotFibre E) := by
    conv_lhs => rw [h1]
    have : (form0Equiv E ℂ) ((form0Equiv E ℂ).symm β) =
        ((form0Equiv E ℂ).symm β) • form0Equiv E ℂ 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, TotFibre.one_eq]
  rw [h2, map_smul, ctrTot_one, smul_zero]

/-- **Z5.e (B.7).** If `𝒜` is odd and every `aᵢ` vanishes at `z`, then `𝒜 z` preserves form degree
`0` (it maps `ofDeg 0`-valued vectors to `ofDeg 0`-valued vectors). -/
theorem preserves_deg_zero {𝒜 : E → FibOp E r} {z : E}
    (ha : ∀ i, aCoef i 𝒜 z = 0) (s : Fib E r)
    (hs : ∀ i, s i = TotFibre.ofDeg 0 (TotFibre.deg 0 (s i))) :
    ∀ i, 𝒜 z s i = TotFibre.ofDeg 0 (TotFibre.deg 0 (𝒜 z s i)) := by
  have h0 : ∀ j, (iotaOp j : FibOp E r) s = 0 := fun j => funext fun k => by
    show ctrTot E j (s k) = 0
    rw [hs k]
    exact ctrTot_ofDeg_zero' j _
  have h1 : ∀ j, (iotaOp j : FibOp E r) (𝒜 z s) = 0 := fun j => by
    have h := congrArg (fun T : FibOp E r => T s) (ha j)
    simp only [aCoef, add_apply, mul_apply_eq_comp, h0, map_zero, add_zero, zero_apply] at h
    exact h
  intro i
  exact eq_ofDeg_zero_of_ctrTot fun j => congrFun (h1 j) i

end Cohesive
