import Cohesivemodules.ChecksAlgebra
import Cohesivemodules.Forms.Realify
import Cohesivemodules.Forms.Fibre
import Cohesivemodules.Forms.Dbar
import Cohesivemodules.Forms.Leibniz

set_option linter.style.header false

/-!
# Checks: blueprint §9 checks and non-vacuity of definitions (part 2 of 2)

Split from `Checks.lean` for size;
continues `ChecksAlgebra.lean`.
-/

namespace Cohesive.Checks
open DirectSum TensorProduct

/-! ## F1, F2 sanity -/

open Manifold in
open scoped ContDiff in
/-- F1 non-vacuity: `ℂ` as a complex manifold is a real smooth manifold via `isManifold_real`. -/
example : IsManifold 𝓘(ℝ, ℂ) ∞ ℂ := isManifold_real (E := ℂ)

/-- F2.c sanity: `Λ^{0,1}(ℂ; ℂ)` is one-dimensional (spanned by `dz̄`). -/
example : Module.finrank ℂ (DolbeaultFibre ℂ 1 ℂ) = 1 := by
  rw [finrank_dolbeaultFibre, Module.finrank_self]
  rfl

/-- F2.c sanity: `Λ^{0,2}(ℂ; F) = 0`. -/
example : Subsingleton (DolbeaultFibre ℂ 2 ℂ) :=
  dolbeaultFibre_subsingleton (by rw [Module.finrank_self]; norm_num)

/-! ## K2: normalization of `∂̄` on `E = ℂ` (blueprint §9; ported from P2) -/

section K2

open Complex ComplexConjugate Conj ContinuousAlternatingMap

/-- K2: `v ↦ v̄` as a `ℂ`-linear map on `Conj ℂ`. -/
noncomputable def conjCLM : Conj ℂ →L[ℂ] ℂ where
  toFun v := conj (ofConj v)
  map_add' v w := by simp
  map_smul' c v := by simp [smul_eq_mul]
  cont := continuous_conj.comp continuous_id

@[simp] theorem conjCLM_apply (v : Conj ℂ) : conjCLM v = conj (ofConj v) := rfl

/-- K2: `dz̄` on `E = ℂ`: the `1`-form `v ↦ v̄` (conventions §6). -/
noncomputable def dzbar : DolbeaultFibre ℂ 1 ℂ := ofSubsingleton ℂ (Conj ℂ) ℂ (0 : Fin 1) conjCLM

/-- **K2 (i):** `∂̄ z̄ = dz̄`. -/
theorem K2_conj (x : ℂ) : dbar (form0 (fun z : ℂ => conj z)) x = dzbar := by
  have hd : HasFDerivAt (fun z : ℂ => conj z) (conjCLE : ℂ →L[ℝ] ℂ) x := conjCLE.hasFDerivAt
  rw [dbar_form0 hd.differentiableAt, hd.fderiv, dzbar]
  congr 1
  ext v
  simp only [antiPart_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply, conjCLM_apply,
    smul_eq_mul, map_mul, conj_I]
  ring_nf
  simp [I_sq]
  ring

/-- **K2 (ii):** `∂̄ z = 0`. -/
theorem K2_id (x : ℂ) : dbar (form0 (fun z : ℂ => z)) x = 0 := by
  have hd : HasFDerivAt (fun z : ℂ => z) (ContinuousLinearMap.id ℝ ℂ) x := hasFDerivAt_id x
  rw [dbar_form0 hd.differentiableAt, hd.fderiv]
  ext v
  simp only [ofSubsingleton_apply_apply, antiPart_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul]
  ring_nf
  simp [I_sq]

/-- **K2 (iii):** `∂̄ |z|² = z · dz̄`, with `|z|² = z z̄`. -/
theorem K2_normSq (x : ℂ) : dbar (form0 (fun z : ℂ => z * conj z)) x = x • dzbar := by
  have hd : HasFDerivAt (fun z : ℂ => z * conj z)
      (x • (conjCLE : ℂ →L[ℝ] ℂ) + conj x • ContinuousLinearMap.id ℝ ℂ) x :=
    (hasFDerivAt_id x).mul conjCLE.hasFDerivAt
  rw [dbar_form0 hd.differentiableAt, hd.fderiv, dzbar]
  ext v
  simp only [ofSubsingleton_apply_apply, antiPart_apply, ContinuousAlternatingMap.smul_apply,
    _root_.add_apply, _root_.smul_apply, ContinuousLinearEquiv.coe_coe, conjCLE_apply,
    ContinuousLinearMap.id_apply, conjCLM_apply, smul_eq_mul, map_mul, conj_I]
  ring_nf
  simp [I_sq]
  ring

end K2

/-! ## K3: `∂̄∂̄ = 0` and Leibniz on `ℂ²`, sign of `dz̄₁ ∧ dz̄₂` (blueprint §9) -/

section K3

open Complex ComplexConjugate Conj ContinuousAlternatingMap TotFibre

/-- K3: the coordinate `v ↦ v̄ⱼ` on `ℂ²`, as a `ℂ`-linear map on `Ē`. -/
noncomputable def conjCoord (j : Fin 2) : Conj (ℂ × ℂ) →L[ℂ] ℂ where
  toFun v := conj (if j = 0 then (ofConj v).1 else (ofConj v).2)
  map_add' v w := by
    split_ifs <;> simp
  map_smul' c v := by
    split_ifs <;> simp [smul_eq_mul]
  cont := by
    split_ifs
    · exact continuous_conj.comp (continuous_fst.comp continuous_id)
    · exact continuous_conj.comp (continuous_snd.comp continuous_id)

/-- K3: `dz̄₁` on `ℂ²`. -/
noncomputable def dzbar₁ : DolbeaultFibre (ℂ × ℂ) 1 ℂ :=
  ofSubsingleton ℂ (Conj (ℂ × ℂ)) ℂ (0 : Fin 1) (conjCoord 0)

/-- K3: `dz̄₂` on `ℂ²`. -/
noncomputable def dzbar₂ : DolbeaultFibre (ℂ × ℂ) 1 ℂ :=
  ofSubsingleton ℂ (Conj (ℂ × ℂ)) ℂ (0 : Fin 1) (conjCoord 1)

/-- K3 helper: the real-linear map `z ↦ z̄₁` on `ℂ²`. -/
private noncomputable def conjProj₁ : ℂ × ℂ →L[ℝ] ℂ :=
  (conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.fst ℝ ℂ ℂ)

/-- K3 helper: the real-linear map `z ↦ z̄₂` on `ℂ²`. -/
private noncomputable def conjProj₂ : ℂ × ℂ →L[ℝ] ℂ :=
  (conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)

/-- K3 helper: `D″ z̄₁ = conjCoord 0`. -/
private theorem antiPart_conjProj₁ : antiPart conjProj₁ = conjCoord 0 := by
  ext v
  simp only [antiPart_apply, conjProj₁, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearEquiv.coe_coe, conjCLE_apply, conjCoord,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, ite_true, smul_eq_mul,
    Prod.smul_fst, map_mul, conj_I]
  ring_nf
  simp [I_sq]
  ring

/-- K3 helper: `D″ z̄₂ = conjCoord 1`. -/
private theorem antiPart_conjProj₂ : antiPart conjProj₂ = conjCoord 1 := by
  ext v
  simp only [antiPart_apply, conjProj₂, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe, conjCLE_apply, conjCoord,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul,
    Prod.smul_snd, map_mul, conj_I, one_ne_zero, ↓reduceIte]
  ring_nf
  simp [I_sq]
  ring

/-- K3 helper: `∂̄ (P · η) = alternatizeUncurryFin ((D″P) ⊗ η)` for a real-linear `P` and a
constant `1`-form `η`. -/
private theorem dbar_linear_smul (P : ℂ × ℂ →L[ℝ] ℂ) (η : DolbeaultFibre (ℂ × ℂ) 1 ℂ) (x : ℂ × ℂ) :
    dbar (fun z : ℂ × ℂ => P z • η) x = alternatizeUncurryFin ((antiPart P).smulRight η) := by
  have hd : HasFDerivAt (fun z : ℂ × ℂ => P z • η) (P.smulRight η) x :=
    P.hasFDerivAt.smul_const η
  have h2 : antiPart (P.smulRight η) = (antiPart P).smulRight η := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [antiPart_apply, ContinuousLinearMap.smulRight_apply, smul_add, smul_smul]
    module
  rw [dbar, dbarPart, hd.fderiv, h2]

/-- K3 helper: `φ ∧ η = alternatizeUncurryFin (φ ⊗ η)` for `1`-forms. -/
private theorem wedge_eq (φ : Conj (ℂ × ℂ) →L[ℂ] ℂ) (η : DolbeaultFibre (ℂ × ℂ) 1 ℂ) :
    wedge (ofSubsingleton ℂ (Conj (ℂ × ℂ)) ℂ (0 : Fin 1) φ) η =
      alternatizeUncurryFin (φ.smulRight η) := by
  have hfin : Module.finrank ℂ (ℂ × ℂ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  unfold wedge
  rw [ofDeg_one_mul, deg_ofDeg_self (by omega)]
  rfl

/-- **K3 (normalization of `∧`):** `(dz̄₁ ∧ dz̄₂)(e₁, e₂) = 1` (no factorials). -/
theorem K3_wedge_eval :
    wedge dzbar₁ dzbar₂ ![toConj ((1 : ℂ), (0 : ℂ)), toConj ((0 : ℂ), (1 : ℂ))] = 1 := by
  have hfin : Module.finrank ℂ (ℂ × ℂ) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  unfold wedge
  rw [ofDeg_one_mul, deg_ofDeg_self (by omega)]
  rw [alternatizeUncurryFin_apply]
  simp [Fin.sum_univ_two, dzbar₁, dzbar₂, conjCoord]

/-- **K3 (sign):** `dz̄₂ ∧ dz̄₁ = -dz̄₁ ∧ dz̄₂`. -/
theorem K3_wedge_anticomm :
    (ofDeg 1 dzbar₂ * ofDeg 1 dzbar₁ : TotFibre (ℂ × ℂ)) = -(ofDeg 1 dzbar₁ * ofDeg 1 dzbar₂) := by
  rw [ofDeg_mul_comm]
  norm_num

/-- **K3:** `∂̄(z̄₁ z̄₂) = z̄₂ dz̄₁ + z̄₁ dz̄₂`. -/
theorem K3_dbar_fun (x : ℂ × ℂ) :
    dbar (form0 fun z : ℂ × ℂ => conj z.1 * conj z.2) x =
      conj x.2 • dzbar₁ + conj x.1 • dzbar₂ := by
  have hd : HasFDerivAt (fun z : ℂ × ℂ => conj z.1 * conj z.2)
      (conj x.1 • conjProj₂ + conj x.2 • conjProj₁) x :=
    (conjProj₁.hasFDerivAt (x := x)).mul (conjProj₂.hasFDerivAt (x := x))
  rw [dbar_form0 hd.differentiableAt, hd.fderiv, antiPart_add, antiPart_smul, antiPart_smul,
    antiPart_conjProj₁, antiPart_conjProj₂]
  ext v
  simp only [dzbar₁, dzbar₂, ofSubsingleton_apply_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, _root_.add_apply, _root_.smul_apply]
  ring

/-- **K3 (Leibniz):** `∂̄(z̄₁ dz̄₂) = dz̄₁ ∧ dz̄₂`. -/
theorem K3_dbar_oneForm (x : ℂ × ℂ) :
    dbar (fun z : ℂ × ℂ => conj z.1 • dzbar₂) x = wedge dzbar₁ dzbar₂ := by
  have h : (fun z : ℂ × ℂ => conj z.1 • dzbar₂) = fun z => conjProj₁ z • dzbar₂ := rfl
  rw [h, dbar_linear_smul, antiPart_conjProj₁]
  exact (wedge_eq (conjCoord 0) dzbar₂).symm

/-- **K3 (`∂̄∂̄ = 0`, computed):** `∂̄(z̄₂ dz̄₁ + z̄₁ dz̄₂) = dz̄₂ ∧ dz̄₁ + dz̄₁ ∧ dz̄₂ = 0`, the
explicit cancellation behind `∂̄∂̄(z̄₁ z̄₂) = 0` (independent of F4). -/
theorem K3_dbar_dbar (x : ℂ × ℂ) :
    dbar (fun z : ℂ × ℂ => conj z.2 • dzbar₁ + conj z.1 • dzbar₂) x = 0 := by
  show dbar (fun z : ℂ × ℂ => conjProj₂ z • dzbar₁ + conjProj₁ z • dzbar₂) x = 0
  have hd1 : DifferentiableAt ℝ (fun z : ℂ × ℂ => conjProj₂ z • dzbar₁) x :=
    (conjProj₂.hasFDerivAt.smul_const dzbar₁).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun z : ℂ × ℂ => conjProj₁ z • dzbar₂) x :=
    (conjProj₁.hasFDerivAt.smul_const dzbar₂).differentiableAt
  have hanti : wedge dzbar₂ dzbar₁ = -wedge dzbar₁ dzbar₂ := by
    unfold wedge
    rw [K3_wedge_anticomm, map_neg]
  refine (dbar_add hd1 hd2).trans ?_
  rw [dbar_linear_smul, dbar_linear_smul, antiPart_conjProj₁,
    antiPart_conjProj₂, ← wedge_eq (conjCoord 1) dzbar₁, ← wedge_eq (conjCoord 0) dzbar₂]
  change wedge dzbar₂ dzbar₁ + wedge dzbar₁ dzbar₂ = 0
  rw [hanti, neg_add_cancel]

end K3

end Cohesive.Checks
