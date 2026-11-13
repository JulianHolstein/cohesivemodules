import Cohesivemodules.Forms.Product
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

set_option linter.style.header false

/-!
# Z5.d: fibre operators for flat ∂̄-superconnections

Blueprint item Z5.d (`blueprint/blueprint-ll.md` §4 B.0, design decision L1; §11 v1.15).
The local model of a cohesive module in a frame of `r` generators (degrees `deg : Fin r → ℤ`) has
fibre `Fib E r = Λ ⊗ ℂ^r` (`r` copies of the total fibre `Λ = Λ^{0,•}(E)`, F5) and fibre operators
`FibOp E r = Fib E r →L[ℂ] Fib E r`, a finite-dimensional complex Banach algebra.
* `dzbarTot j ∈ Λ`: the 1-form `dz̄_j` (dual basis of `Conj.basis (finBasis ℂ E)`), through the
  exterior-algebra description of `Λ` (`extEquivTotFibre`, F5).
* `ctrTot j : Λ → Λ`: contraction with the j-th basis vector of `Ē` (Mathlib's
  `CliffordAlgebra.contractLeft`, `ExteriorAlgebra = CliffordAlgebra 0`).
* `epsOp j`, `iotaOp j`, `mulLeftOp t`: these maps on each of the `r` components.
* CAR relations: `εᵢεⱼ = −εⱼεᵢ`, `ιᵢιⱼ = −ιⱼιᵢ`, `ιᵢεⱼ + εⱼιᵢ = δᵢⱼ`.
* `sgnTot`: the grade involution `(−1)^q` on `Λ^q`.
* `totDegSub deg m`, `IsOfTotDeg deg d T`: total degree (form degree plus generator degree).
* Λ-linearity from the `εⱼ` (`commute_mulLeftOp_of_eps`, `mulLeftOp_of_eps_anticomm`) and the
  kernel lemma (`eq_ofDeg_zero_of_ctrTot`: killed by every contraction ⇒ form degree 0).

## Deviations
* Contraction is defined through the exterior algebra (Mathlib's Clifford contraction), not
  through Z4.d's `ctr` on each `DolbeaultFibre`; the two agree degreewise (not needed here).
-/

noncomputable section

namespace Cohesive

open Conj

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Z5.d.** The dual basis of `Conj.basis (finBasis ℂ E)`: the 1-forms `dz̄_j` as covectors on
`Ē`. -/
def dualConjBasis : Module.Basis (Fin (Module.finrank ℂ E)) ℂ (Module.Dual ℂ (Conj E)) :=
  (Conj.basis (Module.finBasis ℂ E)).dualBasis

/-- **Z5.d.** The 1-form `dz̄_j` in the total fibre `Λ`. -/
def dzbarTot (j : Fin (Module.finrank ℂ E)) : TotFibre E :=
  TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ (dualConjBasis E j))

/-- **Z5.d.** Contraction of `Λ` with the j-th basis vector `b_j` of `Ē` (Clifford contraction
with `eval b_j`, transported along `extEquivTotFibre`). -/
def ctrTot (j : Fin (Module.finrank ℂ E)) : TotFibre E →ₗ[ℂ] TotFibre E :=
  (TotFibre.extEquivTotFibre E).toLinearMap ∘ₗ
    CliffordAlgebra.contractLeft
      (Module.Dual.eval ℂ (Conj E) (Conj.basis (Module.finBasis ℂ E) j)) ∘ₗ
    (TotFibre.extEquivTotFibre E).symm.toLinearMap

/-- **Z5.d.** The grade involution of `Λ`: `(−1)^q` on `Λ^{0,q}`. -/
def sgnTot : TotFibre E →ₗ[ℂ] TotFibre E where
  toFun t q := ((-1 : ℂ) ^ (q : ℕ)) • t q
  map_add' s t := by funext q; exact smul_add _ _ _
  map_smul' c t := by funext q; exact smul_comm _ c _

/-- **Z5.d.** The fibre of the local model: `r` copies of `Λ`. -/
abbrev Fib (r : ℕ) : Type := Fin r → TotFibre E

/-- **Z5.d.** Fibre operators. -/
abbrev FibOp (r : ℕ) : Type := Fib E r →L[ℂ] Fib E r

variable {E} {r : ℕ}

/-- **Z5.d.** A linear map of `Λ`, applied in each of the `r` components. -/
def compOp (L : TotFibre E →ₗ[ℂ] TotFibre E) : FibOp E r :=
  LinearMap.toContinuousLinearMap (LinearMap.pi fun i => L ∘ₗ LinearMap.proj i)

/-- Z5.d: `compOp` acts componentwise (rfl). -/
@[simp] theorem compOp_apply (L : TotFibre E →ₗ[ℂ] TotFibre E) (s : Fib E r) (i : Fin r) :
    compOp L s i = L (s i) := rfl

/-- **Z5.d.** Left multiplication by `t ∈ Λ` in each component. -/
def mulLeftOp (t : TotFibre E) : FibOp E r := compOp (LinearMap.mulLeft ℂ t)

/-- **Z5.d.** Left multiplication by `dz̄_j`. -/
def epsOp (j : Fin (Module.finrank ℂ E)) : FibOp E r := mulLeftOp (dzbarTot E j)

/-- **Z5.d.** Contraction with `b_j` in each component. -/
def iotaOp (j : Fin (Module.finrank ℂ E)) : FibOp E r := compOp (ctrTot E j)

/-- **Z5.d.** The grade involution in each component. -/
def sgnOp : FibOp E r := compOp (sgnTot E)

/-! ## Relations -/

/-- **Z5.d (B.0).** `dz̄_i dz̄_j = −dz̄_j dz̄_i`. -/
theorem dzbarTot_mul_comm (i j : Fin (Module.finrank ℂ E)) :
    dzbarTot E i * dzbarTot E j = -(dzbarTot E j * dzbarTot E i) := by
  simp only [dzbarTot, ← TotFibre.extEquivTotFibre_mul, ← map_neg]
  exact congrArg _ (eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _))

/-- Helper: `ctrTot` on the image of `Φ_tot` is Clifford contraction. -/
private theorem ctrTot_ext (j : Fin (Module.finrank ℂ E))
    (x : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) :
    ctrTot E j (TotFibre.extEquivTotFibre E x) = TotFibre.extEquivTotFibre E
      (CliffordAlgebra.contractLeft
        (Module.Dual.eval ℂ (Conj E) (Conj.basis (Module.finBasis ℂ E) j)) x) := by
  simp only [ctrTot, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

/-- **Z5.d (B.0).** Leibniz rule of the contraction:
`ι_j (dz̄_i t) = δᵢⱼ t − dz̄_i ι_j t`. -/
theorem ctrTot_dzbarTot_mul (i j : Fin (Module.finrank ℂ E)) (t : TotFibre E) :
    ctrTot E j (dzbarTot E i * t) = (if i = j then t else 0) - dzbarTot E i * ctrTot E j t := by
  obtain ⟨y, rfl⟩ := (TotFibre.extEquivTotFibre E).surjective t
  have h := CliffordAlgebra.contractLeft_ι_mul
    (Module.Dual.eval ℂ (Conj E) (Conj.basis (Module.finBasis ℂ E) j)) (dualConjBasis E i) y
  rw [dzbarTot, ← TotFibre.extEquivTotFibre_mul, ctrTot_ext, ctrTot_ext,
    ← TotFibre.extEquivTotFibre_mul]
  have h1 : CliffordAlgebra.ι 0 (dualConjBasis E i) =
    ExteriorAlgebra.ι ℂ (dualConjBasis E i) := rfl
  rw [h1] at h
  rw [h, map_sub, map_smul]
  simp only [Module.Dual.eval_apply, dualConjBasis, Module.Basis.dualBasis_apply_self]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, one_smul]
  · have : j ≠ i := fun h => hij h.symm
    simp only [this, hij, ite_false, zero_smul]

/-- Helper: `mulLeftOp` acts componentwise by left multiplication. -/
private theorem mulLeftOp_apply (t : TotFibre E) (s : Fib E r) (i : Fin r) :
    (mulLeftOp t : FibOp E r) s i = t * s i := rfl

/-- Helper: `epsOp` acts componentwise by left multiplication by `dz̄_j`. -/
private theorem epsOp_apply (j : Fin (Module.finrank ℂ E)) (s : Fib E r) (i : Fin r) :
    (epsOp j : FibOp E r) s i = dzbarTot E j * s i := rfl

/-- Helper: `iotaOp` acts componentwise by `ctrTot`. -/
private theorem iotaOp_apply (j : Fin (Module.finrank ℂ E)) (s : Fib E r) (i : Fin r) :
    (iotaOp j : FibOp E r) s i = ctrTot E j (s i) := rfl

/-- Helper: `sgnOp` acts componentwise by `sgnTot`. -/
private theorem sgnOp_apply (s : Fib E r) (i : Fin r) :
    (sgnOp : FibOp E r) s i = sgnTot E (s i) := rfl

/-- Helper: contractions anticommute on `Λ`. -/
private theorem ctrTot_ctrTot (i j : Fin (Module.finrank ℂ E)) (t : TotFibre E) :
    ctrTot E i (ctrTot E j t) = -ctrTot E j (ctrTot E i t) := by
  obtain ⟨y, rfl⟩ := (TotFibre.extEquivTotFibre E).surjective t
  rw [ctrTot_ext, ctrTot_ext, ctrTot_ext, ctrTot_ext, ← map_neg]
  exact congrArg _ (CliffordAlgebra.contractLeft_comm _ _ _)

/-- Helper: `ι_j ι_j = 0` on `Λ`. -/
private theorem ctrTot_ctrTot_self (j : Fin (Module.finrank ℂ E)) (t : TotFibre E) :
    ctrTot E j (ctrTot E j t) = 0 := by
  obtain ⟨y, rfl⟩ := (TotFibre.extEquivTotFibre E).surjective t
  simp only [ctrTot_ext, CliffordAlgebra.contractLeft_contractLeft, map_zero]

/-- **Z5.d (B.0).** `εᵢεⱼ = −εⱼεᵢ`. -/
theorem epsOp_mul_comm (i j : Fin (Module.finrank ℂ E)) :
    (epsOp i : FibOp E r) * epsOp j = -(epsOp j * epsOp i) := by
  refine ContinuousLinearMap.ext fun s => funext fun k => ?_
  simp only [mul_apply_eq_comp, neg_apply, epsOp_apply,
    Pi.neg_apply]
  rw [← mul_assoc, ← mul_assoc, dzbarTot_mul_comm, neg_mul]

/-- **Z5.d (B.0).** `ιᵢιⱼ = −ιⱼιᵢ`. -/
theorem iotaOp_mul_comm (i j : Fin (Module.finrank ℂ E)) :
    (iotaOp i : FibOp E r) * iotaOp j = -(iotaOp j * iotaOp i) := by
  refine ContinuousLinearMap.ext fun s => funext fun k => ?_
  simp only [mul_apply_eq_comp, neg_apply, iotaOp_apply,
    Pi.neg_apply]
  exact ctrTot_ctrTot i j _

/-- **Z5.d (B.0).** `ιⱼιⱼ = 0`. -/
theorem iotaOp_mul_self (j : Fin (Module.finrank ℂ E)) : (iotaOp j : FibOp E r) * iotaOp j = 0 := by
  refine ContinuousLinearMap.ext fun s => funext fun k => ?_
  simp only [mul_apply_eq_comp, iotaOp_apply, zero_apply,
    Pi.zero_apply]
  exact ctrTot_ctrTot_self j _

/-- **Z5.d (B.0).** `ιᵢεⱼ + εⱼιᵢ = δᵢⱼ`. -/
theorem iotaOp_epsOp (i j : Fin (Module.finrank ℂ E)) :
    (iotaOp i : FibOp E r) * epsOp j + epsOp j * iotaOp i = if i = j then 1 else 0 := by
  refine ContinuousLinearMap.ext fun s => funext fun k => ?_
  simp only [add_apply, mul_apply_eq_comp, iotaOp_apply,
    epsOp_apply, Pi.add_apply]
  rw [ctrTot_dzbarTot_mul]
  by_cases hij : j = i
  · subst hij
    simp only [ite_true, sub_add_cancel, one_apply_eq_self]
  · have : ¬ i = j := fun h => hij h.symm
    simp only [hij, this, ite_false, zero_sub, neg_add_cancel, zero_apply]
    rfl

/-- Helper: `σ` is `(-1)^k` on a homogeneous element of degree `k`. -/
private theorem sgnTot_ofDeg (k : ℕ) (γ : DolbeaultFibre E k ℂ) :
    sgnTot E (TotFibre.ofDeg k γ) = (-1 : ℂ) ^ k • TotFibre.ofDeg k γ := by
  funext i
  show (-1 : ℂ) ^ (i : ℕ) • (if h : k = (i : ℕ) then DolbeaultFibre.cast h γ else 0) =
    (-1 : ℂ) ^ k • (if h : k = (i : ℕ) then DolbeaultFibre.cast h γ else 0)
  by_cases h : k = (i : ℕ)
  · simp only [h, ↓reduceDIte]
  · simp only [h, ↓reduceDIte, smul_zero]

/-- Helper: `σ 1 = 1`. -/
private theorem sgnTot_one : sgnTot E (1 : TotFibre E) = 1 := by
  rw [TotFibre.one_eq, sgnTot_ofDeg, pow_zero, one_smul]

/-- Helper: `dz̄`-type 1-forms `Φ(ι f)` are homogeneous of degree one. -/
private theorem exists_ofDeg_one (f : Module.Dual ℂ (Conj E)) :
    ∃ α : DolbeaultFibre E 1 ℂ, TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ f) =
      TotFibre.ofDeg 1 α := by
  have hm : ExteriorAlgebra.ι ℂ f ∈ ⋀[ℂ]^1 (Module.Dual ℂ (Conj E)) := by
    show _ ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : _ →ₗ[ℂ] ExteriorAlgebra ℂ _) ^ 1
    rw [pow_one]
    exact LinearMap.mem_range_self _ f
  exact ⟨extToFibre E 1 ⟨ExteriorAlgebra.ι ℂ f, hm⟩,
    TotFibre.extEquivTotFibre_of_mem (E := E) (q := 1) ⟨ExteriorAlgebra.ι ℂ f, hm⟩⟩

/-- Helper: `σ (Φ(ι f) · t) = −Φ(ι f) · σ t`. -/
private theorem sgnTot_ι_mul (f : Module.Dual ℂ (Conj E)) (t : TotFibre E) :
    sgnTot E (TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ f) * t) =
      -(TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ f) * sgnTot E t) := by
  obtain ⟨α, hα⟩ := exists_ofDeg_one (E := E) f
  rw [hα]
  conv_lhs => rw [← TotFibre.sum_ofDeg_deg t]
  conv_rhs => rw [← TotFibre.sum_ofDeg_deg t]
  rw [Finset.mul_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h := TotFibre.ofDeg_mul_ofDeg α (TotFibre.deg q t)
  rw [sgnTot_ofDeg, mul_smul_comm, h, sgnTot_ofDeg, pow_add, pow_one, mul_smul, neg_smul,
    one_smul]

/-- Helper: `σ` of a 1-form `dz̄_j` is `−dz̄_j`. -/
private theorem sgnTot_dzbarTot (j : Fin (Module.finrank ℂ E)) :
    sgnTot E (dzbarTot E j) = -dzbarTot E j := by
  have h := sgnTot_ι_mul (E := E) (dualConjBasis E j) 1
  rwa [mul_one, sgnTot_one, mul_one] at h

/-- Helper: `σ` is the transport of the Clifford involution. -/
private theorem sgnTot_ext (x : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) :
    sgnTot E (TotFibre.extEquivTotFibre E x) =
      TotFibre.extEquivTotFibre E (CliffordAlgebra.involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, map_smul, map_smul]
    show r • sgnTot E (1 : TotFibre E) = r • (1 : TotFibre E)
    rw [sgnTot_one]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | ι_mul x m hx =>
    rw [TotFibre.extEquivTotFibre_mul]
    show sgnTot E (TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ m) *
      TotFibre.extEquivTotFibre E x) = TotFibre.extEquivTotFibre E
        (CliffordAlgebra.involute (ExteriorAlgebra.ι ℂ m * x))
    rw [sgnTot_ι_mul, hx, map_mul CliffordAlgebra.involute, CliffordAlgebra.involute_ι, neg_mul,
      map_neg, TotFibre.extEquivTotFibre_mul]

/-- Helper: `σ` is multiplicative. -/
private theorem sgnTot_mul (a b : TotFibre E) :
    sgnTot E (a * b) = sgnTot E a * sgnTot E b := by
  obtain ⟨x, rfl⟩ := (TotFibre.extEquivTotFibre E).surjective a
  obtain ⟨y, rfl⟩ := (TotFibre.extEquivTotFibre E).surjective b
  rw [← TotFibre.extEquivTotFibre_mul, sgnTot_ext, sgnTot_ext, sgnTot_ext, map_mul,
    TotFibre.extEquivTotFibre_mul]

/-- **Z5.d (B.0).** `σ (dz̄_j t) = −dz̄_j σ(t)`, i.e. `σ εⱼ = −εⱼ σ`. -/
theorem sgnOp_epsOp (j : Fin (Module.finrank ℂ E)) :
    (sgnOp : FibOp E r) * epsOp j = -(epsOp j * sgnOp) := by
  refine ContinuousLinearMap.ext fun s => funext fun k => ?_
  simp only [mul_apply_eq_comp, neg_apply, sgnOp_apply, epsOp_apply, Pi.neg_apply]
  exact sgnTot_ι_mul _ _

/-! ## Λ-linearity -/

/-- Helper: `mulLeftOp` is multiplicative. -/
private theorem mulLeftOp_mul (s t : TotFibre E) :
    (mulLeftOp (s * t) : FibOp E r) = mulLeftOp s * mulLeftOp t := by
  refine ContinuousLinearMap.ext fun u => funext fun k => ?_
  simp only [mul_apply_eq_comp, mulLeftOp_apply, mul_assoc]

/-- Helper: `mulLeftOp` is additive. -/
private theorem mulLeftOp_add (s t : TotFibre E) :
    (mulLeftOp (s + t) : FibOp E r) = mulLeftOp s + mulLeftOp t := by
  refine ContinuousLinearMap.ext fun u => funext fun k => ?_
  simp only [add_apply, mulLeftOp_apply, add_mul, Pi.add_apply]

/-- Helper: `mulLeftOp` is homogeneous. -/
private theorem mulLeftOp_smul (c : ℂ) (t : TotFibre E) :
    (mulLeftOp (c • t) : FibOp E r) = c • mulLeftOp t := by
  refine ContinuousLinearMap.ext fun u => funext fun k => ?_
  simp only [smul_apply, mulLeftOp_apply, smul_mul_assoc, Pi.smul_apply]

/-- Helper: `mulLeftOp` commutes with negation. -/
private theorem mulLeftOp_neg (t : TotFibre E) :
    (mulLeftOp (-t) : FibOp E r) = -mulLeftOp t := by
  refine ContinuousLinearMap.ext fun u => funext fun k => ?_
  simp only [neg_apply, mulLeftOp_apply, neg_mul, Pi.neg_apply]

/-- Helper: `mulLeftOp 1 = 1`. -/
private theorem mulLeftOp_one : (mulLeftOp (1 : TotFibre E) : FibOp E r) = 1 := by
  refine ContinuousLinearMap.ext fun u => funext fun k => ?_
  simp only [mulLeftOp_apply, one_mul, one_apply_eq_self]

/-- Helper: `mulLeftOp` commutes with finite sums. -/
private theorem mulLeftOp_sum {ι : Type} (s : Finset ι) (f : ι → TotFibre E) :
    (mulLeftOp (∑ i ∈ s, f i) : FibOp E r) = ∑ i ∈ s, mulLeftOp (f i) :=
  map_sum (AddMonoidHom.mk' (mulLeftOp (E := E) (r := r)) mulLeftOp_add) f s

/-- Helper: `Φ_tot (algebraMap r) = r • 1`. -/
private theorem ext_algebraMap (c : ℂ) :
    TotFibre.extEquivTotFibre E (algebraMap ℂ (ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) c) =
      c • (1 : TotFibre E) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul]
  rfl

/-- Helper: `Φ_tot (ι f)` is a combination of the `dz̄_j`. -/
private theorem ext_ι_expand (f : Module.Dual ℂ (Conj E)) :
    TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ f) =
      ∑ j, (dualConjBasis E).repr f j • dzbarTot E j := by
  conv_lhs => rw [← (dualConjBasis E).sum_repr f]
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul]; rfl

/-- Helper: `mulLeftOp (Φ_tot (ι f))` is a combination of the `εⱼ`. -/
private theorem mulLeftOp_ι_expand (f : Module.Dual ℂ (Conj E)) :
    (mulLeftOp (TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ f)) : FibOp E r) =
      ∑ j, (dualConjBasis E).repr f j • (epsOp j : FibOp E r) := by
  rw [ext_ι_expand, mulLeftOp_sum]
  exact Finset.sum_congr rfl fun j _ => mulLeftOp_smul _ _

/-- **Z5.d.** An operator commuting with every `εⱼ` commutes with left multiplication by every
`t ∈ Λ` (`Λ` is generated by the `dz̄_j`). -/
theorem commute_mulLeftOp_of_eps {T : FibOp E r} (h : ∀ j, epsOp j * T = T * epsOp j)
    (t : TotFibre E) : mulLeftOp t * T = T * mulLeftOp t := by
  obtain ⟨x, rfl⟩ := (TotFibre.extEquivTotFibre E).surjective t
  induction x using ExteriorAlgebra.induction with
  | algebraMap c =>
    rw [ext_algebraMap, mulLeftOp_smul, mulLeftOp_one, smul_mul_assoc, mul_smul_comm, one_mul,
      mul_one]
  | ι f =>
    rw [mulLeftOp_ι_expand, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_mul_assoc, mul_smul_comm, h]
  | mul a b ha hb =>
    rw [TotFibre.extEquivTotFibre_mul, mulLeftOp_mul, mul_assoc, hb, ← mul_assoc, ha,
      mul_assoc]
  | add a b ha hb =>
    rw [map_add, mulLeftOp_add, add_mul, mul_add, ha, hb]

/-- Helper: `σ (Φ_tot (ι f)) = −Φ_tot (ι f)`. -/
private theorem sgnTot_ι (f : Module.Dual ℂ (Conj E)) :
    sgnTot E (TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ f)) =
      -TotFibre.extEquivTotFibre E (ExteriorAlgebra.ι ℂ f) := by
  have h := sgnTot_ι_mul (E := E) f 1
  rwa [mul_one, sgnTot_one, mul_one] at h

/-- **Z5.d.** An operator anticommuting with every `εⱼ` satisfies `T (t·s) = σ(t)·T s`. -/
theorem mulLeftOp_of_eps_anticomm {T : FibOp E r} (h : ∀ j, epsOp j * T = -(T * epsOp j))
    (t : TotFibre E) : T * mulLeftOp t = mulLeftOp (sgnTot E t) * T := by
  obtain ⟨x, rfl⟩ := (TotFibre.extEquivTotFibre E).surjective t
  induction x using ExteriorAlgebra.induction with
  | algebraMap c =>
    rw [ext_algebraMap, map_smul, sgnTot_one, mulLeftOp_smul, mulLeftOp_one, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
  | ι f =>
    rw [sgnTot_ι, mulLeftOp_neg, mulLeftOp_ι_expand, Finset.mul_sum]
    refine Eq.trans ?_ (ContinuousLinearMap.neg_comp _ _).symm
    show _ = -((∑ j, (dualConjBasis E).repr f j • (epsOp j : FibOp E r)) * T)
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      rw [mul_smul_comm, smul_mul_assoc, h j, smul_neg, neg_neg]
  | mul a b ha hb =>
    rw [TotFibre.extEquivTotFibre_mul, sgnTot_mul, mulLeftOp_mul, mulLeftOp_mul, ← mul_assoc,
      ha, mul_assoc, hb, mul_assoc]
  | add a b ha hb =>
    rw [map_add, map_add, mulLeftOp_add, mulLeftOp_add, add_mul, mul_add, ha, hb]

/-- Helper: contraction lowers the exterior power degree by one. -/
private theorem contr_mem {M : Type} [AddCommGroup M] [Module ℂ M] (d : Module.Dual ℂ M)
    (p : ℕ) : ∀ x ∈ ⋀[ℂ]^(p + 1) M,
      (CliffordAlgebra.contractLeft d : ExteriorAlgebra ℂ M →ₗ[ℂ] ExteriorAlgebra ℂ M) x ∈
        ⋀[ℂ]^p M := by
  induction p with
  | zero =>
    intro x hx
    have hx' : x ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : M →ₗ[ℂ] ExteriorAlgebra ℂ M) := by
      simpa only [zero_add, pow_one] using hx
    obtain ⟨a, rfl⟩ := hx'
    have : (CliffordAlgebra.contractLeft d : ExteriorAlgebra ℂ M →ₗ[ℂ] ExteriorAlgebra ℂ M)
      (ExteriorAlgebra.ι ℂ a) = algebraMap ℂ _ (d a) := CliffordAlgebra.contractLeft_ι _ d a
    rw [this]
    show _ ∈ (1 : Submodule ℂ (ExteriorAlgebra ℂ M))
    exact Submodule.mem_one.2 ⟨d a, rfl⟩
  | succ p ih =>
    intro x hx
    have hx' : x ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ : M →ₗ[ℂ] ExteriorAlgebra ℂ M)) ^
      (p + 1 + 1) := hx
    rw [pow_succ'] at hx'
    refine Submodule.mul_induction_on hx' ?_ ?_
    · intro m hm n hn
      obtain ⟨a, rfl⟩ := hm
      have h := CliffordAlgebra.contractLeft_ι_mul d a n
      show (CliffordAlgebra.contractLeft d : ExteriorAlgebra ℂ M →ₗ[ℂ] ExteriorAlgebra ℂ M)
        (ExteriorAlgebra.ι ℂ a * n) ∈ _
      rw [h]
      refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hn) ?_
      show _ ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ : M →ₗ[ℂ] ExteriorAlgebra ℂ M)) ^ (p + 1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul ⟨a, rfl⟩ (ih n hn)
    · intro x y hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- Helper: contraction kills the exterior power of degree `0`. -/
private theorem contr_zero {M : Type} [AddCommGroup M] [Module ℂ M] (d : Module.Dual ℂ M)
    {x : ExteriorAlgebra ℂ M} (hx : x ∈ ⋀[ℂ]^0 M) :
    (CliffordAlgebra.contractLeft d : ExteriorAlgebra ℂ M →ₗ[ℂ] ExteriorAlgebra ℂ M) x = 0 := by
  have hx' : x ∈ (1 : Submodule ℂ (ExteriorAlgebra ℂ M)) := by
    simpa only [pow_zero] using hx
  obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hx'
  exact CliffordAlgebra.contractLeft_algebraMap _ d c

/-- Helper: `Σ_j ι(dz̄_j) · (b_j ⌋ ι a) = ι a`, rewritten as a sum of `a (b_j) • ι(dz̄_j)`. -/
private theorem sum_ι_eval (a : Module.Dual ℂ (Conj E)) :
    ∑ j, Module.Dual.eval ℂ (Conj E) (Conj.basis (Module.finBasis ℂ E) j) a •
      ExteriorAlgebra.ι ℂ (dualConjBasis E j) = ExteriorAlgebra.ι ℂ a := by
  conv_rhs => rw [← (dualConjBasis E).sum_repr a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  simp only [Module.Dual.eval_apply, dualConjBasis, Module.Basis.dualBasis_repr]

/-- Helper: Euler identity `Σ_j dz̄_j ∧ ι_j x = k x` on `⋀^k`. -/
private theorem euler_ext (k : ℕ) : ∀ x ∈ ⋀[ℂ]^k (Module.Dual ℂ (Conj E)),
    ∑ j, ExteriorAlgebra.ι ℂ (dualConjBasis E j) *
      (CliffordAlgebra.contractLeft (Module.Dual.eval ℂ (Conj E)
        (Conj.basis (Module.finBasis ℂ E) j)) :
          ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E)) →ₗ[ℂ]
            ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) x = (k : ℂ) • x := by
  induction k with
  | zero =>
    intro x hx
    simp only [contr_zero _ hx, mul_zero, Finset.sum_const_zero, Nat.cast_zero, zero_smul]
  | succ k ih =>
    intro x hx
    have hx' : x ∈ (LinearMap.range (ExteriorAlgebra.ι ℂ :
      Module.Dual ℂ (Conj E) →ₗ[ℂ] ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E)))) ^ (k + 1) := hx
    rw [pow_succ'] at hx'
    refine Submodule.mul_induction_on hx' ?_ ?_
    · intro m hm n hn
      obtain ⟨a, rfl⟩ := hm
      have step : ∀ j, ExteriorAlgebra.ι ℂ (dualConjBasis E j) *
          (CliffordAlgebra.contractLeft (Module.Dual.eval ℂ (Conj E)
            (Conj.basis (Module.finBasis ℂ E) j)) :
              ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E)) →ₗ[ℂ]
                ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) (ExteriorAlgebra.ι ℂ a * n) =
          (Module.Dual.eval ℂ (Conj E) (Conj.basis (Module.finBasis ℂ E) j) a •
            ExteriorAlgebra.ι ℂ (dualConjBasis E j)) * n +
          ExteriorAlgebra.ι ℂ a * (ExteriorAlgebra.ι ℂ (dualConjBasis E j) *
            (CliffordAlgebra.contractLeft (Module.Dual.eval ℂ (Conj E)
              (Conj.basis (Module.finBasis ℂ E) j)) :
                ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E)) →ₗ[ℂ]
                  ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) n) := by
        intro j
        have hc := ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (dualConjBasis E j) a
        have hc' : ExteriorAlgebra.ι ℂ (dualConjBasis E j) * ExteriorAlgebra.ι ℂ a =
          -(ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ (dualConjBasis E j)) :=
          eq_neg_of_add_eq_zero_left hc
        rw [CliffordAlgebra.contractLeft_ι_mul, mul_sub, ← mul_assoc, hc', neg_mul, mul_assoc,
          sub_neg_eq_add, mul_smul_comm, smul_mul_assoc]
      show ∑ j, ExteriorAlgebra.ι ℂ (dualConjBasis E j) *
        (CliffordAlgebra.contractLeft (Module.Dual.eval ℂ (Conj E)
          (Conj.basis (Module.finBasis ℂ E) j)) :
            ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E)) →ₗ[ℂ]
              ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) (ExteriorAlgebra.ι ℂ a * n) =
        _ • (ExteriorAlgebra.ι ℂ a * n)
      rw [Finset.sum_congr rfl fun j _ => step j, Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_ι_eval, ← Finset.mul_sum, ih n hn, mul_smul_comm, Nat.cast_succ, add_smul, one_smul,
        add_comm]
    · intro x y hx hy
      simp only [map_add, mul_add, Finset.sum_add_distrib, hx, hy, smul_add]

/-- Helper: Euler identity on a homogeneous element of the total fibre. -/
private theorem euler_ofDeg (k : ℕ) (β : DolbeaultFibre E k ℂ) :
    ∑ j, dzbarTot E j * ctrTot E j (TotFibre.ofDeg k β) = (k : ℂ) • TotFibre.ofDeg k β := by
  have hy := TotFibre.extEquivTotFibre_of_mem (E := E) ((extEquivFibre E k).symm β)
  have hβ : extToFibre E k ((extEquivFibre E k).symm β) = β :=
    (extEquivFibre E k).apply_symm_apply β
  rw [hβ] at hy
  rw [← hy, ← map_smul, ← euler_ext k _ ((extEquivFibre E k).symm β).2, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ctrTot_ext, dzbarTot, ← TotFibre.extEquivTotFibre_mul]

/-- **Z5.d (kernel lemma).** An element of `Λ` killed by every contraction lies in form degree
`0`. -/
theorem eq_ofDeg_zero_of_ctrTot {t : TotFibre E} (h : ∀ j, ctrTot E j t = 0) :
    t = TotFibre.ofDeg 0 (TotFibre.deg 0 t) := by
  have ht := TotFibre.sum_ofDeg_deg t
  have hsum : ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
      (q : ℂ) • TotFibre.ofDeg q (TotFibre.deg q t) = 0 := by
    calc _ = ∑ q ∈ Finset.range (Module.finrank ℂ E + 1), ∑ j,
          dzbarTot E j * ctrTot E j (TotFibre.ofDeg q (TotFibre.deg q t)) :=
        Finset.sum_congr rfl fun q _ => (euler_ofDeg q _).symm
      _ = ∑ j, dzbarTot E j * ctrTot E j (∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
          TotFibre.ofDeg q (TotFibre.deg q t)) := by
        rw [Finset.sum_comm]
        simp only [map_sum, Finset.mul_sum]
      _ = 0 := by
        rw [ht]
        simp only [h, mul_zero, Finset.sum_const_zero]
  have hp : ∀ p ∈ Finset.range (Module.finrank ℂ E + 1), 1 ≤ p → TotFibre.deg p t = 0 := by
    intro p hp hp1
    have hpn : p ≤ Module.finrank ℂ E := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
    have h2 := congrArg (TotFibre.deg p) hsum
    rw [map_sum, map_zero, Finset.sum_eq_single p] at h2
    · rw [map_smul, TotFibre.deg_ofDeg_self hpn] at h2
      exact (smul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 (by omega))
    · intro q _ hq
      rw [map_smul, TotFibre.deg_ofDeg_ne (Ne.symm hq), smul_zero]
    · intro hnot
      exact absurd hp hnot
  conv_lhs => rw [← ht]
  rw [Finset.sum_eq_single 0]
  · intro q hq hq0
    rw [hp q hq (by omega), map_zero]
  · intro hnot
    exact absurd (Finset.mem_range.2 (Nat.succ_pos _)) hnot

/-! ## Total degree -/

/-- **Z5.d.** Elements of `Fib E r` of total degree `m`: component `i` has form degree
`m − deg i`. -/
def totDegSub (deg : Fin r → ℤ) (m : ℤ) : Submodule ℂ (Fib E r) where
  carrier := {s | ∀ (i : Fin r) (q : Fin (Module.finrank ℂ E + 1)),
    ((q : ℕ) : ℤ) + deg i ≠ m → s i q = 0}
  add_mem' ha hb i q hq := by
    show _ + _ = (0 : DolbeaultFibre E q ℂ)
    rw [ha i q hq, hb i q hq, add_zero]
  zero_mem' _ _ _ := rfl
  smul_mem' c s hs i q hq := by
    show c • _ = (0 : DolbeaultFibre E q ℂ)
    rw [hs i q hq, smul_zero]

/-- **Z5.d.** `T` has total degree `d`: it maps total degree `m` to `m + d`. -/
def IsOfTotDeg (deg : Fin r → ℤ) (d : ℤ) (T : FibOp E r) : Prop :=
  ∀ m : ℤ, ∀ s ∈ totDegSub (E := E) deg m, T s ∈ totDegSub (E := E) deg (m + d)

/-- Helper: `t ∈ Λ` is homogeneous of form degree `a ∈ ℤ` (all other components vanish). -/
private def HasDegZ (a : ℤ) (t : TotFibre E) : Prop :=
  ∀ q : Fin (Module.finrank ℂ E + 1), ((q : ℕ) : ℤ) ≠ a → t q = 0

/-- Helper: `0` is homogeneous of every degree. -/
private theorem hasDegZ_zero (a : ℤ) : HasDegZ a (0 : TotFibre E) := fun _ _ => rfl

omit [FiniteDimensional ℂ E] in
/-- Helper: `ofDeg k γ` is homogeneous of degree `k`. -/
private theorem hasDegZ_ofDeg (k : ℕ) (γ : DolbeaultFibre E k ℂ) :
    HasDegZ (k : ℤ) (TotFibre.ofDeg k γ) := by
  intro q hq
  have h : ¬ k = (q : ℕ) := fun h => hq (by rw [h])
  show (if h : k = (q : ℕ) then DolbeaultFibre.cast h γ else 0 : DolbeaultFibre E q ℂ) = 0
  simp only [h, ↓reduceDIte]

omit [FiniteDimensional ℂ E] in
/-- Helper: the `q`-th component of `t` is `t q` for `q ≤ n`. -/
private theorem deg_of_lt {q : ℕ} (hq : q < Module.finrank ℂ E + 1) (t : TotFibre E) :
    TotFibre.deg q t = t ⟨q, hq⟩ := by
  simp only [TotFibre.deg, LinearMap.coe_mk, AddHom.coe_mk, hq, ↓reduceDIte]

omit [FiniteDimensional ℂ E] in
/-- Helper: the `q`-th component of `t` is zero for `q > n`. -/
private theorem deg_of_ge {q : ℕ} (hq : ¬ q < Module.finrank ℂ E + 1) (t : TotFibre E) :
    TotFibre.deg q t = 0 := by
  simp only [TotFibre.deg, LinearMap.coe_mk, AddHom.coe_mk, hq, ↓reduceDIte]

/-- Helper: an element of negative degree is zero. -/
private theorem eq_zero_of_hasDegZ_neg {a : ℤ} (ha : a < 0) {t : TotFibre E}
    (h : HasDegZ a t) : t = 0 :=
  funext fun q => h q (by omega)

/-- Helper: a homogeneous element of degree `p ∈ ℕ` is `ofDeg p` of its component. -/
private theorem eq_ofDeg_of_hasDegZ (p : ℕ) {t : TotFibre E} (h : HasDegZ (p : ℤ) t) :
    t = TotFibre.ofDeg p (TotFibre.deg p t) := by
  conv_lhs => rw [← TotFibre.sum_ofDeg_deg t]
  by_cases hp : p < Module.finrank ℂ E + 1
  · rw [Finset.sum_eq_single p]
    · intro q hq hqp
      have : TotFibre.deg q t = 0 := by
        rw [deg_of_lt (Finset.mem_range.1 hq)]
        exact h ⟨q, Finset.mem_range.1 hq⟩ (by simpa using hqp)
      rw [this, map_zero]
    · intro hnot
      exact absurd (Finset.mem_range.2 hp) hnot
  · have h0 : TotFibre.deg p t = 0 := deg_of_ge hp t
    rw [h0, map_zero]
    refine Finset.sum_eq_zero fun q hq => ?_
    have : TotFibre.deg q t = 0 := by
      rw [deg_of_lt (Finset.mem_range.1 hq)]
      exact h ⟨q, Finset.mem_range.1 hq⟩ (by
        have := Finset.mem_range.1 hq
        omega)
    rw [this, map_zero]

/-- Helper: products of homogeneous elements are homogeneous, degrees add. -/
private theorem hasDegZ_mul {a b : ℤ} {s t : TotFibre E} (hs : HasDegZ a s) (ht : HasDegZ b t) :
    HasDegZ (a + b) (s * t) := by
  by_cases ha : a < 0
  · rw [eq_zero_of_hasDegZ_neg ha hs, zero_mul]
    exact hasDegZ_zero _
  by_cases hb : b < 0
  · rw [eq_zero_of_hasDegZ_neg hb ht, mul_zero]
    exact hasDegZ_zero _
  lift a to ℕ using (not_lt.1 ha)
  lift b to ℕ using (not_lt.1 hb)
  rw [eq_ofDeg_of_hasDegZ a hs, eq_ofDeg_of_hasDegZ b ht, TotFibre.ofDeg_mul_ofDeg]
  have := hasDegZ_ofDeg (E := E) (a + b)
    (TotFibre.deg (a + b) (TotFibre.ofDeg a (TotFibre.deg a s) *
      TotFibre.ofDeg b (TotFibre.deg b t) : TotFibre E))
  push_cast at this
  exact this

/-- Helper: `dz̄_j` is homogeneous of degree one. -/
private theorem hasDegZ_dzbarTot (j : Fin (Module.finrank ℂ E)) : HasDegZ 1 (dzbarTot E j) := by
  obtain ⟨α, hα⟩ := exists_ofDeg_one (E := E) (dualConjBasis E j)
  have := hasDegZ_ofDeg (E := E) 1 α
  rw [← hα] at this
  exact this

/-- Helper: every `y ∈ ⋀^k` maps to `ofDeg k` of a `k`-form, and every `k`-form arises so. -/
private theorem exists_ext_of_ofDeg (k : ℕ) (β : DolbeaultFibre E k ℂ) :
    ∃ y : ⋀[ℂ]^k (Module.Dual ℂ (Conj E)),
      TotFibre.extEquivTotFibre E (y : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) =
        TotFibre.ofDeg k β := by
  refine ⟨(extEquivFibre E k).symm β, ?_⟩
  rw [TotFibre.extEquivTotFibre_of_mem]
  exact congrArg _ ((extEquivFibre E k).apply_symm_apply β)

/-- Helper: the contraction maps degree `0` to zero. -/
private theorem ctrTot_ofDeg_zero (j : Fin (Module.finrank ℂ E)) (β : DolbeaultFibre E 0 ℂ) :
    ctrTot E j (TotFibre.ofDeg 0 β) = 0 := by
  obtain ⟨y, hy⟩ := exists_ext_of_ofDeg (E := E) 0 β
  rw [← hy, ctrTot_ext, contr_zero _ y.2, map_zero]

/-- Helper: the contraction maps degree `p + 1` to degree `p`. -/
private theorem ctrTot_ofDeg_succ (j : Fin (Module.finrank ℂ E)) (p : ℕ)
    (β : DolbeaultFibre E (p + 1) ℂ) :
    ∃ γ : DolbeaultFibre E p ℂ, ctrTot E j (TotFibre.ofDeg (p + 1) β) = TotFibre.ofDeg p γ := by
  obtain ⟨y, hy⟩ := exists_ext_of_ofDeg (E := E) (p + 1) β
  rw [← hy, ctrTot_ext]
  have hm := contr_mem (Module.Dual.eval ℂ (Conj E) (Conj.basis (Module.finBasis ℂ E) j)) p y y.2
  exact ⟨extToFibre E p ⟨_, hm⟩, TotFibre.extEquivTotFibre_of_mem (E := E) (q := p) ⟨_, hm⟩⟩

/-- Helper: the contraction lowers the degree by one. -/
private theorem hasDegZ_ctrTot (j : Fin (Module.finrank ℂ E)) {a : ℤ} {t : TotFibre E}
    (h : HasDegZ (a + 1) t) : HasDegZ a (ctrTot E j t) := by
  by_cases ha : a + 1 < 0
  · rw [eq_zero_of_hasDegZ_neg ha h, map_zero]
    exact hasDegZ_zero _
  by_cases ha0 : a + 1 = 0
  · have h0 : HasDegZ ((0 : ℕ) : ℤ) t := by simpa only [Nat.cast_zero] using ha0 ▸ h
    rw [eq_ofDeg_of_hasDegZ 0 h0, ctrTot_ofDeg_zero]
    exact hasDegZ_zero _
  · lift a to ℕ using (by omega)
    have h1 : HasDegZ (((a + 1 : ℕ)) : ℤ) t := by simpa only [Nat.cast_succ] using h
    rw [eq_ofDeg_of_hasDegZ (a + 1) h1]
    obtain ⟨γ, hγ⟩ := ctrTot_ofDeg_succ j a (TotFibre.deg (a + 1) t)
    rw [hγ]
    exact hasDegZ_ofDeg a γ

/-- Helper: membership in `totDegSub` as a degree condition on each component. -/
private theorem mem_totDegSub_iff {deg : Fin r → ℤ} {m : ℤ} {s : Fib E r} :
    s ∈ totDegSub (E := E) deg m ↔ ∀ i, HasDegZ (m - deg i) (s i) := by
  constructor
  · intro hs i q hq
    exact hs i q (by omega)
  · intro hs i q hq
    exact hs i q (by omega)

/-- Z5.d: degrees add under composition. -/
theorem IsOfTotDeg.mul {deg : Fin r → ℤ} {d d' : ℤ} {T T' : FibOp E r} (hT : IsOfTotDeg deg d T)
    (hT' : IsOfTotDeg deg d' T') : IsOfTotDeg deg (d' + d) (T * T') := by
  intro m s hs
  have := hT (m + d') (T' s) (hT' m s hs)
  rwa [add_assoc] at this

/-- Z5.d: `εⱼ` has total degree `1`, `ιⱼ` total degree `−1`. -/
theorem isOfTotDeg_epsOp (deg : Fin r → ℤ) (j : Fin (Module.finrank ℂ E)) :
    IsOfTotDeg deg 1 (epsOp j : FibOp E r) := by
  intro m s hs
  rw [mem_totDegSub_iff] at hs ⊢
  intro i
  have := hasDegZ_mul (hasDegZ_dzbarTot j) (hs i)
  have e : (1 : ℤ) + (m - deg i) = m + 1 - deg i := by omega
  rw [e] at this
  exact this

/-- Z5.d: `ιⱼ` has total degree `−1`. -/
theorem isOfTotDeg_iotaOp (deg : Fin r → ℤ) (j : Fin (Module.finrank ℂ E)) :
    IsOfTotDeg deg (-1) (iotaOp j : FibOp E r) := by
  intro m s hs
  rw [mem_totDegSub_iff] at hs ⊢
  intro i
  have e : m - deg i = (m + -1 - deg i) + 1 := by omega
  exact hasDegZ_ctrTot j (by rw [← e]; exact hs i)

end Cohesive
