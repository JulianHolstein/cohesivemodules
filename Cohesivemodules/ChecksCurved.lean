import Cohesivemodules.ChecksAlgebra
import Cohesivemodules.Algebra.Gauge

set_option linter.style.header false

/-!
# Check K12: a curved toy dga with a cohesive module, and its gauge (blueprint-tw §5)

`Toy k m₀ m₁ = k ⊕ k^{m₀} ⊕ k^{m₁}` (trivial square-zero extension, as in `ChecksAlgebra`) graded
with `k` in degree 0, `k^{m₀}` in degree 1 and `k^{m₁}` in degree 2, and
`d (r, v₀, v₁) = (0, 0, δ v₀)`. For `m₀ = m₁ = 1`, `δ = id` (`ctoy`), `β = (0, 1, 0)` has
`c' = dβ = (0, 0, 1) ≠ 0`; the unit module ungauged by `β` (operator `d + β·`) is a cohesive
module over `(A, c')` (Z3.b, `ungauge`), and its gauge is the unit module again.

## Deviation from blueprint-tw §5
K12 there names `k[t]/t² ⊗ Λ(ε₁, ε₂)` with `dt = ε₁`; that differential is not well defined
(`d(t²) = 2tε₁ ≠ 0` while `t² = 0`, and `2` must be invertible for the gauge). The square-zero toy
above (all products of positive-degree elements vanish) is a consistent replacement with the same
purpose: a cohesive module over a curved dga with `c ≠ 0`, and the signs of A.2 exercised.
-/

namespace Cohesive.Checks

open DirectSum TensorProduct

section CToy

variable (k : Type) [CommRing k] (m₀ m₁ : ℕ)

/-- Degree 0 of the curved toy: `snd = 0`. -/
def ctoyGr0 : Submodule k (Toy k m₀ m₁) :=
  LinearMap.ker (TrivSqZeroExt.sndHom k ((Fin m₀ → k) × (Fin m₁ → k)))

/-- Degree 2 of the curved toy: `fst = 0`, `snd.1 = 0` (the degree-1 part of `ChecksAlgebra`). -/
def ctoyGr2 : Submodule k (Toy k m₀ m₁) := toyGr1 k m₀ m₁

/-- Degree 1 of the curved toy: `fst = 0`, `snd.2 = 0`. -/
def ctoyGr1 : Submodule k (Toy k m₀ m₁) :=
  LinearMap.ker ((TrivSqZeroExt.fstHom k k _).toLinearMap.prod
    ((LinearMap.snd k _ _).comp (TrivSqZeroExt.sndHom k _)))

/-- The grading of the curved toy (degrees 0, 1, 2). -/
def ctoyGr (q : ℤ) : Submodule k (Toy k m₀ m₁) :=
  if q = 0 then ctoyGr0 k m₀ m₁ else if q = 1 then ctoyGr1 k m₀ m₁ else
    if q = 2 then ctoyGr2 k m₀ m₁ else ⊥

variable {k m₀ m₁}

/-- K12: membership in degree 0. -/
@[simp] theorem mem_ctoyGr0 {x : Toy k m₀ m₁} : x ∈ ctoyGr0 k m₀ m₁ ↔ x.snd = 0 := by
  simp [ctoyGr0]

/-- K12: membership in degree 1. -/
@[simp] theorem mem_ctoyGr1 {x : Toy k m₀ m₁} :
    x ∈ ctoyGr1 k m₀ m₁ ↔ x.fst = 0 ∧ x.snd.2 = 0 := by
  simp [ctoyGr1]

/-- K12: membership in degree 2. -/
@[simp] theorem mem_ctoyGr2 {x : Toy k m₀ m₁} :
    x ∈ ctoyGr2 k m₀ m₁ ↔ x.fst = 0 ∧ x.snd.1 = 0 := by
  simp [ctoyGr2]

/-- K12: the grading vanishes outside degrees 0, 1, 2. -/
theorem ctoyGr_of_ne {q : ℤ} (h0 : q ≠ 0) (h1 : q ≠ 1) (h2 : q ≠ 2) : ctoyGr k m₀ m₁ q = ⊥ := by
  simp [ctoyGr, h0, h1, h2]

/-- K12: elements of the grading outside degrees 0, 1, 2 vanish. -/
theorem eq_zero_of_mem_ctoyGr {q : ℤ} {a : Toy k m₀ m₁} (ha : a ∈ ctoyGr k m₀ m₁ q)
    (h : ¬(q = 0 ∨ q = 1 ∨ q = 2)) : a = 0 := by
  simp only [not_or] at h
  simpa [ctoyGr_of_ne h.1 h.2.1 h.2.2] using ha

/-- K12: the grading is multiplicative. -/
theorem ctoyGr_mul_mem {i j : ℤ} {a b : Toy k m₀ m₁} (ha : a ∈ ctoyGr k m₀ m₁ i)
    (hb : b ∈ ctoyGr k m₀ m₁ j) : a * b ∈ ctoyGr k m₀ m₁ (i + j) := by
  by_cases hi : i = 0 ∨ i = 1 ∨ i = 2
  swap
  · simp [eq_zero_of_mem_ctoyGr ha hi]
  by_cases hj : j = 0 ∨ j = 1 ∨ j = 2
  swap
  · simp [eq_zero_of_mem_ctoyGr hb hj]
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp_all [ctoyGr, TrivSqZeroExt.ext_iff]

/-- K12: projection to degree 1, `(0, v₀, 0)`. -/
def ctoyP1 : Toy k m₀ m₁ →ₗ[k] Toy k m₀ m₁ :=
  TrivSqZeroExt.inrHom k _ ∘ₗ LinearMap.inl k _ _ ∘ₗ LinearMap.fst k _ _ ∘ₗ
    TrivSqZeroExt.sndHom k _

/-- K12: projection to degree 2, `(0, 0, v₁)` (`toyP1` of `ChecksAlgebra`). -/
def ctoyP2 : Toy k m₀ m₁ →ₗ[k] Toy k m₀ m₁ := toyP1

/-- K12: projection to degree 0, `(r, 0, 0)`. -/
def ctoyP0 : Toy k m₀ m₁ →ₗ[k] Toy k m₀ m₁ := LinearMap.id - ctoyP1 - ctoyP2

/-- K12: formula for `ctoyP0`. -/
@[simp] theorem ctoyP0_apply (x : Toy k m₀ m₁) :
    ctoyP0 x = x - TrivSqZeroExt.inr (x.snd.1, 0) - TrivSqZeroExt.inr (0, x.snd.2) := rfl

/-- K12: formula for `ctoyP1`. -/
@[simp] theorem ctoyP1_apply (x : Toy k m₀ m₁) :
    ctoyP1 x = TrivSqZeroExt.inr (x.snd.1, 0) := rfl

/-- K12: formula for `ctoyP2`. -/
@[simp] theorem ctoyP2_apply (x : Toy k m₀ m₁) :
    ctoyP2 x = TrivSqZeroExt.inr (0, x.snd.2) := rfl

/-- K12: `ctoyP0` lands in degree 0. -/
theorem ctoyP0_mem (x : Toy k m₀ m₁) : ctoyP0 x ∈ ctoyGr k m₀ m₁ 0 := by
  simp [ctoyGr, Prod.ext_iff]

/-- K12: `ctoyP1` lands in degree 1. -/
theorem ctoyP1_mem (x : Toy k m₀ m₁) : ctoyP1 x ∈ ctoyGr k m₀ m₁ 1 := by
  simp [ctoyGr]

/-- K12: `ctoyP2` lands in degree 2. -/
theorem ctoyP2_mem (x : Toy k m₀ m₁) : ctoyP2 x ∈ ctoyGr k m₀ m₁ 2 := by
  simp [ctoyGr]

/-- K12: the decomposition `x ↦ P₀ x + P₁ x + P₂ x`. -/
def ctoyDecompose : Toy k m₀ m₁ →ₗ[k] ⨁ i, ctoyGr k m₀ m₁ i :=
  lof k ℤ (fun i => ctoyGr k m₀ m₁ i) 0 ∘ₗ ctoyP0.codRestrict _ ctoyP0_mem +
    lof k ℤ (fun i => ctoyGr k m₀ m₁ i) 1 ∘ₗ ctoyP1.codRestrict _ ctoyP1_mem +
    lof k ℤ (fun i => ctoyGr k m₀ m₁ i) 2 ∘ₗ ctoyP2.codRestrict _ ctoyP2_mem

/-- K12: formula for `ctoyDecompose`. -/
private theorem ctoyDecompose_apply (x : Toy k m₀ m₁) :
    ctoyDecompose x = lof k ℤ (fun i => ctoyGr k m₀ m₁ i) 0 (ctoyP0.codRestrict _ ctoyP0_mem x) +
      lof k ℤ (fun i => ctoyGr k m₀ m₁ i) 1 (ctoyP1.codRestrict _ ctoyP1_mem x) +
      lof k ℤ (fun i => ctoyGr k m₀ m₁ i) 2 (ctoyP2.codRestrict _ ctoyP2_mem x) := rfl

/-- K12: the grading is a decomposition. -/
instance ctoyDecomposition : Decomposition (ctoyGr k m₀ m₁) :=
  Decomposition.ofLinearMap _ ctoyDecompose
    (by
      ext x : 1
      simp only [LinearMap.comp_apply, ctoyDecompose_apply, map_add, LinearMap.id_apply]
      ext <;> simp)
    (by
      ext i ⟨a, ha⟩ : 2
      simp only [LinearMap.comp_apply, coeLinearMap_lof, LinearMap.id_comp, ctoyDecompose_apply]
      by_cases h : i = 0 ∨ i = 1 ∨ i = 2
      swap
      · have : a = 0 := eq_zero_of_mem_ctoyGr ha h
        subst this
        have : (⟨0, ha⟩ : ctoyGr k m₀ m₁ i) = 0 := rfl
        simp [this]
      rcases h with rfl | rfl | rfl
      · have h : a.snd = 0 := by simpa [ctoyGr] using ha
        have e0 : ctoyP0.codRestrict (ctoyGr k m₀ m₁ 0) ctoyP0_mem a = ⟨a, ha⟩ :=
          Subtype.ext (by ext <;> simp [h])
        have e1 : ctoyP1.codRestrict (ctoyGr k m₀ m₁ 1) ctoyP1_mem a = 0 :=
          Subtype.ext (by simp [h, Prod.mk_zero_zero])
        have e2 : ctoyP2.codRestrict (ctoyGr k m₀ m₁ 2) ctoyP2_mem a = 0 :=
          Subtype.ext (by simp [h, Prod.mk_zero_zero])
        rw [e0, e1, e2, map_zero, map_zero, add_zero, add_zero]
      · have h : a.fst = 0 ∧ a.snd.2 = 0 := by simpa [ctoyGr] using ha
        have e0 : ctoyP0.codRestrict (ctoyGr k m₀ m₁ 0) ctoyP0_mem a = 0 :=
          Subtype.ext (by ext <;> simp [h])
        have e1 : ctoyP1.codRestrict (ctoyGr k m₀ m₁ 1) ctoyP1_mem a = ⟨a, ha⟩ :=
          Subtype.ext (by ext <;> simp [h])
        have e2 : ctoyP2.codRestrict (ctoyGr k m₀ m₁ 2) ctoyP2_mem a = 0 :=
          Subtype.ext (by simp [h, Prod.mk_zero_zero])
        rw [e0, e1, e2, map_zero, map_zero, zero_add, add_zero]
      · have h : a.fst = 0 ∧ a.snd.1 = 0 := by simpa [ctoyGr] using ha
        have e0 : ctoyP0.codRestrict (ctoyGr k m₀ m₁ 0) ctoyP0_mem a = 0 :=
          Subtype.ext (by ext <;> simp [h])
        have e1 : ctoyP1.codRestrict (ctoyGr k m₀ m₁ 1) ctoyP1_mem a = 0 :=
          Subtype.ext (by simp [h, Prod.mk_zero_zero])
        have e2 : ctoyP2.codRestrict (ctoyGr k m₀ m₁ 2) ctoyP2_mem a = ⟨a, ha⟩ :=
          Subtype.ext (by ext <;> simp [h])
        rw [e0, e1, e2, map_zero, map_zero, zero_add, zero_add])

/-- K12: the curved toy is a graded algebra. -/
instance ctoyGraded : GradedAlgebra (ctoyGr k m₀ m₁) where
  one_mem := by simp [ctoyGr]
  mul_mem _ _ _ _ ha hb := ctoyGr_mul_mem ha hb

/-- K12: products of two elements of positive degree vanish. -/
private theorem ctoy_mul_eq_zero_of_pos {p q : ℤ} {a b : Toy k m₀ m₁}
    (ha : a ∈ ctoyGr k m₀ m₁ p) (hb : b ∈ ctoyGr k m₀ m₁ q) (hp : 0 < p) (hq : 0 < q) :
    a * b = 0 := by
  have h1 : a.fst = 0 := by
    by_cases h : p = 1 ∨ p = 2
    · rcases h with rfl | rfl <;> simp_all [ctoyGr]
    · exact (by simp [eq_zero_of_mem_ctoyGr ha (by omega)] : a = 0) ▸ rfl
  have h2 : b.fst = 0 := by
    by_cases h : q = 1 ∨ q = 2
    · rcases h with rfl | rfl <;> simp_all [ctoyGr]
    · exact (by simp [eq_zero_of_mem_ctoyGr hb (by omega)] : b = 0) ▸ rfl
  ext <;> simp [h1, h2]

/-- K12: the differential `d (r, v₀, v₁) = (0, 0, δ v₀)` (`toyD` of `ChecksAlgebra`). -/
def ctoyD (δ : (Fin m₀ → k) →ₗ[k] (Fin m₁ → k)) : Toy k m₀ m₁ →ₗ[k] Toy k m₀ m₁ := toyD δ

/-- K12: formula for `ctoyD`. -/
@[simp] theorem ctoyD_apply (δ : (Fin m₀ → k) →ₗ[k] (Fin m₁ → k)) (x : Toy k m₀ m₁) :
    ctoyD δ x = TrivSqZeroExt.inr (0, δ x.snd.1) := rfl

/-- K12: the flat toy dga structure (`c = 0`, `N = 2`) for `δ : k^{m₀} → k^{m₁}`. -/
abbrev ctoyGCDga (δ : (Fin m₀ → k) →ₗ[k] (Fin m₁ → k)) : GCDga (ctoyGr k m₀ m₁) where
  N := 2
  zero_of_neg q hq := ctoyGr_of_ne (by omega) (by omega) (by omega)
  zero_of_gt q hq := ctoyGr_of_ne (by omega) (by omega) (by omega)
  gcomm {p q a b} ha hb := by
    by_cases hp : p = 0 ∨ p = 1 ∨ p = 2
    swap
    · simp [eq_zero_of_mem_ctoyGr ha hp]
    by_cases hq : q = 0 ∨ q = 1 ∨ q = 2
    swap
    · simp [eq_zero_of_mem_ctoyGr hb hq]
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · simp [mul_comm]
    · simp [mul_comm]
    · simp [mul_comm]
    · simp [mul_comm]
    · simp [ctoy_mul_eq_zero_of_pos ha hb one_pos one_pos,
        ctoy_mul_eq_zero_of_pos hb ha one_pos one_pos]
    · simp [ctoy_mul_eq_zero_of_pos ha hb one_pos two_pos,
        ctoy_mul_eq_zero_of_pos hb ha two_pos one_pos]
    · simp [mul_comm]
    · simp [ctoy_mul_eq_zero_of_pos ha hb two_pos one_pos,
        ctoy_mul_eq_zero_of_pos hb ha one_pos two_pos]
    · simp [ctoy_mul_eq_zero_of_pos ha hb two_pos two_pos,
        ctoy_mul_eq_zero_of_pos hb ha two_pos two_pos]
  d := ctoyD δ
  d_mem {q a} ha := by
    by_cases hq : q = 0 ∨ q = 1 ∨ q = 2
    swap
    · simp [eq_zero_of_mem_ctoyGr ha hq, Prod.mk_zero_zero]
    rcases hq with rfl | rfl | rfl
    · have h : a.snd = 0 := by simpa [ctoyGr] using ha
      simp [ctoyGr, h]
    · simp [ctoyGr]
    · have h : a.fst = 0 ∧ a.snd.1 = 0 := by simpa [ctoyGr] using ha
      rw [show (2 : ℤ) + 1 = 3 by norm_num, ctoyGr_of_ne (by norm_num) (by norm_num)
        (by norm_num)]
      simp [h, Prod.mk_zero_zero]
  leibniz {p a} ha b := by
    by_cases hp : p = 0 ∨ p = 1 ∨ p = 2
    swap
    · simp [eq_zero_of_mem_ctoyGr ha hp, Prod.mk_zero_zero]
    rcases hp with rfl | rfl | rfl
    · ext <;> simp [mul_comm, add_comm]
    · have h : a.fst = 0 ∧ a.snd.2 = 0 := by simpa [ctoyGr] using ha
      ext <;> simp [h]
    · have h : a.fst = 0 ∧ a.snd.1 = 0 := by simpa [ctoyGr] using ha
      have h0 : a * TrivSqZeroExt.inr (0, δ b.snd.1) = 0 := by ext <;> simp [h]
      simp [h0, h, Prod.mk_zero_zero]
  d_d a := by simp [Prod.mk_zero_zero]
  c := 0
  c_mem := zero_mem _
  d_c := map_zero _

end CToy

/-- K12: the curved toy over `ℚ` with `m₀ = m₁ = 1`, `δ = id`: `k[β, c]/(β², βc, c²)`, `|β| = 1`,
`|c| = 2`, `dβ = c`; flat instance. -/
instance ctoy : GCDga (ctoyGr ℚ 1 1) := ctoyGCDga LinearMap.id

/-- K12: `β = (0, 1, 0)`, of degree 1. -/
def ctoyβ : Toy ℚ 1 1 := TrivSqZeroExt.inr (1, 0)

/-- K12: `β` has degree 1. -/
theorem ctoyβ_mem : ctoyβ ∈ ctoyGr ℚ 1 1 1 := by
  simp [ctoyGr, ctoyβ]

/-- K12: the curvature `c' = dβ = (0, 0, 1)`. -/
def ctoyC : Toy ℚ 1 1 := GCDga.d (𝒜 := ctoyGr ℚ 1 1) ctoyβ

/-- K12: `c'` has degree 2. -/
theorem ctoyC_mem : ctoyC ∈ ctoyGr ℚ 1 1 2 := GCDga.d_mem ctoyβ_mem

/-- K12: `c'` is closed. -/
theorem ctoyC_d : GCDga.d (𝒜 := ctoyGr ℚ 1 1) ctoyC = 0 := GCDga.d_d _

/-- **K12 (non-vacuity of `c ≠ 0`).** The curvature `c' = dβ` of the curved toy is nonzero. -/
theorem ctoyC_ne_zero : ctoyC ≠ 0 := by
  intro h
  unfold ctoyC at h
  rw [show GCDga.d (𝒜 := ctoyGr ℚ 1 1) = ctoyD LinearMap.id from rfl] at h
  have := congrArg (fun y : Toy ℚ 1 1 => y.snd.2 0) h
  simp [ctoyβ] at this

/-- K12: `c' = c + dβ` for the flat instance (`c = 0`). -/
theorem ctoy_hcβ : ctoyC = GCDga.c (𝒜 := ctoyGr ℚ 1 1) + GCDga.d (𝒜 := ctoyGr ℚ 1 1) ctoyβ :=
  (zero_add _).symm

/-- K12: `2` is a unit in `ℚ`. -/
theorem ctoy_two : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr two_ne_zero

/-- **K12.** A cohesive module over the curved toy `(A, c' = dβ ≠ 0)`: the unit module with
operator `d + β·` (Z3.b `ungauge`). -/
def ctoyModule : CCM (inferInstance : GCDga (ctoyGr ℚ 1 1)) ctoyC ctoyC_mem ctoyC_d :=
  CohesiveModule.ungauge ctoyβ ctoyβ_mem ctoy_hcβ ctoy_two (unitCohesive (ctoyGr ℚ 1 1) rfl)

/-- **K12.** The gauge of `ctoyModule` by `β` is the unit module of the flat toy (Z3.b). -/
example : CohesiveModule.gauge ctoyβ ctoyβ_mem ctoy_hcβ ctoy_two ctoyModule =
    unitCohesive (ctoyGr ℚ 1 1) rfl :=
  gauge_ungauge _ _ _ _ _

end Cohesive.Checks
