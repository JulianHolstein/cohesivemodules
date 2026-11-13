import Cohesivemodules.Algebra.Connection
import Cohesivemodules.Algebra.BaseChange
import Cohesivemodules.Algebra.BlockBridge
import Cohesivemodules.Algebra.UnitModule
import Cohesivemodules.Algebra.TotProd
import Cohesivemodules.Algebra.HoPZero
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Homology.Single

set_option linter.style.header false

/-!
# Checks: blueprint §9 checks and non-vacuity of definitions

Phase 1a so far: non-vacuity of A1 (`GCDga`), A2 (`Connection`), A3–A5 (the zero cohesive
module, and `𝒜` itself for zero curvature, built with the A3.a constructor).

## A1 non-vacuity
`Toy k m₀ m₁ = k ⊕ k^{m₀} ⊕ k^{m₁}` with `k^{m₀}` in degree 0, `k^{m₁}` in degree 1, all
products of `k^{m₀} ⊕ k^{m₁}` zero (trivial square-zero extension), and
`d (r, v₀, v₁) = (0, 0, δ₀ v₀)`. Toy 2 (`m₀ = m₁ = 1`, `δ₀ = id`) is
`k[t, ε]/(t², ε², tε)` with `|t| = 0`, `|ε| = 1`, `dt = ε`: a `GCDga` with `d ≠ 0`, so the class
is not satisfied only by degenerate examples.

Part 1 of 2 of the original `Checks.lean`, split for size; continued in
`Checks.lean`.
-/

namespace Cohesive.Checks

open DirectSum TensorProduct

section Toy

variable (k : Type) [CommRing k] (m₀ m₁ : ℕ)

/-- The toy algebra `k ⊕ k^{m₀} ⊕ k^{m₁}`. -/
abbrev Toy := TrivSqZeroExt k ((Fin m₀ → k) × (Fin m₁ → k))

/-- Degree-0 part: `snd.2 = 0`. -/
def toyGr0 : Submodule k (Toy k m₀ m₁) :=
  LinearMap.ker ((LinearMap.snd k _ _).comp (TrivSqZeroExt.sndHom k _))

/-- Degree-1 part: `fst = 0` and `snd.1 = 0`. -/
def toyGr1 : Submodule k (Toy k m₀ m₁) :=
  LinearMap.ker ((TrivSqZeroExt.fstHom k k _).toLinearMap.prod
    ((LinearMap.fst k _ _).comp (TrivSqZeroExt.sndHom k _)))

/-- The grading of the toy algebra. -/
def toyGr (q : ℤ) : Submodule k (Toy k m₀ m₁) :=
  if q = 0 then toyGr0 k m₀ m₁ else if q = 1 then toyGr1 k m₀ m₁ else ⊥

variable {k m₀ m₁}

/-- A1 non-vacuity (toy algebra): Membership in the degree-0 part of the toy grading. -/
@[simp] theorem mem_toyGr0 {x : Toy k m₀ m₁} : x ∈ toyGr0 k m₀ m₁ ↔ x.snd.2 = 0 := by
  simp [toyGr0]

/-- A1 non-vacuity (toy algebra): Membership in the degree-1 part of the toy grading. -/
@[simp] theorem mem_toyGr1 {x : Toy k m₀ m₁} :
    x ∈ toyGr1 k m₀ m₁ ↔ x.fst = 0 ∧ x.snd.1 = 0 := by
  simp [toyGr1]

/-- A1 non-vacuity (toy algebra): The toy grading vanishes outside degrees 0 and 1. -/
theorem toyGr_of_ne {q : ℤ} (h0 : q ≠ 0) (h1 : q ≠ 1) : toyGr k m₀ m₁ q = ⊥ := by
  simp [toyGr, h0, h1]

/-- A1 non-vacuity (toy algebra): Elements of the toy grading outside degrees 0 and 1 vanish. -/
theorem eq_zero_of_mem_toyGr {q : ℤ} {a : Toy k m₀ m₁} (ha : a ∈ toyGr k m₀ m₁ q)
    (h : ¬(q = 0 ∨ q = 1)) : a = 0 := by
  simpa [toyGr_of_ne (not_or.1 h).1 (not_or.1 h).2] using ha

/-- A1 non-vacuity (toy algebra): The toy grading is multiplicative. -/
theorem toyGr_mul_mem {i j : ℤ} {a b : Toy k m₀ m₁} (ha : a ∈ toyGr k m₀ m₁ i)
    (hb : b ∈ toyGr k m₀ m₁ j) : a * b ∈ toyGr k m₀ m₁ (i + j) := by
  by_cases hi : i = 0 ∨ i = 1
  swap
  · simp [eq_zero_of_mem_toyGr ha hi]
  by_cases hj : j = 0 ∨ j = 1
  swap
  · simp [eq_zero_of_mem_toyGr hb hj]
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
    simp_all [toyGr, TrivSqZeroExt.ext_iff]

/-- Projection to the degree-1 part `(0, 0, v₁)`. -/
def toyP1 : Toy k m₀ m₁ →ₗ[k] Toy k m₀ m₁ :=
  TrivSqZeroExt.inrHom k _ ∘ₗ LinearMap.inr k _ _ ∘ₗ LinearMap.snd k _ _ ∘ₗ
    TrivSqZeroExt.sndHom k _

/-- A1 non-vacuity (toy algebra): Formula for the degree-1 projection. -/
@[simp] theorem toyP1_apply (x : Toy k m₀ m₁) : toyP1 x = TrivSqZeroExt.inr (0, x.snd.2) := rfl

/-- A1 non-vacuity (toy algebra): The degree-1 projection lands in degree 1. -/
theorem toyP1_mem (x : Toy k m₀ m₁) : toyP1 x ∈ toyGr k m₀ m₁ 1 := by
  simp [toyGr]

/-- Projection to the degree-0 part `(r, v₀, 0)`. -/
def toyP0 : Toy k m₀ m₁ →ₗ[k] Toy k m₀ m₁ := LinearMap.id - toyP1

/-- A1 non-vacuity (toy algebra): Formula for the degree-0 projection. -/
@[simp] theorem toyP0_apply (x : Toy k m₀ m₁) :
    toyP0 x = x - TrivSqZeroExt.inr (0, x.snd.2) := rfl

/-- A1 non-vacuity (toy algebra): The degree-0 projection lands in degree 0. -/
theorem toyP0_mem (x : Toy k m₀ m₁) : toyP0 x ∈ toyGr k m₀ m₁ 0 := by
  simp [toyGr]

/-- The decomposition `x ↦ P₀ x + P₁ x`. -/
def toyDecompose : Toy k m₀ m₁ →ₗ[k] ⨁ i, toyGr k m₀ m₁ i :=
  lof k ℤ (fun i => toyGr k m₀ m₁ i) 0 ∘ₗ toyP0.codRestrict _ toyP0_mem +
    lof k ℤ (fun i => toyGr k m₀ m₁ i) 1 ∘ₗ toyP1.codRestrict _ toyP1_mem

/-- A1 non-vacuity (toy algebra): Formula for the toy decomposition. -/
theorem toyDecompose_apply (x : Toy k m₀ m₁) :
    toyDecompose x = lof k ℤ (fun i => toyGr k m₀ m₁ i) 0 (toyP0.codRestrict _ toyP0_mem x) +
      lof k ℤ (fun i => toyGr k m₀ m₁ i) 1 (toyP1.codRestrict _ toyP1_mem x) := rfl

/-- A1 non-vacuity (toy algebra): The toy grading is a decomposition. -/
instance toyDecomposition : Decomposition (toyGr k m₀ m₁) :=
  Decomposition.ofLinearMap _ toyDecompose
    (by ext x : 1; simp [toyDecompose_apply])
    (by
      ext i ⟨a, ha⟩ : 2
      simp only [LinearMap.comp_apply, coeLinearMap_lof, LinearMap.id_comp, toyDecompose_apply]
      by_cases h0 : i = 0
      · subst h0
        have h : a.snd.2 = 0 := by simpa [toyGr] using ha
        have e1 : toyP1.codRestrict (toyGr k m₀ m₁ 1) toyP1_mem a = 0 :=
          Subtype.ext (by simp [h, Prod.mk_zero_zero])
        have e0 : toyP0.codRestrict (toyGr k m₀ m₁ 0) toyP0_mem a = ⟨a, ha⟩ :=
          Subtype.ext (by simp [h, Prod.mk_zero_zero])
        rw [e0, e1, map_zero, add_zero]
      by_cases h1 : i = 1
      · subst h1
        have h : a.fst = 0 ∧ a.snd.1 = 0 := by simpa [toyGr] using ha
        have e1 : toyP1.codRestrict (toyGr k m₀ m₁ 1) toyP1_mem a = ⟨a, ha⟩ :=
          Subtype.ext (by ext <;> simp [h])
        have e0 : toyP0.codRestrict (toyGr k m₀ m₁ 0) toyP0_mem a = 0 :=
          Subtype.ext (by ext <;> simp [h])
        rw [e0, e1, map_zero, zero_add]
      · have : a = 0 := eq_zero_of_mem_toyGr ha (by tauto)
        subst this
        have : (⟨0, ha⟩ : toyGr k m₀ m₁ i) = 0 := rfl
        simp [this])

/-- A1 non-vacuity (toy algebra): The toy grading makes the toy a graded algebra. -/
instance toyGraded : GradedAlgebra (toyGr k m₀ m₁) where
  one_mem := by simp [toyGr]
  mul_mem _ _ _ _ ha hb := toyGr_mul_mem ha hb

/-- The toy differential `d (r, v₀, v₁) = (0, 0, δ₀ v₀)`. -/
def toyD (δ₀ : (Fin m₀ → k) →ₗ[k] (Fin m₁ → k)) : Toy k m₀ m₁ →ₗ[k] Toy k m₀ m₁ :=
  TrivSqZeroExt.inrHom k _ ∘ₗ LinearMap.inr k _ _ ∘ₗ δ₀ ∘ₗ LinearMap.fst k _ _ ∘ₗ
    TrivSqZeroExt.sndHom k _

/-- A1 non-vacuity (toy algebra): Formula for the toy differential. -/
@[simp] theorem toyD_apply (δ₀ : (Fin m₀ → k) →ₗ[k] (Fin m₁ → k)) (x : Toy k m₀ m₁) :
    toyD δ₀ x = TrivSqZeroExt.inr (0, δ₀ x.snd.1) := rfl

/-- A1 non-vacuity (toy algebra): Products of two degree-1 elements of the toy vanish. -/
theorem toy_mul_eq_zero_of_one {a b : Toy k m₀ m₁} (ha : a ∈ toyGr k m₀ m₁ 1)
    (hb : b ∈ toyGr k m₀ m₁ 1) : a * b = 0 := by
  have := toyGr_mul_mem ha hb
  rwa [show (1 : ℤ) + 1 = 2 by norm_num, toyGr_of_ne (by norm_num) (by norm_num),
    Submodule.mem_bot] at this

/-- The toy dga structure for a given `δ₀ : V₀ → V₁`. -/
abbrev toyGCDga (δ₀ : (Fin m₀ → k) →ₗ[k] (Fin m₁ → k)) : GCDga (toyGr k m₀ m₁) where
  N := 1
  zero_of_neg q hq := toyGr_of_ne (by omega) (by omega)
  zero_of_gt q hq := toyGr_of_ne (by omega) (by omega)
  gcomm {p q a b} ha hb := by
    by_cases hp : p = 0 ∨ p = 1
    swap
    · simp [eq_zero_of_mem_toyGr ha hp]
    by_cases hq : q = 0 ∨ q = 1
    swap
    · simp [eq_zero_of_mem_toyGr hb hq]
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · simp [mul_comm]
    · simp [mul_comm]
    · simp [mul_comm]
    · simp [toy_mul_eq_zero_of_one ha hb, toy_mul_eq_zero_of_one hb ha]
  d := toyD δ₀
  d_mem {q a} ha := by
    by_cases hq : q = 0 ∨ q = 1
    swap
    · simp [eq_zero_of_mem_toyGr ha hq, Prod.mk_zero_zero]
    rcases hq with rfl | rfl
    · simp [toyGr]
    · have h : a.fst = 0 ∧ a.snd.1 = 0 := by simpa [toyGr] using ha
      rw [show (1 : ℤ) + 1 = 2 by norm_num, toyGr_of_ne (by norm_num) (by norm_num)]
      simp [h, Prod.mk_zero_zero]
  leibniz {p a} ha b := by
    by_cases hp : p = 0 ∨ p = 1
    swap
    · simp [eq_zero_of_mem_toyGr ha hp, Prod.mk_zero_zero]
    rcases hp with rfl | rfl
    · ext <;> simp [mul_comm, add_comm]
    · have h : a.fst = 0 ∧ a.snd.1 = 0 := by simpa [toyGr] using ha
      ext <;> simp [h]
  d_d a := by simp [Prod.mk_zero_zero]
  c := 0
  c_mem := zero_mem _
  d_c := map_zero _

/-- Toy 1 (`k[ε]/(ε²)`, `|ε| = 1`, `d = 0`): a `GCDga` (A1 non-vacuity). -/
instance toy1 : GCDga (toyGr k 0 1) := toyGCDga 0

/-- Toy 2 (`k[t, ε]/(t², ε², tε)`, `dt = ε`): a `GCDga` (A1 non-vacuity). -/
instance toy2 : GCDga (toyGr k 1 1) := toyGCDga LinearMap.id

end Toy

/-- A1 non-vacuity: toy 2 has a nonzero differential (`d t = ε ≠ 0`). -/
theorem toy2_d_ne_zero :
    GCDga.d (𝒜 := toyGr ℤ 1 1) (TrivSqZeroExt.inr (1, 0)) ≠ 0 := by
  intro h
  rw [show GCDga.d (𝒜 := toyGr ℤ 1 1) = toyD LinearMap.id from rfl] at h
  have := congrArg (fun y : Toy ℤ 1 1 => y.snd.2 0) h
  simp at this

/-- A2 non-vacuity: the free module `A⁰` over toy 2 (where `d ≠ 0`) has a connection (A2.a). -/
example : Nonempty (Connection (toyGr ℤ 1 1) (toyGr ℤ 1 1 0)) := Connection.exists_connection

section ZeroModule

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- The total module of the zero family vanishes. -/
instance : Subsingleton (Tot 𝒜 (fun _ => PUnit)) :=
  inferInstanceAs (Subsingleton (A ⊗[𝒜 0] (⨁ _ : ℤ, PUnit)))

/-- A3 non-vacuity: the zero cohesive module (over any `GCDga`, curved or not). -/
def zeroCohesive : CohesiveModule 𝒜 where
  Q _ := PUnit
  X := 0
  X_mem _ := zero_mem _
  leibniz _ _ := Subsingleton.elim _ _
  flat _ := Subsingleton.elim _ _
  bounded := ⟨0, 0, fun _ _ => inferInstance⟩
  finite _ := inferInstance
  projective _ := inferInstance

/-- A5 non-vacuity: `Ho(P_A)` has an object. -/
example : HoP 𝒜 := ⟨zeroCohesive 𝒜⟩

end ZeroModule

/-! ## `𝒜` itself as a cohesive module (blueprint §9: non-vacuity)

`unitCohesive` and its API moved to `Algebra/UnitModule.lean` (K4.b, 2 Nov 2026). -/

/-- Non-vacuity on toy 2 (`d ≠ 0`, `c = 0`): `𝒜` itself is an object of `Ho(P_A)`. -/
example : HoP (toyGr ℤ 1 1) := ⟨unitCohesive (toyGr ℤ 1 1) rfl⟩

/-- A9 non-vacuity: base change of `𝒜` itself along the identity of toy 2. -/
example : CohesiveModule (toyGr ℤ 1 1) :=
  (unitCohesive (toyGr ℤ 1 1) rfl).baseChange (DgaHom.id (toyGr ℤ 1 1))

/-- A9 non-vacuity: the base-change functor `Ho(P_A) ⥤ Ho(P_B)` on the identity endomorphism
of `𝒜` itself (toy 2). -/
example : HoP (toyGr ℤ 1 1) :=
  (bcHoFunctor (DgaHom.id (toyGr ℤ 1 1))).obj ⟨unitCohesive (toyGr ℤ 1 1) rfl⟩

open CategoryTheory in
/-- A9.a non-vacuity: the comparison `(id ∘ id)^*𝒜 ≅ id^*(id^*𝒜)` in `Ho(P_A)` (toy 2), the
component of the natural isomorphism `bcCompNatIso`. -/
example : (bcHoFunctor ((DgaHom.id (toyGr ℤ 1 1)).comp (DgaHom.id (toyGr ℤ 1 1)))).obj
      ⟨unitCohesive (toyGr ℤ 1 1) rfl⟩ ≅
    (bcHoFunctor (DgaHom.id (toyGr ℤ 1 1)) ⋙ bcHoFunctor (DgaHom.id (toyGr ℤ 1 1))).obj
      ⟨unitCohesive (toyGr ℤ 1 1) rfl⟩ :=
  (bcCompNatIso (DgaHom.id (toyGr ℤ 1 1)) (DgaHom.id (toyGr ℤ 1 1))).app _

section A10

open CategoryTheory

/-- A10 non-vacuity: the complex `ℤ` concentrated in degree `0`. -/
noncomputable abbrev singleZ : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  (HomologicalComplex.single (ModuleCat ℤ) (ComplexShape.up ℤ) 0).obj (ModuleCat.of ℤ ℤ)

/-- A10 non-vacuity: `ℤ` in degree `0` is a bounded complex of finitely generated projective
`ℤ`-modules (and it is nonzero in degree 0). -/
theorem singleZ_isBoundedFGProj : IsBoundedFGProj ℤ singleZ where
  bounded := ⟨0, 0, fun p hp => ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ) p
      (by omega))⟩
  finite p := by
    by_cases hp : p = 0
    · subst hp
      exact Module.Finite.equiv (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of ℤ ℤ)).toLinearEquiv.symm
    · have := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ) p hp)
      infer_instance
  projective p := by
    by_cases hp : p = 0
    · subst hp
      exact Module.Projective.of_equiv (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of ℤ ℤ)).toLinearEquiv.symm
    · have := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (ModuleCat.of ℤ ℤ) p hp)
      infer_instance

/-- A10 non-vacuity: `ρ = ℤ → A⁰` (toy 2) satisfies `d ∘ ρ = 0`. -/
theorem toy_dρ (r : ℤ) :
    GCDga.d (𝒜 := toyGr ℤ 1 1) ((Int.castRingHom (toyGr ℤ 1 1 0) r : toyGr ℤ 1 1 0) :
      Toy ℤ 1 1) = 0 := by
  rw [eq_intCast, ← zsmul_one,
    show ((r • (1 : toyGr ℤ 1 1 0) : toyGr ℤ 1 1 0) : Toy ℤ 1 1) = r • (1 : Toy ℤ 1 1) from rfl,
    map_zsmul, GCDga.d_one, smul_zero]

/-- A10 non-vacuity: `A ⊗_ℤ ℤ[0]` over toy 2 is a cohesive module, an object of `Ho(P_A)`. -/
noncomputable example : HoP (toyGr ℤ 1 1) :=
  ⟨CohesiveModule.fromComplex singleZ toy_dρ rfl singleZ_isBoundedFGProj⟩

end A10

section A13

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- Block's total module of the zero family vanishes. -/
instance : Subsingleton (TotR 𝒜 (fun _ => PUnit)) :=
  inferInstanceAs (Subsingleton ((⨁ _ : ℤ, PUnit) ⊗[𝒜 0] A))

/-- A13 non-vacuity: the zero cohesive module in Block's convention, built directly from
Block's definitions (any curvature `cB`). -/
def zeroBlockCohesive (cB : A) : BlockCohesive 𝒜 cB where
  Q _ := PUnit
  E := 0
  E_mem _ := zero_mem _
  leibniz _ _ := Subsingleton.elim _ _
  integrable _ := Subsingleton.elim _ _
  bounded := ⟨0, 0, fun _ _ => inferInstance⟩
  finite _ := inferInstance
  projective _ := inferInstance

end A13

/-- A13 non-vacuity: `𝒜` itself (toy 2, `c = 0`) as a cohesive module in Block's convention
(`cB = -c = -0`), through the bridge. -/
example : BlockCohesive (toyGr ℤ 1 1) (-GCDga.c (𝒜 := toyGr ℤ 1 1)) :=
  (unitCohesive (toyGr ℤ 1 1) rfl).toBlock _ (neg_neg _).symm

/-- A13 non-vacuity: the identity of Block's zero module, transported to `Hom^0` of A4. -/
example : Hom ((zeroBlockCohesive (toyGr ℤ 1 1) (-GCDga.c (𝒜 := toyGr ℤ 1 1))
      ).toBlockQuasiCohesive.toLeft (neg_neg _).symm)
    ((zeroBlockCohesive (toyGr ℤ 1 1) (-GCDga.c (𝒜 := toyGr ℤ 1 1))
      ).toBlockQuasiCohesive.toLeft (neg_neg _).symm) 0 :=
  BlockQuasiCohesive.blockHomEquiv _ 0 ⟨LinearMap.id, fun hx => by simpa using hx, fun _ _ => rfl⟩

/-! ## Z2.c: products of generator families, zero object -/

/-- Z2.c non-vacuity: for toy 2, the total module of `U × U` (unit generators twice) is `A × A`,
through `Tot.prodEquiv` and `unitEquiv`. -/
example : Tot (toyGr ℤ 1 1) (prodQ (UnitQ (toyGr ℤ 1 1)) (UnitQ (toyGr ℤ 1 1))) ≃ₗ[Toy ℤ 1 1]
    Toy ℤ 1 1 × Toy ℤ 1 1 :=
  (Tot.prodEquiv _ _ _).trans ((unitEquiv _).prodCongr (unitEquiv _))

/-- Z2.c: `Ho(P_A)` has a zero object, here for toy 2. -/
example : CategoryTheory.Limits.HasZeroObject (HoP (toyGr ℤ 1 1)) := inferInstance

end Cohesive.Checks
