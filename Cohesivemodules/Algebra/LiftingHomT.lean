import Cohesivemodules.Algebra.Filtration
import Cohesivemodules.Algebra.Connection

set_option linter.style.header false

/-!
# A11–A12: the lifting theorem

Blueprint item A11 ([B, Thm 3.2.7(2), Lemma 3.2.8], [A, Prop 3.3.4, case 2]). Given a
quasi-cohesive `N = (Q, 𝕏)`, generators `P` (finitely generated projective `A⁰`-modules) with an
`A⁰`-linear differential `∂`, and a chain map `e₀ : (P, ∂) → (Q, 𝕏⁰)`, we build a cohesive
structure `𝔼` on `A ⊗ P` with `𝔼⁰ = ∂` and a closed degree-`0` map `e : A ⊗ P → N` with
`(0,0)`-component `e₀`, assuming the cone condition `ConeLift` in each form degree `1 ≤ b ≤ N`
(A11.a derives it from flatness of `A^b` and the quasi-isomorphism `e₀`).

## Signs (re-derived in the left convention, blueprint A11 ⚠)
Write `D` for a Leibniz operator on `T_P = A ⊗ ⨁P` (the extension of generator data `θ`), and
`e ∈ Hom⁰(T_P, T_N)`. The defects are `K := D² - c ∈ Hom²` and `L := 𝕏 e - e D = δe ∈ Hom¹`.
* Bianchi: `δK = DK - KD = Dc - cD = 0` (as `dc = 0`); `δL = 𝕏L + LD = ce - eD² = -eK`.
* If `K, L ∈ F^b` (A6), the pure parts `K_b, L_b` of form degree `b` satisfy
  `δ⁰K_b = 0` and `δ⁰L_b + e₀K_b = 0`, where `δ⁰` is the Hom differential built from the
  form-degree-preserving operators `∂̂` and `𝕏̂⁰`.
* That is: `(K_b, L_b)` is a 1-cycle in Mathlib's cone of `e₀ ∘ - : gr_b Hom(P, P) → gr_b Hom(P, N)`
  (differential `d(x, y) = (-δx, e₀x + δy)`). A preimage `(x', y')` gives `φ := x'`, `ψ := -y'`
  with `δ⁰φ = -K_b`, `δ⁰ψ - e₀φ = -L_b` (`ConeLift`).
* `D' := D + φ̂`, `e' := e + ψ̂`: `K' = K + δφ̂ + φ̂²`, `L' = L + δψ̂ - eφ̂ - ψ̂φ̂`, both in
  `F^{b+1}`.
* Base `b = 1`: `D = ∂̂ + ∇̂` for any connection `∇` (A2.a), `e = ê₀`; `gr₀K = ∂² = 0` and
  `gr₀L = 𝕏⁰e₀ - e₀∂ = 0`. The step at `b = 1` corrects the connection by an `A⁰`-linear `φ`
  ([A]'s twist by `a`). Stop at `b = N + 1`: `F^{N+1} = 0`, so `K = 0`, `L = 0`.
No sign of the sources needs correcting.

## Encoding
The frozen `Hom`/`δ` (A4) need quasi-cohesive modules, but `D` is flat only at the end. So this
file works with `HomT` (the same carrier as `Hom`, `hom_eq_homT` is `rfl`), `δT` for arbitrary
operators, and `FT` (the same as `filHom`, A6).

Part 1 of 3 of the original `Algebra/Lifting.lean`, split for size; continued in
`Algebra/LiftingLead.lean`.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-! ## Hom spaces, differentials and filtrations for arbitrary operators -/

section HomT

variable (𝒜) (Q₁ Q₂ Q₃ : ℤ → Type) [∀ p, AddCommGroup (Q₁ p)] [∀ p, Module (𝒜 0) (Q₁ p)]
  [∀ p, AddCommGroup (Q₂ p)] [∀ p, Module (𝒜 0) (Q₂ p)]
  [∀ p, AddCommGroup (Q₃ p)] [∀ p, Module (𝒜 0) (Q₃ p)]

/-- A11: `Hom^n` on total modules of generator families (the carrier of A4 `Hom`, which only
depends on the generators). -/
def HomT (n : ℤ) : Submodule k (Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂) where
  carrier := {φ | (∀ {m : ℤ} {x : Tot 𝒜 Q₁}, x ∈ totDeg 𝒜 Q₁ m → φ x ∈ totDeg 𝒜 Q₂ (m + n)) ∧
    ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 Q₁, φ (a • x) = (n * p).negOnePow • a • φ x}
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => by simp⟩
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun hx => add_mem (hφ.1 hx) (hψ.1 hx), fun ha x => by simp [hφ.2 ha, hψ.2 ha, smul_add]⟩
  smul_mem' := fun r φ hφ =>
    ⟨fun hx => Submodule.smul_mem _ r (hφ.1 hx), fun ha x => by
      simp only [LinearMap.smul_apply, hφ.2 ha]
      rw [smul_comm r, smul_comm r]⟩

/-- A11: A4 `Hom` is `HomT` of the generators. -/
theorem hom_eq_homT (M₁ M₂ : QuasiCohesive 𝒜) (n : ℤ) : Hom M₁ M₂ n = HomT 𝒜 M₁.Q M₂.Q n :=
  rfl

/-- A11: the filtration `F^b HomT^n` (A6 `filHom` for generator families). -/
def FT (n b : ℤ) : Submodule k (Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂) :=
  HomT 𝒜 Q₁ Q₂ n ⊓
    { carrier := {φ | ∀ (c : ℤ) (x : Tot 𝒜 Q₁), x ∈ filTot 𝒜 Q₁ c → φ x ∈ filTot 𝒜 Q₂ (c + b)}
      add_mem' := fun hφ hψ c x hx => add_mem (hφ c x hx) (hψ c x hx)
      zero_mem' := fun _ _ _ => zero_mem _
      smul_mem' := fun r _ hφ c x hx => Submodule.smul_mem _ r (hφ c x hx) }

/-- A11: A6 `filHom` is `FT` of the generators. -/
theorem filHom_eq_FT (M₁ M₂ : QuasiCohesive 𝒜) (n b : ℤ) :
    filHom M₁ M₂ n b = FT 𝒜 M₁.Q M₂.Q n b := rfl

/-- A11: multiplication by the curvature, `x ↦ c·x`. -/
def cMul : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁ where
  toFun x := GCDga.c (𝒜 := 𝒜) • x
  map_add' := smul_add _
  map_smul' r x := by
    rw [RingHom.id_apply]
    exact smul_algebra_smul_comm r (GCDga.c (𝒜 := 𝒜)) x

variable {𝒜 Q₁ Q₂ Q₃}

/-- A11: a Leibniz operator of degree `1` on a total module (not necessarily flat). -/
structure IsDiffOp (D : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁) : Prop where
  /-- `D` has total degree `1`. -/
  mem : ∀ {m : ℤ} {x : Tot 𝒜 Q₁}, x ∈ totDeg 𝒜 Q₁ m → D x ∈ totDeg 𝒜 Q₁ (m + 1)
  /-- Leibniz: `D(a·x) = da·x + (-1)^{|a|} a·Dx`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 Q₁,
    D (a • x) = GCDga.d (𝒜 := 𝒜) a • x + p.negOnePow • a • D x

/-- A11: the operator of a quasi-cohesive module is a Leibniz operator. -/
theorem QuasiCohesive.isDiffOp (M : QuasiCohesive 𝒜) : IsDiffOp M.X := ⟨M.X_mem, M.leibniz⟩

/-- A11: the differential `δφ = D₂ ∘ φ - (-1)^n φ ∘ D₁` for arbitrary operators. -/
def δT (D₁ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁) (D₂ : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₂) (n : ℤ)
    (φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂) : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂ :=
  D₂ ∘ₗ φ - n.negOnePow • (φ ∘ₗ D₁)

/-- A11: A4 `δ` is `δT` of the operators. -/
theorem δ_eq_δT (M₁ M₂ : QuasiCohesive 𝒜) (n : ℤ) (φ : M₁.T →ₗ[k] M₂.T) :
    δ M₁ M₂ n φ = δT M₁.X M₂.X n φ := rfl

/-- A11: `δT` maps `HomT^n` to `HomT^{n+1}` for Leibniz operators. -/
theorem δT_mem_of_diff {D₁ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁} {D₂ : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₂}
    (hD₁ : IsDiffOp D₁) (hD₂ : IsDiffOp D₂) {n : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂}
    (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n) : δT D₁ D₂ n φ ∈ HomT 𝒜 Q₁ Q₂ (n + 1) := by
  obtain ⟨h₁, h₂⟩ := hφ
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · have e1 : D₂ (φ x) ∈ totDeg 𝒜 Q₂ (m + (n + 1)) := by
      have := hD₂.mem (h₁ hx); rwa [add_assoc] at this
    have e2 : φ (D₁ x) ∈ totDeg 𝒜 Q₂ (m + (n + 1)) := by
      have := h₁ (hD₁.mem hx); rwa [add_assoc, add_comm 1 n] at this
    simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Units.smul_def]
    exact sub_mem e1 (Submodule.smul_of_tower_mem _ _ e2)
  · have hda := GCDga.d_mem (𝒜 := 𝒜) ha
    simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      hD₁.leibniz ha, map_add, h₂ ha, h₂ hda, hD₂.leibniz ha, Units.smul_def, map_zsmul]
    simp only [negOnePow_parity, parity_simps]
    by_cases hn : Even n <;> by_cases hp : Even p <;> simp [hn, hp, smul_sub, smul_neg]

/-- A11: `δT` maps `HomT^n` to `HomT^{n+1}` for operators in `HomT^1` (such as `∂̂`). -/
theorem δT_mem_of_hom {D₁ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁} {D₂ : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₂}
    (hD₁ : D₁ ∈ HomT 𝒜 Q₁ Q₁ 1) (hD₂ : D₂ ∈ HomT 𝒜 Q₂ Q₂ 1) {n : ℤ}
    {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n) :
    δT D₁ D₂ n φ ∈ HomT 𝒜 Q₁ Q₂ (n + 1) := by
  obtain ⟨h₁, h₂⟩ := hφ
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · have e1 : D₂ (φ x) ∈ totDeg 𝒜 Q₂ (m + (n + 1)) := by
      have := hD₂.1 (h₁ hx); rwa [add_assoc] at this
    have e2 : φ (D₁ x) ∈ totDeg 𝒜 Q₂ (m + (n + 1)) := by
      have := h₁ (hD₁.1 hx); rwa [add_assoc, add_comm 1 n] at this
    simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Units.smul_def]
    exact sub_mem e1 (Submodule.smul_of_tower_mem _ _ e2)
  · simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      hD₁.2 ha, h₂ ha, hD₂.2 ha, Units.smul_def, map_zsmul, smul_sub, smul_smul]
    simp only [negOnePow_parity, parity_simps]
    by_cases hn : Even n <;> by_cases hp : Even p <;> simp [hn, hp, smul_neg]

/-- A11: composition `HomT^m × HomT^n → HomT^{m+n}`. -/
theorem comp_mem_homT {m n : ℤ} {ψ : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₃} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂}
    (hψ : ψ ∈ HomT 𝒜 Q₂ Q₃ m) (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n) : ψ ∘ₗ φ ∈ HomT 𝒜 Q₁ Q₃ (m + n) := by
  refine ⟨fun {q x} hx => ?_, fun {p a} ha x => ?_⟩
  · have := hψ.1 (hφ.1 hx)
    rwa [add_assoc, add_comm n m] at this
  · simp only [LinearMap.comp_apply, hφ.2 ha, Units.smul_def, map_zsmul, hψ.2 ha, smul_smul]
    rw [← Units.val_mul, ← Int.negOnePow_add, add_mul, add_comm (m * p)]

/-- A11: `D² - c ∈ HomT²` for a Leibniz operator `D`. -/
theorem sq_sub_c_mem {D : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁} (hD : IsDiffOp D) :
    D ∘ₗ D - cMul 𝒜 Q₁ ∈ HomT 𝒜 Q₁ Q₁ 2 := by
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · have e1 := hD.mem (hD.mem hx)
    have e2 := smul_mem_totDeg (GCDga.c_mem (𝒜 := 𝒜)) hx
    rw [add_assoc, one_add_one_eq_two] at e1
    rw [add_comm] at e2
    exact sub_mem e1 e2
  · have hda := GCDga.d_mem (𝒜 := 𝒜) ha
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, cMul, LinearMap.coe_mk,
      AddHom.coe_mk, hD.leibniz ha, map_add, hD.leibniz hda, GCDga.d_d, zero_smul, zero_add,
      Units.smul_def, map_zsmul, smul_add, smul_smul, GCDga.c_central 𝒜 a,
      Int.negOnePow_two_mul, one_smul]
    simp only [negOnePow_parity, parity_simps]
    by_cases hp : Even p <;> simp [hp, smul_sub, ← smul_assoc]

/-- A11 (Bianchi): `δ(D² - c) = 0`. -/
theorem δT_sq_sub_c {D : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁} (hD : IsDiffOp D) :
    δT D D 2 (D ∘ₗ D - cMul 𝒜 Q₁) = 0 := by
  ext x
  have h2 : (2 : ℤ).negOnePow = 1 := Int.negOnePow_even 2 even_two
  simp only [δT, h2, one_smul, cMul, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, map_sub]
  rw [hD.leibniz (GCDga.c_mem (𝒜 := 𝒜)), GCDga.d_c, zero_smul, zero_add, h2, one_smul]
  abel

/-- A11 (Bianchi): `δ(δe) = -e(D² - c)` for `e ∈ HomT⁰` and a flat target operator. -/
theorem δT_δT_eq {D : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁} (X : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₂)
    (hX : ∀ x, X (X x) = GCDga.c (𝒜 := 𝒜) • x) {e : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂}
    (he : e ∈ HomT 𝒜 Q₁ Q₂ 0) :
    δT D X 1 (δT D X 0 e) = -(e ∘ₗ (D ∘ₗ D - cMul 𝒜 Q₁)) := by
  ext x
  have hc : e (GCDga.c (𝒜 := 𝒜) • x) = GCDga.c (𝒜 := 𝒜) • e x := by
    rw [he.2 (GCDga.c_mem (𝒜 := 𝒜)), zero_mul, Int.negOnePow_zero, one_smul]
  simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply, map_sub,
    Units.smul_def, Int.negOnePow_zero, Int.negOnePow_one, Units.val_one, Units.val_neg,
    one_smul, neg_smul]
  simp only [cMul, LinearMap.coe_mk, AddHom.coe_mk, hX, hc]
  abel

/-- A11: `FT` is decreasing. -/
theorem FT_anti {n b b' : ℤ} (h : b ≤ b') : FT 𝒜 Q₁ Q₂ n b' ≤ FT 𝒜 Q₁ Q₂ n b := by
  intro φ hφ
  obtain ⟨hφ₁, hφ₂⟩ := Submodule.mem_inf.1 hφ
  exact Submodule.mem_inf.2 ⟨hφ₁, fun c x hx => filTot_anti (by omega) (hφ₂ c x hx)⟩

/-- A11: `F^b` is determined on generators (A6 `memFilHom_iff`). -/
theorem memFT_iff {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n) :
    φ ∈ FT 𝒜 Q₁ Q₂ n b ↔ ∀ e, φ (Tot.tmul 𝒜 Q₁ 1 e) ∈ filTot 𝒜 Q₂ b := by
  constructor
  · intro h e
    have := (Submodule.mem_inf.1 h).2 0 (Tot.tmul 𝒜 Q₁ 1 e) (filTot_zero _)
    rwa [zero_add] at this
  · intro h
    refine Submodule.mem_inf.2 ⟨hφ, fun c x hx => ?_⟩
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, a, e, hcq, ha, rfl⟩ := hx
      rw [Tot.tmul_eq_smul, hφ.2 ha, Units.smul_def]
      refine Submodule.smul_of_tower_mem _ _ ?_
      exact filTot_anti (by omega) (smul_mem_filTot ha (h e))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- A11: `F^b = 0` for `b > N` (A6 `filHom_eq_zero`). -/
theorem FT_eq_zero {n b : ℤ} (hb : (GCDga.N 𝒜 : ℤ) < b) {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂}
    (hφ : φ ∈ FT 𝒜 Q₁ Q₂ n b) : φ = 0 := by
  obtain ⟨hφ₁, -⟩ := Submodule.mem_inf.1 hφ
  have h0 : ∀ e, φ (Tot.tmul 𝒜 Q₁ 1 e) = 0 := fun e => by
    have := (memFT_iff hφ₁).1 hφ e
    rwa [filTot_eq_bot hb, Submodule.mem_bot] at this
  ext x
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.tmul_eq_sum, map_sum, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Tot.tmul_eq_smul, hφ₁.2 (GCDga.proj_mem 𝒜 q a), h0, smul_zero, smul_zero]
  | hadd x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

end HomT

/-! ## Extension from generators and pure parts -/

section Pure

variable {Q₁ Q₂ : ℤ → Type} [∀ p, AddCommGroup (Q₁ p)] [∀ p, Module (𝒜 0) (Q₁ p)]
  [∀ p, AddCommGroup (Q₂ p)] [∀ p, Module (𝒜 0) (Q₂ p)]

/-- The additive map underlying `extT`. -/
def extTAdd (n : ℤ) (ψ : (⨁ p, Q₁ p) →+ Tot 𝒜 Q₂)
    (hψ : ∀ (f : 𝒜 0) e, ψ (f • e) = (f : A) • ψ e) : Tot 𝒜 Q₁ →+ Tot 𝒜 Q₂ :=
  TensorProduct.liftAddHom (R := 𝒜 0)
    (AddMonoidHom.mk'
      (fun a => AddMonoidHom.mk' (fun e => GCDga.twist 𝒜 n a • ψ e)
        (fun e e' => by rw [map_add, smul_add]))
      (fun a b => AddMonoidHom.ext fun e => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_smul]))
    fun r a e => by
      show GCDga.twist 𝒜 n (r • a) • ψ e = GCDga.twist 𝒜 n a • ψ (r • e)
      rw [(GCDga.twist 𝒜 n).map_smul, hψ r e, GCDga.smul0_def, ← mul_smul,
        GCDga.central 𝒜 r.2]

/-- A11: the extension `ψ̂(a ⊗ e) = (-1)^{n|a|} a·ψ(e)` of an `A⁰`-linear generator map (A4.c
`extGen` for generator families). -/
def extT (n : ℤ) (ψ : (⨁ p, Q₁ p) →+ Tot 𝒜 Q₂)
    (hψ : ∀ (f : 𝒜 0) e, ψ (f • e) = (f : A) • ψ e) : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂ where
  toFun := extTAdd n ψ hψ
  map_add' := (extTAdd n ψ hψ).map_add
  map_smul' r x := by
    induction x using Tot.induction_on with
    | ht a e =>
      show GCDga.twist 𝒜 n (r • a) • ψ e = r • (GCDga.twist 𝒜 n a • ψ e)
      rw [GCDga.twist_smul, smul_assoc]
    | hadd x y hx hy =>
      simp only [RingHom.id_apply] at hx hy ⊢
      rw [smul_add, (extTAdd n ψ hψ).map_add, hx, hy, (extTAdd n ψ hψ).map_add, smul_add]

/-- A11: `ψ̂` on pure tensors. -/
theorem extT_tmul (n : ℤ) (ψ : (⨁ p, Q₁ p) →+ Tot 𝒜 Q₂)
    (hψ : ∀ (f : 𝒜 0) e, ψ (f • e) = (f : A) • ψ e) (a : A) (e : ⨁ p, Q₁ p) :
    extT n ψ hψ (Tot.tmul 𝒜 Q₁ a e) = GCDga.twist 𝒜 n a • ψ e := rfl

/-- A11: `ψ̂(1 ⊗ e) = ψ(e)`. -/
theorem extT_tmul_one (n : ℤ) (ψ : (⨁ p, Q₁ p) →+ Tot 𝒜 Q₂)
    (hψ : ∀ (f : 𝒜 0) e, ψ (f • e) = (f : A) • ψ e) (e : ⨁ p, Q₁ p) :
    extT n ψ hψ (Tot.tmul 𝒜 Q₁ 1 e) = ψ e := by
  rw [extT_tmul, GCDga.twist_one, one_smul]

/-- A11: `ψ̂ ∈ HomT^n` when `ψ` has degree `n`. -/
theorem extT_mem (n : ℤ) (ψ : (⨁ p, Q₁ p) →+ Tot 𝒜 Q₂)
    (hψ : ∀ (f : 𝒜 0) e, ψ (f • e) = (f : A) • ψ e)
    (hdeg : ∀ p (e : Q₁ p), ψ (lof (𝒜 0) ℤ Q₁ p e) ∈ totDeg 𝒜 Q₂ (p + n)) :
    extT n ψ hψ ∈ HomT 𝒜 Q₁ Q₂ n := by
  refine ⟨fun {m x} hx => ?_, fun {p b} hb x => ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
      change extT n ψ hψ (Tot.tmul 𝒜 Q₁ a _) ∈ _
      rw [extT_tmul, GCDga.twist_of_mem 𝒜 n ha, Units.smul_def, smul_assoc]
      refine Submodule.smul_of_tower_mem _ _ ?_
      have := smul_mem_totDeg ha (hdeg p e)
      rwa [← add_assoc] at this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  · induction x using Tot.induction_on with
    | ht a e =>
      rw [Tot.smul_tmul, extT_tmul, extT_tmul, GCDga.twist_mul_of_mem 𝒜 n hb,
        Units.smul_def, Units.smul_def, smul_assoc, mul_smul]
    | hadd x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

/-- A11: `φ(a ⊗ e) = τₙ(a)·φ(1 ⊗ e)` for `φ ∈ HomT^n` (A4.c `hom_tmul`). -/
theorem homT_tmul {n : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n) (a : A)
    (e : ⨁ p, Q₁ p) : φ (Tot.tmul 𝒜 Q₁ a e) = GCDga.twist 𝒜 n a • φ (Tot.tmul 𝒜 Q₁ 1 e) := by
  conv_lhs => rw [Tot.tmul_eq_sum, map_sum]
  rw [GCDga.twist_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Tot.tmul_eq_smul (GCDga.proj 𝒜 q a) e, hφ.2 (GCDga.proj_mem 𝒜 q a), smul_assoc]

/-- A11: maps in `HomT^n` are determined on the generators `1 ⊗ e`. -/
theorem homT_ext {n : ℤ} {φ φ' : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n)
    (hφ' : φ' ∈ HomT 𝒜 Q₁ Q₂ n) (h : ∀ e, φ (Tot.tmul 𝒜 Q₁ 1 e) = φ' (Tot.tmul 𝒜 Q₁ 1 e)) :
    φ = φ' := by
  ext x
  induction x using Tot.induction_on with
  | ht a e => rw [homT_tmul hφ, homT_tmul hφ', h]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- A11: `π_b` is idempotent. -/
theorem projF_projF (b : ℤ) (y : Tot 𝒜 Q₂) :
    Tot.projF 𝒜 Q₂ b (Tot.projF 𝒜 Q₂ b y) = Tot.projF 𝒜 Q₂ b y := by
  induction y using Tot.induction_on with
  | ht a e =>
    rw [Tot.projF_tmul, Tot.projF_tmul_of_mem (GCDga.proj_mem 𝒜 b a)]
    simp only [↓reduceIte]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- A11: `π_b` lands in `F^b`. -/
theorem projF_mem_filTot (b : ℤ) (y : Tot 𝒜 Q₂) : Tot.projF 𝒜 Q₂ b y ∈ filTot 𝒜 Q₂ b := by
  induction y using Tot.induction_on with
  | ht a e => exact tmul_mem_filTot le_rfl (GCDga.proj_mem 𝒜 b a) e
  | hadd x y hx hy => rw [map_add]; exact add_mem hx hy

/-- A11: `π_b` preserves the total degree. -/
theorem projF_mem_totDeg (b : ℤ) {m : ℤ} {y : Tot 𝒜 Q₂} (hy : y ∈ totDeg 𝒜 Q₂ m) :
    Tot.projF 𝒜 Q₂ b y ∈ totDeg 𝒜 Q₂ m := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change Tot.projF 𝒜 Q₂ b (Tot.tmul 𝒜 Q₂ a _) ∈ _
    rw [Tot.projF_tmul_of_mem ha]
    split_ifs
    · exact tmul_mem_totDeg ha e
    · exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [Tot.projF_smul_k]; exact Submodule.smul_mem _ r hx

/-- A11: for `y ∈ F^b`, `y - π_b y ∈ F^{b+1}`. -/
theorem sub_projF_mem_filTot {b : ℤ} {y : Tot 𝒜 Q₂} (hy : y ∈ filTot 𝒜 Q₂ b) :
    y - Tot.projF 𝒜 Q₂ b y ∈ filTot 𝒜 Q₂ (b + 1) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hbq, ha, rfl⟩ := hx
    rw [Tot.projF_tmul_of_mem ha]
    split_ifs with h
    · rw [sub_self]; exact zero_mem _
    · rw [sub_zero]; exact tmul_mem_filTot (by omega) ha e
  | zero => rw [map_zero, sub_zero]; exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, add_sub_add_comm]; exact add_mem hx hy
  | smul r x _ hx => rw [Tot.projF_smul_k, ← smul_sub]; exact Submodule.smul_mem _ r hx

/-- A11: `π_b` vanishes on `F^{b+1}`. -/
theorem projF_eq_zero_of_mem {b : ℤ} {y : Tot 𝒜 Q₂} (hy : y ∈ filTot 𝒜 Q₂ (b + 1)) :
    Tot.projF 𝒜 Q₂ b y = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hbq, ha, rfl⟩ := hx
    rw [Tot.projF_tmul_of_mem ha]
    simp only [show ¬q = b by omega, ↓reduceIte]
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [Tot.projF_smul_k, hx, smul_zero]

/-- A11: `φ` is pure of form degree `b`: `φ(1 ⊗ e)` has form degree exactly `b`. -/
def IsPure (b : ℤ) (φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂) : Prop :=
  ∀ e, Tot.projF 𝒜 Q₂ b (φ (Tot.tmul 𝒜 Q₁ 1 e)) = φ (Tot.tmul 𝒜 Q₁ 1 e)

/-- A11: the pure part of form degree `b` of `φ ∈ HomT^n`: the extension of
`e ↦ π_b(φ(1 ⊗ e))`. -/
def pure {n : ℤ} (b : ℤ) (φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂) (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n) :
    Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂ :=
  extT n ((Tot.projF 𝒜 Q₂ b).toAddMonoidHom.comp
    (φ.toAddMonoidHom.comp (Tot.oneTmul 𝒜 Q₁).toAddMonoidHom)) fun f e => by
    show Tot.projF 𝒜 Q₂ b (φ (Tot.oneTmul 𝒜 Q₁ (f • e))) =
      (f : A) • Tot.projF 𝒜 Q₂ b (φ (Tot.oneTmul 𝒜 Q₁ e))
    rw [(Tot.oneTmul 𝒜 Q₁).map_smul, Tot.smul0_eq, hφ.2 f.2, mul_zero, Int.negOnePow_zero,
      one_smul, ← Tot.smul0_eq, (Tot.projF 𝒜 Q₂ b).map_smul, Tot.smul0_eq]

/-- A11: the pure part on generators: `pure_b φ (1 ⊗ e) = π_b(φ(1 ⊗ e))`. -/
theorem pure_tmul_one {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n)
    (e : ⨁ p, Q₁ p) :
    pure b φ hφ (Tot.tmul 𝒜 Q₁ 1 e) = Tot.projF 𝒜 Q₂ b (φ (Tot.tmul 𝒜 Q₁ 1 e)) :=
  extT_tmul_one n _ _ e

/-- A11: the pure part lies in `HomT^n`. -/
theorem pure_mem {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n) :
    pure b φ hφ ∈ HomT 𝒜 Q₁ Q₂ n := by
  refine extT_mem n _ _ fun p e => ?_
  show Tot.projF 𝒜 Q₂ b (φ (Tot.tmul 𝒜 Q₁ 1 (lof (𝒜 0) ℤ Q₁ p e))) ∈ _
  refine projF_mem_totDeg b (hφ.1 ?_)
  have := tmul_mem_totDeg (Q := Q₁) (SetLike.GradedOne.one_mem (A := 𝒜)) e
  rwa [zero_add] at this

/-- A11: the pure part is pure. -/
theorem pure_isPure {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n) :
    IsPure b (pure b φ hφ) := fun e => by
  rw [pure_tmul_one, projF_projF]

/-- A11: the pure part of a pure map is the map. -/
theorem pure_eq_self {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n)
    (h : IsPure b φ) : pure b φ hφ = φ :=
  homT_ext (pure_mem hφ) hφ fun e => by rw [pure_tmul_one, h e]

/-- A11: a pure map of degree `b` lies in `F^b`. -/
theorem mem_FT_of_isPure {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n)
    (h : IsPure b φ) : φ ∈ FT 𝒜 Q₁ Q₂ n b :=
  (memFT_iff hφ).2 fun e => by rw [← h e]; exact projF_mem_filTot b _

/-- A11: for `φ ∈ F^b`, `φ - pure_b φ ∈ F^{b+1}`. -/
theorem sub_pure_mem {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ FT 𝒜 Q₁ Q₂ n b) :
    φ - pure b φ (Submodule.mem_inf.1 hφ).1 ∈ FT 𝒜 Q₁ Q₂ n (b + 1) := by
  have h₁ := (Submodule.mem_inf.1 hφ).1
  refine (memFT_iff (sub_mem h₁ (pure_mem h₁))).2 fun e => ?_
  rw [LinearMap.sub_apply, pure_tmul_one]
  exact sub_projF_mem_filTot ((memFT_iff h₁).1 hφ e)

/-- A11: the pure part of degree `b` of `φ ∈ F^{b+1}` vanishes. -/
theorem pure_eq_zero {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ FT 𝒜 Q₁ Q₂ n (b + 1)) :
    pure b φ (Submodule.mem_inf.1 hφ).1 = 0 := by
  have h₁ := (Submodule.mem_inf.1 hφ).1
  refine homT_ext (pure_mem h₁) (zero_mem _) fun e => ?_
  rw [pure_tmul_one, LinearMap.zero_apply]
  exact projF_eq_zero_of_mem ((memFT_iff h₁).1 hφ e)

end Pure

end Cohesive
end
