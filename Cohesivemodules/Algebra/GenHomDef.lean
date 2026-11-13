-- FROZEN (gate 4, 29 Oct 2026; A4.c generator maps, in the main statement). Do not edit.
import Cohesivemodules.Algebra.CohesiveDef
import Cohesivemodules.Algebra.GeneratorsDef
import Mathlib.Data.Int.Interval

set_option linter.style.header false

/-!
# A4.c: generator maps (definitions)

Blueprint item A4.c (definitions only). These definitions enter the main statement through the
functor J (C1), via the base change of morphisms `bcHomL` (A9, `Algebra/BaseChangeHomDef.lean`);
this file is to be frozen at gate 4. Theorems about them stay in `Algebra/Cohesive.lean`.

* `GCDga.twist n`: the sign twist `τₙ(a) = Σ_q (-1)^{nq} a_q`, with its basic API.
* `Tot.smul0_eq`, `Tot.oneTmul`: the `A⁰`-action on the total module and the generator
  embedding `e ↦ 1 ⊗ e`.
* `GenHom M₁ M₂ n`: generator maps of degree `n`; `restrictGen`: restriction of a map in
  `Hom^n` to the generators; `extGen`: the extension `ψ̂(a ⊗ e) = (-1)^{n|a|} a·ψ(e)`, and
  `extGen_mem : extGen n ψ ∈ Hom^n`.
-/

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

namespace GCDga

/-- The sign twist `τₙ(a) = Σ_q (-1)^{nq} a_q` (so `τ₁ = σ`, `τ₀ = id`). -/
def twist (n : ℤ) : A →ₗ[𝒜 0] A :=
  ∑ q ∈ Finset.Icc (0 : ℤ) (N 𝒜), (n * q).negOnePow • proj 𝒜 q

/-- Formula for `twist`. -/
theorem twist_apply (n : ℤ) (a : A) :
    twist 𝒜 n a = ∑ q ∈ Finset.Icc (0 : ℤ) (N 𝒜), (n * q).negOnePow • proj 𝒜 q a := by
  simp [twist, LinearMap.sum_apply]

/-- `τₙ(a) = (-1)^{np} a` for `a ∈ A^p`. -/
theorem twist_of_mem (n : ℤ) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) :
    twist 𝒜 n a = (n * p).negOnePow • a := by
  rw [twist_apply]
  simp_rw [proj_of_mem 𝒜 ha]
  by_cases hp : p ∈ Finset.Icc (0 : ℤ) (N 𝒜)
  · rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (fun h => absurd hp h)]
    simp
  · have : a = 0 := by
      have := proj_eq_zero_of_not_mem 𝒜 hp a
      rwa [proj_of_mem 𝒜 ha, ite_eq_left_iff.2 (fun h => absurd rfl h)] at this
    simp [this]

/-- `τₙ(1) = 1`. -/
theorem twist_one (n : ℤ) : twist 𝒜 n 1 = 1 := by
  rw [twist_of_mem 𝒜 n (SetLike.GradedOne.one_mem (A := 𝒜)), mul_zero, Int.negOnePow_zero,
    one_smul]

/-- `τ₀ = id`. -/
theorem twist_zero (a : A) : twist 𝒜 0 a = a := by
  simp only [twist_apply, zero_mul, Int.negOnePow_zero, one_smul, sum_proj]

/-- `τₙ(b a) = (-1)^{np} b τₙ(a)` for `b ∈ A^p`. -/
theorem twist_mul_of_mem (n : ℤ) {p : ℤ} {b : A} (hb : b ∈ 𝒜 p) (a : A) :
    twist 𝒜 n (b * a) = (n * p).negOnePow • (b * twist 𝒜 n a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add, smul_add]
  | @homogeneous q y =>
    rw [twist_of_mem 𝒜 n (SetLike.GradedMul.mul_mem hb y.2), twist_of_mem 𝒜 n y.2,
      mul_add, Int.negOnePow_add, mul_smul_comm, smul_smul]

/-- `τₙ` is `k`-linear. -/
theorem twist_smul (n : ℤ) (r : k) (a : A) : twist 𝒜 n (r • a) = r • twist 𝒜 n a := by
  simp only [twist_apply, proj_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => smul_comm _ _ _

end GCDga

variable {𝒜} {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

namespace Tot

/-- On the total module, the `A⁰`-action is the restriction of the `A`-action. -/
theorem smul0_eq (f : 𝒜 0) (x : Tot 𝒜 Q) : f • x = (f : A) • x := by
  induction x using induction_on with
  | ht a e => exact (TensorProduct.smul_tmul' (R := 𝒜 0) f a e).trans (smul_tmul (f : A) a e).symm
  | hadd x y hx hy => rw [smul_add, hx, hy, smul_add]

variable (𝒜 Q) in
/-- The generator embedding `e ↦ 1 ⊗ e`. -/
def oneTmul : (⨁ p, Q p) →ₗ[𝒜 0] Tot 𝒜 Q :=
  (TensorProduct.mk (𝒜 0) A (⨁ p, Q p)) 1

/-- Formula for `oneTmul`. -/
theorem oneTmul_apply (e : ⨁ p, Q p) : oneTmul 𝒜 Q e = tmul 𝒜 Q 1 e := rfl

end Tot

/-! ## A4.c: generator form of `Hom` -/

section GenHom

variable (M₁ M₂ : QuasiCohesive 𝒜)

/-- **A4.c** Generator maps of degree `n`: `A⁰`-linear maps `ψ : ⨁_p Q₁^p → A ⊗_{A⁰} ⨁ Q₂` with
`ψ(Q₁^p) ⊆ (A ⊗ Q₂)^{p+n}`, i.e. `⊕_p Hom_{A⁰}(Q₁^p, (A ⊗ Q₂)^{p+n})` (conventions §4,
encoding 2). -/
def GenHom (n : ℤ) : Submodule k ((⨁ p, M₁.Q p) →+ M₂.T) where
  carrier := {ψ | (∀ (f : 𝒜 0) e, ψ (f • e) = (f : A) • ψ e) ∧
    ∀ p (e : M₁.Q p), ψ (lof (𝒜 0) ℤ M₁.Q p e) ∈ totDeg 𝒜 M₂.Q (p + n)}
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => zero_mem _⟩
  add_mem' := fun hψ hφ => ⟨fun f e => by simp [hψ.1 f e, hφ.1 f e, smul_add],
    fun p e => add_mem (hψ.2 p e) (hφ.2 p e)⟩
  smul_mem' := fun r ψ hψ => ⟨fun f e => by
      simp only [AddMonoidHom.smul_apply, hψ.1 f e]
      exact (smul_algebra_smul_comm r (f : A) (ψ e)).symm,
    fun p e => Submodule.smul_mem _ r (hψ.2 p e)⟩

variable {M₁ M₂}

/-- **A4.c** Restriction to generators `φ ↦ (e ↦ φ(1 ⊗ e))`. -/
def restrictGen (n : ℤ) : Hom M₁ M₂ n →ₗ[k] GenHom M₁ M₂ n where
  toFun φ := ⟨(φ.1.toAddMonoidHom).comp (Tot.oneTmul 𝒜 M₁.Q).toAddMonoidHom,
    ⟨fun f e => by
      show φ.1 (Tot.oneTmul 𝒜 M₁.Q (f • e)) = (f : A) • φ.1 (Tot.oneTmul 𝒜 M₁.Q e)
      rw [(Tot.oneTmul 𝒜 M₁.Q).map_smul, Tot.smul0_eq, φ.2.2 f.2, mul_zero, Int.negOnePow_zero,
        one_smul],
     fun p e => by
      have := φ.2.1 (tmul_mem_totDeg (Q := M₁.Q) (SetLike.GradedOne.one_mem (A := 𝒜)) e)
      rwa [zero_add] at this⟩⟩
  map_add' φ ψ := rfl
  map_smul' r φ := rfl

variable (n : ℤ) (ψ : GenHom M₁ M₂ n)

/-- The bi-additive map `(a, e) ↦ τₙ(a)·ψ(e)`. -/
def extGenAux : A →+ (⨁ p, M₁.Q p) →+ M₂.T :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk' (fun e => GCDga.twist 𝒜 n a • ψ.1 e)
      (fun e e' => by rw [map_add, smul_add]))
    (fun a b => AddMonoidHom.ext fun e => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_smul])

/-- **A4.c** The extension `ψ̂(a ⊗ e) = (-1)^{n|a|} a·ψ(e)` (conventions §2). -/
def extGenAdd : M₁.T →+ M₂.T :=
  TensorProduct.liftAddHom (R := 𝒜 0) (extGenAux n ψ) fun r a e => by
    show GCDga.twist 𝒜 n (r • a) • ψ.1 e = GCDga.twist 𝒜 n a • ψ.1 (r • e)
    rw [(GCDga.twist 𝒜 n).map_smul, ψ.2.1 r e, GCDga.smul0_def, ← mul_smul,
      GCDga.central 𝒜 r.2]

/-- `ψ̂` on pure tensors. -/
theorem extGenAdd_tmul (a : A) (e : ⨁ p, M₁.Q p) :
    extGenAdd n ψ (Tot.tmul 𝒜 M₁.Q a e) = GCDga.twist 𝒜 n a • ψ.1 e := rfl

/-- **A4.c** `ψ̂` is `k`-linear. -/
def extGen : M₁.T →ₗ[k] M₂.T where
  toFun := extGenAdd n ψ
  map_add' := (extGenAdd n ψ).map_add
  map_smul' r x := by
    induction x using Tot.induction_on with
    | ht a e =>
      rw [Tot.smul_tmul_k, RingHom.id_apply, extGenAdd_tmul, extGenAdd_tmul, GCDga.twist_smul,
        smul_assoc]
    | hadd x y hx hy =>
      simp only [RingHom.id_apply] at hx hy ⊢
      rw [smul_add, (extGenAdd n ψ).map_add, hx, hy, (extGenAdd n ψ).map_add, smul_add]

/-- **A4.c** `ψ̂ ∈ Hom^n`. -/
theorem extGen_mem : extGen n ψ ∈ Hom M₁ M₂ n := by
  refine ⟨fun {m x} hx => ?_, fun {p b} hb x => ?_⟩
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
      change extGenAdd n ψ (Tot.tmul 𝒜 M₁.Q a _) ∈ _
      rw [extGenAdd_tmul, GCDga.twist_of_mem 𝒜 n ha, Units.smul_def, smul_assoc]
      refine Submodule.smul_of_tower_mem _ _ ?_
      have := smul_mem_totDeg ha (ψ.2.2 p e)
      rwa [← add_assoc] at this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  · induction x using Tot.induction_on with
    | ht a e =>
      change extGenAdd n ψ (b • Tot.tmul 𝒜 M₁.Q a e) = _ • b • extGenAdd n ψ (Tot.tmul 𝒜 M₁.Q a e)
      rw [Tot.smul_tmul, extGenAdd_tmul, extGenAdd_tmul, GCDga.twist_mul_of_mem 𝒜 n hb,
        Units.smul_def, Units.smul_def, smul_assoc, mul_smul]
    | hadd x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

end GenHom

end Cohesive
