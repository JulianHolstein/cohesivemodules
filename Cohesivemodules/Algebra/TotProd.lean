import Cohesivemodules.Algebra.GeneratorsDef
import Mathlib.LinearAlgebra.TensorProduct.Prod

set_option linter.style.header false

/-!
# Z2.c: the total module of a product family

Blueprint item Z2.c (`blueprint/blueprint-tr.md` §3a; blueprint §11 v1.18). For two families of
`A⁰`-modules `Q₁`, `Q₂`, the total module of the degreewise product `(Q₁ × Q₂)^p = Q₁^p × Q₂^p`
is the product of the total modules:
`Tot.prodEquiv : A ⊗_{A⁰} ⨁_p (Q₁^p × Q₂^p) ≃ₗ[A] (A ⊗_{A⁰} ⨁_p Q₁^p) × (A ⊗_{A⁰} ⨁_p Q₂^p)`
(direct sums commute with finite products, `dsumProdEquiv`; the tensor product distributes,
Mathlib's `TensorProduct.prodRight`). It preserves total degree componentwise
(`prodEquiv_mem_totDeg_iff`). The cone (Z2.d) uses it to write its structure maps as
`LinearMap.inl/inr/fst/snd`.
-/

noncomputable section

namespace Cohesive

open DirectSum TensorProduct

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- **Z2.c.** The degreewise product of two families of generators, `(Q₁ × Q₂)^p = Q₁^p × Q₂^p`
(an `abbrev`: the `Prod` instances apply directly). -/
abbrev prodQ (Q₁ Q₂ : ℤ → Type) : ℤ → Type := fun p => Q₁ p × Q₂ p

variable (Q₁ Q₂ : ℤ → Type) [∀ p, AddCommGroup (Q₁ p)] [∀ p, AddCommGroup (Q₂ p)]
  [∀ p, Module (𝒜 0) (Q₁ p)] [∀ p, Module (𝒜 0) (Q₂ p)]

variable (𝒜) in
/-- **Z2.c.** `⨁_p (Q₁^p × Q₂^p) ≃ (⨁_p Q₁^p) × (⨁_p Q₂^p)` as `A⁰`-modules,
`lof p (e₁, e₂) ↦ (lof p e₁, lof p e₂)`. -/
def dsumProdEquiv : (⨁ p, prodQ Q₁ Q₂ p) ≃ₗ[𝒜 0] (⨁ p, Q₁ p) × (⨁ p, Q₂ p) :=
  LinearEquiv.ofLinearMap
    (DirectSum.toModule (𝒜 0) ℤ _ fun p =>
      (lof (𝒜 0) ℤ Q₁ p).prodMap (lof (𝒜 0) ℤ Q₂ p))
    (LinearMap.coprod
      (DirectSum.toModule (𝒜 0) ℤ _ fun p =>
        lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p ∘ₗ LinearMap.inl (𝒜 0) (Q₁ p) (Q₂ p))
      (DirectSum.toModule (𝒜 0) ℤ _ fun p =>
        lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p ∘ₗ LinearMap.inr (𝒜 0) (Q₁ p) (Q₂ p)))
    (by
      refine LinearMap.prod_ext ?_ ?_ <;> refine DirectSum.linearMap_ext _ fun p => ?_ <;>
        refine LinearMap.ext fun e => ?_ <;> simp)
    (by
      refine DirectSum.linearMap_ext _ fun p => LinearMap.ext fun e => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, toModule_lof, LinearMap.prodMap_apply,
        LinearMap.coprod_apply, LinearMap.id_coe, id_eq, LinearMap.inl_apply,
        LinearMap.inr_apply]
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add])

omit [GCDga 𝒜] in
/-- Z2.c: `dsumProdEquiv` on a generator. -/
@[simp] theorem dsumProdEquiv_lof (p : ℤ) (e : prodQ Q₁ Q₂ p) :
    dsumProdEquiv 𝒜 Q₁ Q₂ (lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p e) =
      (lof (𝒜 0) ℤ Q₁ p e.1, lof (𝒜 0) ℤ Q₂ p e.2) := by
  simp [dsumProdEquiv]

omit [GCDga 𝒜] in
/-- Z2.c: `dsumProdEquiv⁻¹` on a generator of the first factor. -/
@[simp] theorem dsumProdEquiv_symm_lof_fst (p : ℤ) (e : Q₁ p) :
    (dsumProdEquiv 𝒜 Q₁ Q₂).symm (lof (𝒜 0) ℤ Q₁ p e, 0) =
      lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p ((e, 0) : Q₁ p × Q₂ p) := by
  rw [LinearEquiv.symm_apply_eq, dsumProdEquiv_lof, map_zero]

omit [GCDga 𝒜] in
/-- Z2.c: `dsumProdEquiv⁻¹` on a generator of the second factor. -/
@[simp] theorem dsumProdEquiv_symm_lof_snd (p : ℤ) (e : Q₂ p) :
    (dsumProdEquiv 𝒜 Q₁ Q₂).symm (0, lof (𝒜 0) ℤ Q₂ p e) =
      lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p ((0, e) : Q₁ p × Q₂ p) := by
  rw [LinearEquiv.symm_apply_eq, dsumProdEquiv_lof, map_zero]

variable (𝒜) in
/-- **Z2.c.** `Tot(Q₁ × Q₂) ≃ₗ[A] Tot(Q₁) × Tot(Q₂)`, `α ⊗ (e₁, e₂) ↦ (α ⊗ e₁, α ⊗ e₂)`: the
direct sum of a product family is the product of the direct sums (`dsumProdEquiv`), and
`A ⊗_{A⁰} -` distributes over products (`TensorProduct.prodRight`). `A`-linear, hence `k`-linear
(`LinearEquiv.restrictScalars k`). -/
def Tot.prodEquiv : Tot 𝒜 (prodQ Q₁ Q₂) ≃ₗ[A] Tot 𝒜 Q₁ × Tot 𝒜 Q₂ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) (dsumProdEquiv 𝒜 Q₁ Q₂)).trans
    (TensorProduct.prodRight (𝒜 0) A A (⨁ p, Q₁ p) (⨁ p, Q₂ p))

/-- Z2.c: `Tot.prodEquiv (α ⊗ e) = (α ⊗ e₁, α ⊗ e₂)` where `(e₁, e₂) = dsumProdEquiv e`. -/
theorem Tot.prodEquiv_tmul (α : A) (e : ⨁ p, prodQ Q₁ Q₂ p) :
    Tot.prodEquiv 𝒜 Q₁ Q₂ (Tot.tmul 𝒜 (prodQ Q₁ Q₂) α e) =
      (Tot.tmul 𝒜 Q₁ α (dsumProdEquiv 𝒜 Q₁ Q₂ e).1,
        Tot.tmul 𝒜 Q₂ α (dsumProdEquiv 𝒜 Q₁ Q₂ e).2) :=
  TensorProduct.prodRight_tmul (𝒜 0) A A (⨁ p, Q₁ p) (⨁ p, Q₂ p) α _

/-- Z2.c: `Tot.prodEquiv (α ⊗ (e₁, e₂)) = (α ⊗ e₁, α ⊗ e₂)` on a generator. -/
@[simp] theorem Tot.prodEquiv_tmul_lof (α : A) (p : ℤ) (e : prodQ Q₁ Q₂ p) :
    Tot.prodEquiv 𝒜 Q₁ Q₂ (Tot.tmul 𝒜 (prodQ Q₁ Q₂) α (lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p e)) =
      (Tot.tmul 𝒜 Q₁ α (lof (𝒜 0) ℤ Q₁ p e.1), Tot.tmul 𝒜 Q₂ α (lof (𝒜 0) ℤ Q₂ p e.2)) := by
  rw [Tot.prodEquiv_tmul, dsumProdEquiv_lof]

/-- Z2.c: `Tot.prodEquiv⁻¹ (α ⊗ e₁, 0) = α ⊗ (e₁, 0)`. -/
@[simp] theorem Tot.prodEquiv_symm_tmul_fst (α : A) (p : ℤ) (e : Q₁ p) :
    (Tot.prodEquiv 𝒜 Q₁ Q₂).symm (Tot.tmul 𝒜 Q₁ α (lof (𝒜 0) ℤ Q₁ p e), 0) =
      Tot.tmul 𝒜 (prodQ Q₁ Q₂) α (lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p ((e, 0) : Q₁ p × Q₂ p)) := by
  rw [LinearEquiv.symm_apply_eq, Tot.prodEquiv_tmul_lof, map_zero, Tot.tmul_zero]

/-- Z2.c: `Tot.prodEquiv⁻¹ (0, α ⊗ e₂) = α ⊗ (0, e₂)`. -/
@[simp] theorem Tot.prodEquiv_symm_tmul_snd (α : A) (p : ℤ) (e : Q₂ p) :
    (Tot.prodEquiv 𝒜 Q₁ Q₂).symm (0, Tot.tmul 𝒜 Q₂ α (lof (𝒜 0) ℤ Q₂ p e)) =
      Tot.tmul 𝒜 (prodQ Q₁ Q₂) α (lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p ((0, e) : Q₁ p × Q₂ p)) := by
  rw [LinearEquiv.symm_apply_eq, Tot.prodEquiv_tmul_lof, map_zero, Tot.tmul_zero]

/-- Z2.c: `Tot.prodEquiv⁻¹ (y, 0)` has the total degree of `y`. -/
private theorem symm_fst_mem {m : ℤ} {y : Tot 𝒜 Q₁} (hy : y ∈ totDeg 𝒜 Q₁ m) :
    (Tot.prodEquiv 𝒜 Q₁ Q₂).symm (y, 0) ∈ totDeg 𝒜 (prodQ Q₁ Q₂) m := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hy
    exact (Tot.prodEquiv_symm_tmul_fst (𝒜 := 𝒜) Q₁ Q₂ a p e).symm ▸ tmul_mem_totDeg ha _
  | zero => rw [Prod.mk_zero_zero, map_zero]; exact zero_mem _
  | add y y' _ _ hy hy' =>
    rw [show ((y + y', 0) : Tot 𝒜 Q₁ × Tot 𝒜 Q₂) = (y, 0) + (y', 0) by simp, map_add]
    exact add_mem hy hy'
  | smul r y _ hy =>
    rw [show ((r • y, 0) : Tot 𝒜 Q₁ × Tot 𝒜 Q₂) = r • (y, 0) by simp,
      ← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ r hy

/-- Z2.c: `Tot.prodEquiv⁻¹ (0, y)` has the total degree of `y`. -/
private theorem symm_snd_mem {m : ℤ} {y : Tot 𝒜 Q₂} (hy : y ∈ totDeg 𝒜 Q₂ m) :
    (Tot.prodEquiv 𝒜 Q₁ Q₂).symm (0, y) ∈ totDeg 𝒜 (prodQ Q₁ Q₂) m := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hy
    exact (Tot.prodEquiv_symm_tmul_snd (𝒜 := 𝒜) Q₁ Q₂ a p e).symm ▸ tmul_mem_totDeg ha _
  | zero => rw [Prod.mk_zero_zero, map_zero]; exact zero_mem _
  | add y y' _ _ hy hy' =>
    rw [show ((0, y + y') : Tot 𝒜 Q₁ × Tot 𝒜 Q₂) = (0, y) + (0, y') by simp, map_add]
    exact add_mem hy hy'
  | smul r y _ hy =>
    rw [show ((0, r • y) : Tot 𝒜 Q₁ × Tot 𝒜 Q₂) = r • (0, y) by simp,
      ← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ r hy

/-- **Z2.c.** `Tot.prodEquiv` preserves total degree componentwise: `x` has total degree `m` iff
both components of `Tot.prodEquiv x` do. -/
theorem Tot.prodEquiv_mem_totDeg_iff (m : ℤ) (x : Tot 𝒜 (prodQ Q₁ Q₂)) :
    x ∈ totDeg 𝒜 (prodQ Q₁ Q₂) m ↔
      (Tot.prodEquiv 𝒜 Q₁ Q₂ x).1 ∈ totDeg 𝒜 Q₁ m ∧
        (Tot.prodEquiv 𝒜 Q₁ Q₂ x).2 ∈ totDeg 𝒜 Q₂ m := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
      rw [show (a ⊗ₜ[𝒜 0] lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p e : A ⊗[𝒜 0] _) =
        Tot.tmul 𝒜 (prodQ Q₁ Q₂) a (lof (𝒜 0) ℤ (prodQ Q₁ Q₂) p e) from rfl,
        Tot.prodEquiv_tmul_lof]
      exact ⟨tmul_mem_totDeg ha _, tmul_mem_totDeg ha _⟩
    | zero => rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy => rw [map_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | smul r x _ hx =>
      rw [← LinearEquiv.coe_toLinearMap, LinearMap.map_smul_of_tower]
      exact ⟨Submodule.smul_mem _ r hx.1, Submodule.smul_mem _ r hx.2⟩
  · rintro ⟨h₁, h₂⟩
    have hx : x = (Tot.prodEquiv 𝒜 Q₁ Q₂).symm ((Tot.prodEquiv 𝒜 Q₁ Q₂ x).1, 0) +
        (Tot.prodEquiv 𝒜 Q₁ Q₂).symm (0, (Tot.prodEquiv 𝒜 Q₁ Q₂ x).2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, LinearEquiv.symm_apply_apply]
    rw [hx]
    exact add_mem (symm_fst_mem Q₁ Q₂ h₁) (symm_snd_mem Q₁ Q₂ h₂)

/-- Z2.c: the inverse form of `Tot.prodEquiv_mem_totDeg_iff`. -/
theorem Tot.prodEquiv_symm_mem_totDeg_iff (m : ℤ) (y : Tot 𝒜 Q₁ × Tot 𝒜 Q₂) :
    (Tot.prodEquiv 𝒜 Q₁ Q₂).symm y ∈ totDeg 𝒜 (prodQ Q₁ Q₂) m ↔
      y.1 ∈ totDeg 𝒜 Q₁ m ∧ y.2 ∈ totDeg 𝒜 Q₂ m := by
  rw [Tot.prodEquiv_mem_totDeg_iff, LinearEquiv.apply_symm_apply]

end Cohesive
