import Cohesivemodules.ChecksCurved

set_option linter.style.header false

/-!
# Check K12b: a curved dga whose `Ho(P)` vanishes

`A = k[c]/(c²)` with `|c| = 2`, `d = 0` and curvature `c`: the square-zero toy of `ChecksCurved`
with `m₀ = 0`, `m₁ = 1` (`ctoyGr k 0 1`: `k` in degree 0, `k·c` in degree 2) and the curvature of
the flat instance `ctoyGCDga 0` replaced by `c` (`withC`). Every object of `Ho(P_A)` is zero.

Proof. `A` has only even degrees, so `Hom^n` consists of `A`-linear maps. On `Tot = A ⊗_{A⁰} ⨁Q`
let `P` be the degree-0 part and `L` the coefficient of `c` (`y = Py + c·Ly`), and
`φ = L𝕏P + (1 − P)𝕏L ∈ Hom⁻¹`. Applying `L` to `𝕏²w = c·w` gives `P(δφ) = id` on `A⁰ ⊗ ⨁Q`, so
`N = δφ − id` lands in `c·Tot` and commutes with `c·`; hence `N² = 0`, and `isZero_of_contraction`
applies. (Block's components: `𝕏 = 𝕏₀ + c𝕏₂` with `[𝕏₀, 𝕏₂] = id`.)

## Deviation
Added by the human (3 Nov 2026) as `k[t, t⁻¹]`, `|t| = 0`, `d = 0`, curvature `t`; that algebra is
outside the `GCDga` class (the curvature has degree 2 and the algebra is bounded, so `c` is
nilpotent). `k[c]/(c²)` is the bounded `ℤ`-graded counterpart, chosen by the human.
-/

namespace Cohesive.Checks

open DirectSum TensorProduct CategoryTheory Limits

variable {k : Type} [CommRing k]

/-- K12b: the element `c = (0, 0, 1)` of `Toy k 0 1`. -/
def czC : Toy k 0 1 := TrivSqZeroExt.inr (0, fun _ => 1)

/-- K12b: `c` has degree 2. -/
theorem czC_mem : (czC : Toy k 0 1) ∈ ctoyGr k 0 1 2 := by
  simp [ctoyGr, czC]

/-- K12b: `dc = 0` (`d = 0`). -/
theorem czC_d : (ctoyGCDga (k := k) (m₀ := 0) (m₁ := 1) 0).d czC = 0 := by
  show TrivSqZeroExt.inr (0, ((0 : (Fin 0 → k) →ₗ[k] (Fin 1 → k)) (czC : Toy k 0 1).snd.1)) = 0
  ext <;> simp
  rename_i i
  exact i.elim0

/-- **K12b.** The curved dga `k[c]/(c²)`, `|c| = 2`, `d = 0`, curvature `c`. -/
instance czInst : GCDga (ctoyGr k 0 1) := (ctoyGCDga 0).withC czC czC_mem czC_d

/-- K12b: the curvature is `c` (rfl). -/
theorem czInst_c : GCDga.c (𝒜 := ctoyGr k 0 1) = czC := rfl

/-- K12b: degree-0 scalars act on `Toy` by multiplication. -/
private theorem czSmul (r : ctoyGr k 0 1 0) (a : Toy k 0 1) :
    r • a = (r : Toy k 0 1) * a := rfl

/-- K12b: degree-0 elements have `snd = 0`. -/
private theorem czSnd (r : ctoyGr k 0 1 0) : (r : Toy k 0 1).snd = 0 := by
  simpa [ctoyGr] using r.2

/-- K12b: degree-0 elements of `Toy` are `inl` of their first component. -/
private theorem czInl_fst {a : Toy k 0 1} (ha : a ∈ ctoyGr k 0 1 0) :
    TrivSqZeroExt.inl a.fst = a := by
  have h : a.snd = 0 := by simpa [ctoyGr] using ha
  ext <;> simp [h]

/-- K12b: a homogeneous element of nonzero degree has `fst = 0`. -/
private theorem cz_fst_zero {q : ℤ} {a : Toy k 0 1} (ha : a ∈ ctoyGr k 0 1 q) (hq : q ≠ 0) :
    a.fst = 0 := by
  by_cases h1 : q = 1
  · subst h1; simp_all [ctoyGr]
  by_cases h2 : q = 2
  · subst h2; simp_all [ctoyGr]
  · have := eq_zero_of_mem_ctoyGr ha (by omega : ¬(q = 0 ∨ q = 1 ∨ q = 2))
    simp [this]

/-- K12b: a homogeneous element of degree `≠ 2` has no `c`-coefficient. -/
private theorem cz_coef_zero {q : ℤ} {a : Toy k 0 1} (ha : a ∈ ctoyGr k 0 1 q) (hq : q ≠ 2) :
    a.snd.2 0 = 0 := by
  by_cases h0 : q = 0
  · subst h0
    have h : a.snd = 0 := by simpa [ctoyGr] using ha
    simp [h]
  by_cases h1 : q = 1
  · subst h1; simp_all [ctoyGr]
  · have := eq_zero_of_mem_ctoyGr ha (by omega : ¬(q = 0 ∨ q = 1 ∨ q = 2))
    simp [this]

/-- K12b: `a = a.fst + c · (a.snd.2 0)`. -/
private theorem cz_decomp (a : Toy k 0 1) :
    TrivSqZeroExt.inl a.fst + (czC : Toy k 0 1) * TrivSqZeroExt.inl (a.snd.2 0) = a := by
  ext <;> simp [czC] <;>
    first | (rename_i i; exact i.elim0) | (rename_i i; rw [Fin.fin_one_eq_zero i])

/-- K12b: `(c a).fst = 0`. -/
private theorem cz_c_mul_fst (a : Toy k 0 1) : (czC * a : Toy k 0 1).fst = 0 := by
  simp [czC]

/-- K12b: `(c a).snd.2 0 = a.fst`. -/
private theorem cz_c_mul_coef (a : Toy k 0 1) : (czC * a : Toy k 0 1).snd.2 0 = a.fst := by
  simp [czC]

/-- K12b: `c c a = 0`. -/
private theorem cz_c_mul_c (a : Toy k 0 1) : (czC : Toy k 0 1) * (czC * a) = 0 := by
  ext <;> simp [czC]

/-- K12b: a degree-0 element `r` commutes with taking `fst`. -/
private theorem cz_mul0_fst {r : Toy k 0 1} (hr : r ∈ ctoyGr k 0 1 0) (a : Toy k 0 1) :
    TrivSqZeroExt.inl (r * a).fst = r * TrivSqZeroExt.inl a.fst := by
  have h : r.snd = 0 := by simpa [ctoyGr] using hr
  ext <;> simp [h]

/-- K12b: a degree-0 element `r` commutes with taking the `c`-coefficient. -/
private theorem cz_mul0_coef {r : Toy k 0 1} (hr : r ∈ ctoyGr k 0 1 0) (a : Toy k 0 1) :
    TrivSqZeroExt.inl ((r * a).snd.2 0) = r * TrivSqZeroExt.inl (a.snd.2 0) := by
  have h : r.snd = 0 := by simpa [ctoyGr] using hr
  ext <;> simp [h, mul_comm]

/-- K12b: `Tot`-typed elementary tensor `a ⊗ e`. -/
private def czT {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (ctoyGr k 0 1 0) (Q p)]
    (a : Toy k 0 1) (e : ⨁ p, Q p) : Tot (ctoyGr k 0 1) Q := a ⊗ₜ[ctoyGr k 0 1 0] e

/-- K12b: induction on `Tot` (an elementary tensor, zero, sums), stated with `Tot`'s instances. -/
private theorem czTot_induction {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (ctoyGr k 0 1 0) (Q p)] {motive : Tot (ctoyGr k 0 1) Q → Prop}
    (y : Tot (ctoyGr k 0 1) Q) (_h0 : motive 0)
    (ht : ∀ (a : Toy k 0 1) (e : ⨁ p, Q p), motive (czT a e))
    (hadd : ∀ x y, motive x → motive y → motive (x + y)) : motive y :=
  TensorProduct.inductionOn y ht hadd

/-- K12b: `czT` is additive in the first slot. -/
private theorem czT_add {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (ctoyGr k 0 1 0) (Q p)] (a b : Toy k 0 1) (e : ⨁ p, Q p) :
    czT (a + b) e = (czT a e : Tot (ctoyGr k 0 1) Q) + czT b e :=
  TensorProduct.add_tmul a b e

/-- K12b: `czT 0 e = 0`. -/
private theorem czT_zero {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (ctoyGr k 0 1 0) (Q p)] (e : ⨁ p, Q p) :
    (czT 0 e : Tot (ctoyGr k 0 1) Q) = 0 :=
  TensorProduct.zero_tmul _ e

/-- K12b: `k` acts on elementary tensors of `Tot` through the left factor. -/
private theorem czT_smul {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (ctoyGr k 0 1 0) (Q p)] (r : k) (a : Toy k 0 1) (e : ⨁ p, Q p) :
    r • (czT a e : Tot (ctoyGr k 0 1) Q) = czT (r • a) e :=
  TensorProduct.smul_tmul' r a e

/-- K12b: `A` acts on elementary tensors of `Tot` through the left factor. -/
private theorem czT_mul {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (ctoyGr k 0 1 0) (Q p)] (b a : Toy k 0 1) (e : ⨁ p, Q p) :
    b • (czT a e : Tot (ctoyGr k 0 1) Q) = czT (b * a) e :=
  TensorProduct.smul_tmul' b a e

section Ops

variable (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (ctoyGr k 0 1 0) (Q p)]

/-- K12b: the degree-0 part `a ↦ (a.fst, 0, 0)`, `A⁰`-linear. -/
def czFst : Toy k 0 1 →ₗ[ctoyGr k 0 1 0] Toy k 0 1 where
  toFun a := TrivSqZeroExt.inl a.fst
  map_add' := by intro a b; simp
  map_smul' := by
    intro r a
    rw [czSmul]
    show _ = (r : Toy k 0 1) * _
    ext <;> simp [czSnd r]

/-- K12b: the coefficient of `c`, `a ↦ (a.snd.2 0, 0, 0)`, `A⁰`-linear. -/
def czCoef : Toy k 0 1 →ₗ[ctoyGr k 0 1 0] Toy k 0 1 where
  toFun a := TrivSqZeroExt.inl (a.snd.2 0)
  map_add' := by intro a b; simp
  map_smul' := by
    intro r a
    rw [czSmul]
    show _ = (r : Toy k 0 1) * _
    ext <;> simp [czSnd r]

/-- K12b: `czFst` is `k`-linear. -/
private theorem czFst_smul (r : k) (a : Toy k 0 1) : czFst (r • a) = r • czFst a := by
  ext <;> simp [czFst]

/-- K12b: `czCoef` is `k`-linear. -/
private theorem czCoef_smul (r : k) (a : Toy k 0 1) : czCoef (r • a) = r • czCoef a := by
  ext <;> simp [czCoef]

variable {Q}

/-- K12b: `rTensor` of an `A⁰`-linear map of `Toy`, as a function on `Tot` (`Tot`-typed). -/
private def czMap (f : Toy k 0 1 →ₗ[ctoyGr k 0 1 0] Toy k 0 1) (y : Tot (ctoyGr k 0 1) Q) :
    Tot (ctoyGr k 0 1) Q :=
  LinearMap.rTensor (⨁ p, Q p) f y

/-- K12b: `czMap f` on elementary tensors. -/
private theorem czMap_tmul (f : Toy k 0 1 →ₗ[ctoyGr k 0 1 0] Toy k 0 1) (a : Toy k 0 1)
    (e : ⨁ p, Q p) : czMap f (czT a e : Tot (ctoyGr k 0 1) Q) = czT (f a) e :=
  LinearMap.rTensor_tmul _ _ _ _

/-- K12b: `czMap f` is additive. -/
private theorem czMap_add (f : Toy k 0 1 →ₗ[ctoyGr k 0 1 0] Toy k 0 1)
    (x y : Tot (ctoyGr k 0 1) Q) : czMap f (x + y) = czMap f x + czMap f y :=
  map_add (LinearMap.rTensor (⨁ p, Q p) f) x y

/-- K12b: `czMap f` is `k`-linear if `f` is. -/
private theorem czMap_smul (f : Toy k 0 1 →ₗ[ctoyGr k 0 1 0] Toy k 0 1)
    (hf : ∀ (r : k) (a : Toy k 0 1), f (r • a) = r • f a) (r : k) (y : Tot (ctoyGr k 0 1) Q) :
    czMap f (r • y) = r • czMap f y := by
  refine czTot_induction (motive := fun y => czMap f (r • y) = r • czMap f y) y ?_
    (fun a e => ?_) (fun x y hx hy => ?_)
  · rw [smul_zero]
    exact (map_zero (LinearMap.rTensor (⨁ p, Q p) f)).trans (smul_zero r).symm
  · rw [czT_smul, czMap_tmul, czMap_tmul, hf, czT_smul]
  · rw [smul_add, czMap_add, czMap_add, smul_add, hx, hy]

variable (Q)

variable (k) in
/-- K12b: `P` on the total module, `a ⊗ e ↦ a.fst ⊗ e` (`rTensor` of `czFst`, `k`-linear). -/
def czP : Tot (ctoyGr k 0 1) Q →ₗ[k] Tot (ctoyGr k 0 1) Q where
  toFun := LinearMap.rTensor (⨁ p, Q p) (czFst (k := k))
  map_add' := map_add _
  map_smul' := fun r y => czMap_smul czFst czFst_smul r y

variable (k) in
/-- K12b: `L` on the total module, `a ⊗ e ↦ (a.snd.2 0) ⊗ e` (`rTensor` of `czCoef`,
`k`-linear). -/
def czL : Tot (ctoyGr k 0 1) Q →ₗ[k] Tot (ctoyGr k 0 1) Q where
  toFun := LinearMap.rTensor (⨁ p, Q p) (czCoef (k := k))
  map_add' := map_add _
  map_smul' := fun r y => czMap_smul czCoef czCoef_smul r y

variable {Q}

/-- K12b: `P` on elementary tensors. -/
private theorem czP_czT (a : Toy k 0 1) (e : ⨁ p, Q p) :
    czP k Q (czT a e) = czT (TrivSqZeroExt.inl a.fst) e :=
  czMap_tmul czFst a e

/-- K12b: `L` on elementary tensors. -/
private theorem czL_czT (a : Toy k 0 1) (e : ⨁ p, Q p) :
    czL k Q (czT a e) = czT (TrivSqZeroExt.inl (a.snd.2 0)) e :=
  czMap_tmul czCoef a e

/-- K12b: `y = Py + c·Ly`. -/
theorem czP_add_czL (y : Tot (ctoyGr k 0 1) Q) : czP k Q y + (czC : Toy k 0 1) •czL k Q y = y := by
  refine czTot_induction (motive := fun y => czP k Q y + (czC : Toy k 0 1) • czL k Q y = y) y
    ?_ (fun a e => ?_) (fun x y hx hy => ?_)
  · simp only [map_zero, smul_zero, add_zero]
  · rw [czP_czT, czL_czT, czT_mul, ← czT_add, cz_decomp]
  · simp only [map_add, smul_add]
    calc _ = (czP k Q x + (czC : Toy k 0 1) • czL k Q x) +
          (czP k Q y + (czC : Toy k 0 1) • czL k Q y) := by abel
      _ = x + y := by rw [hx, hy]

/-- K12b: `P(c·y) = 0`. -/
theorem czP_smul_c (y : Tot (ctoyGr k 0 1) Q) : czP k Q ((czC : Toy k 0 1) •y) = 0 := by
  refine czTot_induction (motive := fun y => czP k Q ((czC : Toy k 0 1) • y) = 0) y
    ?_ (fun a e => ?_) (fun x y hx hy => ?_)
  · simp only [smul_zero, map_zero]
  · rw [czT_mul, czP_czT, cz_c_mul_fst, TrivSqZeroExt.inl_zero, czT_zero]
  · simp only [smul_add, map_add, hx, hy, add_zero]

/-- K12b: `L(c·y) = Py`. -/
theorem czL_smul_c (y : Tot (ctoyGr k 0 1) Q) : czL k Q ((czC : Toy k 0 1) •y) = czP k Q y := by
  refine czTot_induction (motive := fun y => czL k Q ((czC : Toy k 0 1) • y) = czP k Q y) y
    ?_ (fun a e => ?_) (fun x y hx hy => ?_)
  · simp only [smul_zero, map_zero]
  · rw [czT_mul, czL_czT, cz_c_mul_coef, czP_czT]
  · simp only [smul_add, map_add, hx, hy]

/-- K12b: `P∘P = P`. -/
theorem czP_czP (y : Tot (ctoyGr k 0 1) Q) : czP k Q (czP k Q y) = czP k Q y := by
  refine czTot_induction (motive := fun y => czP k Q (czP k Q y) = czP k Q y) y
    ?_ (fun a e => ?_) (fun x y hx hy => ?_)
  · simp only [map_zero]
  · rw [czP_czT, czP_czT, TrivSqZeroExt.fst_inl]
  · simp only [map_add, hx, hy]

/-- K12b: `L∘P = 0`. -/
theorem czL_czP (y : Tot (ctoyGr k 0 1) Q) : czL k Q (czP k Q y) = 0 := by
  refine czTot_induction (motive := fun y => czL k Q (czP k Q y) = 0) y
    ?_ (fun a e => ?_) (fun x y hx hy => ?_)
  · simp only [map_zero]
  · rw [czP_czT, czL_czT]
    simp [czT_zero]
  · simp only [map_add, hx, hy, add_zero]

/-- K12b: `P∘L = L`. -/
theorem czP_czL (y : Tot (ctoyGr k 0 1) Q) : czP k Q (czL k Q y) = czL k Q y := by
  refine czTot_induction (motive := fun y => czP k Q (czL k Q y) = czL k Q y) y
    ?_ (fun a e => ?_) (fun x y hx hy => ?_)
  · simp only [map_zero]
  · rw [czL_czT, czP_czT, TrivSqZeroExt.fst_inl]
  · simp only [map_add, hx, hy]

/-- K12b: `c·c·y = 0`. -/
theorem czC_smul_czC_smul (y : Tot (ctoyGr k 0 1) Q) :
    (czC : Toy k 0 1) • (czC : Toy k 0 1) • y = 0 := by
  refine czTot_induction
    (motive := fun y => (czC : Toy k 0 1) • (czC : Toy k 0 1) • y = 0) y
    ?_ (fun a e => ?_) (fun x y hx hy => ?_)
  · simp only [smul_zero]
  · rw [czT_mul, czT_mul, cz_c_mul_c, czT_zero]
  · simp only [smul_add, hx, hy, add_zero]

/-- K12b: `P` commutes with degree-0 scalars. -/
theorem czP_smul0 {a : Toy k 0 1} (ha : a ∈ ctoyGr k 0 1 0) (y : Tot (ctoyGr k 0 1) Q) :
    czP k Q (a • y) = a • czP k Q y := by
  refine czTot_induction (motive := fun y => czP k Q (a • y) = a • czP k Q y) y
    ?_ (fun b e => ?_) (fun x y hx hy => ?_)
  · simp only [smul_zero, map_zero]
  · rw [czT_mul, czP_czT, czP_czT, czT_mul, cz_mul0_fst ha]
  · simp only [smul_add, map_add, hx, hy]

/-- K12b: `L` commutes with degree-0 scalars. -/
theorem czL_smul0 {a : Toy k 0 1} (ha : a ∈ ctoyGr k 0 1 0) (y : Tot (ctoyGr k 0 1) Q) :
    czL k Q (a • y) = a • czL k Q y := by
  refine czTot_induction (motive := fun y => czL k Q (a • y) = a • czL k Q y) y
    ?_ (fun b e => ?_) (fun x y hx hy => ?_)
  · simp only [smul_zero, map_zero]
  · rw [czT_mul, czL_czT, czL_czT, czT_mul, cz_mul0_coef ha]
  · simp only [smul_add, map_add, hx, hy]

/-- K12b: `P` preserves total degrees. -/
theorem czP_mem {m : ℤ} {y : Tot (ctoyGr k 0 1) Q} (hy : y ∈ totDeg (ctoyGr k 0 1) Q m) :
    czP k Q y ∈ totDeg (ctoyGr k 0 1) Q m := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, hqp, ha, rfl⟩ := hx
    show czP k Q (czT a (lof (ctoyGr k 0 1 0) ℤ Q p e)) ∈ _
    rw [czP_czT]
    by_cases hq : q = 0
    · subst hq
      rw [czInl_fst ha]
      exact Submodule.subset_span ⟨0, p, a, e, hqp, ha, rfl⟩
    · rw [cz_fst_zero ha hq, TrivSqZeroExt.inl_zero, czT_zero]
      exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- K12b: `L` lowers total degrees by 2. -/
theorem czL_mem {m : ℤ} {y : Tot (ctoyGr k 0 1) Q} (hy : y ∈ totDeg (ctoyGr k 0 1) Q m) :
    czL k Q y ∈ totDeg (ctoyGr k 0 1) Q (m - 2) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, hqp, ha, rfl⟩ := hx
    show czL k Q (czT a (lof (ctoyGr k 0 1 0) ℤ Q p e)) ∈ _
    rw [czL_czT]
    by_cases hq : q = 2
    · subst hq
      exact Submodule.subset_span ⟨0, p, TrivSqZeroExt.inl (a.snd.2 0), e, by omega,
        by simp [ctoyGr], rfl⟩
    · rw [cz_coef_zero ha hq, TrivSqZeroExt.inl_zero, czT_zero]
      exact zero_mem _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

end Ops

variable (M : CohesiveModule (ctoyGr k 0 1))

/-- K12b: the contracting homotopy `φ = L𝕏P + (1 − P)𝕏L` (Block: `𝕏₂`, extended `A`-linearly). -/
def czPhi : M.T →ₗ[k] M.T :=
  czL k M.Q ∘ₗ M.X ∘ₗ czP k M.Q + (LinearMap.id - czP k M.Q) ∘ₗ M.X ∘ₗ czL k M.Q

/-- K12b: the differential of `A` vanishes (`d = 0`). -/
private theorem cz_d_zero (a : Toy k 0 1) : GCDga.d (𝒜 := ctoyGr k 0 1) a = 0 := by
  show TrivSqZeroExt.inr (0, ((0 : (Fin 0 → k) →ₗ[k] (Fin 1 → k)) a.snd.1)) = 0
  ext <;> simp
  rename_i i
  exact i.elim0

/-- K12b: `𝕏(c·y) = c·𝕏y` (Leibniz with `dc = 0`, `|c| = 2`). -/
private theorem czX_c (y : M.T) : M.X ((czC : Toy k 0 1) • y) = (czC : Toy k 0 1) • M.X y := by
  rw [M.leibniz czC_mem y, cz_d_zero, zero_smul, zero_add]
  have : (2 : ℤ).negOnePow = 1 := by decide
  rw [this, one_smul]

/-- K12b: `𝕏(a·y) = a·𝕏y` for `a` of degree 0. -/
private theorem czX_smul0 {a : Toy k 0 1} (ha : a ∈ ctoyGr k 0 1 0) (y : M.T) :
    M.X (a • y) = a • M.X y := by
  rw [M.leibniz ha y, cz_d_zero, zero_smul, zero_add]
  have : (0 : ℤ).negOnePow = 1 := by decide
  rw [this, one_smul]

/-- K12b: formula for `φ`. -/
private theorem czPhi_apply (y : M.T) : czPhi M y = czL k M.Q (M.X (czP k M.Q y)) +
    (M.X (czL k M.Q y) - czP k M.Q (M.X (czL k M.Q y))) := rfl

/-- K12b: `z - Pz = c·Lz`. -/
private theorem cz_sub_P {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (ctoyGr k 0 1 0) (Q p)] (z : Tot (ctoyGr k 0 1) Q) :
    z - czP k Q z = (czC : Toy k 0 1) • czL k Q z := by
  rw [sub_eq_iff_eq_add']
  exact (czP_add_czL z).symm

/-- K12b: `φ(c·y) = c·φ(y)`. -/
private theorem czPhi_c (y : M.T) :
    czPhi M ((czC : Toy k 0 1) • y) = (czC : Toy k 0 1) • czPhi M y := by
  rw [czPhi_apply, czPhi_apply, czP_smul_c, czL_smul_c]
  simp only [map_zero, zero_add]
  rw [smul_add, cz_sub_P (M.X (czL k M.Q y)), czC_smul_czC_smul, add_zero,
    cz_sub_P (M.X (czP k M.Q y))]

/-- K12b: `φ(a·y) = a·φ(y)` for `a` of degree 0. -/
private theorem czPhi_smul0 {a : Toy k 0 1} (ha : a ∈ ctoyGr k 0 1 0) (y : M.T) :
    czPhi M (a • y) = a • czPhi M y := by
  simp only [czPhi_apply, czP_smul0 ha, czL_smul0 ha, czX_smul0 M ha, smul_add, smul_sub]

/-- K12b: an element of degree 2 is a multiple of `c`. -/
private theorem cz_deg_two {a : Toy k 0 1} (ha : a ∈ ctoyGr k 0 1 2) :
    a = a.snd.2 0 • (czC : Toy k 0 1) := by
  have h : a.fst = 0 ∧ a.snd.1 = 0 := by simpa [ctoyGr] using ha
  ext <;> simp [czC, h.1] <;>
    first | (rename_i i; exact i.elim0) | (rename_i i; rw [Fin.fin_one_eq_zero i])

/-- K12b: `φ` preserves the degree shift `-1`. -/
private theorem czPhi_deg {m : ℤ} {x : M.T} (hx : x ∈ totDeg (ctoyGr k 0 1) M.Q m) :
    czPhi M x ∈ totDeg (ctoyGr k 0 1) M.Q (m + -1) := by
  have h1 : czL k M.Q (M.X (czP k M.Q x)) ∈ totDeg (ctoyGr k 0 1) M.Q (m + 1 - 2) :=
    czL_mem (M.X_mem (czP_mem hx))
  have h2 : M.X (czL k M.Q x) ∈ totDeg (ctoyGr k 0 1) M.Q (m - 2 + 1) := M.X_mem (czL_mem hx)
  have h3 := czP_mem h2
  rw [czPhi_apply, show m + -1 = m + 1 - 2 by omega]
  refine add_mem h1 (sub_mem ?_ ?_)
  · rw [show m + 1 - 2 = m - 2 + 1 by omega]; exact h2
  · rw [show m + 1 - 2 = m - 2 + 1 by omega]; exact h3

/-- K12b: `φ ∈ Hom⁻¹(M, M)`. -/
theorem czPhi_mem : czPhi M ∈ Hom M.toQuasiCohesive M.toQuasiCohesive (-1) := by
  refine ⟨fun hx => czPhi_deg M hx, fun {p a} ha x => ?_⟩
  by_cases hp : p = 0 ∨ p = 2
  swap
  · have : a = 0 := by
      by_cases h1 : p = 1
      · subst h1
        have h : a.fst = 0 ∧ a.snd.2 = 0 := by simpa [ctoyGr] using ha
        ext <;> simp [h.1, h.2]
        rename_i i
        exact i.elim0
      · exact eq_zero_of_mem_ctoyGr ha (by omega)
    subst this
    simp
  rcases hp with rfl | rfl
  · simp only [mul_zero, Int.negOnePow_zero, one_smul]
    exact czPhi_smul0 M ha x
  · have e : (-1 * (2 : ℤ)).negOnePow = 1 := by decide
    have h := cz_deg_two ha
    generalize a.snd.2 0 = r at h
    subst h
    rw [e, one_smul, smul_assoc, map_smul, czPhi_c, smul_assoc]

/-- K12b: `N = 𝕏φ + φ𝕏 − id` commutes with `c·`. -/
private theorem czN_c (N : M.T →ₗ[k] M.T)
    (hN : ∀ y, N y = M.X (czPhi M y) + czPhi M (M.X y) - y) (z : M.T) :
    N ((czC : Toy k 0 1) • z) = (czC : Toy k 0 1) • N z := by
  simp only [hN, czPhi_c, czX_c, smul_add, smul_sub]

/-- K12b: `P(N w) = 0` for `w` with `Pw = w`, `Lw = 0` (flatness, applying `L` to `𝕏²w = c·w`). -/
private theorem czN_P_aux (N : M.T →ₗ[k] M.T)
    (hN : ∀ y, N y = M.X (czPhi M y) + czPhi M (M.X y) - y) (w : M.T)
    (hPw : czP k M.Q w = w) (hLw : czL k M.Q w = 0) : czP k M.Q (N w) = 0 := by
  have hφw : czPhi M w = czL k M.Q (M.X w) := by
    rw [czPhi_apply, hPw, hLw]
    simp only [map_zero, sub_zero, add_zero]
  have h1 : M.X (M.X w) = (czC : Toy k 0 1) • w := M.flat w
  have h2 : M.X w = czP k M.Q (M.X w) + (czC : Toy k 0 1) • czL k M.Q (M.X w) :=
    (czP_add_czL _).symm
  have h3 : M.X (M.X w) = M.X (czP k M.Q (M.X w)) +
      (czC : Toy k 0 1) • M.X (czL k M.Q (M.X w)) := by
    conv_lhs => rw [h2]
    rw [map_add, czX_c]
  have h4 : czL k M.Q (M.X (M.X w)) = w := by rw [h1, czL_smul_c, hPw]
  rw [h3, map_add, czL_smul_c] at h4
  rw [hN, hφw, map_sub, map_add, czPhi_apply M (M.X w)]
  simp only [map_add, map_sub, czP_czL, czP_czP, sub_self, add_zero, hPw]
  rw [sub_eq_zero, add_comm]
  exact h4

/-- K12b: `P(N y) = 0` for all `y`. -/
private theorem czN_P (N : M.T →ₗ[k] M.T)
    (hN : ∀ y, N y = M.X (czPhi M y) + czPhi M (M.X y) - y) (y : M.T) :
    czP k M.Q (N y) = 0 := by
  have h : N y = N (czP k M.Q y) + (czC : Toy k 0 1) • N (czL k M.Q y) := by
    conv_lhs => rw [← czP_add_czL y]
    rw [map_add, czN_c M N hN]
  rw [h, map_add, czN_P_aux M N hN _ (czP_czP y) (czL_czP y), czP_smul_c, add_zero]

/-- K12b: `N = δφ − id` squares to zero. -/
theorem czPhi_sq :
    (δ M.toQuasiCohesive M.toQuasiCohesive (-1) (czPhi M) - LinearMap.id) ∘ₗ
      (δ M.toQuasiCohesive M.toQuasiCohesive (-1) (czPhi M) - LinearMap.id) = 0 := by
  set N : M.T →ₗ[k] M.T :=
    δ M.toQuasiCohesive M.toQuasiCohesive (-1) (czPhi M) - LinearMap.id with hNdef
  have hN : ∀ y, N y = M.X (czPhi M y) + czPhi M (M.X y) - y := by
    intro y
    have e : ((-1 : ℤ)).negOnePow = -1 := by decide
    simp only [hNdef, LinearMap.sub_apply, δ_apply, LinearMap.comp_apply,
      LinearMap.id_apply, e, Units.neg_smul, one_smul, sub_neg_eq_add, LinearMap.add_apply]
  have hcl : ∀ z, N z = (czC : Toy k 0 1) • czL k M.Q (N z) := by
    intro z
    have h := czP_add_czL (N z)
    rw [czN_P M N hN z, zero_add] at h
    exact h.symm
  refine LinearMap.ext fun y => ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [hcl y, czN_c M N hN, hcl (czL k M.Q (N y))]
  exact czC_smul_czC_smul _

/-- **K12b.** Every object of `Ho(P_A)` for `A = k[c]/(c²)`, `|c| = 2`, `d = 0`, curvature `c`
is a zero object. -/
theorem isZero_czHoP (M : HoP (ctoyGr k 0 1)) : IsZero M :=
  isZero_of_contraction M.as (czPhi_mem M.as) (czPhi_sq M.as)

/-- K12b: `c ≠ 0` over a nontrivial ring, so the vanishing is not that of the flat case. -/
theorem czC_ne_zero [Nontrivial k] : (czC : Toy k 0 1) ≠ 0 := by
  intro h
  have := congrArg (fun y : Toy k 0 1 => y.snd.2 0) h
  simp [czC] at this

end Cohesive.Checks
