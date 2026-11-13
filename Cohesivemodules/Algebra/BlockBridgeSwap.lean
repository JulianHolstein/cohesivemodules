import Cohesivemodules.Algebra.BlockDef
import Cohesivemodules.Algebra.Cohesive

set_option linter.style.header false

/-!
# A13: bridge between Block's right modules and the left-module definition

Blueprint item A13 (sanity). For graded-commutative `A`, Block's cohesive modules
[B, Def 2.3.1–2.3.2] over `(A, d, cB)` (right modules, `Algebra/BlockDef.lean`) are the same as the
left-module cohesive modules of `Algebra/CohesiveDef.lean` over `(A, d, c)` with `c = -cB`
(conventions §3), and the Hom complexes agree with their differentials and composition: a
dg-isomorphism of dg-categories, so `Ho(P_A)` is Block's homotopy category.

## The translation
`blockSwap : E• ⊗_{A⁰} A ≃ A ⊗_{A⁰} E•`, `e ⊗ a ↦ (-1)^{|e||a|} a ⊗ e` (built from the sign
twist `GCDga.twist`). With it:
* `blockSwap (x·a) = (-1)^{|a||x|} a • blockSwap x` (`blockSwap_rAct`);
* operators are conjugated, `𝕏 = σ ∘ 𝔼 ∘ σ⁻¹`; Block's Leibniz rule becomes
  `𝕏(a·x) = da·x + (-1)^{|a|} a·𝕏x`, and `𝔼 ∘ 𝔼 = -(·cB)` becomes `𝕏 ∘ 𝕏 = (-cB)·(-)`;
* right `A`-linearity of a degree-`n` map becomes `φ(a·x) = (-1)^{n|a|} a·φ(x)` (A4), and
  the differentials are literally the same formula.

## Main results
* `BlockQuasiCohesive.toLeft`, `QuasiCohesive.toBlock`, mutually inverse
  (`toBlock_toLeft`, `toLeft_toBlock`); `BlockCohesive.toLeft`, `CohesiveModule.toBlock`.
* `blockConj` (conjugation by `blockSwap`), `mem_hom_blockConj_iff`, `blockConj_δ`,
  `blockConj_comp`, `blockConj_id`, and `blockHomEquiv : BlockHom E₁ E₂ n ≃ₗ[k] Hom _ _ n`.

Part 1 of 2 of the original `Algebra/BlockBridge.lean`, split for size; continued in
`Algebra/BlockBridge.lean`.
-/

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- A13: on the left total module the `k`-action factors through `A⁰`. -/
instance Tot.isScalarTower0 (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] : IsScalarTower k (𝒜 0) (Tot 𝒜 Q) :=
  ⟨fun r f x => by
    rw [Tot.smul0_eq, Tot.smul0_eq]
    exact smul_assoc r (f : A) x⟩


section Induction

variable {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- A13: `⊗` on `TotR` is additive on the right. -/
theorem totR_tmul_add (e : ⨁ p, Q p) (a b : A) :
    TotR.tmul 𝒜 Q e (a + b) = TotR.tmul 𝒜 Q e a + TotR.tmul 𝒜 Q e b :=
  TensorProduct.tmul_add e a b

/-- A13: `⊗` on `TotR` is additive on the left. -/
private theorem totR_add_tmul (e e' : ⨁ p, Q p) (a : A) :
    TotR.tmul 𝒜 Q (e + e') a = TotR.tmul 𝒜 Q e a + TotR.tmul 𝒜 Q e' a :=
  TensorProduct.add_tmul e e' a

/-- A13: `0 ⊗ a = 0` in `TotR`. -/
private theorem totR_zero_tmul (a : A) : TotR.tmul 𝒜 Q (0 : ⨁ p, Q p) a = 0 :=
  TensorProduct.zero_tmul _ a

/-- A13: `e ⊗ 0 = 0` in `TotR`. -/
theorem totR_tmul_zero (e : ⨁ p, Q p) : TotR.tmul 𝒜 Q e (0 : A) = 0 :=
  TensorProduct.tmul_zero _ e

/-- A13: induction on `TotR` through pure tensors. -/
private theorem totR_induction_basic {C : TotR 𝒜 Q → Prop} (x : TotR 𝒜 Q)
    (ht : ∀ (e : ⨁ p, Q p) (a : A), C (TotR.tmul 𝒜 Q e a))
    (hadd : ∀ x y, C x → C y → C (x + y)) : C x :=
  TensorProduct.inductionOn x ht hadd

/-- A13: `(z·b)·a = z·(ba)`. -/
private theorem totR_rAct_rAct (a b : A) (z : TotR 𝒜 Q) :
    TotR.rAct 𝒜 Q a (TotR.rAct 𝒜 Q b z) = TotR.rAct 𝒜 Q (b * a) z := by
  refine totR_induction_basic (C := fun z => TotR.rAct 𝒜 Q a (TotR.rAct 𝒜 Q b z) =
    TotR.rAct 𝒜 Q (b * a) z) z (fun e c => ?_) (fun x y hx hy => ?_)
  · simp only [TotR.rAct_tmul, mul_assoc]
  · simp only [map_add, hx, hy]

/-- A13: `z·0 = 0`. -/
theorem totR_rAct_zero (z : TotR 𝒜 Q) : TotR.rAct 𝒜 Q 0 z = 0 := by
  refine totR_induction_basic (C := fun z => TotR.rAct 𝒜 Q 0 z = 0) z (fun e c => ?_)
    (fun x y hx hy => ?_)
  · simp only [TotR.rAct_tmul, mul_zero, totR_tmul_zero]
  · simp only [map_add, hx, hy, add_zero]

/-- A13: `z·(a + b) = z·a + z·b`. -/
theorem totR_rAct_add (a b : A) (z : TotR 𝒜 Q) :
    TotR.rAct 𝒜 Q (a + b) z = TotR.rAct 𝒜 Q a z + TotR.rAct 𝒜 Q b z := by
  refine totR_induction_basic (C := fun z => TotR.rAct 𝒜 Q (a + b) z =
    TotR.rAct 𝒜 Q a z + TotR.rAct 𝒜 Q b z) z (fun e c => ?_) (fun x y hx hy => ?_)
  · simp only [TotR.rAct_tmul, mul_add, totR_tmul_add]
  · simp only [map_add, hx, hy]
    abel

/-- A13: induction on `TotR` through homogeneous pure tensors `lof p e ⊗ a`, `a ∈ A^q`. -/
theorem totR_induction {C : TotR 𝒜 Q → Prop} (x : TotR 𝒜 Q) (h0 : C 0)
    (hadd : ∀ x y, C x → C y → C (x + y))
    (ht : ∀ (p q : ℤ) (e : Q p) (a : A), a ∈ 𝒜 q →
      C (TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) a)) : C x := by
  refine TensorProduct.inductionOn x (fun e a => ?_) hadd
  show C (TotR.tmul 𝒜 Q e a)
  induction e using DirectSum.induction_on with
  | zero => rw [totR_zero_tmul]; exact h0
  | of p e =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [totR_tmul_zero]; exact h0
    | homogeneous a => exact ht p _ e a a.2
    | add a b ha hb => rw [totR_tmul_add]; exact hadd _ _ ha hb
  | add e e' he he' => rw [totR_add_tmul]; exact hadd _ _ he he'

/-- A13: induction on `Tot` through homogeneous pure tensors `a ⊗ lof p e`, `a ∈ A^q`. -/
private theorem tot_induction {C : Tot 𝒜 Q → Prop} (x : Tot 𝒜 Q) (h0 : C 0)
    (hadd : ∀ x y, C x → C y → C (x + y))
    (ht : ∀ (p q : ℤ) (e : Q p) (a : A), a ∈ 𝒜 q →
      C (Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e))) : C x := by
  refine Tot.induction_on x (fun a e => ?_) hadd
  induction e using DirectSum.induction_on with
  | zero => rw [Tot.tmul_zero]; exact h0
  | of p e =>
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [Tot.zero_tmul]; exact h0
    | homogeneous a => exact ht p _ e a a.2
    | add a b ha hb => rw [Tot.add_tmul]; exact hadd _ _ ha hb
  | add e e' he he' => rw [Tot.tmul_add]; exact hadd _ _ he he'

end Induction

/-! ## The swap `E• ⊗ A ≃ A ⊗ E•` -/

section Swap

variable (𝒜) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- A13: `(e, a) ↦ (-1)^{pq} a ⊗ e` for `e ∈ Q^p` (on `a ∈ A^q`), as an `A⁰`-bilinear map. -/
def swapGen (p : ℤ) : Q p →ₗ[𝒜 0] A →ₗ[𝒜 0] Tot 𝒜 Q :=
  ((TensorProduct.mk (𝒜 0) A (⨁ p, Q p)).flip ∘ₗ lof (𝒜 0) ℤ Q p).compl₂ (GCDga.twist 𝒜 p)

/-- A13: `e ⊗ a ↦ (-1)^{|e||a|} a ⊗ e`, `A⁰`-linear. -/
def swapL : TotR 𝒜 Q →ₗ[𝒜 0] Tot 𝒜 Q :=
  TensorProduct.lift (DirectSum.toModule (𝒜 0) ℤ _ (swapGen 𝒜 Q))

/-- A13: `(e, a) ↦ (-1)^{pq} e ⊗ a` for `e ∈ Q^p` (on `a ∈ A^q`), as an `A⁰`-bilinear map. -/
def unswapGen (p : ℤ) : Q p →ₗ[𝒜 0] A →ₗ[𝒜 0] TotR 𝒜 Q :=
  ((TensorProduct.mk (𝒜 0) (⨁ p, Q p) A) ∘ₗ lof (𝒜 0) ℤ Q p).compl₂ (GCDga.twist 𝒜 p)

/-- A13: `a ⊗ e ↦ (-1)^{|e||a|} e ⊗ a`, `A⁰`-linear; inverse of `swapL`. -/
def unswapL : Tot 𝒜 Q →ₗ[𝒜 0] TotR 𝒜 Q :=
  TensorProduct.lift (DirectSum.toModule (𝒜 0) ℤ _ (unswapGen 𝒜 Q)).flip

variable {𝒜 Q}

/-- A13: `swapL (e ⊗ a) = τ_p(a) ⊗ e` for `e ∈ Q^p`. -/
theorem swapL_tmul {p : ℤ} (e : Q p) (a : A) :
    swapL 𝒜 Q (TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) a) =
      Tot.tmul 𝒜 Q (GCDga.twist 𝒜 p a) (lof (𝒜 0) ℤ Q p e) := by
  have h := DirectSum.toModule_lof (𝒜 0) (ι := ℤ) (φ := swapGen 𝒜 Q) p e
  exact congrArg (fun f => f a) h

/-- A13: `unswapL (a ⊗ e) = e ⊗ τ_p(a)` for `e ∈ Q^p`. -/
theorem unswapL_tmul {p : ℤ} (e : Q p) (a : A) :
    unswapL 𝒜 Q (Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e)) =
      TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) (GCDga.twist 𝒜 p a) := by
  have h := DirectSum.toModule_lof (𝒜 0) (ι := ℤ) (φ := unswapGen 𝒜 Q) p e
  exact congrArg (fun f => f a) h

theorem swapL_comp_unswapL : swapL 𝒜 Q ∘ₗ unswapL 𝒜 Q = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  show swapL 𝒜 Q (unswapL 𝒜 Q x) = x
  refine tot_induction (C := fun x => swapL 𝒜 Q (unswapL 𝒜 Q x) = x) x ?_ ?_ ?_
  · simp only [map_zero]
  · intro x y hx hy
    simp only [map_add]
    rw [hx, hy]
  · intro p q e a _
    rw [unswapL_tmul, swapL_tmul, twist_involutive]

theorem unswapL_comp_swapL : unswapL 𝒜 Q ∘ₗ swapL 𝒜 Q = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  show unswapL 𝒜 Q (swapL 𝒜 Q x) = x
  refine totR_induction (C := fun x => unswapL 𝒜 Q (swapL 𝒜 Q x) = x) x ?_ ?_ ?_
  · simp only [map_zero]
  · intro x y hx hy
    simp only [map_add]
    rw [hx, hy]
  · intro p q e a _
    rw [swapL_tmul, unswapL_tmul, twist_involutive]

variable (𝒜 Q) in
/-- **A13.** The translation `σ : E• ⊗_{A⁰} A ≃ A ⊗_{A⁰} E•`, `e ⊗ a ↦ (-1)^{|e||a|} a ⊗ e`,
between Block's total module and the left total module (conventions §3). `k`-linear. -/
def blockSwap : TotR 𝒜 Q ≃ₗ[k] Tot 𝒜 Q :=
  (LinearEquiv.ofLinearMap (swapL 𝒜 Q) (unswapL 𝒜 Q) swapL_comp_unswapL
    unswapL_comp_swapL).restrictScalars k

/-- A13: `blockSwap` is `swapL`. -/
private theorem blockSwap_apply (x : TotR 𝒜 Q) : blockSwap 𝒜 Q x = swapL 𝒜 Q x := rfl

/-- A13: the inverse of `blockSwap` is `unswapL`. -/
private theorem blockSwap_symm_apply (y : Tot 𝒜 Q) : (blockSwap 𝒜 Q).symm y = unswapL 𝒜 Q y :=
  rfl

/-- A13: signs move out of the right factor of a `TotR` pure tensor. -/
private theorem totR_tmul_units_smul (e : ⨁ p, Q p) (u : ℤˣ) (a : A) :
    TotR.tmul 𝒜 Q e (u • a) = u • TotR.tmul 𝒜 Q e a := by
  simp only [Units.smul_def]
  exact TensorProduct.tmul_smul _ _ _

/-- A13: `σ(e ⊗ a) = (-1)^{pq} a ⊗ e` for `e ∈ Q^p`, `a ∈ A^q`. -/
theorem blockSwap_tmul {p q : ℤ} (e : Q p) {a : A} (ha : a ∈ 𝒜 q) :
    blockSwap 𝒜 Q (TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) a) =
      (p * q).negOnePow • Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e) := by
  rw [blockSwap_apply, swapL_tmul, GCDga.twist_of_mem 𝒜 p ha, Tot.tmul_units_smul]

/-- A13: `σ` preserves the total degree. -/
theorem blockSwap_mem_totDeg_iff {m : ℤ} {x : TotR 𝒜 Q} :
    blockSwap 𝒜 Q x ∈ totDeg 𝒜 Q m ↔ x ∈ totDegR 𝒜 Q m := by
  constructor
  · intro hx
    have h : (totDeg 𝒜 Q m).map (blockSwap 𝒜 Q).symm.toLinearMap ≤ totDegR 𝒜 Q m := by
      rw [totDeg, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, ⟨q, p, a, e, hpq, ha, rfl⟩, rfl⟩
      change (blockSwap 𝒜 Q).symm (Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e)) ∈ _
      rw [blockSwap_symm_apply, unswapL_tmul, GCDga.twist_of_mem 𝒜 p ha, totR_tmul_units_smul,
        Units.smul_def]
      refine zsmul_mem ?_ _
      exact Submodule.subset_span ⟨p, q, e, a, by omega, ha, rfl⟩
    simpa using h ⟨_, hx, rfl⟩
  · intro hx
    have h : (totDegR 𝒜 Q m).map (blockSwap 𝒜 Q).toLinearMap ≤ totDeg 𝒜 Q m := by
      rw [totDegR, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨y, ⟨p, q, e, a, hpq, ha, rfl⟩, rfl⟩
      change blockSwap 𝒜 Q (TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) a) ∈ _
      rw [blockSwap_tmul e ha, Units.smul_def]
      refine zsmul_mem ?_ _
      exact Submodule.subset_span ⟨q, p, a, e, by omega, ha, rfl⟩
    exact h ⟨_, hx, rfl⟩

/-- A13: `blockSwap_rAct` on a homogeneous pure tensor. -/
private theorem blockSwap_rAct_tmul {p q r : ℤ} {a b : A} (ha : a ∈ 𝒜 q) (hb : b ∈ 𝒜 r)
    (e : Q p) :
    blockSwap 𝒜 Q (TotR.rAct 𝒜 Q a (TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) b)) =
      (q * (p + r)).negOnePow • a • blockSwap 𝒜 Q (TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) b) := by
  rw [TotR.rAct_tmul, blockSwap_tmul e (SetLike.GradedMul.mul_mem hb ha), blockSwap_tmul e hb,
    Units.smul_def, Units.smul_def, Units.smul_def, smul_comm a, Tot.smul_tmul,
    GCDga.gcomm ha hb, Units.smul_def, Tot.tmul_zsmul]
  simp only [smul_smul, ← Units.val_mul, ← Int.negOnePow_add]
  have : q * (p + r) + (p * r + q * r) = p * (r + q) + 2 * (q * r) := by ring
  rw [this, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

/-- A13: the right action becomes the left action with the Koszul sign:
`σ(x·a) = (-1)^{|a||x|} a·σ(x)` for `a ∈ A^q` and `x` of degree `m`. -/
theorem blockSwap_rAct {q m : ℤ} {a : A} (ha : a ∈ 𝒜 q) {x : TotR 𝒜 Q}
    (hx : x ∈ totDegR 𝒜 Q m) :
    blockSwap 𝒜 Q (TotR.rAct 𝒜 Q a x) = (q * m).negOnePow • a • blockSwap 𝒜 Q x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, r, e, b, rfl, hb, rfl⟩ := hx
    exact blockSwap_rAct_tmul ha hb e
  | zero => simp only [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy, smul_add, smul_add]
  | smul r x _ hx =>
    rw [map_smul, map_smul, map_smul, hx, smul_algebra_smul_comm, smul_comm (q * m).negOnePow r]

/-- A13: for `a` of degree `2` the sign disappears: `σ(y·a) = a·σ(y)` on all of `TotR`. -/
theorem blockSwap_rAct_two {a : A} (ha : a ∈ 𝒜 2) (y : TotR 𝒜 Q) :
    blockSwap 𝒜 Q (TotR.rAct 𝒜 Q a y) = a • blockSwap 𝒜 Q y := by
  refine totR_induction
    (C := fun y => blockSwap 𝒜 Q (TotR.rAct 𝒜 Q a y) = a • blockSwap 𝒜 Q y) y ?_ ?_ ?_
  · simp only [map_zero, smul_zero]
  · intro x y hx hy
    simp only [map_add, smul_add]
    rw [hx, hy]
  · intro p q e b hb
    rw [blockSwap_rAct_tmul ha hb e, Int.negOnePow_two_mul, one_smul]

/-- A13: `σ` commutes with sign scalars. -/
theorem blockSwap_units_smul (u : ℤˣ) (x : TotR 𝒜 Q) :
    blockSwap 𝒜 Q (u • x) = u • blockSwap 𝒜 Q x := by
  simp only [Units.smul_def, map_zsmul]

/-- A13: `σ⁻¹` commutes with sign scalars. -/
private theorem blockSwap_symm_units_smul (u : ℤˣ) (x : Tot 𝒜 Q) :
    (blockSwap 𝒜 Q).symm (u • x) = u • (blockSwap 𝒜 Q).symm x := by
  simp only [Units.smul_def, map_zsmul]

end Swap

/-! ## Objects -/

variable {cB : A}

namespace BlockQuasiCohesive

variable (E : BlockQuasiCohesive 𝒜 cB)

/-- A13: Block's operator transported to the left total module, `𝕏 = σ ∘ 𝔼 ∘ σ⁻¹`. -/
def leftX : Tot 𝒜 E.Q →ₗ[k] Tot 𝒜 E.Q :=
  (blockSwap 𝒜 E.Q).toLinearMap ∘ₗ E.E ∘ₗ (blockSwap 𝒜 E.Q).symm.toLinearMap

/-- A13: formula for `leftX`. -/
theorem leftX_apply (x : Tot 𝒜 E.Q) :
    E.leftX x = blockSwap 𝒜 E.Q (E.E ((blockSwap 𝒜 E.Q).symm x)) := rfl

/-- A13: `leftX` has total degree `1`. -/
theorem leftX_mem {m : ℤ} {x : Tot 𝒜 E.Q} (hx : x ∈ totDeg 𝒜 E.Q m) :
    E.leftX x ∈ totDeg 𝒜 E.Q (m + 1) := by
  rw [leftX_apply, blockSwap_mem_totDeg_iff]
  refine E.E_mem ?_
  rw [← blockSwap_mem_totDeg_iff, LinearEquiv.apply_symm_apply]
  exact hx

/-- A13: Block's Leibniz rule on a homogeneous pure tensor `e ⊗ b`:
`𝔼(y·a) = 𝔼(y)·a + (-1)^{|y|} y·da`. -/
private theorem blockE_rAct_pure {u r : ℤ} {a b : A} (hb : b ∈ 𝒜 r) (e : E.Q u) :
    E.E (TotR.rAct 𝒜 E.Q a (TotR.tmul 𝒜 E.Q (lof (𝒜 0) ℤ E.Q u e) b)) =
      TotR.rAct 𝒜 E.Q a (E.E (TotR.tmul 𝒜 E.Q (lof (𝒜 0) ℤ E.Q u e) b)) +
        (u + r).negOnePow •
          TotR.rAct 𝒜 E.Q (GCDga.d (𝒜 := 𝒜) a) (TotR.tmul 𝒜 E.Q (lof (𝒜 0) ℤ E.Q u e) b) := by
  rw [TotR.rAct_tmul, E.leibniz e (b * a), E.leibniz e b, GCDga.leibniz hb a, map_add,
    totR_rAct_rAct, totR_tmul_add, totR_tmul_units_smul, TotR.rAct_tmul]
  simp only [Units.smul_def, map_zsmul, TotR.rAct_tmul, Int.negOnePow_add, Units.val_mul]
  module

/-- A13: Block's Leibniz rule becomes the left Leibniz rule
`𝕏(a·x) = da·x + (-1)^{|a|} a·𝕏x`. -/
theorem leftX_leibniz {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (x : Tot 𝒜 E.Q) :
    E.leftX (a • x) = GCDga.d (𝒜 := 𝒜) a • x + p.negOnePow • a • E.leftX x := by
  obtain ⟨y, rfl⟩ := (blockSwap 𝒜 E.Q).surjective x
  refine totR_induction (C := fun y => E.leftX (a • blockSwap 𝒜 E.Q y) =
    GCDga.d (𝒜 := 𝒜) a • blockSwap 𝒜 E.Q y + p.negOnePow • a • E.leftX (blockSwap 𝒜 E.Q y))
    y ?_ ?_ ?_
  · simp only [map_zero, smul_zero, add_zero]
  · intro y z hy hz
    simp only [map_add, smul_add]
    rw [hy, hz]
    abel
  · intro u r e b hb
    have hmem : TotR.tmul 𝒜 E.Q (lof (𝒜 0) ℤ E.Q u e) b ∈ totDegR 𝒜 E.Q (u + r) :=
      Submodule.subset_span ⟨u, r, e, b, rfl, hb, rfl⟩
    have hEmem := E.E_mem hmem
    have hE := E.blockE_rAct_pure (a := a) hb e
    have h1 := blockSwap_rAct ha hmem
    have h2 := blockSwap_rAct ha hEmem
    have h3 := blockSwap_rAct (GCDga.d_mem (𝒜 := 𝒜) ha) hmem
    generalize TotR.tmul 𝒜 E.Q (lof (𝒜 0) ℤ E.Q u e) b = y at *
    generalize u + r = m at *
    have hx : a • blockSwap 𝒜 E.Q y =
        (p * m).negOnePow • blockSwap 𝒜 E.Q (TotR.rAct 𝒜 E.Q a y) := by
      rw [h1, smul_smul, Int.units_mul_self, one_smul]
    have hl : ∀ w, E.leftX (blockSwap 𝒜 E.Q w) = blockSwap 𝒜 E.Q (E.E w) := fun w => by
      rw [leftX_apply, LinearEquiv.symm_apply_apply]
    have hs1 : (p * m).negOnePow * (p * (m + 1)).negOnePow = p.negOnePow := by
      rw [← Int.negOnePow_add, show p * m + p * (m + 1) = p + 2 * (p * m) by ring,
        Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
    have hs2 : (p * m).negOnePow * m.negOnePow * ((p + 1) * m).negOnePow = 1 := by
      rw [← Int.negOnePow_add, ← Int.negOnePow_add,
        show p * m + m + (p + 1) * m = 2 * (p * m + m) by ring, Int.negOnePow_two_mul]
    rw [hx, Units.smul_def, map_zsmul, hl, hE, map_add, blockSwap_units_smul, h2, h3, hl,
      ← Units.smul_def, smul_add, smul_smul, smul_smul, smul_smul, hs1, hs2, one_smul]
    abel

/-- A13: Block's integrability `𝔼 ∘ 𝔼 + (·cB) = 0` becomes flatness `𝕏 ∘ 𝕏 = c·(-)` for
`c = -cB`. -/
theorem leftX_flat (h : GCDga.c (𝒜 := 𝒜) = -cB) (x : Tot 𝒜 E.Q) :
    E.leftX (E.leftX x) = GCDga.c (𝒜 := 𝒜) • x := by
  have hcB : cB ∈ 𝒜 2 := by
    have := GCDga.c_mem (𝒜 := 𝒜)
    rwa [h, neg_mem_iff] at this
  rw [leftX_apply, leftX_apply, LinearEquiv.symm_apply_apply]
  have h2 := E.integrable ((blockSwap 𝒜 E.Q).symm x)
  rw [eq_neg_of_add_eq_zero_left h2, map_neg, blockSwap_rAct_two hcB, LinearEquiv.apply_symm_apply,
    h, neg_smul]

/-- **A13.** A quasi-cohesive module in Block's convention over `(A, d, cB)` as a left
quasi-cohesive module over `(A, d, c)`, `c = -cB`: same generators, operator `σ ∘ 𝔼 ∘ σ⁻¹`
(conventions §3, ⚠ curvature sign). -/
def toLeft (h : GCDga.c (𝒜 := 𝒜) = -cB) : QuasiCohesive 𝒜 where
  Q := E.Q
  X := E.leftX
  X_mem := E.leftX_mem
  leibniz := E.leftX_leibniz
  flat := E.leftX_flat h

end BlockQuasiCohesive

end Cohesive
