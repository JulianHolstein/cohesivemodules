import Cohesivemodules.Algebra.CohesiveDef
import Cohesivemodules.Algebra.GeneratorsDef
import Cohesivemodules.Algebra.GenHomDef
import Mathlib.Data.Int.Interval

set_option linter.style.header false

/-!
# A3–A4: theorems about cohesive modules

Blueprint items A3.a, A3.b, A4.c (definitions in `Algebra/CohesiveDef.lean`).
The A3.a generator construction (`GCDga.proj`, `GCDga.sigma`, `Tot.tmul`, `GenData`,
`QuasiCohesive.ofGenerators`, …) is in `Algebra/GeneratorsDef.lean`.

* The homogeneous projections `proj q : A → A` and the parity involution
  `σ(a) = Σ_q (-1)^q a_q` are `A⁰`-linear; `σ` is multiplicative, and graded commutativity
  gives `σ(a)·df = df·a` for `f ∈ A⁰`.

The sign twist `GCDga.twist`, `Tot.smul0_eq`, `Tot.oneTmul` and the A4.c definitions
`GenHom`, `restrictGen`, `extGen` (with `extGen_mem`) are in `Algebra/GenHomDef.lean`.
-/

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- A4: the sign twist `τₙ` (`GCDga.twist`) is an involution (used in A13 and Z2.a). -/
theorem twist_involutive (n : ℤ) (a : A) : GCDga.twist 𝒜 n (GCDga.twist 𝒜 n a) = a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | homogeneous x =>
    rw [GCDga.twist_of_mem 𝒜 n x.2, Units.smul_def, map_zsmul, ← Units.smul_def,
      GCDga.twist_of_mem 𝒜 n x.2, smul_smul, Int.units_mul_self, one_smul]

/-! ## A3.a: restriction to the generators -/

variable {𝒜} {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- **A3.a** Restriction to the generators determines `𝕏`: an operator with the Leibniz rule
that agrees with `𝕏` on all `1 ⊗ e` equals `𝕏`. [B, after Def 2.3.1]. -/
theorem QuasiCohesive.X_eq_of_generators (M : QuasiCohesive 𝒜) (X' : M.T →ₗ[k] M.T)
    (hX' : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : M.T,
      X' (a • x) = GCDga.d (𝒜 := 𝒜) a • x + p.negOnePow • a • X' x)
    (h : ∀ e, X' (Tot.tmul 𝒜 M.Q 1 e) = M.X (Tot.tmul 𝒜 M.Q 1 e)) : X' = M.X := by
  ext x
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.tmul_eq_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Tot.tmul_eq_smul, hX' (GCDga.proj_mem 𝒜 q a), M.leibniz (GCDga.proj_mem 𝒜 q a), h]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-! ## Form-degree projections and the generator embedding -/

namespace Tot

variable (𝒜 Q) in
/-- The form-degree projection `πⱼ(a ⊗ e) = aⱼ ⊗ e` on the total module. -/
def projF (j : ℤ) : Tot 𝒜 Q →ₗ[𝒜 0] Tot 𝒜 Q :=
  TensorProduct.map (GCDga.proj 𝒜 j) LinearMap.id

/-- `πⱼ` on pure tensors. -/
theorem projF_tmul (j : ℤ) (a : A) (e : ⨁ p, Q p) :
    projF 𝒜 Q j (tmul 𝒜 Q a e) = tmul 𝒜 Q (GCDga.proj 𝒜 j a) e := rfl

/-- `πⱼ` is `k`-linear. -/
theorem projF_smul_k (j : ℤ) (r : k) (x : Tot 𝒜 Q) :
    projF 𝒜 Q j (r • x) = r • projF 𝒜 Q j x := by
  induction x using induction_on with
  | ht a e => rw [smul_tmul_k, projF_tmul, projF_tmul, GCDga.proj_smul, smul_tmul_k]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `πⱼ` on `a ⊗ e` with `a` homogeneous. -/
theorem projF_tmul_of_mem {j q : ℤ} {a : A} (ha : a ∈ 𝒜 q) (e : ⨁ p, Q p) :
    projF 𝒜 Q j (tmul 𝒜 Q a e) = if q = j then tmul 𝒜 Q a e else 0 := by
  rw [projF_tmul, GCDga.proj_of_mem 𝒜 ha]
  split_ifs <;> simp

/-- Multiplication by `a ∈ A^q` shifts the form degree by `q`: `πⱼ(a·x) = a·π_{j-q}(x)`. -/
theorem projF_smul_of_mem {j q : ℤ} {a : A} (ha : a ∈ 𝒜 q) (x : Tot 𝒜 Q) :
    projF 𝒜 Q j (a • x) = a • projF 𝒜 Q (j - q) x := by
  induction x using induction_on with
  | ht b e =>
    rw [smul_tmul, projF_tmul, projF_tmul, smul_tmul]
    congr 1
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, mul_add]
    | @homogeneous i y =>
      rw [GCDga.proj_of_mem 𝒜 (SetLike.GradedMul.mul_mem ha y.2), GCDga.proj_of_mem 𝒜 y.2]
      by_cases h : q + i = j
      · have h' : i = j - q := by omega
        simp [h']
      · have h' : ¬i = j - q := by omega
        simp [h, h']
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable (𝒜) in
/-- The degree-`0` part as an element of `A⁰`. -/
def proj0 (a : A) : 𝒜 0 := ⟨GCDga.proj 𝒜 0 a, GCDga.proj_mem 𝒜 0 a⟩

variable (𝒜) in
/-- `proj0` as an `A⁰`-linear map. -/
def proj0L : A →ₗ[𝒜 0] 𝒜 0 where
  toFun := proj0 𝒜
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' f a := Subtype.ext ((GCDga.proj 𝒜 0).map_smul f a)

variable (𝒜 Q) in
/-- The augmentation `ε(a ⊗ e) = a₀·e` from the total module back to the generators. -/
def eps : Tot 𝒜 Q →ₗ[𝒜 0] (⨁ p, Q p) :=
  TensorProduct.lift ((LinearMap.lsmul (𝒜 0) (⨁ p, Q p)).comp (proj0L 𝒜))

/-- `ε` on pure tensors. -/
theorem eps_tmul (a : A) (e : ⨁ p, Q p) : eps 𝒜 Q (tmul 𝒜 Q a e) = proj0 𝒜 a • e := rfl

/-- `ε(1 ⊗ e) = e`. -/
theorem eps_oneTmul (e : ⨁ p, Q p) : eps 𝒜 Q (oneTmul 𝒜 Q e) = e := by
  rw [oneTmul_apply, eps_tmul]
  convert one_smul (𝒜 0) e
  exact Subtype.ext (by
    show GCDga.proj 𝒜 0 1 = 1
    rw [GCDga.proj_of_mem 𝒜 (SetLike.GradedOne.one_mem (A := 𝒜))]
    simp)

/-- `proj0` is multiplicative (the grading is non-negative). -/
theorem proj0_mul (a b : A) : proj0 𝒜 (a * b) = proj0 𝒜 a * proj0 𝒜 b := by
  apply Subtype.ext
  show GCDga.proj 𝒜 0 (a * b) = GCDga.proj 𝒜 0 a * GCDga.proj 𝒜 0 b
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul]
  | @homogeneous i x =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
    | @homogeneous j y =>
      rw [GCDga.proj_of_mem 𝒜 (SetLike.GradedMul.mul_mem x.2 y.2), GCDga.proj_of_mem 𝒜 x.2,
        GCDga.proj_of_mem 𝒜 y.2]
      by_cases hi : i < 0
      · simp [GCDga.eq_zero_of_neg 𝒜 hi x.2]
      by_cases hj : j < 0
      · simp [GCDga.eq_zero_of_neg 𝒜 hj y.2]
      by_cases h : i + j = 0
      · have h1 : i = 0 := by omega
        have h2 : j = 0 := by omega
        simp [h1, h2]
      · by_cases h1 : i = 0
        · have h2 : ¬j = 0 := by omega
          simp [h1, h2]
        · simp [h, h1]

/-- `proj0` of a homogeneous element of degree `q ≠ 0` vanishes. -/
theorem proj0_of_mem_ne {q : ℤ} {a : A} (ha : a ∈ 𝒜 q) (hq : q ≠ 0) : proj0 𝒜 a = 0 :=
  Subtype.ext (by show GCDga.proj 𝒜 0 a = 0; rw [GCDga.proj_of_mem 𝒜 ha]; simp [hq])

/-- `ε(a·x) = a₀·ε(x)`. -/
theorem eps_smul (a : A) (x : Tot 𝒜 Q) : eps 𝒜 Q (a • x) = proj0 𝒜 a • eps 𝒜 Q x := by
  induction x using induction_on with
  | ht b e => rw [smul_tmul, eps_tmul, eps_tmul, proj0_mul, mul_smul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The elements of `⨁_p Q^p` concentrated in degree `m`. -/
def ConcAt (m : ℤ) (e : ⨁ p, Q p) : Prop := ∀ p, p ≠ m → e p = 0

/-- `ε` maps total degree `m` to generators of degree `m`. -/
theorem eps_concAt {m : ℤ} {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) : ConcAt m (eps 𝒜 Q x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    intro p' hp'
    change (eps 𝒜 Q (tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e))) p' = 0
    rw [eps_tmul]
    by_cases hq : q = 0
    · subst hq
      rw [DirectSum.smul_apply, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (by omega),
        smul_zero]
    · rw [proj0_of_mem_ne ha hq, zero_smul]; rfl
  | zero => intro p _; rfl
  | add x y _ _ hx hy => intro p hp; rw [map_add, DirectSum.add_apply, hx p hp, hy p hp, add_zero]
  | smul r x _ hx =>
    intro p hp
    rw [show r • x = (algebraMap k A r) • x from (algebraMap_smul A r x).symm, eps_smul,
      DirectSum.smul_apply, hx p hp, smul_zero]

end Tot

/-! ## A3.a: components of `𝕏`; A3.b in degree `0` -/

namespace QuasiCohesive

variable (M : QuasiCohesive 𝒜)

/-- The Leibniz rule for `f ∈ A⁰`, with the `A⁰`-action on the total module. -/
theorem X_smul0 (f : 𝒜 0) (x : M.T) :
    M.X (f • x) = GCDga.d (𝒜 := 𝒜) f • x + f • M.X x := by
  rw [Tot.smul0_eq, Tot.smul0_eq, M.leibniz f.2, Int.negOnePow_zero, one_smul]

/-- **A3.a** The component `𝕏ʲ = πⱼ ∘ 𝕏 ∘ (1 ⊗ -)` of `𝕏` on the generators: the part with form
degree `j`. [B, after Def 2.3.1], [A, eq. (2)]. -/
def comp (j : ℤ) (e : ⨁ p, M.Q p) : M.T :=
  Tot.projF 𝒜 M.Q j (M.X (Tot.oneTmul 𝒜 M.Q e))

/-- A3.a: `𝕏ʲ(f e)` split into the `df`-term and `f 𝕏ʲ(e)`. -/
theorem comp_aux (j : ℤ) (f : 𝒜 0) (e : ⨁ p, M.Q p) :
    M.comp j (f • e) = Tot.projF 𝒜 M.Q j (GCDga.d (𝒜 := 𝒜) f • Tot.oneTmul 𝒜 M.Q e) +
      f • M.comp j e := by
  rw [comp, (Tot.oneTmul 𝒜 M.Q).map_smul, M.X_smul0, map_add, (Tot.projF 𝒜 M.Q j).map_smul,
    comp]

/-- **A3.a** `𝕏ʲ` is `A⁰`-linear for `j ≠ 1`. -/
theorem comp_smul0 {j : ℤ} (hj : j ≠ 1) (f : 𝒜 0) (e : ⨁ p, M.Q p) :
    M.comp j (f • e) = f • M.comp j e := by
  rw [comp_aux, Tot.projF_smul_of_mem (GCDga.d_mem_one 𝒜 f.2), Tot.oneTmul_apply,
    Tot.projF_tmul_of_mem (SetLike.GradedOne.one_mem (A := 𝒜))]
  simp only [show ¬(0 : ℤ) = j - 1 by omega, ite_false, smul_zero, zero_add]

/-- **A3.a** `𝕏¹` is a connection: `𝕏¹(f e) = df ⊗ e + f 𝕏¹(e)`. -/
theorem comp_one_leibniz (f : 𝒜 0) (e : ⨁ p, M.Q p) :
    M.comp 1 (f • e) = Tot.tmul 𝒜 M.Q (GCDga.d (𝒜 := 𝒜) f) e + f • M.comp 1 e := by
  rw [comp_aux, Tot.projF_smul_of_mem (GCDga.d_mem_one 𝒜 f.2), Tot.oneTmul_apply,
    Tot.projF_tmul_of_mem (SetLike.GradedOne.one_mem (A := 𝒜))]
  simp only [show (0 : ℤ) = 1 - 1 by norm_num, ite_true, Tot.smul_tmul, mul_one]

/-- **A3.a** The differential `𝕏⁰ = ε ∘ 𝕏 ∘ (1 ⊗ -)` on the generators, `A⁰`-linear. -/
def X0 : (⨁ p, M.Q p) →ₗ[𝒜 0] (⨁ p, M.Q p) where
  toFun e := Tot.eps 𝒜 M.Q (M.X (Tot.oneTmul 𝒜 M.Q e))
  map_add' e e' := by simp only [map_add]
  map_smul' f e := by
    rw [(Tot.oneTmul 𝒜 M.Q).map_smul, M.X_smul0, map_add, (Tot.eps 𝒜 M.Q).map_smul,
      Tot.eps_smul, Tot.proj0_of_mem_ne (GCDga.d_mem_one 𝒜 f.2) one_ne_zero, zero_smul,
      zero_add, RingHom.id_apply]

/-- `ε ∘ 𝕏 = 𝕏⁰ ∘ ε`: the degree-`0` part of `𝕏` only sees degree-`0` parts. -/
theorem eps_X (x : M.T) : Tot.eps 𝒜 M.Q (M.X x) = M.X0 (Tot.eps 𝒜 M.Q x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    simp only [Tot.tmul_eq_sum (Q := M.Q) a e, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq := GCDga.proj_mem 𝒜 q a
    have h0 : Tot.proj0 𝒜 (GCDga.d (𝒜 := 𝒜) (GCDga.proj 𝒜 q a)) = 0 := by
      by_cases h1 : q + 1 = 0
      · rw [GCDga.eq_zero_of_neg 𝒜 (by omega) hq, map_zero]
        exact Tot.proj0_of_mem_ne (zero_mem (𝒜 1)) one_ne_zero
      · exact Tot.proj0_of_mem_ne (GCDga.d_mem (𝒜 := 𝒜) hq) h1
    rw [Tot.tmul_eq_smul, M.leibniz hq, map_add, Tot.eps_smul, h0, zero_smul, zero_add,
      Units.smul_def, map_zsmul, Tot.eps_smul, Tot.eps_smul, map_smul, ← Tot.oneTmul_apply,
      Tot.eps_oneTmul]
    by_cases h0q : q = 0
    · subst h0q
      rw [Int.negOnePow_zero, Units.val_one, one_smul]
      rfl
    · rw [Tot.proj0_of_mem_ne hq h0q, zero_smul, smul_zero, zero_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **A3.b** (degree `0`) `𝕏⁰ ∘ 𝕏⁰ = 0`: `(Q, 𝕏⁰)` is a complex of `A⁰`-modules, also with
curvature (which has form degree `2`). [A, eq. (2)]. -/
theorem X0_X0 (e : ⨁ p, M.Q p) : M.X0 (M.X0 e) = 0 := by
  have h := M.eps_X (M.X (Tot.oneTmul 𝒜 M.Q e))
  rw [M.flat, Tot.eps_smul, Tot.proj0_of_mem_ne (GCDga.c_mem (𝒜 := 𝒜)) two_ne_zero,
    zero_smul, M.eps_X, Tot.eps_oneTmul] at h
  exact h.symm

/-- **A3.a** `𝕏⁰` has degree `+1` on the generators: it maps `Q^p` to `Q^{p+1}`. -/
theorem X0_concAt {p : ℤ} (e : M.Q p) :
    Tot.ConcAt (p + 1) (M.X0 (lof (𝒜 0) ℤ M.Q p e)) := by
  have := tmul_mem_totDeg (Q := M.Q) (SetLike.GradedOne.one_mem (A := 𝒜)) e
  rw [zero_add] at this
  have h := Tot.eps_concAt (M.X_mem this)
  exact h

end QuasiCohesive

/-! ## A4.c: generator form of `Hom` -/

section GenHom

variable {M₁ M₂ : QuasiCohesive 𝒜}

/-- A4.c: `φ(a ⊗ e) = τₙ(a)·φ(1 ⊗ e)` for `φ ∈ Hom^n`. -/
theorem hom_tmul {n : ℤ} {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Hom M₁ M₂ n) (a : A)
    (e : ⨁ p, M₁.Q p) :
    φ (Tot.tmul 𝒜 M₁.Q a e) = GCDga.twist 𝒜 n a • φ (Tot.tmul 𝒜 M₁.Q 1 e) := by
  conv_lhs => rw [Tot.tmul_eq_sum, map_sum]
  rw [GCDga.twist_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Tot.tmul_eq_smul (GCDga.proj 𝒜 q a) e, hφ.2 (GCDga.proj_mem 𝒜 q a), smul_assoc]

variable (n : ℤ)

/-- **A4.c** `Hom^n(M₁, M₂) ≅ ⊕_p Hom_{A⁰}(Q₁^p, (A ⊗ Q₂)^{p+n})`, by restriction to the
generators; the inverse is the extension `ψ̂(a ⊗ e) = (-1)^{n|a|} a·ψ(e)`. [B, §2.3]. -/
def homEquivGen : Hom M₁ M₂ n ≃ₗ[k] GenHom M₁ M₂ n where
  __ := restrictGen n
  invFun ψ := ⟨extGen n ψ, extGen_mem n ψ⟩
  left_inv φ := by
    apply Subtype.ext
    ext x
    induction x using Tot.induction_on with
    | ht a e =>
      change GCDga.twist 𝒜 n a • φ.1 (Tot.tmul 𝒜 M₁.Q 1 e) = φ.1 (Tot.tmul 𝒜 M₁.Q a e)
      conv_rhs => rw [Tot.tmul_eq_sum, map_sum]
      rw [GCDga.twist_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Tot.tmul_eq_smul (GCDga.proj 𝒜 q a) e, φ.2.2 (GCDga.proj_mem 𝒜 q a), smul_assoc]
    | hadd x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  right_inv ψ := by
    apply Subtype.ext
    refine AddMonoidHom.ext fun e => ?_
    change GCDga.twist 𝒜 n 1 • ψ.1 e = ψ.1 e
    rw [GCDga.twist_one, one_smul]

end GenHom

end Cohesive
