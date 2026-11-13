-- FROZEN (gate 3, 26 Oct 2026; generator data, in the main statement). Do not edit without approval.
import Cohesivemodules.Algebra.CohesiveDef
import Mathlib.Data.Int.Interval

set_option linter.style.header false

/-!
# A3.a: quasi-cohesive modules from generator data (definitions)

Blueprint item A3.a. This file holds definitions the main statement depends on (through the
base change A9 and the modules from complexes A10); it is to be frozen at gate 3. Theorems about
them stay in `Algebra/Cohesive.lean`.

Definitions: `GCDga.proj`, `GCDga.sigma`, `Tot.tmul`, `GenData`, `GenData.θ`,
`GenData.extendAux`, `GenData.extendAdd`, `GenData.extend`, `QuasiCohesive.ofGenerators`;
together with the lemmas their constructions need (the projections, `σ`, pure tensors in the
total module and total degrees, among them the helper `Tot.tmulLeft`) and their basic API.

* The homogeneous projections `proj q : A → A` and the parity involution
  `σ(a) = Σ_q (-1)^q a_q` are `A⁰`-linear; `σ` is multiplicative, and graded commutativity
  gives `σ(a)·df = df·a` for `f ∈ A⁰`.
-/

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

namespace GCDga

/-- The homogeneous projection `a ↦ a_q`, as an `A⁰`-linear map. -/
def proj (q : ℤ) : A →ₗ[𝒜 0] A where
  toFun a := decompose 𝒜 a q
  map_add' a b := by simp
  map_smul' f a := by
    simp only [smul0_def, RingHom.id_apply, coe_decompose_mul_of_left_mem_zero 𝒜 f.2]

/-- A3.a: formula for `proj`. -/
@[simp] theorem proj_apply (q : ℤ) (a : A) : proj 𝒜 q a = decompose 𝒜 a q := rfl

/-- `proj` is also `k`-linear. -/
theorem proj_smul (q : ℤ) (r : k) (a : A) : proj 𝒜 q (r • a) = r • proj 𝒜 q a := by
  simp only [proj_apply, decompose_smul, DirectSum.smul_apply, Submodule.coe_smul]

/-- A3.a: `proj q` on a homogeneous element. -/
theorem proj_of_mem {p q : ℤ} {a : A} (ha : a ∈ 𝒜 p) :
    proj 𝒜 q a = if p = q then a else 0 := by
  rw [proj_apply, decompose_of_mem 𝒜 ha]
  by_cases h : p = q
  · subst h; simp
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    simp [h]

/-- A3.a: `proj q a` has degree `q`. -/
theorem proj_mem (q : ℤ) (a : A) : proj 𝒜 q a ∈ 𝒜 q := (decompose 𝒜 a q).2

/-- The degrees in which `a` can have a nonzero component lie in `[0, N]`. -/
theorem proj_eq_zero_of_not_mem {q : ℤ} (hq : q ∉ Finset.Icc (0 : ℤ) (N 𝒜)) (a : A) :
    proj 𝒜 q a = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hq
  rcases hq with hq | hq
  · exact eq_zero_of_neg 𝒜 hq (proj_mem 𝒜 q a)
  · exact eq_zero_of_gt 𝒜 hq (proj_mem 𝒜 q a)

/-- Every `a` is the sum of its components in degrees `0, …, N`. -/
theorem sum_proj (a : A) : ∑ q ∈ Finset.Icc (0 : ℤ) (N 𝒜), proj 𝒜 q a = a := by
  classical
  conv_rhs => rw [← sum_support_decompose 𝒜 a]
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro q hq
    by_contra h
    exact (DFinsupp.mem_support_iff.1 hq) (Subtype.ext (proj_eq_zero_of_not_mem 𝒜 h a))
  · intro q hq
    simp only [Finset.mem_sdiff, DFinsupp.mem_support_iff, not_not] at hq
    simp [hq.2]
  · intro q _
    rfl

/-- The parity involution `σ(a) = Σ_q (-1)^q a_q` (sign of a homogeneous element). -/
def sigma : A →ₗ[𝒜 0] A :=
  ∑ q ∈ Finset.Icc (0 : ℤ) (N 𝒜), q.negOnePow • proj 𝒜 q

/-- A3.a: formula for `σ`. -/
theorem sigma_apply (a : A) :
    sigma 𝒜 a = ∑ q ∈ Finset.Icc (0 : ℤ) (N 𝒜), q.negOnePow • proj 𝒜 q a := by
  simp [sigma, LinearMap.sum_apply]

/-- `σ(a) = (-1)^p a` for `a ∈ A^p`. -/
theorem sigma_of_mem {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) : sigma 𝒜 a = p.negOnePow • a := by
  rw [sigma_apply]
  simp_rw [proj_of_mem 𝒜 ha]
  by_cases hp : p ∈ Finset.Icc (0 : ℤ) (N 𝒜)
  · rw [Finset.sum_eq_single p (fun q _ hq => by simp [Ne.symm hq]) (fun h => absurd hp h)]
    simp
  · have : a = 0 := by
      have := proj_eq_zero_of_not_mem 𝒜 hp a
      rwa [proj_of_mem 𝒜 ha, ite_eq_left_iff.2 (fun h => absurd rfl h)] at this
    simp [this]

/-- `σ` is `k`-linear. -/
theorem sigma_smul (r : k) (a : A) : sigma 𝒜 (r • a) = r • sigma 𝒜 a := by
  simp only [sigma_apply, proj_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => smul_comm _ _ _

/-- `σ` is multiplicative. -/
theorem sigma_mul (a b : A) : sigma 𝒜 (a * b) = sigma 𝒜 a * sigma 𝒜 b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [add_mul, map_add, hx, hy, map_add, add_mul]
  | homogeneous x =>
    induction b using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add y z hy hz => rw [mul_add, map_add, hy, hz, map_add, mul_add]
    | homogeneous y =>
      rw [sigma_of_mem 𝒜 (SetLike.GradedMul.mul_mem x.2 y.2), sigma_of_mem 𝒜 x.2,
        sigma_of_mem 𝒜 y.2, Int.negOnePow_add, smul_mul_smul_comm, mul_comm]

/-- Graded commutativity in the form used for well-definedness of `𝕏`:
`σ(a)·df = df·a` for `f ∈ A⁰` (since `df ∈ A¹`). -/
theorem sigma_mul_d {f : A} (hf : f ∈ 𝒜 0) (a : A) :
    sigma 𝒜 a * d (𝒜 := 𝒜) f = d (𝒜 := 𝒜) f * a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, add_mul, hx, hy, mul_add]
  | homogeneous x =>
    rw [sigma_of_mem 𝒜 x.2, smul_mul_assoc, gcomm x.2 (d_mem_one 𝒜 hf), mul_one, smul_smul,
      Int.units_mul_self, one_smul]

/-- The curvature is central (it has even degree). -/
theorem c_central (a : A) : c (𝒜 := 𝒜) * a = a * c (𝒜 := 𝒜) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [mul_add, hx, hy, add_mul]
  | homogeneous x =>
    rw [gcomm (c_mem (𝒜 := 𝒜)) x.2, show (2 : ℤ) * _ = 2 * (_ : ℤ) from rfl,
      Int.negOnePow_two_mul, one_smul]

end GCDga

/-! ## The total module: pure tensors -/

namespace Tot

variable {𝒜} {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

variable (𝒜 Q) in
/-- `a ⊗ e` in the total module `A ⊗_{A⁰} ⨁_p Q^p`. -/
def tmul (a : A) (e : ⨁ p, Q p) : Tot 𝒜 Q := a ⊗ₜ[𝒜 0] e

/-- A3.a: `a • (b ⊗ e) = (ab) ⊗ e`. -/
theorem smul_tmul (a b : A) (e : ⨁ p, Q p) : a • tmul 𝒜 Q b e = tmul 𝒜 Q (a * b) e :=
  TensorProduct.smul_tmul' (R := 𝒜 0) a b e

/-- A3.a: `r • (b ⊗ e) = (r b) ⊗ e` for `r : k`. -/
theorem smul_tmul_k (r : k) (b : A) (e : ⨁ p, Q p) : r • tmul 𝒜 Q b e = tmul 𝒜 Q (r • b) e :=
  TensorProduct.smul_tmul' (R := 𝒜 0) r b e

/-- A3.a: `⊗` is additive on the left. -/
theorem add_tmul (a b : A) (e : ⨁ p, Q p) : tmul 𝒜 Q (a + b) e = tmul 𝒜 Q a e + tmul 𝒜 Q b e :=
  TensorProduct.add_tmul a b e

/-- A3.a: `⊗` is additive on the right. -/
theorem tmul_add (a : A) (e e' : ⨁ p, Q p) : tmul 𝒜 Q a (e + e') = tmul 𝒜 Q a e + tmul 𝒜 Q a e' :=
  TensorProduct.tmul_add a e e'

/-- A3.a: `0 ⊗ e = 0`. -/
@[simp] theorem zero_tmul (e : ⨁ p, Q p) : tmul 𝒜 Q (0 : A) e = 0 := TensorProduct.zero_tmul _ e
/-- A3.a: `a ⊗ 0 = 0`. -/
@[simp] theorem tmul_zero (a : A) : tmul 𝒜 Q a (0 : ⨁ p, Q p) = 0 := TensorProduct.tmul_zero _ a

/-- `A⁰`-scalars move across the tensor sign. -/
theorem tmul_smul0 (a : A) (f : 𝒜 0) (e : ⨁ p, Q p) : tmul 𝒜 Q a (f • e) = tmul 𝒜 Q (a * f) e := by
  rw [show a * (f : A) = f • a from (GCDga.central 𝒜 f.2 a).symm]
  exact (TensorProduct.smul_tmul (R := 𝒜 0) f a e).symm

/-- `a ⊗ e = a • (1 ⊗ e)`. -/
theorem tmul_eq_smul (a : A) (e : ⨁ p, Q p) : tmul 𝒜 Q a e = a • tmul 𝒜 Q 1 e := by
  rw [smul_tmul, mul_one]

/-- Induction on elements of the total module. -/
theorem induction_on {C : Tot 𝒜 Q → Prop} (x : Tot 𝒜 Q)
    (ht : ∀ a e, C (tmul 𝒜 Q a e)) (hadd : ∀ x y, C x → C y → C (x + y)) : C x :=
  TensorProduct.inductionOn x ht hadd

/-- A3.a: integer scalars on the left factor. -/
theorem tmul_zsmul (z : ℤ) (a : A) (e : ⨁ p, Q p) : tmul 𝒜 Q (z • a) e = z • tmul 𝒜 Q a e :=
  TensorProduct.smul_tmul' (R := 𝒜 0) z a e |>.symm

/-- A3.a: signs on the left factor. -/
theorem tmul_units_smul (u : ℤˣ) (a : A) (e : ⨁ p, Q p) :
    tmul 𝒜 Q (u • a) e = u • tmul 𝒜 Q a e := by
  rw [Units.smul_def, Units.smul_def, tmul_zsmul]

variable (𝒜 Q) in
/-- `a ↦ a ⊗ e` as an additive map. -/
def tmulLeft (e : ⨁ p, Q p) : A →+ Tot 𝒜 Q :=
  AddMonoidHom.mk' (fun a => tmul 𝒜 Q a e) (fun a b => add_tmul a b e)

/-- A3.a: formula for `tmulLeft`. -/
theorem tmulLeft_apply (e : ⨁ p, Q p) (a : A) : tmulLeft 𝒜 Q e a = tmul 𝒜 Q a e := rfl

/-- `a ⊗ e = Σ_q a_q ⊗ e`. -/
theorem tmul_eq_sum (a : A) (e : ⨁ p, Q p) :
    tmul 𝒜 Q a e = ∑ q ∈ Finset.Icc (0 : ℤ) (GCDga.N 𝒜), tmul 𝒜 Q (GCDga.proj 𝒜 q a) e := by
  conv_lhs => rw [← GCDga.sum_proj 𝒜 a]
  rw [← tmulLeft_apply, map_sum]
  rfl

end Tot

/-! ## Total degree -/

section TotDeg

variable {𝒜} {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- `a ⊗ e` with `a ∈ A^q`, `e ∈ Q^p` has total degree `q + p`. -/
theorem tmul_mem_totDeg {q p : ℤ} {a : A} (ha : a ∈ 𝒜 q) (e : Q p) :
    Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e) ∈ totDeg 𝒜 Q (q + p) :=
  Submodule.subset_span ⟨q, p, a, e, rfl, ha, rfl⟩

/-- Multiplication by `a ∈ A^q` raises the total degree by `q`. -/
theorem smul_mem_totDeg {q m : ℤ} {a : A} (ha : a ∈ 𝒜 q) {x : Tot 𝒜 Q}
    (hx : x ∈ totDeg 𝒜 Q m) : a • x ∈ totDeg 𝒜 Q (q + m) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q', p, b, e, rfl, hb, rfl⟩ := hx
    change a • Tot.tmul 𝒜 Q b _ ∈ _
    rw [Tot.smul_tmul, ← add_assoc]
    exact tmul_mem_totDeg (SetLike.GradedMul.mul_mem ha hb) e
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_algebra_smul_comm]; exact Submodule.smul_mem _ r hx

end TotDeg

/-! ## A3.a: constructing `𝕏` from generator data -/

variable {𝒜} {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

variable (𝒜 Q) in
/-- **A3.a** Generator data for a quasi-cohesive structure on `Q`: an additive map
`θ : ⨁_p Q^p → A ⊗_{A⁰} ⨁_p Q^p` (the restriction of `𝕏` to the generators `1 ⊗ e`) with the
Leibniz rule `θ(f e) = df ⊗ e + f·θ(e)` for `f ∈ A⁰`. [B, after Def 2.3.1]. -/
structure GenData where
  /-- The operator on the generators. -/
  θ : (⨁ p, Q p) →+ Tot 𝒜 Q
  /-- `θ(f e) = df ⊗ e + f θ(e)`. -/
  leibniz : ∀ (f : 𝒜 0) (e : ⨁ p, Q p),
    θ (f • e) = Tot.tmul 𝒜 Q (GCDga.d (𝒜 := 𝒜) f) e + (f : A) • θ e

namespace GenData

variable (D : GenData 𝒜 Q)

/-- The bi-additive map `(a, e) ↦ da ⊗ e + σ(a)·θ(e)`. -/
def extendAux : A →+ (⨁ p, Q p) →+ Tot 𝒜 Q :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun e => Tot.tmul 𝒜 Q (GCDga.d (𝒜 := 𝒜) a) e + GCDga.sigma 𝒜 a • D.θ e)
      (fun e e' => by rw [Tot.tmul_add, map_add, smul_add]; abel))
    (fun a b => AddMonoidHom.ext fun e => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, Tot.add_tmul,
        add_smul]
      abel)

/-- A3.a: formula for `extendAux`. -/
theorem extendAux_apply (a : A) (e : ⨁ p, Q p) : D.extendAux a e =
    Tot.tmul 𝒜 Q (GCDga.d (𝒜 := 𝒜) a) e + GCDga.sigma 𝒜 a • D.θ e := rfl

/-- The bi-additive map is `A⁰`-balanced; this uses graded commutativity
(`GCDga.sigma_mul_d`) and the Leibniz rule of `θ`. -/
theorem extendAux_balanced (r : 𝒜 0) (a : A) (e : ⨁ p, Q p) :
    D.extendAux (r • a) e = D.extendAux a (r • e) := by
  rw [extendAux_apply, extendAux_apply, D.leibniz, (GCDga.sigma 𝒜).map_smul r a,
    GCDga.smul0_def 𝒜 r a, GCDga.smul0_def 𝒜 r (GCDga.sigma 𝒜 a), GCDga.leibniz_zero 𝒜 r.2 a,
    Tot.tmul_smul0, smul_add, Tot.smul_tmul, GCDga.sigma_mul_d 𝒜 r.2 a, ← mul_smul,
    ← GCDga.central 𝒜 r.2 (GCDga.sigma 𝒜 a), ← GCDga.central 𝒜 r.2 (GCDga.d (𝒜 := 𝒜) a),
    Tot.add_tmul]
  abel

/-- The extension as an additive map (well defined by `extendAux_balanced`). -/
def extendAdd : Tot 𝒜 Q →+ Tot 𝒜 Q :=
  TensorProduct.liftAddHom (R := 𝒜 0) D.extendAux D.extendAux_balanced

/-- **A3.a** The extension `𝕏(a ⊗ e) = da ⊗ e + (-1)^{|a|} a·θ(e)` of generator data to the total
module. -/
def extend : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q where
  toFun := D.extendAdd
  map_add' := D.extendAdd.map_add
  map_smul' r x := by
    induction x using Tot.induction_on with
    | ht a e =>
      rw [Tot.smul_tmul_k]
      change D.extendAux (r • a) e = r • D.extendAux a e
      rw [extendAux_apply, extendAux_apply, map_smul, GCDga.sigma_smul, smul_add,
        Tot.smul_tmul_k, smul_assoc]
    | hadd x y hx hy =>
      simp only [RingHom.id_apply] at hx hy ⊢
      rw [smul_add, D.extendAdd.map_add, hx, hy, D.extendAdd.map_add, smul_add]

/-- A3.a: the extension on pure tensors. -/
theorem extend_tmul (a : A) (e : ⨁ p, Q p) : D.extend (Tot.tmul 𝒜 Q a e) =
    Tot.tmul 𝒜 Q (GCDga.d (𝒜 := 𝒜) a) e + GCDga.sigma 𝒜 a • D.θ e := rfl

/-- The extension restricts to `θ` on the generators. -/
theorem extend_tmul_one (e : ⨁ p, Q p) : D.extend (Tot.tmul 𝒜 Q 1 e) = D.θ e := by
  rw [extend_tmul, GCDga.d_one, Tot.zero_tmul, zero_add,
    GCDga.sigma_of_mem 𝒜 (SetLike.GradedOne.one_mem (A := 𝒜)), Int.negOnePow_zero, one_smul,
    one_smul]

/-- The extension satisfies the Leibniz rule `𝕏(b·x) = db·x + (-1)^{|b|} b·𝕏x`. -/
theorem extend_leibniz {p : ℤ} {b : A} (hb : b ∈ 𝒜 p) (x : Tot 𝒜 Q) :
    D.extend (b • x) = GCDga.d (𝒜 := 𝒜) b • x + p.negOnePow • b • D.extend x := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.smul_tmul, extend_tmul, extend_tmul, GCDga.leibniz hb, GCDga.sigma_mul,
      GCDga.sigma_of_mem 𝒜 hb, Tot.add_tmul, Tot.tmul_units_smul, Tot.smul_tmul, smul_add,
      Tot.smul_tmul, smul_add, ← Tot.smul_tmul, smul_mul_assoc]
    simp only [Units.smul_def, smul_assoc, mul_smul]
    abel
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add, smul_add]; abel

/-- The extension has total degree `1` if `θ` does on the generators. -/
theorem extend_mem (hθ : ∀ p (e : Q p), D.θ (lof (𝒜 0) ℤ Q p e) ∈ totDeg 𝒜 Q (p + 1))
    {m : ℤ} {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) : D.extend x ∈ totDeg 𝒜 Q (m + 1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change D.extend (Tot.tmul 𝒜 Q a _) ∈ _
    rw [extend_tmul, GCDga.sigma_of_mem 𝒜 ha]
    refine add_mem ?_ ?_
    · have := tmul_mem_totDeg (Q := Q) (GCDga.d_mem (𝒜 := 𝒜) ha) e
      rwa [show q + 1 + p = q + p + 1 by ring] at this
    · have := smul_mem_totDeg ha (hθ p e)
      rw [show q + (p + 1) = q + p + 1 by ring] at this
      rw [Units.smul_def, smul_assoc]
      exact Submodule.smul_of_tower_mem _ _ this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- On `a ⊗ e` with `a` homogeneous, `𝕏 ∘ 𝕏` is computed from its value on `1 ⊗ e`. -/
theorem extend_extend_tmul_of_mem
    (hflat : ∀ e, D.extend (D.θ e) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 Q 1 e)
    {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (e : ⨁ p, Q p) :
    D.extend (D.extend (Tot.tmul 𝒜 Q a e)) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 Q a e := by
  have hda := GCDga.d_mem (𝒜 := 𝒜) ha
  have hu : ∀ (u : ℤˣ) (w : Tot 𝒜 Q), D.extend (u • w) = u • D.extend w := fun u w => by
    rw [Units.smul_def, Units.smul_def, map_zsmul]
  rw [Tot.tmul_eq_smul, D.extend_leibniz ha, map_add, D.extend_leibniz hda, GCDga.d_d,
    zero_smul, zero_add, hu, D.extend_leibniz ha, extend_tmul_one, hflat, smul_smul a,
    ← GCDga.c_central 𝒜 a, mul_smul, Int.negOnePow_succ, Units.neg_smul, smul_add,
    smul_smul p.negOnePow p.negOnePow, Int.units_mul_self, one_smul]
  abel

/-- **A3.a** Flatness of the extension follows from flatness on the generators. -/
theorem extend_extend (hflat : ∀ e, D.extend (D.θ e) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 Q 1 e)
    (x : Tot 𝒜 Q) : D.extend (D.extend x) = GCDga.c (𝒜 := 𝒜) • x := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.tmul_eq_sum, map_sum, map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ =>
      D.extend_extend_tmul_of_mem hflat (GCDga.proj_mem 𝒜 q a) e
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

end GenData

/-- **A3.a** The quasi-cohesive module defined by generator data `θ` of total degree `1` that is
flat on the generators: `𝕏(a ⊗ e) = da ⊗ e + (-1)^{|a|} a·θ(e)`. -/
def QuasiCohesive.ofGenerators (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (D : GenData 𝒜 Q)
    (hθ : ∀ p (e : Q p), D.θ (lof (𝒜 0) ℤ Q p e) ∈ totDeg 𝒜 Q (p + 1))
    (hflat : ∀ e, D.extend (D.θ e) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 Q 1 e) :
    QuasiCohesive 𝒜 where
  Q := Q
  X := D.extend
  X_mem := D.extend_mem hθ
  leibniz := D.extend_leibniz
  flat := D.extend_extend hflat

end Cohesive
