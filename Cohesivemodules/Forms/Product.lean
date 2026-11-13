import Cohesivemodules.Forms.ProductDef
import Cohesivemodules.Forms.Fibre
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

set_option linter.style.header false

/-!
# F5: the product on the total fibre `Λ^{0,•}(E)`

Blueprint item F5 (conventions §6). The total fibre is the finite product
`Λ^{0,•}(E) = Π_{q ≤ n} Λ^{0,q}(E; ℂ)`, `n = dim_ℂ E` (`TotFibre E`, a normed space). Its
multiplication is transported along `Φ_tot = (Φ_q)_q : ⋀_ℂ (Ē)^* ≃ Λ^{0,•}(E)` (F2.b) from the
exterior algebra `ExteriorAlgebra ℂ (Dual_ℂ Ē)`, so associativity, the unit and graded
commutativity come from Mathlib (⚠ blueprint F5: replaces a hand-built shuffle product).
The definitions (and their basic API) are in `Cohesivemodules/Forms/ProductDef.lean`.

* `ofDeg q α` puts a `q`-form in the total fibre, `deg q x` takes the degree-`q` component; all
  statements about homogeneous elements use these, never `Fin` arithmetic.
* F5.a, the Laplace formula: for a `1`-form `φ`, `φ ∧ β = alternatizeUncurryFin (v ↦ φ(v) • β)`.
  This is the only link between the product and the analysis (∂̄ has the same normalization).
* `mulCLM`: the product is a continuous bilinear map (finite dimension), for smoothness of
  products of forms (F6, F9).

## Deviations
* The total fibre is indexed by `Fin (n + 1)`; `Λ^{0,q} = 0` for `q > n` (F2.c), so nothing is
  lost. F5.b (`F`-valued forms as a module) is LATER-only and not built here.
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace TotFibre

/-! ## Homogeneous elements -/

/-- **F5.** The degree-`q` component of an element of the total fibre (zero if `q > n`). -/
def deg (q : ℕ) : TotFibre E →ₗ[ℂ] DolbeaultFibre E q ℂ where
  toFun x := if h : q < Module.finrank ℂ E + 1 then x ⟨q, h⟩ else 0
  map_add' x y := by
    by_cases h : q < Module.finrank ℂ E + 1
    · simp only [h, ↓reduceDIte]
      rfl
    · simp only [h, ↓reduceDIte, add_zero]
  map_smul' c x := by
    by_cases h : q < Module.finrank ℂ E + 1
    · simp only [h, ↓reduceDIte]
      rfl
    · simp only [h, ↓reduceDIte, smul_zero]

/-- F5 helper: the `i`-th component of `ofDeg q α`. -/
private theorem ofDeg_apply (q : ℕ) (α : DolbeaultFibre E q ℂ) (i : Fin (Module.finrank ℂ E + 1)) :
    (show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from ofDeg q α) i =
      if h : q = (i : ℕ) then DolbeaultFibre.cast h α else 0 := rfl

/-- F5 helper: the degree-`q` component of `x`. -/
private theorem deg_apply (q : ℕ) (x : TotFibre E) :
    deg q x = if h : q < Module.finrank ℂ E + 1 then
      (show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from x) ⟨q, h⟩ else 0 := rfl

/-- F5: the degree-`q` component of a `q`-form is the form, if `q ≤ n`. -/
theorem deg_ofDeg_self {q : ℕ} (hq : q ≤ Module.finrank ℂ E) (α : DolbeaultFibre E q ℂ) :
    deg q (ofDeg q α : TotFibre E) = α := by
  have h : q < Module.finrank ℂ E + 1 := by omega
  rw [deg_apply]
  simp only [h, ↓reduceDIte]
  refine (ofDeg_apply q α ⟨q, h⟩).trans ?_
  simp only [Fin.val_mk, ↓reduceDIte]
  rfl

/-- F5: other components of a `q`-form vanish. -/
theorem deg_ofDeg_ne {p q : ℕ} (h : p ≠ q) (α : DolbeaultFibre E q ℂ) :
    deg p (ofDeg q α : TotFibre E) = 0 := by
  rw [deg_apply]
  by_cases hp : p < Module.finrank ℂ E + 1
  · simp only [hp, ↓reduceDIte]
    refine (ofDeg_apply q α ⟨p, hp⟩).trans ?_
    simp only [Fin.val_mk, Ne.symm h, ↓reduceDIte]
  · simp only [hp, ↓reduceDIte]

private theorem sum_ofDeg_deg_apply (x : TotFibre E) (i : Fin (Module.finrank ℂ E + 1)) :
    (show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from
      ∑ q ∈ Finset.range (Module.finrank ℂ E + 1), ofDeg q (deg q x)) i =
      (show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from x) i := by
  refine (Finset.sum_apply (M := fun i : Fin (Module.finrank ℂ E + 1) => DolbeaultFibre E i ℂ) i
    (Finset.range (Module.finrank ℂ E + 1))
    (fun q => (show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from
      ofDeg q (deg q x)))).trans ?_
  rw [Finset.sum_eq_single (i : ℕ)]
  · rw [ofDeg_apply, deg_apply]
    simp only [i.2, ↓reduceDIte]
    rfl
  · intro q _ hq
    rw [ofDeg_apply]
    simp only [hq, ↓reduceDIte]
  · intro h
    exact absurd (Finset.mem_range.2 i.2) h

/-- F5: every element is the sum of its homogeneous components. -/
theorem sum_ofDeg_deg (x : TotFibre E) :
    ∑ q ∈ Finset.range (Module.finrank ℂ E + 1), ofDeg q (deg q x) = x :=
  funext (sum_ofDeg_deg_apply x)

/-! ## The bridge from the exterior algebra -/

variable [FiniteDimensional ℂ E]

/-- F5: on `⋀^q`, `Φ_tot` is `Φ_q`, placed in degree `q`. -/
theorem extEquivTotFibre_of_mem {q : ℕ} (x : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    extEquivTotFibre E (x : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) =
      ofDeg q (extToFibre E q x) := by
  funext i
  show extToFibre E i (DirectSum.decompose (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E)))
    (x : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) i) = _
  rw [DirectSum.decompose_coe]
  show _ = (if h : q = (i : ℕ) then DolbeaultFibre.cast h (extToFibre E q x) else 0)
  by_cases h : q = (i : ℕ)
  · subst h
    rw [DirectSum.of_eq_same]
    simp only [↓reduceDIte]
    rfl
  · rw [DirectSum.of_eq_of_ne _ _ _ (fun h' => h h'.symm)]
    simp only [h, ↓reduceDIte, _root_.map_zero]

/-! ## The ring structure, transported along `Φ_tot` -/

/-- **F5.** `Φ_tot` is multiplicative: `Φ_tot` is an isomorphism of `ℂ`-algebras. -/
theorem extEquivTotFibre_mul (a b : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) :
    extEquivTotFibre E (a * b) = extEquivTotFibre E a * extEquivTotFibre E b := by
  rw [mul_def, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-! ## Homogeneous products -/

/-- F5 helper: `ofDeg q` of a form in degree `q > n` is zero. -/
private theorem ofDeg_of_gt {q : ℕ} (hq : Module.finrank ℂ E < q) (α : DolbeaultFibre E q ℂ) :
    (ofDeg q α : TotFibre E) = 0 := by
  funext i
  refine (ofDeg_apply q α i).trans ?_
  have : ¬ q = (i : ℕ) := by have := i.2; omega
  simp only [this, ↓reduceDIte]
  rfl

/-- F5 helper: `ofDeg q (deg q ·)` is the identity on homogeneous elements of degree `q`. -/
private theorem ofDeg_deg_ofDeg (q : ℕ) (γ : DolbeaultFibre E q ℂ) :
    (ofDeg q (deg q (ofDeg q γ : TotFibre E)) : TotFibre E) = ofDeg q γ := by
  by_cases hq : q ≤ Module.finrank ℂ E
  · rw [deg_ofDeg_self hq]
  · rw [ofDeg_of_gt (by omega), ofDeg_of_gt (by omega)]

/-- F5 helper: a homogeneous element is the image under `Φ_tot` of an element of `⋀^p`. -/
private theorem ofDeg_eq_extEquivTotFibre (p : ℕ) (α : DolbeaultFibre E p ℂ) :
    (ofDeg p α : TotFibre E) =
      extEquivTotFibre E (((extEquivFibre E p).symm α : ⋀[ℂ]^p (Module.Dual ℂ (Conj E))) :
        ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) := by
  rw [extEquivTotFibre_of_mem]
  congr 1
  exact ((extEquivFibre E p).apply_symm_apply α).symm

/-- F5 helper: `ι_multi` products commute up to the sign `(-1)^{pq}` (scalar in `ℂ`). -/
private theorem ιMulti_comm_aux {V : Type} [AddCommGroup V] [Module ℂ V] {p q : ℕ}
    (u : Fin p → V) (v : Fin q → V) :
    ExteriorAlgebra.ιMulti ℂ p u * ExteriorAlgebra.ιMulti ℂ q v =
      (-1 : ℂ) ^ (p * q) • (ExteriorAlgebra.ιMulti ℂ q v * ExteriorAlgebra.ιMulti ℂ p u) := by
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm, mul_comm q p]
  rcases Nat.even_or_odd (p * q) with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_smul, one_smul]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_smul, one_smul, Units.neg_smul, one_smul]

/-- F5 helper: graded commutativity of the exterior algebra for homogeneous elements. -/
private theorem graded_comm_aux {V : Type} [AddCommGroup V] [Module ℂ V] {p q : ℕ}
    (a b : ExteriorAlgebra ℂ V) (ha : a ∈ ⋀[ℂ]^p V) (hb : b ∈ ⋀[ℂ]^q V) :
    a * b = (-1 : ℂ) ^ (p * q) • (b * a) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at ha hb
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact ιMulti_comm_aux u v
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, add_mul, hy, hz, smul_add]
    | smul c y _ hy => rw [mul_smul_comm, smul_mul_assoc, hy, smul_comm]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy, smul_add]
  | smul c x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx, smul_comm]

/-- F5 helper: a product of homogeneous elements is homogeneous, as `Φ_tot` of the product. -/
private theorem ofDeg_mul_ofDeg_eq {p q : ℕ} (α : DolbeaultFibre E p ℂ) (β : DolbeaultFibre E q ℂ) :
    ∃ γ : DolbeaultFibre E (p + q) ℂ, (ofDeg p α * ofDeg q β : TotFibre E) = ofDeg (p + q) γ := by
  refine ⟨extToFibre E (p + q)
    ⟨((extEquivFibre E p).symm α : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
    ((extEquivFibre E q).symm β : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))),
    SetLike.mul_mem_graded ((extEquivFibre E p).symm α).2 ((extEquivFibre E q).symm β).2⟩, ?_⟩
  rw [ofDeg_eq_extEquivTotFibre p α, ofDeg_eq_extEquivTotFibre q β, ← extEquivTotFibre_mul]
  exact extEquivTotFibre_of_mem (E := E) ⟨_, SetLike.mul_mem_graded ((extEquivFibre E p).symm α).2
    ((extEquivFibre E q).symm β).2⟩

/-- **F5.** The product of a `p`-form and a `q`-form is a `(p+q)`-form. -/
theorem ofDeg_mul_ofDeg {p q : ℕ} (α : DolbeaultFibre E p ℂ) (β : DolbeaultFibre E q ℂ) :
    (ofDeg p α * ofDeg q β : TotFibre E) =
      ofDeg (p + q) (deg (p + q) (ofDeg p α * ofDeg q β : TotFibre E)) := by
  obtain ⟨γ, hγ⟩ := ofDeg_mul_ofDeg_eq α β
  rw [hγ, ofDeg_deg_ofDeg]

/-- **F5.** Graded commutativity: `α ∧ β = (-1)^{pq} β ∧ α` for a `p`-form `α` and a `q`-form
`β` (from `ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm`). -/
theorem ofDeg_mul_comm {p q : ℕ} (α : DolbeaultFibre E p ℂ) (β : DolbeaultFibre E q ℂ) :
    (ofDeg p α * ofDeg q β : TotFibre E) = (-1 : ℂ) ^ (p * q) • (ofDeg q β * ofDeg p α) := by
  rw [ofDeg_eq_extEquivTotFibre p α, ofDeg_eq_extEquivTotFibre q β, ← extEquivTotFibre_mul,
    ← extEquivTotFibre_mul, ← map_smul]
  congr 1
  exact graded_comm_aux _ _ ((extEquivFibre E p).symm α).2 ((extEquivFibre E q).symm β).2

/-- **F5.** The unit is the constant `0`-form `1` (F2.a). -/
theorem one_eq : (1 : TotFibre E) = ofDeg 0 (form0Equiv E ℂ 1) := by
  have h1 : extToFibre E 0 (exteriorPower.ιMulti ℂ 0 (fun i : Fin 0 => i.elim0)) =
      form0Equiv E ℂ 1 := by
    ext v
    rw [extToFibre_ιMulti]
    simp only [Matrix.det_isEmpty, form0Equiv_apply]
  rw [ofDeg_eq_extEquivTotFibre]
  have h2 : (extEquivFibre E 0).symm (form0Equiv E ℂ 1) =
      exteriorPower.ιMulti ℂ 0 (fun i : Fin 0 => i.elim0) :=
    (extEquivFibre E 0).symm_apply_eq.2 h1.symm
  rw [h2]
  show extEquivTotFibre E 1 = _
  congr 1

/-- F5 helper: the product of a decomposable `1`-vector and a decomposable `q`-vector. -/
private theorem ιMulti_one_mul_ιMulti {V : Type} [AddCommGroup V] [Module ℂ V] {q : ℕ}
    (f : V) (g : Fin q → V) :
    ExteriorAlgebra.ιMulti ℂ 1 ![f] * ExteriorAlgebra.ιMulti ℂ q g =
      ExteriorAlgebra.ιMulti ℂ (q + 1) (Matrix.vecCons f g) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply (n := q)]
  simp only [ExteriorAlgebra.ιMulti_zero_apply, mul_one, Matrix.cons_val_zero, Matrix.tail_cons]

/-- F5 helper: `Φ_1` of a decomposable `1`-vector is the corresponding functional. -/
private theorem extToFibre_one_ιMulti (f : Module.Dual ℂ (Conj E)) :
    (ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1)).symm
      (extToFibre E 1 (exteriorPower.ιMulti ℂ 1 ![f])) = LinearMap.toContinuousLinearMap f := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext v
  rw [extToFibre_ιMulti]
  simp only [Matrix.det_unique, Matrix.of_apply, ofSubsingletonLIE_apply]
  rfl

/-- F5 helper: the Laplace formula on decomposable elements. -/
private theorem laplace_gen {q : ℕ} (f : Module.Dual ℂ (Conj E))
    (g : Fin q → Module.Dual ℂ (Conj E)) :
    extToFibre E (q + 1) (exteriorPower.ιMulti ℂ (q + 1) (Matrix.vecCons f g)) =
      alternatizeUncurryFin (((ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1)).symm
        (extToFibre E 1 (exteriorPower.ιMulti ℂ 1 ![f]))).smulRight
          (extToFibre E q (exteriorPower.ιMulti ℂ q g))) := by
  ext v
  rw [extToFibre_ιMulti, alternatizeUncurryFin_apply, Matrix.det_succ_column_zero,
    extToFibre_one_ιMulti]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
    extToFibre_ιMulti, LinearMap.coe_toContinuousLinearMap', smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val_zero]
  have : ((Matrix.of fun i j => (Matrix.vecCons f g j) (v i)).submatrix i.succAbove Fin.succ) =
      Matrix.of fun a b => g b (i.removeNth v a) := rfl
  rw [this]
  simp only [zsmul_eq_mul]
  push_cast
  ring

omit [FiniteDimensional ℂ E] in
/-- F5 helper: `alternatizeUncurryFin` of `smulRight` is additive in the functional. -/
private theorem alt_smulRight_add_left {q : ℕ} (c1 c2 : Conj E →L[ℂ] ℂ) (β : DolbeaultFibre E q ℂ) :
    alternatizeUncurryFin ((c1 + c2).smulRight β) =
      alternatizeUncurryFin (c1.smulRight β) + alternatizeUncurryFin (c2.smulRight β) := by
  ext v
  simp [alternatizeUncurryFin_apply, Finset.sum_add_distrib, add_smul]

omit [FiniteDimensional ℂ E] in
/-- F5 helper: `alternatizeUncurryFin` of `smulRight` is homogeneous in the functional. -/
private theorem alt_smulRight_smul_left {q : ℕ} (a : ℂ) (c : Conj E →L[ℂ] ℂ)
    (β : DolbeaultFibre E q ℂ) :
    alternatizeUncurryFin ((a • c).smulRight β) = a • alternatizeUncurryFin (c.smulRight β) := by
  ext v
  simp [alternatizeUncurryFin_apply, Finset.mul_sum, mul_left_comm, mul_assoc]

omit [FiniteDimensional ℂ E] in
/-- F5 helper: `alternatizeUncurryFin` of `smulRight` is additive in the form. -/
private theorem alt_smulRight_add_right {q : ℕ} (c : Conj E →L[ℂ] ℂ)
    (β1 β2 : DolbeaultFibre E q ℂ) :
    alternatizeUncurryFin (c.smulRight (β1 + β2)) =
      alternatizeUncurryFin (c.smulRight β1) + alternatizeUncurryFin (c.smulRight β2) := by
  ext v
  simp [alternatizeUncurryFin_apply, Finset.sum_add_distrib, smul_add]

omit [FiniteDimensional ℂ E] in
/-- F5 helper: `alternatizeUncurryFin` of `smulRight` is homogeneous in the form. -/
private theorem alt_smulRight_smul_right {q : ℕ} (a : ℂ) (c : Conj E →L[ℂ] ℂ)
    (β : DolbeaultFibre E q ℂ) :
    alternatizeUncurryFin (c.smulRight (a • β)) = a • alternatizeUncurryFin (c.smulRight β) := by
  ext v
  simp [alternatizeUncurryFin_apply, Finset.mul_sum, mul_left_comm]

omit [FiniteDimensional ℂ E] in
/-- F5 helper: `alternatizeUncurryFin` of `smulRight` vanishes for the zero functional. -/
private theorem alt_smulRight_zero_left {q : ℕ} (β : DolbeaultFibre E q ℂ) :
    alternatizeUncurryFin ((0 : Conj E →L[ℂ] ℂ).smulRight β) = 0 := by
  ext v
  simp [alternatizeUncurryFin_apply]

omit [FiniteDimensional ℂ E] in
/-- F5 helper: `alternatizeUncurryFin` of `smulRight` vanishes for the zero form. -/
private theorem alt_smulRight_zero_right {q : ℕ} (c : Conj E →L[ℂ] ℂ) :
    alternatizeUncurryFin (c.smulRight (0 : DolbeaultFibre E q ℂ)) = 0 := by
  ext v
  simp [alternatizeUncurryFin_apply]

omit [FiniteDimensional ℂ E] in
/-- F5 helper: a product of a `1`-vector and a `q`-vector lies in degree `q + 1`. -/
private theorem mul_mem_succ {q : ℕ} (a : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E)))
    (b : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    (a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) * b ∈
      ⋀[ℂ]^(q + 1) (Module.Dual ℂ (Conj E)) := by
  have := SetLike.mul_mem_graded a.2 b.2
  rwa [Nat.add_comm] at this

omit [FiniteDimensional ℂ E] in
/-- F5 helper: the product `a * 0` as an element of `⋀^(q+1)` is zero. -/
private theorem mk_zero_right {q : ℕ} (a : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E))) :
    (⟨(a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
      ((0 : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))),
      mul_mem_succ a 0⟩ : ⋀[ℂ]^(q + 1) (Module.Dual ℂ (Conj E))) = 0 :=
  Subtype.ext (mul_zero _)

omit [FiniteDimensional ℂ E] in
/-- F5 helper: the product `0 * b` as an element of `⋀^(q+1)` is zero. -/
private theorem mk_zero_left {q : ℕ} (b : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    (⟨((0 : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E))) : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
      (b : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))), mul_mem_succ 0 b⟩ :
        ⋀[ℂ]^(q + 1) (Module.Dual ℂ (Conj E))) = 0 :=
  Subtype.ext (zero_mul _)

omit [FiniteDimensional ℂ E] in
/-- F5 helper: additivity of the product in the second factor. -/
private theorem mk_add_right {q : ℕ} (a : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E)))
    (b1 b2 : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    (⟨(a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
      ((b1 + b2 : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))),
      mul_mem_succ a (b1 + b2)⟩ : ⋀[ℂ]^(q + 1) (Module.Dual ℂ (Conj E))) =
    ⟨(a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) * b1, mul_mem_succ a b1⟩ +
      ⟨(a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) * b2, mul_mem_succ a b2⟩ :=
  Subtype.ext (mul_add _ _ _)

omit [FiniteDimensional ℂ E] in
/-- F5 helper: additivity of the product in the first factor. -/
private theorem mk_add_left {q : ℕ} (a1 a2 : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E)))
    (b : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    (⟨((a1 + a2 : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E))) : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
      (b : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))), mul_mem_succ (a1 + a2) b⟩ :
        ⋀[ℂ]^(q + 1) (Module.Dual ℂ (Conj E))) =
    ⟨(a1 : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) * b, mul_mem_succ a1 b⟩ +
      ⟨(a2 : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) * b, mul_mem_succ a2 b⟩ :=
  Subtype.ext (add_mul _ _ _)

omit [FiniteDimensional ℂ E] in
/-- F5 helper: homogeneity of the product in the second factor. -/
private theorem mk_smul_right {q : ℕ} (c : ℂ) (a : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E)))
    (b : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    (⟨(a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
      ((c • b : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))),
      mul_mem_succ a (c • b)⟩ : ⋀[ℂ]^(q + 1) (Module.Dual ℂ (Conj E))) =
    c • ⟨(a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) * b, mul_mem_succ a b⟩ :=
  Subtype.ext (mul_smul_comm _ _ _)

omit [FiniteDimensional ℂ E] in
/-- F5 helper: homogeneity of the product in the first factor. -/
private theorem mk_smul_left {q : ℕ} (c : ℂ) (a : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E)))
    (b : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    (⟨((c • a : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E))) : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
      (b : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))), mul_mem_succ (c • a) b⟩ :
        ⋀[ℂ]^(q + 1) (Module.Dual ℂ (Conj E))) =
    c • ⟨(a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) * b, mul_mem_succ a b⟩ :=
  Subtype.ext (smul_mul_assoc _ _ _)

/-- F5 helper: the Laplace formula on `⋀^1 × ⋀^q`, by bilinearity from `laplace_gen`. -/
private theorem laplace_aux {q : ℕ} (a : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E)))
    (b : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    extToFibre E (q + 1) ⟨(a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) * b, mul_mem_succ a b⟩ =
      alternatizeUncurryFin (((ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ)
        (0 : Fin 1)).symm (extToFibre E 1 a)).smulRight (extToFibre E q b)) := by
  have ha : a ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ 1
      (M := Module.Dual ℂ (Conj E)))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  have hb : b ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ q
      (M := Module.Dual ℂ (Conj E)))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      obtain ⟨f, rfl⟩ : ∃ f, u = ![f] := ⟨u 0, by ext i; fin_cases i; rfl⟩
      have : (⟨(exteriorPower.ιMulti ℂ 1 ![f] : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
          (exteriorPower.ιMulti ℂ q w : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))),
          mul_mem_succ _ _⟩ : ⋀[ℂ]^(q + 1) (Module.Dual ℂ (Conj E))) =
          exteriorPower.ιMulti ℂ (q + 1) (Matrix.vecCons f w) :=
        Subtype.ext (by
          simp only [exteriorPower.ιMulti_apply_coe]
          exact ιMulti_one_mul_ιMulti f w)
      rw [this, laplace_gen]
    | zero =>
      rw [mk_zero_right, _root_.map_zero, _root_.map_zero, alt_smulRight_zero_right]
    | add y z _ _ hy hz =>
      rw [mk_add_right, _root_.map_add, hy, hz, _root_.map_add, alt_smulRight_add_right]
    | smul c y _ hy =>
      rw [mk_smul_right, _root_.map_smul, hy, _root_.map_smul, alt_smulRight_smul_right]
  | zero =>
    rw [mk_zero_left, _root_.map_zero, _root_.map_zero, _root_.map_zero, alt_smulRight_zero_left]
  | add x y _ _ hx hy =>
    rw [mk_add_left, _root_.map_add, hx, hy, _root_.map_add, _root_.map_add,
      alt_smulRight_add_left]
  | smul c x _ hx =>
    rw [mk_smul_left, _root_.map_smul, hx, _root_.map_smul, _root_.map_smul,
      alt_smulRight_smul_left]

/-- **F5.a (Laplace formula).** For a `1`-form `φ` and a `q`-form `β`,
`φ ∧ β = alternatizeUncurryFin (v ↦ φ(v) • β)`, i.e.
`(φ ∧ β)(v₀, …, v_q) = Σ_i (-1)^i φ(v_i) β(…, v̂_i, …)`: the normalization of ∂̄ (F3). From
expansion of the determinant along the first row (`Matrix.det_succ_row_zero`). -/
theorem ofDeg_one_mul {q : ℕ} (φ : DolbeaultFibre E 1 ℂ) (β : DolbeaultFibre E q ℂ) :
    (ofDeg 1 φ * ofDeg q β : TotFibre E) =
      ofDeg (q + 1) (alternatizeUncurryFin
        (((ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1)).symm φ).smulRight
          β)) := by
  rw [ofDeg_eq_extEquivTotFibre 1 φ, ofDeg_eq_extEquivTotFibre q β, ← extEquivTotFibre_mul]
  have h := extEquivTotFibre_of_mem (E := E)
    ⟨(((extEquivFibre E 1).symm φ : ⋀[ℂ]^1 (Module.Dual ℂ (Conj E))) :
      ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) *
      (((extEquivFibre E q).symm β : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
        ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))),
    mul_mem_succ ((extEquivFibre E 1).symm φ) ((extEquivFibre E q).symm β)⟩
  refine h.trans ?_
  rw [laplace_aux]
  have h1 : extToFibre E 1 ((extEquivFibre E 1).symm φ) = φ :=
    (extEquivFibre E 1).apply_symm_apply φ
  have h2 : extToFibre E q ((extEquivFibre E q).symm β) = β :=
    (extEquivFibre E q).apply_symm_apply β
  rw [h1, h2]

/-! ## Continuity of the product -/

variable (E) in
/-- F5: the product as a `ℂ`-bilinear map. -/
def mulL : TotFibre E →ₗ[ℂ] TotFibre E →ₗ[ℂ] TotFibre E :=
  LinearMap.mk₂ ℂ (· * ·) add_mul (fun c x y => smul_mul_assoc c x y) mul_add
    (fun c x y => mul_smul_comm c x y)

variable (E) in
/-- **F5.** The product as a continuous bilinear map (finite dimension); used for smoothness of
products of forms. -/
def mulCLM : TotFibre E →L[ℂ] TotFibre E →L[ℂ] TotFibre E :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := TotFibre E) (F' := TotFibre E)).toLinearMap
      ∘ₗ mulL E)

/-- F5: `mulCLM` is the product. -/
@[simp] theorem mulCLM_apply (x y : TotFibre E) : mulCLM E x y = x * y := rfl

end TotFibre

end Cohesive
