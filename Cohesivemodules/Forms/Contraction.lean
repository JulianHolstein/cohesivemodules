import Cohesivemodules.Forms.Dbar
import Mathlib.Analysis.Normed.Module.Alternating.Curry

set_option linter.style.header false

/-!
# Z4.d: contraction of Dolbeault forms with a vector, and `∂̄`

Blueprint item Z4.d (§11, v1.14; audit of `blueprint/blueprint-dg.md`, items A1–A5, B1, B4, B5,
simplification S1). On the fibre `Λ^{0,q}(E; F) = Conj E [⋀^Fin q]→L[ℂ] F` (F2) the contraction
with `v ∈ Ē` is Mathlib's `curryLeft`: `(ctr v a)(w) = a(v, w)`.
* `ctr v`: the contraction as a continuous `ℂ`-linear map `Λ^{0,q+1} → Λ^{0,q}`.
* `ctr_ctr_self`, `ctr_ctr_comm` (A2), `eq_zero_of_ctr_basis` (A5: contractions with a basis
  detect zero).
* `dbarPart_comp_clm` (B1): `D″` commutes with continuous `ℂ`-linear maps of the fibre.
* `ctr_dbar` (B4): `ι_v ∂̄ω = D″_v ω − ∂̄(ι_v ω)`; `ctr_dbar_zero`: in degree 0, `ι_v ∂̄ω = D″_v ω`.
* `InvolvesOnly b k a` (blueprint-dg D4): `a` involves only `dz̄_0, …, dz̄_{k−1}` of the basis `b`.
* `dbarPart_eq_zero_of_dbar_eq_zero` (B5): closed forms involving only the first `k` directions
  are holomorphic (`D″_{b j} ω = 0`) in the directions `j ≥ k`.

## Deviations
* blueprint-dg works on `Fin n → ℂ` with real alternating maps and a type predicate; here the
  fibre is the frozen `DolbeaultFibre` (type (0,q) built in) on any finite-dimensional `E`, with
  a basis `b` of `Ē` in place of the coordinate vectors, and ∂̄ is the frozen F3 `dbar`
  (audit A2, A3, S1). B4 holds for every `v ∈ Ē`; in degree 0 it has no `∂̄(ι_v ω)` term
  (audit B.2).
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap Conj Filter Topology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {q : ℕ}

/-- **Z4.d.** Contraction with `v ∈ Ē`: `(ctr v a)(w₀, …, w_{q−1}) = a(v, w₀, …, w_{q−1})`
(Mathlib's `curryLeft`), a continuous `ℂ`-linear map `Λ^{0,q+1}(E; F) → Λ^{0,q}(E; F)`. -/
def ctr (v : Conj E) : DolbeaultFibre E (q + 1) F →L[ℂ] DolbeaultFibre E q F :=
  ContinuousLinearMap.apply ℂ (DolbeaultFibre E q F) v ∘L
    (curryLeftLI (𝕜 := ℂ) (E := Conj E) (F := F) (n := q)).toContinuousLinearMap

/-- Z4.d: `ctr v a = a.curryLeft v` (rfl). -/
@[simp] theorem ctr_apply (v : Conj E) (a : DolbeaultFibre E (q + 1) F) :
    ctr v a = a.curryLeft v := rfl

/-- Z4.d: `(ctr v a) w = a (v, w)`. -/
theorem ctr_apply_apply (v : Conj E) (a : DolbeaultFibre E (q + 1) F) (w : Fin q → Conj E) :
    ctr v a w = a (Matrix.vecCons v w) := rfl

/-- **Z4.d (A2).** Contracting twice with the same vector gives zero. -/
theorem ctr_ctr_self (v : Conj E) (a : DolbeaultFibre E (q + 2) F) : ctr v (ctr v a) = 0 :=
  curryLeft_same a v

/-- **Z4.d (A2).** Contractions anticommute: `ι_v ι_w = −ι_w ι_v`. -/
theorem ctr_ctr_comm (v w : Conj E) (a : DolbeaultFibre E (q + 2) F) :
    ctr v (ctr w a) = -ctr w (ctr v a) := by
  ext u
  simp only [ctr_apply_apply, ContinuousAlternatingMap.neg_apply]
  have h : a (Matrix.vecCons v (Matrix.vecCons w u) ∘ Equiv.swap (0 : Fin (q + 2)) 1) =
      -a (Matrix.vecCons v (Matrix.vecCons w u)) :=
    a.map_swap (Matrix.vecCons v (Matrix.vecCons w u)) (i := 0) (j := 1) (by simp)
  rw [← h]
  congr 1
  ext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
  · simp [Equiv.swap_apply_left]
  · simp [Equiv.swap_apply_right]
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)]
    · simp
    · exact Fin.succ_succ_ne_one k

/-- **Z4.d (A5).** In degree `q + 1 ≥ 1`, a form whose contractions with all vectors of a basis
`b` of `Ē` vanish is zero (`v ↦ ι_v a` is `ℂ`-linear on `Ē`). -/
theorem eq_zero_of_ctr_basis {ι : Type} (b : Module.Basis ι ℂ (Conj E))
    {a : DolbeaultFibre E (q + 1) F} (h : ∀ i, ctr (b i) a = 0) : a = 0 := by
  have h0 : (a.curryLeft : Conj E →ₗ[ℂ] (Conj E [⋀^Fin q]→L[ℂ] F)) = 0 := by
    apply b.ext
    intro i
    exact h i
  ext v
  have := congrArg (fun f => f (Fin.tail v)) (LinearMap.congr_fun h0 (v 0))
  simp only [ContinuousLinearMap.coe_coe, ContinuousAlternatingMap.curryLeft_apply_apply] at this
  have e : Matrix.vecCons (v 0) (Fin.tail v) = v := Fin.cons_self_tail v
  rw [e] at this
  simpa using this

/-- **Z4.d (B1).** `D″` commutes with continuous `ℂ`-linear maps of the fibre:
`D″(L ∘ ω)(z) = L ∘ D″ω(z)` where `ω` is differentiable at `z` (`antiPart_comp`). -/
theorem dbarPart_comp_clm {p : ℕ} {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℂ F']
    (L : DolbeaultFibre E q F →L[ℂ] DolbeaultFibre E p F') {ω : E → DolbeaultFibre E q F} {z : E}
    (hω : DifferentiableAt ℝ ω z) :
    dbarPart (fun y => L (ω y)) z = L.comp (dbarPart ω z) := by
  have : (fun y => L (ω y)) = (L.restrictScalars ℝ) ∘ ω := rfl
  unfold dbarPart
  rw [this, fderiv_comp z (L.restrictScalars ℝ).differentiableAt hω,
    ContinuousLinearMap.fderiv, antiPart_comp]

/-- **Z4.d (B4).** [Hörmander, proof of Thm 2.3.3]. Contraction of `∂̄`: for `ω` of degree
`q + 1` differentiable at `z` and `v ∈ Ē`,
`ι_v (∂̄ω)(z) = D″ω(z)(v) − ∂̄(ι_v ω)(z)`. (From `alternatizeUncurryFin_apply`: the term `i = 0`
gives `D″_v ω`, the others `−∂̄(ι_v ω)` by B1.) -/
theorem ctr_dbar {ω : E → DolbeaultFibre E (q + 1) F} {z : E} (hω : DifferentiableAt ℝ ω z)
    (v : Conj E) :
    ctr v (dbar ω z) = dbarPart ω z v - dbar (fun y => ctr v (ω y)) z := by
  ext w
  rw [ctr_apply_apply, dbar, alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  have h1 : dbar (fun y => ctr v (ω y)) z = alternatizeUncurryFin
      ((ctr v).comp (dbarPart ω z)) := by
    rw [dbar, dbarPart_comp_clm (ctr v) hω]
  rw [h1, ContinuousAlternatingMap.sub_apply, alternatizeUncurryFin_apply]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, Fin.val_succ,
    Fin.removeNth_zero,Matrix.cons_val_succ, pow_succ, mul_neg, mul_one,
    neg_smul, Finset.sum_neg_distrib, ContinuousLinearMap.comp_apply]
  rw [sub_eq_add_neg]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  have : Fin.removeNth j.succ (Matrix.vecCons v w) = Matrix.vecCons v (Fin.removeNth j w) := by
    exact Fin.cons_comp_succ_succAbove v w j
  rw [this]
  rfl

/-- **Z4.d (B4, degree 0).** For a function `ω` (degree 0), `ι_v (∂̄ω)(z) = D″ω(z)(v)`. -/
theorem ctr_dbar_zero (ω : E → DolbeaultFibre E 0 F) (z : E) (v : Conj E) :
    ctr v (dbar ω z) = dbarPart ω z v := by
  ext w
  rw [ctr_apply_apply, dbar, alternatizeUncurryFin_apply, Fin.sum_univ_one]
  have : Fin.removeNth 0 (Matrix.vecCons v w) = w := Subsingleton.elim _ _
  simp [this]

/-- **Z4.d (blueprint-dg D4).** `a` involves only `dz̄_0, …, dz̄_{k−1}` relative to the basis `b`
of `Ē`: its contractions with `b j` vanish for every `j ≥ k`. -/
def InvolvesOnly {n : ℕ} (b : Module.Basis (Fin n) ℂ (Conj E)) (k : ℕ)
    (a : DolbeaultFibre E (q + 1) F) : Prop :=
  ∀ j : Fin n, k ≤ (j : ℕ) → ctr (b j) a = 0

/-- Z4.d: every form involves only `dz̄_0, …, dz̄_{n−1}` (vacuous). -/
theorem involvesOnly_top {n : ℕ} (b : Module.Basis (Fin n) ℂ (Conj E))
    (a : DolbeaultFibre E (q + 1) F) : InvolvesOnly b n a :=
  fun j hj => absurd j.2 (not_lt.2 hj)

/-- Z4.d (base case of the induction): a form involving none of the `dz̄_j` is zero (A5). -/
theorem InvolvesOnly.eq_zero {n : ℕ} {b : Module.Basis (Fin n) ℂ (Conj E)}
    {a : DolbeaultFibre E (q + 1) F} (h : InvolvesOnly b 0 a) : a = 0 :=
  eq_zero_of_ctr_basis b fun j => h j (Nat.zero_le _)

/-- Z4.d (induction step 1): if `a` (degree `q + 2`) involves only `dz̄_0, …, dz̄_j`, then
`ι_{b j} a` involves only `dz̄_0, …, dz̄_{j−1}` (A2). -/
theorem InvolvesOnly.ctr_basis {n : ℕ} {b : Module.Basis (Fin n) ℂ (Conj E)} (j : Fin n)
    {a : DolbeaultFibre E (q + 2) F} (h : InvolvesOnly b ((j : ℕ) + 1) a) :
    InvolvesOnly b j (ctr (b j) a) := by
  intro j' hj'
  rcases Nat.eq_or_lt_of_le hj' with h' | h'
  · have : j' = j := Fin.ext h'.symm
    subst this
    exact ctr_ctr_self _ a
  · rw [ctr_ctr_comm, h j' (by omega), _root_.map_zero, neg_zero]

/-- **Z4.d (B5).** [Hörmander, proof of Thm 2.3.3]. On an open `U`, let `ω` (degree `q + 1`) be
differentiable, involve only `dz̄_0, …, dz̄_{k−1}`, and satisfy `∂̄ω = 0`. Then `ω` is
holomorphic in the directions `b j`, `j ≥ k`: `D″ω(z)(b j) = 0` on `U` (B4 with
`ι_{b j} ω ≡ 0` near `z`). -/
theorem dbarPart_eq_zero_of_dbar_eq_zero {n : ℕ} {b : Module.Basis (Fin n) ℂ (Conj E)}
    {U : Set E} (hU : IsOpen U) {ω : E → DolbeaultFibre E (q + 1) F}
    (hω : ∀ z ∈ U, DifferentiableAt ℝ ω z) {k : ℕ} (hk : ∀ z ∈ U, InvolvesOnly b k (ω z))
    (hc : ∀ z ∈ U, dbar ω z = 0) (j : Fin n) (hj : k ≤ (j : ℕ)) :
    ∀ z ∈ U, dbarPart ω z (b j) = 0 := by
  intro z hz
  have hev : (fun y => ctr (b j) (ω y)) =ᶠ[𝓝 z] fun _ => (0 : DolbeaultFibre E q F) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact hk y hy j hj
  have h0 : dbar (fun _ : E => (0 : DolbeaultFibre E q F)) z = 0 := by
    have e : dbarPart (fun _ : E => (0 : DolbeaultFibre E q F)) z = 0 := by
      unfold dbarPart
      rw [fderiv_fun_const]
      ext v
      simp
    rw [dbar, e]
    exact map_zero _
  have := ctr_dbar (hω z hz) (b j)
  rw [hc z hz, dbar_congr hev, h0] at this
  simpa using this.symm

end Cohesive
