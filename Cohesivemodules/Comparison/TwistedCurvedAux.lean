import Cohesivemodules.Comparison.TwistedModel

set_option linter.style.header false

/-!
# Z3.t, auxiliary algebra for the curved model (blueprint-tw G′ (g), (h))

Helpers for `TwistedCurvedModel.lean`, split off for file size:
* `degComp n`: the component of total degree `n` of an element of `Tot(𝒜, Q)`, with
  `degComp_mem`, `degComp_self`, `degComp_totMapAlong`, and `eq_of_degComp` (elements are
  determined by their components);
* graded-commutative algebra: `sigma_mul_deg_one`, `sq_eq_zero_deg_one`, `compat_alg`,
  `d_inv_aux` (`d(v) = -v·d(w)·v` for inverse elements `v w` of degree 0).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum
open PreResolvingData (topO)

section DegComp

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- Z3.t: the bi-additive map `(a, y) ↦ a_{n-p} ⊗ y` for `y ∈ Q^p`. -/
def degAuxP (n p : ℤ) : A →+ Q p →+ Tot 𝒜 Q :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun y => Tot.tmul 𝒜 Q (GCDga.proj 𝒜 (n - p) a) (DirectSum.of Q p y))
      (fun y y' => by rw [map_add, Tot.tmul_add]))
    (fun a b => AddMonoidHom.ext fun y => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, Tot.add_tmul])

/-- Z3.t: the bi-additive map `(a, e) ↦ Σ_p a_{n-p} ⊗ e_p`. -/
def degAux (n : ℤ) : A →+ (⨁ p, Q p) →+ Tot 𝒜 Q :=
  (DirectSum.toAddMonoid (fun p => (degAuxP (𝒜 := 𝒜) (Q := Q) n p).flip)).flip

/-- Z3.t: `degAux` on `a`, `of p y`. -/
theorem degAux_of (n : ℤ) (a : A) (p : ℤ) (y : Q p) :
    degAux (𝒜 := 𝒜) n a (DirectSum.of Q p y) =
      Tot.tmul 𝒜 Q (GCDga.proj 𝒜 (n - p) a) (DirectSum.of Q p y) := by
  simp only [degAux, AddMonoidHom.flip_apply, DirectSum.toAddMonoid_of]
  rfl

/-- Z3.t: `degAux` is `A⁰`-balanced. -/
theorem degAux_balanced (n : ℤ) (r : 𝒜 0) (a : A) (e : ⨁ p, Q p) :
    degAux (𝒜 := 𝒜) n (r • a) e = degAux n a (r • e) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | of p y =>
    have h1 : r • DirectSum.of Q p y = DirectSum.of Q p (r • y) :=
      (map_smul (DirectSum.lof (𝒜 0) ℤ Q p) r y).symm
    rw [h1, degAux_of, degAux_of, map_smul (GCDga.proj 𝒜 (n - p)) r a]
    have h := TensorProduct.smul_tmul (R := 𝒜 0) r (GCDga.proj 𝒜 (n - p) a)
      (DirectSum.of Q p y)
    rw [h1] at h
    exact h
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]

variable (𝒜 Q) in
/-- Z3.t: the component of total degree `n`, `a ⊗ e ↦ Σ_p a_{n-p} ⊗ e_p`. -/
def degComp (n : ℤ) : Tot 𝒜 Q →+ Tot 𝒜 Q :=
  TensorProduct.liftAddHom (R := 𝒜 0) (degAux n) (degAux_balanced n)

/-- Z3.t: `degComp` on `a ⊗ of p y`. -/
theorem degComp_tmul_of (n : ℤ) (a : A) (p : ℤ) (y : Q p) :
    degComp 𝒜 Q n (Tot.tmul 𝒜 Q a (DirectSum.of Q p y)) =
      Tot.tmul 𝒜 Q (GCDga.proj 𝒜 (n - p) a) (DirectSum.of Q p y) :=
  degAux_of n a p y

/-- Z3.t: `degComp n x` has total degree `n`. -/
theorem degComp_mem (n : ℤ) (x : Tot 𝒜 Q) : degComp 𝒜 Q n x ∈ totDeg 𝒜 Q n := by
  induction x using Tot.induction_on with
  | ht a e =>
    induction e using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero]; exact zero_mem _
    | of p y =>
      rw [degComp_tmul_of]
      have := tmul_mem_totDeg (𝒜 := 𝒜) (Q := Q) (GCDga.proj_mem 𝒜 (n - p) a) y
      rwa [sub_add_cancel, DirectSum.lof_eq_of] at this
    | add x y hx hy => rw [Tot.tmul_add, map_add]; exact add_mem hx hy
  | hadd x y hx hy => rw [map_add]; exact add_mem hx hy

/-- Z3.t: `degComp` commutes with `totMapAlong`. -/
theorem degComp_totMapAlong (g : DgaHom 𝒜 ℬ) {Q' : ℤ → Type}
    [∀ p, AddCommGroup (Q' p)] [∀ p, Module (ℬ 0) (Q' p)] (u : ∀ p, Q p →+ Q' p)
    (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = g.f0 r • u p x) (n : ℤ) (x : Tot 𝒜 Q) :
    degComp ℬ Q' n (totMapAlong g u hu x) = totMapAlong g u hu (degComp 𝒜 Q n x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    induction e using DirectSum.induction_on with
    | zero => simp only [Tot.tmul_zero, map_zero]
    | of p y =>
      rw [totMapAlong_tmul, famMap_of, degComp_tmul_of, degComp_tmul_of,
        totMapAlong_tmul, famMap_of, g.map_proj]
    | add x y hx hy => rw [Tot.tmul_add]; simp only [map_add, hx, hy]
  | hadd x y hx hy => simp only [map_add, hx, hy]

/-- Z3.t: finite support and reconstruction of the components. -/
def DegG (x : Tot 𝒜 Q) : Prop :=
  ∃ s : Finset ℤ, (∀ n, n ∉ s → degComp 𝒜 Q n x = 0) ∧ x = ∑ n ∈ s, degComp 𝒜 Q n x

/-- Z3.t: `DegG` is closed under addition. -/
theorem DegG.add {x y : Tot 𝒜 Q} (hx : DegG x) (hy : DegG y) : DegG (x + y) := by
  classical
  obtain ⟨s, hs0, hs⟩ := hx
  obtain ⟨t, ht0, ht⟩ := hy
  refine ⟨s ∪ t, fun n hn => ?_, ?_⟩
  · rw [map_add, hs0 n (fun h => hn (Finset.mem_union_left _ h)),
      ht0 n (fun h => hn (Finset.mem_union_right _ h)), add_zero]
  · simp only [map_add, Finset.sum_add_distrib]
    have e1 : ∑ n ∈ s ∪ t, degComp 𝒜 Q n x = x := by
      rw [← Finset.sum_subset (Finset.subset_union_left (s₂ := t)) (fun n _ hn => hs0 n hn)]
      exact hs.symm
    have e2 : ∑ n ∈ s ∪ t, degComp 𝒜 Q n y = y := by
      rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := s)) (fun n _ hn => ht0 n hn)]
      exact ht.symm
    rw [e1, e2]

/-- Z3.t: `DegG` for `a ⊗ of p y`. -/
theorem degG_tmul_of (a : A) (p : ℤ) (y : Q p) :
    DegG (Tot.tmul 𝒜 Q a (DirectSum.of Q p y)) := by
  classical
  refine ⟨(Finset.Icc (0 : ℤ) (GCDga.N 𝒜)).image (· + p), fun n hn => ?_, ?_⟩
  · rw [degComp_tmul_of, GCDga.proj_eq_zero_of_not_mem 𝒜 ?_ a, Tot.zero_tmul]
    intro hmem
    exact hn (Finset.mem_image.2 ⟨n - p, hmem, sub_add_cancel n p⟩)
  · simp only [degComp_tmul_of]
    rw [Finset.sum_image (fun x _ y _ hxy => add_right_cancel hxy)]
    simp only [add_sub_cancel_right]
    exact Tot.tmul_eq_sum a _

/-- Z3.t: `DegG` for `a ⊗ e`. -/
theorem degG_tmul (a : A) (e : ⨁ p, Q p) : DegG (Tot.tmul 𝒜 Q a e) := by
  induction e using DirectSum.induction_on with
  | zero => exact ⟨∅, fun n _ => by rw [Tot.tmul_zero, map_zero], by simp⟩
  | of p y => exact degG_tmul_of a p y
  | add x y hx hy => rw [Tot.tmul_add]; exact hx.add hy

/-- Z3.t: an element of the total module is determined by its components `degComp n`. -/
theorem eq_of_degComp (x y : Tot 𝒜 Q)
    (h : ∀ n, degComp 𝒜 Q n x = degComp 𝒜 Q n y) : x = y := by
  have hG : ∀ z : Tot 𝒜 Q, DegG z := fun z => by
    induction z using Tot.induction_on with
    | ht a e => exact degG_tmul a e
    | hadd x y hx hy => exact hx.add hy
  obtain ⟨s, -, hs⟩ := hG (x - y)
  have : x - y = 0 := by
    rw [hs]
    exact Finset.sum_eq_zero fun n _ => by rw [map_sub, h n, sub_self]
  exact sub_eq_zero.1 this

/-- Z3.t: `degComp` is `k`-linear. -/
theorem degComp_smul_k (n : ℤ) (r : k) (x : Tot 𝒜 Q) :
    degComp 𝒜 Q n (r • x) = r • degComp 𝒜 Q n x := by
  induction x using Tot.induction_on with
  | ht a e =>
    induction e using DirectSum.induction_on with
    | zero => simp only [Tot.tmul_zero, smul_zero, map_zero]
    | of p y =>
      rw [Tot.smul_tmul_k, degComp_tmul_of, degComp_tmul_of, GCDga.proj_smul, Tot.smul_tmul_k]
    | add x y hx hy => rw [Tot.tmul_add, smul_add, map_add, map_add, hx, hy, smul_add]
  | hadd x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- Z3.t: `degComp m` is the identity on elements of total degree `m`. -/
theorem degComp_self {m : ℤ} {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) :
    degComp 𝒜 Q m x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change degComp 𝒜 Q (q + p) (Tot.tmul 𝒜 Q a (DirectSum.lof (𝒜 0) ℤ Q p e)) = _
    rw [DirectSum.lof_eq_of, degComp_tmul_of, add_sub_cancel_right, GCDga.proj_of_mem 𝒜 ha,
      if_pos rfl]
    rfl
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul r x _ hx => rw [degComp_smul_k, hx]

/-- Z3.t: `σ(a)·β = β·a` for `β` of degree `1` (graded commutativity). -/
theorem sigma_mul_deg_one {β : A} (hβ : β ∈ 𝒜 1) (a : A) :
    GCDga.sigma 𝒜 a * β = β * a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, add_mul, hx, hy, mul_add]
  | homogeneous x =>
    rw [GCDga.sigma_of_mem 𝒜 x.2, smul_mul_assoc, GCDga.gcomm hβ x.2, one_mul]

/-- Z3.t: `β² = 0` for `β` of degree `1` (graded commutativity, `2` invertible). -/
theorem sq_eq_zero_deg_one {β : A} (hβ : β ∈ 𝒜 1) (h2 : IsUnit (2 : k)) : β * β = 0 := by
  have h := GCDga.gcomm hβ hβ
  rw [show ((1 : ℤ) * 1).negOnePow = -1 by decide, Units.neg_smul, one_smul] at h
  have h' : (2 : k) • (β * β) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  obtain ⟨u, hu⟩ := h2
  have : (↑u⁻¹ * 2 : k) • (β * β) = 0 := by rw [mul_smul, h', smul_zero]
  rwa [← hu, Units.inv_mul, one_smul] at this

/-- Z3.t: the algebra of the compatibility of the local curved connections: if
`d u = -u (b_β - b_α)` for `u ∈ A⁰` then `u (θ E + b_α ⊗ E) = θ (u E) + b_β ⊗ (u E)`. -/
theorem compat_alg (D : GenData 𝒜 Q) (fu : 𝒜 0) (bα bβ : A)
    (hd : GCDga.d (𝒜 := 𝒜) (fu : A) = -((fu : A) * (bβ - bα))) (E : ⨁ p, Q p) :
    (fu : A) • (D.θ E + bα • Tot.tmul 𝒜 Q 1 E) =
      D.θ (fu • E) + bβ • Tot.tmul 𝒜 Q 1 (fu • E) := by
  have h : GCDga.d (𝒜 := 𝒜) (fu : A) + bβ * (fu : A) = (fu : A) * bα := by
    rw [hd, ← GCDga.central 𝒜 fu.2 bβ, mul_sub]
    abel
  rw [D.leibniz, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (GCDga.d (𝒜 := 𝒜) (fu : A)) E,
    Tot.tmul_eq_smul (fu : A) E, smul_add, smul_smul, smul_smul, ← h, add_smul]
  abel

/-- Z3.t: the logarithmic derivative of an inverse: `v w = 1`, `d w = c w` give `d v = -(v c)`
(for `v, w ∈ A⁰`). -/
theorem d_inv_aux {v w : 𝒜 0} (hvw : (v : A) * (w : A) = 1) (c : A)
    (hw : GCDga.d (𝒜 := 𝒜) (w : A) = c * (w : A)) :
    GCDga.d (𝒜 := 𝒜) (v : A) = -((v : A) * c) := by
  have h1 : GCDga.d (𝒜 := 𝒜) (v : A) * (w : A) + (v : A) * (c * (w : A)) = 0 := by
    rw [← hw, ← GCDga.leibniz_zero 𝒜 v.2, hvw, GCDga.d_one]
  have hwv : (w : A) * (v : A) = 1 := (GCDga.central 𝒜 w.2 (v : A)).trans hvw
  have h3 : (GCDga.d (𝒜 := 𝒜) (v : A) * (w : A) + (v : A) * (c * (w : A))) * (v : A) = 0 := by
    rw [h1, zero_mul]
  simp only [add_mul, mul_assoc, hwv, mul_one] at h3
  exact eq_neg_of_add_eq_zero_left h3

end DegComp

end Cohesive
