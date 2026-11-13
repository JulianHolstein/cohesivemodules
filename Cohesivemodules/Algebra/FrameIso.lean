import Cohesivemodules.Algebra.Frame
import Cohesivemodules.Algebra.BaseChange

set_option linter.style.header false

/-!
# Z5.i (algebra part): the complex `W` of a matrix and the isomorphism `M ≅ A ⊗_R W`

Blueprint item Z5.i, E.3–E.4 (`blueprint/blueprint-ll.md` §4 E; §11 v1.15), in a generic
(possibly curved) dga.
* `matComplex R deg f`: for a matrix `f : Fin r → Fin r → R` over a commutative ring with
  `fₖᵢ = 0` unless `deg k = deg i + 1` and `f² = 0`, the complex `W^p = R^{{i | deg i = p}}`,
  `d(w)ₖ = Σᵢ fₖᵢ wᵢ`; bounded, finite free (`isBoundedFGProj_matComplex`).
* `GradedFrame.frameHom`: the degree-`0` map out of a module with a graded frame determined by
  the images `yⱼ` of the frame vectors (`x ↦ Σⱼ xⱼ • yⱼ`); `GradedFrame.hom_ext`: maps of any
  degree agree if they agree on the frame vectors.
* `exists_iso_fromComplex_of_frame` (E.4 in algebraic form): a cohesive `N` with a graded frame
  `ẽ`, connection matrix `ω` (`GradedFrame.mat`), and mutually inverse matrices `G`, `H` of
  forms with the gauge identity `dGᵢⱼ + Σₖ σ(Gₖⱼ) ρ(fᵢₖ) = Σₗ ωₗⱼ Gᵢₗ` is isomorphic in `Ho(P_A)`
  to `A ⊗_R W` (A10) for `W = matComplex R deg f`. The isomorphism is
  `Ψ(1 ⊗ ẽⱼ) = Σᵢ Gᵢⱼ ⊗ wᵢ` with inverse `Φ(1 ⊗ wᵢ) = Σⱼ Hⱼᵢ ⊗ ẽⱼ`.

## Deviations
* Generic in the (possibly curved) dga and in `R`
 (the blueprint works over `𝒜_X(U″)` and `O(U″)`); the analytic
  input (holomorphic `f`, the gauge `G`) is supplied in `Forms/LocalGauge.lean`.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum CategoryTheory

/-! ## The complex of a matrix -/

section MatComplex

variable (R : Type) [CommRing R] {r : ℕ} (deg : Fin r → ℤ)

/-- **Z5.i (E.3).** `R^{{i | deg i = p}}`, the degree-`p` piece of the complex of a matrix. -/
abbrev MatVec (p : ℤ) : Type := {i : Fin r // deg i = p} → R

/-- **Z5.i (E.3).** The differential of the complex of a matrix: `d(w)ₖ = Σᵢ fₖᵢ wᵢ`. -/
def matD (f : Fin r → Fin r → R) (p : ℤ) : MatVec R deg p →ₗ[R] MatVec R deg (p + 1) where
  toFun w k := ∑ i, f k.1 i.1 * w i
  map_add' w w' := by
    funext k
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _

/-- Z5.i: formula for `matD` (rfl). -/
theorem matD_apply (f : Fin r → Fin r → R) (p : ℤ) (w : MatVec R deg p)
    (k : {i : Fin r // deg i = p + 1}) : matD R deg f p w k = ∑ i, f k.1 i.1 * w i := rfl

/-- A sum over a subtype of a function vanishing off the subtype is the full sum. -/
private theorem sum_subtype_eq_sum {M : Type} [AddCommMonoid M] {ι : Type} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] (g : ι → M) (h : ∀ i, ¬ P i → g i = 0) :
    ∑ i : {i // P i}, g i.1 = ∑ i, g i := by
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) g, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => by
    by_cases hP : P i
    · simp only [hP, ite_true]
    · simp only [hP, ite_false, h i hP]

variable {R deg} in
/-- Z5.i: `d² = 0` for the complex of a matrix with `f² = 0` supported in degree `+1`. -/
theorem matD_matD {f : Fin r → Fin r → R} (hdeg : ∀ k i, deg k ≠ deg i + 1 → f k i = 0)
    (hsq : ∀ k i, ∑ l, f k l * f l i = 0) (p : ℤ) (w : MatVec R deg p) :
    matD R deg f (p + 1) (matD R deg f p w) = 0 := by
  funext k
  simp only [matD_apply, Finset.mul_sum, Pi.zero_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : ∀ l : {l : Fin r // deg l = p + 1}, f k.1 l.1 * (f l.1 i.1 * w i) =
      (fun l : Fin r => f k l * f l i.1) l.1 * w i := fun l => by
    simp only [mul_assoc]
  simp only [h1]
  have hz : ∀ l : Fin r, ¬ deg l = p + 1 → f k l * f l i.1 = 0 := fun l hl => by
    rw [hdeg l i.1 (by rw [i.2]; exact hl), mul_zero]
  rw [← Finset.sum_mul, sum_subtype_eq_sum (fun l => deg l = p + 1)
    (fun l : Fin r => f k l * f l i.1) hz, hsq, zero_mul]

/-- **Z5.i (E.3).** The complex of a matrix `f` (with `fₖᵢ = 0` unless `deg k = deg i + 1`, and
`f² = 0`): `W^p = R^{{i | deg i = p}}`, `d(w)ₖ = Σᵢ fₖᵢ wᵢ`. -/
def matComplex (f : Fin r → Fin r → R) (hdeg : ∀ k i, deg k ≠ deg i + 1 → f k i = 0)
    (hsq : ∀ k i, ∑ l, f k l * f l i = 0) : CochainComplex (ModuleCat.{0} R) ℤ :=
  CochainComplex.of (fun p => ModuleCat.of R (MatVec R deg p))
    (fun p => ModuleCat.ofHom (matD R deg f p))
    (fun p => ModuleCat.hom_ext (LinearMap.ext fun w => matD_matD hdeg hsq p w))

variable {R deg}
variable {f : Fin r → Fin r → R} (hdeg : ∀ k i, deg k ≠ deg i + 1 → f k i = 0)
  (hsq : ∀ k i, ∑ l, f k l * f l i = 0)

/-- Z5.i: the differential of `matComplex` is `matD`. -/
theorem dW_matComplex (p : ℤ) (w : (matComplex R deg f hdeg hsq).X p) :
    dW (matComplex R deg f hdeg hsq) p w = matD R deg f p w := by
  unfold dW matComplex
  change ModuleCat.Hom.hom (CochainComplex.of.d (fun p => ModuleCat.of R (MatVec R deg p)) _ p
    (p + 1)) w = _
  rw [CochainComplex.of_d]
  rfl

/-- **Z5.i (E.3).** The complex of a matrix is bounded, with finite free pieces. -/
theorem isBoundedFGProj_matComplex : IsBoundedFGProj R (matComplex R deg f hdeg hsq) := by
  refine ⟨⟨-(∑ i, |deg i|) - 1, (∑ i, |deg i|) + 1, fun p hp => ?_⟩, fun p => ?_, fun p => ?_⟩
  · have hemp : IsEmpty {i : Fin r // deg i = p} := ⟨fun i => by
      have h1 : |deg i.1| ≤ ∑ j, |deg j| :=
        Finset.single_le_sum (f := fun j => |deg j|) (fun j _ => abs_nonneg _) (Finset.mem_univ _)
      have h2 := i.2
      rw [abs_le'] at *
      rcases hp with hp | hp <;> rw [← h2] at hp <;> cases abs_cases (deg i.1) <;> omega⟩
    exact inferInstanceAs (Subsingleton (MatVec R deg p))
  · exact inferInstanceAs (Module.Finite R (MatVec R deg p))
  · exact inferInstanceAs (Module.Projective R (MatVec R deg p))

end MatComplex

/-! ## Maps out of a module with a graded frame -/

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

namespace GradedFrame

variable {r : ℕ} {N N₂ : QuasiCohesive 𝒜} (F : GradedFrame 𝒜 N.Q r)

/-- `x ↦ Σⱼ xⱼ • yⱼ` is `k`-linear. -/
theorem frameMap_smul (y : Fin r → N₂.T) (c : k) (x : N.T) :
    ∑ j, F.coefTot (c • x) j • y j = c • ∑ j, F.coefTot x j • y j := by
  rw [← algebraMap_smul A c x]
  simp only [F.coefTot_smul, mul_smul, ← Finset.smul_sum]
  rw [algebraMap_smul]

/-- The `k`-linear map `x ↦ Σⱼ xⱼ • yⱼ`. -/
def frameMap (y : Fin r → N₂.T) : N.T →ₗ[k] N₂.T where
  toFun x := ∑ j, F.coefTot x j • y j
  map_add' x x' := by
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := F.frameMap_smul y c x

/-- Z5.i: formula for `frameMap` (rfl). -/
theorem frameMap_apply (y : Fin r → N₂.T) (x : N.T) :
    F.frameMap y x = ∑ j, F.coefTot x j • y j := rfl

/-- `frameMap` has degree `0` when `yⱼ` has total degree `deg j`. -/
theorem frameMap_mem (y : Fin r → N₂.T) (hy : ∀ j, y j ∈ totDeg 𝒜 N₂.Q (F.deg j)) :
    F.frameMap y ∈ Hom N N₂ 0 := by
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · rw [frameMap_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    have := smul_mem_totDeg (F.coefTot_mem hx j) (hy j)
    rwa [show m - F.deg j + F.deg j = m + 0 by ring] at this
  · simp only [frameMap_apply, F.coefTot_smul, mul_smul, ← Finset.smul_sum, zero_mul,
      Int.negOnePow_zero, one_smul]

/-- **Z5.i (E.4).** The degree-`0` map out of a module with a graded frame sending the frame vector
`1 ⊗ ẽⱼ` to `yⱼ` (of total degree `deg j`): `x ↦ Σⱼ xⱼ • yⱼ`. -/
def frameHom (y : Fin r → N₂.T) (hy : ∀ j, y j ∈ totDeg 𝒜 N₂.Q (F.deg j)) : Hom N N₂ 0 :=
  ⟨F.frameMap y, F.frameMap_mem y hy⟩

/-- Z5.i: `frameHom` on the frame vectors. -/
theorem frameHom_vec (y : Fin r → N₂.T) (hy : ∀ j, y j ∈ totDeg 𝒜 N₂.Q (F.deg j)) (j : Fin r) :
    (F.frameHom y hy).1 (F.vec j) = y j := by
  change ∑ i, F.coefTot (F.vec j) i • y i = y j
  simp only [F.coefTot_vec, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

/-- **Z5.i (E.4).** Maps of degree `n` out of a module with a graded frame agree if they agree on
the frame vectors. -/
theorem hom_ext {n : ℤ} {φ ψ : N.T →ₗ[k] N₂.T} (hφ : φ ∈ Hom N N₂ n) (hψ : ψ ∈ Hom N N₂ n)
    (h : ∀ j, φ (F.vec j) = ψ (F.vec j)) : φ = ψ := by
  have h1 : ∀ (θ : N.T →ₗ[k] N₂.T), θ ∈ Hom N N₂ n → ∀ (x : N.T) (j : Fin r),
      θ (F.coefTot x j • F.vec j) = GCDga.twist 𝒜 n (F.coefTot x j) • θ (F.vec j) :=
    fun θ hθ x j => by
      have := hom_tmul hθ (F.coefTot x j) (F.basis j)
      rw [vec, Tot.smul_tmul, mul_one]
      exact this
  ext x
  rw [← F.sum_coefTot x, map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [h1 φ hφ, h1 ψ hψ, h j]

end GradedFrame

/-! ## Isomorphisms in `Ho(P_A)` from inverse closed maps -/

/-- Z5.i: mutually inverse closed maps of degree `0` give an isomorphism in `Ho(P_A)`. -/
def hoPIsoOfInverse {M₁ M₂ : CohesiveModule 𝒜} (φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive)
    (ψ : Z0 M₂.toQuasiCohesive M₁.toQuasiCohesive) (h₁ : ∀ x, ψ.1 (φ.1 x) = x)
    (h₂ : ∀ y, φ.1 (ψ.1 y) = y) : HoP.mk M₁ ≅ HoP.mk M₂ where
  hom := Submodule.Quotient.mk φ
  inv := Submodule.Quotient.mk ψ
  hom_inv_id := congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext h₁))
  inv_hom_id := congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext h₂))

/-! ## The isomorphism `N ≅ A ⊗_R W` -/

section FrameIso

variable {R : Type} [CommRing R] {ρ : R →+* 𝒜 0} (hρ : ∀ r, GCDga.d (𝒜 := 𝒜) (ρ r : A) = 0)
  (hc : GCDga.c (𝒜 := 𝒜) = 0) {r : ℕ} {deg : Fin r → ℤ} {f : Fin r → Fin r → R}
  (hdeg : ∀ k i, deg k ≠ deg i + 1 → f k i = 0) (hsq : ∀ k i, ∑ l, f k l * f l i = 0)

/-- **Z5.i (E.4).** The generator `1 ⊗ wᵢ` of `A ⊗_R W` (`W = matComplex`), `wᵢ` the `i`-th unit
vector of `W^{deg i}`; of total degree `deg i`. -/
def matGen (i : Fin r) : Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq)) :=
  fcι ρ (matComplex R deg f hdeg hsq) (p := deg i)
    (show MatVec R deg (deg i) from Pi.single (⟨i, rfl⟩ : {j : Fin r // deg j = deg i}) 1)

/-- Z5.i: `1 ⊗ wᵢ` has total degree `deg i`. -/
theorem matGen_mem (i : Fin r) :
    matGen (ρ := ρ) hdeg hsq i ∈ totDeg 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq)) (deg i) :=
  fcι_mem ρ _ _

/-- `1 ⊗ (unit vector of the index `k`)` in degree `p = deg k` is `matGen k`. -/
private theorem fcι_single_eq {p : ℤ} (k : Fin r) (h : deg k = p) :
    fcι ρ (matComplex R deg f hdeg hsq) (p := p)
      (show MatVec R deg p from Pi.single (⟨k, h⟩ : {j : Fin r // deg j = p}) 1) =
      matGen (ρ := ρ) hdeg hsq k := by
  subst h
  rfl

/-- `1 ⊗ v` is the `ρ`-combination of the `matGen k`, `deg k = p`, with the coordinates of `v`. -/
private theorem fcι_matVec {p : ℤ} (v : MatVec R deg p) :
    fcι ρ (matComplex R deg f hdeg hsq) (p := p) v =
      ∑ k : {k : Fin r // deg k = p}, ((ρ (v k) : 𝒜 0) : A) • matGen (ρ := ρ) hdeg hsq k.1 := by
  have hv : v = ∑ k : {k : Fin r // deg k = p}, v k • (Pi.single k (1 : R) : MatVec R deg p) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  let e : MatVec R deg p →+ Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq)) :=
    AddMonoidHom.mk' (fun w => fcι ρ (matComplex R deg f hdeg hsq) (p := p) w)
      (fun a b => fcι_add (ρ := ρ) (W := matComplex R deg f hdeg hsq) a b)
  have h1 := map_sum e (fun k : {k : Fin r // deg k = p} =>
    v k • (Pi.single k (1 : R) : MatVec R deg p)) Finset.univ
  rw [← hv] at h1
  refine h1.trans (Finset.sum_congr rfl fun k _ => ?_)
  have h2 := fcι_smulR (ρ := ρ) (W := matComplex R deg f hdeg hsq) (p := p) (v k)
    (show MatVec R deg p from Pi.single k 1)
  refine h2.trans ?_
  exact congrArg _ (fcι_single_eq hdeg hsq k.1 k.2)

/-- **Z5.i (E.4).** `𝕏(1 ⊗ wᵢ) = Σₖ ρ(fₖᵢ) • (1 ⊗ wₖ)` in `A ⊗_R W`. -/
theorem fromComplex_X_matGen (i : Fin r) :
    (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc).X (matGen hdeg hsq i) =
      ∑ k, ((ρ (f k i) : 𝒜 0) : A) • matGen (ρ := ρ) hdeg hsq k := by
  have key := fc_extend_fcι (matComplex R deg f hdeg hsq) hρ (p := deg i)
    (show MatVec R deg (deg i) from Pi.single (⟨i, rfl⟩ : {j : Fin r // deg j = deg i}) 1)
  rw [fromComplex_X_apply]
  refine key.trans ?_
  refine (congrArg (fun w : MatVec R deg (deg i + 1) =>
    fcι ρ (matComplex R deg f hdeg hsq) (p := deg i + 1) w)
    (dW_matComplex hdeg hsq (deg i)
      (show MatVec R deg (deg i) from Pi.single (⟨i, rfl⟩ : {j : Fin r // deg j = deg i}) 1))).trans
    ?_
  refine (fcι_matVec hdeg hsq _).trans ?_
  have hm : ∀ k : {k : Fin r // deg k = deg i + 1}, matD R deg f (deg i)
      (show MatVec R deg (deg i) from Pi.single (⟨i, rfl⟩ : {j : Fin r // deg j = deg i}) 1) k =
      f k.1 i := fun k => by
    rw [matD_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
  refine (Finset.sum_congr rfl fun k _ => by rw [hm k]).trans ?_
  refine (sum_subtype_eq_sum (fun k => deg k = deg i + 1)
    (fun k : Fin r => ((ρ (f k i) : 𝒜 0) : A) • matGen (ρ := ρ) hdeg hsq k) fun k hk => ?_).trans
    ?_
  · rw [hdeg k i hk, map_zero]
    simp only [ZeroMemClass.coe_zero, zero_smul]
  · rfl

/-- **Z5.i (E.4).** Maps of degree `n` out of `A ⊗_R W` agree if they agree on the generators
`1 ⊗ wᵢ`. -/
theorem matGen_hom_ext (N : QuasiCohesive 𝒜) {n : ℤ}
    {φ ψ : Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq)) →ₗ[k] N.T}
    (hφ : φ ∈ Hom (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) N n)
    (hψ : ψ ∈ Hom (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) N n)
    (h : ∀ i, φ (matGen hdeg hsq i) = ψ (matGen hdeg hsq i)) : φ = ψ := by
  have h1 : ∀ (c : 𝒜 0) (i : Fin r),
      φ ((c : A) • matGen hdeg hsq i) = ψ ((c : A) • matGen hdeg hsq i) := fun c i => by
    refine (hφ.2 c.2 (matGen hdeg hsq i)).trans (Eq.trans ?_ (hψ.2 c.2 (matGen hdeg hsq i)).symm)
    exact congrArg (fun t => (n * 0).negOnePow • (c : A) • t) (h i)
  refine fc_hom_ext _ hρ hc N hφ hψ (fun p w => ?_)
  rw [fcι_matVec hdeg hsq w, map_sum, map_sum]
  exact Finset.sum_congr rfl fun k _ => h1 _ _

/-- **Z5.i (E.4).** The degree-`0` map out of `A ⊗_R W` sending `1 ⊗ wᵢ` to `zᵢ` (of total degree
`deg i`). -/
theorem exists_matGen_hom (N : QuasiCohesive 𝒜) (z : Fin r → N.T)
    (hz : ∀ i, z i ∈ totDeg 𝒜 N.Q (deg i)) :
    ∃ φ : Hom (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) N 0,
      ∀ i, φ.1 (matGen hdeg hsq i) = z i := by
  let fam : ∀ p, (matComplex R deg f hdeg hsq).X p →ₛₗ[ρ] N.T := fun p =>
    { toFun := fun w => ∑ j : {j : Fin r // deg j = p}, ρ ((show MatVec R deg p from w) j) • z j.1
      map_add' := fun w w' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        change ρ (w j + w' j) • z j.1 = _
        rw [map_add, add_smul]
      map_smul' := fun c w => by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        change ρ (c * w j) • z j.1 = _
        rw [map_mul, mul_smul] }
  have hfam : fam ∈ HomR ρ (matComplex R deg f hdeg hsq) N 0 := fun p w => by
    change ∑ j : {j : Fin r // deg j = p}, ρ ((show MatVec R deg p from w) j) • z j.1 ∈ _
    refine Submodule.sum_mem _ fun j _ => ?_
    have h1 := smul_mem_totDeg (Q := N.Q) (ρ ((show MatVec R deg p from w) j)).2
      (show z j.1 ∈ totDeg 𝒜 N.Q p by have := hz j.1; rwa [j.2] at this)
    rw [zero_add] at h1
    rw [add_zero]
    rwa [← Tot.smul0_eq] at h1
  refine ⟨fcExt _ hρ hc N 0 ⟨fam, hfam⟩, fun i => ?_⟩
  have h3 : fam (deg i) (show MatVec R deg (deg i) from
      Pi.single (⟨i, rfl⟩ : {j : Fin r // deg j = deg i}) 1) = z i := by
    change ∑ j : {j : Fin r // deg j = deg i}, ρ ((show MatVec R deg (deg i) from Pi.single
      (⟨i, rfl⟩ : {j : Fin r // deg j = deg i}) (1 : R)) j) • z j.1 = z i
    simp only [Pi.single_apply, apply_ite ρ, map_one, map_zero, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
  refine Eq.trans ?_ h3
  exact congrArg (fun g => g (deg i)
    (show MatVec R deg (deg i) from Pi.single (⟨i, rfl⟩ : {j : Fin r // deg j = deg i}) 1))
    (fcResP_fcExt (matComplex R deg f hdeg hsq) hρ hc N 0 ⟨fam, hfam⟩)

/-- The image `Σᵢ Gᵢⱼ • (1 ⊗ wᵢ)` of the `j`-th frame vector has total degree `deg j`. -/
private theorem matY_mem (G : Fin r → Fin r → A) (hG : ∀ i j, G i j ∈ 𝒜 (deg j - deg i))
    (j : Fin r) : ∑ i, G i j • matGen (ρ := ρ) hdeg hsq i ∈
      totDeg 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq)) (deg j) := by
  refine Submodule.sum_mem _ fun i _ => ?_
  have := smul_mem_totDeg (hG i j) (matGen_mem (ρ := ρ) hdeg hsq i)
  rwa [sub_add_cancel] at this

/-- The image `Σⱼ Hⱼᵢ • (1 ⊗ ẽⱼ)` of the generator `1 ⊗ wᵢ` has total degree `deg i`. -/
private theorem frameZ_mem {N : QuasiCohesive 𝒜} (F : GradedFrame 𝒜 N.Q r) (hFdeg : F.deg = deg)
    (H : Fin r → Fin r → A) (hH : ∀ i j, H i j ∈ 𝒜 (deg j - deg i)) (i : Fin r) :
    ∑ j, H j i • F.vec j ∈ totDeg 𝒜 N.Q (deg i) := by
  subst hFdeg
  refine Submodule.sum_mem _ fun j _ => ?_
  have := smul_mem_totDeg (hH j i) (F.vec_mem j)
  rwa [sub_add_cancel] at this

/-- `𝕏` of the image `Σᵢ Gᵢⱼ • (1 ⊗ wᵢ)` of a frame vector, in the basis `1 ⊗ wₖ`
(gauge identity applied). -/
private theorem X_matY {N : QuasiCohesive 𝒜} (F : GradedFrame 𝒜 N.Q r)
    (G : Fin r → Fin r → A) (hG : ∀ i j, G i j ∈ 𝒜 (deg j - deg i))
    (hgauge : ∀ i j, GCDga.d (𝒜 := 𝒜) (G i j) +
        ∑ k, GCDga.sigma 𝒜 (G k j) * ((ρ (f i k) : 𝒜 0) : A) =
      ∑ l, F.mat l j * G i l) (j : Fin r) :
    (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc).X
        (∑ i, G i j • matGen (ρ := ρ) hdeg hsq i) =
      ∑ k, (∑ l, F.mat l j * G k l) • matGen (ρ := ρ) hdeg hsq k := by
  change (fcGenData (matComplex R deg f hdeg hsq) hρ).extend
    (∑ i, G i j • matGen (ρ := ρ) hdeg hsq i) = _
  have hX : ∀ i, (fcGenData (matComplex R deg f hdeg hsq) hρ).extend
      (matGen (ρ := ρ) hdeg hsq i) =
      ∑ k, ((ρ (f k i) : 𝒜 0) : A) • matGen (ρ := ρ) hdeg hsq k :=
    fun i => fromComplex_X_matGen hρ hc hdeg hsq i
  have h1 : ∀ i, (fcGenData (matComplex R deg f hdeg hsq) hρ).extend
      (G i j • matGen (ρ := ρ) hdeg hsq i) =
      GCDga.d (𝒜 := 𝒜) (G i j) • matGen (ρ := ρ) hdeg hsq i +
        ∑ k, (GCDga.sigma 𝒜 (G i j) * ((ρ (f k i) : 𝒜 0) : A)) • matGen (ρ := ρ) hdeg hsq k :=
    fun i => by
    rw [GenData.extend_leibniz _ (hG i j), hX i, GCDga.sigma_of_mem 𝒜 (hG i j)]
    congr 1
    simp only [Finset.smul_sum, smul_mul_assoc, smul_assoc, mul_smul]
  rw [map_sum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_add_distrib, Finset.sum_comm]
  have hR : ∀ k, (∑ l, F.mat l j * G k l) • matGen (ρ := ρ) hdeg hsq k =
      GCDga.d (𝒜 := 𝒜) (G k j) • matGen (ρ := ρ) hdeg hsq k +
        ∑ i, (GCDga.sigma 𝒜 (G i j) * ((ρ (f k i) : 𝒜 0) : A)) • matGen (ρ := ρ) hdeg hsq k :=
    fun k => by rw [← hgauge k j, add_smul, Finset.sum_smul]
  rw [Finset.sum_congr rfl fun k _ => hR k, Finset.sum_add_distrib]

/-- A degree-`0` map `Ψ` with `Ψ(ẽⱼ) = Σᵢ Gᵢⱼ • (1 ⊗ wᵢ)` sends `𝕏(ẽⱼ)` to
`Σₖ (Σₗ ωₗⱼ Gₖₗ) • wₖ`. -/
private theorem frame_X_vec {N : QuasiCohesive 𝒜} (F : GradedFrame 𝒜 N.Q r)
    (G : Fin r → Fin r → A)
    {Ψ : N.T →ₗ[k] Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq))}
    (hΨ : Ψ ∈ Hom N (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) 0)
    (hΨvec : ∀ l, Ψ (F.vec l) = ∑ i, G i l • matGen (ρ := ρ) hdeg hsq i) (j : Fin r) :
    Ψ (N.X (F.vec j)) = ∑ k, (∑ l, F.mat l j * G k l) • matGen (ρ := ρ) hdeg hsq k := by
  have sΨ : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N.T, Ψ (a • x) = a • Ψ x := fun ha x => by
    have := hΨ.2 ha x
    rwa [zero_mul, Int.negOnePow_zero, one_smul] at this
  have h1 : N.X (F.vec j) = ∑ l, F.mat l j • F.vec l := (F.sum_coefTot _).symm
  rw [h1, map_sum]
  have h2 : ∀ l, Ψ (F.mat l j • F.vec l) =
      ∑ k, (F.mat l j * G k l) • matGen (ρ := ρ) hdeg hsq k := fun l => by
    rw [sΨ (F.mat_mem l j), hΨvec l]
    simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_congr rfl fun l _ => h2 l, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => (Finset.sum_smul ..).symm

/-- `δ φ` vanishes at `x` if `𝕏 (φ x) = φ (𝕏 x)`. -/
private theorem δ_zero_apply {M₁ M₂ : QuasiCohesive 𝒜} (φ : M₁.T →ₗ[k] M₂.T) (x : M₁.T)
    (h : M₂.X (φ x) = φ (M₁.X x)) : δ M₁ M₂ 0 φ x = 0 := by
  rw [δ_apply]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Int.negOnePow_zero, one_smul, h,
    sub_self]

/-- The map `Ψ(ẽⱼ) = Σᵢ Gᵢⱼ • (1 ⊗ wᵢ)` commutes with `𝕏` (gauge identity), as `δΨ = 0`. -/
private theorem frame_closed {N : QuasiCohesive 𝒜} (F : GradedFrame 𝒜 N.Q r)
    (G : Fin r → Fin r → A) (hG : ∀ i j, G i j ∈ 𝒜 (deg j - deg i))
    (hgauge : ∀ i j, GCDga.d (𝒜 := 𝒜) (G i j) +
        ∑ k, GCDga.sigma 𝒜 (G k j) * ((ρ (f i k) : 𝒜 0) : A) =
      ∑ l, F.mat l j * G i l)
    {Ψ : N.T →ₗ[k] Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq))}
    (hΨ : Ψ ∈ Hom N (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) 0)
    (hΨvec : ∀ l, Ψ (F.vec l) = ∑ i, G i l • matGen (ρ := ρ) hdeg hsq i) :
    δ N (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) 0 Ψ = 0 := by
  refine F.hom_ext (n := 0 + 1) (δ_mem N _ hΨ) (zero_mem _) (fun j => ?_)
  rw [LinearMap.zero_apply]
  refine δ_zero_apply (M₁ := N)
    (M₂ := QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) Ψ (F.vec j) ?_
  exact (congrArg (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc).X
    (hΨvec j)).trans ((X_matY hρ hc hdeg hsq F G hG hgauge j).trans
    (frame_X_vec hρ hc hdeg hsq F G hΨ hΨvec j).symm)

/-- `Ψ ∘ Φ = id` on the generators `1 ⊗ wᵢ`, from `HG = 1`. -/
private theorem frame_comp_gen {N : QuasiCohesive 𝒜} (F : GradedFrame 𝒜 N.Q r)
    (G H : Fin r → Fin r → A) (hH : ∀ i j, H i j ∈ 𝒜 (deg j - deg i))
    (hHG : ∀ k i, ∑ j, H j i * G k j = if k = i then 1 else 0)
    {Ψ : N.T →ₗ[k] Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq))}
    (hΨ : Ψ ∈ Hom N (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) 0)
    (hΨvec : ∀ l, Ψ (F.vec l) = ∑ i, G i l • matGen (ρ := ρ) hdeg hsq i)
    {Φ : Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq)) →ₗ[k] N.T}
    (hΦ : ∀ i, Φ (matGen (ρ := ρ) hdeg hsq i) = ∑ j, H j i • F.vec j) (i : Fin r) :
    Ψ (Φ (matGen (ρ := ρ) hdeg hsq i)) = matGen (ρ := ρ) hdeg hsq i := by
  have sΨ : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : N.T, Ψ (a • x) = a • Ψ x := fun ha x => by
    have := hΨ.2 ha x
    rwa [zero_mul, Int.negOnePow_zero, one_smul] at this
  rw [hΦ i, map_sum]
  have h2 : ∀ j, Ψ (H j i • F.vec j) = ∑ k, (H j i * G k j) • matGen (ρ := ρ) hdeg hsq k :=
    fun j => by
    rw [sΨ (hH j i), hΨvec j]
    simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_comm]
  simp only [← Finset.sum_smul, hHG, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- `Φ ∘ Ψ = id` on the frame vectors, from `GH = 1`. -/
private theorem frame_comp_vec {N : QuasiCohesive 𝒜} (F : GradedFrame 𝒜 N.Q r)
    (G H : Fin r → Fin r → A) (hG : ∀ i j, G i j ∈ 𝒜 (deg j - deg i))
    (hGH : ∀ l j, ∑ i, G i j * H l i = if l = j then 1 else 0)
    {Ψ : N.T →ₗ[k] Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq))}
    (hΨvec : ∀ l, Ψ (F.vec l) = ∑ i, G i l • matGen (ρ := ρ) hdeg hsq i)
    {Φ : Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq)) →ₗ[k] N.T}
    (hΦ : Φ ∈ Hom (QuasiCohesive.fromComplex (matComplex R deg f hdeg hsq) hρ hc) N 0)
    (hΦgen : ∀ i, Φ (matGen (ρ := ρ) hdeg hsq i) = ∑ j, H j i • F.vec j) (j : Fin r) :
    Φ (Ψ (F.vec j)) = F.vec j := by
  have sΦ : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 (FCGen ρ (matComplex R deg f hdeg hsq)),
      Φ (a • x) = a • Φ x := fun ha x => by
    have := hΦ.2 ha x
    rwa [zero_mul, Int.negOnePow_zero, one_smul] at this
  rw [hΨvec j, map_sum]
  have h2 : ∀ i, Φ (G i j • matGen (ρ := ρ) hdeg hsq i) = ∑ l, (G i j * H l i) • F.vec l :=
    fun i => by
    rw [sΦ (hG i j), hΦgen i]
    simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_comm]
  simp only [← Finset.sum_smul, hGH, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- **Z5.i (E.4), algebraic form.** Let `N` be cohesive with a graded frame `F` (degrees `deg`,
connection matrix `ωₗⱼ = F.mat l j`), and let `G, H : Fin r → Fin r → A` be mutually inverse
matrices (`ΣᵢGᵢⱼHₗᵢ = δₗⱼ`, `ΣⱼHⱼᵢGₖⱼ = δₖᵢ`) with `Gᵢⱼ, Hᵢⱼ` of degree `deg j − deg i`,
satisfying the gauge identity `dGᵢⱼ + Σₖ σ(Gₖⱼ)·ρ(fᵢₖ) = Σₗ ωₗⱼ·Gᵢₗ`. Then `N ≅ A ⊗_R W` in
`Ho(P_A)`, `W = matComplex R deg f` (A10). [B, proof of Lemma 4.1.5]: the gauge `G` transforms
`𝕏` into `d ⊗ 1 + 1 ⊗ d_W`. -/
theorem exists_iso_fromComplex_of_frame (N : CohesiveModule 𝒜)
    (F : GradedFrame 𝒜 N.Q r) (hFdeg : F.deg = deg) (G H : Fin r → Fin r → A)
    (hG : ∀ i j, G i j ∈ 𝒜 (deg j - deg i)) (hH : ∀ i j, H i j ∈ 𝒜 (deg j - deg i))
    (hGH : ∀ l j, ∑ i, G i j * H l i = if l = j then 1 else 0)
    (hHG : ∀ k i, ∑ j, H j i * G k j = if k = i then 1 else 0)
    (hgauge : ∀ i j, GCDga.d (𝒜 := 𝒜) (G i j) +
        ∑ k, GCDga.sigma 𝒜 (G k j) * ((ρ (f i k) : 𝒜 0) : A) =
      ∑ l, F.mat l j * G i l) :
    Nonempty (HoP.mk N ≅ HoP.mk (CohesiveModule.fromComplex (ρ := ρ)
      (matComplex R deg f hdeg hsq) hρ hc (isBoundedFGProj_matComplex hdeg hsq))) := by
  subst hFdeg
  have hy : ∀ j, (∑ i, G i j • matGen (ρ := ρ) hdeg hsq i) ∈
      totDeg 𝒜 (QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc).Q (F.deg j) :=
    fun j => matY_mem hdeg hsq G hG j
  let Ψ : Hom N.toQuasiCohesive
      (QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc) 0 :=
    F.frameHom (fun j => ∑ i, G i j • matGen (ρ := ρ) hdeg hsq i) hy
  have hΨvec : ∀ l, Ψ.1 (F.vec l) = ∑ i, G i l • matGen (ρ := ρ) hdeg hsq i :=
    fun l => F.frameHom_vec _ hy l
  obtain ⟨Φ, hΦ⟩ := exists_matGen_hom hρ hc hdeg hsq N.toQuasiCohesive
    (fun i => ∑ j, H j i • F.vec j) (fun i => frameZ_mem F rfl H hH i)
  have hΦΨ : ∀ x, Φ.1 (Ψ.1 x) = x := by
    have hc1 : Φ.1 ∘ₗ Ψ.1 ∈ Hom N.toQuasiCohesive N.toQuasiCohesive 0 := by
      simpa using comp_mem _ _ _ Φ.2 Ψ.2
    have h := F.hom_ext (n := 0) hc1 (id_mem _)
      (fun j => frame_comp_vec hρ hc hdeg hsq F G H hG hGH (Ψ := Ψ.1) hΨvec (Φ := Φ.1) Φ.2 hΦ j)
    exact fun x => LinearMap.congr_fun h x
  have hΨΦ : ∀ w, Ψ.1 (Φ.1 w) = w := by
    have hc2 : Ψ.1 ∘ₗ Φ.1 ∈ Hom (QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc)
        (QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc) 0 := by
      simpa using comp_mem _ _ _ Ψ.2 Φ.2
    have h := matGen_hom_ext hρ hc hdeg hsq
      (QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc) (n := 0) hc2 (id_mem _)
      (fun i => frame_comp_gen hρ hc hdeg hsq F G H hH hHG (Ψ := Ψ.1) Ψ.2 hΨvec (Φ := Φ.1) hΦ i)
    exact fun w => LinearMap.congr_fun h w
  have hδΨ : δ N.toQuasiCohesive
      (QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc) 0 Ψ.1 = 0 :=
    frame_closed hρ hc hdeg hsq F G hG hgauge Ψ.2 hΨvec
  have hΨX : ∀ z, (QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc).X (Ψ.1 z) =
      Ψ.1 (N.X z) := fun z => by
    have h2 := congrArg (fun g => g z) hδΨ
    simp only [δ_apply, Int.negOnePow_zero, one_smul] at h2
    exact sub_eq_zero.1 h2
  have hΦX : ∀ w, N.X (Φ.1 w) =
      Φ.1 ((QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc).X w) := fun w => by
    have h := hΨX (Φ.1 w)
    rw [hΨΦ w] at h
    rw [h, hΦΨ]
  exact ⟨hoPIsoOfInverse ⟨Ψ.1, Submodule.mem_inf.2 ⟨Ψ.2, LinearMap.mem_ker.2 hδΨ⟩⟩
    ⟨Φ.1, Submodule.mem_inf.2 ⟨Φ.2, LinearMap.mem_ker.2
      (LinearMap.ext fun z => by
        change N.X (Φ.1 z) - (0 : ℤ).negOnePow •
          Φ.1 ((QuasiCohesive.fromComplex (matComplex R F.deg f hdeg hsq) hρ hc).X z) = 0
        rw [Int.negOnePow_zero, one_smul]
        exact sub_eq_zero.2 (hΦX z))⟩⟩ hΦΨ hΨΦ⟩

end FrameIso

end Cohesive
