import Cohesivemodules.Forms.Dbar
import Mathlib.LinearAlgebra.Lagrange

set_option linter.style.header false

/-!
# K7: our `∂̄` against TauCeti's `delBar`

Blueprint check K7 (`blueprint/blueprint.md` §6, detail K7′; promoted from LATER by the human
6 Nov 2026). A sanity check of the normalization of F3 against an independent definition.

**Transcription** (part (a) of K7′; needs human review). TauCeti (`TauCetiProject/TauCeti`,
Apache-2.0; not a dependency) defines, for a real endomorphism `J` and complex-valued real forms
`ω : V [⋀^Fin k]→L[ℝ] F` (`TauCeti/Topology/Algebra/Module/Alternating/AlmostComplexType.lean`):
* `alternatingDerivation J ω v = Σ_i ω (update v i (J (v i)))`;
* `IsOfType ω J p q := p + q = k ∧ alternatingDerivation J ω = ((p − q) i) • ω`;
* `typePolynomial k p q := Lagrange.basis (antidiagonal k) (fun (p', q') ↦ (p' − q') i) (p, q)`,
  `typeProjection J p q := aeval (alternatingDerivation J) (typePolynomial k p q)`;
and (`TauCeti/Geometry/Manifold/DifferentialForm/Dolbeault/Basic.lean`)
`delBar φ = Σ_{(p,q) ∈ antidiagonal k} π^{p,q+1}(d (π^{p,q} φ))`. Here these are transcribed on
the model space `E` with `J = i·` (`tcJ`), Mathlib's `extDeriv` in place of `mextDerivₗ`, and the
type projections applied pointwise: `tcDeriv`, `tcIsOfType`, `tcEig`, `tcTypePolynomial`,
`tcTypeProjection`, `tcDelBar`. The alternation proof of `tcDeriv` follows TauCeti's
`sum_compSlot_eq_zero`.

**Checks.**
* (b) `tcTypeProjection_of_isOfType`: on a form of type `(p,q)`, `π^{p',q'}` is the identity for
  `(p',q') = (p,q)` and `0` otherwise;
* (i) `tcIsOfType_toReal`: `DolbeaultFibre.toReal α` has type `(0,q)`;
* (ii) `tcDelBar_of_isOfType`: for a family of `(0,q)`-forms, `tcDelBar φ = π^{0,q+1}(dφ)`;
* (e) `tcTypeProjection_zero_apply`: `π^{0,n} ω (v) = 2^{-n} Σ_S i^{|S|} ω(J_S v)`;
* (iii) `tcDelBar_toReal`: `tcDelBar (toReal ∘ α) = toReal (dbar α)` (with F3.c
  `dbar_eq_extDeriv`);
* (iv) `tcDelBar_conj`: on `E = ℂ`, `tcDelBar` of the function `z̄` is `v ↦ v̄`.
-/

noncomputable section

namespace Cohesive

open Complex Polynomial Function
open scoped ComplexConjugate

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ## (a) Transcription -/

variable (E) in
/-- **K7 (a).** The complex structure `J = i·` of `E`, as a real continuous linear map. -/
def tcJ : E →L[ℝ] E := (I : ℂ) • ContinuousLinearMap.id ℝ E

/-- K7: `tcJ v = i • v` (rfl). -/
theorem tcJ_apply (v : E) : tcJ E v = I • v := rfl

/-- **K7 (a).** TauCeti's `compSlot`: `ω` with `J` applied to the `i`-th argument. -/
def tcSlot {k : ℕ} (ω : E [⋀^Fin k]→L[ℝ] F) (i : Fin k) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) F :=
  ω.toContinuousMultilinearMap.compContinuousLinearMap
    (update (fun _ ↦ ContinuousLinearMap.id ℝ E) i (tcJ E))

/-- K7: `tcSlot ω i v = ω (update v i (J (v i)))`. -/
theorem tcSlot_apply {k : ℕ} (ω : E [⋀^Fin k]→L[ℝ] F) (i : Fin k) (v : Fin k → E) :
    tcSlot ω i v = ω (update v i (tcJ E (v i))) := by
  simp only [tcSlot, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine congrArg ω (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [update_of_ne hj]

/-- K7 (TauCeti `sum_compSlot_eq_zero`): `Σ_i tcSlot ω i` is alternating. -/
theorem tcSlot_sum_eq_zero {k : ℕ} (ω : E [⋀^Fin k]→L[ℝ] F) (v : Fin k → E) {a b : Fin k}
    (hv : v a = v b) (hab : a ≠ b) : (∑ i, tcSlot ω i) v = 0 := by
  rw [sum_apply, Fintype.sum_eq_add a b hab]
  · rw [tcSlot_apply, tcSlot_apply]
    have hswap : update v b (tcJ E (v b)) = update v a (tcJ E (v a)) ∘ Equiv.swap a b := by
      rw [update_comp_equiv, Equiv.symm_swap, Equiv.swap_apply_left, ← hv]
      congr 1
      ext j
      rcases eq_or_ne j a with rfl | hja
      · simp [hv]
      rcases eq_or_ne j b with rfl | hjb
      · simp [hv]
      · simp [Equiv.swap_apply_of_ne_of_ne hja hjb]
    rw [hswap, add_comm]
    simpa using ω.toAlternatingMap.map_swap_add (update v a (tcJ E (v a))) hab
  · rintro i ⟨hia, hib⟩
    rw [tcSlot_apply]
    exact ω.map_eq_zero_of_eq _ (by simp [update_of_ne hia.symm, update_of_ne hib.symm, hv]) hab

/-- K7: additivity of `Σ_i tcSlot · i`. -/
theorem tcSlot_sum_add {k : ℕ} (ω ω' : E [⋀^Fin k]→L[ℝ] F) :
    ∑ i, tcSlot (ω + ω') i = ∑ i, tcSlot ω i + ∑ i, tcSlot ω' i := by
  ext v
  simp [tcSlot_apply, Finset.sum_add_distrib]

/-- K7: `ℂ`-homogeneity of `Σ_i tcSlot · i`. -/
theorem tcSlot_sum_smul {k : ℕ} (c : ℂ) (ω : E [⋀^Fin k]→L[ℝ] F) :
    ∑ i, tcSlot (c • ω) i = c • ∑ i, tcSlot ω i := by
  ext v
  simp [tcSlot_apply, Finset.smul_sum]

/-- **K7 (a).** TauCeti's `alternatingDerivation` of `J = i·`:
`tcDeriv ω v = Σ_i ω (update v i (i • v i))`. -/
def tcDeriv {k : ℕ} : (E [⋀^Fin k]→L[ℝ] F) →ₗ[ℂ] (E [⋀^Fin k]→L[ℝ] F) where
  toFun ω := ⟨∑ i, tcSlot ω i, fun v _ _ hv hab ↦ tcSlot_sum_eq_zero ω v hv hab⟩
  map_add' ω ω' := ContinuousAlternatingMap.ext fun v ↦ by simp [tcSlot_sum_add]
  map_smul' c ω := ContinuousAlternatingMap.ext fun v ↦ by simp [tcSlot_sum_smul]

/-- K7: `tcDeriv ω v = Σ_i ω (update v i (i • v i))`. -/
theorem tcDeriv_apply {k : ℕ} (ω : E [⋀^Fin k]→L[ℝ] F) (v : Fin k → E) :
    tcDeriv ω v = ∑ i, ω (update v i (I • v i)) := by
  simp [tcDeriv, tcSlot_apply, tcJ_apply]

/-- **K7 (a).** TauCeti's `IsOfType` for `J = i·`: `p + q = k` and `tcDeriv ω = ((p − q) i) • ω`. -/
def tcIsOfType {k : ℕ} (ω : E [⋀^Fin k]→L[ℝ] F) (p q : ℕ) : Prop :=
  p + q = k ∧ tcDeriv ω = (((p : ℂ) - q) * I) • ω

/-- **K7 (a).** TauCeti's `typeEigenvalue`: `(p, q) ↦ (p − q) i`. -/
def tcEig (pq : ℕ × ℕ) : ℂ := ((pq.1 : ℂ) - pq.2) * I

/-- **K7 (a).** TauCeti's `typePolynomial`: the Lagrange basis polynomial at `(p − q) i` of the
nodes `(p' − q') i`, `p' + q' = k`. -/
def tcTypePolynomial (k p q : ℕ) : ℂ[X] :=
  Lagrange.basis (Finset.antidiagonal k) tcEig (p, q)

/-- **K7 (a).** TauCeti's `typeProjection` for `J = i·`: the type polynomial evaluated at the
derivation. -/
def tcTypeProjection {k : ℕ} (p q : ℕ) : Module.End ℂ (E [⋀^Fin k]→L[ℝ] F) :=
  aeval (tcDeriv : Module.End ℂ (E [⋀^Fin k]→L[ℝ] F)) (tcTypePolynomial k p q)

/-- **K7 (a).** TauCeti's `delBar` on the model space: for `φ : E → E [⋀^Fin k]→L[ℝ] F`,
`tcDelBar φ x = Σ_{(p,q) ∈ antidiagonal k} π^{p,q+1}(d(π^{p,q} ∘ φ)(x))`, with Mathlib's `extDeriv`
for TauCeti's `mextDerivₗ`. -/
def tcDelBar {k : ℕ} (φ : E → E [⋀^Fin k]→L[ℝ] F) (x : E) : E [⋀^Fin (k + 1)]→L[ℝ] F :=
  ∑ pq ∈ Finset.antidiagonal k,
    tcTypeProjection pq.1 (pq.2 + 1) (extDeriv (fun y ↦ tcTypeProjection pq.1 pq.2 (φ y)) x)

/-! ## (b)–(iv) Checks -/

/-- K7 helper: the eigenvalues `tcEig` are distinct on the antidiagonal. -/
private theorem tcEig_injOn (k : ℕ) :
    Set.InjOn tcEig (Finset.antidiagonal k : Set (ℕ × ℕ)) := by
  rintro ⟨p, q⟩ hpq ⟨p', q'⟩ hpq' h
  simp only [Finset.mem_coe, Finset.mem_antidiagonal] at hpq hpq'
  have h' : (p : ℤ) - q = p' - q' := by
    exact_mod_cast mul_right_cancel₀ I_ne_zero (h : ((p : ℂ) - q) * I = ((p' : ℂ) - q') * I)
  ext <;> simp only <;> omega

/-- K7 helper: a polynomial in an endomorphism acts on an eigenvector by the eigenvalue
(`Module.End.aeval_apply_of_mem_apply_eq_smul`, not imported here). -/
private theorem aeval_apply_eigen {M : Type*} [AddCommGroup M] [Module ℂ M] {f : Module.End ℂ M}
    {μ : ℂ} {x : M} (hx : f x = μ • x) (g : ℂ[X]) :
    aeval f g x = g.eval μ • x := by
  refine g.induction_on ?_ ?_ ?_
  · intro a; simp [Module.algebraMap_end_apply]
  · intro p q hp hq; simp [hp, hq, add_smul]
  · intro n a hna
    rw [mul_comm, pow_succ', mul_assoc, map_mul, Module.End.mul_apply, mul_comm, hna]
    simp only [hx, smul_smul, aeval_X, eval_mul, eval_C, eval_pow, eval_X,
      map_smulₛₗ, RingHom.id_apply, mul_comm]

/-- **K7 (b).** On a form of type `(p,q)`, the type projection `π^{p',q'}` (`p' + q' = k`) is the
identity if `(p',q') = (p,q)` and `0` otherwise (Lagrange basis values at an eigenvector). -/
theorem tcTypeProjection_of_isOfType {k : ℕ} {ω : E [⋀^Fin k]→L[ℝ] F} {p q : ℕ}
    (h : tcIsOfType ω p q) {p' q' : ℕ} (hpq' : p' + q' = k) :
    tcTypeProjection p' q' ω = if (p', q') = (p, q) then ω else 0 := by
  have hev : tcTypeProjection p' q' ω = (Lagrange.basis (Finset.antidiagonal k) tcEig
      (p', q')).eval (tcEig (p, q)) • ω :=
    aeval_apply_eigen h.2 _
  rw [hev]
  have hm : (p, q) ∈ Finset.antidiagonal k := by simpa using h.1
  split_ifs with hc
  · rw [← hc, Lagrange.eval_basis_self (tcEig_injOn k) (by simpa using hpq'), one_smul]
  · rw [Lagrange.eval_basis_of_ne hc hm, zero_smul]

/-- K7 helper: `toReal α` is antilinear in each slot: `J` in slot `i` multiplies by `-i`. -/
private theorem toReal_update_I {q : ℕ} (α : DolbeaultFibre E q F) (v : Fin q → E) (i : Fin q) :
    DolbeaultFibre.toReal α (update v i (I • v i)) = (-I) • DolbeaultFibre.toReal α v := by
  rw [DolbeaultFibre.toReal_apply, DolbeaultFibre.toReal_apply]
  have h : (fun j ↦ Conj.toConj (update v i (I • v i) j)) =
      update (fun j ↦ Conj.toConj (v j)) i (conj I • Conj.toConj (v i)) := by
    ext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [update_of_ne hj]
  rw [h, ContinuousAlternatingMap.map_update_smul]
  have h2 : update (fun j ↦ Conj.toConj (v j)) i (Conj.toConj (v i)) =
      fun j ↦ Conj.toConj (v j) := update_eq_self i _
  rw [h2, conj_I]

/-- **K7 (i).** `DolbeaultFibre.toReal α` has type `(0,q)` (antilinear in every slot). -/
theorem tcIsOfType_toReal {q : ℕ} (α : DolbeaultFibre E q F) :
    tcIsOfType (DolbeaultFibre.toReal α) 0 q := by
  refine ⟨by simp, ?_⟩
  ext v
  rw [tcDeriv_apply]
  simp only [toReal_update_I, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ContinuousAlternatingMap.smul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

/-- **K7 (ii).** For a family of forms of type `(0,q)`, only the term `(0,q)` of `tcDelBar`
survives: `tcDelBar φ x = π^{0,q+1}(dφ(x))`. -/
theorem tcDelBar_of_isOfType {q : ℕ} (φ : E → E [⋀^Fin q]→L[ℝ] F)
    (hφ : ∀ y, tcIsOfType (φ y) 0 q) (x : E) :
    tcDelBar φ x = tcTypeProjection 0 (q + 1) (extDeriv φ x) := by
  have hproj : ∀ pq ∈ Finset.antidiagonal q, ∀ y, tcTypeProjection pq.1 pq.2 (φ y) =
      if pq = (0, q) then φ y else 0 := fun pq hpq y ↦
    tcTypeProjection_of_isOfType (hφ y) (Finset.mem_antidiagonal.1 hpq)
  rw [tcDelBar, Finset.sum_eq_single (0, q)]
  · have : (fun y ↦ tcTypeProjection (0, q).1 (0, q).2 (φ y)) = φ := by
      funext y
      rw [hproj _ (by simp) y]
      simp
    rw [this]
  · intro pq hpq hne
    have : (fun y ↦ tcTypeProjection pq.1 pq.2 (φ y)) = fun _ ↦ 0 := by
      funext y
      rw [hproj _ hpq y]
      simp [hne]
    rw [this]
    have h0 : extDeriv (fun _ : E ↦ (0 : E [⋀^Fin q]→L[ℝ] F)) x = 0 := by
      ext v
      simp [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
    rw [h0, map_zero]
  · intro h
    exact absurd (by simp) h

/-- K7 helper: in a commutative algebra, `Σ tᵢ` for `tᵢ² = -1` applied through a polynomial `g`
that is `1` at the eigenvalue `-n i` and `0` at the others is `2^{-n} Σ_S i^{|S|} ∏_S tᵢ`. -/
private theorem aeval_sum_eq {A : Type*} [CommRing A] [Algebra ℂ A] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → A) (ht : ∀ i, t i * t i = -1) (g : ℂ[X])
    (hg : ∀ T : Finset ι,
      g.eval (((T.card : ℂ) - (Tᶜ.card : ℂ)) * I) = if T = ∅ then 1 else 0) :
    aeval (∑ i, t i) g =
      ∑ S : Finset ι, algebraMap ℂ A (((2 : ℂ) ^ Fintype.card ι)⁻¹ * I ^ S.card) *
        ∏ i ∈ S, t i := by
  set a : ℂ →+* A := algebraMap ℂ A with ha
  have haI : a I * a I = -1 := by rw [← map_mul, ← sq, I_sq, map_neg, map_one]
  set Pp : ι → A := fun i ↦ a (1 / 2) * (1 - a I * t i) with hPp
  set Pm : ι → A := fun i ↦ a (1 / 2) * (1 + a I * t i) with hPm
  set e : Finset ι → A := fun T ↦ (∏ i ∈ T, Pp i) * ∏ i ∈ Tᶜ, Pm i with he
  have h12 : a (1 / 2) + a (1 / 2) = 1 := by
    rw [← map_add, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, map_one]
  have h1 : ∀ i, Pp i + Pm i = 1 := fun i ↦ by
    simp only [hPp, hPm]; linear_combination h12
  have hsum : ∑ T : Finset ι, e T = 1 := by
    have h := Finset.prod_add Pp Pm (Finset.univ : Finset ι)
    simp only [h1, Finset.prod_const_one, Finset.powerset_univ] at h
    refine Eq.trans ?_ h.symm
    refine Finset.sum_congr rfl fun T _ ↦ ?_
    simp only [he, Finset.compl_eq_univ_sdiff]
  have hPp1 : ∀ i, t i * Pp i = a I * Pp i := fun i ↦ by
    simp only [hPp]; linear_combination (-(a (1 / 2) * a I)) * ht i + (a (1 / 2) * t i) * haI
  have hPm1 : ∀ i, t i * Pm i = (-a I) * Pm i := fun i ↦ by
    simp only [hPm]; linear_combination (a (1 / 2) * a I) * ht i + (a (1 / 2) * t i) * haI
  have hteq : ∀ (T : Finset ι) j, t j * e T = a (if j ∈ T then I else -I) * e T := by
    intro T j
    by_cases hj : j ∈ T
    · have hj' : ∏ i ∈ T, Pp i = Pp j * ∏ i ∈ T.erase j, Pp i :=
        (Finset.mul_prod_erase T Pp hj).symm
      simp only [he, hj', hj, ↓reduceIte]
      linear_combination (∏ i ∈ T.erase j, Pp i) * (∏ i ∈ Tᶜ, Pm i) * hPp1 j
    · have hj'' : j ∈ Tᶜ := Finset.mem_compl.2 hj
      have hj' : ∏ i ∈ Tᶜ, Pm i = Pm j * ∏ i ∈ Tᶜ.erase j, Pm i :=
        (Finset.mul_prod_erase _ Pm hj'').symm
      simp only [he, hj', hj, ↓reduceIte, map_neg]
      linear_combination (∏ i ∈ T, Pp i) * (∏ i ∈ Tᶜ.erase j, Pm i) * hPm1 j
  have heig : ∀ T : Finset ι, (∑ i, t i) * e T =
      a (((T.card : ℂ) - (Tᶜ.card : ℂ)) * I) * e T := by
    intro T
    rw [Finset.sum_mul]
    simp only [hteq]
    rw [← Finset.sum_mul, ← map_sum]
    congr 2
    rw [← Finset.sum_compl_add_sum T]
    have h1 : ∑ j ∈ Tᶜ, (if j ∈ T then I else -I) = ∑ j ∈ Tᶜ, -I :=
      Finset.sum_congr rfl fun j hj ↦ by simp [Finset.mem_compl.1 hj]
    have h2 : ∑ j ∈ T, (if j ∈ T then I else -I) = ∑ j ∈ T, I :=
      Finset.sum_congr rfl fun j hj ↦ by simp [hj]
    rw [h1, h2]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hgd : ∀ T : Finset ι, aeval (∑ i, t i) g * e T =
      a (g.eval (((T.card : ℂ) - (Tᶜ.card : ℂ)) * I)) * e T := by
    intro T
    have h := aeval_apply_eigen (f := Algebra.lmul ℂ A (∑ i, t i))
      (μ := ((T.card : ℂ) - (Tᶜ.card : ℂ)) * I) (x := e T)
      (by
        show (∑ i, t i) * e T = _ • e T
        rw [Algebra.smul_def]; exact heig T) g
    rw [Polynomial.aeval_algHom_apply] at h
    change aeval (∑ i, t i) g * e T = _ • e T at h
    rw [Algebra.smul_def] at h
    exact h
  have hexp : ∏ i, Pm i = ∑ S : Finset ι,
      algebraMap ℂ A (((2 : ℂ) ^ Fintype.card ι)⁻¹ * I ^ S.card) * ∏ i ∈ S, t i := by
    have hPm' : ∀ i, Pm i = a (I / 2) * t i + a (1 / 2) := fun i ↦ by
      simp only [hPm, show (I / 2 : ℂ) = 1 / 2 * I by ring, map_mul]; ring
    have h := Finset.prod_add (fun i ↦ a (I / 2) * t i) (fun _ ↦ a (1 / 2))
      (Finset.univ : Finset ι)
    simp only [← hPm', Finset.powerset_univ] at h
    rw [h]
    refine Finset.sum_congr rfl fun S _ ↦ ?_
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ_sdiff]
    have hs : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    have hc : ((2 : ℂ) ^ Fintype.card ι)⁻¹ * I ^ S.card =
        (I / 2) ^ S.card * (1 / 2) ^ (Fintype.card ι - S.card) := by
      have h2 : (2 : ℂ) ^ Fintype.card ι = 2 ^ S.card * 2 ^ (Fintype.card ι - S.card) := by
        rw [← pow_add, Nat.add_sub_cancel' hs]
      rw [h2, div_pow, one_div, inv_pow, mul_inv]
      ring
    rw [hc, map_mul, map_pow, map_pow]
    ring
  calc aeval (∑ i, t i) g = aeval (∑ i, t i) g * ∑ T, e T := by rw [hsum, mul_one]
    _ = ∑ T, a (g.eval (((T.card : ℂ) - (Tᶜ.card : ℂ)) * I)) * e T := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun T _ ↦ hgd T
    _ = ∑ T : Finset ι, if T = ∅ then e T else 0 := by
        refine Finset.sum_congr rfl fun T _ ↦ ?_
        rw [hg T]
        split_ifs <;> simp
    _ = e ∅ := by simp
    _ = ∏ i, Pm i := by simp [he]
    _ = _ := hexp

/-- K7 helper: the slot operators `f ↦ f(…, i·v_i, …)` on real multilinear maps: they commute and
square to `-1`. -/
private theorem exists_slot_ops (n : ℕ) :
    ∃ T : Fin n → Module.End ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F),
      (∀ i f v, T i f v = f (update v i (I • v i))) ∧
      (∀ i j, T i * T j = T j * T i) ∧ (∀ i, T i * T i = -1) := by
  let T : Fin n → Module.End ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F) :=
    fun i ↦ ⟨⟨fun f ↦ f.compContinuousLinearMap
      (update (fun _ : Fin n ↦ ContinuousLinearMap.id ℝ E) i (tcJ E)), fun _ _ ↦ rfl⟩,
      fun _ _ ↦ rfl⟩
  have happ : ∀ i f v, T i f v = f (update v i (I • v i)) := by
    intro i f v
    show f.compContinuousLinearMap _ v = _
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    refine congrArg f (funext fun j ↦ ?_)
    rcases eq_or_ne j i with rfl | hj
    · simp [tcJ_apply]
    · simp [update_of_ne hj]
  refine ⟨T, happ, fun i j ↦ ?_, fun i ↦ ?_⟩
  · ext f v
    rw [Module.End.mul_apply, Module.End.mul_apply, happ, happ, happ, happ]
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · congr 1
      simp [update_of_ne hij, update_of_ne hij.symm, update_comm hij]
  · ext f v
    rw [Module.End.mul_apply, happ, happ]
    simp only [update_idem, update_self, smul_smul, I_mul_I, neg_smul, one_smul,
      Module.End.one_apply, LinearMap.neg_apply, neg_apply]
    have := f.toMultilinearMap.map_update_neg v i (v i)
    rw [update_eq_self] at this
    exact this

open scoped IsMulCommutative in
/-- K7 helper: for commuting slot operators `T i` squaring to `-1`, a polynomial `g` that is `1` at
`-n i` and `0` at the other type eigenvalues gives `f ↦ 2^{-n} Σ_S i^{|S|} f(J_S ·)`. -/
private theorem aeval_slot_apply {n : ℕ}
    (T : Fin n → Module.End ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F))
    (happ : ∀ i f v, T i f v = f (update v i (I • v i)))
    (hcomm : ∀ i j, T i * T j = T j * T i) (hsq : ∀ i, T i * T i = -1) (g : ℂ[X])
    (hg : ∀ S : Finset (Fin n),
      g.eval (((S.card : ℂ) - (Sᶜ.card : ℂ)) * I) = if S = ∅ then 1 else 0)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F) (v : Fin n → E) :
    aeval (∑ i, T i) g f v = ((2 : ℂ) ^ n)⁻¹ • ∑ S : Finset (Fin n), I ^ S.card •
      f (fun j ↦ if j ∈ S then I • v j else v j) := by
  have hc : (Set.range T).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j
  have := Algebra.isMulCommutative_adjoin ℂ hc
  let t : Fin n → Algebra.adjoin ℂ (Set.range T) :=
    fun i ↦ ⟨T i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have ht : ∀ i, t i * t i = -1 := fun i ↦ Subtype.ext (hsq i)
  have h := aeval_sum_eq t ht g hg
  have hD : (Algebra.adjoin ℂ (Set.range T)).val (∑ i, t i) = ∑ i, T i := by
    rw [map_sum]; rfl
  have hprod : ∀ (S : Finset (Fin n)) f v, (Algebra.adjoin ℂ (Set.range T)).val (∏ i ∈ S, t i) f v
      = f (fun j ↦ if j ∈ S then I • v j else v j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro f v; simp
    | insert a S ha ih =>
      intro f v
      rw [Finset.prod_insert ha, map_mul, Module.End.mul_apply]
      show T a _ v = _
      rw [happ, ih]
      congr 1
      funext j
      rcases eq_or_ne j a with rfl | hj
      · simp [ha]
      · simp [hj]
  have h' : aeval (∑ i, T i) g = (Algebra.adjoin ℂ (Set.range T)).val
      (∑ S : Finset (Fin n), algebraMap ℂ (Algebra.adjoin ℂ (Set.range T))
        (((2 : ℂ) ^ Fintype.card (Fin n))⁻¹ * I ^ S.card) * ∏ i ∈ S, t i) := by
    rw [← hD, Polynomial.aeval_algHom_apply, h]
  rw [h', map_sum, LinearMap.sum_apply, sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  rw [map_mul, AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply, smul_apply,
    hprod, Fintype.card_fin, mul_smul]

/-- K7 helper: a linear map intertwining two endomorphisms intertwines their polynomials. -/
private theorem aeval_intertwine {N M : Type*} [AddCommGroup N] [Module ℂ N] [AddCommGroup M]
    [Module ℂ M] (φ : N →ₗ[ℂ] M) {A : Module.End ℂ N} {B : Module.End ℂ M}
    (h : ∀ x, φ (A x) = B (φ x)) (g : ℂ[X]) (x : N) :
    φ (aeval A g x) = aeval B g (φ x) := by
  revert x
  refine g.induction_on ?_ ?_ ?_
  · intro a x; simp [Module.algebraMap_end_apply]
  · intro p q hp hq x; simp [hp, hq]
  · intro n a hna x
    have e : (C a * X ^ (n + 1) : ℂ[X]) = X * (C a * X ^ n) := by ring
    rw [e, map_mul (aeval B) X, Module.End.mul_apply, aeval_X, ← hna x,
      map_mul (aeval A) X, Module.End.mul_apply, aeval_X, h]

/-- **K7 (e).** The `(0,n)` component of a real `n`-form, slotwise:
`π^{0,n} ω (v) = 2^{-n} Σ_{S ⊆ Fin n} i^{|S|} ω(J_S v)`, where `J_S` multiplies the slots in `S`
by `i` (the antilinear projection `½(f(v) + i f(J v))` in every slot). -/
theorem tcTypeProjection_zero_apply {n : ℕ} (ω : E [⋀^Fin n]→L[ℝ] F) (v : Fin n → E) :
    tcTypeProjection 0 n ω v = ((2 : ℂ) ^ n)⁻¹ • ∑ S : Finset (Fin n), I ^ S.card •
      ω (fun j ↦ if j ∈ S then I • v j else v j) := by
  obtain ⟨T, happ, hcomm, hsq⟩ := exists_slot_ops (E := E) (F := F) n
  let φ : (E [⋀^Fin n]→L[ℝ] F) →ₗ[ℂ] ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F :=
    ⟨⟨fun ω ↦ ω.toContinuousMultilinearMap, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
  have hAB : ∀ ω : E [⋀^Fin n]→L[ℝ] F, φ (tcDeriv ω) = (∑ i, T i) (φ ω) := by
    intro ω
    ext w
    rw [LinearMap.sum_apply, sum_apply]
    show tcDeriv ω w = _
    rw [tcDeriv_apply]
    simp only [happ]
    rfl
  have hg : ∀ S : Finset (Fin n),
      (tcTypePolynomial n 0 n).eval (((S.card : ℂ) - (Sᶜ.card : ℂ)) * I) =
        if S = ∅ then 1 else 0 := by
    intro S
    have hs : S.card ≤ n := by simpa using Finset.card_le_univ S
    have key : ((S.card : ℂ) - (Sᶜ.card : ℂ)) * I = tcEig (S.card, n - S.card) := by
      rw [Finset.card_compl, Fintype.card_fin]; rfl
    have hm : (S.card, n - S.card) ∈ Finset.antidiagonal n := by simp [hs]
    rw [key, tcTypePolynomial]
    split_ifs with h0
    · subst h0
      simpa using Lagrange.eval_basis_self (tcEig_injOn n) (show (0, n) ∈ _ by simp)
    · refine Lagrange.eval_basis_of_ne ?_ hm
      intro h1
      exact h0 (Finset.card_eq_zero.1 (congrArg Prod.fst h1).symm)
  have h := aeval_intertwine φ hAB (tcTypePolynomial n 0 n) ω
  have h2 := aeval_slot_apply T happ hcomm hsq _ hg (φ ω) v
  have h3 : tcTypeProjection 0 n ω v =
      (aeval (∑ i, T i) (tcTypePolynomial n 0 n)) (φ ω) v := by
    rw [← h]; rfl
  rw [h3, h2]
  rfl

/-- **K7 (iii).** TauCeti's `delBar` of `toReal ∘ α` is `toReal` of our `∂̄α` (F3), for `α`
differentiable at `x`: the two normalizations agree. -/
theorem tcDelBar_toReal {q : ℕ} {α : E → DolbeaultFibre E q F} {x : E}
    (hα : DifferentiableAt ℝ α x) :
    tcDelBar (fun y ↦ DolbeaultFibre.toReal (α y)) x = DolbeaultFibre.toReal (dbar α x) := by
  rw [tcDelBar_of_isOfType _ (fun y ↦ tcIsOfType_toReal (α y)) x]
  ext v
  rw [tcTypeProjection_zero_apply, DolbeaultFibre.toReal_apply, dbar_eq_extDeriv hα v]

/-- **K7 (iv).** On `E = ℂ`, TauCeti's `delBar` of the function `z ↦ z̄` (a `0`-form) is
`v ↦ v̄`, i.e. `dz̄` (as K2). -/
theorem tcDelBar_conj (x : ℂ) (v : Fin 1 → ℂ) :
    tcDelBar (fun z : ℂ ↦ DolbeaultFibre.toReal (form0 (F := ℂ) (fun w : ℂ ↦ conj w) z)) x v =
      conj (v 0) := by
  have hd : HasFDerivAt (fun z : ℂ ↦ conj z) (conjCLE : ℂ →L[ℝ] ℂ) x := conjCLE.hasFDerivAt
  have hdf : DifferentiableAt ℝ (form0 (F := ℂ) (fun w : ℂ ↦ conj w)) x := by
    unfold form0
    exact ((form0Equiv ℂ ℂ : ℂ →L[ℂ] DolbeaultFibre ℂ 0 ℂ).restrictScalars ℝ).differentiableAt.comp
      x hd.differentiableAt
  rw [tcDelBar_toReal hdf, DolbeaultFibre.toReal_apply, dbar_form0 hd.differentiableAt,
    hd.fderiv]
  simp only [Nat.reduceAdd, Fin.isValue, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    antiPart_apply, Conj.ofConj_toConj, ContinuousLinearEquiv.coe_coe,
    ContinuousAlgEquiv.coeCLE_apply, conjCAE_apply, smul_eq_mul, map_mul, conj_I, neg_mul,
    mul_neg]
  linear_combination (-(2⁻¹ : ℂ) * conj (v 0)) * I_sq

end Cohesive
