import Cohesivemodules.Algebra.BaseChangeDef
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

set_option linter.style.header false

/-!
# Z5.h (algebra part): graded frames and coefficients of the total module

Blueprint item Z5.h, E.1 (`blueprint/blueprint-ll.md` §4 E; §11 v1.15). For a graded `A⁰`-module
`Q` whose total `⨁_p Q^p` has a basis `ẽ₁ … ẽ_r` of homogeneous elements (a *graded frame*),
every element `x` of the total module `A ⊗_{A⁰} ⨁_p Q^p` is uniquely `x = Σᵢ xᵢ · (1 ⊗ ẽᵢ)` with
coefficients `xᵢ ∈ A` (`coefTot`). For a quasi-cohesive `N` with such a frame, the
*connection matrix* `ωⱼᵢ` is the `j`-th coefficient of `𝕏(1 ⊗ ẽᵢ)`, and
`𝕏(x)ⱼ = d(xⱼ) + Σᵢ σ(xᵢ) ωⱼᵢ` (`coefTot_X`), from the Leibniz rule `QuasiCohesive.X_tmul`.

Everything is generic in the (possibly curved) dga (no Dolbeault types): `Module.Free` and
`Module.Finite` goals on
the Dolbeault base change time out in `isDefEq` (PROGRESS traps), so the frame of a base change is
produced here for any `DgaHom` (`exists_gradedFrame_bcGen`).

## Deviations
* One frame of `⨁_p Q^p` indexed by `Fin r` with a degree function `deg`, instead of a frame of
  each `Q^p` separately (the fibre operators of Z5.d are indexed by `Fin r`).
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

variable (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- **Z5.h (E.1).** A graded frame of `Q`: a basis `ẽ : Fin r → ⨁_p Q^p` over `A⁰` with
`ẽᵢ ∈ Q^{deg i}`. [B, proof of Lemma 4.1.5]. The field `repr_lof` says that the coordinates of an
element of `Q^p` vanish off the generators of degree `p`. -/
structure GradedFrame (r : ℕ) where
  /-- The degree of the `i`-th frame vector. -/
  deg : Fin r → ℤ
  /-- The frame: a basis of `⨁_p Q^p` over `A⁰`. -/
  basis : Module.Basis (Fin r) (𝒜 0) (⨁ p, Q p)
  /-- The `i`-th frame vector lies in `Q^{deg i}`. -/
  basis_mem : ∀ i, ∃ v : Q (deg i), basis i = lof (𝒜 0) ℤ Q (deg i) v
  /-- Coordinates of an element of `Q^p` vanish at frame vectors of other degrees. -/
  repr_lof : ∀ (p : ℤ) (v : Q p) (i : Fin r), deg i ≠ p → basis.repr (lof (𝒜 0) ℤ Q p v) i = 0

namespace GradedFrame

variable {𝒜 Q} {r : ℕ} (F : GradedFrame 𝒜 Q r)

/-- **Z5.h (E.1).** The frame vector `1 ⊗ ẽᵢ` of the total module. -/
def vec (i : Fin r) : Tot 𝒜 Q := Tot.tmul 𝒜 Q 1 (F.basis i)

/-- The bi-additive map `(a, e) ↦ (a · eᵢ)ᵢ`, `eᵢ` the coordinates of `e`. -/
def coefAux : A →+ (⨁ p, Q p) →+ (Fin r → A) :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk' (fun e i => a * ((F.basis.repr e i : 𝒜 0) : A))
      (fun e e' => by
        funext i
        simp only [map_add, Finsupp.add_apply, Submodule.coe_add, mul_add, Pi.add_apply]))
    (fun a b => AddMonoidHom.ext fun e => by
      funext i
      simp only [AddMonoidHom.mk'_apply, add_mul, AddMonoidHom.add_apply, Pi.add_apply])

/-- Z5.h: formula for `coefAux` (rfl). -/
theorem coefAux_apply (a : A) (e : ⨁ p, Q p) (i : Fin r) :
    F.coefAux a e i = a * ((F.basis.repr e i : 𝒜 0) : A) := rfl

/-- `coefAux` is `A⁰`-balanced (`A⁰` is central). -/
theorem coefAux_balanced (f : 𝒜 0) (a : A) (e : ⨁ p, Q p) :
    F.coefAux (f • a) e = F.coefAux a (f • e) := by
  funext i
  rw [coefAux_apply, coefAux_apply, GCDga.smul0_def 𝒜 f a, map_smul, Finsupp.smul_apply,
    smul_eq_mul]
  change (f : A) * a * _ = a * ((f : A) * _)
  rw [← mul_assoc, GCDga.central 𝒜 f.2 a]

/-- The coefficients as an additive map. -/
def coefAdd : Tot 𝒜 Q →+ (Fin r → A) :=
  TensorProduct.liftAddHom (R := 𝒜 0) F.coefAux F.coefAux_balanced

/-- `coefAdd` is `A`-linear. -/
theorem coefAdd_smul (a : A) (x : Tot 𝒜 Q) : F.coefAdd (a • x) = a • F.coefAdd x := by
  induction x using Tot.induction_on with
  | ht b e =>
    rw [Tot.smul_tmul]
    funext i
    change F.coefAux (a * b) e i = (a • F.coefAux b e) i
    simp only [coefAux_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  | hadd x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **Z5.h (E.1).** The coefficients `x ↦ (xᵢ)ᵢ` of the total module in the frame:
`x = Σᵢ xᵢ · (1 ⊗ ẽᵢ)` (`sum_coefTot`). An `A`-linear map. -/
def coefTot : Tot 𝒜 Q →ₗ[A] (Fin r → A) where
  toFun := F.coefAdd
  map_add' := F.coefAdd.map_add
  map_smul' := F.coefAdd_smul

/-- Z5.h: coefficients of a pure tensor (rfl). -/
theorem coefTot_tmul (a : A) (e : ⨁ p, Q p) (i : Fin r) :
    F.coefTot (Tot.tmul 𝒜 Q a e) i = a * ((F.basis.repr e i : 𝒜 0) : A) := rfl

/-- Z5.h: `(a·x)ᵢ = a·xᵢ`. -/
theorem coefTot_smul (a : A) (x : Tot 𝒜 Q) (i : Fin r) :
    F.coefTot (a • x) i = a * F.coefTot x i := by
  rw [map_smul]
  rfl

/-- Z5.h: the coefficients of the frame vector `1 ⊗ ẽᵢ` are `δᵢⱼ`. -/
theorem coefTot_vec (i j : Fin r) : F.coefTot (F.vec i) j = if j = i then 1 else 0 := by
  rw [vec, coefTot_tmul, one_mul, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : j = i
  · subst h
    simp only [ite_true]
    rfl
  · have h' : ¬ i = j := fun e => h e.symm
    simp only [h, h', ite_false]
    rfl

/-- **Z5.h (E.1).** Every element is the combination of the frame vectors with its
coefficients. -/
theorem sum_coefTot (x : Tot 𝒜 Q) : ∑ i, F.coefTot x i • F.vec i = x := by
  induction x using Tot.induction_on with
  | ht a e =>
    have h : ∑ i, F.coefTot (Tot.tmul 𝒜 Q a e) i • F.vec i
        = ∑ i, Tot.tmul 𝒜 Q a (F.basis.repr e i • F.basis i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coefTot_tmul, vec, Tot.smul_tmul, mul_one, Tot.tmul_smul0]
    rw [h]
    change _ = a ⊗ₜ[𝒜 0] e
    change ∑ i, a ⊗ₜ[𝒜 0] (F.basis.repr e i • F.basis i) = _
    rw [← TensorProduct.tmul_sum, Module.Basis.sum_repr]
  | hadd x y hx hy =>
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [hx, hy]

/-- Z5.h: elements with the same coefficients are equal. -/
theorem ext_coefTot {x y : Tot 𝒜 Q} (h : ∀ i, F.coefTot x i = F.coefTot y i) : x = y := by
  rw [← F.sum_coefTot x, ← F.sum_coefTot y]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- **Z5.h (E.1).** Degrees: the `i`-th coefficient of an element of total degree `m` has form
degree `m − deg i`. -/
theorem coefTot_mem {m : ℤ} {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) (i : Fin r) :
    F.coefTot x i ∈ 𝒜 (m - F.deg i) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q', p, b, e, rfl, hb, rfl⟩ := hx
    change b * ((F.basis.repr (lof (𝒜 0) ℤ Q p e) i : 𝒜 0) : A) ∈ _
    by_cases h : F.deg i = p
    · subst h
      have := SetLike.GradedMul.mul_mem hb (F.basis.repr (lof (𝒜 0) ℤ Q (F.deg i) e) i).2
      rw [add_zero] at this
      rwa [add_sub_cancel_right]
    · rw [F.repr_lof p e i h]
      simp only [ZeroMemClass.coe_zero, mul_zero]
      exact zero_mem _
  | zero => simp only [map_zero, Pi.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, Pi.add_apply]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [← smul_one_smul A r x, coefTot_smul, smul_one_mul]
    exact Submodule.smul_mem _ r hx

/-- Z5.h: the frame vector `1 ⊗ ẽᵢ` has total degree `deg i`. -/
theorem vec_mem (i : Fin r) : F.vec i ∈ totDeg 𝒜 Q (F.deg i) := by
  obtain ⟨v, hv⟩ := F.basis_mem i
  rw [vec, hv]
  have := tmul_mem_totDeg (Q := Q) (SetLike.GradedOne.one_mem (A := 𝒜)) v
  rwa [zero_add] at this

end GradedFrame

/-! ## The connection matrix of a quasi-cohesive module -/

namespace GradedFrame

variable {𝒜} {r : ℕ} {N : QuasiCohesive 𝒜} (F : GradedFrame 𝒜 N.Q r)

/-- **Z5.h (E.1).** The connection matrix: `ωⱼᵢ` is the `j`-th coefficient of `𝕏(1 ⊗ ẽᵢ)`, so
`𝕏(1 ⊗ ẽᵢ) = Σⱼ ωⱼᵢ · (1 ⊗ ẽⱼ)`. [B, proof of Lemma 4.1.5]. -/
def mat (j i : Fin r) : A := F.coefTot (N.X (F.vec i)) j

/-- **Z5.h (E.1).** `ωⱼᵢ` has form degree `deg i + 1 − deg j`. -/
theorem mat_mem (j i : Fin r) : F.mat j i ∈ 𝒜 (F.deg i + 1 - F.deg j) :=
  F.coefTot_mem (N.X_mem (F.vec_mem i)) j

/-- **Z5.h (E.1).** `𝕏` in the frame: `(𝕏x)ⱼ = d(xⱼ) + Σᵢ σ(xᵢ)·ωⱼᵢ`, from the Leibniz rule
`𝕏(a ⊗ e) = da ⊗ e + σ(a)·𝕏(1 ⊗ e)` (`QuasiCohesive.X_tmul`). -/
theorem coefTot_X (x : N.T) (j : Fin r) :
    F.coefTot (N.X x) j =
      GCDga.d (𝒜 := 𝒜) (F.coefTot x j) + ∑ i, GCDga.sigma 𝒜 (F.coefTot x i) * F.mat j i := by
  have key : ∀ i, F.coefTot (N.X (F.coefTot x i • F.vec i)) j =
      (if j = i then GCDga.d (𝒜 := 𝒜) (F.coefTot x i) else 0) +
        GCDga.sigma 𝒜 (F.coefTot x i) * F.mat j i := by
    intro i
    have h1 : F.coefTot x i • F.vec i = Tot.tmul 𝒜 N.Q (F.coefTot x i) (F.basis i) := by
      rw [vec, Tot.smul_tmul, mul_one]
    have h2 : Tot.tmul 𝒜 N.Q (GCDga.d (𝒜 := 𝒜) (F.coefTot x i)) (F.basis i) =
        GCDga.d (𝒜 := 𝒜) (F.coefTot x i) • F.vec i := by
      rw [vec, Tot.smul_tmul, mul_one]
    rw [h1, N.X_tmul, map_add, Pi.add_apply, coefTot_smul, h2, coefTot_smul, coefTot_vec]
    congr 1
    split_ifs <;> simp only [mul_one, mul_zero]
  conv_lhs => rw [← F.sum_coefTot x]
  rw [map_sum, map_sum, Finset.sum_apply]
  simp only [key, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end GradedFrame

/-! ## Existence of graded frames -/

/-- The coordinates of an element of `Q^p` vanish off the fibre over `p` (`DFinsupp.basis`). -/
private theorem dfinsupp_repr_lof_ne {η : ℤ → Type} (bs : ∀ p, Module.Basis (η p) (𝒜 0) (Q p))
    (p : ℤ) (v : Q p) (ix : Σ j, η j) (h : ix.1 ≠ p) :
    (DFinsupp.basis bs).repr (lof (𝒜 0) ℤ Q p v) ix = 0 := by
  obtain ⟨j, a⟩ := ix
  change (bs j).repr ((DFinsupp.single p v : Π₀ i, Q i) j) a = 0
  rw [DFinsupp.single_eq_of_ne h]
  simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]

/-- The basis vectors of `DFinsupp.basis` are the `lof` of the fibre bases. -/
private theorem dfinsupp_basis_apply {η : ℤ → Type} (bs : ∀ p, Module.Basis (η p) (𝒜 0) (Q p))
    (ix : Σ j, η j) : (DFinsupp.basis bs) ix = lof (𝒜 0) ℤ Q ix.1 (bs ix.1 ix.2) := by
  obtain ⟨j, a⟩ := ix
  have h : DFinsupp.basis bs ⟨j, a⟩ = DFinsupp.single j (bs j a) := by
    simp [DFinsupp.basis]
  exact h

/-- **Z5.h (E.1).** A graded module whose pieces are finite free and vanish outside a bounded
range of degrees has a graded frame. -/
theorem exists_gradedFrame (hfree : ∀ p, Module.Free (𝒜 0) (Q p))
    (hfin : ∀ p, Module.Finite (𝒜 0) (Q p))
    (hbdd : ∃ a b : ℤ, ∀ p, (p < a ∨ b < p) → Subsingleton (Q p)) :
    ∃ r, Nonempty (GradedFrame 𝒜 Q r) := by
  classical
  by_cases hT : Subsingleton (𝒜 0)
  · have : Subsingleton (⨁ p, Q p) := Module.subsingleton (𝒜 0) _
    exact ⟨0, ⟨GradedFrame.mk (fun i => Fin.elim0 i) (Module.Basis.empty (⨁ p, Q p))
      (fun i => Fin.elim0 i) (fun _ _ i => Fin.elim0 i)⟩⟩
  · have : Nontrivial (𝒜 0) := not_subsingleton_iff_nontrivial.1 hT
    obtain ⟨a, b, hab⟩ := hbdd
    let bs : ∀ p, Module.Basis (Module.Free.ChooseBasisIndex (𝒜 0) (Q p)) (𝒜 0) (Q p) :=
      fun p => Module.Free.chooseBasis (𝒜 0) (Q p)
    have hmem : ∀ s : (Σ p, Module.Free.ChooseBasisIndex (𝒜 0) (Q p)), s.1 ∈ Set.Icc a b := by
      intro ⟨p, i⟩
      by_contra hp
      have hp' : p < a ∨ b < p := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hp
        exact hp
      have := hab p hp'
      exact (bs p).ne_zero i (Subsingleton.elim _ _)
    have : ∀ p, Finite (Module.Free.ChooseBasisIndex (𝒜 0) (Q p)) :=
      fun p => Module.Finite.finite_basis (bs p)
    have : Finite (Σ p, Module.Free.ChooseBasisIndex (𝒜 0) (Q p)) := by
      refine Finite.of_injective
        (fun s : (Σ p, Module.Free.ChooseBasisIndex (𝒜 0) (Q p)) =>
          (⟨⟨s.1, hmem s⟩, s.2⟩ : Σ p : Set.Icc a b,
            Module.Free.ChooseBasisIndex (𝒜 0) (Q p.1))) ?_
      rintro ⟨p, x⟩ ⟨q, y⟩ h
      simp only [Sigma.mk.inj_iff, Subtype.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      rw [heq_iff_eq] at h2
      rw [h2]
    let e := Finite.equivFin (Σ p, Module.Free.ChooseBasisIndex (𝒜 0) (Q p))
    refine ⟨_, ⟨GradedFrame.mk (fun i => (e.symm i).1) ((DFinsupp.basis bs).reindex e) ?_ ?_⟩⟩
    · intro i
      refine ⟨bs _ (e.symm i).2, ?_⟩
      rw [Module.Basis.reindex_apply]
      exact dfinsupp_basis_apply 𝒜 Q bs (e.symm i)
    · intro p v i h
      rw [Module.Basis.repr_reindex_apply]
      exact dfinsupp_repr_lof_ne 𝒜 Q bs p v _ h

variable {𝒜} {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ]
  [GCDga ℬ]

/-- A tensor product `S ⊗ Q` with `Q` subsingleton is subsingleton. -/
private theorem subsingleton_tensor_aux {R : Type*} [CommRing R] {S : Type*} [AddCommGroup S]
    [Module R S] {Q' : Type*} [AddCommGroup Q'] [Module R Q'] [Subsingleton Q'] :
    Subsingleton (S ⊗[R] Q') := by
  refine subsingleton_iff_forall_eq 0 |>.2 fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | tmul s q => rw [Subsingleton.elim q 0, TensorProduct.tmul_zero]
  | add t t' ht ht' => rw [ht, ht', add_zero]

/-- **Z5.h (E.1).** The base change of a cohesive module along a map of (possibly curved) dgas has
a graded frame as soon as
 its generators are free (they are finite and bounded automatically). Stated for any
`DgaHom` to keep the Dolbeault types out of instance search. -/
theorem exists_gradedFrame_bcGen (f : DgaHom 𝒜 ℬ) (M : CohesiveModule 𝒜)
    (hfree : ∀ p, Module.Free (ℬ 0) (BCGen f M.Q p)) :
    ∃ r, Nonempty (GradedFrame ℬ (BCGen f M.Q) r) := by
  have hfin : ∀ p, Module.Finite (ℬ 0) (BCGen f M.Q p) := fun p => by
    have := M.finite p
    exact inferInstanceAs (Module.Finite f.B0 (f.B0 ⊗[𝒜 0] M.Q p))
  obtain ⟨a, b, hab⟩ := M.bounded
  refine exists_gradedFrame ℬ (BCGen f M.Q) hfree hfin ⟨a, b, fun p hp => ?_⟩
  have := hab p hp
  exact subsingleton_tensor_aux (R := 𝒜 0) (S := f.B0) (Q' := M.Q p)

end Cohesive
