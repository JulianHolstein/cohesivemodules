import Cohesivemodules.Algebra.Frame

set_option linter.style.header false

/-!
# Z5.i (algebra part): base change of graded frames

Blueprint item Z5.i, E.4 (`blueprint/blueprint-ll.md` §4 E; §11 v1.15): the iso is built over a
smaller open `U″ ⊆ U′`, so the frame of `M|U′` must be restricted to `(M|U′)|U″`. Generic in the
map of (possibly curved) dgas `f : A → B`:
* `exists_frame_baseChange`: a graded frame `ẽ` of `Q` gives a graded frame `1 ⊗ ẽ` of
  `B⁰ ⊗_{A⁰} Q` (same degrees);
* `coefTot_bcF`, `vec_bcF`, `mat_baseChange`: coefficients, frame vectors and the connection
  matrix are mapped by `f`.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  (f : DgaHom 𝒜 ℬ) {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
  {r : ℕ}

/-- Coordinates of `ι(e)` in a basis `b'` with `b' i = ι(b i)`: they are `f⁰` of those of `e`. -/
private theorem repr_bcι_aux (b : Module.Basis (Fin r) (𝒜 0) (⨁ p, Q p))
    (b' : Module.Basis (Fin r) (ℬ 0) (⨁ p, BCGen f Q p))
    (hb : ∀ i, b' i = bcι f Q (b i)) (e : ⨁ p, Q p) (i : Fin r) :
    b'.repr (bcι f Q e) i = f.f0 (b.repr e i) := by
  have h : bcι f Q e = ∑ j, f.f0 (b.repr e j) • b' j := by
    conv_lhs => rw [← b.sum_repr e]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [bcι_smul, hb]
  rw [h, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
  simp

/-- The base-changed basis of the total module: `1 ⊗ b`, transported along `directSumRight`. -/
private def bcEquiv (b : Module.Basis (Fin r) (𝒜 0) (⨁ p, Q p)) :
    (⨁ p, f.B0 ⊗[𝒜 0] Q p) ≃ₗ[f.B0] (Fin r →₀ f.B0) :=
  (TensorProduct.directSumRight (𝒜 0) f.B0 f.B0 Q).symm ≪≫ₗ
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl f.B0 f.B0) b.repr ≪≫ₗ
        TensorProduct.finsuppScalarRight (𝒜 0) f.B0 f.B0 (Fin r))

/-- The base-changed basis of the total module over `B⁰`. -/
private def bcBasis (b : Module.Basis (Fin r) (𝒜 0) (⨁ p, Q p)) :
    Module.Basis (Fin r) (ℬ 0) (⨁ p, BCGen f Q p) :=
  Module.Basis.ofRepr (bcEquiv f b)

/-- The base-changed basis vectors are the `ι` of the original ones. -/
private theorem bcBasis_apply (b : Module.Basis (Fin r) (𝒜 0) (⨁ p, Q p)) (i : Fin r) :
    bcBasis f b i = bcι f Q (b i) := by
  have key : ∀ e : ⨁ p, Q p, TensorProduct.directSumRight (𝒜 0) f.B0 f.B0 Q
      ((1 : f.B0) ⊗ₜ[𝒜 0] e) = bcι f Q e := by
    intro e
    induction e using DirectSum.induction_on with
    | zero =>
      rw [TensorProduct.tmul_zero, map_zero]
      exact (map_zero _).symm
    | of p q =>
      exact (TensorProduct.directSumRight_tmul_lof (𝒜 0) f.B0 (M₁' := f.B0) (M₂ := Q) 1 p q).trans
        (bcι_lof f Q p q).symm
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, map_add, hx, hy]
      exact (map_add _ _ _).symm
  rw [← key]
  change (bcEquiv f b).symm (Finsupp.single i 1) = _
  simp only [bcEquiv, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  rw [TensorProduct.finsuppScalarRight_symm_apply_single]
  rfl

/-- **Z5.i.** A graded frame `ẽ` of `Q` gives the graded frame `1 ⊗ ẽ` of the base change
`B⁰ ⊗_{A⁰} Q`, with the same degrees. -/
theorem exists_frame_baseChange (F : GradedFrame 𝒜 Q r) :
    ∃ F' : GradedFrame ℬ (BCGen f Q) r,
      F'.deg = F.deg ∧ ∀ i, F'.basis i = bcι f Q (F.basis i) := by
  refine ⟨⟨F.deg, bcBasis f F.basis, ?_, ?_⟩, rfl, bcBasis_apply f F.basis⟩
  · intro i
    obtain ⟨v, hv⟩ := F.basis_mem i
    exact ⟨BCGen.tmul f Q 1 v, by
      change bcBasis f F.basis i = _
      rw [bcBasis_apply, hv, bcι_lof]⟩
  · intro p w i hi
    change (bcBasis f F.basis).repr (lof (ℬ 0) ℤ (BCGen f Q) p w) i = 0
    induction w using BCGen.induction_on with
    | ht β q =>
      rw [BCGen.tmul_eq_smul, map_smul, ← bcι_lof, map_smul, Finsupp.smul_apply,
        repr_bcι_aux f F.basis _ (bcBasis_apply f F.basis), F.repr_lof p q i hi]
      simp
    | hadd x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy, add_zero]

variable {f} {F : GradedFrame 𝒜 Q r} {F' : GradedFrame ℬ (BCGen f Q) r}
  (hF : ∀ i, F'.basis i = bcι f Q (F.basis i))

include hF

/-- Z5.i: the frame vectors of the base-changed frame are the images `F(1 ⊗ ẽᵢ)`. -/
theorem vec_bcF (i : Fin r) : F'.vec i = bcF f Q (F.vec i) := by
  rw [GradedFrame.vec, GradedFrame.vec, bcF_tmul, f.map_one', hF]

/-- **Z5.i.** Coefficients in the base-changed frame: `(F x)ᵢ = f(xᵢ)`. -/
theorem coefTot_bcF (x : Tot 𝒜 Q) (i : Fin r) :
    F'.coefTot (bcF f Q x) i = f (F.coefTot x i) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul, GradedFrame.coefTot_tmul, GradedFrame.coefTot_tmul,
      repr_bcι_aux f F.basis F'.basis hF, f.map_mul', DgaHom.coe_f0]
  | hadd x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add F.coefTot, Pi.add_apply, f.map_add']

omit hF in
/-- **Z5.i.** The connection matrix of the base change is the image of the connection matrix:
`ω′ⱼᵢ = f(ωⱼᵢ)` (`bc_extend_bcF`). -/
theorem mat_baseChange {N : QuasiCohesive 𝒜} {F : GradedFrame 𝒜 N.Q r}
    {F' : GradedFrame ℬ (BCGen f N.Q) r} (hF : ∀ i, F'.basis i = bcι f N.Q (F.basis i))
    (j i : Fin r) : F'.mat (N := N.baseChange f) j i = f (F.mat j i) := by
  change F'.coefTot ((N.baseChange f).X (F'.vec i)) j = f (F.coefTot (N.X (F.vec i)) j)
  rw [vec_bcF hF]
  change F'.coefTot ((bcGenData f N).extend (bcF f N.Q (F.vec i))) j = _
  rw [bc_extend_bcF f N, coefTot_bcF hF]

end Cohesive
