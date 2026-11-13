import Cohesivemodules.Algebra.BaseChangeComp

set_option linter.style.header false

/-!
# A9: base change along maps of (possibly curved) dgas (part 3 of 3)

Split from `Algebra/BaseChange.lean` for size;
continues `Algebra/BaseChangeComp.lean`.
-/

noncomputable section
namespace Cohesive
open TensorProduct DirectSum
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
variable (f : DgaHom 𝒜 ℬ) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
variable (M : QuasiCohesive 𝒜)

/-! ## A10: cohesive modules from complexes (definitions in `Algebra/FromComplexDef.lean`) -/

section FromComplex

open CategoryTheory

variable {R : Type} [CommRing R] (ρ : R →+* 𝒜 0)

variable (W : CochainComplex (ModuleCat.{0} R) ℤ)

variable {ρ} (hρ : ∀ r, GCDga.d (𝒜 := 𝒜) (ρ r : A) = 0)

/-! ### A10.a: the adjunction `Hom^•_{P_A}(A ⊗_R W, M) ≅ Hom^•_R(W, M)` -/

section Adjunction

variable (hc : GCDga.c (𝒜 := 𝒜) = 0) (N : QuasiCohesive 𝒜)

variable (ρ) in
/-- **A10.a** `Hom^n_R(W, N)`: families of `R`-linear maps `f_p : W^p → N` (`N` an `R`-module
through `ρ`, so `f_p` is `ρ`-semilinear into the `A⁰`-module `A ⊗_{A⁰} ⨁ Q_N`) with
`f_p(W^p)` in total degree `p + n`. -/
def HomR (n : ℤ) : AddSubgroup (∀ p, W.X p →ₛₗ[ρ] N.T) where
  carrier := {f | ∀ p w, f p w ∈ totDeg 𝒜 N.Q (p + n)}
  zero_mem' _ _ := zero_mem _
  add_mem' hf hg p w := add_mem (hf p w) (hg p w)
  neg_mem' hf p w := neg_mem (hf p w)

include hρ in
/-- A10.a: `𝕏_N` is `ρ`-semilinear (uses `d ∘ ρ = 0`). -/
theorem X_smulR (r : R) (x : N.T) : N.X (ρ r • x) = ρ r • N.X x := by
  rw [Tot.smul0_eq, Tot.smul0_eq, N.leibniz (ρ r).2, hρ, zero_smul, zero_add,
    Int.negOnePow_zero, one_smul]

include hρ in
/-- **A10.a** The differential of `Hom^•_R(W, N)` on a family:
`(δf)_p = 𝕏 ∘ f_p - (-1)^n f_{p+1} ∘ d_W` (conventions §2). -/
def homRδ (n : ℤ) (f : ∀ p, W.X p →ₛₗ[ρ] N.T) (p : ℤ) : W.X p →ₛₗ[ρ] N.T where
  toFun w := N.X (f p w) - n.negOnePow • f (p + 1) (dW W p w)
  map_add' w w' := by
    rw [map_add, map_add, map_add, map_add, smul_add]
    abel
  map_smul' r w := by
    rw [map_smulₛₗ, X_smulR hρ N, map_smulₛₗ, map_smulₛₗ, RingHom.id_apply, smul_sub,
      smul_comm]

/-- **A10.a** Restriction along `w ↦ 1 ⊗ (1 ⊗ w)`: `φ ↦ (φ(1 ⊗ (1 ⊗ -)))_p`. -/
def fcResP (n : ℤ) (φ : Hom (QuasiCohesive.fromComplex W hρ hc) N n) (p : ℤ) :
    W.X p →ₛₗ[ρ] N.T where
  toFun w := φ.1 (fcι ρ W w)
  map_add' w w' := by
    rw [fcι_add]
    exact φ.1.map_add _ _
  map_smul' r w := by
    have h := φ.2.2 (ρ r).2 (fcι ρ W w)
    rw [mul_zero, Int.negOnePow_zero, one_smul] at h
    rw [fcι_smulR]
    exact h.trans (Tot.smul0_eq _ _).symm

/-- A10.a: formula for the restriction. -/
theorem fcResP_apply (n : ℤ) (φ : Hom (QuasiCohesive.fromComplex W hρ hc) N n) (p : ℤ)
    (w : W.X p) : fcResP W hρ hc N n φ p w = φ.1 (fcι ρ W w) := rfl

/-- A10.a: the restriction lands in `Hom^n_R(W, N)`. -/
theorem fcResP_mem (n : ℤ) (φ : Hom (QuasiCohesive.fromComplex W hρ hc) N n) :
    fcResP W hρ hc N n φ ∈ HomR ρ W N n := fun _ w => φ.2.1 (fcι_mem ρ W w)

/-- **A10.a** Restriction along `w ↦ 1 ⊗ (1 ⊗ w)`, as an additive map
`Hom^n(A ⊗_R W, N) → Hom^n_R(W, N)`. -/
def fcRes (n : ℤ) : Hom (QuasiCohesive.fromComplex W hρ hc) N n →+ HomR ρ W N n where
  toFun φ := ⟨fcResP W hρ hc N n φ, fcResP_mem W hρ hc N n φ⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **A10.a** Restriction commutes with the differentials:
`res(δφ) = 𝕏 ∘ res φ - (-1)^n res φ ∘ d_W`. -/
theorem fcResP_δ (n : ℤ) (φ : Hom (QuasiCohesive.fromComplex W hρ hc) N n) :
    fcResP W hρ hc N (n + 1) ⟨δ _ N n φ.1, δ_mem _ N φ.2⟩ =
      homRδ W hρ N n (fcResP W hρ hc N n φ) := by
  funext p
  ext w
  show N.X (φ.1 (fcι ρ W w)) - n.negOnePow • φ.1 ((fcGenData W hρ).extend (fcι ρ W w)) = _
  rw [fc_extend_fcι]
  rfl

/-- **A10.a** The differential maps `Hom^n_R(W, N)` to `Hom^{n+1}_R(W, N)`. -/
theorem homRδ_mem {n : ℤ} {f : ∀ p, W.X p →ₛₗ[ρ] N.T} (hf : f ∈ HomR ρ W N n) :
    homRδ W hρ N n f ∈ HomR ρ W N (n + 1) := by
  intro p w
  refine sub_mem ?_ (Submodule.smul_of_tower_mem _ _ ?_)
  · have := N.X_mem (hf p w)
    rwa [add_assoc] at this
  · have := hf (p + 1) (dW W p w)
    rwa [add_assoc, add_comm 1 n] at this

/-- **A10.a** Maps of degree `n` out of `A ⊗_R W` are determined on the generators
`1 ⊗ (1 ⊗ w)`. -/
theorem fc_hom_ext {n : ℤ} {χ χ' : Tot 𝒜 (FCGen ρ W) →ₗ[k] N.T}
    (hχ : χ ∈ Hom (QuasiCohesive.fromComplex W hρ hc) N n)
    (hχ' : χ' ∈ Hom (QuasiCohesive.fromComplex W hρ hc) N n)
    (h : ∀ p (w : W.X p), χ (fcι ρ W w) = χ' (fcι ρ W w)) : χ = χ' := by
  have s₁ : ∀ (α : 𝒜 0) (y : Tot 𝒜 (FCGen ρ W)), χ ((α : A) • y) = (α : A) • χ y := by
    intro α y
    have := hχ.2 α.2 y
    rwa [mul_zero, Int.negOnePow_zero, one_smul] at this
  have s₂ : ∀ (α : 𝒜 0) (y : Tot 𝒜 (FCGen ρ W)), χ' ((α : A) • y) = (α : A) • χ' y := by
    intro α y
    have := hχ'.2 α.2 y
    rwa [mul_zero, Int.negOnePow_zero, one_smul] at this
  have t₁ : ∀ (a : A) (e : ⨁ p, FCGen ρ W p), χ (Tot.tmul 𝒜 _ a e) =
      GCDga.twist 𝒜 n a • χ (Tot.tmul 𝒜 _ 1 e) := fun a e => hom_tmul hχ a e
  have t₂ : ∀ (a : A) (e : ⨁ p, FCGen ρ W p), χ' (Tot.tmul 𝒜 _ a e) =
      GCDga.twist 𝒜 n a • χ' (Tot.tmul 𝒜 _ 1 e) := fun a e => hom_tmul hχ' a e
  have hgen : ∀ e : ⨁ p, FCGen ρ W p, χ (Tot.tmul 𝒜 _ 1 e) = χ' (Tot.tmul 𝒜 _ 1 e) := by
    intro e
    induction e using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero, map_zero]
    | of p x =>
      induction x using FCGen.induction_on with
      | ht α w =>
        change χ (Tot.tmul 𝒜 _ 1 (DirectSum.of _ p (FCGen.tmul ρ W (RA0.un ρ α) w))) =
          χ' (Tot.tmul 𝒜 _ 1 (DirectSum.of _ p (FCGen.tmul ρ W (RA0.un ρ α) w)))
        rw [fc_of_tmul, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul, s₁, s₂]
        exact congrArg _ (h p w)
      | hadd x y hx hy =>
        rw [(DirectSum.of (FCGen ρ W) p).map_add, Tot.tmul_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [Tot.tmul_add, map_add, map_add, hx, hy]
  ext x
  induction x using Tot.induction_on with
  | ht a e => rw [t₁, t₂, hgen]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- The bi-additive map `(α, w) ↦ α·f_p(w)` on degree `p`. -/
def fcExtAux (f : ∀ p, W.X p →ₛₗ[ρ] N.T) (p : ℤ) : RA0 ρ →+ W.X p →+ N.T :=
  AddMonoidHom.mk'
    (fun α => AddMonoidHom.mk' (fun w => (RA0.un ρ α : A) • f p w)
      (fun w w' => by rw [map_add, smul_add]))
    (fun α α' => AddMonoidHom.ext fun w => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [show RA0.un ρ (α + α') = RA0.un ρ α + RA0.un ρ α' from rfl, Submodule.coe_add,
        add_smul])

/-- **A10.a** The extension of a family `f` on the degree-`p` generators:
`α ⊗ w ↦ α·f_p(w)`. -/
def fcExtP (f : ∀ p, W.X p →ₛₗ[ρ] N.T) (p : ℤ) : FCGen ρ W p →+ N.T :=
  TensorProduct.liftAddHom (R := R) (fcExtAux W N f p) fun r α w => by
    show (RA0.un ρ (r • α) : A) • f p w = (RA0.un ρ α : A) • f p (r • w)
    rw [RA0.un_smul, map_smulₛₗ, Tot.smul0_eq, smul_smul,
      show ((ρ r * RA0.un ρ α : 𝒜 0) : A) = (ρ r : A) * (RA0.un ρ α : A) from rfl,
      GCDga.central 𝒜 (ρ r).2]

/-- A10.a: `f̂(α ⊗ w) = α·f_p(w)`. -/
theorem fcExtP_tmul (f : ∀ p, W.X p →ₛₗ[ρ] N.T) (p : ℤ) (α : 𝒜 0) (w : W.X p) :
    fcExtP W N f p (FCGen.tmul ρ W α w) = (α : A) • f p w := rfl

/-- **A10.a** The extension of a family `f` to the generators `⨁_p A⁰ ⊗_R W^p`. -/
def fcExtGen (f : ∀ p, W.X p →ₛₗ[ρ] N.T) : (⨁ p, FCGen ρ W p) →+ N.T :=
  DirectSum.toAddMonoid (fcExtP W N f)

/-- A10.a: the extension on a homogeneous generator. -/
theorem fcExtGen_of (f : ∀ p, W.X p →ₛₗ[ρ] N.T) (p : ℤ) (x : FCGen ρ W p) :
    fcExtGen W N f (DirectSum.of (FCGen ρ W) p x) = fcExtP W N f p x :=
  DirectSum.toAddMonoid_of _ p x

/-- A10.a: the extension is `A⁰`-linear. -/
theorem fcExtGen_smul (f : ∀ p, W.X p →ₛₗ[ρ] N.T) (γ : 𝒜 0) (e : ⨁ p, FCGen ρ W p) :
    fcExtGen W N f (γ • e) = (γ : A) • fcExtGen W N f e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    induction x using FCGen.induction_on with
    | ht α w =>
      change fcExtGen W N f (γ • DirectSum.of _ p (FCGen.tmul ρ W (RA0.un ρ α) w)) = _
      rw [show γ • DirectSum.of (FCGen ρ W) p (FCGen.tmul ρ W (RA0.un ρ α) w) =
          DirectSum.of (FCGen ρ W) p (γ • FCGen.tmul ρ W (RA0.un ρ α) w) from
          (map_smul (DirectSum.lof (𝒜 0) ℤ (FCGen ρ W) p) γ _).symm,
        FCGen.smul_tmul, fcExtGen_of, fcExtGen_of, fcExtP_tmul, fcExtP_tmul,
        show ((γ * RA0.un ρ α : 𝒜 0) : A) = (γ : A) * (RA0.un ρ α : A) from rfl, mul_smul]
      rfl
    | hadd x y hx hy =>
      rw [(DirectSum.of (FCGen ρ W) p).map_add, smul_add, map_add, hx, hy, map_add, smul_add]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- A10.a: the extension of a family in `Hom^n_R(W, N)` has degree `n`. -/
theorem fcExtGen_deg {n : ℤ} {f : ∀ p, W.X p →ₛₗ[ρ] N.T} (hf : f ∈ HomR ρ W N n) (p : ℤ)
    (x : FCGen ρ W p) :
    fcExtGen W N f (lof (𝒜 0) ℤ (FCGen ρ W) p x) ∈ totDeg 𝒜 N.Q (p + n) := by
  induction x using FCGen.induction_on with
  | ht α w =>
    change fcExtGen W N f (DirectSum.of _ p _) ∈ _
    rw [fcExtGen_of]
    have := smul_mem_totDeg (RA0.un ρ α).2 (hf p w)
    rwa [zero_add] at this
  | hadd x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/-- **A10.a** The extension `Hom^n_R(W, N) → Hom^n(A ⊗_R W, N)`,
`(f̂)(a ⊗ (α ⊗ w)) = (-1)^{n|a|} aα·f_p(w)`. -/
def fcExt (n : ℤ) (f : HomR ρ W N n) : Hom (QuasiCohesive.fromComplex W hρ hc) N n :=
  ⟨extGen n ⟨fcExtGen W N f.1, fun γ e => fcExtGen_smul W N f.1 γ e, fcExtGen_deg W N f.2⟩,
    extGen_mem n _⟩

/-- A10.a: restriction after extension is the identity. -/
theorem fcResP_fcExt (n : ℤ) (f : HomR ρ W N n) :
    fcResP W hρ hc N n (fcExt W hρ hc N n f) = f.1 := by
  funext p
  ext w
  show GCDga.twist 𝒜 n 1 • fcExtGen W N f.1 (DirectSum.of _ p (FCGen.tmul ρ W 1 w)) = f.1 p w
  rw [GCDga.twist_one, one_smul, fcExtGen_of, fcExtP_tmul, show ((1 : 𝒜 0) : A) = 1 from rfl,
    one_smul]

/-- **A10.a** The adjunction `Hom^n_{P_A}(A ⊗_R W, N) ≅ Hom^n_R(W, N)`, by restriction along
`w ↦ 1 ⊗ (1 ⊗ w)`; it commutes with the differentials (`fcResP_δ`), so it is an isomorphism of
complexes. Used in C4 [A, proof of Prop 7.2.19]. -/
def fcHomEquiv (n : ℤ) : Hom (QuasiCohesive.fromComplex W hρ hc) N n ≃+ HomR ρ W N n where
  toFun := fcRes W hρ hc N n
  invFun := fcExt W hρ hc N n
  left_inv φ := by
    refine Subtype.ext (fc_hom_ext W hρ hc N (fcExt W hρ hc N n _).2 φ.2 fun p w => ?_)
    exact congrFun (congrArg DFunLike.coe
      (congrFun (fcResP_fcExt W hρ hc N n (fcRes W hρ hc N n φ)) p)) w
  right_inv f := Subtype.ext (fcResP_fcExt W hρ hc N n f)
  map_add' := (fcRes W hρ hc N n).map_add

end Adjunction

end FromComplex

end Cohesive

end
