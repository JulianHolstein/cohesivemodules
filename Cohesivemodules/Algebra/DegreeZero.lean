import Cohesivemodules.Algebra.BaseChange

set_option linter.style.header false

/-!
# Cohesive modules over a dga concentrated in degree 0

A sanity result about A10 (`CohesiveModule.fromComplex`), used for the H2 trivial case (K1,
`localGaugeLemma_of_finrank_eq_zero` in `Hypotheses.lean`).

* `exists_iso_fromComplex_of_degree_zero`: if `𝒜 q = 0` for `q ≠ 0` and `ρ : R → A⁰` is a
  bijective ring map with `d ∘ ρ = 0`, `c = 0`, every cohesive module `M` is isomorphic in
  `Ho(P_A)` to `A ⊗_R W` (A10), `W` its complex of generators `(M.Q, 𝕏⁰)` regarded as
  `R`-modules through `ρ`.

The proof (by `lean-prover`, moved here from `Hypotheses.lean`) builds mutually inverse closed
maps of degree 0: `φ : A ⊗_R W → M`, the extension of `w ↦ 1 ⊗ w` (A10.a), and `ψ = famTot` of
`y ↦ 1 ⊗ y`.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- If `𝒜 q = 0` for `q ≠ 0` then `proj0` is the identity. -/
private theorem proj0_eq (hdeg : ∀ q, q ≠ 0 → 𝒜 q = ⊥) (a : A) :
    ((Tot.proj0 𝒜 a : 𝒜 0) : A) = a := by
  have h := GCDga.sum_proj (𝒜 := 𝒜) a
  have h0 : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) (GCDga.N 𝒜) := by simp
  rw [Finset.sum_eq_single_of_mem 0 h0] at h
  · exact h
  · intro q _ hq
    have := GCDga.proj_mem 𝒜 q a
    rw [hdeg q hq, Submodule.mem_bot] at this
    exact this

/-- If `𝒜 q = 0` for `q ≠ 0` then `1 ⊗ ε x = x`. -/
private theorem oneTmul_eps (hdeg : ∀ q, q ≠ 0 → 𝒜 q = ⊥) (Q : ℤ → Type)
    [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (x : Tot 𝒜 Q) :
    Tot.oneTmul 𝒜 Q (Tot.eps 𝒜 Q x) = x := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.eps_tmul, Tot.oneTmul_apply, Tot.tmul_smul0, one_mul, proj0_eq hdeg]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- Under `hdeg`, `𝕏 x = 1 ⊗ 𝕏⁰ (ε x)`. -/
private theorem X_eq (hdeg : ∀ q, q ≠ 0 → 𝒜 q = ⊥) (M : QuasiCohesive 𝒜) (x : M.T) :
    M.X x = Tot.oneTmul 𝒜 M.Q (M.X0 (Tot.eps 𝒜 M.Q x)) := by
  rw [← M.eps_X, oneTmul_eps hdeg]

variable {R : Type} [CommRing R]

/-- The generators `M.Q p` regarded as `R`-modules through `ρ`. -/
private def QR (_ρ : R →+* 𝒜 0) (M : QuasiCohesive 𝒜) (p : ℤ) : Type := M.Q p

private instance (ρ : R →+* 𝒜 0) (M : QuasiCohesive 𝒜) (p : ℤ) : AddCommGroup (QR ρ M p) :=
  inferInstanceAs (AddCommGroup (M.Q p))

private instance (ρ : R →+* 𝒜 0) (M : QuasiCohesive 𝒜) (p : ℤ) : Module R (QR ρ M p) :=
  Module.compHom (M.Q p) ρ

/-- `r • y = ρ r • y` in `QR`. -/
private theorem QR_smul (ρ : R →+* 𝒜 0) (M : QuasiCohesive 𝒜) (p : ℤ) (r : R) (y : QR ρ M p) :
    r • y = ρ r • (show M.Q p from y) := rfl

/-- The component `Q^p → Q^{p+1}` of `𝕏⁰`, `A⁰`-linear. -/
private def dq (M : QuasiCohesive 𝒜) (p : ℤ) : M.Q p →ₗ[𝒜 0] M.Q (p + 1) where
  toFun y := (M.X0 (lof (𝒜 0) ℤ M.Q p y)) (p + 1)
  map_add' y y' := by
    rw [map_add, map_add]; rfl
  map_smul' r y := by
    rw [map_smul, map_smul, DirectSum.smul_apply, RingHom.id_apply]

/-- The component `Q^p → Q^{p+1}` of `𝕏⁰`, `R`-linear. -/
private def dQ (ρ : R →+* 𝒜 0) (M : QuasiCohesive 𝒜) (p : ℤ) :
    QR ρ M p →ₗ[R] QR ρ M (p + 1) where
  toFun y := dq M p y
  map_add' y y' := (dq M p).map_add y y'
  map_smul' r y := (dq M p).map_smul (ρ r) (show M.Q p from y)

/-- `𝕏⁰` on a homogeneous generator. -/
private theorem X0_lof (M : QuasiCohesive 𝒜) (p : ℤ) (y : M.Q p) :
    M.X0 (lof (𝒜 0) ℤ M.Q p y) = lof (𝒜 0) ℤ M.Q (p + 1) (dq M p y) := by
  ext p'
  by_cases h : p' = p + 1
  · subst h
    simp only [lof_eq_of, of_eq_same]
    rfl
  · rw [M.X0_concAt y p' h, lof_eq_of, of_eq_of_ne _ _ _ h]

/-- `d ∘ d = 0` on the generators. -/
private theorem dq_dq (M : QuasiCohesive 𝒜) (p : ℤ) (y : M.Q p) :
    dq M (p + 1) (dq M p y) = 0 := by
  have h := M.X0_X0 (lof (𝒜 0) ℤ M.Q p y)
  rw [X0_lof, X0_lof] at h
  have h2 := congrArg (fun e => e (p + 1 + 1)) h
  simpa [lof_eq_of] using h2

/-- The complex of generators `(Q, 𝕏⁰)` as a complex of `R`-modules. -/
private def Wc (ρ : R →+* 𝒜 0) (M : QuasiCohesive 𝒜) : CochainComplex (ModuleCat.{0} R) ℤ :=
  CochainComplex.of (fun p => ModuleCat.of R (QR ρ M p))
    (fun p => ModuleCat.ofHom (dQ ρ M p))
    (fun p => by
      ext y
      exact dq_dq M p y)

/-- The differential of `Wc` is `dQ`. -/
private theorem Wc_d (ρ : R →+* 𝒜 0) (M : QuasiCohesive 𝒜) (p : ℤ) (y : QR ρ M p) :
    dW (Wc ρ M) p y = dQ ρ M p y := by
  unfold dW Wc
  change ModuleCat.Hom.hom (CochainComplex.of.d (fun p => ModuleCat.of R (QR ρ M p)) _ p
    (p + 1)) y = _
  rw [CochainComplex.of_d]
  rfl

/-- `Wc` is a bounded complex of finitely generated projective `R`-modules when `ρ` is
bijective. -/
private theorem Wc_bdd (ρ : R →+* 𝒜 0) (hρ : Function.Bijective ρ) (M : CohesiveModule 𝒜) :
    IsBoundedFGProj R (Wc ρ M.toQuasiCohesive) := by
  let e : R ≃+* 𝒜 0 := RingEquiv.ofBijective ρ hρ
  have : RingHomInvPair (e.symm : 𝒜 0 →+* R) (e : R →+* 𝒜 0) :=
    RingHomInvPair.of_ringEquiv_symm e
  have : RingHomInvPair (e : R →+* 𝒜 0) (e.symm : 𝒜 0 →+* R) := RingHomInvPair.of_ringEquiv e
  have key : ∀ p, ∃ e₂ : M.Q p ≃ₛₗ[(e.symm : 𝒜 0 →+* R)] QR ρ M.toQuasiCohesive p,
      ∀ y, e₂ y = y := fun p =>
    ⟨{ toFun := fun y => y
       map_add' := fun _ _ => rfl
       map_smul' := fun a y => by
         change _ = ρ (e.symm a) • y
         have : ρ (e.symm a) = a := e.apply_symm_apply a
         rw [this]
       invFun := fun y => y
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl }, fun _ => rfl⟩
  refine ⟨?_, fun p => ?_, fun p => ?_⟩
  · obtain ⟨a, b, h⟩ := M.bounded
    exact ⟨a, b, fun p hp => h p hp⟩
  · have := M.finite p
    obtain ⟨e₂, _⟩ := key p
    exact Module.Finite.of_surjective e₂.toLinearMap e₂.surjective
  · have := M.projective p
    obtain ⟨e₂, _⟩ := key p
    exact Module.Projective.of_equiv e₂

/-- The generator inclusion `w ↦ 1 ⊗ w`, `ρ`-semilinear on `W^p`. -/
private def genIncl (ρ : R →+* 𝒜 0) (M : QuasiCohesive 𝒜) (p : ℤ) :
    (Wc ρ M).X p →ₛₗ[ρ] M.T where
  toFun w := Tot.oneTmul 𝒜 M.Q (lof (𝒜 0) ℤ M.Q p (show M.Q p from w))
  map_add' w w' := by
    rw [← map_add, ← map_add]
    rfl
  map_smul' r w := by
    rw [← map_smul, ← map_smul]
    rfl

/-- **A10, degree-0 case** (sanity; used for K1). [B, Lemma 4.1.5 (proof)]. Let `𝒜` be
concentrated in degree `0` (`𝒜 q = ⊥` for `q ≠ 0`), `ρ : R →+* 𝒜 0` bijective with `d ∘ ρ = 0`,
and `c = 0`. Then every cohesive module `M` over `𝒜` is isomorphic in `Ho(P_A)` to
`fromComplex ρ W` (`A ⊗_R W`, A10) for some bounded complex `W` of finitely generated projective
`R`-modules (its generator complex `(M.Q, 𝕏⁰)` through `ρ`). -/
theorem exists_iso_fromComplex_of_degree_zero (hdeg : ∀ q, q ≠ 0 → 𝒜 q = ⊥)
    (ρ : R →+* 𝒜 0) (hb : Function.Bijective ρ) (hρ : ∀ r, GCDga.d (𝒜 := 𝒜) (ρ r : A) = 0)
    (hc : GCDga.c (𝒜 := 𝒜) = 0) (M : CohesiveModule 𝒜) :
    ∃ (W : CochainComplex (ModuleCat.{0} R) ℤ) (hW : IsBoundedFGProj R W),
      Nonempty (HoP.mk M ≅ HoP.mk (CohesiveModule.fromComplex (ρ := ρ) W hρ hc hW)) := by
  refine ⟨Wc ρ M.toQuasiCohesive, Wc_bdd ρ hb M, ?_⟩
  let W := Wc ρ M.toQuasiCohesive
  let N := M.toQuasiCohesive
  let F := QuasiCohesive.fromComplex W hρ hc
  have hf : (fun p => genIncl ρ N p) ∈ HomR ρ W N 0 := fun p w => by
    have := tmul_mem_totDeg (Q := N.Q) (SetLike.GradedOne.one_mem (A := 𝒜)) (show N.Q p from w)
    rw [zero_add] at this
    rwa [add_zero]
  let φ : Hom F N 0 := fcExt W hρ hc N 0 ⟨fun p => genIncl ρ N p, hf⟩
  have hφι : ∀ p (w : W.X p), φ.1 (fcι ρ W w) = genIncl ρ N p w := fun p w =>
    congrArg (fun g => g p w) (fcResP_fcExt W hρ hc N 0 ⟨fun p => genIncl ρ N p, hf⟩)
  have hφX : ∀ z, N.X (φ.1 z) = φ.1 (F.X z) := by
    have h := fc_hom_ext W hρ hc N (n := 0 + 1) (δ_mem F N φ.2) (zero_mem _) (fun p w => by
      have h1 : N.X (genIncl ρ N p w) = genIncl ρ N (p + 1) (dW W p w) := by
        rw [show dW W p w = dQ ρ N p w from Wc_d ρ N p w]
        change N.X (Tot.oneTmul 𝒜 N.Q (lof (𝒜 0) ℤ N.Q p w)) =
          Tot.oneTmul 𝒜 N.Q (lof (𝒜 0) ℤ N.Q (p + 1) (dq N p w))
        rw [X_eq hdeg, Tot.eps_oneTmul]
        exact congrArg (Tot.oneTmul 𝒜 N.Q) (X0_lof N p (show N.Q p from w))
      have h3 : F.X (fcι ρ W w) = fcι ρ W (dW W p w) := fc_extend_fcι W hρ w
      show N.X (φ.1 (fcι ρ W w)) - (0 : ℤ).negOnePow • φ.1 (F.X (fcι ρ W w)) = 0
      rw [h3, hφι, hφι, h1, Int.negOnePow_zero, one_smul, sub_self])
    intro z
    have h2 := congrArg (fun g => g z) h
    simp only [δ_apply, Int.negOnePow_zero, one_smul] at h2
    exact sub_eq_zero.1 h2
  let v : ∀ p, N.Q p →+ F.Q p := fun p =>
    AddMonoidHom.mk' (fun y => FCGen.tmul ρ W 1 (show W.X p from y))
      (fun y y' => FCGen.tmul_add 1 _ _)
  have hv : ∀ p (r : 𝒜 0) (y : N.Q p), v p (r • y) = r • v p y := by
    intro p r y
    obtain ⟨s, hs⟩ := hb.2 r
    have h1 : r • y = s • (show W.X p from y) := by
      rw [← hs]
      rfl
    change FCGen.tmul ρ W 1 (show W.X p from r • y) =
      r • FCGen.tmul ρ W 1 (show W.X p from y)
    rw [h1, FCGen.tmul_smulR, FCGen.smul_tmul, hs]
  let ψ : Hom N F 0 := ⟨famTot (k := k) v hv, famTot_mem v hv⟩
  have ha : ∀ x, ψ.1 (φ.1 x) = x := by
    have hcomp : ψ.1 ∘ₗ φ.1 ∈ Hom F F 0 := by simpa using comp_mem F N F ψ.2 φ.2
    have h := fc_hom_ext W hρ hc F hcomp (id_mem F) (fun p w => by
      show ψ.1 (φ.1 (fcι ρ W w)) = fcι ρ W w
      rw [hφι]
      change famTot (k := k) v hv
          (Tot.tmul 𝒜 N.Q 1 (DirectSum.of N.Q p (show N.Q p from w))) =
        Tot.tmul 𝒜 F.Q 1 (DirectSum.of F.Q p (FCGen.tmul ρ W 1 w))
      rw [famTot_tmul, famMap_of]
      rfl)
    exact fun x => LinearMap.congr_fun h x
  have hb' : ∀ x, φ.1 (ψ.1 x) = x := by
    have hgen : ∀ e : ⨁ p, N.Q p,
        φ.1 (Tot.tmul 𝒜 F.Q 1 (famMap v e)) = Tot.tmul 𝒜 N.Q 1 e := by
      intro e
      induction e using DirectSum.induction_on with
      | zero => rw [map_zero, Tot.tmul_zero, map_zero, Tot.tmul_zero]
      | of p y =>
        rw [famMap_of]
        exact hφι p (show W.X p from y)
      | add x y hx hy => rw [map_add, Tot.tmul_add, map_add, hx, hy, Tot.tmul_add]
    intro x
    induction x using Tot.induction_on with
    | ht a e =>
      change φ.1 (famTot (k := k) v hv (Tot.tmul 𝒜 N.Q a e)) = _
      rw [famTot_tmul, hom_tmul φ.2 a, hgen, GCDga.twist_zero, Tot.tmul_eq_smul a e]
    | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  have hψX : ∀ z, F.X (ψ.1 z) = ψ.1 (N.X z) := fun z => by
    have h := hφX (ψ.1 z)
    rw [hb' z] at h
    rw [h, ha]
  let zψ : Z0 N F := ⟨ψ.1, Submodule.mem_inf.2 ⟨ψ.2, LinearMap.mem_ker.2
    (LinearMap.ext fun z => by
      change F.X (ψ.1 z) - (0 : ℤ).negOnePow • ψ.1 (N.X z) = 0
      rw [hψX, Int.negOnePow_zero, one_smul, sub_self])⟩⟩
  let zφ : Z0 F N := ⟨φ.1, Submodule.mem_inf.2 ⟨φ.2, LinearMap.mem_ker.2
    (LinearMap.ext fun z => by
      change N.X (φ.1 z) - (0 : ℤ).negOnePow • φ.1 (F.X z) = 0
      rw [hφX, Int.negOnePow_zero, one_smul, sub_self])⟩⟩
  refine ⟨{ hom := Submodule.Quotient.mk zψ, inv := Submodule.Quotient.mk zφ,
            hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · exact congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext hb'))
  · exact congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.ext ha))

end Cohesive
