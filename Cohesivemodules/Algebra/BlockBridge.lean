import Cohesivemodules.Algebra.BlockBridgeSwap

set_option linter.style.header false

/-!
# A13: bridge between Block's right modules and the left-module definition (part 2 of 2)

Split from `Algebra/BlockBridge.lean` for size;
continues `Algebra/BlockBridgeSwap.lean`.
-/

namespace Cohesive
open TensorProduct DirectSum
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
variable {cB : A}

namespace QuasiCohesive

variable (M : QuasiCohesive 𝒜)

/-- A13: the left operator transported to Block's total module, `𝔼 = σ⁻¹ ∘ 𝕏 ∘ σ`. -/
def blockE : TotR 𝒜 M.Q →ₗ[k] TotR 𝒜 M.Q :=
  (blockSwap 𝒜 M.Q).symm.toLinearMap ∘ₗ M.X ∘ₗ (blockSwap 𝒜 M.Q).toLinearMap

/-- A13: formula for `blockE`. -/
theorem blockE_apply (x : TotR 𝒜 M.Q) :
    M.blockE x = (blockSwap 𝒜 M.Q).symm (M.X (blockSwap 𝒜 M.Q x)) := rfl

/-- A13: `blockE` has total degree `1`. -/
theorem blockE_mem {m : ℤ} {x : TotR 𝒜 M.Q} (hx : x ∈ totDegR 𝒜 M.Q m) :
    M.blockE x ∈ totDegR 𝒜 M.Q (m + 1) := by
  rw [← blockSwap_mem_totDeg_iff, blockE_apply, LinearEquiv.apply_symm_apply]
  exact M.X_mem (blockSwap_mem_totDeg_iff.2 hx)

/-- A13: `σ(𝔼 y) = 𝕏(σ y)`. -/
private theorem blockSwap_blockE (y : TotR 𝒜 M.Q) :
    blockSwap 𝒜 M.Q (M.blockE y) = M.X (blockSwap 𝒜 M.Q y) := by
  rw [blockE_apply, LinearEquiv.apply_symm_apply]

/-- A13: Block's Leibniz rule for the transported operator, `ω` homogeneous. -/
private theorem blockE_leibniz_hom {u r : ℤ} (e : M.Q u) {ω : A} (hω : ω ∈ 𝒜 r) :
    M.blockE (TotR.tmul 𝒜 M.Q (lof (𝒜 0) ℤ M.Q u e) ω) =
      TotR.rAct 𝒜 M.Q ω (M.blockE (TotR.tmul 𝒜 M.Q (lof (𝒜 0) ℤ M.Q u e) 1)) +
        u.negOnePow • TotR.tmul 𝒜 M.Q (lof (𝒜 0) ℤ M.Q u e) (GCDga.d (𝒜 := 𝒜) ω) := by
  apply (blockSwap 𝒜 M.Q).injective
  have hy1 : TotR.tmul 𝒜 M.Q (lof (𝒜 0) ℤ M.Q u e) 1 ∈ totDegR 𝒜 M.Q (u + 0) :=
    Submodule.subset_span ⟨u, 0, e, 1, rfl, SetLike.GradedOne.one_mem (A := 𝒜), rfl⟩
  have hE1 := M.blockE_mem hy1
  have hσ1 := blockSwap_tmul (Q := M.Q) e (SetLike.GradedOne.one_mem (A := 𝒜))
  have hσω := blockSwap_tmul (Q := M.Q) e hω
  have hσd := blockSwap_tmul (Q := M.Q) e (GCDga.d_mem (𝒜 := 𝒜) hω)
  have hσr := blockSwap_rAct hω hE1
  have hL := M.leibniz hω (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q u e))
  rw [mul_zero, Int.negOnePow_zero, one_smul] at hσ1
  rw [Tot.tmul_eq_smul] at hσω hσd
  have hXu : ∀ (v : ℤˣ) (z : Tot 𝒜 M.Q), M.X (v • z) = v • M.X z := fun v z => by
    simp only [Units.smul_def, map_zsmul]
  have e1 : (u * r).negOnePow * r.negOnePow = (r * (u + 0 + 1)).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  have e2 : u.negOnePow * (u * (r + 1)).negOnePow = (u * r).negOnePow := by
    rw [← Int.negOnePow_add, show u + u * (r + 1) = u * r + 2 * u by ring, Int.negOnePow_add,
      Int.negOnePow_two_mul, mul_one]
  rw [map_add, hσr, blockSwap_units_smul, hσd, blockSwap_blockE, blockSwap_blockE, hσω, hσ1,
    hXu, hL, smul_add, smul_smul, e1, ← e2, mul_smul]
  abel

/-- A13: the left Leibniz rule becomes Block's `𝔼(e ω) = 𝔼(e ⊗ 1) ω + (-1)^{|e|} e dω`. -/
theorem blockE_leibniz {p : ℤ} (e : M.Q p) (ω : A) :
    M.blockE (TotR.tmul 𝒜 M.Q (lof (𝒜 0) ℤ M.Q p e) ω) =
      TotR.rAct 𝒜 M.Q ω (M.blockE (TotR.tmul 𝒜 M.Q (lof (𝒜 0) ℤ M.Q p e) 1)) +
        p.negOnePow • TotR.tmul 𝒜 M.Q (lof (𝒜 0) ℤ M.Q p e) (GCDga.d (𝒜 := 𝒜) ω) := by
  induction ω using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero =>
    simp only [totR_tmul_zero, map_zero, totR_rAct_zero, smul_zero, add_zero]
  | homogeneous ω => exact M.blockE_leibniz_hom e ω.2
  | add x y hx hy =>
    rw [totR_tmul_add, map_add, hx, hy, totR_rAct_add, map_add, totR_tmul_add, smul_add]
    abel

/-- A13: flatness `𝕏 ∘ 𝕏 = c·(-)` becomes Block's integrability `𝔼 ∘ 𝔼 + (·cB) = 0` for
`cB = -c`. -/
theorem blockE_integrable (h : GCDga.c (𝒜 := 𝒜) = -cB) (x : TotR 𝒜 M.Q) :
    M.blockE (M.blockE x) + TotR.rAct 𝒜 M.Q cB x = 0 := by
  have hcB : cB ∈ 𝒜 2 := by
    have := GCDga.c_mem (𝒜 := 𝒜)
    rwa [h, neg_mem_iff] at this
  apply (blockSwap 𝒜 M.Q).injective
  rw [map_add, blockSwap_blockE, blockSwap_blockE, blockSwap_rAct_two hcB, M.flat, h, neg_smul,
    map_zero, neg_add_cancel]

variable (cB) in
/-- **A13.** A left quasi-cohesive module over `(A, d, c)` as a quasi-cohesive module in Block's
convention over `(A, d, cB)`, `cB = -c`: same generators, operator `σ⁻¹ ∘ 𝕏 ∘ σ`. -/
def toBlock (h : GCDga.c (𝒜 := 𝒜) = -cB) : BlockQuasiCohesive 𝒜 cB where
  Q := M.Q
  E := M.blockE
  E_mem := M.blockE_mem
  leibniz := M.blockE_leibniz
  integrable := M.blockE_integrable h

end QuasiCohesive

/-- **A13.** Block's convention → left convention → Block's convention is the identity. -/
theorem BlockQuasiCohesive.toBlock_toLeft (E : BlockQuasiCohesive 𝒜 cB)
    (h : GCDga.c (𝒜 := 𝒜) = -cB) : (E.toLeft h).toBlock cB h = E := by
  have hE : (E.toLeft h).blockE = E.E := by
    refine LinearMap.ext fun (x : TotR 𝒜 E.Q) => ?_
    show (blockSwap 𝒜 E.Q).symm (E.leftX (blockSwap 𝒜 E.Q x)) = E.E x
    rw [E.leftX_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  revert hE
  cases E
  intro hE
  unfold QuasiCohesive.toBlock
  simp only [BlockQuasiCohesive.mk.injEq]
  exact ⟨rfl, HEq.rfl, HEq.rfl, heq_of_eq hE⟩

/-- **A13.** Left convention → Block's convention → left convention is the identity. -/
theorem QuasiCohesive.toLeft_toBlock (M : QuasiCohesive 𝒜) (h : GCDga.c (𝒜 := 𝒜) = -cB) :
    (M.toBlock cB h).toLeft h = M := by
  have hX : (M.toBlock cB h).leftX = M.X := by
    refine LinearMap.ext fun (x : Tot 𝒜 M.Q) => ?_
    show blockSwap 𝒜 M.Q (M.blockE ((blockSwap 𝒜 M.Q).symm x)) = M.X x
    rw [QuasiCohesive.blockE_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  revert hX
  cases M
  intro hX
  unfold BlockQuasiCohesive.toLeft
  simp only [QuasiCohesive.mk.injEq]
  exact ⟨rfl, HEq.rfl, HEq.rfl, heq_of_eq hX⟩

/-- **A13.** A cohesive module in Block's convention [B, Def 2.3.2(1)] as a cohesive module
(A3); the finiteness conditions are the same. -/
def BlockCohesive.toLeft (E : BlockCohesive 𝒜 cB) (h : GCDga.c (𝒜 := 𝒜) = -cB) :
    CohesiveModule 𝒜 where
  toQuasiCohesive := E.toBlockQuasiCohesive.toLeft h
  bounded := E.bounded
  finite := E.finite
  projective := E.projective

/-- **A13.** A cohesive module (A3) as a cohesive module in Block's convention. -/
def CohesiveModule.toBlock (M : CohesiveModule 𝒜) (cB : A) (h : GCDga.c (𝒜 := 𝒜) = -cB) :
    BlockCohesive 𝒜 cB where
  toBlockQuasiCohesive := M.toQuasiCohesive.toBlock cB h
  bounded := M.bounded
  finite := M.finite
  projective := M.projective

/-! ## Morphisms -/

namespace BlockQuasiCohesive

variable {E₁ E₂ E₃ : BlockQuasiCohesive 𝒜 cB} (h : GCDga.c (𝒜 := 𝒜) = -cB)

/-- **A13.** Conjugation by `σ`: Block's maps `E₁ ⊗ A → E₂ ⊗ A` as maps of left total modules,
`φ ↦ σ ∘ φ ∘ σ⁻¹`. -/
def blockConj : (E₁.T →ₗ[k] E₂.T) ≃ₗ[k] ((E₁.toLeft h).T →ₗ[k] (E₂.toLeft h).T) :=
  LinearEquiv.arrowCongr (blockSwap 𝒜 E₁.Q) (blockSwap 𝒜 E₂.Q)

/-- A13: formula for `blockConj`. -/
theorem blockConj_apply (φ : E₁.T →ₗ[k] E₂.T) (x : (E₁.toLeft h).T) :
    blockConj h φ x = blockSwap 𝒜 E₂.Q (φ ((blockSwap 𝒜 E₁.Q).symm x)) := rfl

/-- A13: `blockConj φ (σ y) = σ (φ y)`. -/
private theorem blockConj_swap (φ : E₁.T →ₗ[k] E₂.T) (y : TotR 𝒜 E₁.Q) :
    blockConj h φ (blockSwap 𝒜 E₁.Q y) = blockSwap 𝒜 E₂.Q (φ y) := by
  show blockSwap 𝒜 E₂.Q (φ ((blockSwap 𝒜 E₁.Q).symm (blockSwap 𝒜 E₁.Q y))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- A13: on a homogeneous `y` with `φ y` homogeneous of degree `m + n`, right linearity of `φ`
at `(a, y)` is the sign-twisted left linearity of `σ φ σ⁻¹` at `(a, σ y)`. -/
private theorem conj_pure_iff {n p m : ℤ} {a : A} (ha : a ∈ 𝒜 p) {y : TotR 𝒜 E₁.Q}
    (hy : y ∈ totDegR 𝒜 E₁.Q m) (φ : E₁.T →ₗ[k] E₂.T) (hφy : φ y ∈ totDegR 𝒜 E₂.Q (m + n)) :
    φ (TotR.rAct 𝒜 E₁.Q a y) = TotR.rAct 𝒜 E₂.Q a (φ y) ↔
      blockConj h φ (a • blockSwap 𝒜 E₁.Q y) =
        (n * p).negOnePow • a • blockConj h φ (blockSwap 𝒜 E₁.Q y) := by
  have h1 : (blockSwap 𝒜 E₁.Q).symm (a • blockSwap 𝒜 E₁.Q y) =
      (p * m).negOnePow • TotR.rAct 𝒜 E₁.Q a y := by
    apply (blockSwap 𝒜 E₁.Q).injective
    rw [LinearEquiv.apply_symm_apply, blockSwap_units_smul, blockSwap_rAct ha hy, smul_smul,
      Int.units_mul_self, one_smul]
  have h2 := blockSwap_rAct ha hφy
  have hφu : ∀ (u : ℤˣ) (w : TotR 𝒜 E₁.Q), φ (u • w) = u • φ w := fun u w => by
    simp only [Units.smul_def, map_zsmul]
  have hst : (p * m).negOnePow * (p * (m + n)).negOnePow = (n * p).negOnePow := by
    rw [← Int.negOnePow_add, show p * m + p * (m + n) = n * p + 2 * (p * m) by ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]
  have hst' : (p * m).negOnePow * (n * p).negOnePow = (p * (m + n)).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  rw [blockConj_swap, show blockConj h φ (a • blockSwap 𝒜 E₁.Q y) =
    blockSwap 𝒜 E₂.Q (φ ((blockSwap 𝒜 E₁.Q).symm (a • blockSwap 𝒜 E₁.Q y))) from rfl, h1, hφu,
    blockSwap_units_smul]
  constructor
  · intro h3
    rw [h3, h2, smul_smul, hst]
    rfl
  · intro h3
    apply (blockSwap 𝒜 E₂.Q).injective
    rw [h2]
    have h3' : (p * m).negOnePow • blockSwap 𝒜 E₂.Q (φ (TotR.rAct 𝒜 E₁.Q a y)) =
        (n * p).negOnePow • a • blockSwap 𝒜 E₂.Q (φ y) := h3
    have h4 := congrArg (fun z => (p * m).negOnePow • z) h3'
    beta_reduce at h4
    rw [smul_smul, smul_smul, Int.units_mul_self, one_smul, hst'] at h4
    exact h4

/-- **A13.** Block's morphisms of degree `n` (right `A`-linear) are exactly the maps whose
conjugate lies in `Hom^n` (A4: `φ(a·x) = (-1)^{n|a|} a·φ(x)`). -/
theorem mem_hom_blockConj_iff {n : ℤ} {φ : E₁.T →ₗ[k] E₂.T} :
    blockConj h φ ∈ Hom (E₁.toLeft h) (E₂.toLeft h) n ↔ φ ∈ BlockHom E₁ E₂ n := by
  constructor
  · rintro ⟨hd, hl⟩
    have hd' : ∀ {m : ℤ} {x : E₁.T}, x ∈ totDegR 𝒜 E₁.Q m → φ x ∈ totDegR 𝒜 E₂.Q (m + n) := by
      intro m x hx
      have h1 : blockSwap 𝒜 E₁.Q x ∈ totDeg 𝒜 E₁.Q m := blockSwap_mem_totDeg_iff.2 hx
      have h2 : blockSwap 𝒜 E₂.Q (φ x) ∈ totDeg 𝒜 E₂.Q (m + n) := by
        rw [← blockConj_swap h φ x]
        exact hd h1
      exact blockSwap_mem_totDeg_iff.1 h2
    refine ⟨hd', fun a x => ?_⟩
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => rw [totR_rAct_zero, map_zero, totR_rAct_zero]
    | add a b ha hb => rw [totR_rAct_add, map_add, ha, hb, totR_rAct_add]
    | homogeneous a =>
      refine totR_induction (C := fun x => φ (TotR.rAct 𝒜 E₁.Q a x) =
        TotR.rAct 𝒜 E₂.Q a (φ x)) x ?_ ?_ ?_
      · simp only [map_zero]
      · intro y z hy hz
        rw [map_add, map_add, map_add, map_add, hy, hz]
      · intro u r e b hb
        have hy : TotR.tmul 𝒜 E₁.Q (lof (𝒜 0) ℤ E₁.Q u e) b ∈ totDegR 𝒜 E₁.Q (u + r) :=
          Submodule.subset_span ⟨u, r, e, b, rfl, hb, rfl⟩
        exact (conj_pure_iff h a.2 hy φ (hd' hy)).2 (hl a.2 _)
  · rintro ⟨hd', hr⟩
    refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
    · have hx' : (blockSwap 𝒜 E₁.Q).symm x ∈ totDegR 𝒜 E₁.Q m := by
        rw [← blockSwap_mem_totDeg_iff]
        have e : blockSwap 𝒜 E₁.Q ((blockSwap 𝒜 E₁.Q).symm x) = x :=
          LinearEquiv.apply_symm_apply _ x
        exact (congrArg (· ∈ totDeg 𝒜 E₁.Q m) e).mpr hx
      exact blockSwap_mem_totDeg_iff.2 (hd' hx')
    · obtain ⟨y, rfl⟩ := (blockSwap 𝒜 E₁.Q).surjective x
      refine totR_induction (C := fun y => blockSwap 𝒜 E₂.Q
          (φ ((blockSwap 𝒜 E₁.Q).symm (a • blockSwap 𝒜 E₁.Q y))) =
        (n * p).negOnePow • a • blockSwap 𝒜 E₂.Q
          (φ ((blockSwap 𝒜 E₁.Q).symm (blockSwap 𝒜 E₁.Q y)))) y ?_ ?_ ?_
      · simp only [map_zero, smul_zero]
      · intro y z hy hz
        simp only [map_add, smul_add] at hy hz ⊢
        rw [hy, hz]
      · intro u r e b hb
        have hy : TotR.tmul 𝒜 E₁.Q (lof (𝒜 0) ℤ E₁.Q u e) b ∈ totDegR 𝒜 E₁.Q (u + r) :=
          Submodule.subset_span ⟨u, r, e, b, rfl, hb, rfl⟩
        exact (conj_pure_iff h ha hy φ (hd' hy)).1 (hr a _)

/-- **A13.** Block's differential is the differential `δ` of A4 under conjugation. -/
theorem blockConj_δ (n : ℤ) (φ : E₁.T →ₗ[k] E₂.T) :
    blockConj h (blockδ E₁ E₂ n φ) = δ (E₁.toLeft h) (E₂.toLeft h) n (blockConj h φ) := by
  have key : ∀ y : Tot 𝒜 E₁.Q,
      blockSwap 𝒜 E₂.Q (E₂.E (φ ((blockSwap 𝒜 E₁.Q).symm y)) -
        n.negOnePow • φ (E₁.E ((blockSwap 𝒜 E₁.Q).symm y))) =
      E₂.leftX (blockSwap 𝒜 E₂.Q (φ ((blockSwap 𝒜 E₁.Q).symm y))) -
        n.negOnePow • blockSwap 𝒜 E₂.Q (φ ((blockSwap 𝒜 E₁.Q).symm (E₁.leftX y))) := by
    intro y
    rw [map_sub, blockSwap_units_smul, E₂.leftX_apply, LinearEquiv.symm_apply_apply, E₁.leftX_apply,
      LinearEquiv.symm_apply_apply]
  refine LinearMap.ext fun x => ?_
  exact key x

/-- **A13.** Conjugation preserves composition. -/
theorem blockConj_comp (ψ : E₂.T →ₗ[k] E₃.T) (φ : E₁.T →ₗ[k] E₂.T) :
    blockConj h (ψ ∘ₗ φ) = blockConj h ψ ∘ₗ blockConj h φ := by
  refine LinearMap.ext fun x => ?_
  show blockSwap 𝒜 E₃.Q (ψ (φ ((blockSwap 𝒜 E₁.Q).symm x))) =
    blockSwap 𝒜 E₃.Q (ψ ((blockSwap 𝒜 E₂.Q).symm (blockSwap 𝒜 E₂.Q
      (φ ((blockSwap 𝒜 E₁.Q).symm x)))))
  rw [LinearEquiv.symm_apply_apply]

/-- **A13.** Conjugation preserves identities. -/
theorem blockConj_id : blockConj (E₁ := E₁) (E₂ := E₁) h LinearMap.id = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  exact LinearEquiv.apply_symm_apply (blockSwap 𝒜 E₁.Q) x

/-- A13: conjugation maps Block's `Hom^n` onto `Hom^n`. -/
theorem map_blockHom (n : ℤ) :
    (BlockHom E₁ E₂ n).map (blockConj h).toLinearMap = Hom (E₁.toLeft h) (E₂.toLeft h) n := by
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact (mem_hom_blockConj_iff h).2 hφ
  · intro hψ
    refine ⟨(blockConj h).symm ψ, (mem_hom_blockConj_iff h).1 ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [LinearEquiv.apply_symm_apply]
    exact hψ

/-- **A13.** Block's Hom complex is isomorphic to the Hom complex of A4, degree by degree; with
`blockConj_δ`, `blockConj_comp`, `blockConj_id` (and the bijection on objects
`toBlock_toLeft`, `toLeft_toBlock`) this is a dg-isomorphism between Block's `P_A` and the
left-module `P_A`. -/
def blockHomEquiv (n : ℤ) :
    BlockHom E₁ E₂ n ≃ₗ[k] Hom (E₁.toLeft h) (E₂.toLeft h) n :=
  (blockConj h).ofSubmodules _ _ (map_blockHom h n)

end BlockQuasiCohesive

end Cohesive
