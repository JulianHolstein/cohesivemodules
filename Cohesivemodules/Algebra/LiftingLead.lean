import Cohesivemodules.Algebra.LiftingHomT

set_option linter.style.header false

/-!
# A11–A12: the lifting theorem (part 2 of 3)

Split from `Algebra/Lifting.lean` for size;
continues `Algebra/LiftingHomT.lean`.
-/

noncomputable section
namespace Cohesive
open TensorProduct DirectSum
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-! ## Leading operators -/

section Leading

variable {Q₁ Q₂ : ℤ → Type} [∀ p, AddCommGroup (Q₁ p)] [∀ p, Module (𝒜 0) (Q₁ p)]
  [∀ p, AddCommGroup (Q₂ p)] [∀ p, Module (𝒜 0) (Q₂ p)]

/-- A11: `1 ⊗ e` has total degree `m` if `e` is concentrated in degree `m`. -/
theorem tmul_one_mem_totDeg_of_concAt {m : ℤ} {e : ⨁ p, Q₂ p} (h : Tot.ConcAt m e) :
    Tot.tmul 𝒜 Q₂ 1 e ∈ totDeg 𝒜 Q₂ m := by
  have he : e = DirectSum.of Q₂ m (e m) := by
    ext i
    by_cases hi : i = m
    · subst hi
      rw [DirectSum.of_eq_same]
    · rw [h i hi, DirectSum.of_eq_of_ne m i (e m) hi]
  rw [he]
  have := tmul_mem_totDeg (Q := Q₂) (SetLike.GradedOne.one_mem (A := 𝒜)) (e m)
  rwa [zero_add] at this

/-- A11: the extension `ĝ(a ⊗ e) = (-1)^{n|a|} a ⊗ g(e)` of an `A⁰`-linear map of generators
(`∂̂`, `𝕏̂⁰` with `n = 1`, `ê₀` with `n = 0`). It preserves form degrees. -/
def hatGen (n : ℤ) (g : (⨁ p, Q₁ p) →ₗ[𝒜 0] (⨁ p, Q₂ p)) : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂ :=
  extT n ((Tot.oneTmul 𝒜 Q₂).toAddMonoidHom.comp g.toAddMonoidHom) fun f e => by
    show Tot.oneTmul 𝒜 Q₂ (g (f • e)) = (f : A) • Tot.oneTmul 𝒜 Q₂ (g e)
    rw [g.map_smul, (Tot.oneTmul 𝒜 Q₂).map_smul, Tot.smul0_eq]

/-- A11: `ĝ ∈ HomT^n` when `g` has degree `n`. -/
theorem hatGen_mem {n : ℤ} {g : (⨁ p, Q₁ p) →ₗ[𝒜 0] (⨁ p, Q₂ p)}
    (hg : ∀ p (e : Q₁ p), Tot.ConcAt (p + n) (g (lof (𝒜 0) ℤ Q₁ p e))) :
    hatGen n g ∈ HomT 𝒜 Q₁ Q₂ n :=
  extT_mem n _ _ fun p e => tmul_one_mem_totDeg_of_concAt (hg p e)

/-- A11: `ĝ(1 ⊗ e) = 1 ⊗ g(e)`. -/
theorem hatGen_tmul_one (n : ℤ) (g : (⨁ p, Q₁ p) →ₗ[𝒜 0] (⨁ p, Q₂ p)) (e : ⨁ p, Q₁ p) :
    hatGen n g (Tot.tmul 𝒜 Q₁ 1 e) = Tot.tmul 𝒜 Q₂ 1 (g e) :=
  extT_tmul_one n _ _ e

/-- A11: the augmentation `ε` (form-degree-`0` part) vanishes on `F^1`. -/
theorem eps_eq_zero_of_mem {y : Tot 𝒜 Q₂} (hy : y ∈ filTot 𝒜 Q₂ 1) : Tot.eps 𝒜 Q₂ y = 0 := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hq, ha, rfl⟩ := hx
    rw [Tot.eps_tmul, Tot.proj0_of_mem_ne ha (by omega), zero_smul]
  | zero => rw [map_zero]
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [← algebraMap_smul A r x, Tot.eps_smul, hx, smul_zero]

/-- A11: the sign twist commutes with the homogeneous projections: `π_j ∘ τ_n = τ_n ∘ π_j`. -/
theorem proj_twist (n j : ℤ) (a : A) :
    GCDga.proj 𝒜 j (GCDga.twist 𝒜 n a) = GCDga.twist 𝒜 n (GCDga.proj 𝒜 j a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | @homogeneous i x =>
    rw [GCDga.twist_of_mem 𝒜 n x.2, Units.smul_def, map_zsmul, GCDga.proj_of_mem 𝒜 x.2]
    split_ifs with h
    · rw [GCDga.twist_of_mem 𝒜 n x.2, Units.smul_def]
    · rw [map_zero, zsmul_zero]

/-- A11: `ĝ(a ⊗ e) = τₙ(a) ⊗ g(e)`. -/
theorem hatGen_tmul (n : ℤ) (g : (⨁ p, Q₁ p) →ₗ[𝒜 0] (⨁ p, Q₂ p)) (a : A) (e : ⨁ p, Q₁ p) :
    hatGen n g (Tot.tmul 𝒜 Q₁ a e) = Tot.tmul 𝒜 Q₂ (GCDga.twist 𝒜 n a) (g e) := by
  rw [hatGen, extT_tmul]
  show GCDga.twist 𝒜 n a • Tot.tmul 𝒜 Q₂ 1 (g e) = _
  rw [Tot.smul_tmul, mul_one]

/-- A11: `ĝ` commutes with the form-degree projections. -/
theorem projF_hatGen (n j : ℤ) (g : (⨁ p, Q₁ p) →ₗ[𝒜 0] (⨁ p, Q₂ p)) (x : Tot 𝒜 Q₁) :
    Tot.projF 𝒜 Q₂ j (hatGen n g x) = hatGen n g (Tot.projF 𝒜 Q₁ j x) := by
  induction x using Tot.induction_on with
  | ht a e => rw [hatGen_tmul, Tot.projF_tmul, Tot.projF_tmul, hatGen_tmul, proj_twist]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- A11: `ĝ` preserves the form-degree filtration. -/
theorem hatGen_mem_filTot (n : ℤ) (g : (⨁ p, Q₁ p) →ₗ[𝒜 0] (⨁ p, Q₂ p)) {c : ℤ}
    {x : Tot 𝒜 Q₁} (hx : x ∈ filTot 𝒜 Q₁ c) : hatGen n g x ∈ filTot 𝒜 Q₂ c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hcq, ha, rfl⟩ := hx
    rw [hatGen_tmul, GCDga.twist_of_mem 𝒜 n ha, Tot.tmul_units_smul]
    exact Submodule.smul_of_tower_mem _ _ (tmul_mem_filTot hcq ha _)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- A11: `D` has leading operator `D₀`: `D - D₀` raises the form-degree filtration by `1`. -/
def LeadsTo (D : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁) (D₀ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁) : Prop :=
  ∀ (c : ℤ) (x : Tot 𝒜 Q₁), x ∈ filTot 𝒜 Q₁ c → D x - D₀ x ∈ filTot 𝒜 Q₁ (c + 1)

/-- A11: an operator with leading operator `ĝ` preserves the form-degree filtration. -/
theorem lead_mem_filTot {D : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁} {g : (⨁ p, Q₁ p) →ₗ[𝒜 0] (⨁ p, Q₁ p)}
    {n : ℤ} (h : LeadsTo D (hatGen n g)) {c : ℤ} {x : Tot 𝒜 Q₁} (hx : x ∈ filTot 𝒜 Q₁ c) :
    D x ∈ filTot 𝒜 Q₁ c := by
  have := add_mem (filTot_anti (by omega) (h c x hx)) (hatGen_mem_filTot n g hx)
  rwa [sub_add_cancel] at this

/-- A11: `δT` of `φ ∈ F^b` with leading operators: the pure part of degree `b` of `δφ` is
`δ⁰` of the pure part, `δ⁰` built from the leading operators `hatGen 1 g₁`, `hatGen 1 g₂`. -/
theorem pure_δT {D₁ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁} {D₂ : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₂}
    {g₁ : (⨁ p, Q₁ p) →ₗ[𝒜 0] (⨁ p, Q₁ p)} {g₂ : (⨁ p, Q₂ p) →ₗ[𝒜 0] (⨁ p, Q₂ p)}
    (hg₁ : ∀ p (e : Q₁ p), Tot.ConcAt (p + 1) (g₁ (lof (𝒜 0) ℤ Q₁ p e)))
    (hg₂ : ∀ p (e : Q₂ p), Tot.ConcAt (p + 1) (g₂ (lof (𝒜 0) ℤ Q₂ p e)))
    (hD₁ : IsDiffOp D₁) (hD₂ : IsDiffOp D₂) (hl₁ : LeadsTo D₁ (hatGen 1 g₁))
    (hl₂ : LeadsTo D₂ (hatGen 1 g₂)) {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂}
    (hφ : φ ∈ FT 𝒜 Q₁ Q₂ n b) :
    δT D₁ D₂ n φ ∈ FT 𝒜 Q₁ Q₂ (n + 1) b ∧
      ∀ h : δT D₁ D₂ n φ ∈ HomT 𝒜 Q₁ Q₂ (n + 1), pure b (δT D₁ D₂ n φ) h =
        δT (hatGen 1 g₁) (hatGen 1 g₂) n (pure b φ (Submodule.mem_inf.1 hφ).1) := by
  obtain ⟨hφ₁, hφ₂⟩ := Submodule.mem_inf.1 hφ
  refine ⟨Submodule.mem_inf.2 ⟨δT_mem_of_diff hD₁ hD₂ hφ₁, fun c x hx => ?_⟩, fun h => ?_⟩
  · simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Units.smul_def]
    refine sub_mem (lead_mem_filTot hl₂ (hφ₂ c x hx))
      (Submodule.smul_of_tower_mem _ _ (hφ₂ c _ (lead_mem_filTot hl₁ hx)))
  · refine homT_ext (pure_mem h) (δT_mem_of_hom (hatGen_mem hg₁) (hatGen_mem hg₂)
      (pure_mem hφ₁)) fun e => ?_
    have hy := (memFT_iff hφ₁).1 hφ e
    -- `D₂ (φ y) ≡ ĝ₂ (φ y)` and `φ (D₁ y) ≡ φ (ĝ₁ y)` modulo `F^{b+1}`
    have h₂ := hl₂ b _ hy
    have h₁ : φ (D₁ (Tot.tmul 𝒜 Q₁ 1 e)) - φ (hatGen 1 g₁ (Tot.tmul 𝒜 Q₁ 1 e)) ∈
        filTot 𝒜 Q₂ (b + 1) := by
      rw [← map_sub]
      have := hφ₂ 1 _ (by simpa using hl₁ 0 _ (filTot_zero (Tot.tmul 𝒜 Q₁ 1 e)))
      rwa [add_comm] at this
    rw [pure_tmul_one]
    simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Units.smul_def, map_sub, map_zsmul]
    have h₂' := projF_eq_zero_of_mem h₂
    have h₁' := projF_eq_zero_of_mem h₁
    rw [map_sub, sub_eq_zero] at h₂' h₁'
    rw [h₂', h₁', hatGen_tmul_one, pure_tmul_one, pure_tmul_one, projF_hatGen,
      ← hatGen_tmul_one 1 g₁ e]

/-- A11: the pure part only depends on the map. -/
theorem pure_congr {n b : ℤ} {φ ψ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n)
    (hψ : ψ ∈ HomT 𝒜 Q₁ Q₂ n) (h : φ = ψ) : pure b φ hφ = pure b ψ hψ := by
  subst h; rfl

/-- A11: the pure part of the zero map vanishes. -/
theorem pure_of_eq_zero {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n)
    (h : φ = 0) : pure b φ hφ = 0 := by
  subst h
  refine homT_ext (pure_mem hφ) (zero_mem _) fun e => ?_
  rw [pure_tmul_one, LinearMap.zero_apply, map_zero]

/-- A11: the pure part commutes with negation. -/
theorem pure_neg {n b : ℤ} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hφ : φ ∈ HomT 𝒜 Q₁ Q₂ n)
    (hφ' : -φ ∈ HomT 𝒜 Q₁ Q₂ n) : pure b (-φ) hφ' = -pure b φ hφ := by
  refine homT_ext (pure_mem hφ') (neg_mem (pure_mem hφ)) fun e => ?_
  rw [pure_tmul_one, LinearMap.neg_apply, map_neg, LinearMap.neg_apply, pure_tmul_one]

/-- A11: `F^{b₁} ∘ F^{b₂} ⊆ F^{b₁ + b₂}`. -/
theorem comp_mem_FT {Q₃ : ℤ → Type} [∀ p, AddCommGroup (Q₃ p)] [∀ p, Module (𝒜 0) (Q₃ p)]
    {m n b₁ b₂ : ℤ} {ψ : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₃} {φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂}
    (hψ : ψ ∈ FT 𝒜 Q₂ Q₃ m b₁) (hφ : φ ∈ FT 𝒜 Q₁ Q₂ n b₂) :
    ψ ∘ₗ φ ∈ FT 𝒜 Q₁ Q₃ (m + n) (b₁ + b₂) := by
  obtain ⟨hψ₁, hψ₂⟩ := Submodule.mem_inf.1 hψ
  obtain ⟨hφ₁, hφ₂⟩ := Submodule.mem_inf.1 hφ
  refine Submodule.mem_inf.2 ⟨comp_mem_homT hψ₁ hφ₁, fun c x hx => ?_⟩
  have := hψ₂ _ _ (hφ₂ c x hx)
  rwa [add_assoc, add_comm b₂] at this

/-- A11: the pure part of `e ∘ K` is `ê ∘ (pure part of K)` when `e` has leading part `ĝ`. -/
theorem pure_comp_lead {Q₃ : ℤ → Type} [∀ p, AddCommGroup (Q₃ p)] [∀ p, Module (𝒜 0) (Q₃ p)]
    {g : (⨁ p, Q₂ p) →ₗ[𝒜 0] (⨁ p, Q₃ p)} {e : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₃}
    (he : e ∈ HomT 𝒜 Q₂ Q₃ 0) (hg : e - hatGen 0 g ∈ FT 𝒜 Q₂ Q₃ 0 1) {n b : ℤ}
    {K : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂} (hK : K ∈ FT 𝒜 Q₁ Q₂ n b)
    (h : e ∘ₗ K ∈ HomT 𝒜 Q₁ Q₃ n) :
    pure b (e ∘ₗ K) h = hatGen 0 g ∘ₗ pure b K (Submodule.mem_inf.1 hK).1 := by
  obtain ⟨hK₁, -⟩ := Submodule.mem_inf.1 hK
  obtain ⟨hg₁, hg₂⟩ := Submodule.mem_inf.1 hg
  have hĝ : hatGen 0 g ∈ HomT 𝒜 Q₂ Q₃ 0 := by
    have := sub_mem he hg₁
    rwa [sub_sub_cancel] at this
  have hc : hatGen 0 g ∘ₗ pure b K hK₁ ∈ HomT 𝒜 Q₁ Q₃ n := by
    have := comp_mem_homT hĝ (pure_mem (b := b) hK₁)
    rwa [zero_add] at this
  refine homT_ext (pure_mem h) hc fun x => ?_
  have hy := (memFT_iff hK₁).1 hK x
  have h1 : e (K (Tot.tmul 𝒜 Q₁ 1 x)) - hatGen 0 g (K (Tot.tmul 𝒜 Q₁ 1 x)) ∈
      filTot 𝒜 Q₃ (b + 1) := hg₂ b _ hy
  have h2 := projF_eq_zero_of_mem h1
  rw [map_sub, sub_eq_zero] at h2
  rw [pure_tmul_one, LinearMap.comp_apply, h2, LinearMap.comp_apply, projF_hatGen,
    pure_tmul_one]

/-- A11: `y - 1 ⊗ ε(y) ∈ F^1`: the part of form degree `0` is `1 ⊗ ε(y)`. -/
theorem sub_tmul_eps_mem (y : Tot 𝒜 Q₂) :
    y - Tot.tmul 𝒜 Q₂ 1 (Tot.eps 𝒜 Q₂ y) ∈ filTot 𝒜 Q₂ 1 := by
  have h : Tot.projF 𝒜 Q₂ 0 y = Tot.tmul 𝒜 Q₂ 1 (Tot.eps 𝒜 Q₂ y) := by
    induction y using Tot.induction_on with
    | ht a e =>
      rw [Tot.projF_tmul, Tot.eps_tmul, Tot.tmul_smul0, one_mul]
      rfl
    | hadd x y hx hy => rw [map_add, hx, hy, map_add, Tot.tmul_add]
  have := sub_projF_mem_filTot (filTot_zero (Q := Q₂) y)
  rwa [h, zero_add] at this

/-- A11: the operator of a quasi-cohesive module has leading operator `𝕏̂⁰`. -/
theorem X_lead (M : QuasiCohesive 𝒜) : LeadsTo M.X (hatGen 1 M.X0) := by
  intro c x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hcq, ha, rfl⟩ := hx
    rw [hatGen_tmul, GCDga.twist_of_mem 𝒜 1 ha, one_mul, Tot.tmul_units_smul,
      Tot.tmul_eq_smul a (M.X0 e), Tot.tmul_eq_smul a e, M.leibniz ha, Units.smul_def,
      Units.smul_def, add_sub_assoc, ← smul_sub, ← smul_sub]
    have hX0 : M.X0 e = Tot.eps 𝒜 M.Q (M.X (Tot.tmul 𝒜 M.Q 1 e)) := rfl
    refine add_mem ?_ (Submodule.smul_of_tower_mem _ _ ?_)
    · have := smul_mem_filTot (GCDga.d_mem (𝒜 := 𝒜) ha) (filTot_zero (Tot.tmul 𝒜 M.Q 1 e))
      exact filTot_anti (by omega) this
    · rw [hX0]
      exact filTot_anti (by omega) (smul_mem_filTot ha (sub_tmul_eps_mem _))
  | zero => rw [map_zero, map_zero, sub_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, map_add, add_sub_add_comm]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul, map_smul, ← smul_sub]; exact Submodule.smul_mem _ r hx

end Leading

/-! ## Modifying generator data -/

section Modify

variable {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- A11: `τ₁ = σ`. -/
theorem twist_one_eq_sigma (a : A) : GCDga.twist 𝒜 1 a = GCDga.sigma 𝒜 a := by
  rw [GCDga.twist_apply, GCDga.sigma_apply]
  simp only [one_mul]

/-- A11: generator data `θ + φ(1 ⊗ -)` for an `A⁰`-linear correction `φ ∈ HomT¹`. -/
def GenData.addHom (θ : GenData 𝒜 Q) (φ : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q) (hφ : φ ∈ HomT 𝒜 Q Q 1) :
    GenData 𝒜 Q where
  θ := θ.θ + φ.toAddMonoidHom.comp (Tot.oneTmul 𝒜 Q).toAddMonoidHom
  leibniz f e := by
    have h : φ (Tot.oneTmul 𝒜 Q (f • e)) = (f : A) • φ (Tot.oneTmul 𝒜 Q e) := by
      rw [(Tot.oneTmul 𝒜 Q).map_smul, Tot.smul0_eq, hφ.2 f.2, mul_zero, Int.negOnePow_zero,
        one_smul]
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
      LinearMap.toAddMonoidHom_coe]
    rw [θ.leibniz, h, smul_add, add_assoc]

/-- A11: the extension of generator data of total degree `1` is a Leibniz operator. -/
theorem GenData.isDiffOp (θ : GenData 𝒜 Q)
    (hθ : ∀ p (e : Q p), θ.θ (lof (𝒜 0) ℤ Q p e) ∈ totDeg 𝒜 Q (p + 1)) :
    IsDiffOp θ.extend :=
  ⟨θ.extend_mem hθ, θ.extend_leibniz⟩

/-- A11: the extension of `θ + φ(1 ⊗ -)` is `𝔼 + φ`. -/
theorem GenData.extend_addHom (θ : GenData 𝒜 Q) (φ : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q)
    (hφ : φ ∈ HomT 𝒜 Q Q 1) : (θ.addHom φ hφ).extend = θ.extend + φ := by
  ext x
  induction x using Tot.induction_on with
  | ht a e =>
    rw [LinearMap.add_apply, GenData.extend_tmul, GenData.extend_tmul, homT_tmul hφ,
      twist_one_eq_sigma]
    show _ + GCDga.sigma 𝒜 a • (θ.θ e + φ (Tot.oneTmul 𝒜 Q e)) = _
    rw [smul_add, add_assoc]
    rfl
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

end Modify

section Base

variable {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- A11: `a ⊗ x ↦ a ⊗ (x in degree p)`, from `A¹ ⊗_{A⁰} Q^p` (values of a connection) to the
total module. -/
def connTot (p : ℤ) : GCDga.piece 𝒜 1 ⊗[𝒜 0] Q p →+ Tot 𝒜 Q :=
  TensorProduct.liftAddHom (R := 𝒜 0)
    (AddMonoidHom.mk'
      (fun a => AddMonoidHom.mk' (fun x => Tot.tmul 𝒜 Q (a : A) (lof (𝒜 0) ℤ Q p x))
        (fun x x' => by rw [map_add, Tot.tmul_add]))
      (fun a a' => AddMonoidHom.ext fun x => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Submodule.coe_add,
          Tot.add_tmul]))
    fun r a x => by
      show Tot.tmul 𝒜 Q ((r • a : GCDga.piece 𝒜 1) : A) (lof (𝒜 0) ℤ Q p x) =
        Tot.tmul 𝒜 Q (a : A) (lof (𝒜 0) ℤ Q p (r • x))
      rw [GCDga.coe_smul_piece, map_smul, Tot.tmul_smul0, GCDga.central 𝒜 r.2]

/-- A11: `connTot` on pure tensors. -/
theorem connTot_tmul (p : ℤ) (a : GCDga.piece 𝒜 1) (x : Q p) :
    connTot p (a ⊗ₜ x) = Tot.tmul 𝒜 Q (a : A) (lof (𝒜 0) ℤ Q p x) := rfl

/-- A11: values of `connTot` have total degree `p + 1` and form degree `≥ 1`. -/
theorem connTot_mem (p : ℤ) (y : GCDga.piece 𝒜 1 ⊗[𝒜 0] Q p) :
    connTot p y ∈ totDeg 𝒜 Q (p + 1) ∧ connTot p y ∈ filTot 𝒜 Q 1 := by
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    rw [connTot_tmul]
    refine ⟨?_, tmul_mem_filTot le_rfl ((GCDga.mem_piece 𝒜).1 a.2) _⟩
    have := tmul_mem_totDeg (Q := Q) (𝒜 := 𝒜) ((GCDga.mem_piece 𝒜).1 a.2) x
    rwa [add_comm] at this
  | add x y hx hy => rw [map_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩

/-- A11: `connTot` is `A⁰`-linear. -/
theorem connTot_smul (p : ℤ) (f : 𝒜 0) (y : GCDga.piece 𝒜 1 ⊗[𝒜 0] Q p) :
    connTot p (f • y) = (f : A) • connTot p y := by
  induction y using TensorProduct.inductionOn with
  | tmul a x =>
    rw [TensorProduct.smul_tmul', connTot_tmul, connTot_tmul, GCDga.coe_smul_piece,
      Tot.smul_tmul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- A11: an element with vanishing augmentation lies in `F^1`. -/
theorem mem_filTot_one_of_eps {y : Tot 𝒜 Q} (h : Tot.eps 𝒜 Q y = 0) : y ∈ filTot 𝒜 Q 1 := by
  have := sub_tmul_eps_mem y
  rwa [h, Tot.tmul_zero, sub_zero] at this

/-- A11: `ε ∘ ĝ = g ∘ ε`. -/
theorem eps_hatGen {Q' : ℤ → Type} [∀ p, AddCommGroup (Q' p)] [∀ p, Module (𝒜 0) (Q' p)]
    (n : ℤ) (g : (⨁ p, Q p) →ₗ[𝒜 0] (⨁ p, Q' p)) (x : Tot 𝒜 Q) :
    Tot.eps 𝒜 Q' (hatGen n g x) = g (Tot.eps 𝒜 Q x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    have h0 : Tot.proj0 𝒜 (GCDga.twist 𝒜 n a) = Tot.proj0 𝒜 a := by
      apply Subtype.ext
      show GCDga.proj 𝒜 0 (GCDga.twist 𝒜 n a) = GCDga.proj 𝒜 0 a
      rw [proj_twist, GCDga.twist_of_mem 𝒜 n (GCDga.proj_mem 𝒜 0 a), mul_zero,
        Int.negOnePow_zero, one_smul]
    rw [hatGen_tmul, Tot.eps_tmul, Tot.eps_tmul, h0, map_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- A11: `ε ∘ D = g ∘ ε` for an operator with leading operator `ĝ`. -/
theorem eps_lead {D : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q} {g : (⨁ p, Q p) →ₗ[𝒜 0] (⨁ p, Q p)}
    (h : LeadsTo D (hatGen 1 g)) (x : Tot 𝒜 Q) : Tot.eps 𝒜 Q (D x) = g (Tot.eps 𝒜 Q x) := by
  have h1 := h 0 x (filTot_zero x)
  rw [zero_add] at h1
  have h2 := eps_eq_zero_of_mem h1
  rw [map_sub, sub_eq_zero, eps_hatGen] at h2
  exact h2

end Base

end Cohesive
end
