import Cohesivemodules.Comparison.ModelCritSite

set_option linter.style.header false

/-!
# C7.f: the quasi-isomorphism criterion for maps of `T`-complexes (part 2 of 4)

Split from `Comparison/ModelCrit.lean` for size;
continues `Comparison/ModelCritSite.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace DirectSum
variable {X : Type} [TopologicalSpace X]
namespace PreResolvingData
variable {P : PreResolvingData X} {U : Opens X}
  {F₁ F₂ : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ}
namespace ConnHom
variable {θ₁ : P.Conn U F₁} {θ₂ : P.Conn U F₂} (Φ : ConnHom θ₁ θ₂)

section ProjGen

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {Q : ℤ → Type}
  [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- `x = ∑_q π_q x`. -/
private theorem sum_projF (x : Tot 𝒜 Q) :
    ∑ q ∈ Finset.Icc (0 : ℤ) (GCDga.N 𝒜), Tot.projF 𝒜 Q q x = x := by
  induction x using Tot.induction_on with
  | ht a e =>
    simp only [Tot.projF_tmul]
    exact (Tot.tmul_eq_sum a e).symm
  | hadd x y hx hy => rw [Finset.sum_congr rfl fun q _ => map_add _ x y, Finset.sum_add_distrib,
      hx, hy]

/-- Vanishing of `π_q x` for `q < b` implies `x ∈ F^b`. -/
theorem mem_filTot_of_projF {b : ℤ} {x : Tot 𝒜 Q}
    (h : ∀ q < b, Tot.projF 𝒜 Q q x = 0) : x ∈ filTot 𝒜 Q b := by
  rw [← sum_projF x]
  refine Submodule.sum_mem _ fun q _ => ?_
  by_cases hq : q < b
  · rw [h q hq]
    exact zero_mem _
  · exact filTot_anti (not_lt.1 hq) (projF_mem_filTot q x)

/-- `π_q` kills `F^b` for `q < b`. -/
theorem projF_eq_zero_of_lt {b q : ℤ} (hq : q < b) {x : Tot 𝒜 Q}
    (hx : x ∈ filTot 𝒜 Q b) : Tot.projF 𝒜 Q q x = 0 :=
  projF_eq_zero_of_mem (filTot_anti (by omega) hx)

/-- `F^b = 0` if `A^q = 0` for `q ≥ b`. -/
theorem filTot_eq_bot_of_zero {b : ℤ} (h : ∀ q, b ≤ q → ∀ a ∈ 𝒜 q, a = 0) :
    filTot 𝒜 Q b = ⊥ := by
  rw [eq_bot_iff, filTot, Submodule.span_le]
  rintro _ ⟨q, a, e, hbq, ha, rfl⟩
  rw [h q hbq a ha, Tot.zero_tmul]
  exact zero_mem _

/-- On pure form degree `b`: `π_b 𝕏 π_b 𝕏 = 0` (when `𝕏² = 0`). -/
theorem projF_X_projF_X (M : QuasiCohesive 𝒜) (hXX : ∀ x : M.T, M.X (M.X x) = 0)
    (b : ℤ) {x : M.T} (hx : Tot.projF 𝒜 M.Q b x = x) :
    Tot.projF 𝒜 M.Q b (M.X (Tot.projF 𝒜 M.Q b (M.X x))) = 0 := by
  have h0 : x ∈ filTot 𝒜 M.Q b := hx ▸ projF_mem_filTot b x
  have h1 : M.X x ∈ filTot 𝒜 M.Q b := X_mem_filTot M h0
  have h2 : M.X x - Tot.projF 𝒜 M.Q b (M.X x) ∈ filTot 𝒜 M.Q (b + 1) := sub_projF_mem_filTot h1
  have h3 : M.X (Tot.projF 𝒜 M.Q b (M.X x)) = - M.X (M.X x - Tot.projF 𝒜 M.Q b (M.X x)) := by
    rw [map_sub, hXX, zero_sub, neg_neg]
  have h5 := X_mem_filTot M h2
  rw [h3, map_neg, projF_eq_zero_of_mem h5, neg_zero]

/-- On `F^b`: `π_b 𝕏 π_b = π_b 𝕏`. -/
theorem projF_X_projF (M : QuasiCohesive 𝒜) (b : ℤ) {x : M.T}
    (hx : x ∈ filTot 𝒜 M.Q b) :
    Tot.projF 𝒜 M.Q b (M.X (Tot.projF 𝒜 M.Q b x)) = Tot.projF 𝒜 M.Q b (M.X x) := by
  have h := projF_eq_zero_of_mem (X_mem_filTot M (sub_projF_mem_filTot hx))
  rw [map_sub, map_sub, sub_eq_zero] at h
  exact h.symm

end ProjGen

section Coord

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {Q : ℤ → Type}
  [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
  (b : ℕ) {m : ℕ} (c : Fin m → ↥(GCDga.piece 𝒜 (b : ℤ)) →ₗ[↥(𝒜 0)] ↥(𝒜 0))

/-- The coefficient of `a` along the generator `j`: `c_j(a_b)`. -/
private def coefA (j : Fin m) : A →ₗ[↥(𝒜 0)] ↥(𝒜 0) :=
  (c j) ∘ₗ (LinearMap.codRestrict (GCDga.piece 𝒜 (b : ℤ)) (GCDga.proj 𝒜 (b : ℤ))
    (fun a => GCDga.proj_mem 𝒜 _ a))

/-- The coordinate `a ⊗ e ↦ c_j(a_b) • e_p`. -/
def crdL (j : Fin m) (p : ℤ) : Tot 𝒜 Q →ₗ[↥(𝒜 0)] Q p :=
  TensorProduct.lift (LinearMap.mk₂ (↥(𝒜 0)) (fun a (e : ⨁ p, Q p) => coefA b c j a • e p)
    (fun a a' e => by simp only [map_add, add_smul])
    (fun γ a e => by rw [map_smul, smul_assoc])
    (fun a e e' => by rw [DirectSum.add_apply, smul_add])
    (fun γ a e => by rw [DirectSum.smul_apply, smul_comm]))

private theorem crdL_tmul (j : Fin m) (p : ℤ) (a : A) (e : ⨁ p, Q p) :
    crdL b c j p (Tot.tmul 𝒜 Q a e) = coefA b c j a • e p := rfl

/-- The coefficient along the generator vanishes on elements of another degree. -/
private theorem coefA_of_ne (j : Fin m) {a : A} {q : ℤ} (ha : a ∈ 𝒜 q) (h : q ≠ (b : ℤ)) :
    coefA b c j a = 0 := by
  have h1 : GCDga.proj 𝒜 (b : ℤ) a = 0 := by
    rw [GCDga.proj_of_mem 𝒜 ha]
    exact ite_eq_right_iff.2 (fun h' => absurd h' h)
  have h2 : (⟨GCDga.proj 𝒜 (b : ℤ) a, GCDga.proj_mem 𝒜 _ a⟩ :
      ↥(GCDga.piece 𝒜 (b : ℤ))) = 0 := Subtype.ext h1
  exact (congrArg (c j) h2).trans (map_zero _)

/-- The coefficient only sees the degree-`b` part. -/
private theorem coefA_proj (j : Fin m) (a : A) :
    coefA b c j (GCDga.proj 𝒜 (b : ℤ) a) = coefA b c j a := by
  have h : GCDga.proj 𝒜 (b : ℤ) (GCDga.proj 𝒜 (b : ℤ) a) = GCDga.proj 𝒜 (b : ℤ) a := by
    rw [GCDga.proj_of_mem 𝒜 (GCDga.proj_mem 𝒜 (b : ℤ) a)]
    simp only [↓reduceIte]
  have h2 : (⟨GCDga.proj 𝒜 (b : ℤ) (GCDga.proj 𝒜 (b : ℤ) a), GCDga.proj_mem 𝒜 _ _⟩ :
      ↥(GCDga.piece 𝒜 (b : ℤ))) = ⟨GCDga.proj 𝒜 (b : ℤ) a, GCDga.proj_mem 𝒜 _ a⟩ :=
    Subtype.ext h
  exact congrArg (c j) h2

/-- `crdL` only sees `π_b x`. -/
theorem crdL_projF (j : Fin m) (p : ℤ) (x : Tot 𝒜 Q) :
    crdL b c j p (Tot.projF 𝒜 Q (b : ℤ) x) = crdL b c j p x := by
  induction x using Tot.induction_on with
  | ht a e => rw [Tot.projF_tmul, crdL_tmul, crdL_tmul, coefA_proj]
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- `crdL` kills `F^{b+1}`. -/
private theorem crdL_eq_zero_of_mem (j : Fin m) (p : ℤ) {y : Tot 𝒜 Q}
    (hy : y ∈ filTot 𝒜 Q ((b : ℤ) + 1)) : crdL b c j p y = 0 := by
  rw [← crdL_projF, projF_eq_zero_of_mem hy, map_zero]

variable (s : Fin m → ↥(GCDga.piece 𝒜 (b : ℤ)))

/-- The reconstruction `z ↦ s_j ⊗ z`. -/
def recL (j : Fin m) (p : ℤ) : Q p →ₗ[↥(𝒜 0)] Tot 𝒜 Q where
  toFun z := Tot.tmul 𝒜 Q (s j : A) (lof (𝒜 0) ℤ Q p z)
  map_add' z z' := by rw [map_add, Tot.tmul_add]
  map_smul' γ z := by
    rw [map_smul, RingHom.id_apply, Tot.tmul_smul0, Tot.smul0_eq, Tot.smul_tmul]
    exact congrArg (Tot.tmul 𝒜 Q · _) (GCDga.central 𝒜 γ.2 _).symm

private theorem coefA_of_eq (j : Fin m) {a : A} (ha : a ∈ 𝒜 (b : ℤ)) :
    coefA b c j a = c j ⟨a, ha⟩ := by
  have h2 : (⟨GCDga.proj 𝒜 (b : ℤ) a, GCDga.proj_mem 𝒜 _ a⟩ :
      ↥(GCDga.piece 𝒜 (b : ℤ))) = ⟨a, ha⟩ :=
    Subtype.ext (by
      show GCDga.proj 𝒜 (b : ℤ) a = a
      rw [GCDga.proj_of_mem 𝒜 ha]
      exact ite_eq_left_iff.2 (fun h' => absurd rfl h'))
  exact congrArg (c j) h2

variable
  (he : ∀ a : ↥(GCDga.piece 𝒜 (b : ℤ)), (a : A) = ∑ j, ((c j a : ↥(𝒜 0)) : A) * (s j : A))

include he in
/-- `π_b x = ∑_j s_j ⊗ c_j(x)` on elements of total degree `n`. -/
theorem projF_eq_sum {n : ℤ} {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q n) :
    Tot.projF 𝒜 Q (b : ℤ) x =
      ∑ j, recL b s j (n + -(b : ℤ)) (crdL b c j (n + -(b : ℤ)) x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    show Tot.projF 𝒜 Q (b : ℤ) (Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e)) =
      ∑ j, recL b s j (q + p + -(b : ℤ)) (crdL b c j (q + p + -(b : ℤ))
        (Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e)))
    by_cases hq : q = (b : ℤ)
    · subst hq
      have hp : (b : ℤ) + p + -(b : ℤ) = p := by ring
      rw [hp]
      have he' : (lof (𝒜 0) ℤ Q p e) p = e := by
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
      have h1 : ∀ j, recL b s j p (crdL b c j p (Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q p e))) =
          Tot.tmul 𝒜 Q ((s j : A) * (c j ⟨a, ha⟩ : ↥(𝒜 0))) (lof (𝒜 0) ℤ Q p e) :=
        fun j => by
          rw [crdL_tmul, coefA_of_eq b c j ha]
          show Tot.tmul 𝒜 Q (s j : A) (lof (𝒜 0) ℤ Q p (c j ⟨a, ha⟩ • (lof (𝒜 0) ℤ Q p e) p)) = _
          rw [he', map_smul, Tot.tmul_smul0]
      have hs : (∑ j, (s j : A) * (c j ⟨a, ha⟩ : ↥(𝒜 0))) = a :=
        (Finset.sum_congr rfl fun j _ => (GCDga.central 𝒜 (c j ⟨a, ha⟩).2 _).symm).trans
          (he ⟨a, ha⟩).symm
      rw [Tot.projF_tmul_of_mem ha, if_pos rfl, Finset.sum_congr rfl fun j _ => h1 j]
      exact ((TensorProduct.sum_tmul _ _ _).symm.trans
        (congrArg (fun x => Tot.tmul 𝒜 Q x _) hs)).symm
    · rw [Tot.projF_tmul_of_mem ha, if_neg hq]
      symm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [crdL_tmul, coefA_of_ne b c j ha hq, zero_smul, map_zero]
  | zero => simp only [map_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [map_add, map_add]
  | smul r x _ hx =>
    rw [Tot.smul_k_eq_smul0 r x, map_smul, hx, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, map_smul]

/-- `c_j((a a')_b) = (a'_0) c_j(a)` for `a ∈ A^b`. -/
private theorem coefA_mul (j : Fin m) {a : A} (ha : a ∈ 𝒜 (b : ℤ)) (a' : A) :
    coefA b c j (a * a') = (Tot.proj0 𝒜 a' : ↥(𝒜 0)) * coefA b c j a := by
  conv_lhs => rw [← GCDga.sum_proj 𝒜 a']
  rw [Finset.mul_sum, map_sum, Finset.sum_eq_single (0 : ℤ)]
  · have hz : GCDga.proj 𝒜 0 a' ∈ 𝒜 0 := GCDga.proj_mem 𝒜 0 a'
    have h : a * GCDga.proj 𝒜 0 a' = (⟨GCDga.proj 𝒜 0 a', hz⟩ : ↥(𝒜 0)) • a := by
      rw [GCDga.smul0_def]
      exact (GCDga.central 𝒜 hz a).symm
    rw [h, map_smul, smul_eq_mul]
    rfl
  · intro q' _ hq'
    have : a * GCDga.proj 𝒜 q' a' ∈ 𝒜 ((b : ℤ) + q') :=
      SetLike.GradedMul.mul_mem ha (GCDga.proj_mem 𝒜 q' a')
    exact coefA_of_ne b c j this (by omega)
  · intro h0
    exact absurd (Finset.mem_Icc.2 ⟨le_rfl, Int.natCast_nonneg _⟩) h0

/-- `c_j(a · y)_p = c_j(a) · ε(y)_p` for `a ∈ A^b`. -/
private theorem crdL_smul_of_mem (j : Fin m) (p : ℤ) {a : A} (ha : a ∈ 𝒜 (b : ℤ))
    (y : Tot 𝒜 Q) : crdL b c j p (a • y) = coefA b c j a • Tot.eps 𝒜 Q y p := by
  induction y using Tot.induction_on with
  | ht a' e =>
    rw [Tot.smul_tmul, crdL_tmul, coefA_mul b c j ha, Tot.eps_tmul, DirectSum.smul_apply,
      mul_comm, mul_smul]
  | hadd x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add, DirectSum.add_apply, smul_add]

/-- `ℤˣ`-scalars commute with `crdL`. -/
private theorem crdL_units_smul (j : Fin m) (p : ℤ) (ε : ℤˣ) (x : Tot 𝒜 Q) :
    crdL b c j p (ε • x) = ε • crdL b c j p x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- `(𝕏⁰ e)_{p+1} = 𝕏⁰ (e_p)`. -/
private theorem X0_apply (M : QuasiCohesive 𝒜) (p : ℤ) (e : ⨁ q, M.Q q) :
    (M.X0 e) (p + 1) = M.X0comp p (e p) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply]
  | of p' z =>
    have h1 : ∀ (r : ℤ) (w : M.Q r), (lof (𝒜 0) ℤ M.Q r w) r = w := fun r w => by
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
    have h2 : ∀ (r r' : ℤ) (w : M.Q r), r ≠ r' → (lof (𝒜 0) ℤ M.Q r w) r' = 0 :=
      fun r r' w hr => by rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hr)]
    show (M.X0 (lof (𝒜 0) ℤ M.Q p' z)) (p + 1) = M.X0comp p ((lof (𝒜 0) ℤ M.Q p' z) p)
    by_cases h : p' = p
    · subst h
      rw [M.X0_lof, h1, h1]
    · rw [M.X0_lof, h2 _ _ _ (fun hh => h (by omega)), h2 _ _ _ h, map_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, hx, hy, DirectSum.add_apply, map_add]

/-- Coordinates of `𝕏 x` for `x ∈ F^b`: `c_j(𝕏 x)_{p+1} = (-1)^b 𝕏⁰ (c_j(x)_p)`. -/
theorem crdL_X (M : QuasiCohesive 𝒜) (j : Fin m) (p : ℤ) {x : Tot 𝒜 M.Q}
    (hx : x ∈ filTot 𝒜 M.Q (b : ℤ)) :
    crdL b c j (p + 1) (M.X x) = (b : ℤ).negOnePow • M.X0comp p (crdL b c j p x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hbq, ha, rfl⟩ := hx
    show crdL b c j (p + 1) (M.X (Tot.tmul 𝒜 M.Q a e)) =
      (b : ℤ).negOnePow • M.X0comp p (crdL b c j p (Tot.tmul 𝒜 M.Q a e))
    by_cases hq : q = (b : ℤ)
    · subst hq
      have h1 : crdL b c j (p + 1) (GCDga.d (𝒜 := 𝒜) a • Tot.tmul 𝒜 M.Q 1 e) = 0 := by
        rw [Tot.smul_tmul, mul_one, crdL_tmul,
          coefA_of_ne b c j (GCDga.d_mem (𝒜 := 𝒜) ha) (by omega), zero_smul]
      have h2 : Tot.eps 𝒜 M.Q (M.X (Tot.tmul 𝒜 M.Q 1 e)) (p + 1) = M.X0comp p (e p) := by
        rw [M.eps_X, ← Tot.oneTmul_apply, Tot.eps_oneTmul, X0_apply]
      rw [Tot.tmul_eq_smul, M.leibniz ha, map_add, h1, zero_add, crdL_units_smul,
        crdL_smul_of_mem b c j _ ha, h2, crdL_smul_of_mem b c j _ ha, ← Tot.oneTmul_apply,
        Tot.eps_oneTmul, map_smul]
    · have h1 : Tot.tmul 𝒜 M.Q a e ∈ filTot 𝒜 M.Q ((b : ℤ) + 1) :=
        tmul_mem_filTot (by omega) ha e
      rw [crdL_eq_zero_of_mem b c j (p + 1) (X_mem_filTot M h1), crdL_tmul,
        coefA_of_ne b c j ha hq, zero_smul, map_zero, smul_zero]
  | zero => simp only [map_zero, smul_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
  | smul r x _ hx =>
    rw [map_smul, Tot.smul_k_eq_smul0 r (M.X x), Tot.smul_k_eq_smul0 r x, map_smul, map_smul,
      map_smul, hx, smul_comm]

end Coord

section Compat

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

private theorem eps_hom_eq_lof_crit {M₁ M₂ : QuasiCohesive 𝒜}
    {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Hom M₁ M₂ 0) (p : ℤ) (e : M₁.Q p) :
    Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p e))) =
      lof (𝒜 0) ℤ M₂.Q p (comp0L hφ p e) := by
  have h1 := hφ.1 (tmul_mem_totDeg (𝒜 := 𝒜) (SetLike.GradedOne.one_mem (A := 𝒜)) e)
  rw [zero_add, add_zero] at h1
  exact eq_lof_of_concAt (Tot.eps_concAt h1)

/-- `ε(φ(1 ⊗ e))_p = φ⁰(e_p)`. -/
private theorem eps_hom_apply {M₁ M₂ : QuasiCohesive 𝒜}
    {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Hom M₁ M₂ 0) (p : ℤ) (e : ⨁ q, M₁.Q q) :
    Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 e)) p = comp0L hφ p (e p) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [Tot.tmul_zero, map_zero, DirectSum.zero_apply]
  | of p' z =>
    have h := eps_hom_eq_lof_crit hφ p' z
    change Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p' z))) p =
      comp0L hφ p ((lof (𝒜 0) ℤ M₁.Q p' z) p)
    rw [h]
    by_cases hp : p' = p
    · subst hp
      rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hp),
        DirectSum.of_eq_of_ne _ _ _ (Ne.symm hp), map_zero]
  | add x y hx hy =>
    rw [Tot.tmul_add, map_add, map_add, DirectSum.add_apply, hx, hy, DirectSum.add_apply,
      map_add]

/-- `π_0 y = 1 ⊗ ε(y)`. -/
private theorem projF_zero_eq {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (y : Tot 𝒜 Q) :
    Tot.projF 𝒜 Q 0 y = Tot.tmul 𝒜 Q 1 (Tot.eps 𝒜 Q y) := by
  induction y using Tot.induction_on with
  | ht a e => rw [Tot.projF_tmul, Tot.eps_tmul, Tot.tmul_smul0, one_mul]; rfl
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, Tot.tmul_add]

variable (b : ℕ) {m : ℕ} (c : Fin m → ↥(GCDga.piece 𝒜 (b : ℤ)) →ₗ[↥(𝒜 0)] ↥(𝒜 0))
  (s : Fin m → ↥(GCDga.piece 𝒜 (b : ℤ)))

/-- `φ⁰` is the lead term of `φ` in coordinates, on pure generators. -/
private theorem crdL_hom_tmul {M₁ M₂ : QuasiCohesive 𝒜} {φ : M₁.T →ₗ[k] M₂.T}
    (hφ : φ ∈ Hom M₁ M₂ 0) (j : Fin m) (p : ℤ) {a : A} (ha : a ∈ 𝒜 (b : ℤ))
    (e : ⨁ q, M₁.Q q) :
    crdL b c j p (φ (Tot.tmul 𝒜 M₁.Q a e)) =
      comp0L hφ p (crdL b c j p (Tot.tmul 𝒜 M₁.Q a e)) := by
  rw [Tot.tmul_eq_smul, hom0_smul hφ, crdL_smul_of_mem b c j p ha,
    crdL_smul_of_mem b c j p ha, eps_hom_apply hφ p e, ← Tot.oneTmul_apply, Tot.eps_oneTmul,
    map_smul]

/-- `c_j(φ(π_b x)) = φ⁰ c_j(x)`. -/
theorem crdL_hom_projF {M₁ M₂ : QuasiCohesive 𝒜} {φ : M₁.T →ₗ[k] M₂.T}
    (hφ : φ ∈ Hom M₁ M₂ 0) (j : Fin m) (p : ℤ) (x : Tot 𝒜 M₁.Q) :
    crdL b c j p (φ (Tot.projF 𝒜 M₁.Q (b : ℤ) x)) = comp0L hφ p (crdL b c j p x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.projF_tmul, crdL_hom_tmul b c hφ j p (GCDga.proj_mem 𝒜 _ a), crdL_tmul, crdL_tmul,
      coefA_proj]
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]

/-- `π_b φ (s_j ⊗ z) = s_j ⊗ φ⁰ z`. -/
theorem projF_hom_recL {M₁ M₂ : QuasiCohesive 𝒜} {φ : M₁.T →ₗ[k] M₂.T}
    (hφ : φ ∈ Hom M₁ M₂ 0) (j : Fin m) (p : ℤ) (z : M₁.Q p) :
    Tot.projF 𝒜 M₂.Q (b : ℤ) (φ (recL b s j p z)) = recL b s j p (comp0L hφ p z) := by
  show Tot.projF 𝒜 M₂.Q (b : ℤ) (φ (Tot.tmul 𝒜 M₁.Q (s j : A) (lof (𝒜 0) ℤ M₁.Q p z))) =
    Tot.tmul 𝒜 M₂.Q (s j : A) (lof (𝒜 0) ℤ M₂.Q p (comp0L hφ p z))
  have hs : (s j : A) ∈ 𝒜 (b : ℤ) := (s j).2
  rw [Tot.tmul_eq_smul, hom0_smul hφ, Tot.projF_smul_of_mem hs, sub_self, projF_zero_eq,
    eps_hom_eq_lof_crit hφ p z, Tot.tmul_eq_smul (s j : A)]

/-- `π_b 𝕏 (s_j ⊗ z) = (-1)^b s_j ⊗ 𝕏⁰ z`. -/
theorem projF_X_recL (M : QuasiCohesive 𝒜) (j : Fin m) (p : ℤ) (z : M.Q p) :
    Tot.projF 𝒜 M.Q (b : ℤ) (M.X (recL b s j p z)) =
      (b : ℤ).negOnePow • recL b s j (p + 1) (M.X0comp p z) := by
  have hs : (s j : A) ∈ 𝒜 (b : ℤ) := (s j).2
  show Tot.projF 𝒜 M.Q (b : ℤ) (M.X (Tot.tmul 𝒜 M.Q (s j : A) (lof (𝒜 0) ℤ M.Q p z))) =
    (b : ℤ).negOnePow • Tot.tmul 𝒜 M.Q (s j : A) (lof (𝒜 0) ℤ M.Q (p + 1) (M.X0comp p z))
  have h1 : Tot.projF 𝒜 M.Q (b : ℤ) (GCDga.d (𝒜 := 𝒜) (s j : A) •
      Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p z)) = 0 := by
    rw [Tot.smul_tmul, mul_one]
    exact projF_eq_zero_of_mem (tmul_mem_filTot (by omega) (GCDga.d_mem (𝒜 := 𝒜) hs) _)
  have h2 : Tot.eps 𝒜 M.Q (M.X (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p z))) =
      lof (𝒜 0) ℤ M.Q (p + 1) (M.X0comp p z) := by
    rw [M.eps_X, ← Tot.oneTmul_apply, Tot.eps_oneTmul, M.X0_lof]
  rw [Tot.tmul_eq_smul (s j : A), M.leibniz hs, map_add, h1, zero_add, Units.smul_def,
    map_zsmul, Tot.projF_smul_of_mem hs, sub_self, projF_zero_eq, h2, ← Units.smul_def,
    ← Tot.tmul_eq_smul]

end Compat

section Nat

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
  {Q' : ℤ → Type} [∀ p, AddCommGroup (Q' p)] [∀ p, Module (ℬ 0) (Q' p)]
  (b : ℕ) {m : ℕ} (c : Fin m → ↥(GCDga.piece 𝒜 (b : ℤ)) →ₗ[↥(𝒜 0)] ↥(𝒜 0))
  (c' : Fin m → ↥(GCDga.piece ℬ (b : ℤ)) →ₗ[↥(ℬ 0)] ↥(ℬ 0))
  (s : Fin m → ↥(GCDga.piece 𝒜 (b : ℤ))) (s' : Fin m → ↥(GCDga.piece ℬ (b : ℤ)))
  (g : DgaHom 𝒜 ℬ) (u : ∀ p, Q p →+ Q' p)
  (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = g.f0 r • u p x)
  (hc : ∀ (j : Fin m) (a : ↥(GCDga.piece 𝒜 (b : ℤ))) (b' : ↥(GCDga.piece ℬ (b : ℤ))),
    (b' : B) = g a → c' j b' = g.f0 (c j a))
  (hs : ∀ j, g (s j : A) = (s' j : B))

include hc in
private theorem coefA_map (j : Fin m) (a : A) :
    coefA b c' j (g a) = g.f0 (coefA b c j a) :=
  hc j _ _ (g.map_proj _ a).symm

include hu hc in
/-- Coordinates are natural. -/
theorem crdL_map (j : Fin m) (p : ℤ) (x : Tot 𝒜 Q) :
    crdL b c' j p (totMapAlong g u hu x) = u p (crdL b c j p x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [totMapAlong_tmul, crdL_tmul, crdL_tmul, coefA_map b c c' g hc,
      famMap_apply_mdl u, hu]
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

include hu hs in
/-- Reconstruction is natural. -/
theorem recL_map (j : Fin m) (p : ℤ) (z : Q p) :
    totMapAlong g u hu (recL b s j p z) = recL b s' j p (u p z) := by
  show totMapAlong g u hu (Tot.tmul 𝒜 Q (s j : A) (lof (𝒜 0) ℤ Q p z)) = _
  rw [totMapAlong_tmul, hs, DirectSum.lof_eq_of, famMap_of]
  rfl

end Nat

section Retract

/-- `ρ` as a morphism of sheaves of rings `R ⟶ 𝒜⁰`. -/
def ρS (P : PreResolvingData X) : P.R ⟶ ringOf P.A0 :=
  ⟨{ app := fun V => RingCat.ofHom (P.ρ V.unop)
     naturality := by
       intro V W f
       refine RingCat.hom_ext (RingHom.ext fun a => ?_)
       exact Subtype.ext (congrArg Subtype.val (P.ρ_natural (leOfHom f.unop) a)).symm }⟩

/-- Restriction of scalars along `ρ` on the over-site. -/
abbrev resρ (P : PreResolvingData X) (U : Opens X) :
    Mod ((ringOf P.A0).over U) ⥤ Mod (P.R.over U) :=
  SheafOfModules.restrictScalars.{0}
    (((Opens.grothendieckTopology X).overPullback RingCat U).map (ρS P))

/-- Dual basis data for `𝒜^b`: sections `s_j` and functionals `c_j`, compatible with
restriction, with `a = ∑ c_j(a) s_j`. -/
structure DualData (P : PreResolvingData X) (b : ℕ) where
  /-- The number of generators. -/
  m : ℕ
  /-- The generators. -/
  s : Fin m → ∀ V : Opens X, ↥(GCDga.piece (P.D.𝒜 V) b)
  /-- The coefficient functionals. -/
  c : Fin m → ∀ V : Opens X, ↥(GCDga.piece (P.D.𝒜 V) b) →ₗ[↥(P.D.𝒜 V 0)] ↥(P.D.𝒜 V 0)
  /-- The generators are compatible with restriction. -/
  hs : ∀ j (V W : Opens X) (h : W ≤ V), P.D.res h (s j V : P.D.A V) = (s j W : P.D.A W)
  /-- The functionals are compatible with restriction. -/
  hc : ∀ j (V W : Opens X) (h : W ≤ V) (a : ↥(GCDga.piece (P.D.𝒜 V) b)),
    c j W (P.resPiece b h a) = (P.D.res h).f0 (c j V a)
  /-- The expansion. -/
  he : ∀ (V : Opens X) (a : ↥(GCDga.piece (P.D.𝒜 V) b)),
    (a : P.D.A V) = ∑ j, ((c j V a : ↥(P.D.𝒜 V 0)) : P.D.A V) * (s j V : P.D.A V)

theorem exists_dualData (P : PreResolvingData X) [CompactSpace X] (b : ℕ) :
    Nonempty (DualData P b) := by
  obtain ⟨m, s, c, hs, hc, he⟩ := P.exists_dual b
  exact ⟨⟨m, s, c, hs, hc, he⟩⟩

end Retract

end ConnHom
end PreResolvingData
end Cohesive
end
