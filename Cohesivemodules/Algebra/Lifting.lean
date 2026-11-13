import Cohesivemodules.Algebra.LiftingLead

set_option linter.style.header false

/-!
# A11–A12: the lifting theorem (part 3 of 3)

Split from `Algebra/Lifting.lean` for size;
continues `Algebra/LiftingLead.lean`.
-/

noncomputable section
namespace Cohesive
open TensorProduct DirectSum
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-! ## The inductive construction -/

section Construction

variable (P : ℤ → Type) [∀ p, AddCommGroup (P p)] [∀ p, Module (𝒜 0) (P p)]
  (N : QuasiCohesive 𝒜) (dP : (⨁ p, P p) →ₗ[𝒜 0] (⨁ p, P p))
  (e₀ : (⨁ p, P p) →ₗ[𝒜 0] (⨁ p, N.Q p))

omit [∀ p, AddCommGroup (P p)] [∀ p, Module (𝒜 0) (P p)] in
/-- **A11.a (form used in the proof)** The cone of `e₀ ∘ - : gr_b Hom(P, P) → gr_b Hom(P, Q)` has
no cohomology in degree `1`: every pair `(K, L)` of pure maps of form degree `b` (`K` of degree
`2`, `L` of degree `1`) with `δ⁰K = 0` and `δ⁰L + e₀K = 0` comes from `(φ, ψ)` with
`δ⁰φ = -K` and `δ⁰ψ - e₀φ = -L`. Here `δ⁰` uses `∂̂ = hatGen 1 dP` and `𝕏̂⁰ = hatGen 1 dQ`
(for `Q = Q_N`, `dQ = 𝕏⁰`). [A, proof of Prop 3.3.4]. -/
def ConeLift (P Q : ℤ → Type) [∀ p, AddCommGroup (P p)] [∀ p, Module (𝒜 0) (P p)]
    [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    (dP : (⨁ p, P p) →ₗ[𝒜 0] (⨁ p, P p)) (dQ : (⨁ p, Q p) →ₗ[𝒜 0] (⨁ p, Q p))
    (e₀ : (⨁ p, P p) →ₗ[𝒜 0] (⨁ p, Q p)) (b : ℤ) : Prop :=
  ∀ K ∈ HomT 𝒜 P P 2, IsPure b K → ∀ L ∈ HomT 𝒜 P Q 1, IsPure b L →
    δT (k := k) (hatGen 1 dP) (hatGen 1 dP) 2 K = 0 →
    δT (hatGen 1 dP) (hatGen 1 dQ) 1 L + hatGen 0 e₀ ∘ₗ K = 0 →
    ∃ φ ∈ HomT 𝒜 P P 1, IsPure b φ ∧ ∃ ψ ∈ HomT 𝒜 P Q 0, IsPure b ψ ∧
      δT (hatGen 1 dP) (hatGen 1 dP) 1 φ = -K ∧
      δT (hatGen 1 dP) (hatGen 1 dQ) 0 ψ - hatGen 0 e₀ ∘ₗ φ = -L

/-- A11: the state of the induction at form degree `b`: generator data `θ` with leading part `∂`,
a degree-`0` map `e` with leading part `e₀`, and both defects `D² - c`, `δe` in `F^b`. -/
structure LiftStage (b : ℤ) where
  /-- The generator data of `𝔼` built so far. -/
  θ : GenData 𝒜 P
  /-- `θ` has total degree `1`. -/
  θ_mem : ∀ p (x : P p), θ.θ (lof (𝒜 0) ℤ P p x) ∈ totDeg 𝒜 P (p + 1)
  /-- `𝔼` has leading operator `∂̂`. -/
  θ_lead : LeadsTo θ.extend (hatGen 1 dP)
  /-- The map `e` built so far. -/
  e : Tot 𝒜 P →ₗ[k] Tot 𝒜 N.Q
  /-- `e` has degree `0`. -/
  e_mem : e ∈ HomT 𝒜 P N.Q 0
  /-- `e` has leading part `ê₀`. -/
  e_lead : e - hatGen 0 e₀ ∈ FT 𝒜 P N.Q 0 1
  /-- The curvature defect `𝔼² - c` lies in `F^b`. -/
  K_mem : θ.extend ∘ₗ θ.extend - cMul 𝒜 P ∈ FT 𝒜 P P 2 b
  /-- The closedness defect `δe` lies in `F^b`. -/
  L_mem : δT θ.extend N.X 0 e ∈ FT 𝒜 P N.Q 1 b

/-- **A11 (base)** The stage `b = 1`: `𝔼 = ∂̂ + ∇̂` for connections `∇` on the `P^p` (A2.a) and
`e = ê₀`. -/
theorem liftStage_one [∀ p, Module.Finite (𝒜 0) (P p)] [∀ p, Module.Projective (𝒜 0) (P p)]
    (hdP : ∀ p (x : P p), Tot.ConcAt (p + 1) (dP (lof (𝒜 0) ℤ P p x)))
    (hdP2 : ∀ x, dP (dP x) = 0)
    (he₀ : ∀ p (x : P p), Tot.ConcAt p (e₀ (lof (𝒜 0) ℤ P p x)))
    (he₀d : ∀ x, N.X0 (e₀ x) = e₀ (dP x)) :
    Nonempty (LiftStage P N dP e₀ 1) := by
  -- connections `∇_p` on the `P^p` (A2.a), assembled to `∇ : ⨁P → A ⊗ ⨁P`
  have conn : ∀ p, Connection 𝒜 (P p) := fun p =>
    (Connection.exists_connection (𝒜 := 𝒜) (P := P p)).some
  obtain ⟨nab, nab_of⟩ : ∃ nab : (⨁ p, P p) →+ Tot 𝒜 P,
      ∀ p x, nab (DirectSum.of P p x) = connTot p (conn p x) :=
    ⟨DirectSum.toAddMonoid fun p => (connTot p).comp (conn p).toAddMonoidHom,
      fun p x => DirectSum.toAddMonoid_of _ p x⟩
  have nab_leib : ∀ (f : 𝒜 0) e, nab (f • e) =
      Tot.tmul 𝒜 P (GCDga.d (𝒜 := 𝒜) f) e + (f : A) • nab e := by
    intro f e
    induction e using DirectSum.induction_on with
    | zero => simp
    | of p x =>
      rw [show f • DirectSum.of P p x = DirectSum.of P p (f • x) from
          (map_smul (DirectSum.lof (𝒜 0) ℤ P p) f x).symm, nab_of, nab_of,
        (conn p).leibniz, map_add, connTot_tmul, connTot_smul]
      rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, Tot.tmul_add, smul_add]; abel
  have nab_fil : ∀ e, nab e ∈ filTot 𝒜 P 1 := by
    intro e
    induction e using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of p x => rw [nab_of]; exact (connTot_mem p _).2
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
  -- the generator data `θ = 1 ⊗ ∂ + ∇`
  obtain ⟨θ, hθ⟩ : ∃ θ : GenData 𝒜 P, ∀ e, θ.θ e = Tot.tmul 𝒜 P 1 (dP e) + nab e :=
    ⟨{ θ := (Tot.oneTmul 𝒜 P).toAddMonoidHom.comp dP.toAddMonoidHom + nab
       leibniz := fun f e => by
         show Tot.oneTmul 𝒜 P (dP (f • e)) + nab (f • e) = _ +
           (f : A) • (Tot.oneTmul 𝒜 P (dP e) + nab e)
         rw [dP.map_smul, (Tot.oneTmul 𝒜 P).map_smul, Tot.smul0_eq, nab_leib, smul_add]
         abel }, fun _ => rfl⟩
  have θ_mem : ∀ p (x : P p), θ.θ (lof (𝒜 0) ℤ P p x) ∈ totDeg 𝒜 P (p + 1) := by
    intro p x
    rw [hθ]
    refine add_mem (tmul_one_mem_totDeg_of_concAt (hdP p x)) ?_
    rw [show lof (𝒜 0) ℤ P p x = DirectSum.of P p x from rfl, nab_of]
    exact (connTot_mem p _).1
  have θ_lead : LeadsTo θ.extend (hatGen 1 dP) := by
    intro c x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, a, e, hcq, ha, rfl⟩ := hx
      rw [GenData.extend_tmul, hθ, hatGen_tmul, twist_one_eq_sigma,
        Tot.tmul_eq_smul (GCDga.sigma 𝒜 a), smul_add, add_sub_assoc, add_sub_cancel_left,
        GCDga.sigma_of_mem 𝒜 ha, Units.smul_def, smul_assoc]
      refine add_mem (tmul_mem_filTot (by omega) (GCDga.d_mem (𝒜 := 𝒜) ha) e)
        (Submodule.smul_of_tower_mem _ _ ?_)
      exact filTot_anti (by omega) (smul_mem_filTot ha (nab_fil e))
    | zero => rw [map_zero, map_zero, sub_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add, map_add, add_sub_add_comm]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, map_smul, ← smul_sub]; exact Submodule.smul_mem _ r hx
  have hD : IsDiffOp θ.extend := θ.isDiffOp θ_mem
  have he_mem : hatGen 0 e₀ ∈ HomT 𝒜 P N.Q 0 :=
    hatGen_mem fun p x => by rw [add_zero]; exact he₀ p x
  refine ⟨{
    θ := θ
    θ_mem := θ_mem
    θ_lead := θ_lead
    e := hatGen 0 e₀
    e_mem := he_mem
    e_lead := by rw [sub_self]; exact zero_mem _
    K_mem := ?_
    L_mem := ?_ }⟩
  · refine (memFT_iff (sq_sub_c_mem hD)).2 fun e => mem_filTot_one_of_eps ?_
    have hc : Tot.eps 𝒜 P (GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 P 1 e) = 0 := by
      rw [Tot.eps_smul, Tot.proj0_of_mem_ne (GCDga.c_mem (𝒜 := 𝒜)) two_ne_zero, zero_smul]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, cMul, LinearMap.coe_mk,
      AddHom.coe_mk, map_sub, hc, sub_zero]
    rw [eps_lead θ_lead, eps_lead θ_lead,
      show Tot.eps 𝒜 P (Tot.tmul 𝒜 P 1 e) = e from Tot.eps_oneTmul e, hdP2]
  · refine (memFT_iff (δT_mem_of_diff hD N.isDiffOp he_mem)).2 fun e =>
      mem_filTot_one_of_eps ?_
    simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, Int.negOnePow_zero, one_smul,
      map_sub]
    rw [QuasiCohesive.eps_X, eps_hatGen, eps_hatGen, eps_lead θ_lead,
      show Tot.eps 𝒜 P (Tot.tmul 𝒜 P 1 e) = e from Tot.eps_oneTmul e, he₀d, sub_self]

/-- **A11 (step)** From stage `b` to stage `b + 1`, using `ConeLift` in form degree `b`. -/
theorem liftStage_succ (hdP : ∀ p (x : P p), Tot.ConcAt (p + 1) (dP (lof (𝒜 0) ℤ P p x)))
    {b : ℤ} (hb : 1 ≤ b) (hlift : ConeLift (k := k) P N.Q dP N.X0 e₀ b)
    (S : LiftStage P N dP e₀ b) : Nonempty (LiftStage P N dP e₀ (b + 1)) := by
  have hX0 : ∀ p (e : N.Q p), Tot.ConcAt (p + 1) (N.X0 (lof (𝒜 0) ℤ N.Q p e)) :=
    fun _ e => N.X0_concAt e
  have hD : IsDiffOp S.θ.extend := S.θ.isDiffOp S.θ_mem
  have hX : IsDiffOp N.X := N.isDiffOp
  obtain ⟨hK₁, -⟩ := Submodule.mem_inf.1 S.K_mem
  obtain ⟨hL₁, -⟩ := Submodule.mem_inf.1 S.L_mem
  -- the cycle conditions on the pure parts `K_b`, `L_b`
  have c1 : δT (hatGen 1 dP) (hatGen 1 dP) 2 (pure b _ hK₁) = 0 := by
    rw [← (pure_δT hdP hdP hD hD S.θ_lead S.θ_lead S.K_mem).2 (δT_mem_of_diff hD hD hK₁)]
    exact pure_of_eq_zero _ (δT_sq_sub_c hD)
  have hEK : S.e ∘ₗ (S.θ.extend ∘ₗ S.θ.extend - cMul 𝒜 P) ∈ HomT 𝒜 P N.Q 2 := by
    have := comp_mem_homT S.e_mem hK₁
    rwa [zero_add] at this
  have c2 : δT (hatGen 1 dP) (hatGen 1 N.X0) 1 (pure b _ hL₁) +
      hatGen 0 e₀ ∘ₗ pure b _ hK₁ = 0 := by
    rw [← (pure_δT hdP hX0 hD hX S.θ_lead (X_lead N) S.L_mem).2 (δT_mem_of_diff hD hX hL₁),
      pure_congr _ (neg_mem hEK) (δT_δT_eq N.X N.flat S.e_mem), pure_neg hEK,
      pure_comp_lead S.e_mem S.e_lead S.K_mem hEK, neg_add_cancel]
  obtain ⟨φ, hφ, hφp, ψ, hψ, hψp, e1, e2⟩ :=
    hlift _ (pure_mem hK₁) (pure_isPure hK₁) _ (pure_mem hL₁) (pure_isPure hL₁) c1 c2
  have hφF : φ ∈ FT 𝒜 P P 1 b := mem_FT_of_isPure hφ hφp
  have hψF : ψ ∈ FT 𝒜 P N.Q 0 b := mem_FT_of_isPure hψ hψp
  refine ⟨{
    θ := S.θ.addHom φ hφ
    θ_mem := ?_
    θ_lead := ?_
    e := S.e + ψ
    e_mem := add_mem S.e_mem hψ
    e_lead := ?_
    K_mem := ?_
    L_mem := ?_ }⟩
  · intro p x
    refine add_mem (S.θ_mem p x) (hφ.1 ?_)
    have := tmul_mem_totDeg (Q := P) (SetLike.GradedOne.one_mem (A := 𝒜)) x
    rwa [zero_add] at this
  · intro c x hx
    rw [GenData.extend_addHom, LinearMap.add_apply, add_sub_right_comm]
    exact add_mem (S.θ_lead c x hx)
      (filTot_anti (by omega) ((Submodule.mem_inf.1 hφF).2 c x hx))
  · rw [add_sub_right_comm]
    exact add_mem S.e_lead (FT_anti hb hψF)
  · -- `K' = (K - K_b) + (δφ - δ⁰φ) + φ∘φ`, using `δ⁰φ = -K_b`
    rw [GenData.extend_addHom]
    have hδφ := pure_δT hdP hdP hD hD S.θ_lead S.θ_lead hφF
    have m1 := sub_pure_mem S.K_mem
    have m2 : δT S.θ.extend S.θ.extend 1 φ - δT (hatGen 1 dP) (hatGen 1 dP) 1 φ ∈
        FT 𝒜 P P (1 + 1) (b + 1) := by
      have := sub_pure_mem hδφ.1
      rwa [hδφ.2, pure_eq_self hφ hφp] at this
    have m3 : φ ∘ₗ φ ∈ FT 𝒜 P P (1 + 1) (b + 1) := FT_anti (by omega) (comp_mem_FT hφF hφF)
    rw [one_add_one_eq_two] at m2 m3
    have key : (S.θ.extend + φ) ∘ₗ (S.θ.extend + φ) - cMul 𝒜 P =
        (S.θ.extend ∘ₗ S.θ.extend - cMul 𝒜 P - pure b _ hK₁) +
          (δT S.θ.extend S.θ.extend 1 φ - δT (hatGen 1 dP) (hatGen 1 dP) 1 φ) + φ ∘ₗ φ := by
      rw [e1]
      ext x
      simp only [δT, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add,
        Int.negOnePow_one, Units.neg_smul, one_smul, sub_neg_eq_add]
      abel
    rw [key]
    exact add_mem (add_mem m1 m2) m3
  · -- `L' = (L - L_b) + (δψ - δ⁰ψ) - (e - ê₀)∘φ - ψ∘φ`, using `δ⁰ψ = ê₀φ - L_b`
    rw [GenData.extend_addHom]
    have hδψ := pure_δT hdP hX0 hD hX S.θ_lead (X_lead N) hψF
    have m1 := sub_pure_mem S.L_mem
    have m2 : δT S.θ.extend N.X 0 ψ - δT (hatGen 1 dP) (hatGen 1 N.X0) 0 ψ ∈
        FT 𝒜 P N.Q (0 + 1) (b + 1) := by
      have := sub_pure_mem hδψ.1
      rwa [hδψ.2, pure_eq_self hψ hψp] at this
    have m3 : (S.e - hatGen 0 e₀) ∘ₗ φ ∈ FT 𝒜 P N.Q (0 + 1) (b + 1) := by
      have := comp_mem_FT S.e_lead hφF
      rwa [add_comm 1 b] at this
    have m4 : ψ ∘ₗ φ ∈ FT 𝒜 P N.Q (0 + 1) (b + 1) := FT_anti (by omega) (comp_mem_FT hψF hφF)
    rw [zero_add] at m2 m3 m4
    have e2' : δT (hatGen 1 dP) (hatGen 1 N.X0) 0 ψ =
        hatGen 0 e₀ ∘ₗ φ - pure b _ hL₁ := by
      rw [sub_eq_iff_eq_add.1 e2]; abel
    have key : δT (S.θ.extend + φ) N.X 0 (S.e + ψ) =
        (δT S.θ.extend N.X 0 S.e - pure b _ hL₁) +
          (δT S.θ.extend N.X 0 ψ - δT (hatGen 1 dP) (hatGen 1 N.X0) 0 ψ) -
          (S.e - hatGen 0 e₀) ∘ₗ φ - ψ ∘ₗ φ := by
      rw [e2']
      ext x
      simp only [δT, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add,
        Int.negOnePow_zero, one_smul]
      abel
    rw [key]
    exact sub_mem (sub_mem (add_mem m1 m2) m3) m4

/-- A11: iterating the step up to form degree `N + 1`. -/
theorem liftStage_top [∀ p, Module.Finite (𝒜 0) (P p)] [∀ p, Module.Projective (𝒜 0) (P p)]
    (hdP : ∀ p (x : P p), Tot.ConcAt (p + 1) (dP (lof (𝒜 0) ℤ P p x)))
    (hdP2 : ∀ x, dP (dP x) = 0)
    (he₀ : ∀ p (x : P p), Tot.ConcAt p (e₀ (lof (𝒜 0) ℤ P p x)))
    (he₀d : ∀ x, N.X0 (e₀ x) = e₀ (dP x))
    (hlift : ∀ b : ℤ, 1 ≤ b → b ≤ GCDga.N 𝒜 → ConeLift (k := k) P N.Q dP N.X0 e₀ b) :
    Nonempty (LiftStage P N dP e₀ (GCDga.N 𝒜 + 1)) := by
  obtain ⟨S₁⟩ := liftStage_one P N dP e₀ hdP hdP2 he₀ he₀d
  have key : ∀ j : ℕ, (j : ℤ) ≤ GCDga.N 𝒜 → Nonempty (LiftStage P N dP e₀ (j + 1)) := by
    intro j
    induction j with
    | zero => intro _; simpa using ⟨S₁⟩
    | succ j ih =>
      intro hj
      obtain ⟨S⟩ := ih (by omega)
      have := liftStage_succ P N dP e₀ hdP (b := (j : ℤ) + 1) (by omega)
        (hlift _ (by omega) (by omega)) S
      simpa [add_assoc] using this
  exact key (GCDga.N 𝒜) le_rfl

/-- A11: the `(0,0)`-component of a map with leading part `ê₀` is `e₀`. -/
theorem eps_of_lead {e : Tot 𝒜 P →ₗ[k] Tot 𝒜 N.Q} (h : e - hatGen 0 e₀ ∈ FT 𝒜 P N.Q 0 1)
    (x : ⨁ p, P p) : Tot.eps 𝒜 N.Q (e (Tot.tmul 𝒜 P 1 x)) = e₀ x := by
  have h1 := (memFT_iff (Submodule.mem_inf.1 h).1).1 h x
  rw [LinearMap.sub_apply, hatGen_tmul_one] at h1
  have h2 := eps_eq_zero_of_mem h1
  rw [map_sub, show Tot.eps 𝒜 N.Q (Tot.tmul 𝒜 N.Q 1 (e₀ x)) = e₀ x from Tot.eps_oneTmul _,
    sub_eq_zero] at h2
  exact h2

/-- A11: the form-degree-`0` part of generator data with leading operator `∂̂` is `∂`. -/
theorem eps_θ_of_lead {θ : GenData 𝒜 P} (h : LeadsTo θ.extend (hatGen 1 dP))
    (x : ⨁ p, P p) : Tot.eps 𝒜 P (θ.θ x) = dP x := by
  have h1 := h 0 (Tot.tmul 𝒜 P 1 x) (filTot_zero _)
  rw [GenData.extend_tmul_one, hatGen_tmul_one, zero_add] at h1
  have h2 := eps_eq_zero_of_mem h1
  rw [map_sub, show Tot.eps 𝒜 P (Tot.tmul 𝒜 P 1 (dP x)) = dP x from Tot.eps_oneTmul _,
    sub_eq_zero] at h2
  exact h2

/-- **A11 (core)** The lifting theorem on generators. Let `N` be quasi-cohesive, `P` a family of
finitely generated projective `A⁰`-modules with an `A⁰`-linear differential `∂` of degree `1`,
and `e₀ : (P, ∂) → (Q_N, 𝕏⁰)` an `A⁰`-linear chain map of degree `0`. If the cone condition
`ConeLift` holds in every form degree `1 ≤ b ≤ N`, then there are generator data `θ` on `P` (a
quasi-cohesive structure `𝔼` on `A ⊗ P`) with `𝔼⁰ = ∂` and a closed degree-`0` map
`e : A ⊗ P → N` with `(0,0)`-component `e₀`. [B, Thm 3.2.7(2) and Lemma 3.2.8],
[A, Prop 3.3.4, case 2]. -/
theorem lift_core [∀ p, Module.Finite (𝒜 0) (P p)] [∀ p, Module.Projective (𝒜 0) (P p)]
    (hdP : ∀ p (x : P p), Tot.ConcAt (p + 1) (dP (lof (𝒜 0) ℤ P p x)))
    (hdP2 : ∀ x, dP (dP x) = 0)
    (he₀ : ∀ p (x : P p), Tot.ConcAt p (e₀ (lof (𝒜 0) ℤ P p x)))
    (he₀d : ∀ x, N.X0 (e₀ x) = e₀ (dP x))
    (hlift : ∀ b : ℤ, 1 ≤ b → b ≤ GCDga.N 𝒜 → ConeLift (k := k) P N.Q dP N.X0 e₀ b) :
    ∃ (θ : GenData 𝒜 P) (hθ : ∀ p (x : P p), θ.θ (lof (𝒜 0) ℤ P p x) ∈ totDeg 𝒜 P (p + 1))
      (hflat : ∀ x, θ.extend (θ.θ x) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 P 1 x),
      (∀ x, Tot.eps 𝒜 P (θ.θ x) = dP x) ∧
      ∃ e ∈ Z0 (QuasiCohesive.ofGenerators P θ hθ hflat) N,
        ∀ x, Tot.eps 𝒜 N.Q (e (Tot.tmul 𝒜 P 1 x)) = e₀ x := by
  obtain ⟨S⟩ := liftStage_top P N dP e₀ hdP hdP2 he₀ he₀d hlift
  have hK := FT_eq_zero (show (GCDga.N 𝒜 : ℤ) < GCDga.N 𝒜 + 1 by omega) S.K_mem
  have hL := FT_eq_zero (show (GCDga.N 𝒜 : ℤ) < GCDga.N 𝒜 + 1 by omega) S.L_mem
  have hflat : ∀ x, S.θ.extend (S.θ.θ x) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 P 1 x := by
    intro x
    have h := LinearMap.congr_fun hK (Tot.tmul 𝒜 P 1 x)
    rw [LinearMap.sub_apply, LinearMap.comp_apply, GenData.extend_tmul_one,
      LinearMap.zero_apply, sub_eq_zero] at h
    exact h
  refine ⟨S.θ, S.θ_mem, hflat, eps_θ_of_lead P dP S.θ_lead, S.e,
    Submodule.mem_inf.2 ⟨S.e_mem, LinearMap.mem_ker.2 hL⟩, eps_of_lead P N e₀ S.e_lead⟩

end Construction

end Cohesive
