import Cohesivemodules.Comparison.TwistedCurvedGlue

set_option linter.style.header false

/-!
# Z3.t: the curved global model `N^h` and its localizations (blueprint-tw G′ (g), (h), (j))

Blueprint item Z3.t (`blueprint/blueprint-tw.md` §3 G′ (g), (h), (j); G.5, G.7). For pre-resolving
data `P` (`X` compact), a closed `h ∈ 𝒜²(X)`, a twist datum `T` for `h`, a complex `K'` of
`ȟ`-twisted `O`-modules and the C7.b connections `θ_α` on `F_α = 𝒜⁰|U_α ⊗ K'_α`. Let
`F = untwist(K')`, a complex of `𝒜⁰`-modules on `X` (G′ (b)).
* `twGens p = F^p(X)` (sections over the terminal object of `Over ⊤`), `πgen α`: the component
  `α` of the restriction to `U_α`, `F^p(X) → F_α^p(U_α)`; `πTot α`: the induced map of total
  modules `Tot(𝒜(X), F(X)) → Tot(𝒜(U_α), F_α(U_α))` along `res`;
* `πTot_ext` (G′ (g)): elements of `Tot(𝒜(X), F(X))` are determined by their images `πTot α`;
* `exists_θh` (G′ (h)): generator data `θ^h` over the curved algebra `(𝒜(X), h)` with
  `πTot α ∘ θ^h = θ_α + h⁰_α` on generators; `θh_mem`, `θh_flat` (`(θ^h)² = h`), `θh_eps`;
* `Nh`: the quasi-cohesive module `(F^•(X), θ^h)` over `(𝒜(X), h)`;
* `πTot_X`: `πTot α` intertwines `𝕏^h` with the operator of `ungauge_{h⁰_α}(N_α)`,
  `N_α = θ_α.N(U_α)`;
* `exists_eα` (G′ (j)): for `e ∈ Z0(M, N^h)`, the localization `e_α ∈ Z0(gauge_{h⁰_α}(M|U_α), N_α)`
  with `e_α(1 ⊗ x) = πTot α (e x)`.

## Deviations
* `θ^h` is constructed on global sections only (no curved copy of C7's `Conn` for every `V`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum
open PreResolvingData (topO)

attribute [local instance] PreResolvingData.tDegModuleC

variable {X : Type} [TopologicalSpace X] [CompactSpace X] (P : PreResolvingData X)
  {h : P.D.A ⊤} (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2)
  (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (K' : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ)

variable (θ : ∀ α, P.Conn (T.U α) (twFα P T K' α))
  (hθ : ∀ α, P.IsBCConn (T.U α) (twKα P T K' α) (θ α))

include hθ in
/-- **Z3.t (G′ (h)).** [A, Rem 7.2.4], blueprint-tw G.5. Generator data `θ^h` on `F^•(X)` over the
curved algebra `(𝒜(X), h)` whose localization to every `U_α` is `θ_α + h⁰_α·` on generators:
`πTot α (θ^h s) = θ_α(πgen α s) + h⁰_α ⊗ πgen α s`. Constructed by gluing in the sheaf `T(F)`
(C7.a): the local elements are compatible on `U_α ∩ U_β` because `d(u_αβ⁻¹) = −u_αβ⁻¹(h⁰_β − h⁰_α)`
(checked on `η k`, then C.7′ (b)). -/
theorem exists_θh :
    ∃ θh : GenData (𝒜h P hh hd) (twGens P T K'),
      ∀ (α : T.ι) (p : ℤ) (s : twGens P T K' p),
        πTot P T K' α (show TotX P T K' from θh.θ (DirectSum.of (twGens P T K') p s)) =
          ((θ α).θ (topO (T.U α))).θ
              (lof ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) ℤ
                (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) p (πgen P T K' α p s)) +
            (show P.D.A (topO (T.U α)).unop.left from T.h0 α) •
              Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
                (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1
                (lof ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) ℤ
                  (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) p (πgen P T K' α p s)) := by
  refine ⟨⟨DirectSum.toAddMonoid (θgen P T K' θ hθ), fun f e => θext_leibniz P T K' θ hθ f e⟩,
    fun α p s => ?_⟩
  exact (congrArg (πTot P T K' α) (DirectSum.toAddMonoid_of (θgen P T K' θ hθ) p s)).trans
    (πTot_θgen P T K' θ hθ α p s)

/-- **Z3.t (G′ (h)).** The curved generator data `θ^h` (a choice in `exists_θh`). -/
def θh : GenData (𝒜h P hh hd) (twGens P T K') :=
  (exists_θh P T hh hd K' θ hθ).choose

/-- Z3.t: the defining property of `θ^h` (`exists_θh`). -/
theorem πTot_θh (α : T.ι) (p : ℤ) (s : twGens P T K' p) :
    πTot P T K' α
        (show TotX P T K' from (θh P T hh hd K' θ hθ).θ (DirectSum.of (twGens P T K') p s)) =
      ((θ α).θ (topO (T.U α))).θ
          (lof ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) ℤ
            (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) p (πgen P T K' α p s)) +
        (show P.D.A (topO (T.U α)).unop.left from T.h0 α) •
          Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
            (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1
            (lof ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) ℤ
              (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) p (πgen P T K' α p s)) :=
  (exists_θh P T hh hd K' θ hθ).choose_spec α p s

/-- Z3.t: `θ^h` as an additive map into the flat spelling `TotX` of the total module. -/
private def θhT : (⨁ p, twGens P T K' p) →+ TotX P T K' := (θh P T hh hd K' θ hθ).θ

/-- Z3.t: `πTot_θh` on all of `⨁_p F^p(X)` (additivity). -/
private theorem πTot_θh_gen (α : T.ι) (e : ⨁ p, twGens P T K' p) :
    πTot P T K' α (θhT P T hh hd K' θ hθ e) =
      ((θ α).θ (topO (T.U α))).θ (famMap (πgen P T K' α) e) +
        h0A P T α •
          Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
            (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1
            (famMap (πgen P T K' α) e) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero, add_zero, Tot.tmul_zero]
  | of p s =>
    have := πTot_θh P T hh hd K' θ hθ α p s
    rw [DirectSum.lof_eq_of] at this
    rw [famMap_of]
    exact this
  | add x y hx hy =>
    simp only [map_add, hx, hy, Tot.tmul_add, smul_add]
    abel

/-- **Z3.t (G′ (h)).** `θ^h` has total degree `1`. -/
theorem θh_mem (p : ℤ) (s : twGens P T K' p) :
    (θh P T hh hd K' θ hθ).θ (lof ↥(𝒜h P hh hd 0) ℤ (twGens P T K') p s) ∈
      totDeg (𝒜h P hh hd) (twGens P T K') (p + 1) := by
  have hmem : θhT P T hh hd K' θ hθ (DirectSum.of _ p s) ∈
      totDeg (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K') (p + 1) := by
    refine mem_totDeg_of_πTot P T K' (p + 1) _ fun α => ?_
    rw [πTot_θh_gen P T hh hd K' θ hθ α, famMap_of]
    refine add_mem ((θ α).mem (topO (T.U α)) p _) ?_
    have h1 := tmul_mem_totDeg (𝒜 := P.D.𝒜 (topO (T.U α)).unop.left)
      (Q := (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))))
      (SetLike.GradedOne.one_mem (A := P.D.𝒜 (topO (T.U α)).unop.left)) (πgen P T K' α p s)
    have h2 := smul_mem_totDeg (𝒜 := P.D.𝒜 (topO (T.U α)).unop.left)
      (Q := (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α)))) (T.h0_mem α) h1
    rw [show 1 + (0 + p) = p + 1 by ring] at h2
    exact h2
  exact hmem

/-- Z3.t: the curvature `h|⊤` as an element of the algebra at the terminal object of `Over ⊤`. -/
private abbrev cTop (g : P.D.A ⊤) : P.D.A (topO (⊤ : Opens X)).unop.left :=
  P.D.res (le_top : (⊤ : Opens X) ≤ ⊤) g

/-- Z3.t: the Leibniz extension of `θ^h`, as an additive map on `TotX`. -/
private def θhX : TotX P T K' →+ TotX P T K' := (θh P T hh hd K' θ hθ).extend.toAddMonoidHom

/-- Z3.t: `πTot α` intertwines the Leibniz extension of `θ^h` with `𝕏_α + h⁰_α·`. -/
private theorem πTot_θhX (α : T.ι) (x : TotX P T K') :
    πTot P T K' α (θhX P T hh hd K' θ hθ x) =
      ((θ α).θ (topO (T.U α))).extend (πTot P T K' α x) + h0A P T α • πTot P T K' α x := by
  induction x using Tot.induction_on with
  | ht a e =>
    have e1 : θhX P T hh hd K' θ hθ (Tot.tmul _ _ a e) =
        Tot.tmul _ _ (GCDga.d (𝒜 := P.D.𝒜 (topO (⊤ : Opens X)).unop.left) a) e +
          GCDga.sigma (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) a • θhT P T hh hd K' θ hθ e := rfl
    rw [e1, map_add]
    have e2 : πTot P T K' α (GCDga.sigma (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) a •
        θhT P T hh hd K' θ hθ e) = GCDga.sigma (P.D.𝒜 (topO (T.U α)).unop.left) (resα P T α a) •
        πTot P T K' α (θhT P T hh hd K' θ hθ e) := by
      rw [← (resα P T α).map_sigma]
      exact totMapAlong_smul (resα P T α) (πgen P T K' α) (πgen_smul P T K' α) _ _
    rw [e2, πTot_θh_gen P T hh hd K' θ hθ α]
    have e3 : ∀ y, πTot P T K' α (Tot.tmul _ _ y e) =
        Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
          (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) (resα P T α y)
          (famMap (πgen P T K' α) e) := fun y => totMapAlong_tmul _ _ _ _ _
    rw [e3, e3, GenData.extend_tmul, (resα P T α).map_d]
    have h0m : h0A P T α ∈ P.D.𝒜 (topO (T.U α)).unop.left 1 := T.h0_mem α
    have e4 : GCDga.sigma (P.D.𝒜 (topO (T.U α)).unop.left) ((resα P T α).toAlgHom a) •
        (h0A P T α • Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
          (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1 (famMap (πgen P T K' α) e)) =
        h0A P T α • Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
          (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) ((resα P T α).toAlgHom a)
          (famMap (πgen P T K' α) e) := by
      rw [← mul_smul, sigma_mul_deg_one h0m, mul_smul, Tot.smul_tmul, mul_one]
    rw [smul_add, e4]
    abel
  | hadd x y hx hy => simp only [map_add, hx, hy, smul_add]; abel

/-- **Z3.t (G′ (h)).** `θ^h` is flat for the curvature `h`: `𝕏^h(θ^h e) = h·(1 ⊗ e)` (in each
component `(θ_α + h⁰_α)² = d h⁰_α = h|U_α`). -/
theorem θh_flat (e : ⨁ p, twGens P T K' p) :
    (θh P T hh hd K' θ hθ).extend ((θh P T hh hd K' θ hθ).θ e) =
      GCDga.c (𝒜 := 𝒜h P hh hd) • Tot.tmul (𝒜h P hh hd) (twGens P T K') 1 e := by
  change θhX P T hh hd K' θ hθ (θhT P T hh hd K' θ hθ e) =
    cTop P h •
      Tot.tmul (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K') 1 e
  refine πTot_ext P T K' _ _ fun α => ?_
  have h0m : h0A P T α ∈ P.D.𝒜 (topO (T.U α)).unop.left 1 := T.h0_mem α
  have hflat := (θ α).flat (topO (T.U α)) (famMap (πgen P T K' α) e)
  rw [P.c_eq_zero, zero_smul] at hflat
  have hL := GenData.extend_leibniz ((θ α).θ (topO (T.U α))) h0m
    (Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
      (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1 (famMap (πgen P T K' α) e))
  rw [GenData.extend_tmul_one] at hL
  have hsq : h0A P T α • h0A P T α • Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
      (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1 (famMap (πgen P T K' α) e) = 0 := by
    rw [← mul_smul, sq_eq_zero_deg_one h0m (isUnit_iff_ne_zero.2 two_ne_zero), zero_smul]
  have hR : πTot P T K' α (cTop P h •
      Tot.tmul (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K') 1 e) =
      GCDga.d (𝒜 := P.D.𝒜 (topO (T.U α)).unop.left) (h0A P T α) •
        Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
          (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1 (famMap (πgen P T K' α) e) := by
    rw [show GCDga.d (𝒜 := P.D.𝒜 (topO (T.U α)).unop.left) (h0A P T α) =
      (resα P T α) (cTop P h) from
      (T.d_h0 α).trans (P.D.res_comp _ _ h).symm]
    exact (totMapAlong_smul (resα P T α) (πgen P T K' α) (πgen_smul P T K' α) _ _).trans
      (congrArg _ (totMapAlong_tmul _ _ _ _ _ |>.trans (by rw [DgaHom.map_one'])))
  rw [πTot_θhX, πTot_θh_gen, hR, map_add, hflat, hL, smul_add]
  simp only [Int.negOnePow_one, Units.neg_smul, one_smul, hsq, zero_add]
  abel

/-- **Z3.t (G′ (h)).** The form-degree-`0` part of `θ^h` is the differential of `F`. -/
theorem θh_eps (p : ℤ) (s : twGens P T K' p) :
    Tot.eps (𝒜h P hh hd) (twGens P T K')
        ((θh P T hh hd K' θ hθ).θ (lof ↥(𝒜h P hh hd 0) ℤ (twGens P T K') p s)) =
      lof ↥(𝒜h P hh hd 0) ℤ (twGens P T K') (p + 1) (P.fD ⊤ (twFtop P T K') p (topO ⊤) s) := by
  show Tot.eps (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K')
      (θhT P T hh hd K' θ hθ (DirectSum.of _ p s)) = DirectSum.of _ (p + 1) _
  refine gen_ext P T K' _ _ fun α => ?_
  rw [← eps_totMapAlong (resα P T α) (πgen P T K' α) (πgen_smul P T K' α)]
  change Tot.eps _ _ (πTot P T K' α (θhT P T hh hd K' θ hθ (DirectSum.of _ p s))) = _
  rw [πTot_θh_gen P T hh hd K' θ hθ α, famMap_of, famMap_of, map_add, Tot.eps_smul,
    Tot.proj0_of_mem_ne (𝒜 := P.D.𝒜 (topO (T.U α)).unop.left) (T.h0_mem α) one_ne_zero,
    zero_smul, add_zero]
  have := (θ α).eps (topO (T.U α)) p (πgen P T K' α p s)
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of] at this
  rw [this, πgen_fD]

/-- **Z3.t (G′ (h)).** [A, Rem 7.2.4], blueprint-tw G.5. The quasi-cohesive module
`N^h = (F^•(X), θ^h)` over the curved algebra `(𝒜(X), h)`. -/
def Nh : QuasiCohesive (𝒜h P hh hd) :=
  QuasiCohesive.ofGenerators (twGens P T K') (θh P T hh hd K' θ hθ) (θh_mem P T hh hd K' θ hθ)
    (θh_flat P T hh hd K' θ hθ)

/-- **Z3.t (G′ (h)).** `πTot α` intertwines the operator `𝕏^h` of `N^h` with `𝕏_α + h⁰_α·`, the
operator of `ungauge_{h⁰_α}(N_α)`, `N_α = θ_α.N(U_α)` (Leibniz extension of `πTot_θh`). -/
theorem πTot_X (α : T.ι) (x : (Nh P T hh hd K' θ hθ).T) :
    πTot P T K' α (show TotX P T K' from (Nh P T hh hd K' θ hθ).X x) =
      (show P.TTot (T.U α) (twFα P T K' α) (topO (T.U α)) from
          ((θ α).N (topO (T.U α))).X (πTot P T K' α (show TotX P T K' from x))) +
        (show P.D.A (topO (T.U α)).unop.left from T.h0 α) •
          πTot P T K' α (show TotX P T K' from x) :=
  πTot_θhX P T hh hd K' θ hθ α x

/-- Z3.t: `πTot α` as a `ℂ`-linear map. -/
private def πTotL (α : T.ι) :
    TotX P T K' →ₗ[ℂ] P.TTot (T.U α) (twFα P T K' α) (topO (T.U α)) where
  toFun := πTot P T K' α
  map_add' := map_add _
  map_smul' r x := totMapAlong_smul_k _ _ _ r x

/-- Z3.t: `h|U_α` has degree `2` in the flat algebra over `U_α`. -/
private theorem hcRes (hh : h ∈ P.D.𝒜 ⊤ 2) (α : T.ι) :
    P.D.res (le_top : T.U α ≤ ⊤) h ∈ P.D.𝒜 (T.U α) 2 :=
  (P.D.res le_top).map_mem hh

/-- Z3.t: `h|U_α` is closed. -/
private theorem hdRes (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0) (α : T.ι) :
    GCDga.d (𝒜 := P.D.𝒜 (T.U α)) (P.D.res (le_top : T.U α ≤ ⊤) h) = 0 := by
  rw [← (P.D.res le_top).map_d, hd]
  exact map_zero _

/-- Z3.t: `πTot α` preserves the total degree. -/
private theorem πTot_mem_totDeg (α : T.ι) {m : ℤ} {z : TotX P T K'}
    (hz : z ∈ totDeg (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K') m) :
    πTot P T K' α z ∈ totDeg (P.D.𝒜 (topO (T.U α)).unop.left)
      (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) m :=
  totMapAlong_mem_totDeg _ _ _ hz

/-- Z3.t: `πTot α` is semilinear along `res_α`. -/
private theorem πTot_smul_A (α : T.ι) (a : P.D.A (topO (⊤ : Opens X)).unop.left) (z : TotX P T K') :
    πTot P T K' α (a • z) = (resα P T α) a • πTot P T K' α z :=
  totMapAlong_smul _ _ _ a z

/-- **Z3.t (G′ (j)).** [A, §7.2], blueprint-tw G.7. For `e ∈ Z0(M, N^h)` and every `α`, a closed
degree-`0` map `e_α : gauge_{h⁰_α}(M|U_α) → N_α` with `e_α(1 ⊗ x) = πTot α (e x)`: the
`𝒜(U_α)`-linear extension (`bcLift`) of `πTot α ∘ e` (closed by `πTot_X`), transported by the gauge
(`gauge_Z0`, A.3: `N_α = gauge_{h⁰_α}(ungauge_{h⁰_α} N_α)`). -/
theorem exists_eα (α : T.ι) (M : CohesiveModule (𝒜h P hh hd))
    (e : M.T →ₗ[ℂ] (Nh P T hh hd K' θ hθ).T)
    (he : e ∈ Z0 M.toQuasiCohesive (Nh P T hh hd K' θ hθ)) :
    ∃ eα ∈ Z0 (gaugedRes P T hh hd α M).toQuasiCohesive ((θ α).N (topO (T.U α))),
      ∀ x : M.T, eα (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
        M.Q x) = πTot P T K' α (show TotX P T K' from e x) := by
  let Nu := QuasiCohesive.ungauge (i := P.D.dga (T.U α)) (c' := P.D.res (le_top : T.U α ≤ ⊤) h)
    (hc := hcRes P T hh α) (hd := hdRes P T hd α) ((θ α).N (topO (T.U α))) (T.h0 α) (T.h0_mem α)
    (twistDatum_hcβ P T α) (isUnit_of_invertible 2)
  let f := (P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)
  have hχ : (πTotL P T K' α).comp e ∈ LinAlong f M.toQuasiCohesive Nu := by
    refine ⟨fun {m x} hx => ?_, fun a x => ?_⟩
    · have h1 := he.1.1 hx
      rw [add_zero] at h1
      exact πTot_mem_totDeg P T K' α h1
    · have h1 := hom0_smul he.1 a x
      change πTot P T K' α (e (a • x)) = (resα P T α) a • πTot P T K' α (e x)
      rw [h1]
      exact πTot_smul_A P T K' α a _
  have hbc := bcLift_mem_Z0 (f := f) (M := M.toQuasiCohesive) (N := Nu)
    ⟨(πTotL P T K' α).comp e, hχ⟩ (fun x => by
      have h2 := πTot_θhX P T hh hd K' θ hθ α (e x)
      have h3 : (Nh P T hh hd K' θ hθ).X (e x) = e (M.X x) :=
        closed0_X (LinearMap.mem_ker.1 he.2) x
      exact h2.symm.trans (congrArg (πTot P T K' α) h3))
  have hg := gauge_Z0 (i := P.D.dga (T.U α)) (c' := P.D.res (le_top : T.U α ≤ ⊤) h)
    (hc := hcRes P T hh α) (hd := hdRes P T hd α) (T.h0 α) (T.h0_mem α)
    (twistDatum_hcβ P T α) (isUnit_of_invertible 2)
    (@QuasiCohesive.baseChange ℂ _ _ _ _ (P.toSheafData.withCurvature h hh hd).𝒜X _ _
      (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _
      ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α)) f M.toQuasiCohesive) Nu
  refine ⟨bcLift (f := f) (M := M.toQuasiCohesive) (N := Nu) ⟨(πTotL P T K' α).comp e, hχ⟩,
    ?_, fun x => bcLift_bcF _ x⟩
  have hz := hg.symm ▸ hbc
  refine ⟨hz.1, LinearMap.mem_ker.2 ?_⟩
  have hδ := LinearMap.mem_ker.1 hz.2
  refine LinearMap.ext fun y => ?_
  have hy := LinearMap.congr_fun hδ y
  erw [δ_apply] at hy ⊢
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.zero_apply] at hy ⊢
  refine Eq.trans ?_ hy
  exact congrArg (· - _) (add_sub_cancel_right _ _).symm

end Cohesive
