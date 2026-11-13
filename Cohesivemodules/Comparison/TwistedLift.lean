import Cohesivemodules.Comparison.TwistedLiftAux

set_option linter.style.header false

/-!
# Z3.u: the curved lifting and the local `gr0Ξ` (blueprint-tw G′ (d), (i), (k))

Blueprint item Z3.u (`blueprint/blueprint-tw.md` §3 G′ (d), (i), (k); G.4, G.6, G.8). For a
strictly perfect complex `Pt` of `𝒜⁰`-modules with a quasi-isomorphism `f⁰ : Pt → F`,
`F = untwist(K')` (S10, G′ (d)):
* `exists_twisted_lift` (G′ (i) and (k)): A11 (general curvature) with `e⁰ := Γ(f⁰)` gives a
  cohesive module `M` over `(𝒜(X), h)` on `𝒜(X) ⊗ Γ(Pt)` and a closed `e : M → N^h`, and every
  localization `gr0Ξ_{e_α}` is a quasi-isomorphism (C5 step (D) over `U_α`,
  `quasiIso_gr0Ξ_of_equiv`, with `φ_p : 𝒜⁰(U_α) ⊗_{𝒜⁰(X)} Γ(Pt^p) ≅ Pt^p(U_α)`).

## Deviations
* None.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum
open PreResolvingData (topO)
open TwLift


variable {X : Type} [TopologicalSpace X] [CompactSpace X] (P : PreResolvingData X)
  {h : P.D.A ⊤} (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2)
  (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (K' : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ)
  (θ : ∀ α, P.Conn (T.U α) (twFα P T K' α))
  (hθ : ∀ α, P.IsBCConn (T.U α) (twKα P T K' α) (θ α))

omit [CompactSpace X] in
/-- Gauging does not change `𝕏⁰` (`ε(β·x) = 0` for `β` of form degree `1`). -/
private theorem gaugedRes_X0comp_tmul (α : T.ι) (M : CohesiveModule (𝒜h P hh hd)) (p : ℤ)
    (β : ↥(P.D.𝒜 (T.U α) 0)) (q : M.Q p) :
    (gaugedRes P T hh hd α M).X0comp p
        (BCGen.tmul ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) M.Q β q) =
      BCGen.tmul ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) M.Q β
        (M.X0comp p q) := by
  refine Eq.trans ?_ (X0comp_bc_tmul ((P.toSheafData.withCurvature h hh hd).D.res
    (le_top : T.U α ≤ ⊤)) M.toQuasiCohesive p β q)
  generalize BCGen.tmul ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    M.Q β q = x
  show DirectSum.component ↥(P.D.𝒜 (T.U α) 0) ℤ _ (p + 1)
      ((gaugedRes P T hh hd α M).X0 (lof ↥(P.D.𝒜 (T.U α) 0) ℤ _ p x)) =
    DirectSum.component ↥((P.toSheafData.withCurvature h hh hd).D.𝒜 (T.U α) 0) ℤ _ (p + 1)
      (bcX0 ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
        M.toQuasiCohesive
        (lof ↥((P.toSheafData.withCurvature h hh hd).D.𝒜 (T.U α) 0) ℤ _ p x))
  refine congrArg (DirectSum.component ↥(P.D.𝒜 (T.U α) 0) ℤ _ (p + 1)) ?_
  unfold QuasiCohesive.X0 gaugedRes CohesiveModule.gauge QuasiCohesive.gauge
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  exact @eps_sub_smul_deg_one ℂ _ _ _ _ (P.D.𝒜 (T.U α)) _ _ (gaugedRes P T hh hd α M).Q _ _ _
    (T.h0 α) (T.h0_mem α) _

omit [CompactSpace X] in
/-- `gr0Ξ e` on `1 ⊗ q` over `⊤`: the `p`-component of `ε(e(1 ⊗ q))` (copy of the private
`gr0ΞV_topO` of `EssSurjCore.lean`, over a general `U`). -/
private theorem gr0ΞV_topO' {U : Opens X}
    {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} {θ : P.Conn U F}
    {M : CohesiveModule (P.D.𝒜 U)} (e : Z0 M.toQuasiCohesive (θ.N (topO U))) (p : ℤ)
    (q : M.Q p) :
    PreResolvingData.gr0ΞV e p (topO U)
        (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q) =
      Tot.eps (P.D.𝒜 (topO U).unop.left) (θ.N (topO U)).Q
        (e.1 (Tot.tmul (P.D.𝒜 U) M.Q 1 (lof (P.D.𝒜 U 0) ℤ M.Q p q))) p := by
  have key : PreResolvingData.ΞV e (topO U)
      (Tot.tmul (P.D.𝒜 (topO U).unop.left) _ 1
        (lof ↥(P.D.𝒜 (topO U).unop.left 0) ℤ _ p
          (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q))) =
      e.1 (Tot.tmul (P.D.𝒜 U) M.Q 1 (lof (P.D.𝒜 U 0) ℤ M.Q p q)) :=
    ((congrArg (PreResolvingData.ΞV e (topO U))
      (tmul_one_lof_eq_bcF (P.D.res (leOfHom (topO U).unop.hom))
      M.toQuasiCohesive p q)).trans (bcLift_bcF _ _)).trans
      (P.tRes_id U F (topO U) _)
  unfold PreResolvingData.gr0ΞV comp0L
  exact congrArg (fun z => Tot.eps (P.D.𝒜 (topO U).unop.left) (θ.N (topO U)).Q z p) key

/-- Generic: `1 ⊗ (β ⊗ q) = β · F(1 ⊗ q)` in the total module of a base change. -/
private theorem tmul_lof_tmul_eq {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
    {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
    (f : DgaHom 𝒜 ℬ) (M : QuasiCohesive 𝒜) (p : ℤ) (β : ℬ 0) (q : M.Q p) :
    Tot.tmul ℬ (BCGen f M.Q) 1 (lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q β q)) =
      (β : B) • bcF f M.Q (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q)) := by
  have hx : lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q β q) =
      β • bcι f M.Q (lof (𝒜 0) ℤ M.Q p q) := by
    rw [bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul]
  have hF1 : Tot.tmul ℬ (BCGen f M.Q) 1 (bcι f M.Q (lof (𝒜 0) ℤ M.Q p q)) =
      bcF f M.Q (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q)) := by
    rw [bcF_tmul, f.map_one']
  rw [hx, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (β : B), hF1]

/-- Generic: `ε(β · w) = β · ε(w)` for `β` of form degree `0`. -/
private theorem eps_smul_deg_zero {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {Q : ℤ → Type}
    [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (β : 𝒜 0) (w : Tot 𝒜 Q) :
    Tot.eps 𝒜 Q ((β : A) • w) = β • Tot.eps 𝒜 Q w := by
  rw [Tot.eps_smul, show Tot.proj0 𝒜 (β : A) = β from
    Subtype.ext ((GCDga.proj_of_mem 𝒜 β.2).trans (by simp))]

/-- The local core (step (D) over `U_α`): for `M = A ⊗ Γ(Pt)` from A11 and `e` with
`(0,0)`-component `e⁰`, the localization `e_α` has `gr0Ξ` a quasi-isomorphism. -/
private theorem quasiIso_local (α : T.ι) {Pt : CochainComplex (Mod (ringOf P.A0)) ℤ}
    (hfree : ∀ n, IsFinFreeSummand (Pt.X n)) (f₀ : Pt ⟶ untwF P T K') [QuasiIso f₀]
    (a b₀ : ℤ) [(PcT P hh hd Pt).IsStrictlyGE a] [(PcT P hh hd Pt).IsStrictlyLE b₀]
    [∀ p, Module.Finite ↥(𝒜h P hh hd 0) ((PcT P hh hd Pt).X p)]
    [∀ p, Module.Projective ↥(𝒜h P hh hd 0) ((PcT P hh hd Pt).X p)]
    (θ' : GenData (𝒜h P hh hd) (Gens (PcT P hh hd Pt)))
    (hθ' : ∀ p (x : Gens (PcT P hh hd Pt) p),
      θ'.θ (lof ↥(𝒜h P hh hd 0) ℤ (Gens (PcT P hh hd Pt)) p x) ∈
        totDeg (𝒜h P hh hd) (Gens (PcT P hh hd Pt)) (p + 1))
    (hflat' : ∀ x, θ'.extend (θ'.θ x) =
      GCDga.c (𝒜 := 𝒜h P hh hd) • Tot.tmul (𝒜h P hh hd) (Gens (PcT P hh hd Pt)) 1 x)
    (hε : ∀ x, Tot.eps (𝒜h P hh hd) (Gens (PcT P hh hd Pt)) (θ'.θ x) = dGen (PcT P hh hd Pt) x)
    (e : (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat').T →ₗ[ℂ]
      (Nh P T hh hd K' θ hθ).T)
    (he : e ∈ Z0 (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat').toQuasiCohesive
      (Nh P T hh hd K' θ hθ))
    (hee : ∀ x, Tot.eps (𝒜h P hh hd) (Nh P T hh hd K' θ hθ).Q
      (e (Tot.tmul (𝒜h P hh hd) (Gens (PcT P hh hd Pt)) 1 x)) =
        e0N (e0MapT P T hh hd K' θ hθ Pt f₀) x) :
    QuasiIso (PreResolvingData.gr0Ξ (eLoc P T hh hd K' θ hθ
      (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat') e he α)) := by
  let φ : ∀ p, (gaugedRes P T hh hd α
      (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q p ≃+
      P.FSec (T.U α) ((restr (ringOf P.A0) (T.U α)).mapHomologicalComplex (ComplexShape.up ℤ)
        |>.obj Pt) p (topO (T.U α)) :=
    fun p => AddEquiv.ofBijective (nuS P T hh hd α (Pt.X p)) (nuS_bij P T hh hd α (hfree p))
  have hφ : ∀ p (r : ↥(P.D.𝒜 (T.U α) 0))
      (q : (gaugedRes P T hh hd α
        (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q p),
      φ p (r • q) = (show ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) from r) • φ p q :=
    fun p r q => nuS_smul P T hh hd α (Pt.X p) r q
  have hX0 : ∀ p (q : (gaugedRes P T hh hd α
        (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q p),
      φ (p + 1) ((gaugedRes P T hh hd α
        (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).X0comp p q) =
      P.fD (T.U α) ((restr (ringOf P.A0) (T.U α)).mapHomologicalComplex (ComplexShape.up ℤ)
        |>.obj Pt) p (topO (T.U α)) (φ p q) := by
    have hX : ∀ p (q : (PcT P hh hd Pt).X p),
        (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat').X0comp p q =
          ((PcT P hh hd Pt).d p (p + 1)).hom q := by
      intro p q
      have h : (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat').X0
          (lof ↥(𝒜h P hh hd 0) ℤ (Gens (PcT P hh hd Pt)) p q) =
          lof ↥(𝒜h P hh hd 0) ℤ (Gens (PcT P hh hd Pt)) (p + 1)
            (((PcT P hh hd Pt).d p (p + 1)).hom q) := by
        show Tot.eps (𝒜h P hh hd) (Gens (PcT P hh hd Pt))
          (θ'.extend (Tot.tmul (𝒜h P hh hd) (Gens (PcT P hh hd Pt)) 1 _)) = _
        rw [GenData.extend_tmul_one, hε]
        exact dGen_lof _ p q
      show DirectSum.component ↥(𝒜h P hh hd 0) ℤ (Gens (PcT P hh hd Pt)) (p + 1)
        ((CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat').X0
          (lof ↥(𝒜h P hh hd 0) ℤ (Gens (PcT P hh hd Pt)) p q)) = _
      rw [h, DirectSum.component.lof_self]
    intro p q
    change BCGen ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
      (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat').Q p at q
    induction q using BCGen.induction_on with
    | ht β q₀ =>
      rw [gaugedRes_X0comp_tmul P T hh hd α _ p β q₀]
      show nuS P T hh hd α (Pt.X (p + 1)) (TensorProduct.tmul ↥(𝒜h P hh hd 0) β
          ((CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat').X0comp p q₀)) =
        P.fD (T.U α) ((restr (ringOf P.A0) (T.U α)).mapHomologicalComplex (ComplexShape.up ℤ)
          |>.obj Pt) p (topO (T.U α)) (nuS P T hh hd α (Pt.X p)
            (TensorProduct.tmul ↥(𝒜h P hh hd 0) β q₀))
      rw [hX p q₀]
      refine (nuS_tmul P T hh hd α (Pt.X (p + 1)) β _).trans ?_
      refine Eq.trans ?_ (congrArg (P.fD (T.U α)
        ((restr (ringOf P.A0) (T.U α)).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj Pt) p
        (topO (T.U α))) (nuS_tmul P T hh hd α (Pt.X p) β q₀)).symm
      refine Eq.trans (congrArg ((show Bα P T hh hd α from β) • ·)
        (rhoS_nat P T hh hd α (Pt.d p (p + 1)) q₀)) ?_
      exact (((restr (ringOf P.A0) (T.U α)).map (Pt.d p (p + 1))).val.app
        (topO (T.U α))).hom.map_smul (show Bα P T hh hd α from β) _ |>.symm
    | hadd x y hx hy =>
      refine (congrArg (φ (p + 1)) (map_add _ x y)).trans ((map_add _ _ _).trans
        ((congrArg₂ (· + ·) hx hy).trans ((map_add _ _ _).symm.trans
          (congrArg _ (map_add _ x y).symm))))
  let g : ((restr (ringOf P.A0) (T.U α)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Pt ⟶
      twFα P T K' α :=
    ((restr (ringOf P.A0) (T.U α)).mapHomologicalComplex (ComplexShape.up ℤ)).map f₀ ≫
      (untwFRestrIso P T K' α).hom
  have hg : ∀ p (q : (gaugedRes P T hh hd α
        (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q p),
      PreResolvingData.gr0ΞV (eLoc P T hh hd K' θ hθ
        (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat') e he α) p
        (topO (T.U α)) (BCGen.tmul (P.D.res (leOfHom (topO (T.U α)).unop.hom)) _ 1 q) =
      ((g.f p).val.app (topO (T.U α))).hom (φ p q) := by
    intro p q
    refine (gr0ΞV_topO' P (eLoc P T hh hd K' θ hθ
      (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat') e he α) p q).trans ?_
    change BCGen ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
      (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat').Q p at q
    induction q using BCGen.induction_on with
    | ht β q₀ =>
      have H1 := tmul_lof_tmul_eq ((P.toSheafData.withCurvature h hh hd).D.res
        (le_top : T.U α ≤ ⊤)) (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ'
        hflat').toQuasiCohesive p β q₀
      refine (congrArg (fun z => (Tot.eps (P.D.𝒜 (topO (T.U α)).unop.left)
        ((θ α).N (topO (T.U α))).Q ((eLoc P T hh hd K' θ hθ
          (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat') e he α).1 z)) p)
        H1).trans ?_
      have key : (Tot.eps (P.D.𝒜 (topO (T.U α)).unop.left) ((θ α).N (topO (T.U α))).Q
          ((eLoc P T hh hd K' θ hθ (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ'
            hflat') e he α).1 (bcF ((P.toSheafData.withCurvature h hh hd).D.res
              (le_top : T.U α ≤ ⊤)) (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ'
                hflat').Q (Tot.tmul (𝒜h P hh hd) (Gens (PcT P hh hd Pt)) 1
                  (lof ↥(𝒜h P hh hd 0) ℤ (Gens (PcT P hh hd Pt)) p q₀))))) p =
          πgen P T K' α p (((e0MapT P T hh hd K' θ hθ Pt f₀).f p).hom q₀) := by
        refine (congrArg (fun z => (Tot.eps (P.D.𝒜 (topO (T.U α)).unop.left)
          ((θ α).N (topO (T.U α))).Q z) p) (eLoc_bcF P T hh hd K' θ hθ _ e he α _)).trans ?_
        refine (congrArg (fun z => z p) (eps_totMapAlong (resα P T α) (πgen P T K' α)
          (πgen_smul P T K' α) _)).trans ?_
        have h2 := (hee (lof ↥(𝒜h P hh hd 0) ℤ (Gens (PcT P hh hd Pt)) p q₀)).trans
          (e0N_lof (e0MapT P T hh hd K' θ hθ Pt f₀) p q₀)
        refine (congrArg (fun z => (famMap (πgen P T K' α) z) p) h2).trans ?_
        exact (congrArg (fun z => z p) (famMap_of (πgen P T K' α) p _)).trans
          (DirectSum.of_eq_same p _)
      refine (congrArg (fun z => (Tot.eps (P.D.𝒜 (topO (T.U α)).unop.left)
        ((θ α).N (topO (T.U α))).Q z) p) (hom0_smul (eLoc P T hh hd K' θ hθ
          (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat') e he α).2.1 _ _)).trans ?_
      refine (DFunLike.congr_fun (eps_smul_deg_zero (𝒜 := P.D.𝒜 (topO (T.U α)).unop.left)
        (Q := ((θ α).N (topO (T.U α))).Q)
        (show ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) from β) _) p).trans ?_
      refine (DirectSum.smul_apply (show ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) from β) _ p).trans ?_
      refine (congrArg ((show ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) from β) • ·) key).trans ?_
      refine Eq.trans ?_ (((g.f p).val.app (topO (T.U α))).hom.map_smul
        (show Bα P T hh hd α from β) (rhoS P T hh hd α (Pt.X p) q₀)).symm
      refine congrArg ((show ↥(P.D.𝒜 (topO (T.U α)).unop.left 0) from β) • ·) ?_
      exact (congrArg (untwistComp P T (K'.X p) α (le_refl (T.U α)))
        (rhoS_nat P T hh hd α (f₀.f p) q₀)).trans rfl
    | hadd x y hx hy =>
      have e1 := map_add (lof ↥(P.D.𝒜 (T.U α) 0) ℤ (gaugedRes P T hh hd α
        (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q p) x y
      have e2 := Tot.tmul_add (𝒜 := P.D.𝒜 (T.U α))
        (Q := (gaugedRes P T hh hd α
          (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q) 1
        (lof ↥(P.D.𝒜 (T.U α) 0) ℤ (gaugedRes P T hh hd α
          (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q p x)
        (lof ↥(P.D.𝒜 (T.U α) 0) ℤ (gaugedRes P T hh hd α
          (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q p y)
      refine (congrArg (fun z => (Tot.eps (P.D.𝒜 (topO (T.U α)).unop.left)
        ((θ α).N (topO (T.U α))).Q ((eLoc P T hh hd K' θ hθ
          (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat') e he α).1
            (Tot.tmul (P.D.𝒜 (T.U α)) (gaugedRes P T hh hd α
              (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat')).Q 1 z))) p)
        e1).trans ?_
      refine (congrArg (fun z => (Tot.eps (P.D.𝒜 (topO (T.U α)).unop.left)
        ((θ α).N (topO (T.U α))).Q ((eLoc P T hh hd K' θ hθ
          (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat') e he α).1 z)) p)
        e2).trans ?_
      refine Eq.trans ?_ (congrArg (ModuleCat.Hom.hom ((g.f p).val.app (topO (T.U α))))
        (map_add (φ p) x y)).symm
      refine Eq.trans ?_ (map_add (ModuleCat.Hom.hom ((g.f p).val.app (topO (T.U α)))) _ _).symm
      refine (congrArg (fun z => (Tot.eps (P.D.𝒜 (topO (T.U α)).unop.left)
        ((θ α).N (topO (T.U α))).Q z) p) (map_add (eLoc P T hh hd K' θ hθ
          (CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat') e he α).1 _ _)).trans ?_
      exact (DFunLike.congr_fun (map_add (Tot.eps (P.D.𝒜 (topO (T.U α)).unop.left)
        ((θ α).N (topO (T.U α))).Q) _ _) p).trans
        ((DirectSum.add_apply _ _ p).trans (congrArg₂ (· + ·) hx hy))
  have : QuasiIso g := by
    have h1 : QuasiIso (((restr (ringOf P.A0) (T.U α)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f₀) := inferInstance
    have h2 : IsIso (untwFRestrIso P T K' α).hom := Iso.isIso_hom _
    have h3 : QuasiIso (untwFRestrIso P T K' α).hom := quasiIso_of_isIso _
    exact quasiIso_comp _ _ (hφ := h1) (hφ' := h3)
  exact PreResolvingData.quasiIso_gr0Ξ_of_equiv P _ _ φ hφ
    (fun n => IsFinFreeSummand.restr (ringOf P.A0) (T.U α) (hfree n)) hX0 _ _ hg

/-- **Z3.u (G′ (i), (k)).** [A, Prop 7.2.18, Rem 7.2.4, §7.4], blueprint-tw G.6–G.8. Given a
strictly perfect complex `Pt` of `𝒜⁰`-modules and a quasi-isomorphism `f⁰ : Pt → F` onto
`F = untwist(K')`, there are a cohesive module `M` over the curved algebra `(𝒜(X), h)` and a
closed morphism `e : M → N^h` (A11 with `(0,0)`-component `Γ(f⁰)`, `N^h = (F^•(X), θ^h)`) such
that for every `α` the localization `e_α : gauge_{h⁰_α}(M|U_α) → N_α` has `gr0Ξ_{e_α}` a
quasi-isomorphism. -/
theorem exists_twisted_lift {Pt : CochainComplex (Mod (ringOf P.A0)) ℤ}
    (hPt : IsStrictlyPerfect Pt) (f₀ : Pt ⟶ untwF P T K') [QuasiIso f₀] :
    ∃ (M : CohesiveModule (𝒜h P hh hd)) (e : M.T →ₗ[ℂ] (Nh P T hh hd K' θ hθ).T)
      (he : e ∈ Z0 M.toQuasiCohesive (Nh P T hh hd K' θ hθ)),
      ∀ α, QuasiIso (PreResolvingData.gr0Ξ (eLoc P T hh hd K' θ hθ M e he α)) := by
  classical
  obtain ⟨⟨a, b₀, ha, hb⟩, hfree⟩ := hPt
  have : (PcT P hh hd Pt).IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
      Functor.map_isZero (globalSections (ringOf P.A0)) (Pt.isZero_of_isStrictlyGE a i hi)
  have : (PcT P hh hd Pt).IsStrictlyLE b₀ :=
    (CochainComplex.isStrictlyLE_iff _ b₀).2 fun i hi =>
      Functor.map_isZero (globalSections (ringOf P.A0)) (Pt.isZero_of_isStrictlyLE b₀ i hi)
  have : ∀ p, Module.Finite ↥(𝒜h P hh hd 0) ((PcT P hh hd Pt).X p) :=
    fun p => finite_globalSections (hfree p)
  have : ∀ p, Module.Projective ↥(𝒜h P hh hd 0) ((PcT P hh hd Pt).X p) :=
    fun p => projective_globalSections (hfree p)
  have : ∀ q, Module.Flat ↥(𝒜h P hh hd 0) (GCDga.piece (𝒜h P hh hd) q) :=
    fun q => P.flat_piece q
  have := quasiIso_e0MapT P T hh hd K' θ hθ Pt f₀
  obtain ⟨θ', hθ', hflat', hε, e, he, hee⟩ :=
    lifting (Nh P T hh hd K' θ hθ) a b₀ (e0MapT P T hh hd K' θ hθ Pt f₀)
  exact ⟨CohesiveModule.ofGenData (PcT P hh hd Pt) a b₀ θ' hθ' hflat', e, he,
    fun α => quasiIso_local P T hh hd K' θ hθ α hfree f₀ a b₀ θ' hθ' hflat' hε e he hee⟩

end Cohesive
