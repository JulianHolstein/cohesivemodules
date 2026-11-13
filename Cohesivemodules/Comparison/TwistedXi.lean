import Cohesivemodules.Comparison.TwistedCurvedModel

set_option linter.style.header false

/-!
# Z3.u: the comparison `Ξ^tw : J_T(M) → T^tw(K')` (blueprint-tw G′ (k))

Blueprint item Z3.u (`blueprint/blueprint-tw.md` §3 G′ (k); G.8). For pre-resolving data `P`
(`X` compact), a twist datum `T` for a closed `h ∈ 𝒜²(X)`, a complex `K'` of `ȟ`-twisted
`O`-modules with C7.b connections `θ_α` on `F_{K'_α}`, a cohesive module `M` over `(𝒜(X), h)` and
a closed `e : M → N^h` (Z3.t):
* `eLoc α ∈ Z0(gauge_{h⁰_α}(M|U_α), N_α)`: the localization of `e` (`exists_eα`, G′ (j));
* `twXiComp n α`: in degree `n` and component `α`, `twLocalIso` (D.6) followed by C7.e's
  `Ξ_{e_α}` and the identification `twCompIso` of the component of `T^tw(K')` with `θ_α.TC`;
* `twXiComp_comm`: these components commute with the gluings (`u_αβ·` on `J_T(M)`, `φ^T` on
  `T^tw(K')`; G′ (g));
* `twXi : J_T(M) → T^tw(K')`, a morphism of complexes of twisted sheaves;
* `quasiIso_twXi`: `Ξ^tw` is a quasi-isomorphism if every `gr0Ξ_{e_α}` is (C7.f componentwise).

## Deviations
* None.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum
open PreResolvingData (topO)

variable {X : Type} [TopologicalSpace X] [CompactSpace X] (P : PreResolvingData X)
  {h : P.D.A ⊤} (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2)
  (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (K' : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ)
  (θ : ∀ α, P.Conn (T.U α) (twFα P T K' α))
  (hθ : ∀ α, P.IsBCConn (T.U α) (twKα P T K' α) (θ α))
  (M : CohesiveModule (𝒜h P hh hd)) (e : M.T →ₗ[ℂ] (Nh P T hh hd K' θ hθ).T)
  (he : e ∈ Z0 M.toQuasiCohesive (Nh P T hh hd K' θ hθ))

/-- **Z3.u (G′ (j)).** The localization `e_α ∈ Z0(gauge_{h⁰_α}(M|U_α), N_α)` of `e`, with
`e_α(1 ⊗ x) = π_α(e x)` (a choice in `exists_eα`). -/
def eLoc (α : T.ι) :
    Z0 (gaugedRes P T hh hd α M).toQuasiCohesive ((θ α).N (topO (T.U α))) :=
  ⟨(exists_eα P T hh hd K' θ hθ α M e he).choose,
    (exists_eα P T hh hd K' θ hθ α M e he).choose_spec.1⟩

/-- **Z3.u (G′ (j)).** `eLoc α` on `1 ⊗ x` is `π_α(e x)`. -/
theorem eLoc_bcF (α : T.ι) (x : M.T) :
    (eLoc P T hh hd K' θ hθ M e he α).1
        (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) M.Q x) =
      πTot P T K' α (show TotX P T K' from e x) :=
  (exists_eα P T hh hd K' θ hθ α M e he).choose_spec.2 x

/-- **Z3.u (G′ (k)).** [A, §7.4], blueprint-tw G.8. The component `α` in degree `n` of `Ξ^tw`:
`J_T(M)^n_α ≅ α(gauge(M|U_α))^n` (`twLocalIso`, D.6), then C7.e's `Ξ_{e_α}` into `θ_α.TC`, which
is the component `α` of `T^tw(K')^n` (`twCompIso`). -/
def twXiComp (n : ℤ) (α : T.ι) :
    (TwMod.comp P.toSheafData.O T.U T.ch α).obj ((T.twistedSheafOf hh hd M).X n) ⟶
      (TwMod.comp P.toSheafData.O T.U T.ch α).obj ((twModel P T K' θ hθ).X n) :=
  (twLocalIso P T hh hd α M).hom.f n ≫
    (PreResolvingData.Ξ (eLoc P T hh hd K' θ hθ M e he α)).f n ≫
      (twCompIso P T K' θ hθ α).inv.f n

/-- Generic: `cmpTot` sends `F_{f₂}(x)` to `F_g(F_f(x))` (`cmpTot` is `bcCompTot`). -/
private theorem cmpTot_bcF_gen {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
    {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
    {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]
    (f : DgaHom 𝒜 ℬ) (g : DgaHom ℬ 𝒞) (f₂ : DgaHom 𝒜 𝒞) (hf : g.comp f = f₂)
    (M : QuasiCohesive 𝒜) (x : M.T) :
    cmpTot f g f₂ hf M (bcF f₂ M.Q x) = bcF g (BCGen f M.Q) (bcF f M.Q x) := by
  subst hf
  exact bcCompTot_bcF f g M x

omit [CompactSpace X] in
/-- `twCmp` sends `F(x)` to `F(F(x))`. -/
private theorem twCmp_bcF (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (x : M.T) :
    twCmp P T hh hd α M hα
        (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : W ≤ ⊤)) M.Q x) =
      bcF (P.D.res hα) (gaugedRes P T hh hd α M).Q
        (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) M.Q x) :=
  cmpTot_bcF_gen ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res hα) _ (curved_res_comp_eq P T hh hd α hα)
    M.toQuasiCohesive x

/-- `Ξ_{e_α}` on `F(F(x))` over `W ≤ U_α` is the component `α` of `res_W(e x)`. -/
private theorem xi_bcF (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (x : M.T) :
    PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he α) (ovr hα)
        (twCmp P T hh hd α M hα
          (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : W ≤ ⊤)) M.Q x)) =
      cTotW P T K' α hα (P.tRes ⊤ (twFtop P T K')
        (PreResolvingData.toV (ovr (hα.trans le_top))) (show TotX P T K' from e x)) := by
  rw [twCmp_bcF]
  unfold PreResolvingData.ΞV
  refine (bcLift_bcF _ _).trans ?_
  change P.tRes (T.U α) (twFα P T K' α) (PreResolvingData.toV (ovr hα))
    ((eLoc P T hh hd K' θ hθ M e he α).1 _) = _
  refine (congrArg _ (eLoc_bcF P T hh hd K' θ hθ M e he α x)).trans ?_
  refine (congrArg _ (πTot_eq_cTot P T K' α _)).trans ?_
  have hcomp : PreResolvingData.toV (ovr (le_top : T.U α ≤ ⊤)) ≫ resF le_top hα =
      PreResolvingData.toV (ovr (hα.trans le_top)) :=
    Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))
  have h1 := P.tRes_comp ⊤ (twFtop P T K') (PreResolvingData.toV (ovr (le_top : T.U α ≤ ⊤)))
    (resF le_top hα) (show TotX P T K' from e x)
  rw [hcomp] at h1
  rw [h1]
  exact (cTotW_tRes P T K' α (le_refl (T.U α)) hα _).symm

/-- The two sides of `xi_main` agree on `F(x)` (`xi_bcF` twice, `cTotW_compat`). -/
private theorem xi_main_bcF (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (x : M.T) :
    twTotφ P T K' α β hα hβ (PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he α) (ovr hα)
        (twCmp P T hh hd α M hα
          (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : W ≤ ⊤)) M.Q x))) =
      (Subtype.val ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)) : P.D.A W) •
        PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he β) (ovr hβ)
          (twCmp P T hh hd β M hβ
            (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : W ≤ ⊤)) M.Q x)) := by
  rw [xi_bcF, xi_bcF]
  have hu : (Subtype.val ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)) :
      P.D.A (ovr hβ).unop.left) * (fuA P T α β hα hβ : P.D.A (ovr hβ).unop.left) = 1 := by
    have h1 := (unitRes P.A0 (le_inf hα hβ) (T.u α β)).mul_inv
    have h2 : unitRes P.A0 (le_inf hα hβ) (uInv P T α β) =
        (unitRes P.A0 (le_inf hα hβ) (T.u α β))⁻¹ := map_inv _ _
    have hv : ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β) :
        ↥(P.D.𝒜 (ovr hβ).unop.left 0)) =
        (Units.val (unitRes P.A0 (le_inf hα hβ) (T.u α β)) :
          ↥(P.D.𝒜 (ovr hβ).unop.left 0)) := rfl
    unfold fuA
    rw [h2, hv]
    exact congrArg Subtype.val h1
  have hc := cTotW_compat P T K' α β hα hβ (P.tRes ⊤ (twFtop P T K')
    (PreResolvingData.toV (ovr (hα.trans le_top))) (show TotX P T K' from e x))
  refine Eq.trans ?_ (congrArg (fun w => (Subtype.val ((P.toSheafData.D.res (le_inf hα hβ)).f0
    (T.u α β)) : P.D.A W) • w) hc.symm)
  exact ((smul_smul _ _ _).trans ((congrArg (· • _) hu).trans (one_smul _ _))).symm

/-- Uniqueness (copy of the private `bc_ext_semilinear_mdl` of `ModelDef.lean`): two additive maps
out of `Tot(f^*Q)` that are `g`-semilinear and agree on the image of `F` are equal. -/
private theorem bc_ext_xi {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
    {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
    {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]
    (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ)
    (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    {N : Type} [AddCommGroup N] [Module C N] (ψ ψ' : Tot ℬ (BCGen f Q) →+ N)
    (hs : ∀ (b : B) (y), ψ (b • y) = g b • ψ y)
    (hs' : ∀ (b : B) (y), ψ' (b • y) = g b • ψ' y)
    (h : ∀ x, ψ (bcF f Q x) = ψ' (bcF f Q x)) : ψ = ψ' := by
  have hgen : ∀ e' : ⨁ p, BCGen f Q p,
      ψ (Tot.tmul ℬ _ 1 e') = ψ' (Tot.tmul ℬ _ 1 e') := by
    intro e'
    induction e' using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero, map_zero]
    | of p x =>
      induction x using BCGen.induction_on with
      | ht β q =>
        have hx : DirectSum.of (BCGen f Q) p (BCGen.tmul f Q β q) =
            (β : ℬ 0) • bcι f Q (lof (𝒜 0) ℤ Q p q) := by
          rw [bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul]; rfl
        have hF1 : Tot.tmul ℬ _ 1 (bcι f Q (lof (𝒜 0) ℤ Q p q)) =
            bcF f Q (Tot.tmul 𝒜 Q 1 (lof (𝒜 0) ℤ Q p q)) := by
          rw [bcF_tmul, f.map_one']
        rw [hx, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (β : B), hs, hs', hF1, h]
      | hadd x y hx hy =>
        rw [(DirectSum.of (BCGen f Q) p).map_add, Tot.tmul_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [Tot.tmul_add, map_add, map_add, hx, hy]
  ext x
  induction x using Tot.induction_on with
  | ht b e' => rw [Tot.tmul_eq_smul b e', hs, hs', hgen]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- The key identity on all of `Tot(M|W)` (uniqueness of `bcLift`-type extensions, `xi_main_bcF`):
`φ^T(Ξ_{e_α}(twCmp_α z)) = u_αβ · Ξ_{e_β}(twCmp_β z)`. -/
private theorem xi_main (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (z : (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : W ≤ ⊤)) :
    twTotφ P T K' α β hα hβ (PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he α) (ovr hα)
        (twCmp P T hh hd α M hα z)) =
      (Subtype.val ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)) : P.D.A W) •
        PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he β) (ovr hβ)
          (twCmp P T hh hd β M hβ z) := by
  let f := (P.toSheafData.withCurvature h hh hd).D.res (le_top : W ≤ ⊤)
  let _ : Module ((P.toSheafData.withCurvature h hh hd).D.A W)
    (P.TTot (T.U β) (twFα P T K' β) (ovr hβ)) :=
    inferInstanceAs (Module (P.D.A (ovr hβ).unop.left)
      (P.TTot (T.U β) (twFα P T K' β) (ovr hβ)))
  have key := bc_ext_xi (g := DgaHom.id ((P.toSheafData.withCurvature h hh hd).D.𝒜 W))
    (f := f) (Q := M.Q)
    (N := P.TTot (T.U β) (twFα P T K' β) (ovr hβ))
    ((twTotφ P T K' α β hα hβ).comp ((PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he α)
      (ovr hα)).toAddMonoidHom.comp (twCmp P T hh hd α M hα)))
    ((DistribSMul.toAddMonoidHom (P.TTot (T.U β) (twFα P T K' β) (ovr hβ))
      (Subtype.val ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)) :
        P.D.A (ovr hβ).unop.left)).comp
      ((PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he β)
      (ovr hβ)).toAddMonoidHom.comp (twCmp P T hh hd β M hβ)))
    (fun b y => by
      exact (congrArg (twTotφ P T K' α β hα hβ)
        ((congrArg (PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he α) (ovr hα))
          (twCmp_smul P T hh hd α M hα b y)).trans
          (hom0_smul (PreResolvingData.ΞV_mem (eLoc P T hh hd K' θ hθ M e he α) (ovr hα)).1
            (show P.D.A W from b) _))).trans
        (totMapAlong_smul (idAt P T hα hβ) (twGenφ P T K' α β hα hβ)
          (twGenφ_smul P T K' α β hα hβ) _ _))
    (fun b y => by
      have h1 := (congrArg (PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he β) (ovr hβ))
          (twCmp_smul P T hh hd β M hβ b y)).trans
          (hom0_smul (PreResolvingData.ΞV_mem (eLoc P T hh hd K' θ hθ M e he β) (ovr hβ)).1
            (show P.D.A W from b) (twCmp P T hh hd β M hβ y))
      have hcen : (Subtype.val ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)) :
          P.D.A (ovr hβ).unop.left) * (show P.D.A (ovr hβ).unop.left from b) =
          (show P.D.A (ovr hβ).unop.left from b) * (Subtype.val
            ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)) : P.D.A (ovr hβ).unop.left) :=
        GCDga.central (P.D.𝒜 W) ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)).2 _
      exact (congrArg (fun w => (Subtype.val ((P.toSheafData.D.res (le_inf hα hβ)).f0
        (T.u α β)) : P.D.A (ovr hβ).unop.left) • w) h1).trans
        ((smul_smul _ _ _).trans ((congrArg (· • _) hcen).trans (smul_smul _ _ _).symm)))
    (fun x => xi_main_bcF P T hh hd K' θ hθ M e he α β hα hβ x)
  exact DFunLike.congr_fun key z

/-- **Z3.u (G′ (k)).** [A, §7.4]. The components of `Ξ^tw` commute with the gluings: on `J_T(M)`
the gluing is multiplication by `u_αβ` (`twTerm_φ`), on `T^tw(K')` it is `φ^T` (`twModelφ`), and
`φ^T(π_α y) = u_αβ · π_β(y)` (G′ (g)). -/
theorem twXiComp_comm (n : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (x : sec P.toSheafData.O (((T.twistedSheafOf hh hd M).X n).M α) hα) :
    ((twModel P T K' θ hθ).X n).φ α β hα hβ
        (((twXiComp P T hh hd K' θ hθ M e he n α).val.app (ovr hα)).hom x) =
      ((twXiComp P T hh hd K' θ hθ M e he n β).val.app (ovr hβ)).hom
        (((T.twistedSheafOf hh hd M).X n).φ α β hα hβ x) := by
  refine Subtype.ext ?_
  change twTotφ P T K' α β hα hβ (PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he α) (ovr hα)
      (twCmp P T hh hd α M hα x.1)) =
    PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he β) (ovr hβ) (twCmp P T hh hd β M hβ
      ((P.toSheafData.withCurvature h hh hd).smul0L M n le_top
        ((P.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)) x).1)
  refine (xi_main P T hh hd K' θ hθ M e he α β hα hβ x.1).trans ?_
  exact (congrArg (fun w => (Subtype.val ((P.toSheafData.D.res (le_inf hα hβ)).f0
    (T.u α β)) : P.D.A W) • w) rfl).trans
    ((congrArg (PreResolvingData.ΞV (eLoc P T hh hd K' θ hθ M e he β) (ovr hβ))
      (twCmp_smul P T hh hd β M hβ _ x.1)).trans
      (hom0_smul (PreResolvingData.ΞV_mem (eLoc P T hh hd K' θ hθ M e he β) (ovr hβ)).1
        (show P.D.A W from _) _)).symm

/-- **Z3.u (G′ (k)).** `Ξ^tw` in degree `n`, a morphism of twisted sheaves. -/
def twXiN (n : ℤ) : (T.twistedSheafOf hh hd M).X n ⟶ (twModel P T K' θ hθ).X n :=
  ⟨twXiComp P T hh hd K' θ hθ M e he n, twXiComp_comm P T hh hd K' θ hθ M e he n⟩

/-- Pasting three commuting squares in any category. -/
private theorem sq3 {C : Type*} [Category C] {A1 A2 B1 B2 C1 C2 D1 D2 : C}
    (a1 : A1 ⟶ B1) (b1 : B1 ⟶ C1) (c1 : C1 ⟶ D1) (a2 : A2 ⟶ B2) (b2 : B2 ⟶ C2) (c2 : C2 ⟶ D2)
    (dA : A1 ⟶ A2) (dB : B1 ⟶ B2) (dC : C1 ⟶ C2) (dD : D1 ⟶ D2)
    (h1 : a1 ≫ dB = dA ≫ a2) (h2 : b1 ≫ dC = dB ≫ b2) (h3 : c1 ≫ dD = dC ≫ c2) :
    (a1 ≫ b1 ≫ c1) ≫ dD = dA ≫ a2 ≫ b2 ≫ c2 := by
  rw [Category.assoc, Category.assoc, h3, ← Category.assoc b1, h2, Category.assoc,
    ← Category.assoc a1, h1, Category.assoc]

/-- **Z3.u (G′ (k)).** `Ξ^tw` commutes with the differentials (componentwise: `twLocalIso`,
`Ξ_{e_α}` and `twCompIso` are morphisms of complexes). -/
theorem twXiN_comm (i j : ℤ) :
    twXiN P T hh hd K' θ hθ M e he i ≫ (twModel P T K' θ hθ).d i j =
      (T.twistedSheafOf hh hd M).d i j ≫ twXiN P T hh hd K' θ hθ M e he j := by
  refine TwMod.hom_ext fun α => ?_
  have h1 := (twLocalIso P T hh hd α M).hom.comm i j
  have h2 := (PreResolvingData.Ξ (eLoc P T hh hd K' θ hθ M e he α)).comm i j
  have h3 := (twCompIso P T K' θ hθ α).inv.comm i j
  change twXiComp P T hh hd K' θ hθ M e he i α ≫ _ = _ ≫ twXiComp P T hh hd K' θ hθ M e he j α
  unfold twXiComp
  exact sq3 _ _ _ _ _ _ _ _ _ _ h1 h2 h3

/-- **Z3.u (G′ (k)).** [A, §7.4], blueprint-tw G.8. The comparison `Ξ^tw : J_T(M) → T^tw(K')`
of complexes of `ȟ`-twisted sheaves, with components `twLocalIso ≫ Ξ_{e_α} ≫ twCompIso⁻¹`. -/
def twXi : T.twistedSheafOf hh hd M ⟶ twModel P T K' θ hθ where
  f n := twXiN P T hh hd K' θ hθ M e he n
  comm' i j _ := twXiN_comm P T hh hd K' θ hθ M e he i j

/-- Generic: an isomorphism, a quasi-isomorphism and an inverse isomorphism compose to one. -/
private theorem qi3 {C : Type*} [Category C] [Abelian C] {K1 K2 K3 K4 : CochainComplex C ℤ}
    (a : K1 ≅ K2) (f : K2 ⟶ K3) (b : K3 ≅ K4) (hf : QuasiIso f) :
    QuasiIso (a.hom ≫ f ≫ b.hom) := by
  have := Iso.isIso_hom a
  have := Iso.isIso_hom b
  infer_instance

/-- **Z3.u (G′ (k)).** [A, §7.4]. If every `gr0Ξ_{e_α}` is a quasi-isomorphism, then
`Ξ^tw : J_T(M) → T^tw(K')` is a quasi-isomorphism (C7.f `quasiIso_Ξ` in each component;
`quasiIso_of_twComp`). -/
theorem quasiIso_twXi
    (hgr : ∀ α, QuasiIso (PreResolvingData.gr0Ξ (eLoc P T hh hd K' θ hθ M e he α))) :
    QuasiIso (twXi P T hh hd K' θ hθ M e he) := by
  refine quasiIso_of_twComp P T _ fun α => ?_
  have hE : ((TwMod.comp P.toSheafData.O T.U T.ch α).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (twXi P T hh hd K' θ hθ M e he) =
      (twLocalIso P T hh hd α M).hom ≫ PreResolvingData.Ξ (eLoc P T hh hd K' θ hθ M e he α) ≫
        (twCompIso P T K' θ hθ α).inv :=
    HomologicalComplex.hom_ext _ _ fun n => rfl
  rw [hE]
  have h1 : QuasiIso (PreResolvingData.Ξ (eLoc P T hh hd K' θ hθ M e he α)) :=
    PreResolvingData.quasiIso_Ξ _ (hgr α)
  exact qi3 (twLocalIso P T hh hd α M) _ (twCompIso P T K' θ hθ α).symm h1

end Cohesive
