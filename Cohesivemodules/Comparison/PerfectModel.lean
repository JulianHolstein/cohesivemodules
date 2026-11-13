import Cohesivemodules.Comparison.PerfectLoc
import Cohesivemodules.Comparison.ModelConn
import Cohesivemodules.Comparison.ModelTensor
import Cohesivemodules.Comparison.EssSurjAux

set_option linter.style.header false

/-!
# C2 core via the explicit model C7

Blueprint item C2 (§4, v1.11 "Proof via C7"). For `W` a bounded complex of finitely generated
projective `O(U)`-modules, `L` its strictly perfect lift (S4.c on the over-site, `ε : Γ L ≅ W`)
and `u : L → α_U(𝒜(U) ⊗ W)` with `Γ u = ε ⋙ (w ↦ 1 ⊗ 1 ⊗ w)`: `u` is a quasi-isomorphism.

Proof (`quasiIso_of_gamma_eq`): take the connection `θ` on `F_L = 𝒜⁰ ⊗_R L` (C7.b) and the closed
map `e : 𝒜(U) ⊗ W → N_L(U)`, `1 ⊗ 1 ⊗ w ↦ 1 ⊗ η(ε⁻¹ w)` (`exists_fcToN`). Then
* `gr0Ξ e` is an isomorphism (`isIso_gr0Ξ_fc`): both sides are summands of finite free
  `𝒜⁰|U`-modules with the same global sections (S4.c on the over-site);
* so `Ξ_e` is a quasi-isomorphism (C7.f);
* `u ≫ Ξ_e = ιT` (`comp_Ξ_eq_ιT`, both determined by `Γ`), a quasi-isomorphism (C7.d; `L` is
  K-flat);
* hence `u` is one (2-out-of-3).

## Deviations
* `X` compact Hausdorff (v1.11, C7.a). Stated for the lift `L` of `W` rather than for `W̃`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X)
  (W : CochainComplex (ModuleCat.{0} (P.O.obj.obj (op U))) ℤ)
  (hW : IsBoundedFGProj (P.O.obj.obj (op U)) W)
  (L : CochainComplex (Mod (P.R.over U)) ℤ)
  (ε : ((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ≅ W)

/-- **C2 via C7.** The element `1 ⊗ η(ε⁻¹ w)` of `𝒜(U) ⊗_{𝒜⁰(U)} ⨁_p F_L^p(U)`, for `w ∈ W^p`. -/
def ηTot (p : ℤ) (w : W.X p) : P.TTot U (P.FK U L) (topO U) :=
  Tot.tmul (P.D.𝒜 (topO U).unop.left) (P.FSec U (P.FK U L) · (topO U)) 1
    (lof ↥(P.D.𝒜 (topO U).unop.left 0) ℤ (P.FSec U (P.FK U L) · (topO U)) p
      (P.bcη U L p (topO U) ((ε.inv.f p).hom w)))

/-- The unit `η` is `ρ`-semilinear: `η(r k) = ρ(r) η(k)`. -/
private theorem bcη_smul (p : ℤ) (V : (Over U)ᵒᵖ) (r : (P.R.over U).obj.obj V)
    (k : (L.X p).val.obj V) :
    P.bcη U L p V (r • k) = (P.ρ V.unop.left r : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U L p V k := by
  have := (((sheafBCAdj (overHom P.ρSheaf U)).unit.app (L.X p)).val.app V).hom.map_smul r k
  exact this

/-- `ηTot` is additive. -/
private theorem ηTot_add (p : ℤ) (w w' : W.X p) :
    P.ηTot U W L ε p (w + w') = P.ηTot U W L ε p w + P.ηTot U W L ε p w' := by
  have h0 : (ε.inv.f p).hom (w + w') = (ε.inv.f p).hom w + (ε.inv.f p).hom w' := map_add _ _ _
  have key : P.bcη U L p (topO U) ((ε.inv.f p).hom (w + w')) =
      P.bcη U L p (topO U) ((ε.inv.f p).hom w) + P.bcη U L p (topO U) ((ε.inv.f p).hom w') :=
    (congrArg (P.bcη U L p (topO U)) h0).trans
      ((P.bcη U L p (topO U)).map_add ((ε.inv.f p).hom w) ((ε.inv.f p).hom w'))
  unfold ηTot
  rw [key, map_add, Tot.tmul_add]

/-- `ηTot` is `ρ`-semilinear: `η(r w) = ρ(r) η(w)`. -/
private theorem ηTot_smul (p : ℤ) (r : P.O.obj.obj (op U)) (w : W.X p) :
    P.ηTot U W L ε p (r • w) =
      (P.ρ (topO U).unop.left r : P.D.A (topO U).unop.left) • P.ηTot U W L ε p w := by
  have h1 := (ε.inv.f p).hom.map_smul (show (P.R.over U).obj.obj (topO U) from r) w
  have h2 := P.bcη_smul U L p (topO U) (show (P.R.over U).obj.obj (topO U) from r)
    ((ε.inv.f p).hom w)
  have key : P.bcη U L p (topO U) ((ε.inv.f p).hom (r • w)) =
      (P.ρ (topO U).unop.left r : ↥(P.D.𝒜 (topO U).unop.left 0)) •
        P.bcη U L p (topO U) ((ε.inv.f p).hom w) :=
    (congrArg (P.bcη U L p (topO U)) h1).trans h2
  unfold ηTot
  rw [key, map_smul, Tot.tmul_smul0, one_mul, Tot.smul_tmul, mul_one]

/-- A10.a with closedness: a `ρ`-semilinear family `f_p : W^p → N` of degree `0` that commutes
with the differentials extends to a closed degree-`0` map `𝒜(U) ⊗ W → N`. -/
private theorem exists_closed_ext (N : QuasiCohesive (P.D.𝒜 U))
    (f : ∀ p, W.X p →ₛₗ[P.ρ U] N.T) (hf : f ∈ HomR (P.ρ U) W N 0)
    (hX : ∀ p w, N.X (f p w) = f (p + 1) (dW W p w)) :
    ∃ e : Z0 (P.fcMod U W hW).toQuasiCohesive N, ∀ (p : ℤ) (w : W.X p),
      e.1 (fcι (P.ρ U) W w) = f p w := by
  have hρ := P.d_ρ U
  have hc := P.c_eq_zero U
  have hres := fcResP_fcExt W hρ hc N 0 ⟨f, hf⟩
  refine ⟨⟨(fcExt W hρ hc N 0 ⟨f, hf⟩).1, ?_⟩, fun p w => ?_⟩
  · refine Submodule.mem_inf.2 ⟨(fcExt W hρ hc N 0 ⟨f, hf⟩).2, LinearMap.mem_ker.2 ?_⟩
    refine fc_hom_ext W hρ hc N (n := 0 + 1) (δ_mem _ N (fcExt W hρ hc N 0 ⟨f, hf⟩).2)
      (zero_mem _) (fun p w => ?_)
    have h := congrArg (fun g => g p w)
      (fcResP_δ W hρ hc N 0 (fcExt W hρ hc N 0 ⟨f, hf⟩))
    simp only [homRδ, LinearMap.coe_mk, AddHom.coe_mk, fcResP_apply] at h
    have e1 : (fcExt W hρ hc N 0 ⟨f, hf⟩).1 (fcι (P.ρ U) W w) = f p w :=
      congrArg (fun g => g p w) hres
    have e2 : (fcExt W hρ hc N 0 ⟨f, hf⟩).1 (fcι (P.ρ U) W (dW W p w)) =
        f (p + 1) (dW W p w) := congrArg (fun g => g (p + 1) (dW W p w)) hres
    rw [e1, e2, ← hX, Int.negOnePow_zero, one_smul, sub_self] at h
    exact h
  · exact congrArg (fun g => g p w) hres

/-- The quasi-cohesive `𝒜(U)`-module `N_{topO U}` of a connection (`topO U` is `U` up to `rfl`). -/
private def topN (θ : P.Conn U (P.FK U L)) : QuasiCohesive (P.D.𝒜 U) := θ.N (topO U)

/-- `η(ε⁻¹ ·)` as a `ρ`-semilinear family of generator maps into `N_{topO U}`. -/
private def ηLin (θ : P.Conn U (P.FK U L)) (p : ℤ) : W.X p →ₛₗ[P.ρ U] (P.topN U L θ).T where
  toFun := P.ηTot U W L ε p
  map_add' := P.ηTot_add U W L ε p
  map_smul' := fun r w => by
    have h := P.ηTot_smul U W L ε p r w
    exact h.trans (Tot.smul0_eq _ _).symm

/-- `η(ε⁻¹ ·)` has degree `0`. -/
private theorem ηLin_mem (θ : P.Conn U (P.FK U L)) :
    P.ηLin U W L ε θ ∈ HomR (P.ρ U) W (P.topN U L θ) 0 := fun p w => by
  show P.ηTot U W L ε p w ∈ totDeg (P.D.𝒜 (topO U).unop.left) _ (p + 0)
  rw [add_zero]
  exact tmul_bcη_mem p (topO U) _

/-- `𝕏 η(ε⁻¹ w) = η(ε⁻¹ d_W w)` (`IsBCConn` and `ε` a chain map). -/
private theorem ηLin_X (θ : P.Conn U (P.FK U L)) (hθ : P.IsBCConn U L θ) (p : ℤ) (w : W.X p) :
    (P.topN U L θ).X (P.ηLin U W L ε θ p w) = P.ηLin U W L ε θ (p + 1) (dW W p w) := by
  have hk := hθ (topO U) p ((ε.inv.f p).hom w)
  have hc := congrArg (fun g => g.hom w) (ε.inv.comm p (p + 1))
  have hd : P.kD U L p (topO U) ((ε.inv.f p).hom w) = (ε.inv.f (p + 1)).hom (dW W p w) := by
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
    have h3 : P.kD U L p (topO U) ((ε.inv.f p).hom w) =
        ((((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).d p (p + 1)).hom ((ε.inv.f p).hom w) := rfl
    refine h3.trans ?_
    exact hc
  show (θ.θ (topO U)).extend (P.ηTot U W L ε p w) = P.ηTot U W L ε (p + 1) (dW W p w)
  unfold ηTot
  rw [GenData.extend_tmul_one, hk, hd]

/-- `Ξ_e` on the image of `F`: `ΞV e V (F x) = res_V (e x)` (`bcLift_bcF`). -/
private theorem ΞV_bcF {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} {θ : P.Conn U F}
    {M : CohesiveModule (P.D.𝒜 U)} (e : Z0 M.toQuasiCohesive (θ.N (topO U))) (V : (Over U)ᵒᵖ)
    (x : M.T) :
    ΞV e V (bcF (P.D.res (leOfHom V.unop.hom)) M.Q x) = P.tRes U F (toV V) (e.1 x) :=
  bcLift_bcF _ x

/-- **C2 via C7.** The closed degree-`0` map `e : 𝒜(U) ⊗_{O(U)} W → N_L(U)` with
`e(1 ⊗ 1 ⊗ w) = 1 ⊗ η(ε⁻¹ w)` (A10 generators; closed because `∇(η l) = 0`, `IsBCConn`, and `ε`
is a chain map). -/
theorem exists_fcToN [CompactSpace X] (θ : P.Conn U (P.FK U L)) (hθ : P.IsBCConn U L θ) :
    ∃ e : Z0 (P.fcMod U W hW).toQuasiCohesive (θ.N (topO U)),
      ∀ (p : ℤ) (w : W.X p), e.1 (fcι (P.ρ U) W w) =
        P.ηTot U W L ε p w := by
  exact P.exists_closed_ext U W hW (P.topN U L θ) (P.ηLin U W L ε θ) (P.ηLin_mem U W L ε θ)
    (P.ηLin_X U W L ε θ hθ)

/-- On global sections, `gr0Ξ e (1 ⊗ (1 ⊗ w)) = η(ε⁻¹ w)`. -/
private theorem gr0ΞV_top_one [CompactSpace X] (θ : P.Conn U (P.FK U L))
    (e : Z0 (P.fcMod U W hW).toQuasiCohesive (θ.N (topO U)))
    (he : ∀ (p : ℤ) (w : W.X p), e.1 (fcι (P.ρ U) W w) =
        P.ηTot U W L ε p w) (p : ℤ) (w : W.X p) :
    gr0ΞV e p (topO U)
      (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1
        (FCGen.tmul (P.ρ U) W 1 w)) = P.bcη U L p (topO U) ((ε.inv.f p).hom w) := by
  have key : ΞV e (topO U)
      (Tot.tmul (P.D.𝒜 (topO U).unop.left) _ 1
        (lof ↥(P.D.𝒜 (topO U).unop.left 0) ℤ _ p (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom))
          (P.fcMod U W hW).Q 1 (FCGen.tmul (P.ρ U) W 1 w)))) = P.ηTot U W L ε p w :=
    ((congrArg (ΞV e (topO U)) (tmul_one_lof_eq_bcF (P.D.res (leOfHom (topO U).unop.hom))
      (P.fcMod U W hW).toQuasiCohesive p (FCGen.tmul (P.ρ U) W 1 w))).trans
      (P.ΞV_bcF U e (topO U) (fcι (P.ρ U) W w))).trans
      ((congrArg _ (he p w)).trans (P.tRes_id U (P.FK U L) (topO U) _))
  unfold gr0ΞV comp0L
  refine (congrArg (fun z => (Tot.eps (P.D.𝒜 (topO U).unop.left) (θ.N (topO U)).Q z) p)
    key).trans ?_
  unfold ηTot
  have h3 := Tot.eps_oneTmul (𝒜 := P.D.𝒜 (topO U).unop.left)
    (Q := (P.FSec U (P.FK U L) · (topO U)))
    (lof ↥(P.D.𝒜 (topO U).unop.left 0) ℤ (P.FSec U (P.FK U L) · (topO U)) p
      (P.bcη U L p (topO U) ((ε.inv.f p).hom w)))
  refine (DFunLike.congr_fun h3 p).trans ?_
  exact DirectSum.of_eq_same p _

/-- The map `Γ L^p → Γ(G0^p)`, `l ↦ 1 ⊗ (1 ⊗ ε l)`, `O(U)`-linear. -/
private def k0 (p : ℤ) : (gammaT (P.R.over U) (Over.mk (𝟙 U))).obj (L.X p) ⟶
    (ModuleCat.restrictScalars
      (show (P.R.over U).obj.obj (topO U) →+* ((ringOf P.A0).over U).obj.obj (topO U)
        from P.ρ U)).obj
      ((P.G0Sh U (P.fcMod U W hW) p).val.obj (topO U)) :=
  ModuleCat.semilinearMapAddEquiv
    (show (P.R.over U).obj.obj (op (Over.mk (𝟙 U))) →+*
      ((ringOf P.A0).over U).obj.obj (topO U) from P.ρ U)
    ((gammaT (P.R.over U) (Over.mk (𝟙 U))).obj (L.X p))
    ((P.G0Sh U (P.fcMod U W hW) p).val.obj (topO U))
    { toFun := fun l => (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1
        (FCGen.tmul (P.ρ U) W 1 ((ε.hom.f p).hom l)) :
          (P.G0Sh U (P.fcMod U W hW) p).val.obj (topO U))
      map_add' := fun l l' =>
        (congrArg (fun w => BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom))
          (P.fcMod U W hW).Q 1 (FCGen.tmul (P.ρ U) W 1 w)) (map_add (ε.hom.f p).hom l l')).trans
          ((congrArg (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1 ·)
            (FCGen.tmul_add 1 _ _)).trans (BCGen.tmul_add _ _ _))
      map_smul' := fun r l => by
        let r' : P.O.obj.obj (op U) := r
        have h1 : (ε.hom.f p).hom (r • l) = r' • (ε.hom.f p).hom l :=
          (ε.hom.f p).hom.map_smul r l
        have h2 : FCGen.tmul (P.ρ U) W 1 ((ε.hom.f p).hom (r • l)) =
            (P.ρ U r' : ↥(P.D.𝒜 U 0)) • FCGen.tmul (P.ρ U) W 1 ((ε.hom.f p).hom l) := by
          rw [h1, FCGen.tmul_smulR, mul_one, FCGen.smul_tmul, mul_one]
        have h3 := BCGen.tmul_smul0 (f := P.D.res (leOfHom (topO U).unop.hom))
          (Q := (P.fcMod U W hW).Q) (P.ρ U r')
          (FCGen.tmul (P.ρ U) W 1 ((ε.hom.f p).hom l))
        have h4 : (P.D.res (leOfHom (topO U).unop.hom)).f0 (P.ρ U r') = P.ρ U r' :=
          Subtype.ext (P.D.res_id _ _)
        rw [h4] at h3
        refine (congrArg (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom))
          (P.fcMod U W hW).Q 1 ·) h2).trans ?_
        exact h3 }

/-- Degree `p` of `isIso_gr0Ξ_fc`. -/
private theorem isIso_gr0Ξn [CompactSpace X] (hL : IsStrictlyPerfect L)
    (θ : P.Conn U (P.FK U L))
    (e : Z0 (P.fcMod U W hW).toQuasiCohesive (θ.N (topO U)))
    (he : ∀ (p : ℤ) (w : W.X p), e.1 (fcι (P.ρ U) W w) =
        P.ηTot U W L ε p w) (p : ℤ) :
    IsIso (gr0Ξn e p) := by
  obtain ⟨h, hh⟩ := (bijective_gammaT_map (R := P.R.over U) (Over.mkIdTerminal (X := U))
    (hL.2 p) ((SheafOfModules.restrictScalars.{0} (ringHomOf (overHom P.ρSheaf U))).obj
      (P.G0Sh U (P.fcMod U W hW) p))).2 (by exact P.k0 U W hW L ε p)
  let adj := sheafBCAdj (overHom P.ρSheaf U)
  let g' : (sheafBC (overHom P.ρSheaf U)).obj (L.X p) ⟶ P.G0Sh U (P.fcMod U W hW) p :=
    (adj.homEquiv _ _).symm h
  have hg' : h = adj.unit.app (L.X p) ≫
      (SheafOfModules.restrictScalars.{0} (ringHomOf (overHom P.ρSheaf U))).map g' :=
    ((adj.homEquiv _ _).apply_symm_apply h).symm.trans
      (Adjunction.homEquiv_unit adj (L.X p) _ g')
  have hB : ∀ k : (L.X p).val.obj (topO U),
      (g'.val.app (topO U)).hom (P.bcη U L p (topO U) k) = (P.k0 U W hW L ε p).hom k :=
    fun k => (congrArg (fun f => ((gammaT (P.R.over U) (Over.mk (𝟙 U))).map f).hom k)
      hg').symm.trans (congrArg (fun f => f.hom k) hh)
  have hA : ∀ w : W.X p,
      ((gr0Ξn e p).val.app (topO U)).hom
        (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1
          (FCGen.tmul (P.ρ U) W 1 w)) = P.bcη U L p (topO U) ((ε.inv.f p).hom w) :=
    fun w => P.gr0ΞV_top_one U W hW L ε θ e he p w
  have hinv : ∀ l : (L.X p).val.obj (topO U),
      (ε.inv.f p).hom ((ε.hom.f p).hom l) = l := fun l =>
    congrArg (fun g => g.hom l) (congrArg (fun g => g.f p) ε.hom_inv_id)
  have F1 : g' ≫ gr0Ξn e p = 𝟙 _ := by
    apply (adj.homEquiv _ _).injective
    have e1 := Adjunction.homEquiv_naturality_right adj g' (gr0Ξn e p)
    have e2 : adj.homEquiv _ _ (𝟙 ((sheafBC (overHom P.ρSheaf U)).obj (L.X p))) =
        adj.unit.app (L.X p) :=
      (Adjunction.homEquiv_unit adj (L.X p) _ (𝟙 _)).trans
        ((congrArg (adj.unit.app (L.X p) ≫ ·)
          ((SheafOfModules.restrictScalars.{0} (ringHomOf (overHom P.ρSheaf U))).map_id _)).trans
          (Category.comp_id _))
    refine e1.trans ((congrArg (· ≫ _) ((adj.homEquiv _ _).apply_symm_apply h)).trans
      (Eq.trans ?_ e2.symm))
    refine (bijective_gammaT_map (R := P.R.over U) (Over.mkIdTerminal (X := U)) (hL.2 p)
      _).1 ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun l => ?_)
    have hk := congrArg (fun f => f.hom l) hh
    exact (congrArg (fun z => ((gr0Ξn e p).val.app (topO U)).hom z) hk).trans
      ((hA _).trans (congrArg (P.bcη U L p (topO U)) (hinv l)))
  have hinv' : ∀ w : W.X p, (ε.hom.f p).hom ((ε.inv.f p).hom w) = w := fun w =>
    congrArg (fun g => g.hom w) (congrArg (fun g => g.f p) ε.inv_hom_id)
  have E1 : ∀ w : W.X p,
      (g'.val.app (topO U)).hom (((gr0Ξn e p).val.app (topO U)).hom
        (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1
          (FCGen.tmul (P.ρ U) W 1 w))) =
      BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1
          (FCGen.tmul (P.ρ U) W 1 w) := fun w =>
    ((congrArg (g'.val.app (topO U)).hom (hA w)).trans (hB _)).trans
      (congrArg (fun z => BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1
        (FCGen.tmul (P.ρ U) W 1 z)) (hinv' w))
  have F2 : gr0Ξn e p ≫ g' = 𝟙 _ := by
    refine P.g0Sh_hom_ext U (P.fcMod U W hW) p _ _ fun q => ?_
    have key : ∀ q : FCGen (P.ρ U) W p,
        (g'.val.app (topO U)).hom (((gr0Ξn e p).val.app (topO U)).hom
          (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1 q)) =
        BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1 q := by
      intro q
      induction q using FCGen.induction_on with
      | ht α w =>
        let α' : ((ringOf P.A0).over U).obj.obj (topO U) :=
          (P.D.res (leOfHom (topO U).unop.hom)).f0 α
        have E0 := (congrArg
          (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1 ·)
            (FCGen.tmul_eq_smul α w)).trans (BCGen.tmul_smul0 α _)
        have s3 := (congrArg (g'.val.app (topO U)).hom
          (((gr0Ξn e p).val.app (topO U)).hom.map_smul α'
            (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) (P.fcMod U W hW).Q 1
              (FCGen.tmul (P.ρ U) W 1 w) :
                (P.G0Sh U (P.fcMod U W hW) p).val.obj (topO U)))).trans
          ((g'.val.app (topO U)).hom.map_smul α' _)
        rw [E1 w] at s3
        exact (congrArg (fun z => (g'.val.app (topO U)).hom (((gr0Ξn e p).val.app (topO U)).hom
          z)) E0).trans (s3.trans E0.symm)
      | hadd x y hx hy =>
        have ta := BCGen.tmul_add (f := P.D.res (leOfHom (topO U).unop.hom))
          (Q := (P.fcMod U W hW).Q) 1 x y
        exact (congrArg (fun z => (g'.val.app (topO U)).hom
          (((gr0Ξn e p).val.app (topO U)).hom z)) ta).trans
          (((congrArg (g'.val.app (topO U)).hom
            (((gr0Ξn e p).val.app (topO U)).hom.map_add _ _)).trans
            ((g'.val.app (topO U)).hom.map_add _ _)).trans ((congrArg₂ _ hx hy).trans ta.symm))
    exact key q
  exact ⟨⟨g', F2, F1⟩⟩

/-- **C2 via C7.** For `e` as in `exists_fcToN` and `L` strictly perfect, the `(0,0)`-component
`gr0Ξ e : G0(𝒜(U) ⊗ W) → 𝒜⁰ ⊗_R L` is an isomorphism: in each degree both sides are summands of
finite free `𝒜⁰|U`-modules (`Q^p = 𝒜⁰(U) ⊗ W^p` f.g. projective; `sheafBC` of a summand of a
finite free module), and `Γ(gr0Ξ e)` is `β ⊗ (α ⊗ w) ↦ βα·η(ε⁻¹ w)`, an isomorphism; S4.c on the
over-site (`bijective_gammaT_map`). -/
theorem isIso_gr0Ξ_fc [CompactSpace X] (hL : IsStrictlyPerfect L) (θ : P.Conn U (P.FK U L))
    (e : Z0 (P.fcMod U W hW).toQuasiCohesive (θ.N (topO U)))
    (he : ∀ (p : ℤ) (w : W.X p), e.1 (fcι (P.ρ U) W w) =
        P.ηTot U W L ε p w) :
    IsIso (gr0Ξ e) := by
  have : ∀ p, IsIso ((gr0Ξ e).f p) := fun p => P.isIso_gr0Ξn U W hW L ε hL θ e he p
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **C2 via C7.** `u ≫ Ξ_e = ιT`: both are maps out of the summands of finite free modules
`L^n`, so they are determined by `Γ` (`bijective_gammaT_map`); on `Γ`, `l ↦ Ξ_e(1 ⊗ 1 ⊗ ε l) =
res(e(1 ⊗ 1 ⊗ ε l)) = 1 ⊗ η l` (`bcLift_bcF`, `he`, `tRes_id`). -/
theorem comp_Ξ_eq_ιT [CompactSpace X] (hL : IsStrictlyPerfect L) (θ : P.Conn U (P.FK U L))
    (hθ : P.IsBCConn U L θ) (e : Z0 (P.fcMod U W hW).toQuasiCohesive (θ.N (topO U)))
    (he : ∀ (p : ℤ) (w : W.X p), e.1 (fcι (P.ρ U) W w) =
        P.ηTot U W L ε p w)
    (u : L ⟶ P.sheafOfOver U (P.fcMod U W hW))
    (hu : ((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u = ε.hom ≫ P.unitMap U W hW) :
    u ≫ Ξ e = ιT θ hθ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine (bijective_gammaT_map (R := P.R.over U) (Over.mkIdTerminal (X := U)) (hL.2 n)
    (P.TSh U (P.FK U L) n)).1 ?_
  have hn := congrArg (fun g => g.f n) hu
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun l => ?_
  apply Subtype.ext
  have h1 := congrArg (fun g => g.f n) ε.hom_inv_id
  have hinv : (ε.inv.f n).hom ((ε.hom.f n).hom l) = l :=
    congrArg (fun g => g.hom l) h1
  have hA : (((gammaT (P.R.over U) (Over.mk (𝟙 U))).map (u.f n)).hom l).1 =
      bcF (P.D.res (le_refl U)) (P.fcMod U W hW).Q (fcι (P.ρ U) W ((ε.hom.f n).hom l)) :=
    congrArg Subtype.val (congrArg (fun g => g.hom l) hn)
  change ΞV e (topO U) (((gammaT (P.R.over U) (Over.mk (𝟙 U))).map (u.f n)).hom l).1 =
    (ιTfun n (topO U) l).1
  rw [hA]
  refine (P.ΞV_bcF U e (topO U) (fcι (P.ρ U) W ((ε.hom.f n).hom l))).trans ?_
  rw [he]
  refine (P.tRes_id U (P.FK U L) (topO U) _).trans ?_
  unfold ηTot
  rw [hinv]
  rfl

end PreResolvingData

namespace ResolvingData

variable (D : ResolvingData X) (U : Opens X)
  (W : CochainComplex (ModuleCat.{0} (D.O.obj.obj (op U))) ℤ)
  (hW : IsBoundedFGProj (D.O.obj.obj (op U)) W)

/-- **C2 core (audit G1, G2).** [A, Lemma 7.2.17]; blueprint C2, "W̃ → 𝒜 ⊗_R W̃ is a
quasi-isomorphism". Let `L` be a strictly perfect complex of `O|U`-modules and `ε : Γ L ≅ W`
(global sections over `U`, i.e. evaluation at the terminal object of the over-site). If
`u : L → α_U(𝒜(U) ⊗ W)` has `Γ u = ε ⋙ (w ↦ 1 ⊗ 1 ⊗ w)`, then `u` is a quasi-isomorphism.
(Since each `L^n` is a summand of a finite free module, `u` is determined by `Γ u`, so `u` is
the map `W̃ → 𝒜|U ⊗_R W̃` of the blueprint.) Proof via C7 (blueprint C2, v1.11), see the module
doc. Deviations: stated for the lift `L` of `W` from S4.c rather than for `W̃` itself; (v1.11)
`X` compact Hausdorff. -/
theorem quasiIso_of_gamma_eq [CompactSpace X] [T2Space X]
    (L : CochainComplex (Mod (D.R.over U)) ℤ) (hL : IsStrictlyPerfect L)
    (ε : ((gammaT (D.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ≅ W)
    (u : L ⟶ D.sheafOfOver U (D.fcMod U W hW))
    (hu : ((gammaT (D.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u = ε.hom ≫ D.unitMap U W hW) : QuasiIso u := by
  obtain ⟨θ, hθ⟩ := D.exists_conn U L
  obtain ⟨e, he⟩ := D.exists_fcToN U W hW L ε θ hθ
  have h0 : IsIso (PreResolvingData.gr0Ξ e) := D.isIso_gr0Ξ_fc U W hW L ε hL θ e he
  have hΞ : QuasiIso (PreResolvingData.Ξ e) := PreResolvingData.quasiIso_Ξ e inferInstance
  have hι : QuasiIso (PreResolvingData.ιT θ hθ) :=
    D.quasiIso_ιT U L (isKFlat_of_isStrictlyPerfect (D.O.over U) hL) θ hθ
  have hcomp : QuasiIso (u ≫ PreResolvingData.Ξ e) := by
    rw [D.comp_Ξ_eq_ιT U W hW L ε hL θ hθ e he u hu]
    exact hι
  exact quasiIso_of_comp_right u (PreResolvingData.Ξ e)

end ResolvingData

end Cohesive
