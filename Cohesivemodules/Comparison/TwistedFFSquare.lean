import Cohesivemodules.Comparison.TwistedFFEv
import Cohesivemodules.Comparison.TwistedFFSec
import Cohesivemodules.Comparison.TwistedPsi

set_option linter.style.header false

/-!
# Z3.s: C4^tw step 3, the value of `ι` and the commuting square

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F′ (j); twisted copy of C4's `ι_app_res`
and `jK_Φ_evL`, `Comparison/FullyFaithfulPhi.lean`, `Comparison/FullyFaithfulSquare.lean`).
For `U′ ≤ U_α`, C2's `u : L → α_{U′}(𝒜(U′) ⊗ W)` and a closed degree-`0` map
`φ : 𝒜(U′) ⊗ W → gM₁|U′`:
* `ιtw := u ≫ α_{U′}(φ) ≫ (α_{U_α}(gM₁)|U′ ≅ α_{U′}(gM₁|U′))⁻¹ ≫ (twLocalIso|U′)⁻¹ :
  L → (J_T M₁)_α|U′`;
* `ιtw_app_res`: `ιtw` sends `(ε⁻¹ w)|Y` to `(twCmpInv(φ(1 ⊗ 1 ⊗ w)))|V`;
* `jKtw_Φtw_evLtw` (the square): `jK^tw ≫ Φ^tw_Y ≫ (sections ≅ cochains) ≫ evL^tw =
  alongPre φ ≫ alongEv`, `Φ^tw = Ψ^tw|U′ ≫ twHomRestrOverIso ≫ ιtw^*`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X] (P : PreResolvingData X) {h : P.D.A ⊤}
  (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (α : T.ι) {U' : Opens X} (hU' : U' ≤ T.U α)
  (W : CochainComplex (ModuleCat.{0} (P.O.obj.obj (op U'))) ℤ)
  (hW : IsBoundedFGProj (P.O.obj.obj (op U')) W)
  (L : CochainComplex (Mod ((ringOf P.toSheafData.O).over U')) ℤ)
  (ε : ((gammaT ((ringOf P.toSheafData.O).over U') (Over.mk (𝟙 U'))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L ≅ W)
  (u : L ⟶ P.sheafOfOver U' (P.fcMod U' W hW))
  (M₁ M₂ : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X)
  (φ : Z0 (P.fcMod U' W hW).toQuasiCohesive
    ((gaugedRes P T hh hd α M₁).baseChange (P.D.res hU')).toQuasiCohesive)

/-- **Z3.s.** `ι := u ≫ α_{U′}(φ) ≫ (restrOverSheafOfIso)⁻¹ ≫ (twLocalIso|U′)⁻¹ :
L ⟶ (J_T M₁)_α|U′`. -/
def ιtw : L ⟶ twK₂ P T hh hd α hU' M₁ :=
  u ≫ P.sheafOfOverMap U' φ ≫ (P.restrOverSheafOfIso hU' (gaugedRes P T hh hd α M₁)).inv ≫
    (restrOverC hU').map (twLocalIso P T hh hd α M₁).inv

/-- **Z3.s.** If `Γ_{U′}(u) = ε ≫ unitMap` (C2), then `ιtw` sends `(ε⁻¹ w)|Y` to
`(twCmpInv(φ(1 ⊗ 1 ⊗ w)))|V` (as C4's `ι_app_res`, with `twLocalIso` on top). -/
theorem ιtw_app_res
    (hu : ((gammaT ((ringOf P.toSheafData.O).over U') (Over.mk (𝟙 U'))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u = ε.hom ≫ P.unitMap U' W hW) (Y : Over U') (p : ℤ)
    (w : W.X p) :
    (show (P.toSheafData.withCurvature h hh hd).sheafOfSec M₁ p (le_top : Y.left ≤ ⊤) from
      (((ιtw P T hh hd α hU' W hW L u M₁ φ).f p).val.app (op Y)).hom
        (((L.X p).val.map ((Over.mkIdTerminal (X := U')).from Y).op).hom
          ((ε.inv.f p).hom w))).1 =
      (P.toSheafData.withCurvature h hh hd).totRes M₁ le_top (leOfHom Y.hom)
        (twCmpInv P T hh hd α M₁ hU' (φ.1 (fcι (P.ρ U') W w))) := by
  have hm : (ε.hom.f p).hom ((ε.inv.f p).hom w) = w :=
    congrArg (fun φ => (φ.f p).hom w) ε.inv_hom_id
  have hu' : ((u.f p).val.app (op (Over.mk (𝟙 U')))).hom ((ε.inv.f p).hom w) =
      P.unitElt U' W hW p w :=
    (congrArg (fun φ => (φ.f p).hom ((ε.inv.f p).hom w)) hu).trans
      (congrArg (fun x => (P.unitHom U' W hW p).hom x) hm)
  have hnat := PresheafOfModules.naturality_apply
    ((ιtw P T hh hd α hU' W hW L u M₁ φ).f p).val
    ((Over.mkIdTerminal (X := U')).from Y).op ((ε.inv.f p).hom w)
  have e0 := congrArg Subtype.val hu'
  have hz : ((((ιtw P T hh hd α hU' W hW L u M₁ φ).f p).val.app
      (op (Over.mk (𝟙 U')))).hom ((ε.inv.f p).hom w) :
        (P.toSheafData.withCurvature h hh hd).sheafOfSec M₁ p (le_top : U' ≤ ⊤)).1 =
      twCmpInv P T hh hd α M₁ hU' (φ.1 (fcι (P.ρ U') W w)) := by
    change twCmpInv P T hh hd α M₁ hU' (cmpTotInv (P.D.res hU') (P.D.res (le_refl U'))
      (P.D.res hU') _ (gaugedRes P T hh hd α M₁).toQuasiCohesive
      (bcHomL (P.D.res (le_refl U')) 0 (P.toHom0 φ)
        (((u.f p).val.app (op (Over.mk (𝟙 U')))).hom ((ε.inv.f p).hom w)).1)) = _
    have e1 : (P.unitElt U' W hW p w).1 =
        bcF (P.D.res (le_refl U')) (FCGen (P.ρ U') W) (fcι (P.ρ U') W w) := rfl
    have e2 : bcHomL (P.D.res (le_refl U')) 0 (P.toHom0 φ)
        (bcF (P.D.res (le_refl U')) (FCGen (P.ρ U') W) (fcι (P.ρ U') W w)) =
        bcF (P.D.res (le_refl U'))
          ((gaugedRes P T hh hd α M₁).baseChange (P.D.res hU')).toQuasiCohesive.Q
          (φ.1 (fcι (P.ρ U') W w)) :=
      bcHomL_bcF (P.D.res (le_refl U')) 0 (P.toHom0 φ) (fcι (P.ρ U') W w)
    rw [e0, e1]
    refine congrArg (twCmpInv P T hh hd α M₁ hU') ?_
    refine (congrArg (fun y => cmpTotInv (P.D.res hU') (P.D.res (le_refl U')) (P.D.res hU') _
      (gaugedRes P T hh hd α M₁).toQuasiCohesive y) e2).trans ?_
    refine (cmpTotInv_bcF (P.D.res hU') (P.D.res (le_refl U')) (P.D.res hU') _
      (gaugedRes P T hh hd α M₁).toQuasiCohesive _).trans ?_
    exact P.totRes_id (gaugedRes P T hh hd α M₁) _ _
  refine Eq.trans (congrArg Subtype.val hnat) ?_
  change (P.toSheafData.withCurvature h hh hd).totRes M₁ (le_top : U' ≤ ⊤) (leOfHom Y.hom) _ = _
  rw [hz]

/-- **Z3.s (C4^tw step 3, the square).** For `Y : Over U′` (`V = Y.left`):
`jK^tw ≫ Φ^tw_Y ≫ (sections of 𝓗om ≅ Cochain) ≫ evL^tw = alongPre φ ≫ alongEv`, with
`Φ^tw = Ψ^tw|U′ ≫ twHomRestrOverIso ≫ ιtw^*`. Elementwise both sides send `χ'` to
`w ↦ χ'(φ(1 ⊗ 1 ⊗ w))` (`twHomRestrOver_map₁_sections`, `ιtw_app_res`, `extAlong_jKtw`). -/
theorem jKtw_Φtw_evLtw
    (hu : ((gammaT ((ringOf P.toSheafData.O).over U') (Over.mk (𝟙 U'))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u = ε.hom ≫ P.unitMap U' W hW) (Y : Over U') :
    jKtw P T hh hd α hU' M₁ M₂ Y ≫
      (secAb ((ringOf P.toSheafData.O).over U') (op Y)).map
        (((restr (ringOf P.toSheafData.O) U').mapHomologicalComplex (ComplexShape.up ℤ)).map
          (T.Ψtw hh hd M₁ M₂) ≫
        (twHomRestrOverIso T.ch_aba T.iSup_eq α hU' (T.twistedSheafOf hh hd M₁)
          (T.twistedSheafOf hh hd M₂)).hom ≫
        homComplexMap₁ (isCommSheaf_over U') (ιtw P T hh hd α hU' W hW L u M₁ φ)
          (twK₂ P T hh hd α hU' M₂)) ≫
      (homSectionsIso (isCommSheaf_over U') L (twK₂ P T hh hd α hU' M₂) Y).hom ≫
      evLtw P T hh hd α hU' W L ε M₂ Y =
    alongPre (P.D.res (leOfHom Y.hom)) (twNY P T hh hd α hU' M₂ Y) φ ≫
      alongEv (P.D.res (leOfHom Y.hom)) W (P.d_ρ U') (P.c_eq_zero U') (P.c_eq_zero Y.left)
        (twNY P T hh hd α hU' M₂ Y) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro χ'
  apply Subtype.ext
  funext p
  apply LinearMap.ext
  intro w
  refine Eq.trans (evLtwf_apply P T hh hd α hU' W L ε M₂ Y n _ p w) ?_
  change _ = χ'.1 (φ.1 (fcι (P.ρ U') W w))
  have hsec := twHomRestrOver_map₁_sections T.ch_aba T.iSup_eq α hU'
    (T.twistedSheafOf hh hd M₁) (T.twistedSheafOf hh hd M₂)
    (ιtw P T hh hd α hU' W hW L u M₁ φ) n Y
    (((T.Ψtw hh hd M₁ M₂).f n).val.app (op Y.left) ((jKtwf P T hh hd α hU' M₁ M₂ Y n).hom χ'))
    ⟨p, p + n, rfl⟩ (((L.X p).val.map ((Over.mkIdTerminal (X := U')).from Y).op).hom
      ((ε.inv.f p).hom w))
  have hπ := congrArg (fun g => (g.val.app (op Y.left)).hom
      ((jKtwf P T hh hd α hU' M₁ M₂ Y n).hom χ'))
    (Limits.Pi.lift_comp_π (fun T' : Triplet n ↦ T.ΨtwT hh hd M₁ M₂ n T') ⟨p, p + n, rfl⟩)
  refine (congrArg (fun z : (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + n)
    (le_top : Y.left ≤ ⊤) => twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU') z.1) hsec).trans ?_
  simp only at hπ
  erw [hπ]
  change twCmp P T hh hd α M₂ _ (extAlong ((P.toSheafData.withCurvature h hh hd).homAt M₁ M₂ n _
    ((jKtwf P T hh hd α hU' M₁ M₂ Y n).hom χ'))
    (show (P.toSheafData.withCurvature h hh hd).sheafOfSec M₁ p (le_top : Y.left ≤ ⊤) from
      (((ιtw P T hh hd α hU' W hW L u M₁ φ).f p).val.app (op Y)).hom
        (((L.X p).val.map ((Over.mkIdTerminal (X := U')).from Y).op).hom
          ((ε.inv.f p).hom w))).1) = _
  rw [ιtw_app_res P T hh hd α hU' W hW L ε u M₁ φ hu Y p w, twCmpInv_totRes]
  exact (congrArg (twCmp P T hh hd α M₂ _)
    (extAlong_jKtw P T hh hd α hU' M₁ M₂ Y n χ' _ _)).trans (twCmp_twCmpInv P T hh hd α M₂ _ _)

end Cohesive
