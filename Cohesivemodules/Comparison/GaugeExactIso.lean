import Cohesivemodules.Comparison.GaugeSheaf
import Cohesivemodules.Comparison.TwistDatumBasic
import Cohesivemodules.Sheaf.Twisted.GlueEquiv

set_option linter.style.header false

/-!
# K14: `J_{T_β} ≅ gauge_β ⋙ J ⋙ ofSheaf` for an exact curvature

Blueprint check K14 (`blueprint/blueprint-tw.md` §5), auxiliary. For pre-resolving data `P`, a
closed `h = dβ` (`β ∈ 𝒜¹(X)`, `hcβ`) and the twist datum `exactTwistDatum β` (cover `{⊤}`,
`h⁰ = β`, `u = 1`, `ȟ = 1`):
* `gaugeExactCompSh`: `α(M)^n|⊤ ≅ α(gauge_β M)^n|⊤` on `Over ⊤` (sectionwise `gaugeSec`);
* `gaugeExactTermHom`, `gaugeExactTermIso`: `J_{T_β}(M)^n ≅ ofSheaf(α(gauge_β M)^n)` as twisted
  sheaves (both gluing maps are the identity), compatible with the differentials
  (`gaugeExactTermHom_diff`: `𝕏 − β` vs `𝕏` of the gauge) and natural in closed degree-`0` maps
  (`gaugeExactTermHom_map`);
* `gaugeExactCpx`, `gaugeExactCpx_map`: the complex iso `J_{T_β}(M) ≅ ofSheaf(α(gauge_β M))`;
* `gaugeExactNatIso`: the natural iso `J_{T_β} ≅ gauge_β ⋙ J ⋙ ofSheaf` of functors
  `Ho(P_{(𝒜(X), h)}) ⥤ K(TwMod O {⊤} 1)`.
Specialized to the Dolbeault data in `ChecksTwistedK8.lean` (`nonempty_twistedJK_exact_iso`).

## Lean notes
Stated over abstract `S`/`P`: over the concrete Dolbeault data the same statements time out in
`isDefEq` (even at 1M heartbeats). Prover-written (5 Nov 2026), moved here from
`ChecksTwistedK8.lean` (file length).
-/

noncomputable section

namespace Cohesive

open CategoryTheory

/-- K14: the components `α(M)^n|⊤ ≅ α(gauge_β M)^n|⊤` as sheaves on `Over ⊤` (`gaugeSec` on
sections over every `W`; `O`-linear by `gaugeTot_smul`, natural by `gaugeSec_res`). -/
def gaugeExactCompSh {Y : Type} [TopologicalSpace Y] {S : DgaSheafData Y} {h : S.D.A ⊤}
    (hh : h ∈ S.D.𝒜 ⊤ 2)
    (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) (β : S.D.A ⊤) (hβ : β ∈ S.D.𝒜 ⊤ 1)
    (hcβ : S.D.res le_top h = (S.D.dga ⊤).c + (S.D.dga ⊤).d β)
    (M : CohesiveModule (S.withCurvature h hh hd).𝒜X) (n : ℤ) :
    (restr (ringOf S.O) (⊤ : TopologicalSpace.Opens Y)).obj
        ((S.withCurvature h hh hd).sheafOfSh M n) ≅
      (restr (ringOf S.O) (⊤ : TopologicalSpace.Opens Y)).obj
        (S.sheafOfSh (gaugeM S hh hd β hβ hcβ M) n) where
  hom := homOfSec₀ (fun {W} hW => (gaugeSec S hh hd β hβ hcβ M le_top n).toAddMonoidHom)
    (by
      intro W hW r x
      refine Subtype.ext ?_
      exact gaugeTot_smul S hh hd β hβ hcβ M (le_top : W ≤ ⊤) (S.ρ W r : S.D.A W) x.1)
    (by
      intro W W' hW h' x
      exact gaugeSec_res S hh hd β hβ hcβ M (le_top : W ≤ ⊤) n h' x)
  inv := homOfSec₀ (fun {W} hW => (gaugeSec S hh hd β hβ hcβ M le_top n).symm.toAddMonoidHom)
    (by
      intro W hW r y
      have hf : ∀ z : (S.withCurvature h hh hd).sheafOfSec M n (le_top : W ≤ ⊤),
          gaugeSec S hh hd β hβ hcβ M le_top n
              ((show (S.withCurvature h hh hd).O.obj.obj (Opposite.op W) from r) • z) =
            r • gaugeSec S hh hd β hβ hcβ M le_top n z := fun z =>
        Subtype.ext (gaugeTot_smul S hh hd β hβ hcβ M (le_top : W ≤ ⊤)
          (S.ρ W r : S.D.A W) z.1)
      refine ((gaugeSec S hh hd β hβ hcβ M le_top n).symm_apply_eq).2 ?_
      refine Eq.trans ?_ (hf _).symm
      exact congrArg _ ((gaugeSec S hh hd β hβ hcβ M le_top n).apply_symm_apply y).symm)
    (by
      intro W W' hW h' y
      refine (Equiv.symm_apply_eq
        (gaugeSec S hh hd β hβ hcβ M (h'.trans le_top) n).toEquiv).2 ?_
      refine Eq.trans ?_ (gaugeSec_res S hh hd β hβ hcβ M (le_top : W ≤ ⊤) n h' _).symm
      exact congrArg _ ((gaugeSec S hh hd β hβ hcβ M le_top n).apply_symm_apply y).symm)
  hom_inv_id := by
    ext Y x
    exact (gaugeSec S hh hd β hβ hcβ M le_top n).symm_apply_apply x
  inv_hom_id := by
    ext Y y
    exact (gaugeSec S hh hd β hβ hcβ M le_top n).apply_symm_apply y

/-- K14: `J_{T_β}(M)^n ⟶ ofSheaf(α(gauge_β M)^n)`, the component iso `gaugeExactCompSh` (the
gluing maps on both sides are the identity), for abstract sheaf data. -/
def gaugeExactTermHom {Y : Type} [TopologicalSpace Y] {S : DgaSheafData Y} {h : S.D.A ⊤}
    (hh : h ∈ S.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) (β : S.D.A ⊤)
    (hβ : β ∈ S.D.𝒜 ⊤ 1) (hcβ : S.D.res le_top h = (S.D.dga ⊤).c + (S.D.dga ⊤).d β)
    (M : CohesiveModule (S.withCurvature h hh hd).𝒜X) (hh' : GCDga.d (𝒜 := S.D.𝒜 ⊤) β = h)
    (n : ℤ) :
    (exactTwistDatum S β hβ h hh').twTerm hh hd M n ⟶
      TwMod.ofSheaf S.O (exactTwistDatum S β hβ h hh').U
        (S.sheafOfSh (gaugeM S hh hd β hβ hcβ M) n) where
  f _ := (gaugeExactCompSh hh hd β hβ hcβ M n).hom
  comm := by
    intro α γ W hα hγ x
    have h1 : (S.D.res (le_inf hα hγ)).f0 ((exactTwistDatum S β hβ h hh').u α γ) = 1 :=
      map_one _
    have h2 := (S.withCurvature h hh hd).smul0L_one M n (le_top : W ≤ ⊤) x
    exact (congrArg (((gaugeExactCompSh hh hd β hβ hcβ M n).hom).val.app (ovr hγ)).hom
      ((congrArg (fun u => (S.withCurvature h hh hd).smul0L M n (le_top : W ≤ ⊤) u x) h1).trans
        h2)).symm

/-- K14: `gaugeExactTermHom` is an isomorphism of twisted sheaves (componentwise iso). -/
def gaugeExactTermIso {Y : Type} [TopologicalSpace Y] {S : DgaSheafData Y} {h : S.D.A ⊤}
    (hh : h ∈ S.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) (β : S.D.A ⊤)
    (hβ : β ∈ S.D.𝒜 ⊤ 1) (hcβ : S.D.res le_top h = (S.D.dga ⊤).c + (S.D.dga ⊤).d β)
    (M : CohesiveModule (S.withCurvature h hh hd).𝒜X) (hh' : GCDga.d (𝒜 := S.D.𝒜 ⊤) β = h)
    (n : ℤ) :
    (exactTwistDatum S β hβ h hh').twTerm hh hd M n ≅
      TwMod.ofSheaf S.O (exactTwistDatum S β hβ h hh').U
        (S.sheafOfSh (gaugeM S hh hd β hβ hcβ M) n) :=
  haveI : ∀ α, IsIso ((gaugeExactTermHom hh hd β hβ hcβ M hh' n).f α) := fun _ =>
    inferInstanceAs (IsIso (gaugeExactCompSh hh hd β hβ hcβ M n).hom)
  haveI := TwMod.isIso_of_isIso_f (gaugeExactTermHom hh hd β hβ hcβ M hh' n)
  asIso (gaugeExactTermHom hh hd β hβ hcβ M hh' n)

/-- K14: `gaugeExactTermHom` intertwines `𝕏 − β` with `𝕏` of the gauge (`gaugeSec_gaugeDV`). -/
theorem gaugeExactTermHom_diff {Y : Type} [TopologicalSpace Y] {S : DgaSheafData Y}
    {h : S.D.A ⊤} (hh : h ∈ S.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) (β : S.D.A ⊤)
    (hβ : β ∈ S.D.𝒜 ⊤ 1) (hcβ : S.D.res le_top h = (S.D.dga ⊤).c + (S.D.dga ⊤).d β)
    (M : CohesiveModule (S.withCurvature h hh hd).𝒜X) (hh' : GCDga.d (𝒜 := S.D.𝒜 ⊤) β = h)
    (n : ℤ) :
    (exactTwistDatum S β hβ h hh').twDiff hh hd M n ≫
        gaugeExactTermHom hh hd β hβ hcβ M hh' (n + 1) =
      gaugeExactTermHom hh hd β hβ hcβ M hh' n ≫
        TwMod.ofSheafMap (U := (exactTwistDatum S β hβ h hh').U)
          (S.sheafOfX (gaugeM S hh hd β hβ hcβ M) n) := by
  refine TwMod.hom_ext fun α => ?_
  change (exactTwistDatum S β hβ h hh').twDiffComp hh hd M n α ≫
      (gaugeExactCompSh hh hd β hβ hcβ M (n + 1)).hom =
    (gaugeExactCompSh hh hd β hβ hcβ M n).hom ≫ (restr (ringOf S.O) ⊤).map
      (S.sheafOfX (gaugeM S hh hd β hβ hcβ M) n)
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  exact gaugeSec_gaugeDV S hh hd β hβ hcβ M (leOfHom V.unop.hom) n x

/-- K14: `gaugeExactTermHom` is natural in closed degree-`0` maps (`gaugeSec_sheafOfMapV`). -/
theorem gaugeExactTermHom_map {Y : Type} [TopologicalSpace Y] {S : DgaSheafData Y}
    {h : S.D.A ⊤} (hh : h ∈ S.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) (β : S.D.A ⊤)
    (hβ : β ∈ S.D.𝒜 ⊤ 1) (hcβ : S.D.res le_top h = (S.D.dga ⊤).c + (S.D.dga ⊤).d β)
    (M N : CohesiveModule (S.withCurvature h hh hd).𝒜X) (hh' : GCDga.d (𝒜 := S.D.𝒜 ⊤) β = h)
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) :
    (exactTwistDatum S β hβ h hh').twMapN hh hd φ n ≫ gaugeExactTermHom hh hd β hβ hcβ N hh' n =
      gaugeExactTermHom hh hd β hβ hcβ M hh' n ≫
        TwMod.ofSheafMap (U := (exactTwistDatum S β hβ h hh').U)
          (S.sheafOfMapN (gaugeZ0 S hh hd β hβ hcβ M φ) n) := by
  refine TwMod.hom_ext fun α => ?_
  change (restr (ringOf S.O) ⊤).map ((S.withCurvature h hh hd).sheafOfMapN φ n) ≫
      (gaugeExactCompSh hh hd β hβ hcβ N n).hom =
    (gaugeExactCompSh hh hd β hβ hcβ M n).hom ≫ (restr (ringOf S.O) ⊤).map
      (S.sheafOfMapN (gaugeZ0 S hh hd β hβ hcβ M φ) n)
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  exact gaugeSec_sheafOfMapV S hh hd β hβ hcβ M (leOfHom V.unop.hom) φ n x

/-- `TwMod.ofSheafFunctor` is additive. -/
instance TwMod.ofSheafFunctor_additive {Y : Type} [TopologicalSpace Y]
    {R : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{0}} {ι : Type}
    (U : ι → TopologicalSpace.Opens Y) : (TwMod.ofSheafFunctor R U).Additive :=
  ⟨fun {_ _ _ _} => TwMod.hom_ext fun α => Functor.map_add (restr (ringOf R) (U α))⟩

/-- K14: the complex iso `J_{T_β}(M) ≅ ofSheaf(α(gauge_β M))`, termwise `gaugeExactTermIso`, for an
abstract `PreResolvingData`. -/
def gaugeExactCpx {Y : Type} [TopologicalSpace Y] {P : PreResolvingData Y}
    {h : P.toSheafData.D.A ⊤} (hh : h ∈ P.toSheafData.D.𝒜 ⊤ 2)
    (hd : GCDga.d (𝒜 := P.toSheafData.D.𝒜 ⊤) h = 0) (β : P.toSheafData.D.A ⊤)
    (hβ : β ∈ P.toSheafData.D.𝒜 ⊤ 1)
    (hcβ : P.toSheafData.D.res le_top h =
      (P.toSheafData.D.dga ⊤).c + (P.toSheafData.D.dga ⊤).d β)
    (M : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X)
    (hh' : GCDga.d (𝒜 := P.toSheafData.D.𝒜 ⊤) β = h) :
    (exactTwistDatum P.toSheafData β hβ h hh').twistedSheafOf hh hd M ≅
      ((TwMod.ofSheafFunctor P.toSheafData.O (exactTwistDatum P.toSheafData β hβ h hh').U
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P.sheafOf (gaugeM P.toSheafData hh hd β hβ hcβ M)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => gaugeExactTermIso hh hd β hβ hcβ M hh' n) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have e1 : (P.sheafOf (gaugeM P.toSheafData hh hd β hβ hcβ M)).d i (i + 1) =
        P.sheafOfD (gaugeM P.toSheafData hh hd β hβ hcβ M) i := CochainComplex.of_d _ _ _
    have e2 : ((exactTwistDatum P.toSheafData β hβ h hh').twistedSheafOf hh hd M).d i (i + 1) =
        (exactTwistDatum P.toSheafData β hβ h hh').twDiff hh hd M i := CochainComplex.of_d _ _ _
    change _ ≫ (TwMod.ofSheafFunctor P.toSheafData.O _).map
      ((P.sheafOf (gaugeM P.toSheafData hh hd β hβ hcβ M)).d i (i + 1)) = _
    rw [e1, e2]
    exact (gaugeExactTermHom_diff hh hd β hβ hcβ M hh' i).symm)

/-- K14: `gaugeExactCpx` is natural in closed degree-`0` maps. -/
theorem gaugeExactCpx_map {Y : Type} [TopologicalSpace Y] {P : PreResolvingData Y}
    {h : P.toSheafData.D.A ⊤} (hh : h ∈ P.toSheafData.D.𝒜 ⊤ 2)
    (hd : GCDga.d (𝒜 := P.toSheafData.D.𝒜 ⊤) h = 0) (β : P.toSheafData.D.A ⊤)
    (hβ : β ∈ P.toSheafData.D.𝒜 ⊤ 1)
    (hcβ : P.toSheafData.D.res le_top h =
      (P.toSheafData.D.dga ⊤).c + (P.toSheafData.D.dga ⊤).d β)
    (M N : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X)
    (hh' : GCDga.d (𝒜 := P.toSheafData.D.𝒜 ⊤) β = h)
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) :
    (exactTwistDatum P.toSheafData β hβ h hh').twMap hh hd φ ≫
        (gaugeExactCpx hh hd β hβ hcβ N hh').hom =
      (gaugeExactCpx hh hd β hβ hcβ M hh').hom ≫
        ((TwMod.ofSheafFunctor P.toSheafData.O (exactTwistDatum P.toSheafData β hβ h hh').U
          ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (P.sheafOfMap (gaugeZ0 P.toSheafData hh hd β hβ hcβ M φ)) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact gaugeExactTermHom_map hh hd β hβ hcβ M N hh' φ n

/-- K14: `J_{T_β} ≅ gauge_β ⋙ J ⋙ ofSheaf` on homotopy categories, for an abstract
`PreResolvingData` (objectwise `gaugeExactCpx`, naturality `gaugeExactCpx_map`). -/
def gaugeExactNatIso {Y : Type} [TopologicalSpace Y] {P : PreResolvingData Y}
    {h : P.toSheafData.D.A ⊤} (hh : h ∈ P.toSheafData.D.𝒜 ⊤ 2)
    (hd : GCDga.d (𝒜 := P.toSheafData.D.𝒜 ⊤) h = 0) (β : P.toSheafData.D.A ⊤)
    (hβ : β ∈ P.toSheafData.D.𝒜 ⊤ 1)
    (hcβ : P.toSheafData.D.res le_top h =
      (P.toSheafData.D.dga ⊤).c + (P.toSheafData.D.dga ⊤).d β)
    (hh' : GCDga.d (𝒜 := P.toSheafData.D.𝒜 ⊤) β = h) :
    (exactTwistDatum P.toSheafData β hβ h hh').twistedJK hh hd ≅
      gaugeFunctor (i := P.toSheafData.D.dga ⊤) (c' := P.toSheafData.D.res le_top h)
        (hc := (P.toSheafData.D.res le_top).map_mem hh)
        (hd := (P.toSheafData.D.curvedInst h hh hd ⊤).d_c) β hβ hcβ (isUnit_of_invertible 2) ⋙
      P.JK ⋙ (TwMod.ofSheafFunctor P.toSheafData.O
        (exactTwistDatum P.toSheafData β hβ h hh').U).mapHomotopyCategory (ComplexShape.up ℤ) :=
  NatIso.ofComponents
    (fun M => (HomotopyCategory.quotient _ _).mapIso (gaugeExactCpx hh hd β hβ hcβ M.as hh')) (by
    intro M N f
    induction f using Submodule.Quotient.induction_on with
    | H φ =>
    have key := congrArg (HomotopyCategory.quotient _ _).map
      (gaugeExactCpx_map hh hd β hβ hcβ M.as N.as hh' φ)
    exact ((Functor.map_comp _ _ _).symm.trans key).trans (Functor.map_comp _ _ _))

end Cohesive
