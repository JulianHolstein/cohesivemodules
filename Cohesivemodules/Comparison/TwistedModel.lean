import Cohesivemodules.Comparison.TwistedUntwist
import Cohesivemodules.Comparison.ModelTensor
import Cohesivemodules.Sheaf.Twisted.Perfect

set_option linter.style.header false

/-!
# Z3.t: the twisted model `T^tw(K')` (blueprint-tw G′ (e), (f))

Blueprint item Z3.t (`blueprint/blueprint-tw.md` §3 G′ (e), (f); G.9). For pre-resolving data `P`
(`X` compact), a twist datum `T` and a complex `K'` of `ȟ`-twisted `O`-modules, with the C7.b
connections `θ_α` on `F_α = 𝒜⁰|U_α ⊗ K'_α` (`IsBCConn`):
* `twGenφ`: the gluing of `𝒜⁰ ⊗ K'^p` (Z3.l′ `twBC`) on sections, the generators of the model;
* `twTotφ`, `twModelφ`: the gluing of the model, `a ⊗ s ↦ a ⊗ φ^B_αβ(s)` on `Tot(𝒜(W), F_α(W))`
  (`totMapAlong` along the identity of `𝒜(W)`), in each total degree;
* `twModelObj n`: the `ȟ`-twisted `O`-module with components `T_α^n = (θ_α.TC)^n` (C7);
* `twModel`: the complex `T^tw` with differentials `θ_α.TD` (chain maps: `twModel_TD_comm`, by
  C.7′ (b): `θ_β φ^B − φ^B θ_α` is `𝒜⁰`-linear and vanishes on `η k`);
* `ιTtw : K' ⟶ T^tw`, components C7.d's `ιT`; a quasi-isomorphism when every `K'_α` is K-flat.

## Deviations
* None beyond those of C7 (the model replaces the sheafified tensor product) and of `TwMod`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] [CompactSpace X] (P : PreResolvingData X)
  {h : P.D.A ⊤} (T : TwistDatum P.toSheafData h)
  (K' : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ)

/-- Z3.t: the component complex `K'_α` on `Over U_α`, spelled over `P.R` (as C7 expects). -/
abbrev twKα (α : T.ι) : CochainComplex (Mod (P.R.over (T.U α))) ℤ :=
  ((TwMod.comp P.toSheafData.O T.U T.ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K'

/-- Z3.t: `F_α = 𝒜⁰|U_α ⊗ K'_α` (C7.b `FK`). -/
abbrev twFα (α : T.ι) : CochainComplex (Mod ((ringOf P.A0).over (T.U α))) ℤ :=
  P.FK (T.U α) (twKα P T K' α)

/-- Z3.t: the term `T_α^n` of the C7 model of `F_α`, spelled over the twisted ring. -/
abbrev twTSh (n : ℤ) (α : T.ι) : Mod ((ringOf P.toSheafData.O).over (T.U α)) :=
  P.TSh (T.U α) (twFα P T K' α) n

/-- Z3.t: C7's `Module 𝒜⁰(V)` instance on generator sections, as a term (for `fSecModuleOvr`). -/
abbrev fSecModule {U : Opens X} (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (p : ℤ)
    (V : (Over U)ᵒᵖ) : Module ↥(P.D.𝒜 V.unop.left 0) (P.FSec U F p V) :=
  inferInstance

/-- Z3.t: C7's `Module 𝒜⁰(W)` instance on generator sections at `ovr h` (instance search does
not find the generic one there, P25; definitionally the same instance, no diamond). -/
instance fSecModuleOvr {U W : Opens X} (hW : W ≤ U)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (p : ℤ) :
    Module ↥(P.D.𝒜 (ovr hW).unop.left 0) (P.FSec U F p (ovr hW)) :=
  fSecModule P F p (ovr hW)

/-- Z3.t: the identity of `𝒜(W)`, typed between the algebras at `ovr hα` and `ovr hβ`. -/
abbrev idAt {α β : T.ι} {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) :
    DgaHom (P.D.𝒜 (ovr hα).unop.left) (P.D.𝒜 (ovr hβ).unop.left) :=
  DgaHom.id (P.D.𝒜 W)

/-- Z3.t: the `𝒜⁰(V)`-module structure on `tDeg`, typed over the ring of sections of `𝒜⁰|U`
(definitionally the same, P9). -/
private instance PreResolvingData.tDegModule (U : Opens X)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (n : ℤ) (V : (Over U)ᵒᵖ) :
    Module (((ringOf P.A0).over U).obj.obj V) ↥(P.tDeg U F n V) :=
  inferInstanceAs (Module ↥(P.D.𝒜 V.unop.left 0) ↥(P.tDeg U F n V))

/-- Z3.t: restriction of `T^n` as a semilinear map over `𝒜⁰` (helper for the uniqueness
argument of `twModel_TD_comm`). -/
private def PreResolvingData.tResA (U : Opens X) (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    (n : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    ↥(P.tDeg U F n V) →ₛₗ[(((ringOf P.A0).over U).obj.map f).hom] ↥(P.tDeg U F n W) where
  toFun x := ⟨P.tRes U F f x.1, P.tRes_mem U F f x.2⟩
  map_add' x y := Subtype.ext (map_add (P.tRes U F f) x.1 y.1)
  map_smul' r x :=
    Subtype.ext (P.tRes_smul U F f (show ↥(P.D.𝒜 V.unop.left 0) from r).1 x.1)

/-- Z3.t: `T^n` as a presheaf of `𝒜⁰|U`-modules (same underlying presheaf of groups as `TPre`). -/
private def PreResolvingData.tPreA (U : Opens X) (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    (n : ℤ) : PresheafOfModules.{0} ((ringOf P.A0).over U).obj where
  obj V := ModuleCat.of (P.D.𝒜 V.unop.left 0) ↥(P.tDeg U F n V)
  map {V W} f := ModuleCat.semilinearMapAddEquiv (((ringOf P.A0).over U).obj.map f).hom
      (ModuleCat.of (P.D.𝒜 V.unop.left 0) ↥(P.tDeg U F n V))
      (ModuleCat.of (P.D.𝒜 W.unop.left 0) ↥(P.tDeg U F n W))
      (P.tResA U F n f)
  map_id V := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact P.tRes_id U F V x.1
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact P.tRes_comp U F f g x.1

/-- Z3.t: `T^n` as a sheaf of `𝒜⁰|U`-modules. -/
private def PreResolvingData.tShA (U : Opens X) (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    (n : ℤ) : Mod ((ringOf P.A0).over U) :=
  ⟨P.tPreA U F n, P.isSheaf_TPre U F n⟩

/-- **Z3.t (G′ (f)).** The gluing of `𝒜⁰ ⊗ K'^p` on sections over `W ≤ U_α ∩ U_β` (the gluing maps
of `twBC ρ (K'^p)`, Z3.l′), between the generators `F_α^p(W)` and `F_β^p(W)` of the model. -/
def twGenφ (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) (p : ℤ) :
    P.FSec (T.U α) (twFα P T K' α) p (ovr hα) →+ P.FSec (T.U β) (twFα P T K' β) p (ovr hβ) :=
  ((K'.X p).bcObj P.ρSheafT).φ α β hα hβ

/-- Z3.t: `twGenφ` is `𝒜⁰(W)`-linear. -/
theorem twGenφ_smul (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) (p : ℤ)
    (r : ↥(P.D.𝒜 (ovr hα).unop.left 0)) (x : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    twGenφ P T K' α β hα hβ p (r • x) =
      (idAt P T hα hβ).f0 r • twGenφ P T K' α β hα hβ p x :=
  ((K'.X p).bcObj P.ρSheafT).φ_smul α β hα hβ r x

/-- **Z3.t (G′ (f)).** The gluing of the model on total modules over `W ≤ U_α ∩ U_β`:
`a ⊗ s ↦ a ⊗ φ^B_αβ(s)` (`totMapAlong` along the identity of `𝒜(W)`). -/
def twTotφ (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) :
    P.TTot (T.U α) (twFα P T K' α) (ovr hα) →+ P.TTot (T.U β) (twFα P T K' β) (ovr hβ) :=
  totMapAlong (idAt P T hα hβ) (twGenφ P T K' α β hα hβ) (twGenφ_smul P T K' α β hα hβ)

/-- Z3.t: `twTotφ` preserves the total degree. -/
theorem twTotφ_mem (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) (n : ℤ)
    {x : P.TTot (T.U α) (twFα P T K' α) (ovr hα)}
    (hx : x ∈ P.tDeg (T.U α) (twFα P T K' α) n (ovr hα)) :
    twTotφ P T K' α β hα hβ x ∈ P.tDeg (T.U β) (twFα P T K' β) n (ovr hβ) :=
  totMapAlong_mem_totDeg _ _ _ hx

/-- **Z3.t (G′ (f)).** The gluing of the model in total degree `n`, on sections over
`W ≤ U_α ∩ U_β` of `T_α^n` and `T_β^n`. -/
def twModelφ (n : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) :
    sec P.toSheafData.O (twTSh P T K' n α) hα →+ sec P.toSheafData.O (twTSh P T K' n β) hβ where
  toFun x := ⟨twTotφ P T K' α β hα hβ x.1, twTotφ_mem P T K' α β hα hβ n x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)

/-- Z3.t: `twModelφ` is `O(W)`-linear. -/
theorem twModelφ_smul (n : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (r : P.toSheafData.O.obj.obj (op W)) (x : sec P.toSheafData.O (twTSh P T K' n α) hα) :
    twModelφ P T K' n α β hα hβ (toSec P.toSheafData.O hα r • x) =
      toSec P.toSheafData.O hβ r • twModelφ P T K' n α β hα hβ x := by
  apply Subtype.ext
  exact totMapAlong_smul (idAt P T hα hβ) (twGenφ P T K' α β hα hβ)
    (twGenφ_smul P T K' α β hα hβ) (P.ρ W r : P.D.A W) x.1

/-- Z3.t: `twTotφ` commutes with `tRes` along `W' ≤ W` (as morphisms of the over-site). -/
private theorem twTotφ_tRes (α β : T.ι) {W W' : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (h' : W' ≤ W) (y : P.TTot (T.U α) (twFα P T K' α) (ovr hα)) :
    twTotφ P T K' α β (h'.trans hα) (h'.trans hβ)
        (P.tRes (T.U α) (twFα P T K' α)
          (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hα)) ⟶
            Over.mk (homOfLE hα)).op y) =
      P.tRes (T.U β) (twFα P T K' β)
        (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hβ)) ⟶
            Over.mk (homOfLE hβ)).op (twTotφ P T K' α β hα hβ y) := by
  induction y using Tot.induction_on with
  | ht a e =>
    simp only [PreResolvingData.tRes_apply, twTotφ, totMapAlong_tmul]
    refine congrArg (Tot.tmul _ _ _) ?_
    induction e using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of p x =>
      simp only [famMap_of]
      exact congrArg (DirectSum.of _ p) (((K'.X p).bcObj P.ρSheafT).φ_res α β hα hβ h' x)
    | add x y hx hy => simp only [map_add, hx, hy]
  | hadd x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- Z3.t: the cocycle on `twTotφ`, from the cocycle `hc` on the generators with scalar `c`. -/
private theorem twTotφ_cocycle_aux (α β γ : T.ι) {W : Opens X} (hα : W ≤ T.U α)
    (hβ : W ≤ T.U β) (hγ : W ≤ T.U γ) (c : ↥(P.D.𝒜 (ovr hγ).unop.left 0))
    (hc : ∀ (p : ℤ) y, twGenφ P T K' β γ hβ hγ p (twGenφ P T K' α β hα hβ p y) =
      c • twGenφ P T K' α γ hα hγ p y)
    (y : P.TTot (T.U α) (twFα P T K' α) (ovr hα)) :
    twTotφ P T K' β γ hβ hγ (twTotφ P T K' α β hα hβ y) =
      (c : P.D.A (ovr hγ).unop.left) • twTotφ P T K' α γ hα hγ y := by
  induction y using Tot.induction_on with
  | ht a e =>
    simp only [twTotφ, totMapAlong_tmul]
    have he : famMap (twGenφ P T K' β γ hβ hγ) (famMap (twGenφ P T K' α β hα hβ) e) =
        c • famMap (twGenφ P T K' α γ hα hγ) e := by
      induction e using DirectSum.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | of p x =>
        simp only [famMap_of]
        rw [hc p x]
        exact (map_smul (DirectSum.lof ↥(P.D.𝒜 (ovr hγ).unop.left 0) ℤ
          (P.FSec (T.U γ) (twFα P T K' γ) · (ovr hγ)) p) c _)
      | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    rw [he, Tot.tmul_smul0, Tot.smul_tmul]
    exact congrArg (Tot.tmul _ _ · _) (GCDga.central _ c.2 _).symm
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]

omit [CompactSpace X] in
/-- Z3.t: `ρ` commutes with restriction of the cocycle (copy of the private `psi_unitRes`). -/
private theorem ρ_unitRes_aux {W V : Opens X} (k : W ≤ V)
    (c : (P.toSheafData.O.obj.obj (op V))ˣ) :
    (P.ρSheafT.hom.app (op W)).hom
        (unitRes P.toSheafData.O k c : P.toSheafData.O.obj.obj (op W)) =
      (unitRes P.A0 k (Units.map (P.ρSheafT.hom.app (op V)).hom.toMonoidHom c) :
        P.A0.obj.obj (op W)) := by
  change (P.ρSheafT.hom.app (op W)).hom ((P.toSheafData.O.obj.map (homOfLE k).op).hom c) =
    (P.A0.obj.map (homOfLE k).op).hom ((P.ρSheafT.hom.app (op V)).hom c)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  exact congrArg (fun t => t.hom c) (P.ρSheafT.hom.naturality (homOfLE k).op)

/-- Z3.t: `twModelφ` commutes with restriction to `W' ≤ W`. -/
theorem twModelφ_res (n : ℤ) (α β : T.ι) {W W' : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (h' : W' ≤ W) (x : sec P.toSheafData.O (twTSh P T K' n α) hα) :
    twModelφ P T K' n α β (h'.trans hα) (h'.trans hβ)
        (secRes P.toSheafData.O (twTSh P T K' n α) hα h' x) =
      secRes P.toSheafData.O (twTSh P T K' n β) hβ h' (twModelφ P T K' n α β hα hβ x) :=
  Subtype.ext (twTotφ_tRes P T K' α β hα hβ h' x.1)

/-- Z3.t: `twModelφ α α` is the identity. -/
theorem twModelφ_self (n : ℤ) (α : T.ι) {W : Opens X} (hα : W ≤ T.U α)
    (x : sec P.toSheafData.O (twTSh P T K' n α) hα) :
    twModelφ P T K' n α α hα hα x = x :=
  Subtype.ext (totMapAlong_id (idAt P T hα hα) (fun _ => rfl) (twGenφ P T K' α α hα hα)
    (fun p y => ((K'.X p).bcObj P.ρSheafT).φ_self α hα y) (twGenφ_smul P T K' α α hα hα) x.1)

/-- Z3.t: the cocycle of the model is `ȟ` (acting through `ρ`). -/
theorem twModelφ_cocycle (n : ℤ) (α β γ : T.ι) {W : Opens X} (hα : W ≤ T.U α)
    (hβ : W ≤ T.U β) (hγ : W ≤ T.U γ) (x : sec P.toSheafData.O (twTSh P T K' n α) hα) :
    twModelφ P T K' n β γ hβ hγ (twModelφ P T K' n α β hα hβ x) =
      toSec P.toSheafData.O hγ
          (unitRes P.toSheafData.O (le_inf (le_inf hα hβ) hγ) (T.ch α β γ) :
            P.toSheafData.O.obj.obj (op W)) •
        twModelφ P T K' n α γ hα hγ x := by
  apply Subtype.ext
  have hρ := ρ_unitRes_aux P (le_inf (le_inf hα hβ) hγ) (T.ch α β γ)
  refine (twTotφ_cocycle_aux P T K' α β γ hα hβ hγ
    (unitRes P.A0 (le_inf (le_inf hα hβ) hγ) (chMap P.ρSheafT T.ch α β γ) :
      P.A0.obj.obj (op W))
    (fun p y => ((K'.X p).bcObj P.ρSheafT).cocycle α β γ hα hβ hγ y) x.1).trans ?_
  exact congrArg (fun c : P.D.A (ovr hγ).unop.left => c • twTotφ P T K' α γ hα hγ x.1)
    (congrArg Subtype.val hρ).symm

/-- **Z3.t (G′ (f)).** The `ȟ`-twisted `O`-module `T^tw,n`: components `T_α^n` (C7's `TSh` for
`F_α`), gluing `twModelφ`. -/
def twModelObj (n : ℤ) : TwMod P.toSheafData.O T.U T.ch where
  M α := twTSh P T K' n α
  φ α β _ hα hβ := twModelφ P T K' n α β hα hβ
  φ_smul α β _ hα hβ := twModelφ_smul P T K' n α β hα hβ
  φ_res α β _ _ hα hβ h' := twModelφ_res P T K' n α β hα hβ h'
  φ_self α _ hα := twModelφ_self P T K' n α hα
  cocycle α β γ _ hα hβ hγ := twModelφ_cocycle P T K' n α β γ hα hβ hγ

variable (θ : ∀ α, P.Conn (T.U α) (twFα P T K' α))
  (hθ : ∀ α, P.IsBCConn (T.U α) (twKα P T K' α) (θ α))

omit [CompactSpace X] in
/-- Z3.t: `of` on generators is `𝒜⁰`-linear. -/
private theorem PreResolvingData.of_smul_aux (U : Opens X)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (V : (Over U)ᵒᵖ) (p : ℤ)
    (s : ↥(P.D.𝒜 V.unop.left 0)) (z : P.FSec U F p V) :
    DirectSum.of (P.FSec U F · V) p (s • z) = s • DirectSum.of (P.FSec U F · V) p z :=
  map_smul (DirectSum.lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) p) s z

/-- Z3.t: `twTotφ ∘ θ_α − θ_β ∘ twGenφ` on the generator `e ∈ F_α^p(W)`, with values in `Tot`. -/
private def twDtot (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) :
    P.FSec (T.U α) (twFα P T K' α) p (ovr hα) →+ P.TTot (T.U β) (twFα P T K' β) (ovr hβ) :=
  (twTotφ P T K' α β hα hβ).comp (((θ α).θ (ovr hα)).θ.comp
      (DirectSum.of (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p)) -
    (((θ β).θ (ovr hβ)).θ.comp ((DirectSum.of (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p).comp
      (twGenφ P T K' α β hα hβ p)))

/-- Z3.t: `twDtot` lies in total degree `p + 1`. -/
private theorem twDtot_mem (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (y : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    twDtot P T K' θ p α β hα hβ y ∈ P.tDeg (T.U β) (twFα P T K' β) (p + 1) (ovr hβ) :=
  sub_mem (twTotφ_mem P T K' α β hα hβ (p + 1) ((θ α).mem (ovr hα) p y))
    ((θ β).mem (ovr hβ) p _)

/-- Z3.t: the family `twDtot` as additive maps into sections of the `𝒜⁰`-sheaf `T_β^{p+1}`. -/
private def twDfam (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    {W' : Opens X} (hW' : W' ≤ W) :
    P.FSec (T.U α) (twFα P T K' α) p (ovr (hW'.trans hα)) →+
      sec P.A0 (P.tShA (T.U β) (twFα P T K' β) (p + 1)) (hW'.trans hβ) where
  toFun y := (⟨twDtot P T K' θ p α β (hW'.trans hα) (hW'.trans hβ) y,
    twDtot_mem P T K' θ p α β (hW'.trans hα) (hW'.trans hβ) y⟩ :
      ↥(P.tDeg (T.U β) (twFα P T K' β) (p + 1) (ovr (hW'.trans hβ))))
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

/-- Z3.t: `twDtot` is `𝒜⁰(W)`-linear (both terms obey the Leibniz rule with the same `dr ⊗ ·`). -/
private theorem twDtot_smul (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (r : ↥(P.D.𝒜 (ovr hα).unop.left 0)) (y : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    twDtot P T K' θ p α β hα hβ (r • y) =
      (show P.D.A (ovr hβ).unop.left from (r : P.D.A (ovr hα).unop.left)) •
        twDtot P T K' θ p α β hα hβ y := by
  simp only [twDtot, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
  rw [twGenφ_smul, PreResolvingData.of_smul_aux, PreResolvingData.of_smul_aux,
    (θ α).θ (ovr hα) |>.leibniz, ((θ β).θ (ovr hβ)).leibniz]
  simp only [twTotφ, map_add, totMapAlong_tmul, totMapAlong_smul, famMap_of, smul_sub]
  exact add_sub_add_left_eq_sub _ _ _

/-- Z3.t: `twDtot` is natural for restriction (`Conn.natural`, `twTotφ_tRes`, `φ_res`). -/
private theorem twDtot_res (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    {W' : Opens X} (h' : W' ≤ W) (y : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    twDtot P T K' θ p α β (h'.trans hα) (h'.trans hβ)
        (P.fRes (T.U α) (twFα P T K' α) p
          (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hα)) ⟶
            Over.mk (homOfLE hα)).op y) =
      P.tRes (T.U β) (twFα P T K' β)
        (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hβ)) ⟶
            Over.mk (homOfLE hβ)).op (twDtot P T K' θ p α β hα hβ y) := by
  have hφ : twGenφ P T K' α β (h'.trans hα) (h'.trans hβ) p
      (P.fRes (T.U α) (twFα P T K' α) p
        (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hα)) ⟶
          Over.mk (homOfLE hα)).op y) =
      P.fRes (T.U β) (twFα P T K' β) p
        (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hβ)) ⟶
          Over.mk (homOfLE hβ)).op (twGenφ P T K' α β hα hβ p y) :=
    ((K'.X p).bcObj P.ρSheafT).φ_res α β hα hβ h' y
  have nα := (θ α).natural (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hα)) ⟶
            Over.mk (homOfLE hα)).op (DirectSum.of _ p y)
  have nβ := (θ β).natural (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hβ)) ⟶
            Over.mk (homOfLE hβ)).op (DirectSum.of _ p (twGenφ P T K' α β hα hβ p y))
  simp only [twDtot, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, map_sub]
  rw [← twTotφ_tRes P T K' α β hα hβ h', hφ]
  simp only [PreResolvingData.tRes_apply, nα, nβ, famMap_of]

/-- Z3.t: the zero family of additive maps (the second family in the uniqueness argument). -/
private def twZfam (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    {W' : Opens X} (hW' : W' ≤ W) :
    P.FSec (T.U α) (twFα P T K' α) p (ovr (hW'.trans hα)) →+
      sec P.A0 (P.tShA (T.U β) (twFα P T K' β) (p + 1)) (hW'.trans hβ) :=
  0

include hθ in
/-- Z3.t: `twDtot` vanishes on `η m` (IsBCConn, `bcφ_bcUnit`, `d` commutes with `φ`). -/
private theorem twDtot_bcUnit (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (m : sec P.toSheafData.O ((K'.X p).M α) hα) :
    twDtot P T K' θ p α β hα hβ (bcUnit P.ρSheafT ((K'.X p).M α) hα m) = 0 := by
  have e1 := hθ α (ovr hα) p m
  have e2 := hθ β (ovr hβ) p ((K'.X p).φ α β hα hβ m)
  have e3 := bcφ_bcUnit P.ρSheafT (K'.X p) α β hα hβ m
  have e5 := (K'.d p (p + 1)).comm α β hα hβ m
  have e4 := bcφ_bcUnit P.ρSheafT (K'.X (p + 1)) α β hα hβ
    ((((K'.d p (p + 1)).f α).val.app (ovr hα)).hom m)
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of] at e1 e2
  have e6 : twGenφ P T K' α β hα hβ (p + 1) (bcUnit P.ρSheafT ((K'.X (p + 1)).M α) hα
      ((((K'.d p (p + 1)).f α).val.app (ovr hα)).hom m)) =
      bcUnit P.ρSheafT ((K'.X (p + 1)).M β) hβ
        ((((K'.d p (p + 1)).f β).val.app (ovr hβ)).hom ((K'.X p).φ α β hα hβ m)) :=
    e4.trans (congrArg (bcUnit P.ρSheafT ((K'.X (p + 1)).M β) hβ) e5)
  have eB : ((θ β).θ (ovr hβ)).θ (DirectSum.of (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p
      (twGenφ P T K' α β hα hβ p (bcUnit P.ρSheafT ((K'.X p).M α) hα m))) =
      Tot.tmul (P.D.𝒜 (ovr hβ).unop.left) (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) 1
      (DirectSum.of (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) (p + 1)
        (bcUnit P.ρSheafT ((K'.X (p + 1)).M β) hβ
          ((((K'.d p (p + 1)).f β).val.app (ovr hβ)).hom ((K'.X p).φ α β hα hβ m)))) := by
    have := e3
    change _ = bcUnit P.ρSheafT ((K'.X p).M β) hβ ((K'.X p).φ α β hα hβ m) at this
    exact (congrArg (fun z => ((θ β).θ (ovr hβ)).θ
      (DirectSum.of (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p z)) this).trans e2
  refine sub_eq_zero.2 ?_
  refine (congrArg (twTotφ P T K' α β hα hβ) e1).trans (Eq.trans ?_ eB.symm)
  simp only [twTotφ, totMapAlong_tmul, famMap_of]
  exact congrArg (fun z => Tot.tmul (P.D.𝒜 (ovr hβ).unop.left)
    (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) 1
    (DirectSum.of (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) (p + 1) z)) e6

include hθ in
/-- Z3.t: `twDtot` vanishes identically (uniqueness on `η`, `sec_eq_of_bcUnit`): the two
connections `θ_β ∘ twGenφ` and `twTotφ ∘ θ_α` agree on the generators. -/
private theorem twDtot_eq_zero (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (y : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    twDtot P T K' θ p α β hα hβ y = 0 := by
  have := sec_eq_of_bcUnit (ψ := P.ρSheafT) hα hβ (M := (K'.X p).M α)
    (Q := P.tShA (T.U β) (twFα P T K' β) (p + 1))
    (fun {W'} hW' => twDfam P T K' θ p α β hα hβ hW')
    (fun {W'} hW' => twZfam P T K' p α β hα hβ hW')
    (fun {W'} hW' r x => Subtype.ext (twDtot_smul P T K' θ p α β _ _ r x))
    (fun {W' W''} hW' h' x => Subtype.ext (twDtot_res P T K' θ p α β _ _ h' x))
    (fun {W'} hW' r x => (smul_zero _).symm)
    (fun {W' W''} hW' h' x => (map_zero _).symm)
    (fun {W'} hW' m => Subtype.ext (twDtot_bcUnit P T K' θ hθ p α β _ _ m)) y
  exact congrArg Subtype.val this

include hθ in
/-- **Z3.t (G′ (f)).** The differentials `θ_α.TD` commute with the gluing of the model:
`θ_β ∘ φ^T = φ^T ∘ θ_α` (both are connections; their difference is `𝒜⁰`-linear and vanishes on
`1 ⊗ η k` since `d_{K'}` commutes with the gluing of `K'`, C.7′ (b)). -/
theorem twModel_TD_comm (n : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (x : sec P.toSheafData.O (twTSh P T K' n α) hα) :
    twModelφ P T K' (n + 1) α β hα hβ ((((θ α).TD n).val.app (ovr hα)).hom x) =
      (((θ β).TD n).val.app (ovr hβ)).hom (twModelφ P T K' n α β hα hβ x) := by
  refine Subtype.ext (totMapAlong_extend (idAt P T hα hβ) (twGenφ P T K' α β hα hβ)
    (twGenφ_smul P T K' α β hα hβ) ((θ α).θ (ovr hα)) ((θ β).θ (ovr hβ)) (fun e => ?_) x.1)
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p y =>
    rw [famMap_of]
    exact sub_eq_zero.1 (twDtot_eq_zero P T K' θ hθ p α β hα hβ y)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **Z3.t (G′ (f)).** The differential `T^tw,n ⟶ T^tw,n+1`, components `θ_α.TD n`. -/
def twModelD (n : ℤ) : twModelObj P T K' n ⟶ twModelObj P T K' (n + 1) :=
  ⟨fun α => (θ α).TD n, fun α β _ hα hβ x => twModel_TD_comm P T K' θ hθ n α β hα hβ x⟩

/-- Z3.t: `d² = 0` on the twisted model (componentwise `TD_TD`). -/
theorem twModelD_twModelD (n : ℤ) :
    twModelD P T K' θ hθ n ≫ twModelD P T K' θ hθ (n + 1) = 0 :=
  TwMod.hom_ext fun α => (θ α).TD_TD n

/-- **Z3.t (G′ (f)).** [A, Rem 7.2.4], blueprint-tw G.9. The twisted model `T^tw(K')`, a complex
of `ȟ`-twisted `O`-modules with components the C7 models `θ_α.TC`. -/
def twModel : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ :=
  CochainComplex.of (twModelObj P T K') (twModelD P T K' θ hθ) (twModelD_twModelD P T K' θ hθ)

/-- **Z3.t (G′ (f)).** `ιT` commutes with the gluing: `φ^T(1 ⊗ η k) = 1 ⊗ η(φ k)`
(`bcφ_bcUnit`). -/
theorem ιTtw_comm (n : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (x : sec P.toSheafData.O ((K'.X n).M α) hα) :
    twModelφ P T K' n α β hα hβ ((((P.ιT (θ α) (hθ α)).f n).val.app (ovr hα)).hom x) =
      (((P.ιT (θ β) (hθ β)).f n).val.app (ovr hβ)).hom ((K'.X n).φ α β hα hβ x) := by
  have e3 := bcφ_bcUnit P.ρSheafT (K'.X n) α β hα hβ x
  refine Subtype.ext ?_
  change twTotφ P T K' α β hα hβ (Tot.tmul (P.D.𝒜 (ovr hα).unop.left)
      (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) 1
      (DirectSum.lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ
        (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) n
        (P.bcη (T.U α) (twKα P T K' α) n (ovr hα) x))) =
    Tot.tmul (P.D.𝒜 (ovr hβ).unop.left) (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) 1
      (DirectSum.lof ↥(P.D.𝒜 (ovr hβ).unop.left 0) ℤ
        (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) n
        (P.bcη (T.U β) (twKα P T K' β) n (ovr hβ) ((K'.X n).φ α β hα hβ x)))
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  simp only [twTotφ, totMapAlong_tmul, famMap_of]
  exact congrArg (fun z => Tot.tmul (P.D.𝒜 (ovr hβ).unop.left)
    (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) 1
    (DirectSum.of (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) n z)) e3

/-- **Z3.t (G′ (f)).** [A, Rem 7.2.4], blueprint-tw G.9. `ιT^tw : K' ⟶ T^tw(K')`, componentwise
C7.d's `ιT` (`k ↦ 1 ⊗ η k`). -/
def ιTtw : K' ⟶ twModel P T K' θ hθ where
  f n := ⟨fun α => (P.ιT (θ α) (hθ α)).f n,
    fun α β _ hα hβ x => ιTtw_comm P T K' θ hθ n α β hα hβ x⟩
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine TwMod.hom_ext fun α => ?_
    have e1 : (twModel P T K' θ hθ).d i (i + 1) = twModelD P T K' θ hθ i :=
      CochainComplex.of_d _ _ _
    rw [e1]
    exact PreResolvingData.ιTn_comm (θ α) (hθ α) i

/-- Z3.t: a morphism of complexes of twisted sheaves is a quasi-isomorphism if all its component
morphisms are (homology commutes with the exact component functors, which jointly reflect
isomorphisms, `TwMod.isIso_of_isIso_f`). -/
theorem quasiIso_of_twComp
    {M N : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ} (g : M ⟶ N)
    (hg : ∀ α, QuasiIso (((TwMod.comp P.toSheafData.O T.U T.ch α).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g)) : QuasiIso g := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff]
  have γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) i).map g)
      (M.sc i).leftHomologyData (N.sc i).leftHomologyData := default
  rw [γ.quasiIso_iff]
  have h2 : ∀ α, IsIso ((TwMod.comp P.toSheafData.O T.U T.ch α).map γ.φH) := fun α => by
    have h3 : ShortComplex.QuasiIso
        ((TwMod.comp P.toSheafData.O T.U T.ch α).mapShortComplex.map
          ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) i).map g)) :=
      (quasiIsoAt_iff _ i).1 ((quasiIso_iff _).1 (hg α) i)
    rw [(γ.map (TwMod.comp P.toSheafData.O T.U T.ch α)).quasiIso_iff] at h3
    exact h3
  exact @TwMod.isIso_of_isIso_f _ _ _ _ _ _ _ _ γ.φH h2

/-- Z3.t: C7.d's `quasiIso_ιT` for pre-resolving data, with the quasi-isomorphism property of
`ρ̂ : O → 𝒜^•` as a hypothesis (the proof of `ResolvingData.quasiIso_ιT` uses only this). -/
private theorem quasiIso_ιT_of_ρhat (hρhat : QuasiIso P.ρhat) (U : Opens X)
    (K : CochainComplex (Mod (P.R.over U)) ℤ) (hK : IsKFlat (P.O.over U) K)
    (θ : P.Conn U (P.FK U K)) (hθ : P.IsBCConn U K θ) : QuasiIso (P.ιT θ hθ) := by
  obtain ⟨e, u, h⟩ := P.exists_TC_iso_tensorC U K θ hθ
  have hρ : QuasiIso (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map P.ρhat) :=
    haveI := hρhat
    inferInstance
  have hc := (quasiIso_iff_acyclic_mappingCone
    (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map P.ρhat)).1 hρ
  have h1 := hK _ hc
  have h2 : QuasiIso (tensorCMap₁ (P.O.over U)
      (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map P.ρhat) K) := by
    refine (quasiIso_iff_acyclic_mappingCone _).2 ?_
    exact fun i => (h1 i).of_iso
      ((tensorCSymIso (P.O.over U) _ _).symm ≪≫ tensorCConeIso₁ (P.O.over U) _ K)
  have hu : QuasiIso u.hom := by
    have := Iso.isIso_hom u
    exact quasiIso_of_isIso _
  have he : QuasiIso e.hom := by
    have := Iso.isIso_hom e
    exact quasiIso_of_isIso _
  have h3 : QuasiIso (P.ιT θ hθ ≫ e.hom) := by
    rw [h]
    exact quasiIso_comp _ _ (hφ := hu) (hφ' := h2)
  exact (quasiIso_iff_comp_right (P.ιT θ hθ) e.hom).1 h3

/-- Z3.t: the `α`-component complex of `T^tw(K')` is C7's `θ_α.TC` (componentwise identities;
the two differentials agree by `CochainComplex.of_d`). -/
def twCompIso (α : T.ι) :
    ((TwMod.comp P.toSheafData.O T.U T.ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (twModel P T K' θ hθ) ≅ (θ α).TC :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) (fun i j hij => by
    obtain rfl : i + 1 = j := hij
    have e1 : (twModel P T K' θ hθ).d i (i + 1) = twModelD P T K' θ hθ i :=
      CochainComplex.of_d _ _ _
    have e2 : (θ α).TC.d i (i + 1) = (θ α).TD i := CochainComplex.of_d _ _ _
    change 𝟙 _ ≫ (θ α).TC.d i (i + 1) =
      (TwMod.comp P.toSheafData.O T.U T.ch α).map ((twModel P T K' θ hθ).d i (i + 1)) ≫ 𝟙 _
    rw [e1, e2]
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

/-- Z3.t: `ιT^tw`, followed by the identification `twCompIso`, is C7's `ιT` componentwise. -/
private theorem comp_map_ιTtw (α : T.ι) :
    ((TwMod.comp P.toSheafData.O T.U T.ch α).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (ιTtw P T K' θ hθ) ≫ (twCompIso P T K' θ hθ α).hom = P.ιT (θ α) (hθ α) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  exact Category.comp_id _

/-- **Z3.t (G′ (e), (f)).** `ιT^tw` is a quasi-isomorphism when `ρ̂ : O → 𝒜^•` is a resolution
(`hρ`; for resolving data `ResolvingData.quasiIso_ρhat`) and every component `K'_α` is K-flat
(C7.d `quasiIso_ιT` componentwise; quasi-isomorphisms of twisted complexes are detected on
components, C.6 (e)). -/
theorem quasiIso_ιTtw (hρ : QuasiIso P.ρhat)
    (hK : ∀ α, IsKFlat (P.O.over (T.U α)) (twKα P T K' α)) :
    QuasiIso (ιTtw P T K' θ hθ) := by
  have hρhat : QuasiIso P.ρhat := hρ
  refine quasiIso_of_twComp P T (ιTtw P T K' θ hθ) fun α => ?_
  have h1 := quasiIso_ιT_of_ρhat P hρhat (T.U α) (twKα P T K' α) (hK α) (θ α) (hθ α)
  rw [← comp_map_ιTtw P T K' θ hθ α] at h1
  have hI := Iso.isIso_hom (twCompIso P T K' θ hθ α)
  have hQ : QuasiIso (twCompIso P T K' θ hθ α).hom := quasiIso_of_isIso _
  exact (quasiIso_iff_comp_right _ (twCompIso P T K' θ hθ α).hom).1 h1

end Cohesive
