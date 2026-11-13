import Cohesivemodules.Comparison.TwistedCurvedAux
import Cohesivemodules.Comparison.TwistedLocal

set_option linter.style.header false

/-!
# Z3.t: generators of the curved model and their localizations (blueprint-tw G′ (g))

Part 1 of the curved model of `TwistedCurvedModel.lean` (split for file size). For pre-resolving
data `P` (`X` compact), a twist datum `T` for a closed `h ∈ 𝒜²(X)` and a complex `K'` of
`ȟ`-twisted `O`-modules, with `F = untwist(K')` (G′ (b)):
* `twGens p = F^p(X)`, `πgen α : F^p(X) → F_α^p(U_α)`, `TotX = Tot(𝒜(X), F(X))`, and
  `πTot α : TotX → Tot(𝒜(U_α), F_α(U_α))` along `res`;
* `πTot_ext` (G′ (g)): elements of `TotX` are determined by their images `πTot α`;
* `𝒜h`: the curved algebra `(𝒜(X), h)`; `twGensModH`: `F^p(X)` as an `𝒜h⁰`-module;
* helpers: component isomorphisms `cmpW`, `cTotW` between `F|W` and `F_α|W` for `W ≤ U_α`, their
  compatibility on overlaps (`cTotW_compat`, via `fuA = u_αβ⁻¹` and `d_fuA`), and a copy `tShAC`
  of the sheaf `T^n` of C7.a typed over `𝒜⁰`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum
open PreResolvingData (topO)

variable {X : Type} [TopologicalSpace X] [CompactSpace X] (P : PreResolvingData X)
  {h : P.D.A ⊤} (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2)
  (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (K' : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ)

/-- **Z3.t (G′ (b)).** `F = untwist(K')`, a complex of sheaves of `𝒜⁰`-modules on `X`. -/
abbrev untwF : CochainComplex (Mod (ringOf P.A0)) ℤ :=
  ((untwist P T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K'

/-- Z3.t: `F` on the over-site of `⊤` (C7's setting, as in C5). -/
abbrev twFtop : CochainComplex (Mod ((ringOf P.A0).over ⊤)) ℤ :=
  ((restr (ringOf P.A0) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj (untwF P T K')

/-- **Z3.t (G′ (h)).** The generators `F^p(X)` of `N^h`. -/
abbrev twGens (p : ℤ) : Type := P.FSec ⊤ (twFtop P T K') p (topO ⊤)

/-- Z3.t: the restriction `𝒜(X) → 𝒜(U_α)`, typed between the algebras at the terminal objects of
`Over ⊤` and `Over U_α`. -/
abbrev resα (α : T.ι) :
    DgaHom (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (P.D.𝒜 (topO (T.U α)).unop.left) :=
  P.D.res (le_top : T.U α ≤ ⊤)

/-- **Z3.t (G′ (g)).** The component `α` of the restriction to `U_α`, `F^p(X) → F_α^p(U_α)`
(`untwistComp` after restriction). -/
def πgen (α : T.ι) (p : ℤ) :
    twGens P T K' p →+ P.FSec (T.U α) (twFα P T K' α) p (topO (T.U α)) :=
  (untwistComp P T (K'.X p) α (le_refl (T.U α))).comp
    (((untwF P T K').X p).val.map (homOfLE (le_top : T.U α ≤ ⊤)).op).hom.toAddMonoidHom

/-- Z3.t: `πgen` is semilinear along `res⁰`. -/
theorem πgen_smul (α : T.ι) (p : ℤ) (r : ↥(P.D.𝒜 (topO (⊤ : Opens X)).unop.left 0))
    (s : twGens P T K' p) :
    πgen P T K' α p (r • s) = (resα P T α).f0 r • πgen P T K' α p s := by
  have h1 := (((untwF P T K').X p).val.map (homOfLE (le_top : T.U α ≤ ⊤)).op).hom.map_smul r s
  have h2 := ((untwistRestrIso P T (K'.X p) α).hom.val.app (ovr (le_refl (T.U α)))).hom.map_smul
  unfold πgen
  exact (congrArg (untwistComp P T (K'.X p) α (le_refl (T.U α))) h1).trans (h2 _ _)

/-- Z3.t: the total module `Tot(𝒜(X), F(X))` (flat instance; the curved instance has the same
carrier, conversions by `show`). -/
abbrev TotX : Type := Tot (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K')

/-- **Z3.t (G′ (g)).** `πTot α : Tot(𝒜(X), F(X)) → Tot(𝒜(U_α), F_α(U_α))`,
`a ⊗ s ↦ a|U_α ⊗ πgen α s`. -/
def πTot (α : T.ι) :
    Tot (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K') →+
      P.TTot (T.U α) (twFα P T K' α) (topO (T.U α)) :=
  totMapAlong (resα P T α) (πgen P T K' α) (πgen_smul P T K' α)

/-- Z3.t: the identity of `𝒜(U_α)`, typed from the algebra at `ovr` to that at `topO`. -/
abbrev idUα (α : T.ι) :
    DgaHom (P.D.𝒜 (ovr (le_top : T.U α ≤ ⊤)).unop.left)
      (P.D.𝒜 (topO (T.U α)).unop.left) :=
  DgaHom.id (P.D.𝒜 (T.U α))

/-- Z3.t: the component `α` of sections of `F` over `U_α`, `F^p(U_α) → F_α^p(U_α)`. -/
def compGen (α : T.ι) (p : ℤ) :
    P.FSec ⊤ (twFtop P T K') p (ovr (le_top : T.U α ≤ ⊤)) →+
      P.FSec (T.U α) (twFα P T K' α) p (topO (T.U α)) :=
  untwistComp P T (K'.X p) α (le_refl (T.U α))

/-- Z3.t: `compGen` is semilinear along the identity of `𝒜⁰(U_α)`. -/
theorem compGen_smul (α : T.ι) (p : ℤ)
    (r : ↥(P.D.𝒜 (ovr (le_top : T.U α ≤ ⊤)).unop.left 0))
    (s : P.FSec ⊤ (twFtop P T K') p (ovr (le_top : T.U α ≤ ⊤))) :
    compGen P T K' α p (r • s) = (idUα P T α).f0 r • compGen P T K' α p s :=
  ((untwistRestrIso P T (K'.X p) α).hom.val.app (ovr (le_refl (T.U α)))).hom.map_smul r s

/-- Z3.t: the component map on total modules over `U_α`. -/
def cTot (α : T.ι) :
    P.TTot ⊤ (twFtop P T K') (ovr (le_top : T.U α ≤ ⊤)) →+
      P.TTot (T.U α) (twFα P T K' α) (topO (T.U α)) :=
  totMapAlong (idUα P T α) (compGen P T K' α) (compGen_smul P T K' α)

/-- Z3.t: `πTot α` is `cTot α` after the restriction `tRes` to `U_α`. -/
theorem πTot_eq_cTot (α : T.ι) (x : TotX P T K') :
    πTot P T K' α x = cTot P T K' α (P.tRes ⊤ (twFtop P T K')
      (PreResolvingData.toV (ovr (le_top : T.U α ≤ ⊤))) x) :=
  (totMapAlong_comp (idUα P T α)
    (P.D.res (leOfHom (PreResolvingData.toV (ovr (le_top : T.U α ≤ ⊤))).unop.left))
    (resα P T α) (fun a => rfl)
    (fun p => P.fRes ⊤ (twFtop P T K') p (PreResolvingData.toV (ovr (le_top : T.U α ≤ ⊤))))
    (compGen P T K' α) (πgen P T K' α) (fun p x => rfl)
    (fun p => P.fRes_smul ⊤ (twFtop P T K') _ p) (compGen_smul P T K' α) (πgen_smul P T K' α)
    x).symm

/-- Z3.t: the identity of `𝒜(U_α)`, typed from the algebra at `topO` to that at `ovr`. -/
abbrev idUα' (α : T.ι) :
    DgaHom (P.D.𝒜 (topO (T.U α)).unop.left)
      (P.D.𝒜 (ovr (le_top : T.U α ≤ ⊤)).unop.left) :=
  DgaHom.id (P.D.𝒜 (T.U α))

/-- Z3.t: the inverse of the component `α` on sections over `U_α`. -/
def compGenInv (α : T.ι) (p : ℤ) :
    P.FSec (T.U α) (twFα P T K' α) p (topO (T.U α)) →+
      P.FSec ⊤ (twFtop P T K') p (ovr (le_top : T.U α ≤ ⊤)) :=
  ((untwistRestrIso P T (K'.X p) α).inv.val.app (ovr (le_refl (T.U α)))).hom.toAddMonoidHom

/-- Z3.t: `compGenInv` is semilinear along the identity of `𝒜⁰(U_α)`. -/
theorem compGenInv_smul (α : T.ι) (p : ℤ) (r : ↥(P.D.𝒜 (topO (T.U α)).unop.left 0))
    (s : P.FSec (T.U α) (twFα P T K' α) p (topO (T.U α))) :
    compGenInv P T K' α p (r • s) = (idUα' P T α).f0 r • compGenInv P T K' α p s :=
  ((untwistRestrIso P T (K'.X p) α).inv.val.app (ovr (le_refl (T.U α)))).hom.map_smul r s

/-- Z3.t: `compGenInv ∘ compGen = id`. -/
theorem compGenInv_compGen (α : T.ι) (p : ℤ)
    (s : P.FSec ⊤ (twFtop P T K') p (ovr (le_top : T.U α ≤ ⊤))) :
    compGenInv P T K' α p (compGen P T K' α p s) = s :=
  congrArg (fun k => (k.val.app (ovr (le_refl (T.U α)))).hom s)
    (untwistRestrIso P T (K'.X p) α).hom_inv_id

/-- Z3.t: the component map on total modules is injective (it has the inverse `compGenInv`). -/
theorem cTot_injective (α : T.ι) {x y : P.TTot ⊤ (twFtop P T K') (ovr (le_top : T.U α ≤ ⊤))}
    (h : cTot P T K' α x = cTot P T K' α y) : x = y := by
  have key : ∀ z, totMapAlong (idUα' P T α) (compGenInv P T K' α) (compGenInv_smul P T K' α)
      (cTot P T K' α z) = z := fun z => by
    rw [cTot, totMapAlong_comp (idUα' P T α) (idUα P T α)
      (DgaHom.id (P.D.𝒜 (ovr (le_top : T.U α ≤ ⊤)).unop.left)) (fun a => rfl) (compGen P T K' α)
      (compGenInv P T K' α) (fun p => AddMonoidHom.id _)
      (fun p x => compGenInv_compGen P T K' α p x)
      (compGen_smul P T K' α) (compGenInv_smul P T K' α) (fun p r x => rfl) z]
    exact totMapAlong_id _ (fun a => rfl) _ (fun p x => rfl) _ z
  rw [← key x, ← key y, h]

/-- Z3.t: the `𝒜⁰(V)`-module structure on `tDeg`, typed over the ring of sections of `𝒜⁰|U`
(copy of the private instance of `TwistedModel.lean`; a local instance in the files of the curved
model). -/
@[reducible] def PreResolvingData.tDegModuleC (U : Opens X)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (n : ℤ) (V : (Over U)ᵒᵖ) :
    Module (((ringOf P.A0).over U).obj.obj V) ↥(P.tDeg U F n V) :=
  inferInstanceAs (Module ↥(P.D.𝒜 V.unop.left 0) ↥(P.tDeg U F n V))

attribute [local instance] PreResolvingData.tDegModuleC

/-- Z3.t: restriction of `T^n` as a semilinear map over `𝒜⁰`. -/
def PreResolvingData.tResAC (U : Opens X)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (n : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    ↥(P.tDeg U F n V) →ₛₗ[(((ringOf P.A0).over U).obj.map f).hom] ↥(P.tDeg U F n W) where
  toFun x := ⟨P.tRes U F f x.1, P.tRes_mem U F f x.2⟩
  map_add' x y := Subtype.ext (map_add (P.tRes U F f) x.1 y.1)
  map_smul' r x :=
    Subtype.ext (P.tRes_smul U F f (show ↥(P.D.𝒜 V.unop.left 0) from r).1 x.1)

/-- Z3.t: `T^n` as a presheaf of `𝒜⁰|U`-modules. -/
def PreResolvingData.tPreAC (U : Opens X)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (n : ℤ) :
    PresheafOfModules.{0} ((ringOf P.A0).over U).obj where
  obj V := ModuleCat.of (P.D.𝒜 V.unop.left 0) ↥(P.tDeg U F n V)
  map {V W} f := ModuleCat.semilinearMapAddEquiv (((ringOf P.A0).over U).obj.map f).hom
      (ModuleCat.of (P.D.𝒜 V.unop.left 0) ↥(P.tDeg U F n V))
      (ModuleCat.of (P.D.𝒜 W.unop.left 0) ↥(P.tDeg U F n W))
      (P.tResAC U F n f)
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

/-- Z3.t: `T^n` as a sheaf of `𝒜⁰|U`-modules (C7.a). -/
def PreResolvingData.tShAC (U : Opens X)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (n : ℤ) : Mod ((ringOf P.A0).over U) :=
  ⟨P.tPreAC U F n, P.isSheaf_TPre U F n⟩

/-- Z3.t: the restriction `Over.mk (U_α ⟶ ⊤) → Over.mk (⊤ ⟶ ⊤)` as a morphism of the over-site. -/
abbrev toUα (α : T.ι) :
    ovr (le_refl (⊤ : Opens X)) ⟶ ovr ((le_top : T.U α ≤ ⊤).trans (le_refl ⊤)) :=
  (Over.homMk (homOfLE (le_top : T.U α ≤ ⊤)) :
    Over.mk (homOfLE ((le_top : T.U α ≤ ⊤).trans (le_refl ⊤))) ⟶
      Over.mk (homOfLE (le_refl (⊤ : Opens X)))).op

/-- Z3.t: `secRes` of the sheaf `T^n` is `tRes`. -/
theorem secRes_tShAC (n : ℤ) (α : T.ι)
    (z : P.tDeg ⊤ (twFtop P T K') n (ovr (le_refl (⊤ : Opens X)))) :
    (show P.tDeg ⊤ (twFtop P T K') n (ovr ((le_top : T.U α ≤ ⊤).trans (le_refl ⊤))) from
      secRes P.A0 (P.tShAC ⊤ (twFtop P T K') n) (le_refl (⊤ : Opens X))
        (le_top : T.U α ≤ ⊤) z).1 =
      P.tRes ⊤ (twFtop P T K') (toUα P T α) z.1 := rfl

/-- Z3.t: the restriction `toV` agrees with `toUα`. -/
theorem tRes_toV (α : T.ι) (x : P.TTot ⊤ (twFtop P T K') (topO ⊤)) :
    P.tRes ⊤ (twFtop P T K') (PreResolvingData.toV (ovr (le_top : T.U α ≤ ⊤))) x =
      P.tRes ⊤ (twFtop P T K') (toUα P T α) x := rfl

/-- Z3.t: degree-`n` elements of `Tot(𝒜(X), F(X))` with equal restrictions to all `U_α` are equal
(separatedness of the sheaf `T^n`, `sec_ext_of_cover`). -/
theorem tDeg_ext (n : ℤ) {x y : P.TTot ⊤ (twFtop P T K') (ovr (le_refl (⊤ : Opens X)))}
    (hx : x ∈ P.tDeg ⊤ (twFtop P T K') n (ovr (le_refl (⊤ : Opens X))))
    (hy : y ∈ P.tDeg ⊤ (twFtop P T K') n (ovr (le_refl (⊤ : Opens X))))
    (h : ∀ α, P.tRes ⊤ (twFtop P T K') (toUα P T α) x =
      P.tRes ⊤ (twFtop P T K') (toUα P T α) y) :
    x = y := by
  let t : sec P.A0 (P.tShAC ⊤ (twFtop P T K') n) (le_refl (⊤ : Opens X)) := ⟨x, hx⟩
  let t' : sec P.A0 (P.tShAC ⊤ (twFtop P T K') n) (le_refl (⊤ : Opens X)) := ⟨y, hy⟩
  have h1 : ∀ α, secRes P.A0 (P.tShAC ⊤ (twFtop P T K') n) (le_refl (⊤ : Opens X))
      (le_top : T.U α ≤ ⊤) t = secRes P.A0 (P.tShAC ⊤ (twFtop P T K') n)
      (le_refl (⊤ : Opens X)) (le_top : T.U α ≤ ⊤) t' := fun α => by
    apply Subtype.ext
    have e1 := secRes_tShAC P T K' n α ⟨x, hx⟩
    have e2 := secRes_tShAC P T K' n α ⟨y, hy⟩
    exact e1.trans ((h α).trans e2.symm)
  have := sec_ext_of_cover (R := P.A0) (le_refl (⊤ : Opens X)) (P.tShAC ⊤ (twFtop P T K') n)
    T.U (fun α => le_top) T.iSup_eq.ge t t' h1
  exact congrArg Subtype.val this

/-- **Z3.t (G′ (g)).** Elements of `Tot(𝒜(X), F(X))` are determined by their images under all
`πTot α` (`T(F)` is a sheaf, C7.a, and sections of `F` are determined by their components,
`untwist_ext`). -/
theorem πTot_ext (x y : Tot (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K'))
    (hxy : ∀ α, πTot P T K' α x = πTot P T K' α y) : x = y := by
  refine eq_of_degComp x y fun n => ?_
  have key : ∀ (α : T.ι) (z : TotX P T K'), cTot P T K' α (P.tRes ⊤ (twFtop P T K')
      (toUα P T α) z) = πTot P T K' α z := fun α z => (πTot_eq_cTot P T K' α z).symm
  have hπ : ∀ (α : T.ι) (z : TotX P T K'), πTot P T K' α (degComp _ _ n z) =
      degComp _ _ n (πTot P T K' α z) := fun α z =>
    (degComp_totMapAlong (resα P T α) (πgen P T K' α) (πgen_smul P T K' α) n z).symm
  refine tDeg_ext P T K' n (degComp_mem n x) (degComp_mem n y) fun α => ?_
  refine cTot_injective P T K' α ?_
  rw [key, key, hπ, hπ, hxy α]

/-- Z3.t: `πTot α` commutes with the total-degree components. -/
theorem πTot_degComp (α : T.ι) (n : ℤ) (z : TotX P T K') :
    πTot P T K' α (degComp (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K') n z) =
      degComp (P.D.𝒜 (topO (T.U α)).unop.left)
        (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) n (πTot P T K' α z) :=
  (degComp_totMapAlong (resα P T α) (πgen P T K' α) (πgen_smul P T K' α) n z).symm

/-- Z3.t: an element of `Tot(𝒜(X), F(X))` has total degree `m` if all its images `πTot α` do. -/
theorem mem_totDeg_of_πTot (m : ℤ) (x : TotX P T K')
    (h : ∀ α, πTot P T K' α x ∈ P.tDeg (T.U α) (twFα P T K' α) m (topO (T.U α))) :
    x ∈ totDeg (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K') m := by
  have e : degComp (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K') m x = x := by
    refine πTot_ext P T K' _ _ fun α => ?_
    rw [πTot_degComp]
    exact degComp_self (h α)
  rw [← e]
  exact degComp_mem m x

/-- Z3.t: elements of `⨁_p F^p(X)` are determined by their images under all `famMap (πgen α)`
(`πTot_ext` on `1 ⊗ e`, then `ε`). -/
theorem gen_ext (e e' : ⨁ p, twGens P T K' p)
    (h : ∀ α, famMap (πgen P T K' α) e = famMap (πgen P T K' α) e') : e = e' := by
  have h1 := πTot_ext P T K' (Tot.oneTmul (P.D.𝒜 (topO (⊤ : Opens X)).unop.left)
    (twGens P T K') e) (Tot.oneTmul _ _ e') fun α => by
    rw [Tot.oneTmul_apply, Tot.oneTmul_apply]
    exact (congrArg (πTot P T K' α) rfl).trans (by
      show Tot.tmul _ _ ((resα P T α) 1) (famMap (πgen P T K' α) e) =
        Tot.tmul _ _ ((resα P T α) 1) (famMap (πgen P T K' α) e')
      rw [DgaHom.map_one', h α])
  have h2 := congrArg (Tot.eps (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K')) h1
  rwa [Tot.eps_oneTmul, Tot.eps_oneTmul] at h2

/-- Z3.t: `πgen` commutes with the differentials of `F` and `F_α` (naturality of
`untwistRestrIso`). -/
theorem πgen_fD (α : T.ι) (p : ℤ) (s : twGens P T K' p) :
    P.fD (T.U α) (twFα P T K' α) p (topO (T.U α)) (πgen P T K' α p s) =
      πgen P T K' α (p + 1) (P.fD ⊤ (twFtop P T K') p (topO ⊤) s) := by
  have n1 := PresheafOfModules.naturality_apply ((untwist P T).map (K'.d p (p + 1))).val
    (homOfLE (le_top : T.U α ≤ ⊤)).op s
  have n2 := congrArg (fun k => (k.val.app (ovr (le_refl (T.U α)))).hom
    ((((untwF P T K').X p).val.map (homOfLE (le_top : T.U α ≤ ⊤)).op).hom s))
    (untwistRestrIso_hom_naturality P T (K'.d p (p + 1)) α)
  exact n2.symm.trans (congrArg (fun z =>
    ((untwistRestrIso P T (K'.X (p + 1)) α).hom.val.app (ovr (le_refl (T.U α)))).hom z) n1)

/-- Z3.t: the curved algebra `(𝒜(X), h)` of the twisted theorem (`withCurvature`, Z3.a). -/
abbrev 𝒜h : ℤ → Submodule ℂ ((P.toSheafData.withCurvature h hh hd).D.A ⊤) :=
  (P.toSheafData.withCurvature h hh hd).𝒜X

/-- Z3.t: the generators `F^p(X)` are modules over `𝒜⁰(X)` of the curved algebra (the same ring as
for the flat one; definitionally C7's instance). -/
instance twGensModH (p : ℤ) : Module ↥(𝒜h P hh hd 0) (twGens P T K' p) :=
  fSecModule P (twFtop P T K') p (topO ⊤)

/-- Z3.t: the identity of `𝒜(W)`, typed between the algebras at two over-objects with `W`. -/
abbrev idW {U U' W : Opens X} (h1 : W ≤ U) (h2 : W ≤ U') :
    DgaHom (P.D.𝒜 (ovr h1).unop.left) (P.D.𝒜 (ovr h2).unop.left) :=
  DgaHom.id (P.D.𝒜 W)

/-- Z3.t: the component `α` of sections of `F` over `W ≤ U_α` (`untwistComp`). -/
def cmpW (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (p : ℤ) :
    P.FSec ⊤ (twFtop P T K') p (ovr (hα.trans le_top)) →+
      P.FSec (T.U α) (twFα P T K' α) p (ovr hα) :=
  untwistComp P T (K'.X p) α hα

/-- Z3.t: `cmpW` is semilinear along the identity of `𝒜⁰(W)`. -/
theorem cmpW_smul (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (p : ℤ)
    (r : ↥(P.D.𝒜 (ovr (hα.trans le_top)).unop.left 0))
    (s : P.FSec ⊤ (twFtop P T K') p (ovr (hα.trans le_top))) :
    cmpW P T K' α hα p (r • s) = (idW P (hα.trans le_top) hα).f0 r • cmpW P T K' α hα p s :=
  ((untwistRestrIso P T (K'.X p) α).hom.val.app (ovr hα)).hom.map_smul r s

/-- Z3.t: the inverse of `cmpW`. -/
def cmpWInv (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (p : ℤ) :
    P.FSec (T.U α) (twFα P T K' α) p (ovr hα) →+
      P.FSec ⊤ (twFtop P T K') p (ovr (hα.trans le_top)) :=
  ((untwistRestrIso P T (K'.X p) α).inv.val.app (ovr hα)).hom.toAddMonoidHom

/-- Z3.t: `cmpWInv` is semilinear along the identity of `𝒜⁰(W)`. -/
theorem cmpWInv_smul (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (p : ℤ)
    (r : ↥(P.D.𝒜 (ovr hα).unop.left 0)) (s : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    cmpWInv P T K' α hα p (r • s) =
      (idW P hα (hα.trans le_top)).f0 r • cmpWInv P T K' α hα p s :=
  ((untwistRestrIso P T (K'.X p) α).inv.val.app (ovr hα)).hom.map_smul r s

/-- Z3.t: `cmpWInv ∘ cmpW = id`. -/
theorem cmpWInv_cmpW (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (p : ℤ)
    (s : P.FSec ⊤ (twFtop P T K') p (ovr (hα.trans le_top))) :
    cmpWInv P T K' α hα p (cmpW P T K' α hα p s) = s :=
  congrArg (fun k => (k.val.app (ovr hα)).hom s) (untwistRestrIso P T (K'.X p) α).hom_inv_id

/-- Z3.t: `cmpW ∘ cmpWInv = id`. -/
theorem cmpW_cmpWInv (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (p : ℤ)
    (s : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    cmpW P T K' α hα p (cmpWInv P T K' α hα p s) = s :=
  congrArg (fun k => (k.val.app (ovr hα)).hom s) (untwistRestrIso P T (K'.X p) α).inv_hom_id

/-- Z3.t: the component map on total modules over `W ≤ U_α`. -/
def cTotW (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) :
    P.TTot ⊤ (twFtop P T K') (ovr (hα.trans le_top)) →+
      P.TTot (T.U α) (twFα P T K' α) (ovr hα) :=
  totMapAlong (idW P (hα.trans le_top) hα) (cmpW P T K' α hα) (cmpW_smul P T K' α hα)

/-- Z3.t: the inverse of the component map on total modules over `W ≤ U_α`. -/
def cTotWInv (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) :
    P.TTot (T.U α) (twFα P T K' α) (ovr hα) →+
      P.TTot ⊤ (twFtop P T K') (ovr (hα.trans le_top)) :=
  totMapAlong (idW P hα (hα.trans le_top)) (cmpWInv P T K' α hα) (cmpWInv_smul P T K' α hα)

/-- Z3.t: `cTotWInv ∘ cTotW = id`. -/
theorem cTotWInv_cTotW (α : T.ι) {W : Opens X} (hα : W ≤ T.U α)
    (x : P.TTot ⊤ (twFtop P T K') (ovr (hα.trans le_top))) :
    cTotWInv P T K' α hα (cTotW P T K' α hα x) = x := by
  rw [cTotW, cTotWInv, totMapAlong_comp (idW P hα (hα.trans le_top))
    (idW P (hα.trans le_top) hα) (DgaHom.id (P.D.𝒜 (ovr (hα.trans le_top)).unop.left))
    (fun a => rfl) (cmpW P T K' α hα) (cmpWInv P T K' α hα) (fun p => AddMonoidHom.id _)
    (fun p y => cmpWInv_cmpW P T K' α hα p y) (cmpW_smul P T K' α hα)
    (cmpWInv_smul P T K' α hα) (fun p r y => rfl) x]
  exact totMapAlong_id _ (fun a => rfl) _ (fun p y => rfl) _ x

/-- Z3.t: `cTotW ∘ cTotWInv = id`. -/
theorem cTotW_cTotWInv (α : T.ι) {W : Opens X} (hα : W ≤ T.U α)
    (y : P.TTot (T.U α) (twFα P T K' α) (ovr hα)) :
    cTotW P T K' α hα (cTotWInv P T K' α hα y) = y := by
  rw [cTotW, cTotWInv, totMapAlong_comp (idW P (hα.trans le_top) hα)
    (idW P hα (hα.trans le_top)) (DgaHom.id (P.D.𝒜 (ovr hα).unop.left))
    (fun a => rfl) (cmpWInv P T K' α hα) (cmpW P T K' α hα) (fun p => AddMonoidHom.id _)
    (fun p z => cmpW_cmpWInv P T K' α hα p z) (cmpWInv_smul P T K' α hα)
    (cmpW_smul P T K' α hα) (fun p r z => rfl) y]
  exact totMapAlong_id _ (fun a => rfl) _ (fun p z => rfl) _ y

/-- Z3.t: restriction `W' ≤ W` of sections of `F` (over `Over ⊤`), as a morphism of the
over-site. -/
abbrev resF {W W' : Opens X} (hW : W ≤ ⊤) (hW' : W' ≤ W) :
    ovr hW ⟶ ovr (hW'.trans hW) :=
  (Over.homMk (homOfLE hW') : Over.mk (homOfLE (hW'.trans hW)) ⟶ Over.mk (homOfLE hW)).op

/-- Z3.t: `cmpW` commutes with restriction (naturality of `untwistRestrIso`). -/
theorem cmpW_res (α : T.ι) {W W' : Opens X} (hα : W ≤ T.U α) (hW' : W' ≤ W) (p : ℤ)
    (z : P.FSec ⊤ (twFtop P T K') p (ovr (hα.trans le_top))) :
    cmpW P T K' α (hW'.trans hα) p (P.fRes ⊤ (twFtop P T K') p (resF (hα.trans le_top) hW') z) =
      P.fRes (T.U α) (twFα P T K' α) p
        ((Over.homMk (homOfLE hW') : Over.mk (homOfLE (hW'.trans hα)) ⟶
          Over.mk (homOfLE hα)).op) (cmpW P T K' α hα p z) :=
  PresheafOfModules.naturality_apply (untwistRestrIso P T (K'.X p) α).hom.val
    (Over.homMk (homOfLE hW') : Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op z

/-- Z3.t: `cTotW` commutes with restriction. -/
theorem cTotW_tRes (α : T.ι) {W W' : Opens X} (hα : W ≤ T.U α) (hW' : W' ≤ W)
    (x : P.TTot ⊤ (twFtop P T K') (ovr (hα.trans le_top))) :
    cTotW P T K' α (hW'.trans hα) (P.tRes ⊤ (twFtop P T K') (resF (hα.trans le_top) hW') x) =
      P.tRes (T.U α) (twFα P T K' α) ((Over.homMk (homOfLE hW') :
        Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op) (cTotW P T K' α hα x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    simp only [PreResolvingData.tRes_apply, cTotW, totMapAlong_tmul]
    refine congrArg (Tot.tmul _ _ _) ?_
    induction e using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of p y =>
      simp only [famMap_of]
      exact congrArg (DirectSum.of _ p) (cmpW_res P T K' α hα hW' p y)
    | add x y hx hy => simp only [map_add, hx, hy]
  | hadd x y hx hy => simp only [map_add, hx, hy]

/-- Z3.t: the unit `u_αβ⁻¹|W ∈ 𝒜⁰(W)` relating the components `α` and `β` (`untwist_compat`). -/
def fuA (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) :
    ↥(P.D.𝒜 (ovr hβ).unop.left 0) :=
  (Units.val (unitRes P.A0 (le_inf hα hβ) (uInv P T α β)) : P.A0.obj.obj (op W))

/-- Z3.t: components of a section over `W ≤ U_α ⊓ U_β` of `F`:
`s_β = u_αβ⁻¹ · φ^B(s_α)` (`untwist_compat`). -/
theorem cmpW_compat (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (p : ℤ) (z : P.FSec ⊤ (twFtop P T K') p (ovr (hα.trans le_top))) :
    cmpW P T K' β hβ p z =
      fuA P T α β hα hβ • twGenφ P T K' α β hα hβ p (cmpW P T K' α hα p z) :=
  untwist_compat P T (K'.X p) α β hα hβ z

/-- Z3.t: the unit `u_αβ`, spelled over `P.D` (one spelling for instance search). -/
abbrev uP (α β : T.ι) : (↥(P.D.𝒜 (T.U α ⊓ T.U β) 0))ˣ := T.u α β

/-- Z3.t: `d(u_αβ⁻¹|W) = -u_αβ⁻¹|W (h⁰_β|W - h⁰_α|W)` (from `d_u`). -/
theorem d_fuA (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) :
    GCDga.d (𝒜 := P.D.𝒜 W) (Subtype.val (fuA P T α β hα hβ) : P.D.A W) =
      -((Subtype.val (fuA P T α β hα hβ) : P.D.A W) *
        (P.D.res hβ (T.h0 β) - P.D.res hα (T.h0 α))) := by
  have hvw : (Subtype.val (Units.val (uP P T α β)⁻¹) : P.D.A (T.U α ⊓ T.U β)) *
      (Subtype.val (Units.val (uP P T α β)) : P.D.A (T.U α ⊓ T.U β)) = 1 :=
    congrArg Subtype.val (Units.inv_mul (uP P T α β))
  have hv := d_inv_aux (𝒜 := P.D.𝒜 (T.U α ⊓ T.U β)) hvw
    (P.D.res inf_le_right (T.h0 β) - P.D.res inf_le_left (T.h0 α)) (T.d_u α β)
  have h1 := congrArg (P.D.res (le_inf hα hβ)) hv
  rw [(P.D.res (le_inf hα hβ)).map_d] at h1
  simp only [map_neg, map_mul] at h1
  erw [(P.D.res (le_inf hα hβ)).toAlgHom.map_sub, P.D.res_comp, P.D.res_comp] at h1
  exact h1

/-- Z3.t: `cTotW β = u⁻¹ · φ^T ∘ cTotW α` on total modules over `W ≤ U_α ⊓ U_β`. -/
theorem cTotW_compat (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (x : P.TTot ⊤ (twFtop P T K') (ovr (hα.trans le_top))) :
    cTotW P T K' β hβ x = (fuA P T α β hα hβ : P.D.A (ovr hβ).unop.left) •
      twTotφ P T K' α β hα hβ (cTotW P T K' α hα x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    simp only [cTotW, twTotφ, totMapAlong_tmul]
    have he : famMap (cmpW P T K' β hβ) e = fuA P T α β hα hβ •
        famMap (twGenφ P T K' α β hα hβ) (famMap (cmpW P T K' α hα) e) := by
      induction e using DirectSum.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | of p y =>
        simp only [famMap_of]
        rw [cmpW_compat P T K' α β hα hβ p y]
        exact (map_smul (DirectSum.lof ↥(P.D.𝒜 (ovr hβ).unop.left 0) ℤ
          (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p) (fuA P T α β hα hβ) _)
      | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    rw [he, Tot.tmul_smul0, Tot.smul_tmul]
    exact congrArg (Tot.tmul _ _ · _) (GCDga.central _ (fuA P T α β hα hβ).2 _).symm
  | hadd x y hx hy => simp only [map_add, hx, hy, smul_add]


end Cohesive
