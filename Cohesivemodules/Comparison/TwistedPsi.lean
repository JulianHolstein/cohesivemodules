import Cohesivemodules.Comparison.TwistedPsiAux
import Cohesivemodules.Comparison.TwistedFunctorDef
import Cohesivemodules.Comparison.SheafDataMap
import Cohesivemodules.Sheaf.Twisted.HomSectionsTw

set_option linter.style.header false

/-!
# Z3.s: `Ψ^tw : ℋ^h(M₁, M₂) ⟶ 𝓗om^tw(J_T M₁, J_T M₂)`

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F.2, F′ (i); [A, Prop 7.2.19, §7.4]). For sheaf
data `S`, a closed `h`, a twist datum `T` and cohesive modules `M₁, M₂` over `(𝒜(X), h)`:
* `ΨtwComp`: for `χ ∈ ℋ^{h,n}(W)` (the curved C3 copy, Z3.q) and `α`, the morphism
  `J_T(M₁)^p_α|(W ⊓ U_α) ⟶ J_T(M₂)^q_α|(W ⊓ U_α)` given on sections over `W' ≤ W ⊓ U_α` by C4's
  `extAlong (χ|W')` (`ΨW` over the curved data, Z3.s copy);
* `ΨtwSec`: these components form a compatible family (the gluing maps `u_αβ·` have degree `0`,
  `ΨW_smul0L`), a section of `glue(homTw(J_T(M₁)^p, J_T(M₂)^q))` over `W`;
* `ΨtwT`, `Ψtw`: the morphism of complexes of sheaves on `X`; it commutes with `δ` since on `U_α`
  the differentials are `𝕏 − h⁰_α` (`ΨW_homδ_gauge`);
* `Ψtw_top`: on global sections, `Ψ^tw` sends `F ∘ φ` for a closed degree-`0` `φ` to the cochain
  of `J_T(φ)` (`twHomTopEquiv`), the compatibility of C4 step 5.

## Deviations
* As C4: `ℋ^n(V)` is spelled as maps out of `Tot(M₁)` semilinear along `res_V` (C3).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite
open CochainComplex.HomComplex

/-- Z3.s (copy of C4 `totRes_extAlong` over `DgaSheafData`): `extAlong` commutes with `totRes`
when `χ' = totRes ∘ χ`. -/
private theorem totRes_extAlong_c {X : Type} [TopologicalSpace X] (S : DgaSheafData X)
    (M₁ M₂ : CohesiveModule S.𝒜X) (n : ℤ) {W W' : Opens X} (hW : W' ≤ W)
    (χ : HomAlong (S.D.res (le_top : W ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n)
    (χ' : HomAlong (S.D.res (le_top : W' ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n)
    (hχ : ∀ x, χ'.1 x = S.totRes M₂ le_top hW (χ.1 x)) (y : S.TotSec M₁ (le_top : W ≤ ⊤)) :
    S.totRes M₂ le_top hW (extAlong χ y) = extAlong χ' (S.totRes M₁ le_top hW y) := by
  have hsm₁ : ∀ (b : S.D.A W) (y : S.TotSec M₁ (le_top : W ≤ ⊤)),
      S.totRes M₁ le_top hW (b • y) = S.D.res hW b • S.totRes M₁ le_top hW y :=
    fun b y => bcTotRes_smul (S.D.res hW) (S.D.res le_top) (S.D.res le_top)
      (S.D.res_comp le_top hW) M₁.Q b y
  have hsm₂ : ∀ (b : S.D.A W) (y : S.TotSec M₂ (le_top : W ≤ ⊤)),
      S.totRes M₂ le_top hW (b • y) = S.D.res hW b • S.totRes M₂ le_top hW y :=
    fun b y => bcTotRes_smul (S.D.res hW) (S.D.res le_top) (S.D.res le_top)
      (S.D.res_comp le_top hW) M₂.Q b y
  have hz : ∀ (u : ℤˣ) (z : S.TotSec M₂ (le_top : W ≤ ⊤)),
      S.totRes M₂ le_top hW (u • z) = u • S.totRes M₂ le_top hW z := fun u z => by
    rw [Units.smul_def, Units.smul_def, map_zsmul]
  have hF : ∀ x : M₁.T, S.totRes M₁ le_top hW (bcF (S.D.res (le_top : W ≤ ⊤)) M₁.Q x) =
      bcF (S.D.res (le_top : W' ≤ ⊤)) M₁.Q x := fun x =>
    bcTotRes_bcF (S.D.res hW) (S.D.res le_top) (S.D.res le_top)
      (S.D.res_comp le_top hW) M₁.Q x
  have e1 : ∀ {p : ℤ} {b : S.D.A W}, b ∈ S.D.𝒜 W p → ∀ y : S.TotSec M₁ (le_top : W ≤ ⊤),
      extAlong χ (b • y) = (n * p).negOnePow • b • extAlong χ y :=
    fun hb y => (extAlong_mem χ).2 hb y
  have e2 : ∀ {p : ℤ} {b : S.D.A W'}, b ∈ S.D.𝒜 W' p → ∀ y : S.TotSec M₁ (le_top : W' ≤ ⊤),
      extAlong χ' (b • y) = (n * p).negOnePow • b • extAlong χ' y :=
    fun hb y => (extAlong_mem χ').2 hb y
  have e3 : ∀ x : M₁.T, extAlong χ (bcF (S.D.res (le_top : W ≤ ⊤)) M₁.Q x) = χ.1 x :=
    fun x => extAlong_bcF χ x
  have e4 : ∀ x : M₁.T, extAlong χ' (bcF (S.D.res (le_top : W' ≤ ⊤)) M₁.Q x) = χ'.1 x :=
    fun x => extAlong_bcF χ' x
  have key := bc_ext_semilinear (S.D.res hW) (S.D.res (le_top : W ≤ ⊤)) M₁.Q n
    (N := S.TotSec M₂ (le_top : W' ≤ ⊤))
    ((S.totRes M₂ le_top hW).comp (extAlong χ).toAddMonoidHom)
    ((extAlong χ').toAddMonoidHom.comp (S.totRes M₁ le_top hW))
    (fun {p b} hb (y : S.TotSec M₁ (le_top : W ≤ ⊤)) => by
      change S.totRes M₂ le_top hW (extAlong χ (b • y)) =
        (n * p).negOnePow • S.D.res hW b • S.totRes M₂ le_top hW (extAlong χ y)
      refine (congrArg (S.totRes M₂ le_top hW) (e1 hb y)).trans ((hz _ _).trans ?_)
      exact congrArg _ (hsm₂ b _))
    (fun {p b} hb (y : S.TotSec M₁ (le_top : W ≤ ⊤)) => by
      change extAlong χ' (S.totRes M₁ le_top hW (b • y)) =
        (n * p).negOnePow • S.D.res hW b • extAlong χ' (S.totRes M₁ le_top hW y)
      rw [hsm₁, e2 ((S.D.res hW).map_mem hb)])
    (fun x => by
      change S.totRes M₂ le_top hW (extAlong χ (bcF (S.D.res (le_top : W ≤ ⊤)) M₁.Q x)) =
        extAlong χ' (S.totRes M₁ le_top hW (bcF (S.D.res (le_top : W ≤ ⊤)) M₁.Q x))
      rw [e3, hF, e4, hχ])
  exact DFunLike.congr_fun key y

/-- Z3.s: `homAt` is additive in `χ`. -/
private theorem homAt_add {X : Type} [TopologicalSpace X] (S : DgaSheafData X)
    (M₁ M₂ : CohesiveModule S.𝒜X) (n : ℤ) {V W : Opens X} (hW : W ≤ V)
    (χ ψ : S.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) :
    S.homAt M₁ M₂ n hW (χ + ψ) = S.homAt M₁ M₂ n hW χ + S.homAt M₁ M₂ n hW ψ :=
  Subtype.ext (LinearMap.ext fun y => by
    change S.totRes M₂ (le_top : V ≤ ⊤) hW (χ.1 y + ψ.1 y) =
      S.totRes M₂ (le_top : V ≤ ⊤) hW (χ.1 y) + S.totRes M₂ (le_top : V ≤ ⊤) hW (ψ.1 y)
    exact map_add _ _ _)

/-- Z3.s: `ΨW` is additive in `χ` (as in C4 `ΨVAdd`). -/
private theorem ΨW_add {X : Type} [TopologicalSpace X] (S : DgaSheafData X)
    (M₁ M₂ : CohesiveModule S.𝒜X) (n : ℤ) (T : Triplet n) {V W : Opens X} (hW : W ≤ V)
    (χ ψ : S.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) (x : S.sheafOfSec M₁ T.p (le_top : W ≤ ⊤)) :
    S.ΨW M₁ M₂ n T hW (χ + ψ) x = S.ΨW M₁ M₂ n T hW χ x + S.ΨW M₁ M₂ n T hW ψ x := by
  apply Subtype.ext
  change extAlong (S.homAt M₁ M₂ n hW (χ + ψ)) x.1 =
    extAlong (S.homAt M₁ M₂ n hW χ) x.1 + extAlong (S.homAt M₁ M₂ n hW ψ) x.1
  rw [homAt_add]
  exact LinearMap.congr_fun (extAlong_add _ _) x.1

/-- Z3.s: `ΨW` is `O`-linear in `χ` (as in C4 `ΨT`): `Ψ(r χ) = r|W · Ψ(χ)`. -/
private theorem ΨW_smul_hom {X : Type} [TopologicalSpace X] (S : DgaSheafData X)
    (M₁ M₂ : CohesiveModule S.𝒜X) (n : ℤ) (T : Triplet n) {V W : Opens X} (hW : W ≤ V)
    (r : S.O.obj.obj (op V)) (χ : S.HomSec M₁ M₂ n (le_top : V ≤ ⊤))
    (x : S.sheafOfSec M₁ T.p (le_top : W ≤ ⊤)) :
    S.ΨW M₁ M₂ n T hW (r • χ) x = ((S.O.obj.map (homOfLE hW).op).hom r) •
      S.ΨW M₁ M₂ n T hW χ x := by
  apply Subtype.ext
  change extAlong (S.homAt M₁ M₂ n hW (r • χ)) x.1 =
    ((S.ρ W ((S.O.obj.map (homOfLE hW).op).hom r) : ↥(S.D.𝒜 W 0)) : S.D.A W) •
      extAlong (S.homAt M₁ M₂ n hW χ) x.1
  refine extAlong_smul0 (S.ρ W ((S.O.obj.map (homOfLE hW).op).hom r)) _ _
    (fun y => ?_) x.1
  change S.totRes M₂ (le_top : V ≤ ⊤) hW (S.ρ V r • χ.1 y) =
    ((S.ρ W ((S.O.obj.map (homOfLE hW).op).hom r) : ↥(S.D.𝒜 W 0)) : S.D.A W) •
      S.totRes M₂ (le_top : V ≤ ⊤) hW (χ.1 y)
  rw [S.totRes_smul0]
  exact congrArg (fun c : ↥(S.D.𝒜 W 0) => (c : S.D.A W) •
    S.totRes M₂ (le_top : V ≤ ⊤) hW (χ.1 y)) (S.ρ_natural hW r)

/-- Sections of a sum of morphisms of sheaves of modules. -/
private lemma sheaf_add_app' {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {A B : Mod R} (f g : A ⟶ B) (Z : Cᵒᵖ) (s : A.val.obj Z) :
    ((f + g).val.app Z).hom s = (f.val.app Z).hom s + (g.val.app Z).hom s := rfl

/-- Sections of a `ℤˣ`-multiple of a morphism of sheaves of modules. -/
private lemma sheaf_units_app' {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {A B : Mod R} (z : ℤˣ) (f : A ⟶ B) (Z : Cᵒᵖ)
    (s : A.val.obj Z) :
    ((z • f).val.app Z).hom s = z • (f.val.app Z).hom s := by
  have h : (SheafOfModules.evaluation.{0} R Z).map ((z : ℤ) • f) =
      (z : ℤ) • (SheafOfModules.evaluation.{0} R Z).map f := Functor.map_zsmul _
  rw [Units.smul_def, Units.smul_def]
  exact congrArg (fun g : A.val.obj Z ⟶ B.val.obj Z ↦ g.hom s) h

/-- Sections of `f ≫ (g + z • g')` for morphisms of sheaves of modules. -/
private lemma comp_add_units_app {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {A B D : Mod R} (f : A ⟶ B) (g g' : B ⟶ D) (z : ℤˣ) (Z : Cᵒᵖ)
    (s : A.val.obj Z) :
    ((f ≫ (g + z • g')).val.app Z).hom s = (g.val.app Z).hom ((f.val.app Z).hom s) +
      z • (g'.val.app Z).hom ((f.val.app Z).hom s) :=
  (sheaf_add_app' g (z • g') Z _).trans (congrArg _ (sheaf_units_app' z g' Z _))

/-- `secApp` of `a + z • b` for morphisms of restrictions. -/
private lemma secApp_add_units {X : Type} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} {U W : Opens X} (hW : W ≤ U)
    {P Q : Mod ((ringOf R).over U)}
    (a b : P.over (Over.mk (homOfLE hW)) ⟶ Q.over (Over.mk (homOfLE hW))) (z : ℤˣ)
    {W' : Opens X} (h' : W' ≤ W) (x : sec R P (h'.trans hW)) :
    secApp hW (a + z • b) h' x = secApp hW a h' x + z • secApp hW b h' x :=
  (sheaf_add_app' a (z • b) (ovr₂ hW h') x).trans
    (congrArg _ (sheaf_units_app' z b (ovr₂ hW h') x))

/-- `Pi.lift g` composed with a combination of two projections. -/
private lemma lift_comp_add_units {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {ι : Type} (F : ι → Mod R) {Y Z : Mod R} (g : ∀ i, Y ⟶ F i)
    (i j : ι) (a : F i ⟶ Z) (b : F j ⟶ Z) (z : ℤˣ) :
    Limits.Pi.lift g ≫ (Limits.Pi.π F i ≫ a + z • (Limits.Pi.π F j ≫ b)) =
      g i ≫ a + z • (g j ≫ b) := by
  rw [Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc, ← Category.assoc,
    Limits.Pi.lift_comp_π, Limits.Pi.lift_comp_π]

/-- Z3.s (copy of C4 `extAlong_homAt_top` over `DgaSheafData`): on `F ∘ φ`, `extAlong` is the
base change `bcHomL` of `φ`. -/
private theorem extAlong_homAt_top_c {X : Type} [TopologicalSpace X] (S : DgaSheafData X)
    (M₁ M₂ : CohesiveModule S.𝒜X) (φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive)
    {W : Opens X} :
    extAlong (S.homAt M₁ M₂ 0 (le_top : W ≤ ⊤) (S.homTop M₁ M₂ 0 (S.toHom0 φ))) =
      bcHomL (S.D.res (le_top : W ≤ ⊤)) 0 (S.toHom0 φ) := by
  refine (eq_extAlong _ (bcHomL_mem (S.D.res (le_top : W ≤ ⊤)) 0 (S.toHom0 φ)) fun x => ?_).symm
  have h1 : bcHomL (S.D.res (le_top : W ≤ ⊤)) 0 (S.toHom0 φ) (bcF (S.D.res le_top) M₁.Q x) =
      bcF (S.D.res (le_top : W ≤ ⊤)) M₂.Q (φ.1 x) := bcHomL_bcF _ 0 (S.toHom0 φ) x
  refine h1.trans ?_
  exact (bcTotRes_bcF (S.D.res (le_top : W ≤ ⊤)) (S.D.res (le_top : (⊤ : Opens X) ≤ ⊤))
    (S.D.res (le_top : W ≤ ⊤)) (S.D.res_comp le_top le_top) M₂.Q (φ.1 x)).symm

/-- Sections of `Pi.lift` followed by a projection. -/
private lemma lift_sections' {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {ι : Type} (F : ι → Mod R) {Y : Mod R} (g : ∀ i, Y ⟶ F i) (i : ι)
    (V : Cᵒᵖ) (s : Y.val.obj V) :
    ((Limits.Pi.π F i).val.app V).hom (((Limits.Pi.lift g).val.app V).hom s) =
      ((g i).val.app V).hom s :=
  congrArg (fun m : Y ⟶ F i => (m.val.app V).hom s) (Limits.Pi.lift_comp_π g i)

variable {X : Type} [TopologicalSpace X] {S : DgaSheafData X} {h : S.D.A ⊤}

namespace TwistDatum

variable (T : TwistDatum S h)

/-- Z3.s: the cocycle of a twist datum is normalized in the form `ȟ_αβα = 1` used by `homTw`. -/
theorem ch_aba (α β : T.ι) : T.ch α β α = 1 :=
  T.normalized α β α (Or.inr (Or.inr rfl))

variable (hh : h ∈ S.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0)
  (M₁ M₂ : CohesiveModule (S.withCurvature h hh hd).𝒜X)

/-- **Z3.s (F′ (i)).** The `α`-component of `Ψ^tw(χ)` for `χ ∈ ℋ^{h,n}(W)` in the factor
`p + n = q`: on sections over `W' ≤ W ⊓ U_α`, `x ↦ extAlong (χ|W') x` (`ΨW`). -/
def ΨtwComp (n : ℤ) (T' : Triplet n) {W : Opens X}
    (χ : (S.withCurvature h hh hd).HomSec M₁ M₂ n (le_top : W ≤ ⊤)) (α : T.ι) :
    ((T.twTerm hh hd M₁ T'.p).M α).over
        (Over.mk (homOfLE (inf_le_right : W ⊓ T.U α ≤ T.U α))) ⟶
      ((T.twTerm hh hd M₂ T'.q).M α).over
        (Over.mk (homOfLE (inf_le_right : W ⊓ T.U α ≤ T.U α))) :=
  secHomOf inf_le_right
    (fun {_} h' =>
      ((S.withCurvature h hh hd).ΨW M₁ M₂ n T' (h'.trans inf_le_left) χ).toAddMonoidHom)
    (fun h' r x => ((S.withCurvature h hh hd).ΨW M₁ M₂ n T' (h'.trans inf_le_left) χ).map_smul r x)
    (fun h' h'' x => by
      refine Subtype.ext ?_
      change extAlong ((S.withCurvature h hh hd).homAt M₁ M₂ n _ χ)
          ((S.withCurvature h hh hd).totRes M₁ le_top h'' x.1) =
        (S.withCurvature h hh hd).totRes M₂ le_top h''
          (extAlong ((S.withCurvature h hh hd).homAt M₁ M₂ n _ χ) x.1)
      exact (totRes_extAlong_c (S.withCurvature h hh hd) M₁ M₂ n h''
        ((S.withCurvature h hh hd).homAt M₁ M₂ n _ χ) ((S.withCurvature h hh hd).homAt M₁ M₂ n _ χ)
        (fun y => ((S.withCurvature h hh hd).totRes_comp M₂ (le_top : W ≤ ⊤)
          (h'.trans inf_le_left) h'' (χ.1 y)).symm) x.1).symm)

/-- Z3.s: `ΨtwComp` on sections is `ΨW` (rfl). -/
theorem secApp_ΨtwComp (n : ℤ) (T' : Triplet n) {W : Opens X}
    (χ : (S.withCurvature h hh hd).HomSec M₁ M₂ n (le_top : W ≤ ⊤)) (α : T.ι) {W' : Opens X}
    (h' : W' ≤ W ⊓ T.U α) (x : (S.withCurvature h hh hd).sheafOfSec M₁ T'.p (le_top : W' ≤ ⊤)) :
    secApp inf_le_right (T.ΨtwComp hh hd M₁ M₂ n T' χ α) h' x =
      (S.withCurvature h hh hd).ΨW M₁ M₂ n T' (h'.trans inf_le_left) χ x := rfl

/-- **Z3.s (F′ (i)).** The components `ΨtwComp` form a compatible family: a section of
`glue(homTw(J_T(M₁)^p, J_T(M₂)^q))` over `W` (`u_αβ` has degree `0`: `ΨW_smul0L`). -/
def ΨtwSec (n : ℤ) (T' : Triplet n) {W : Opens X}
    (χ : (S.withCurvature h hh hd).HomSec M₁ M₂ n (le_top : W ≤ ⊤)) :
    glueSub (homTw T.ch_aba (T.twTerm hh hd M₁ T'.p) (T.twTerm hh hd M₂ T'.q)) W :=
  ⟨fun α => T.ΨtwComp hh hd M₁ M₂ n T' χ α, by
    refine mem_glueSub.2 ?_
    intro α β W' h' hα hβ
    refine secHom_ext hβ fun h'' x => ?_
    change (T.twTerm hh hd M₂ T'.q).φ α β (h''.trans hα) (h''.trans hβ)
        ((S.withCurvature h hh hd).ΨW M₁ M₂ n T' _ χ
          ((T.twTerm hh hd M₁ T'.p).φ β α (h''.trans hβ) (h''.trans hα) x)) =
      (S.withCurvature h hh hd).ΨW M₁ M₂ n T' _ χ x
    have hs := TwMod.φ_symm T.ch_aba (T.twTerm hh hd M₁ T'.p) β α (h''.trans hβ)
      (h''.trans hα) x
    refine Eq.trans ?_ (congrArg ((S.withCurvature h hh hd).ΨW M₁ M₂ n T' _ χ) hs)
    exact ((S.withCurvature h hh hd).ΨW_smul0L M₁ M₂ n T' _ χ _ _).symm⟩

/-- **Z3.s (F′ (i)).** `Ψ^tw` in degree `n` and factor `p + n = q`:
`ℋ^{h,n} ⟶ glue(homTw(J_T(M₁)^p, J_T(M₂)^q))`, `χ ↦ ΨtwSec χ` on sections. -/
def ΨtwT (n : ℤ) (T' : Triplet n) :
    (S.withCurvature h hh hd).homSh M₁ M₂ n ⟶
      (glue S.O T.U).obj (homTw T.ch_aba (T.twTerm hh hd M₁ T'.p) (T.twTerm hh hd M₂ T'.q)) where
  val :=
    { app := fun W => ModuleCat.ofHom
        { toFun := fun χ => T.ΨtwSec hh hd M₁ M₂ n T' (W := W.unop) χ
          map_add' := fun χ ψ => by
            refine Subtype.ext (funext fun α => secHom_ext inf_le_right fun h' x => ?_)
            exact ΨW_add (S.withCurvature h hh hd) M₁ M₂ n T' _ χ ψ x
          map_smul' := fun r χ => by
            refine Subtype.ext (funext fun α => secHom_ext inf_le_right fun h' x => ?_)
            refine (ΨW_smul_hom (S.withCurvature h hh hd) M₁ M₂ n T' _ r χ x).trans ?_
            have e : ((S.O.obj.map (homOfLE (h'.trans inf_le_left)).op).hom r) =
                (S.O.obj.map (homOfLE h').op).hom
                  ((S.O.obj.map (homOfLE inf_le_left).op).hom r) := by
              rw [← CommRingCat.comp_apply, ← Functor.map_comp]
              rfl
            erw [e]
            rfl }
      naturality := fun {W W'} f => by
        apply ModuleCat.hom_ext
        refine DFunLike.ext _ _ fun χ => ?_
        refine Subtype.ext (funext fun α => secHom_ext inf_le_right fun h' x => ?_)
        change (S.withCurvature h hh hd).ΨW M₁ M₂ n T' _
            ((S.withCurvature h hh hd).homRes M₁ M₂ n le_top (leOfHom f.unop) χ) x =
          (S.withCurvature h hh hd).ΨW M₁ M₂ n T' _ χ x
        refine Subtype.ext ?_
        change extAlong ((S.withCurvature h hh hd).homAt M₁ M₂ n _
            ((S.withCurvature h hh hd).homRes M₁ M₂ n le_top (leOfHom f.unop) χ)) x.1 =
          extAlong ((S.withCurvature h hh hd).homAt M₁ M₂ n _ χ) x.1
        refine congrArg (fun φ => extAlong φ x.1) (Subtype.ext (LinearMap.ext fun y => ?_))
        exact (S.withCurvature h hh hd).totRes_comp M₂ (le_top : unop W ≤ ⊤) (leOfHom f.unop)
          _ (χ.1 y) }

/-- Z3.s: `ΨtwT` on sections (rfl). -/
theorem ΨtwT_app (n : ℤ) (T' : Triplet n) (W : Opens X)
    (χ : (S.withCurvature h hh hd).HomSec M₁ M₂ n (le_top : W ≤ ⊤)) :
    ((T.ΨtwT hh hd M₁ M₂ n T').val.app (op W)).hom χ = T.ΨtwSec hh hd M₁ M₂ n T' χ := rfl

/-- Z3.s: `Ψ^tw` commutes with the differentials in the factor `(p, p + n + 1)`: the
`ΨW_homδ_gauge` identity, sheaf-theoretically. -/
private theorem ΨtwT_comm (n p : ℤ) (hpq : p + (n + 1) = p + n + 1) :
    T.ΨtwT hh hd M₁ M₂ n ⟨p, p + n, rfl⟩ ≫ (glue S.O T.U).map
        (homTwPost T.ch_aba ((T.twistedSheafOf hh hd M₁).X p)
          ((T.twistedSheafOf hh hd M₂).d (p + n) (p + n + 1))) +
      (n + 1).negOnePow • (T.ΨtwT hh hd M₁ M₂ n ⟨p + 1, p + n + 1, by lia⟩ ≫ (glue S.O T.U).map
        (homTwPre T.ch_aba ((T.twistedSheafOf hh hd M₁).d p (p + 1))
          ((T.twistedSheafOf hh hd M₂).X (p + n + 1)))) =
    (S.withCurvature h hh hd).homD M₁ M₂ n ≫ T.ΨtwT hh hd M₁ M₂ (n + 1) ⟨p, p + n + 1, hpq⟩ := by
  have e2 : ∀ (M : CohesiveModule (S.withCurvature h hh hd).𝒜X) (i : ℤ),
      (T.twistedSheafOf hh hd M).d i (i + 1) = T.twDiff hh hd M i :=
    fun M i => CochainComplex.of_d _ _ i
  rw [e2 M₂ (p + n), e2 M₁ p]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun χ => ?_
  refine Subtype.ext (funext fun α => secHom_ext inf_le_right fun h' x => ?_)
  rw [sheaf_add_app', sheaf_units_app']
  refine (secApp_add_units inf_le_right _ _ _ h' x).trans ?_
  have key := (S.withCurvature h hh hd).ΨW_homδ_gauge M₁ M₂ n ⟨p, p + n + 1, hpq⟩
    (h'.trans inf_le_left) χ (S.D.res (h'.trans inf_le_right) (T.h0 α))
    ((S.D.res (h'.trans inf_le_right)).map_mem (T.h0_mem α)) x
  refine Subtype.ext (Eq.trans ?_ key.symm)
  rfl

/-- Z3.s: `Ψ^tw` commutes with the differentials, in degree `n` (as C4 `Ψ_comm`). -/
private theorem Ψtw_comm (n : ℤ) :
    (Limits.Pi.lift fun T' : Triplet n ↦ T.ΨtwT hh hd M₁ M₂ n T') ≫
        twHomD T.ch_aba (T.twistedSheafOf hh hd M₁) (T.twistedSheafOf hh hd M₂) n =
      (S.withCurvature h hh hd).homD M₁ M₂ n ≫
        Limits.Pi.lift fun T' : Triplet (n + 1) ↦ T.ΨtwT hh hd M₁ M₂ (n + 1) T' := by
  refine Limits.Pi.hom_ext _ _ fun T' => ?_
  obtain ⟨p, q, hpq⟩ := T'
  obtain rfl : q = p + n + 1 := by lia
  have hp : twHomD T.ch_aba (T.twistedSheafOf hh hd M₁) (T.twistedSheafOf hh hd M₂) n ≫
      Pi.π (fun t : Triplet (n + 1) ↦ (glue S.O T.U).obj (homTw T.ch_aba
        ((T.twistedSheafOf hh hd M₁).X t.p) ((T.twistedSheafOf hh hd M₂).X t.q)))
        ⟨p, p + n + 1, hpq⟩ =
      Pi.π (fun t : Triplet n ↦ (glue S.O T.U).obj (homTw T.ch_aba
          ((T.twistedSheafOf hh hd M₁).X t.p) ((T.twistedSheafOf hh hd M₂).X t.q)))
          ⟨p, p + n, rfl⟩ ≫
          (glue S.O T.U).map (homTwPost T.ch_aba ((T.twistedSheafOf hh hd M₁).X p)
            ((T.twistedSheafOf hh hd M₂).d (p + n) (p + n + 1))) +
        (n + 1).negOnePow •
          (Pi.π (fun t : Triplet n ↦ (glue S.O T.U).obj (homTw T.ch_aba
              ((T.twistedSheafOf hh hd M₁).X t.p) ((T.twistedSheafOf hh hd M₂).X t.q)))
              ⟨p + 1, p + n + 1, by lia⟩ ≫
            (glue S.O T.U).map (homTwPre T.ch_aba ((T.twistedSheafOf hh hd M₁).d p (p + 1))
              ((T.twistedSheafOf hh hd M₂).X (p + n + 1)))) :=
    Pi.lift_comp_π _ _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun z => (Limits.Pi.lift fun T' : Triplet n ↦ T.ΨtwT hh hd M₁ M₂ n T') ≫ z)
    hp).trans ?_
  refine (lift_comp_add_units _ _ _ _ _ _ _).trans ?_
  refine (T.ΨtwT_comm hh hd M₁ M₂ n p hpq).trans ?_
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun z => (S.withCurvature h hh hd).homD M₁ M₂ n ≫ z)
      (Limits.Pi.lift_comp_π _ _))).symm

/-- **Z3.s (F′ (i)).** [A, Prop 7.2.19, §7.4]. `Ψ^tw : ℋ^h(M₁, M₂) ⟶ 𝓗om^tw(J_T M₁, J_T M₂)`,
termwise `ΨtwT`; a morphism of complexes (`ΨW_homδ_gauge`: the differentials of `J_T` are
`𝕏 − h⁰_α` on `U_α`). -/
def Ψtw : (S.withCurvature h hh hd).ℋ M₁ M₂ ⟶
    twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) (T.twistedSheafOf hh hd M₂) T.iSup_eq where
  f n := Limits.Pi.lift fun T' : Triplet n => T.ΨtwT hh hd M₁ M₂ n T'
  comm' := by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have h1 : (twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) (T.twistedSheafOf hh hd M₂)
        T.iSup_eq).d i (i + 1) =
        twHomD T.ch_aba (T.twistedSheafOf hh hd M₁) (T.twistedSheafOf hh hd M₂) i :=
      twHomComplex_d _ _ _ _ i
    have h2 : ((S.withCurvature h hh hd).ℋ M₁ M₂).d i (i + 1) =
        (S.withCurvature h hh hd).homD M₁ M₂ i := CochainComplex.of_d _ _ i
    rw [h1, h2]
    exact T.Ψtw_comm hh hd M₁ M₂ i

/-- **Z3.s (C4 step 5 compatibility).** At `X`, `Ψ^tw` sends `F ∘ φ` for a closed degree-`0`
`φ` to the cochain of `J_T(φ)` (through `twHomTopEquiv`, F′ (e)). -/
theorem Ψtw_top (φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive) :
    twHomTopEquiv T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) (T.twistedSheafOf hh hd M₂) 0
        (((T.Ψtw hh hd M₁ M₂).f 0).val.app (op ⊤)
          ((S.withCurvature h hh hd).homTop M₁ M₂ 0 ((S.withCurvature h hh hd).toHom0 φ))) =
      Cochain.ofHom (T.twMap hh hd φ) := by
  funext t
  obtain ⟨p, q, hpq⟩ := t
  obtain rfl : q = p := by lia
  rw [twHomTopEquiv_apply]
  refine Eq.trans (congrArg (glueHomTwTopEquiv _ _ _)
    (lift_sections' _ (fun T' : Triplet 0 ↦ T.ΨtwT hh hd M₁ M₂ 0 T') ⟨q, q, hpq⟩ (op ⊤) _)) ?_
  change glueTopHom _ _ _ _ = (T.twMap hh hd φ).f q
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext m
  refine Subtype.ext ?_
  exact LinearMap.congr_fun (extAlong_homAt_top_c (S.withCurvature h hh hd) M₁ M₂ φ) m.1

end TwistDatum

end Cohesive
