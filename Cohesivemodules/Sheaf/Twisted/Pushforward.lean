import Cohesivemodules.Sheaf.Twisted.SecRes
import Cohesivemodules.Sheaf.Twisted.CocycleBasic
import Cohesivemodules.Sheaf.Twisted.Def

set_option linter.style.header false

/-!
# Z3.i: Toda's twisted pushforward

Blueprint item Z3.i (`blueprint/blueprint-tw.md` §3 C.4′(b)–(d); prototype P20). For a twist
cocycle `T` and a sheaf of modules `N` on `Over U_α`, the twisted sheaf `push T α N`:
* `pbo U α W`: the open `W ∩ U_α`, as Mathlib's chosen pullback in `Opens X` (equal to `W ⊓ U_α`,
  not definitionally);
* `jstar U α N`: the pushforward of `N` to `X` (`SheafOfModules.overPullback`); its sections over
  `W` are sections of `N` over `pbo U α W` (P20, `rfl`);
* `pushComp U α N β`: its restriction to `U_β`. Sections over `W ≤ U_β` are `N(pbo U α W)` for
  every `β` (definitionally; this is why one pushes to `X` first);
* gluing `pushGlue`: multiplication by `ȟ_αβγ|pbo U α W`;
* `push T α`, a functor `Mod (R.over U_α) ⥤ TwMod R T.U T.ch`; `pushCounit`: the counit
  `(push N)_α ⟶ N`, restriction along `W ≤ pbo U α W`.

## Deviations
[Toda, §4.3], [A, Lemma 7.1.6] use `W ↦ N(W ∩ U_α)` directly; here `W ∩ U_α` is the chosen
pullback (Mathlib's `overPullback`), and the cover is finite with a normalized cocycle.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}

section pbo

variable {ι : Type} (U : ι → Opens X)

/-- **Z3.i.** The open `W ∩ U_α`, as the chosen pullback of `W ⟶ ⊤ ⟵ U_α` in `Opens X`. -/
abbrev pbo (α : ι) (W : Opens X) : Opens X :=
  pullback (homOfLE (le_top : W ≤ ⊤)) (homOfLE (le_top : U α ≤ ⊤))

/-- Z3.i: `W ∩ U_α ≤ U_α`. -/
theorem pbo_le_left (α : ι) (W : Opens X) : pbo U α W ≤ U α := leOfHom (pullback.snd _ _)

/-- Z3.i: `W ∩ U_α ≤ W`. -/
theorem pbo_le (α : ι) (W : Opens X) : pbo U α W ≤ W := leOfHom (pullback.fst _ _)

/-- Z3.i: `W ⊓ U_α ≤ W ∩ U_α`. -/
theorem inf_le_pbo (α : ι) (W : Opens X) : W ⊓ U α ≤ pbo U α W :=
  leOfHom (pullback.lift (homOfLE inf_le_left) (homOfLE inf_le_right) (Subsingleton.elim _ _))

/-- Z3.i: `W ≤ W ∩ U_α` if `W ≤ U_α`. -/
theorem le_pbo {α : ι} {W : Opens X} (h : W ≤ U α) : W ≤ pbo U α W :=
  (le_inf le_rfl h).trans (inf_le_pbo U α W)

/-- Z3.i: `W ∩ U_α` is monotone in `W`. -/
theorem pbo_mono (α : ι) {W W' : Opens X} (h : W' ≤ W) : pbo U α W' ≤ pbo U α W :=
  (le_inf ((pbo_le U α W').trans h) (pbo_le_left U α W')).trans (inf_le_pbo U α W)

/-- Z3.i: `W ∩ U_α ≤ U_α ⊓ U_β ⊓ U_γ` if `W ≤ U_β, U_γ`. -/
theorem pbo_le_three (α : ι) {β γ : ι} {W : Opens X} (hβ : W ≤ U β) (hγ : W ≤ U γ) :
    pbo U α W ≤ U α ⊓ U β ⊓ U γ :=
  le_inf (le_inf (pbo_le_left U α W) ((pbo_le U α W).trans hβ)) ((pbo_le U α W).trans hγ)

end pbo

variable (R) {ι : Type} (U : ι → Opens X)

/-- **Z3.i.** The pushforward of `N` on `Over U_α` to `X` (`overPullback` along `U_α ≤ ⊤`). -/
abbrev jstar (α : ι) (N : Mod ((ringOf R).over (U α))) : Mod ((ringOf R).over ⊤) :=
  (SheafOfModules.overPullback.{0} (ringOf R) (homOfLE (le_top : U α ≤ ⊤))).obj N

/-- **Z3.i.** The `β`-component of the twisted pushforward: `jstar U α N` restricted to `U_β`. -/
abbrev pushComp (α : ι) (N : Mod ((ringOf R).over (U α))) (β : ι) :
    Mod ((ringOf R).over (U β)) :=
  (restrOver (ringOf R) (le_top : U β ≤ ⊤)).obj (jstar R U α N)

variable {R U}

/-- Z3.i: `r ∈ R(W)` acts on sections of `pushComp` by `r|W ∩ U_α` on sections of `N` (rfl, P20).
-/
theorem pushComp_smul (α : ι) (N : Mod ((ringOf R).over (U α))) {β : ι} {W : Opens X}
    (hW : W ≤ U β) (r : R.obj.obj (op W)) (x : sec R (pushComp R U α N β) hW) :
    (show (sec R N (pbo_le_left U α W) : Type) from toSec R hW r • x) =
      toSec R (pbo_le_left U α W) ((R.obj.map (homOfLE (pbo_le U α W)).op).hom r) •
        (show (sec R N (pbo_le_left U α W) : Type) from x) := rfl

/-- Z3.i: restriction of sections of `pushComp` is restriction in `N` along
`W' ∩ U_α ≤ W ∩ U_α` (rfl, P20). -/
theorem pushComp_res (α : ι) (N : Mod ((ringOf R).over (U α))) {β : ι} {W W' : Opens X}
    (hW : W ≤ U β) (h' : W' ≤ W) (x : sec R (pushComp R U α N β) hW) :
    (show (sec R N (pbo_le_left U α W') : Type) from secRes R (pushComp R U α N β) hW h' x) =
      secRes R N (pbo_le_left U α W) (pbo_mono U α h')
        (show (sec R N (pbo_le_left U α W) : Type) from x) := rfl

variable (ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ)

/-- **Z3.i.** The gluing maps of the twisted pushforward: on sections over `W ≤ U_β ⊓ U_γ`
(sections of `N` over `W ∩ U_α`), multiplication by `ȟ_αβγ|W ∩ U_α`. -/
def pushGlue (α : ι) (N : Mod ((ringOf R).over (U α))) (β γ : ι) {W : Opens X} (hβ : W ≤ U β)
    (hγ : W ≤ U γ) : sec R (pushComp R U α N β) hβ →+ sec R (pushComp R U α N γ) hγ :=
  DistribSMul.toAddMonoidHom (sec R N (pbo_le_left U α W))
    (toSec R (pbo_le_left U α W)
      (unitRes R (pbo_le_three U α hβ hγ) (ch α β γ) : R.obj.obj (op (pbo U α W))))

/-- Z3.i: `pushGlue` is multiplication by the restricted unit (rfl). -/
theorem pushGlue_apply (α : ι) (N : Mod ((ringOf R).over (U α))) (β γ : ι) {W : Opens X}
    (hβ : W ≤ U β) (hγ : W ≤ U γ) (x : sec R (pushComp R U α N β) hβ) :
    (show (sec R N (pbo_le_left U α W) : Type) from pushGlue ch α N β γ hβ hγ x) =
      toSec R (pbo_le_left U α W)
        (unitRes R (pbo_le_three U α hβ hγ) (ch α β γ) : R.obj.obj (op (pbo U α W))) •
        (show (sec R N (pbo_le_left U α W) : Type) from x) := rfl

/-- Z3.i: scalars of `R(W)` commute on sections over `W ≤ V`. -/
private theorem toSec_smul_comm {V : Opens X} (N : Mod ((ringOf R).over V)) {W : Opens X}
    (h : W ≤ V) (a b : R.obj.obj (op W)) (y : sec R N h) :
    toSec R h a • toSec R h b • y = toSec R h b • toSec R h a • y := by
  rw [← mul_smul, ← mul_smul]
  exact congrArg (· • y) (mul_comm a b)

/-- Z3.i: `pushGlue` is `R(W)`-linear (commutativity of `R(W ∩ U_α)`). -/
theorem pushGlue_smul (α : ι) (N : Mod ((ringOf R).over (U α))) (β γ : ι) {W : Opens X}
    (hβ : W ≤ U β) (hγ : W ≤ U γ) (r : R.obj.obj (op W)) (x : sec R (pushComp R U α N β) hβ) :
    pushGlue ch α N β γ hβ hγ (toSec R hβ r • x) = toSec R hγ r • pushGlue ch α N β γ hβ hγ x :=
  toSec_smul_comm N (pbo_le_left U α W) _ _ _

/-- Z3.i: `pushGlue` is natural in `W` (restriction of units). -/
theorem pushGlue_res (α : ι) (N : Mod ((ringOf R).over (U α))) (β γ : ι) {W W' : Opens X}
    (hβ : W ≤ U β) (hγ : W ≤ U γ) (h' : W' ≤ W) (x : sec R (pushComp R U α N β) hβ) :
    pushGlue ch α N β γ (h'.trans hβ) (h'.trans hγ) (secRes R (pushComp R U α N β) hβ h' x) =
      secRes R (pushComp R U α N γ) hγ h' (pushGlue ch α N β γ hβ hγ x) := by
  have e := secRes_smul N (pbo_le_left U α W) (pbo_mono U α h')
    (unitRes R (pbo_le_three U α hβ hγ) (ch α β γ) : R.obj.obj (op (pbo U α W)))
    (show (sec R N (pbo_le_left U α W) : Type) from x)
  rw [unitRes_res] at e
  exact e.symm

variable (T : TwistCocycle R)

/-- Z3.i: `pushGlue` is the identity for `β = γ` (`ȟ_αββ = 1`). -/
theorem pushGlue_self (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) (β : T.ι) {W : Opens X}
    (hβ : W ≤ T.U β) (x : sec R (pushComp R T.U α N β) hβ) :
    pushGlue T.ch α N β β hβ hβ x = x := by
  have h1 := T.unitRes_normalized (Or.inr (Or.inl rfl)) (pbo_le_three T.U α hβ hβ)
  change toSec R (pbo_le_left T.U α W) (unitRes R (pbo_le_three T.U α hβ hβ) (T.ch α β β) :
    R.obj.obj (op (pbo T.U α W))) • (show (sec R N (pbo_le_left T.U α W) : Type) from x) = _
  rw [h1, Units.val_one]
  exact one_smul _ _

/-- Z3.i: the twisted cocycle for `pushGlue` (Čech cocycle at `(α, β, γ, δ)`):
`φ_γδ φ_βγ = ȟ_βγδ φ_βδ`. -/
theorem pushGlue_cocycle (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) (β γ δ : T.ι)
    {W : Opens X} (hβ : W ≤ T.U β) (hγ : W ≤ T.U γ) (hδ : W ≤ T.U δ)
    (x : sec R (pushComp R T.U α N β) hβ) :
    pushGlue T.ch α N γ δ hγ hδ (pushGlue T.ch α N β γ hβ hγ x) =
      toSec R hδ (unitRes R (le_inf (le_inf hβ hγ) hδ) (T.ch β γ δ) : R.obj.obj (op W)) •
        pushGlue T.ch α N β δ hβ hδ x := by
  have hc := congrArg Units.val (T.unitRes_cocycle α β γ δ (pbo_le_left T.U α W)
    ((pbo_le T.U α W).trans hβ) ((pbo_le T.U α W).trans hγ) ((pbo_le T.U α W).trans hδ))
  simp only [Units.val_mul] at hc
  have e := pushComp_smul α N hδ
    (unitRes R (le_inf (le_inf hβ hγ) hδ) (T.ch β γ δ) : R.obj.obj (op W))
    (pushGlue T.ch α N β δ hβ hδ x)
  rw [unitRes_res] at e
  refine Eq.trans ?_ e.symm
  change toSec R (pbo_le_left T.U α W) _ • toSec R (pbo_le_left T.U α W) _ •
    (show (sec R N (pbo_le_left T.U α W) : Type) from x) =
      toSec R (pbo_le_left T.U α W) _ • toSec R (pbo_le_left T.U α W) _ •
        (show (sec R N (pbo_le_left T.U α W) : Type) from x)
  rw [← mul_smul, ← mul_smul]
  exact congrArg (fun a : R.obj.obj (op (pbo T.U α W)) =>
    toSec R (pbo_le_left T.U α W) a •
      (show (sec R N (pbo_le_left T.U α W) : Type) from x)) hc.symm

/-- **Z3.i.** [Toda, §4.3], [A, Lemma 7.1.6], blueprint-tw C.4′(c). The twisted pushforward of
`N` on `Over U_α`: components `pushComp T.U α N β` (sections over `W ≤ U_β` are `N(W ∩ U_α)`),
gluing maps multiplication by `ȟ_αβγ`. -/
def pushObj (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) : TwMod R T.U T.ch where
  M β := pushComp R T.U α N β
  φ β γ _ hβ hγ := pushGlue T.ch α N β γ hβ hγ
  φ_smul β γ _ hβ hγ r x := pushGlue_smul T.ch α N β γ hβ hγ r x
  φ_res β γ _ _ hβ hγ h' x := pushGlue_res T.ch α N β γ hβ hγ h' x
  φ_self β _ hβ x := pushGlue_self T α N β hβ x
  cocycle β γ δ _ hβ hγ hδ x := pushGlue_cocycle T α N β γ δ hβ hγ hδ x

/-- Z3.i: the twisted pushforward of a morphism: components `restrOver (jstar k)`. -/
def pushMap (α : T.ι) {N N' : Mod ((ringOf R).over (T.U α))} (k : N ⟶ N') :
    pushObj T α N ⟶ pushObj T α N' where
  f β := (restrOver (ringOf R) (le_top : T.U β ≤ ⊤)).map
    ((SheafOfModules.overPullback.{0} (ringOf R) (homOfLE (le_top : T.U α ≤ ⊤))).map k)
  comm β γ W hβ hγ x :=
    (app_smul k (pbo_le_left T.U α W)
      (unitRes R (pbo_le_three T.U α hβ hγ) (T.ch α β γ) : R.obj.obj (op (pbo T.U α W)))
      (show (sec R N (pbo_le_left T.U α W) : Type) from x)).symm

/-- Z3.i: restricting `r ∈ R(W)` to `W ∩ U_α` and back to `W` (`W ≤ U_α`) gives `r`. -/
private theorem res_res_le_pbo (α : ι) {W : Opens X} (hW : W ≤ U α) (r : R.obj.obj (op W)) :
    (R.obj.map (homOfLE (le_pbo U hW)).op).hom
      ((R.obj.map (homOfLE (pbo_le U α W)).op).hom r) = r := by
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  have e : (homOfLE (pbo_le U α W)).op ≫ (homOfLE (le_pbo U hW)).op = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id]
  rfl

/-- Z3.i: sections of `pushMap k` are sections of `k` over `W ∩ U_α` (rfl). -/
theorem pushMap_app (α : T.ι) {N N' : Mod ((ringOf R).over (T.U α))} (k : N ⟶ N') (β : T.ι)
    {W : Opens X} (hW : W ≤ T.U β) (x : sec R (pushComp R T.U α N β) hW) :
    (show (sec R N' (pbo_le_left T.U α W) : Type) from
      (((pushMap T α k).f β).val.app (ovr hW)).hom x) =
      (k.val.app (ovr (pbo_le_left T.U α W))).hom
        (show (sec R N (pbo_le_left T.U α W) : Type) from x) := rfl

/-- **Z3.i.** [Toda, §4.3]. The twisted pushforward functor `Mod (R.over U_α) ⥤ TwMod R T.U T.ch`.
-/
def push (α : T.ι) : Mod ((ringOf R).over (T.U α)) ⥤ TwMod R T.U T.ch where
  obj := pushObj T α
  map := pushMap T α
  map_id N := by
    refine TwMod.hom_ext fun β => ?_
    change (restrOver (ringOf R) (le_top : T.U β ≤ ⊤)).map
      ((SheafOfModules.overPullback.{0} (ringOf R)
        (homOfLE (le_top : T.U α ≤ ⊤))).map (𝟙 N)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  map_comp k k' := by
    refine TwMod.hom_ext fun β => ?_
    change (restrOver (ringOf R) (le_top : T.U β ≤ ⊤)).map
      ((SheafOfModules.overPullback.{0} (ringOf R) (homOfLE (le_top : T.U α ≤ ⊤))).map
        (k ≫ k')) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl

/-- **Z3.i.** The counit `(push N)_α ⟶ N`: on sections over `W ≤ U_α`, restriction along
`W ≤ W ∩ U_α`. -/
def pushCounit (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) : (pushObj T α N).M α ⟶ N :=
  homOfSec₀ (fun hW => secResHom R N (pbo_le_left T.U α _) (le_pbo T.U hW))
    (fun {W} hW r x => by
      have e := secRes_smul N (pbo_le_left T.U α W) (le_pbo T.U hW)
        ((R.obj.map (homOfLE (pbo_le T.U α W)).op).hom r)
        (show (sec R N (pbo_le_left T.U α W) : Type) from x)
      rw [res_res_le_pbo α hW r] at e
      exact e)
    (fun {W W'} hW h' x => by
      exact (secRes_secRes N (pbo_le_left T.U α W) (pbo_mono T.U α h')
        (le_pbo T.U (h'.trans hW))
        (show (sec R N (pbo_le_left T.U α W) : Type) from x)).trans
        (secRes_secRes N (pbo_le_left T.U α W) (le_pbo T.U hW) h'
          (show (sec R N (pbo_le_left T.U α W) : Type) from x)).symm)

/-- Z3.i: sections of the counit (rfl). -/
theorem pushCounit_app (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) {W : Opens X}
    (hW : W ≤ T.U α) (x : sec R (pushComp R T.U α N α) hW) :
    ((pushCounit T α N).val.app (ovr hW)).hom x =
      secRes R N (pbo_le_left T.U α W) (le_pbo T.U hW)
        (show (sec R N (pbo_le_left T.U α W) : Type) from x) := rfl

/-- Z3.i: the counit is natural. -/
theorem pushCounit_naturality (α : T.ι) {N N' : Mod ((ringOf R).over (T.U α))} (k : N ⟶ N') :
    (pushMap T α k).f α ≫ pushCounit T α N' = pushCounit T α N ≫ k := by
  ext Y x
  exact (app_secRes k (pbo_le_left T.U α Y.unop.left) (le_pbo T.U (leOfHom Y.unop.hom))
    (show (sec R N (pbo_le_left T.U α Y.unop.left) : Type) from x)).symm

end Cohesive
