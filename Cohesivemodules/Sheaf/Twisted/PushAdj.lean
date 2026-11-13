import Cohesivemodules.Sheaf.Twisted.Pushforward

set_option linter.style.header false

/-!
# Z3.i: the component functor is left adjoint to the twisted pushforward

Blueprint item Z3.i (`blueprint/blueprint-tw.md` §3 C.4′(e)). For a twist cocycle `T`:
`Hom(M, push T α N) ≃ Hom(M_α, N)`, `F ↦ F_α ≫ ε_N`, with inverse `pushLift g`,
`(pushLift g)_β (x) = g(φ_βα(x|W ∩ U_α))` for `x ∈ M_β(W)`. `pushLift g` commutes with the gluing
by the cocycle and cyclic symmetry of `ȟ`. Hence `TwMod.comp α ⊣ push T α`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  (T : TwistCocycle R)

/-- **Z3.i.** The section maps of `pushLift g` on `M_β`: `x ↦ g(φ_βα(x|W ∩ U_α))`, a section of
`N` over `W ∩ U_α`, i.e. of `(push N)_β` over `W`. -/
def pushLiftFam (α : T.ι) {M : TwMod R T.U T.ch} {N : Mod ((ringOf R).over (T.U α))}
    (g : M.M α ⟶ N) (β : T.ι) {W : Opens X} (hW : W ≤ T.U β) :
    sec R (M.M β) hW →+ sec R (pushComp R T.U α N β) hW :=
  (g.val.app (ovr (pbo_le_left T.U α W))).hom.toAddMonoidHom.comp
    ((M.φ β α ((pbo_le T.U α W).trans hW) (pbo_le_left T.U α W)).comp
      (secResHom R (M.M β) hW (pbo_le T.U α W)))

/-- Z3.i: `pushLiftFam` is `R(W)`-linear. -/
theorem pushLiftFam_smul (α : T.ι) {M : TwMod R T.U T.ch} {N : Mod ((ringOf R).over (T.U α))}
    (g : M.M α ⟶ N) (β : T.ι) {W : Opens X} (hW : W ≤ T.U β) (r : R.obj.obj (op W))
    (x : sec R (M.M β) hW) :
    pushLiftFam T α g β hW (toSec R hW r • x) = toSec R hW r • pushLiftFam T α g β hW x := by
  show (g.val.app (ovr (pbo_le_left T.U α W))).hom
      (M.φ β α ((pbo_le T.U α W).trans hW) (pbo_le_left T.U α W)
        (secRes R (M.M β) hW (pbo_le T.U α W) (toSec R hW r • x))) =
    toSec R (pbo_le_left T.U α W) ((R.obj.map (homOfLE (pbo_le T.U α W)).op).hom r) •
      (g.val.app (ovr (pbo_le_left T.U α W))).hom
        (M.φ β α ((pbo_le T.U α W).trans hW) (pbo_le_left T.U α W)
          (secRes R (M.M β) hW (pbo_le T.U α W) x))
  rw [secRes_smul, M.φ_smul, app_smul]

/-- Z3.i: `pushLiftFam` is natural in `W`. -/
theorem pushLiftFam_res (α : T.ι) {M : TwMod R T.U T.ch} {N : Mod ((ringOf R).over (T.U α))}
    (g : M.M α ⟶ N) (β : T.ι) {W W' : Opens X} (hW : W ≤ T.U β) (h' : W' ≤ W)
    (x : sec R (M.M β) hW) :
    pushLiftFam T α g β (h'.trans hW) (secRes R (M.M β) hW h' x) =
      secRes R (pushComp R T.U α N β) hW h' (pushLiftFam T α g β hW x) := by
  show (g.val.app (ovr (pbo_le_left T.U α W'))).hom
      (M.φ β α ((pbo_le T.U α W').trans (h'.trans hW)) (pbo_le_left T.U α W')
        (secRes R (M.M β) (h'.trans hW) (pbo_le T.U α W')
          (secRes R (M.M β) hW h' x))) =
    secRes R N (pbo_le_left T.U α W) (pbo_mono T.U α h')
      ((g.val.app (ovr (pbo_le_left T.U α W))).hom
        (M.φ β α ((pbo_le T.U α W).trans hW) (pbo_le_left T.U α W)
          (secRes R (M.M β) hW (pbo_le T.U α W) x)))
  rw [← app_secRes g (pbo_le_left T.U α W) (pbo_mono T.U α h'), ← M.φ_res,
    secRes_secRes, secRes_secRes]

/-- Z3.i: `pushLiftFam` commutes with the gluing maps (cocycle and cyclic symmetry of `ȟ`). -/
theorem pushLiftFam_comm (α : T.ι) {M : TwMod R T.U T.ch} {N : Mod ((ringOf R).over (T.U α))}
    (g : M.M α ⟶ N) (β γ : T.ι) {W : Opens X} (hβ : W ≤ T.U β) (hγ : W ≤ T.U γ)
    (x : sec R (M.M β) hβ) :
    pushGlue T.ch α N β γ hβ hγ (pushLiftFam T α g β hβ x) =
      pushLiftFam T α g γ hγ (M.φ β γ hβ hγ x) := by
  show toSec R (pbo_le_left T.U α W)
      (unitRes R (pbo_le_three T.U α hβ hγ) (T.ch α β γ) : R.obj.obj (op (pbo T.U α W))) •
      (g.val.app (ovr (pbo_le_left T.U α W))).hom
        (M.φ β α ((pbo_le T.U α W).trans hβ) (pbo_le_left T.U α W)
          (secRes R (M.M β) hβ (pbo_le T.U α W) x)) =
    (g.val.app (ovr (pbo_le_left T.U α W))).hom
      (M.φ γ α ((pbo_le T.U α W).trans hγ) (pbo_le_left T.U α W)
        (secRes R (M.M γ) hγ (pbo_le T.U α W) (M.φ β γ hβ hγ x)))
  rw [← M.φ_res, M.cocycle, app_smul,
    TwistCocycle.unitRes_cyclic T α β γ (pbo_le_left T.U α W)
      ((pbo_le T.U α W).trans hβ) ((pbo_le T.U α W).trans hγ)]

/-- **Z3.i.** The morphism `M ⟶ push T α N` corresponding to `g : M_α ⟶ N`. -/
def pushLift (α : T.ι) {M : TwMod R T.U T.ch} {N : Mod ((ringOf R).over (T.U α))}
    (g : M.M α ⟶ N) : M ⟶ (push T α).obj N where
  f β := homOfSec₀ (pushLiftFam T α g β) (pushLiftFam_smul T α g β) (pushLiftFam_res T α g β)
  comm β γ _ hβ hγ x := pushLiftFam_comm T α g β γ hβ hγ x

/-- Z3.i: sections of `pushLift g` (rfl). -/
theorem pushLift_app (α : T.ι) {M : TwMod R T.U T.ch} {N : Mod ((ringOf R).over (T.U α))}
    (g : M.M α ⟶ N) (β : T.ι) {W : Opens X} (hW : W ≤ T.U β) (x : sec R (M.M β) hW) :
    (((pushLift T α g).f β).val.app (ovr hW)).hom x = pushLiftFam T α g β hW x := rfl

/-- Helper: `pushGlue` towards the index `α` is the identity on sections of `N` (`ȟ_αβα = 1`). -/
private theorem pushGlue_back_eq (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) (β : T.ι)
    {W : Opens X} (hβ : W ≤ T.U β) (hα : W ≤ T.U α) (y : sec R (pushComp R T.U α N β) hβ) :
    (show (sec R N (pbo_le_left T.U α W) : Type) from pushGlue T.ch α N β α hβ hα y) =
      (show (sec R N (pbo_le_left T.U α W) : Type) from y) := by
  rw [pushGlue_apply, TwistCocycle.unitRes_normalized T (Or.inr (Or.inr rfl))]
  exact one_smul _ _

/-- **Z3.i.** [Toda, §4.3], blueprint-tw C.4′(e). `Hom(M, push T α N) ≃ Hom(M_α, N)`,
`F ↦ F_α ≫ ε_N`, inverse `pushLift`. -/
def pushHomEquiv (α : T.ι) (M : TwMod R T.U T.ch) (N : Mod ((ringOf R).over (T.U α))) :
    (M ⟶ (push T α).obj N) ≃ (M.M α ⟶ N) where
  toFun F := F.f α ≫ pushCounit T α N
  invFun := pushLift T α
  left_inv := fun F => by
    show pushLift T α (F.f α ≫ pushCounit T α N) = F
    refine TwMod.hom_ext fun β => ?_
    have key : ∀ {W : Opens X} (hW : W ≤ T.U β) (x : sec R (M.M β) hW),
        (((pushLift T α (F.f α ≫ pushCounit T α N)).f β).val.app (ovr hW)).hom x =
          ((F.f β).val.app (ovr hW)).hom x := by
      intro W hW x
      show secRes R N (pbo_le_left T.U α (pbo T.U α W)) (le_pbo T.U (pbo_le_left T.U α W))
          (((F.f α).val.app (ovr (pbo_le_left T.U α W))).hom
            (M.φ β α ((pbo_le T.U α W).trans hW) (pbo_le_left T.U α W)
              (secRes R (M.M β) hW (pbo_le T.U α W) x))) = _
      rw [← F.comm β α ((pbo_le T.U α W).trans hW) (pbo_le_left T.U α W)]
      show secRes R N (pbo_le_left T.U α (pbo T.U α W)) (le_pbo T.U (pbo_le_left T.U α W))
          (pushGlue T.ch α N β α ((pbo_le T.U α W).trans hW) (pbo_le_left T.U α W)
            (((F.f β).val.app (ovr ((pbo_le T.U α W).trans hW))).hom
              (secRes R (M.M β) hW (pbo_le T.U α W) x))) = _
      refine (congrArg (secRes R N (pbo_le_left T.U α (pbo T.U α W))
        (le_pbo T.U (pbo_le_left T.U α W))) (pushGlue_back_eq T α N β _ _ _)).trans ?_
      rw [app_secRes]
      show secRes R N (pbo_le_left T.U α (pbo T.U α W)) (le_pbo T.U (pbo_le_left T.U α W))
          (secRes R N (pbo_le_left T.U α W) (pbo_mono T.U α (pbo_le T.U α W))
            (show (sec R N (pbo_le_left T.U α W) : Type) from
              ((F.f β).val.app (ovr hW)).hom x)) = _
      rw [secRes_secRes, secRes_id]
    ext Y x
    exact key (leOfHom Y.unop.hom) x
  right_inv := fun g => by
    show (pushLift T α g).f α ≫ pushCounit T α N = g
    have key : ∀ {W : Opens X} (hW : W ≤ T.U α) (x : sec R (M.M α) hW),
        (((pushLift T α g).f α ≫ pushCounit T α N).val.app (ovr hW)).hom x =
          (g.val.app (ovr hW)).hom x := by
      intro W hW x
      show secRes R N (pbo_le_left T.U α W) (le_pbo T.U hW)
          ((g.val.app (ovr (pbo_le_left T.U α W))).hom
            (M.φ α α ((pbo_le T.U α W).trans hW) (pbo_le_left T.U α W)
              (secRes R (M.M α) hW (pbo_le T.U α W) x))) = _
      rw [M.φ_self, ← app_secRes g (pbo_le_left T.U α W) (le_pbo T.U hW), secRes_secRes,
        secRes_id]
    ext Y x
    exact key (leOfHom Y.unop.hom) x

/-- Z3.i: `pushHomEquiv` is `F ↦ F_α ≫ ε_N` (rfl). -/
theorem pushHomEquiv_apply (α : T.ι) (M : TwMod R T.U T.ch) (N : Mod ((ringOf R).over (T.U α)))
    (F : M ⟶ (push T α).obj N) : pushHomEquiv T α M N F = F.f α ≫ pushCounit T α N := rfl

/-- **Z3.i.** [Toda, §4.3], [A, Lemma 7.1.6]. The component functor `M ↦ M_α` is left adjoint to
the twisted pushforward `push T α`. -/
def pushAdj (α : T.ι) : TwMod.comp R T.U T.ch α ⊣ push T α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M N => (pushHomEquiv T α M N).symm
      homEquiv_naturality_left_symm := fun {M' M N} f g => by
        show pushHomEquiv T α M' N (f ≫ g) = (TwMod.comp R T.U T.ch α).map f ≫
          pushHomEquiv T α M N g
        simp only [pushHomEquiv_apply, TwMod.comp_f]
        rfl
      homEquiv_naturality_right := fun {M N N'} f g => by
        change (M.M α ⟶ N) at f
        show pushLift T α (f ≫ g) = pushLift T α f ≫ (push T α).map g
        apply (pushHomEquiv T α M N').injective
        have h1 : pushHomEquiv T α M N' (pushLift T α (f ≫ g)) = f ≫ g :=
          (pushHomEquiv T α M N').right_inv (f ≫ g)
        have h2 : pushHomEquiv T α M N (pushLift T α f) = f :=
          (pushHomEquiv T α M N).right_inv f
        rw [h1]
        show f ≫ g = ((pushLift T α f).f α ≫ (pushMap T α g).f α) ≫ pushCounit T α N'
        have h3 := Category.assoc ((pushLift T α f).f α) ((pushMap T α g).f α)
          (pushCounit T α N')
        have h4 := Category.assoc ((pushLift T α f).f α) (pushCounit T α N) g
        have h5 := congrArg (fun k => (pushLift T α f).f α ≫ k) (pushCounit_naturality T α g)
        have h6 : (pushLift T α f).f α ≫ pushCounit T α N = f := h2
        refine Eq.trans ?_ h3.symm
        refine Eq.trans ?_ h5.symm
        refine Eq.trans ?_ h4
        rw [h6] }

end Cohesive
