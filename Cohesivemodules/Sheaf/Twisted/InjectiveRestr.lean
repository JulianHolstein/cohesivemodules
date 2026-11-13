import Cohesivemodules.Sheaf.Twisted.Injective
import Cohesivemodules.Sheaf.HomOver

set_option linter.style.header false

/-!
# Z3.r: restrictions of injective twisted sheaves are injective (twisted S5.c)

Blueprint item Z3.r (`blueprint/blueprint-tw.md` §3 F′ (g)), the input of S7.c′ in the local step
of C4^tw. For an injective object `I` of `TwMod R U ȟ` (finite cover):
* `injective_restrOver_comp`: every restriction `(I_α)|W`, `W ≤ U_α`, is injective. `I` is a
  summand of `∏_β push_β J_β` with `J_β` injective (C.4 (g)); the components of `push_β J` are
  restrictions of `jstar β J` (`overPullback` of an injective, injective), and restrictions of an
  injective sheaf on `Over ⊤` compose (`restrOver` composes definitionally) and are injective by
  S5.c through `restr R ⊤`; finite products and summands of injectives are injective.
* `injective_overFunctor_restrOver`: if every restriction of `P` on `Over U` is injective, so is
  the restriction of `P|W` to every object `V` of `Over W` (`(P|W)|V ≅ P|V.left` through
  `Over V ≌ Over V.left`), the form of the hypothesis of S7.c′.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}

/-- Z3.r: restriction `restrOver h` preserves injective objects: `G ≅ (G_*)|U` with `G_*` the
right adjoint of `restr R U` (injective since `restr` preserves monos), then `restr_restrOver`. -/
private theorem injective_restrOver_obj {U V : Opens X} (h : V ≤ U)
    (G : Mod ((ringOf R).over U)) [Injective G] : Injective ((restrOver (ringOf R) h).obj G) := by
  let t : Adjunction.Triple (extZero (ringOf R) U) (restr (ringOf R) U) _ :=
    ⟨extZeroAdj (ringOf R) U, SheafOfModules.overPushforwardOverAdj.{0} (R := ringOf R) U⟩
  have h1 : IsIso t.adj₁.unit := by
    have : ∀ N, IsIso (t.adj₁.unit.app N) := isIso_extZeroAdj_unit (ringOf R) U
    exact NatIso.isIso_of_isIso_app _
  have h2 : IsIso t.adj₂.counit := t.isIso_unit_iff_isIso_counit.1 h1
  have h3 := t.adj₂.map_injective G inferInstance
  have h4 : Injective ((restr (ringOf R) V).obj
      ((SheafOfModules.pushforward.{0} (SheafOfModules.pushforwardOver U)).obj G)) :=
    inferInstance
  have e : (restrOver (ringOf R) h).obj ((restr (ringOf R) U).obj
      ((SheafOfModules.pushforward.{0} (SheafOfModules.pushforwardOver U)).obj G)) ≅
      (restrOver (ringOf R) h).obj G :=
    (restrOver (ringOf R) h).mapIso (asIso (t.adj₂.counit.app G))
  exact Injective.of_iso
    (((restr_restrOver (ringOf R) h).app _).symm ≪≫ e) h4

/-- **Z3.r (F′ (g)).** blueprint-tw C.4–C.5. For an injective twisted sheaf `I`, every restriction
of every component `I_α` to `W ≤ U_α` is injective. -/
theorem injective_restrOver_comp (T : TwistCocycle R) (I : TwMod R T.U T.ch) [Injective I]
    (α : T.ι) {W : Opens X} (h : W ≤ T.U α) : Injective ((restrOver (ringOf R) h).obj (I.M α)) := by
  let F : T.ι → TwMod R T.U T.ch := fun β => (push T β).obj (Injective.under (I.M β))
  let ι' : I ⟶ ∏ᶜ F := Pi.lift (fun β => pushLift T β (Injective.ι (I.M β)))
  have hm : ∀ β, Mono (ι'.f β) := by
    intro β
    have h1 : Mono ((pushLift T β (Injective.ι (I.M β))).f β) :=
      mono_of_mono_fac (pushLift_f_comp_counit T β (Injective.ι (I.M β)))
    have h2 : ι'.f β ≫ (Pi.π F β).f β = (pushLift T β (Injective.ι (I.M β))).f β := by
      rw [← TwMod.comp_f, Pi.lift_comp_π]
    exact mono_of_mono_fac h2
  have : Mono ι' := TwMod.mono_of_mono_f _
  let s : ∏ᶜ F ⟶ I := Injective.factorThru (𝟙 I) ι'
  have hs : ι' ≫ s = 𝟙 I := Injective.comp_factorThru _ _
  have hF : ∀ β, Injective ((TwMod.comp R T.U T.ch α).obj (F β)) := fun β =>
    injective_restrOver_obj (le_top : T.U α ≤ ⊤) _
  have hP : Injective ((TwMod.comp R T.U T.ch α).obj (∏ᶜ F)) :=
    Injective.of_iso (asIso (piComparison (TwMod.comp R T.U T.ch α) F)).symm inferInstance
  have hret : Retract ((TwMod.comp R T.U T.ch α).obj I)
      ((TwMod.comp R T.U T.ch α).obj (∏ᶜ F)) :=
    ⟨(TwMod.comp R T.U T.ch α).map ι', (TwMod.comp R T.U T.ch α).map s, by
      rw [← Functor.map_comp, hs]; exact (TwMod.comp R T.U T.ch α).map_id _⟩
  have hI : Injective ((TwMod.comp R T.U T.ch α).obj I) := hret.injective
  exact @injective_restrOver_obj X _ R _ _ h (I.M α) hI

/-- Z3.r: modules on the nested over-site `(Over W).over V` are modules on `Over V.left`
(copy of `overOverEquiv'` in `Sheaf/HomOver.lean`). -/
private def overOverEquiv'' (W : Opens X) (V : Over W) :
    Mod (((ringOf R).over W).over V) ≌ Mod ((ringOf R).over V.left) :=
  (SheafOfModules.pushforwardPushforwardEquivalence.{0} (Over.iteratedSliceEquiv V)
    (S := ((ringOf R).over W).over V) (R := (ringOf R).over V.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact (ringOf R).1.map_id _) (by ext : 2; exact (ringOf R).1.map_id _)).symm

/-- Z3.r: restricting `P` to `W` and then to `V` is restricting `P` to `V.left`. -/
private def overOverEquivObjIso'' {U : Opens X} (W : Opens X) (V : Over W) (h : W ≤ U)
    (P : Mod ((ringOf R).over U)) :
    (overOverEquiv'' W V).functor.obj
      ((SheafOfModules.overFunctor.{0} ((ringOf R).over W) V).obj
        ((restrOver (ringOf R) h).obj P)) ≅
      (restrOver (ringOf R) (V.hom.le.trans h)).obj P :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl))

/-- **Z3.r (F′ (g)).** If every restriction of `P` (on `Over U`) to `W' ≤ U` is injective, then for
`W ≤ U` and every object `V` of `Over W`, the restriction of `P|W` to `V` (Mathlib's
`overFunctor`) is injective. -/
theorem injective_overFunctor_restrOver {U W : Opens X} (P : Mod ((ringOf R).over U))
    (hP : ∀ {W' : Opens X} (h' : W' ≤ U), Injective ((restrOver (ringOf R) h').obj P))
    (h : W ≤ U) (V : Over W) :
    Injective ((SheafOfModules.overFunctor.{0} ((ringOf R).over W) V).obj
      ((restrOver (ringOf R) h).obj P)) := by
  have h1 : Injective ((restrOver (ringOf R) (V.hom.le.trans h)).obj P) := hP _
  have h2 : Injective ((overOverEquiv'' W V).functor.obj
      ((SheafOfModules.overFunctor.{0} ((ringOf R).over W) V).obj
        ((restrOver (ringOf R) h).obj P))) :=
    Injective.of_iso (overOverEquivObjIso'' W V h P).symm h1
  have h3 := (overOverEquiv'' W V).toAdjunction.map_injective _ h2
  exact Injective.of_iso ((overOverEquiv'' W V).unitIso.app _).symm h3

end Cohesive
