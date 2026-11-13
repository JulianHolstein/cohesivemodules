-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Sheaf.Twisted.Def
import Cohesivemodules.Sheaf.RestrOver

set_option linter.style.header false

/-!
# Z3.h: section families and morphisms of sheaves on over-sites

Blueprint item Z3.h (`blueprint/blueprint-tw.md` §3 C.2′; prototype P19). The gluing maps of a
twisted sheaf are given on sections; kernels and cokernels are computed by sheaf morphisms. This
file is the bridge:
* `homOfSec`: an `R(W)`-linear family of maps on sections over every `W ≤ V`, natural in `W`, is a
  morphism of sheaves `restrOver h₁ P ⟶ restrOver h₂ Q` on `Over V` (sections of `restrOver` are
  the original sections definitionally, P19);
* `sec_injective_of_mono`: a monomorphism of sheaves of modules is injective on sections;
* `sec_eq_of_epi`: two such families that agree after precomposing with an epimorphism agree
  (cancel the epimorphism `restrOver h₁ p` against `homOfSec`; sections of a cokernel are not
  images of sections, so this replaces a section-level argument);
* `sec_eq_zero_of_isZero`: sections of a zero object vanish.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}

set_option linter.internalConstructors false in
/-- **Z3.h.** [Stacks 00VR]. A family of additive maps `f hW` from sections of `P` over `W` to
sections of `Q` over `W`, for `W ≤ V`, that is `R(W)`-linear (`hsmul`) and natural in `W` (`hres`),
as a morphism of sheaves of modules `restrOver h₁ P ⟶ restrOver h₂ Q` on the over-site `Over V`.

Lean note: the components are built with `ModuleCat.Hom._mkInternal`; `ModuleCat.ofHom`
re-synthesizes the module structure on the pushforward carrier and fails (P19). -/
def homOfSec {U₁ U₂ V : Opens X} (h₁ : V ≤ U₁) (h₂ : V ≤ U₂)
    {P : Mod ((ringOf R).over U₁)} {Q : Mod ((ringOf R).over U₂)}
    (f : ∀ {W : Opens X} (hW : W ≤ V), sec R P (hW.trans h₁) →+ sec R Q (hW.trans h₂))
    (hsmul : ∀ {W : Opens X} (hW : W ≤ V) (r : R.obj.obj (op W)) x,
      f hW (toSec R (hW.trans h₁) r • x) = toSec R (hW.trans h₂) r • f hW x)
    (hres : ∀ {W W' : Opens X} (hW : W ≤ V) (h' : W' ≤ W) x,
      f (h'.trans hW) (secRes R P (hW.trans h₁) h' x) = secRes R Q (hW.trans h₂) h' (f hW x)) :
    (restrOver (ringOf R) h₁).obj P ⟶ (restrOver (ringOf R) h₂).obj Q where
  val :=
    { app := fun Y => ModuleCat.Hom._mkInternal
        { toFun := f (leOfHom Y.unop.hom)
          map_add' := map_add _
          map_smul' := fun r x => hsmul (leOfHom Y.unop.hom) r x }
      naturality := fun {Y Y'} g => by
        ext x
        exact hres (leOfHom Y.unop.hom) (leOfHom g.unop.left) x }

set_option linter.internalConstructors false in
/-- **Z3.i.** As `homOfSec`, for sheaves of modules `P`, `Q` on the same over-site `Over V`: a
family of additive maps on sections over every `W ≤ V`, `R(W)`-linear and natural in `W`, is a
morphism of sheaves of modules `P ⟶ Q`. -/
def homOfSec₀ {V : Opens X} {P Q : Mod ((ringOf R).over V)}
    (f : ∀ {W : Opens X} (hW : W ≤ V), sec R P hW →+ sec R Q hW)
    (hsmul : ∀ {W : Opens X} (hW : W ≤ V) (r : R.obj.obj (op W)) x,
      f hW (toSec R hW r • x) = toSec R hW r • f hW x)
    (hres : ∀ {W W' : Opens X} (hW : W ≤ V) (h' : W' ≤ W) x,
      f (h'.trans hW) (secRes R P hW h' x) = secRes R Q hW h' (f hW x)) :
    P ⟶ Q where
  val :=
    { app := fun Y => ModuleCat.Hom._mkInternal
        { toFun := f (leOfHom Y.unop.hom)
          map_add' := map_add _
          map_smul' := fun r x => hsmul (leOfHom Y.unop.hom) r x }
      naturality := fun {Y Y'} g => by
        ext x
        exact hres (leOfHom Y.unop.hom) (leOfHom g.unop.left) x }

/-- Z3.i: the components of `homOfSec₀` are the given maps (rfl). -/
theorem homOfSec₀_app {V : Opens X} {P Q : Mod ((ringOf R).over V)}
    (f : ∀ {W : Opens X} (hW : W ≤ V), sec R P hW →+ sec R Q hW)
    (hsmul : ∀ {W : Opens X} (hW : W ≤ V) (r : R.obj.obj (op W)) x,
      f hW (toSec R hW r • x) = toSec R hW r • f hW x)
    (hres : ∀ {W W' : Opens X} (hW : W ≤ V) (h' : W' ≤ W) x,
      f (h'.trans hW) (secRes R P hW h' x) = secRes R Q hW h' (f hW x))
    {W : Opens X} (hW : W ≤ V) (x : sec R P hW) :
    ((homOfSec₀ f hsmul hres).val.app (ovr hW)).hom x = f hW x := rfl

/-- Z3.h: the components of `homOfSec` are the given maps (rfl). -/
theorem homOfSec_app {U₁ U₂ V : Opens X} (h₁ : V ≤ U₁) (h₂ : V ≤ U₂)
    {P : Mod ((ringOf R).over U₁)} {Q : Mod ((ringOf R).over U₂)}
    (f : ∀ {W : Opens X} (hW : W ≤ V), sec R P (hW.trans h₁) →+ sec R Q (hW.trans h₂))
    (hsmul : ∀ {W : Opens X} (hW : W ≤ V) (r : R.obj.obj (op W)) x,
      f hW (toSec R (hW.trans h₁) r • x) = toSec R (hW.trans h₂) r • f hW x)
    (hres : ∀ {W W' : Opens X} (hW : W ≤ V) (h' : W' ≤ W) x,
      f (h'.trans hW) (secRes R P (hW.trans h₁) h' x) = secRes R Q (hW.trans h₂) h' (f hW x))
    {W : Opens X} (hW : W ≤ V) (x : sec R P (hW.trans h₁)) :
    ((homOfSec h₁ h₂ f hsmul hres).val.app (ovr hW)).hom x = f hW x := rfl

/-- Z3.h: components of `restrOver h` applied to a morphism are the original components (rfl). -/
theorem restrOver_map_app {U V : Opens X} (h : V ≤ U) {P Q : Mod ((ringOf R).over U)}
    (g : P ⟶ Q) {W : Opens X} (hW : W ≤ V) (x : sec R P (hW.trans h)) :
    (((restrOver (ringOf R) h).map g).val.app (ovr hW)).hom x =
      (g.val.app (ovr (hW.trans h))).hom x :=
  rfl

/-- **Z3.h.** A monomorphism of sheaves of modules on `Over U` is injective on sections over every
`W ≤ U` (sheaves to presheaves and evaluation preserve monomorphisms). -/
theorem sec_injective_of_mono {U : Opens X} {P Q : Mod ((ringOf R).over U)} (i : P ⟶ Q) [Mono i]
    {W : Opens X} (h : W ≤ U) : Function.Injective (i.val.app (ovr h)).hom := by
  have h1 : Mono ((SheafOfModules.evaluation _ (ovr h)).map i) :=
    (SheafOfModules.evaluation _ (ovr h)).map_mono i
  exact (ModuleCat.mono_iff_injective _).1 h1

/-- **Z3.h.** Cancellation of an epimorphism `p : P ⟶ P'` of sheaves of modules on `Over U₁` against
section families: if two `R(W')`-linear natural families `a`, `b` (sections of `P'` over `W' ≤ W`
to sections of `Q`) agree on all images `p y`, they agree. Proof: `restrOver h₁ p` is an
epimorphism (`restrOver` is a left adjoint) and `restrOver h₁ p ≫ homOfSec a = restrOver h₁ p ≫
homOfSec b` on sections. -/
theorem sec_eq_of_epi {U₁ U₂ W : Opens X} (h₁ : W ≤ U₁) (h₂ : W ≤ U₂)
    {P P' : Mod ((ringOf R).over U₁)} {Q : Mod ((ringOf R).over U₂)} (p : P ⟶ P') [Epi p]
    (a b : ∀ {W' : Opens X} (hW' : W' ≤ W), sec R P' (hW'.trans h₁) →+ sec R Q (hW'.trans h₂))
    (ha_smul : ∀ {W' : Opens X} (hW' : W' ≤ W) (r : R.obj.obj (op W')) x,
      a hW' (toSec R (hW'.trans h₁) r • x) = toSec R (hW'.trans h₂) r • a hW' x)
    (ha_res : ∀ {W' W'' : Opens X} (hW' : W' ≤ W) (h' : W'' ≤ W') x,
      a (h'.trans hW') (secRes R P' (hW'.trans h₁) h' x) = secRes R Q (hW'.trans h₂) h' (a hW' x))
    (hb_smul : ∀ {W' : Opens X} (hW' : W' ≤ W) (r : R.obj.obj (op W')) x,
      b hW' (toSec R (hW'.trans h₁) r • x) = toSec R (hW'.trans h₂) r • b hW' x)
    (hb_res : ∀ {W' W'' : Opens X} (hW' : W' ≤ W) (h' : W'' ≤ W') x,
      b (h'.trans hW') (secRes R P' (hW'.trans h₁) h' x) = secRes R Q (hW'.trans h₂) h' (b hW' x))
    (hab : ∀ {W' : Opens X} (hW' : W' ≤ W) (y : sec R P (hW'.trans h₁)),
      a hW' ((p.val.app (ovr (hW'.trans h₁))).hom y) =
        b hW' ((p.val.app (ovr (hW'.trans h₁))).hom y))
    (x : sec R P' h₁) : a (le_refl W) x = b (le_refl W) x := by
  let A := homOfSec h₁ h₂ a ha_smul ha_res
  let B := homOfSec h₁ h₂ b hb_smul hb_res
  have hE : Epi ((restrOver (ringOf R) h₁).map p) := inferInstance
  have hAB : (restrOver (ringOf R) h₁).map p ≫ A = (restrOver (ringOf R) h₁).map p ≫ B := by
    ext Y y
    exact hab (leOfHom Y.unop.hom) y
  have h3 : A = B := (cancel_epi _).1 hAB
  exact congrArg (fun k => (k.val.app (ovr (le_refl W))).hom x) h3

/-- **Z3.h.** Sections of a zero object of sheaves of modules vanish. -/
theorem sec_eq_zero_of_isZero {U : Opens X} {P : Mod ((ringOf R).over U)} (hP : IsZero P)
    {W : Opens X} (h : W ≤ U) (x : sec R P h) : x = 0 := by
  have h1 : (𝟙 P : P ⟶ P) = 0 := hP.eq_of_src _ _
  have h2 := congrArg (fun k : P ⟶ P => (k.val.app (ovr h)).hom x) h1
  exact h2

end Cohesive
