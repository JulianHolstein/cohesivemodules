import Cohesivemodules.Sheaf.Twisted.ExtZero
import Cohesivemodules.Sheaf.Twisted.Injective

set_option linter.style.header false

/-!
# Z3.l: twisted extension by zero `extTw α`

Blueprint item Z3.l (blueprint §11 v1.20 item 2; `blueprint/blueprint-tw.md` C.8; prototype P22).
For a twist cocycle `T`, an index `α` and a sheaf of modules `N` on `Over U_α`, the twisted sheaf
`extTw α N` with components `(extTw α N)_β = (j_! N)|U_β` (`restr (U β) (extX (U α) N)`). Its
sections over `W ≤ U_β` are sections of `N` over `W ⊓ U_α` with support closed in `W`, for every
`β` (definitionally), so the gluing maps are multiplication by `ȟ_αβγ|(W ⊓ U_α)`; `φ_self` holds by
normalization, the cocycle by `unitRes_cocycle` at `(α, β, γ, δ)`.
* `extTw T α : Mod (R|U_α) ⥤ TwMod R T.U T.ch` preserves monomorphisms;
* its components are flat if `N` is.

## Deviations
* [Căldăraru, §1.2] define the extension by zero of twisted sheaves through Mathlib-style `j_!`;
  here explicit sections (v1.20), and the components are restrictions of one sheaf on `X`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  (T : TwistCocycle R)

/-- Z3.l: scalars of `R(W)` commute on sections over `W ≤ V`. -/
private theorem toSec_smul_comm' {V : Opens X} (N : Mod ((ringOf R).over V)) {W : Opens X}
    (h : W ≤ V) (a b : R.obj.obj (op W)) (y : sec R N h) :
    toSec R h a • toSec R h b • y = toSec R h b • toSec R h a • y := by
  rw [← mul_smul, ← mul_smul]
  exact congrArg (· • y) (mul_comm a b)

/-- **Z3.l.** The gluing maps of `extTw α N`: multiplication by `ȟ_αβγ|(W ⊓ U_α)` on sections of
`N` over `W ⊓ U_α` (with support closed in `W`). -/
def extTwφ (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) (β γ : T.ι) {W : Opens X}
    (hβ : W ≤ T.U β) (hγ : W ≤ T.U γ) :
    sec R ((restr (ringOf R) (T.U β)).obj (extX (T.U α) N)) hβ →+
      sec R ((restr (ringOf R) (T.U γ)).obj (extX (T.U α) N)) hγ where
  toFun s := ⟨toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α)
      (unitRes R (le_inf (le_inf inf_le_right (inf_le_left.trans hβ)) (inf_le_left.trans hγ))
        (T.ch α β γ) : R.obj.obj (op (W ⊓ T.U α))) • s.1, by
    obtain ⟨W', h, hW, hs⟩ := s.2
    refine ⟨W', h, hW, ?_⟩
    have e := secRes_smul N (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_inf_right (T.U α) h)
      (unitRes R (le_inf (le_inf inf_le_right (inf_le_left.trans hβ)) (inf_le_left.trans hγ))
        (T.ch α β γ) : R.obj.obj (op (W ⊓ T.U α))) s.1
    refine e.trans ?_
    rw [show secRes R N inf_le_right (inf_le_inf_right (T.U α) h) s.1 = 0 from hs]
    exact smul_zero _⟩
  map_zero' := by
    refine Subtype.ext ?_
    exact smul_zero _
  map_add' := by
    intro s s'
    refine Subtype.ext ?_
    exact smul_add _ _ _

theorem extTwφ_apply (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) (β γ : T.ι) {W : Opens X}
    (hβ : W ≤ T.U β) (hγ : W ≤ T.U γ) (s : extSub (T.U α) N W) :
    (extTwφ T α N β γ hβ hγ s).1 = toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α)
      (unitRes R (le_inf (le_inf inf_le_right (inf_le_left.trans hβ)) (inf_le_left.trans hγ))
        (T.ch α β γ) : R.obj.obj (op (W ⊓ T.U α))) • s.1 :=
  rfl

/-- **Z3.l.** [Căldăraru, §1.2]. The twisted extension by zero of `N` on `U_α`: components
`(j_! N)|U_β`, gluing `ȟ_αβγ ·`. -/
def extTwObj (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) : TwMod R T.U T.ch where
  M β := (restr (ringOf R) (T.U β)).obj (extX (T.U α) N)
  φ β γ _ hβ hγ := extTwφ T α N β γ hβ hγ
  φ_smul β γ {W} hβ hγ r x := by
    refine Subtype.ext ?_
    exact toSec_smul_comm' N inf_le_right _ _ x.1
  φ_res β γ {W W'} hβ hγ h' x := by
    refine Subtype.ext ?_
    have e := secRes_smul N (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_inf_right (T.U α) h')
      (unitRes R (le_inf (le_inf inf_le_right (inf_le_left.trans hβ)) (inf_le_left.trans hγ))
        (T.ch α β γ) : R.obj.obj (op (W ⊓ T.U α))) x.1
    rw [unitRes_res] at e
    exact e.symm
  φ_self β {W} hβ x := by
    refine Subtype.ext ?_
    have h0 : W ⊓ T.U α ≤ T.U α ⊓ T.U β ⊓ T.U β :=
      le_inf (le_inf inf_le_right (inf_le_left.trans hβ)) (inf_le_left.trans hβ)
    have h1 := T.unitRes_normalized (Or.inr (Or.inl rfl)) h0
    change toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α) (unitRes R h0 (T.ch α β β) :
      R.obj.obj (op (W ⊓ T.U α))) • x.1 = x.1
    rw [h1, Units.val_one]
    exact one_smul _ _
  cocycle β γ δ {W} hβ hγ hδ x := by
    refine Subtype.ext ?_
    have hc := congrArg Units.val (T.unitRes_cocycle α β γ δ
      (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_left.trans hβ) (inf_le_left.trans hγ) (inf_le_left.trans hδ))
    simp only [Units.val_mul] at hc
    have e := unitRes_res (R := R) (le_inf (le_inf hβ hγ) hδ)
      (inf_le_left : W ⊓ T.U α ≤ W) (T.ch β γ δ)
    change toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α) _ •
      toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α) _ • x.1 =
        toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α) ((R.obj.map (homOfLE
          (inf_le_left : W ⊓ T.U α ≤ W)).op).hom
          (unitRes R (le_inf (le_inf hβ hγ) hδ) (T.ch β γ δ) : R.obj.obj (op W))) •
        toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α) _ • x.1
    rw [e, ← mul_smul, ← mul_smul]
    exact congrArg (fun a : R.obj.obj (op (W ⊓ T.U α)) =>
      toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α) a • x.1) hc.symm

theorem extTwObj_M (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) (β : T.ι) :
    (extTwObj T α N).M β = (restr (ringOf R) (T.U β)).obj (extX (T.U α) N) :=
  rfl

/-- **Z3.l.** `extTw α` on morphisms: `j_! f` on every component. -/
def extTwMap (α : T.ι) {N N' : Mod ((ringOf R).over (T.U α))} (f : N ⟶ N') :
    extTwObj T α N ⟶ extTwObj T α N' where
  f β := (restr (ringOf R) (T.U β)).map (extXMap f)
  comm β γ {W} hβ hγ x := by
    refine Subtype.ext ?_
    change toSec R (inf_le_right : W ⊓ T.U α ≤ T.U α) _ • (extXMapL f W x).1 =
      (extXMapL f W (extTwφ T α N β γ hβ hγ x)).1
    exact (app_smul f (inf_le_right : W ⊓ T.U α ≤ T.U α) _ x.1).symm

theorem extTwMap_f (α : T.ι) {N N' : Mod ((ringOf R).over (T.U α))} (f : N ⟶ N') (β : T.ι) :
    (extTwMap T α f).f β = (restr (ringOf R) (T.U β)).map (extXMap f) :=
  rfl

/-- **Z3.l.** The twisted extension by zero as a functor `Mod (R|U_α) ⥤ TwMod R T.U T.ch`. -/
def extTw (α : T.ι) : Mod ((ringOf R).over (T.U α)) ⥤ TwMod R T.U T.ch where
  obj := extTwObj T α
  map := extTwMap T α
  map_id N := by
    refine TwMod.hom_ext fun β => ?_
    change (restr (ringOf R) (T.U β)).map (extXMap (𝟙 N)) = 𝟙 _
    rw [extXMap_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    refine TwMod.hom_ext fun β => ?_
    change (restr (ringOf R) (T.U β)).map (extXMap (f ≫ g)) =
      (restr (ringOf R) (T.U β)).map (extXMap f) ≫ (restr (ringOf R) (T.U β)).map (extXMap g)
    rw [extXMap_comp, CategoryTheory.Functor.map_comp]

/-- **Z3.l.** `extTw α` preserves monomorphisms (componentwise `j_!` of a monomorphism,
restricted). -/
instance extTw_preservesMonomorphisms (α : T.ι) : (extTw T α).PreservesMonomorphisms := by
  refine ⟨fun {N N'} f hf => ?_⟩
  have hpm : ∀ β, (restr (ringOf R) (T.U β)).PreservesMonomorphisms := fun β =>
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have : ∀ β, Mono (((extTw T α).map f).f β) := fun β =>
    @(hpm β).preserves _ _ (extXMap f) (mono_extXMap f)
  exact TwMod.mono_of_mono_f _

/-- **Z3.l.** The components of the twisted extension by zero of a flat sheaf are flat
(`isFlat_extX`, `IsFlat.restr`). -/
theorem isFlat_extTwObj (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    (hN : IsFlat (R.over (T.U α)) N) (β : T.ι) :
    IsFlat (R.over (T.U β)) ((extTwObj T α N).M β) :=
  IsFlat.restr R (isFlat_extX hN) (T.U β)

end Cohesive
