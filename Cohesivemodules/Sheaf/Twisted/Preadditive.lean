-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Sheaf.Twisted.Def

set_option linter.style.header false

/-!
# Z3.h: twisted sheaves form a preadditive category

Blueprint item Z3.h (`blueprint/blueprint-tw.md` §3 C.2). Sums, negatives, integer multiples and
zero of morphisms of twisted sheaves are taken componentwise (the gluing maps are additive, and
sections of a sum of sheaf morphisms are sums of sections, `app_add`, …). The component functors
are additive.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

section app

variable {V : Opens X} {P Q : Mod ((ringOf R).over V)} {W : Opens X} (h : W ≤ V)

/-- Z3.h: sections of a sum of sheaf morphisms. -/
theorem app_add (f g : P ⟶ Q) (x : sec R P h) :
    ((f + g).val.app (ovr h)).hom x = (f.val.app (ovr h)).hom x + (g.val.app (ovr h)).hom x := by
  rfl

/-- Z3.h: sections of the zero sheaf morphism. -/
theorem app_zero (x : sec R P h) : ((0 : P ⟶ Q).val.app (ovr h)).hom x = 0 := by
  rfl

/-- Z3.h: sections of the negative of a sheaf morphism. -/
theorem app_neg (f : P ⟶ Q) (x : sec R P h) :
    ((-f).val.app (ovr h)).hom x = -(f.val.app (ovr h)).hom x := by
  rfl

/-- Z3.h: sections of a difference of sheaf morphisms. -/
theorem app_sub (f g : P ⟶ Q) (x : sec R P h) :
    ((f - g).val.app (ovr h)).hom x = (f.val.app (ovr h)).hom x - (g.val.app (ovr h)).hom x := by
  rfl

/-- Z3.h: sections of a natural multiple of a sheaf morphism. -/
theorem app_nsmul (n : ℕ) (f : P ⟶ Q) (x : sec R P h) :
    ((n • f).val.app (ovr h)).hom x = n • (f.val.app (ovr h)).hom x := by
  have := Functor.map_nsmul (SheafOfModules.forget ((ringOf R).over V) ⋙
    PresheafOfModules.evaluation _ (ovr h)) (n := n) (f := f)
  exact congrArg (fun g => g.hom x) this

/-- Z3.h: sections of an integer multiple of a sheaf morphism. -/
theorem app_zsmul (n : ℤ) (f : P ⟶ Q) (x : sec R P h) :
    ((n • f).val.app (ovr h)).hom x = n • (f.val.app (ovr h)).hom x := by
  have := Functor.map_zsmul (SheafOfModules.forget ((ringOf R).over V) ⋙
    PresheafOfModules.evaluation _ (ovr h)) (r := n) (f := f)
  exact congrArg (fun g => g.hom x) this

end app

namespace TwMod

variable {M N : TwMod R U ch}

/-- Z3.h: the zero morphism of twisted sheaves (componentwise). -/
instance : Zero (M ⟶ N) := ⟨⟨fun _ => 0, fun _ _ _ _ _ _ => by
  simp only [app_zero, map_zero]⟩⟩

/-- Z3.h: the sum of morphisms of twisted sheaves (componentwise). -/
instance : Add (M ⟶ N) := ⟨fun f g => ⟨fun α => f.f α + g.f α, fun α β _ hα hβ x => by
  simp only [app_add, map_add, f.comm, g.comm]⟩⟩

/-- Z3.h: the negative of a morphism of twisted sheaves (componentwise). -/
instance : Neg (M ⟶ N) := ⟨fun f => ⟨fun α => -f.f α, fun α β _ hα hβ x => by
  simp only [app_neg, map_neg, f.comm]⟩⟩

/-- Z3.h: the difference of morphisms of twisted sheaves (componentwise). -/
instance : Sub (M ⟶ N) := ⟨fun f g => ⟨fun α => f.f α - g.f α, fun α β _ hα hβ x => by
  simp only [app_sub, map_sub, f.comm, g.comm]⟩⟩

/-- Z3.h: natural multiples of morphisms of twisted sheaves (componentwise). -/
instance : SMul ℕ (M ⟶ N) := ⟨fun n f => ⟨fun α => n • f.f α, fun α β _ hα hβ x => by
  simp only [app_nsmul, map_nsmul, f.comm]⟩⟩

/-- Z3.h: integer multiples of morphisms of twisted sheaves (componentwise). -/
instance : SMul ℤ (M ⟶ N) := ⟨fun n f => ⟨fun α => n • f.f α, fun α β _ hα hβ x => by
  simp only [app_zsmul, map_zsmul, f.comm]⟩⟩

/-- Z3.h: components of the zero morphism (rfl). -/
@[simp] theorem zero_f (α : ι) : (0 : M ⟶ N).f α = 0 := rfl

/-- Z3.h: components of a sum (rfl). -/
@[simp] theorem add_f (f g : M ⟶ N) (α : ι) : (f + g).f α = f.f α + g.f α := rfl

/-- Z3.h: components of a negative (rfl). -/
@[simp] theorem neg_f (f : M ⟶ N) (α : ι) : (-f).f α = -f.f α := rfl

/-- Z3.h: components of a difference (rfl). -/
@[simp] theorem sub_f (f g : M ⟶ N) (α : ι) : (f - g).f α = f.f α - g.f α := rfl

/-- Z3.h: components of a natural multiple (rfl). -/
@[simp] theorem nsmul_f (n : ℕ) (f : M ⟶ N) (α : ι) : (n • f).f α = n • f.f α := rfl

/-- Z3.h: components of an integer multiple (rfl). -/
@[simp] theorem zsmul_f (n : ℤ) (f : M ⟶ N) (α : ι) : (n • f).f α = n • f.f α := rfl

/-- **Z3.h.** Morphisms of twisted sheaves form an abelian group (componentwise; `TwMod.hom_ext`
makes the components injective). -/
instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup (fun f : M ⟶ N => f.f) (fun _ _ h => TwMod.Hom.ext h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- **Z3.h.** [Căldăraru, §1.2]. Twisted sheaves form a preadditive category. -/
instance : Preadditive (TwMod R U ch) where
  add_comp _ _ _ _ _ _ := TwMod.hom_ext fun _ => Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := TwMod.hom_ext fun _ => Preadditive.comp_add _ _ _ _ _ _

variable (R U ch) in
/-- Z3.h: the component functors are additive. -/
instance comp_additive (α : ι) : (TwMod.comp R U ch α).Additive where
  map_add := rfl

end TwMod

end Cohesive
