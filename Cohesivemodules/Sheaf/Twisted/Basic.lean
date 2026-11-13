import Cohesivemodules.Sheaf.Twisted.Def

set_option linter.style.header false

/-!
# Z3.g: basic API of twisted sheaves

Blueprint item Z3.g (`blueprint/blueprint-tw.md` §3 C.1).
* `φ_symm`: `φ_βα ∘ φ_αβ = id` when `ȟ_αβα = 1` (normalization), so the gluing maps are additive
  equivalences (`φEquiv`);
* `isIso_of_isIso_f`: a morphism whose components are isomorphisms is an isomorphism (the
  component functors jointly reflect isomorphisms; they are jointly faithful by `TwMod.hom_ext`);
* `TwMod.ofSheaf N`: a sheaf of modules on `X` gives a twisted sheaf for the trivial cocycle, with
  components `N|U_α` and identity gluing (non-vacuity, and the easy half of S12 gluing, C.7).
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- **Z3.g.** [Căldăraru, §1.2]. If `ȟ_αβα = 1` (normalized cocycle), `φ_βα ∘ φ_αβ = id`:
cocycle at `(α, β, α)` and `φ_αα = id`. -/
theorem TwMod.φ_symm (hch : ∀ α β, ch α β α = 1) (M : TwMod R U ch) (α β : ι) {W : Opens X}
    (hα : W ≤ U α) (hβ : W ≤ U β) (x : sec R (M.M α) hα) :
    M.φ β α hβ hα (M.φ α β hα hβ x) = x := by
  rw [M.cocycle α β α hα hβ hα x, hch α β]
  simp only [map_one, Units.val_one]
  rw [M.φ_self α hα x]
  exact one_smul (((ringOf R).over (U α)).obj.obj (ovr hα)) x

/-- **Z3.g.** The gluing maps of a twisted sheaf with normalized cocycle are additive equivalences,
with inverse `φ_βα`. -/
def TwMod.φEquiv (hch : ∀ α β, ch α β α = 1) (M : TwMod R U ch) (α β : ι) {W : Opens X}
    (hα : W ≤ U α) (hβ : W ≤ U β) : sec R (M.M α) hα ≃+ sec R (M.M β) hβ where
  toFun := M.φ α β hα hβ
  invFun := M.φ β α hβ hα
  left_inv := TwMod.φ_symm hch M α β hα hβ
  right_inv := TwMod.φ_symm hch M β α hβ hα
  map_add' := map_add _

/-- Helper: an isomorphism of sheaves of modules is bijective on sections, `g (g⁻¹ y) = y`. -/
private theorem app_inv_apply {V : Opens X} {A B : Mod ((ringOf R).over V)} (g : A ⟶ B) [IsIso g]
    {W : Opens X} (h : W ≤ V) (y : sec R B h) :
    ((g.val.app (ovr h)).hom) (((inv g).val.app (ovr h)).hom y) = y := by
  have := congrArg (fun k : B ⟶ B => (k.val.app (ovr h)).hom y) (IsIso.inv_hom_id g)
  exact this

/-- Helper: an isomorphism of sheaves of modules is bijective on sections, `g⁻¹ (g x) = x`. -/
private theorem app_apply_inv {V : Opens X} {A B : Mod ((ringOf R).over V)} (g : A ⟶ B) [IsIso g]
    {W : Opens X} (h : W ≤ V) (x : sec R A h) :
    ((inv g).val.app (ovr h)).hom (((g.val.app (ovr h)).hom) x) = x := by
  have := congrArg (fun k : A ⟶ A => (k.val.app (ovr h)).hom x) (IsIso.hom_inv_id g)
  exact this

/-- **Z3.g (C.1).** A morphism of twisted sheaves whose components are isomorphisms is an
isomorphism (the inverse has the inverse components; it commutes with the gluing). -/
theorem TwMod.isIso_of_isIso_f {M N : TwMod R U ch} (f : M ⟶ N) [∀ α, IsIso (f.f α)] :
    IsIso f := by
  refine ⟨⟨⟨fun α => inv (f.f α), ?_⟩, ?_, ?_⟩⟩
  · intro α β W hα hβ x
    have hinj : Function.Injective ((f.f β).val.app (ovr hβ)).hom := fun a b hab => by
      have := congrArg ((inv (f.f β)).val.app (ovr hβ)).hom hab
      rwa [app_apply_inv, app_apply_inv] at this
    apply hinj
    rw [app_inv_apply (f.f β) hβ, ← f.comm α β hα hβ, app_inv_apply (f.f α) hα]
  · exact TwMod.hom_ext fun α => IsIso.hom_inv_id (f.f α)
  · exact TwMod.hom_ext fun α => IsIso.inv_hom_id (f.f α)

variable (R U) in
/-- **Z3.g.** A sheaf of modules `N` on `X` as a twisted sheaf for the trivial cocycle: components
`N|U_α` (`restr`), gluing maps the identity of `N(W)` (sections of `N|U_α` over `W ≤ U_α` are
`N(W)` definitionally). -/
def TwMod.ofSheaf (N : Mod (ringOf R)) : TwMod R U (fun _ _ _ => 1) where
  M α := (restr (ringOf R) (U α)).obj N
  φ _ _ _ _ _ := AddMonoidHom.id _
  φ_smul _ _ _ _ _ _ _ := rfl
  φ_res := by intros; rfl
  φ_self _ _ _ _ := rfl
  cocycle := by
    intro α β γ W hα hβ hγ x
    simp only [map_one, Units.val_one]
    exact (one_smul (((ringOf R).over (U γ)).obj.obj (ovr hγ))
      (show sec R ((restr (ringOf R) (U γ)).obj N) hγ from x)).symm

end Cohesive
