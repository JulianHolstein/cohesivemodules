-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Sheaf.RingOfDef
import Cohesivemodules.Sheaf.Twisted.CocycleDef
import Cohesivemodules.Sheaf.Basic

set_option linter.style.header false

/-!
# Z3.g: `ȟ`-twisted sheaves of modules

Blueprint item Z3.g (`blueprint/blueprint-tw.md` §2.3, §3 C.1; blueprint §11 v1.19, decisions D4,
D5; prototype P16). For a sheaf of commutative rings `R` on `X`, opens `U : ι → Opens X` and units
`ch α β γ ∈ R(U_α ∩ U_β ∩ U_γ)ˣ`:
* `sec M h`: sections over `W ≤ U` of a sheaf of modules `M` on the over-site `Over U`;
  `toSec h r` is `r ∈ R(W)` as a scalar on them, `secRes` restriction of sections;
* `TwMod R U ch`: components `M α` on `Over U_α` with gluing maps `φ α β` on sections over every
  `W ≤ U_α ∩ U_β`, `R(W)`-linear, natural in `W`, with `φ_βγ ∘ φ_αβ = ȟ_αβγ · φ_αγ`;
* morphisms (componentwise, commuting with the gluing), the category, the component functors.

## Deviations
* [A, Def 7.1.2], [Căldăraru, Def 1.2.1] glue isomorphisms of sheaves `φ_αβ : M_α|U_αβ → M_β|U_αβ`;
  here `φ` is given on sections over every `W ≤ U_α ∩ U_β`, natural in `W` (equivalent data, and it
  avoids restricting between over-sites of intersections, decision D5). `φ_αα = id` is a field
  (`φ_self`, as in [Căldăraru]); with it and the normalized cocycle, `φ_βα ∘ φ_αβ = id`, so the
  `φ α β` are bijective (Z3.g API). ⚠ Correction of blueprint-tw §2.3/P16, which listed `φ_self`
  as API: without the field, `φ = 0` satisfies all other axioms (the cocycle only makes `φ_αα`
  idempotent).
* Left modules over `R`; `ch` normalized (`TwistCocycle`); cocycle order of [A] corrected (audit
  a1): `φ_βγ φ_αβ = ȟ_αβγ φ_αγ`, matching `ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹` of the twist data.

## Lean notes
`R(W)` does not act on `sec M h` by instance search; `toSec` is the definitional coercion (P16).
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})

/-- Z3.g: the object `W ⟶ U` of `Over U`, in the opposite category. -/
abbrev ovr {U W : Opens X} (h : W ≤ U) : (Over U)ᵒᵖ := op (Over.mk (homOfLE h))

/-- **Z3.g.** Sections over `W ≤ U` of a sheaf of modules on the over-site `Over U`: a module over
`R(W)` (spelled as the ring of `(ringOf R).over U` at `W ⟶ U`). -/
abbrev sec {U : Opens X} (M : Mod ((ringOf R).over U)) {W : Opens X} (h : W ≤ U) :
    ModuleCat (((ringOf R).over U).obj.obj (ovr h)) :=
  M.val.obj (ovr h)

/-- **Z3.g.** `r ∈ R(W)` as a scalar on sections over `W ≤ U` (definitional, P16). -/
abbrev toSec {U W : Opens X} (h : W ≤ U) (r : R.obj.obj (op W)) :
    ((ringOf R).over U).obj.obj (ovr h) := r

/-- **Z3.g.** Restriction of sections along `W' ≤ W ≤ U`. -/
def secRes {U : Opens X} (M : Mod ((ringOf R).over U)) {W W' : Opens X} (h : W ≤ U)
    (h' : W' ≤ W) : sec R M h → sec R M (h'.trans h) :=
  fun x => (M.val.map (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans h)) ⟶
    Over.mk (homOfLE h)).op).hom x

variable {ι : Type} (U : ι → Opens X)

/-- **Z3.g.** [A, Def 7.1.2], [Căldăraru, Def 1.2.1], blueprint-tw §2.3. `ȟ`-twisted sheaves of
`R`-modules on the cover `U`: for every `α` a sheaf of modules `M α` on the over-site `Over U_α`,
and for every `W ≤ U_α ∩ U_β` an additive map `φ α β` from sections of `M α` over `W` to sections
of `M β` over `W`, `R(W)`-linear, compatible with restriction to `W' ≤ W`, the identity for
`α = β`, with the twisted cocycle `φ_βγ (φ_αβ x) = ȟ_αβγ|W · φ_αγ x` on every
`W ≤ U_α ∩ U_β ∩ U_γ`. See the module docstring for the deviations (section-level gluing, ⚠ field
`φ_self`). -/
structure TwMod (ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ) : Type 1 where
  /-- The components, on the over-sites `Over U_α`. -/
  M : ∀ α, Mod ((ringOf R).over (U α))
  /-- The gluing maps on sections over `W ≤ U_α ∩ U_β`. -/
  φ : ∀ α β {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β), sec R (M α) hα →+ sec R (M β) hβ
  φ_smul : ∀ α β {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (r : R.obj.obj (op W)) x,
    φ α β hα hβ (toSec R hα r • x) = toSec R hβ r • φ α β hα hβ x
  φ_res : ∀ α β {W W' : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (h' : W' ≤ W) x,
    φ α β (h'.trans hα) (h'.trans hβ) (secRes R (M α) hα h' x) =
      secRes R (M β) hβ h' (φ α β hα hβ x)
  φ_self : ∀ α {W : Opens X} (hα : W ≤ U α) x, φ α α hα hα x = x
  cocycle : ∀ α β γ {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (hγ : W ≤ U γ) x,
    φ β γ hβ hγ (φ α β hα hβ x) =
      toSec R hγ (unitRes R (le_inf (le_inf hα hβ) hγ) (ch α β γ) : R.obj.obj (op W)) •
        φ α γ hα hγ x

variable {R U} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- **Z3.g.** Morphisms of twisted sheaves: componentwise morphisms of sheaves of modules
commuting with the gluing maps on sections. -/
@[ext] structure TwMod.Hom (M N : TwMod R U ch) where
  /-- The components. -/
  f : ∀ α, M.M α ⟶ N.M α
  comm : ∀ α β {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) x,
    N.φ α β hα hβ (((f α).val.app (ovr hα)).hom x) =
      ((f β).val.app (ovr hβ)).hom (M.φ α β hα hβ x)

/-- **Z3.g.** The category of `ȟ`-twisted sheaves: identities and composition componentwise. -/
instance : Category (TwMod R U ch) where
  Hom := TwMod.Hom
  id M := ⟨fun _ => 𝟙 _, fun _ _ _ _ _ _ => rfl⟩
  comp f g := ⟨fun α => f.f α ≫ g.f α, fun α β _ hα hβ x => by
    change _ = ((g.f β).val.app (ovr hβ)).hom (((f.f β).val.app (ovr hβ)).hom _)
    rw [← f.comm, ← g.comm]
    rfl⟩

/-- Z3.g: components of the identity (rfl). -/
@[simp] theorem TwMod.id_f (M : TwMod R U ch) (α : ι) : (𝟙 M : M ⟶ M).f α = 𝟙 (M.M α) := rfl

/-- Z3.g: components of a composite (rfl). -/
@[simp] theorem TwMod.comp_f {M N P : TwMod R U ch} (f : M ⟶ N) (g : N ⟶ P) (α : ι) :
    (f ≫ g).f α = f.f α ≫ g.f α := rfl

/-- Z3.g: morphisms are equal if their components are. -/
@[ext] theorem TwMod.hom_ext {M N : TwMod R U ch} {f g : M ⟶ N} (h : ∀ α, f.f α = g.f α) :
    f = g :=
  TwMod.Hom.ext (funext h)

variable (R U ch) in
/-- **Z3.g.** The component functor `TwMod R U ch ⥤ Mod (R.over U_α)`, `M ↦ M α`. -/
def TwMod.comp (α : ι) : TwMod R U ch ⥤ Mod ((ringOf R).over (U α)) where
  obj M := M.M α
  map f := f.f α

end Cohesive
