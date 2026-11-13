import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective

set_option linter.style.header false

/-!
# S11: derived-category facts from Mathlib

Blueprint item S11 (§3): wiring only, for any abelian category `C` (applied to `Mod R`), in the
form the comparison layer uses them (chain maps and homotopies rather than the homotopy
category).

* Bounded-below injective resolutions (Mathlib's `CochainComplex.Plus.exists_quasiIso_injective`,
  stated on `InjectiveObject C`), as plain complexes with injective terms.
* Morphisms in `D(C)` into a K-injective complex, or out of a K-projective complex, are homotopy
  classes of chain maps (Mathlib's `IsKInjective.Qh_map_bijective`,
  `IsKProjective.Qh_map_bijective`).
* Bounded complexes of projectives are K-projective, bounded-below complexes of injectives
  K-injective: Mathlib's `isKProjective_of_projective`, `isKInjective_of_injective`, used
  directly.
* Universes: `HasDerivedCategory.standard` as a local instance (conventions §7).
-/

universe v u

noncomputable section

namespace Cohesive

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **S11.** Bounded-below injective resolutions: a complex `K` strictly zero below degree `n`
has a quasi-isomorphism `K ⟶ I` to a complex `I` of injective objects, also strictly zero below
degree `n` (hence K-injective, `CochainComplex.isKInjective_of_injective`). -/
theorem exists_injective_resolution [EnoughInjectives C] (K : CochainComplex C ℤ) (n : ℤ)
    [K.IsStrictlyGE n] :
    ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsStrictlyGE n ∧ (∀ i, Injective (I.X i)) ∧ QuasiIso f := by
  obtain ⟨L, i, hi, hL, hLn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  exact ⟨L, i, hLn, hL, hi⟩

variable [HasDerivedCategory C]

/-- `Q f = Q g` iff the images of `f`, `g` in the homotopy category agree after `Qh`. -/
private lemma Qh_map_quotient_map_eq_iff {K L : CochainComplex C ℤ} (f g : K ⟶ L) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g ↔
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map g) := by
  have hf := (DerivedCategory.quotientCompQhIso C).hom.naturality f
  have hg := (DerivedCategory.quotientCompQhIso C).hom.naturality g
  simp only [Functor.comp_map] at hf hg
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K), ← hf, ← hg,
    cancel_mono]

/-- Reduction: `Q f` is the transport of `Qh (quotient f)`. -/
private lemma Q_map_eq_comp {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map f = (DerivedCategory.quotientCompQhIso C).inv.app K ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app L := by
  have hf := (DerivedCategory.quotientCompQhIso C).hom.naturality f
  simp only [Functor.comp_map] at hf
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app K), ← hf]
  simp

/-- **S11.** Every morphism `Q K ⟶ Q L` in the derived category into a K-injective complex `L`
is `Q f` for a chain map `f : K ⟶ L`. -/
theorem Q_map_surjective_of_isKInjective (K L : CochainComplex C ℤ) [L.IsKInjective]
    (φ : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = φ := by
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) L).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ φ ≫
      (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective ψ
  refine ⟨f, ?_⟩
  rw [Q_map_eq_comp, hψ]
  simp

/-- **S11.** Two chain maps into a K-injective complex agree in the derived category iff they
are homotopic. -/
theorem Q_map_eq_iff_of_isKInjective {K L : CochainComplex C ℤ} [L.IsKInjective]
    (f g : K ⟶ L) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g ↔ Nonempty (Homotopy f g) := by
  refine ⟨fun h => ⟨HomotopyCategory.homotopyOfEq f g ?_⟩,
    fun ⟨h⟩ => DerivedCategory.Q_map_eq_of_homotopy C h⟩
  exact (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) L).injective
    ((Qh_map_quotient_map_eq_iff f g).1 h)

/-- **S11.** Every morphism `Q K ⟶ Q L` in the derived category out of a K-projective complex
`K` is `Q f` for a chain map `f : K ⟶ L`. -/
theorem Q_map_surjective_of_isKProjective (K L : CochainComplex C ℤ) [K.IsKProjective]
    (φ : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = φ := by
  obtain ⟨ψ, hψ⟩ := (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ φ ≫
      (DerivedCategory.quotientCompQhIso C).inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective ψ
  refine ⟨f, ?_⟩
  rw [Q_map_eq_comp, hψ]
  simp

/-- **S11.** Two chain maps out of a K-projective complex agree in the derived category iff they
are homotopic. -/
theorem Q_map_eq_iff_of_isKProjective {K L : CochainComplex C ℤ} [K.IsKProjective]
    (f g : K ⟶ L) :
    DerivedCategory.Q.map f = DerivedCategory.Q.map g ↔ Nonempty (Homotopy f g) := by
  refine ⟨fun h => ⟨HomotopyCategory.homotopyOfEq f g ?_⟩,
    fun ⟨h⟩ => DerivedCategory.Q_map_eq_of_homotopy C h⟩
  exact (CochainComplex.IsKProjective.Qh_map_bijective K
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)).injective
    ((Qh_map_quotient_map_eq_iff f g).1 h)

/-- **S11. Lifting along quasi-isomorphisms.** For `P` K-projective and a quasi-isomorphism
`s : L ⟶ K`, every chain map `g : P ⟶ K` lifts through `s` up to homotopy. -/
theorem exists_lift_of_isKProjective {P K L : CochainComplex C ℤ} [P.IsKProjective]
    (s : L ⟶ K) [QuasiIso s] (g : P ⟶ K) : ∃ f : P ⟶ L, Nonempty (Homotopy (f ≫ s) g) := by
  obtain ⟨f, hf⟩ := Q_map_surjective_of_isKProjective P L
    (DerivedCategory.Q.map g ≫ inv (DerivedCategory.Q.map s))
  refine ⟨f, (Q_map_eq_iff_of_isKProjective (f ≫ s) g).1 ?_⟩
  rw [Functor.map_comp, hf, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end Cohesive
