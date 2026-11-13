import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option linter.style.header false

/-!
# `H⁰` of a quasi-isomorphism of complexes of modules, elementwise

Blueprint item C4 step 5 (§4): the `H⁰` dictionary is applied to `Γ(Ψ ≫ r_*)`, a
quasi-isomorphism of complexes of `R(X)`-modules. These two lemmas say what `H⁰(f)` bijective
means for elements: every degree-`0` cocycle of the target is hit up to a coboundary
(surjectivity), and a cocycle of the source whose image is a coboundary is itself a coboundary
(injectivity).
-/

namespace Cohesive

open CategoryTheory

universe u v

/-- Two cycles of a short complex of modules have the same homology class iff their
difference is in the image of `f`. -/
private lemma homologyπ_eq_iff {S : Type u} [Ring S] {T : ShortComplex (ModuleCat.{v} S)}
    (a b : T.cycles.carrier) :
    T.homologyπ a = T.homologyπ b ↔
      ∃ w : T.X₁, (T.moduleCatCyclesIso.hom a).1 - (T.moduleCatCyclesIso.hom b).1 = T.f w := by
  have h1 : T.homologyπ a = T.homologyπ b ↔
      T.moduleCatHomologyIso.hom (T.homologyπ a) = T.moduleCatHomologyIso.hom (T.homologyπ b) :=
    (T.moduleCatHomologyIso.toLinearEquiv.injective.eq_iff).symm
  rw [h1]
  have h2 : ∀ x, T.moduleCatHomologyIso.hom (T.homologyπ x) =
      T.moduleCatLeftHomologyData.π (T.moduleCatCyclesIso.hom x) := fun x =>
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.1 T.π_moduleCatCyclesIso_hom) x
  rw [h2, h2]
  have h3 : ∀ x y : ↥(LinearMap.ker T.g.hom),
      (Submodule.Quotient.mk x : ↥(LinearMap.ker T.g.hom) ⧸ LinearMap.range T.moduleCatToCycles) =
        Submodule.Quotient.mk y ↔ ∃ w : T.X₁, x.1 - y.1 = T.f w := by
    intro x y
    rw [Submodule.Quotient.eq]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, (congrArg Subtype.val hw).symm⟩
    · rintro ⟨w, hw⟩
      exact ⟨w, Subtype.ext hw.symm⟩
  exact h3 (T.moduleCatCyclesIso.hom a) (T.moduleCatCyclesIso.hom b)

/-- The map on cycles induced by a morphism of short complexes is `τ₂` on kernels. -/
private lemma cyclesIso_cyclesMap {S : Type u} [Ring S] {T₁ T₂ : ShortComplex (ModuleCat.{v} S)}
    (φ : T₁ ⟶ T₂) (c : T₁.cycles.carrier) :
    (T₂.moduleCatCyclesIso.hom (ShortComplex.cyclesMap φ c)).1 =
      φ.τ₂ (T₁.moduleCatCyclesIso.hom c).1 := by
  have h := ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i φ) c
  have e1 := ConcreteCategory.congr_hom T₂.moduleCatCyclesIso_hom_i
    (ShortComplex.cyclesMap φ c)
  have e2 := ConcreteCategory.congr_hom T₁.moduleCatCyclesIso_hom_i c
  exact e1.trans (h.trans (congrArg φ.τ₂ e2.symm))

/-- Round trip through the explicit description of cycles. -/
private lemma cyclesIso_roundtrip {S : Type u} [Ring S] (T : ShortComplex (ModuleCat.{v} S))
    (x : ↥(LinearMap.ker T.g.hom)) :
    (T.moduleCatCyclesIso.hom (T.moduleCatCyclesIso.inv x)).1 = x.1 :=
  congrArg Subtype.val (ConcreteCategory.congr_hom T.moduleCatCyclesIso.inv_hom_id x)

/-- The explicit description of the zero cycle. -/
private lemma cyclesIso_zero {S : Type u} [Ring S] (T : ShortComplex (ModuleCat.{v} S)) :
    (T.moduleCatCyclesIso.hom (0 : T.cycles.carrier)).1 = 0 := by
  rw [map_zero]
  rfl

/-- Surjectivity of the homology map, elementwise, for short complexes of modules. -/
private lemma sc_surj {S : Type u} [Ring S] {T₁ T₂ : ShortComplex (ModuleCat.{v} S)}
    (φ : T₁ ⟶ T₂) [IsIso (ShortComplex.homologyMap φ)] (z : T₂.X₂) (hz : T₂.g z = 0) :
    ∃ (y : T₁.X₂) (w : T₂.X₁), T₁.g y = 0 ∧ φ.τ₂ y = z + T₂.f w := by
  obtain ⟨c₁, hc₁⟩ := (ModuleCat.epi_iff_surjective T₁.homologyπ).1 inferInstance
    (inv (ShortComplex.homologyMap φ)
      (T₂.homologyπ (T₂.moduleCatCyclesIso.inv ⟨z, LinearMap.mem_ker.2 hz⟩)))
  have h1 : T₂.homologyπ (ShortComplex.cyclesMap φ c₁) =
      T₂.homologyπ (T₂.moduleCatCyclesIso.inv ⟨z, LinearMap.mem_ker.2 hz⟩) := by
    have h := ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality φ) c₁
    have h' : ShortComplex.homologyMap φ (T₁.homologyπ c₁) =
        T₂.homologyπ (T₂.moduleCatCyclesIso.inv ⟨z, LinearMap.mem_ker.2 hz⟩) := by
      rw [hc₁]
      exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (ShortComplex.homologyMap φ)) _
    exact h.symm.trans h'
  obtain ⟨w, hw⟩ := (homologyπ_eq_iff _ _).1 h1
  refine ⟨(T₁.moduleCatCyclesIso.hom c₁).1, w, LinearMap.mem_ker.1
    (T₁.moduleCatCyclesIso.hom c₁).2, ?_⟩
  rw [← cyclesIso_cyclesMap, ← sub_eq_iff_eq_add']
  have e : (T₂.moduleCatCyclesIso.hom (T₂.moduleCatCyclesIso.inv ⟨z, LinearMap.mem_ker.2 hz⟩)).1
      = z := by
    exact cyclesIso_roundtrip T₂ _
  rw [← e]
  exact hw

/-- Injectivity of the homology map, elementwise, for short complexes of modules. -/
private lemma sc_inj {S : Type u} [Ring S] {T₁ T₂ : ShortComplex (ModuleCat.{v} S)}
    (φ : T₁ ⟶ T₂) [IsIso (ShortComplex.homologyMap φ)] (y : T₁.X₂) (hy : T₁.g y = 0)
    (w : T₂.X₁) (hw : φ.τ₂ y = T₂.f w) : ∃ v : T₁.X₁, y = T₁.f v := by
  let c : T₁.cycles := T₁.moduleCatCyclesIso.inv ⟨y, LinearMap.mem_ker.2 hy⟩
  have hc : (T₁.moduleCatCyclesIso.hom c).1 = y := by
    exact cyclesIso_roundtrip T₁ _
  have h0 : T₂.homologyπ (ShortComplex.cyclesMap φ c) =
      T₂.homologyπ (ShortComplex.cyclesMap φ 0) := by
    rw [homologyπ_eq_iff]
    refine ⟨w, ?_⟩
    rw [cyclesIso_cyclesMap, cyclesIso_cyclesMap, hc, hw, cyclesIso_zero, map_zero, sub_zero]
  have h1 : ShortComplex.homologyMap φ (T₁.homologyπ c) =
      ShortComplex.homologyMap φ (T₁.homologyπ 0) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ShortComplex.homologyπ_naturality, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, h0]
  have h2 : T₁.homologyπ c = T₁.homologyπ 0 :=
    (ConcreteCategory.injective_of_mono_of_preservesPullback _) h1
  obtain ⟨v, hv⟩ := (homologyπ_eq_iff _ _).1 h2
  refine ⟨v, ?_⟩
  rw [← hv, hc, cyclesIso_zero, sub_zero]

variable {S : Type u} [Ring S] {K L : CochainComplex (ModuleCat.{v} S) ℤ}

/-- **C4 step 5 (surjectivity of `H⁰ f`).** For a quasi-isomorphism `f : K ⟶ L` of cochain
complexes of `S`-modules, every degree-`0` cocycle `z` of `L` is `f(y)` up to a coboundary,
for a cocycle `y` of `K`. -/
theorem exists_cocycle_of_quasiIso (f : K ⟶ L) [QuasiIso f] (z : L.X 0)
    (hz : (L.d 0 1).hom z = 0) :
    ∃ (y : K.X 0) (w : L.X (-1)), (K.d 0 1).hom y = 0 ∧
      (f.f 0).hom y = z + (L.d (-1) 0).hom w := by
  have : IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} S) (ComplexShape.up ℤ)
        (-1) 0 1).map f)) :=
    (ShortComplex.quasiIso_iff _).1 ((quasiIsoAt_iff' f (-1) 0 1
      (by simp) (by simp)).1 inferInstance)
  exact sc_surj ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} S)
    (ComplexShape.up ℤ) (-1) 0 1).map f) z hz

/-- **C4 step 5 (injectivity of `H⁰ f`).** For a quasi-isomorphism `f : K ⟶ L` of cochain
complexes of `S`-modules, a degree-`0` cocycle `y` of `K` whose image is a coboundary is a
coboundary. -/
theorem exists_eq_d_of_quasiIso (f : K ⟶ L) [QuasiIso f] (y : K.X 0)
    (hy : (K.d 0 1).hom y = 0) (w : L.X (-1)) (hw : (f.f 0).hom y = (L.d (-1) 0).hom w) :
    ∃ v : K.X (-1), y = (K.d (-1) 0).hom v := by
  have : IsIso (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} S) (ComplexShape.up ℤ)
        (-1) 0 1).map f)) :=
    (ShortComplex.quasiIso_iff _).1 ((quasiIsoAt_iff' f (-1) 0 1
      (by simp) (by simp)).1 inferInstance)
  exact sc_inj ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} S)
    (ComplexShape.up ℤ) (-1) 0 1).map f) y hy w hw

end Cohesive
