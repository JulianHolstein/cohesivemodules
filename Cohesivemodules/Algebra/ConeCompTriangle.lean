import Cohesivemodules.Algebra.ConeComp

set_option linter.style.header false

/-!
# Z2.g1: the distinguished triangle of a composite

Blueprint item Z2.g (`blueprint/blueprint-tr.md` §3d), split off from `Algebra/ConeComp.lean`.
Following Mathlib's `mappingConeCompTriangleh_distinguished`: `C(v) ≅ C(m₁)` in `Ho(P_A)`
(`compIso`), and the triangle `C(u) → C(v ∘ u) → C(v) → C(u)⟦1⟧` (`compTriangle`) is distinguished.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Pretriangulated

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable {X₁ X₂ X₃ : CohesiveModule 𝒜} (u : Z0 X₁.toQuasiCohesive X₂.toQuasiCohesive)
  (v : Z0 X₂.toQuasiCohesive X₃.toQuasiCohesive)

/-- **Z2.g1.** `C(v) ≅ C(m₁)` in `Ho(P_A)`, with `[compHom]` as forward map. -/
def compIso : (⟨cone v⟩ : HoP 𝒜) ≅ ⟨cone (compMor₁ u v)⟩ where
  hom := Submodule.Quotient.mk (compHom u v)
  inv := Submodule.Quotient.mk (compInv u v)
  hom_inv_id := compHmkEq' _ (idZ0 _) (compInv_compHom u v)
  inv_hom_id := compHmkEq _ (idZ0 _) _ (compH_mem u v) (compHom_compInv u v)

/-- **Z2.g1.** [B, §2.4]; Mathlib `mappingConeCompTriangleh`. The triangle
`C(u) →[m₁] C(v ∘ u) →[m₂] C(v) →[w_v ≫ inr_u⟦1⟧] C(u)⟦1⟧` in `Ho(P_A)`. -/
def compTriangle : Triangle (HoP 𝒜) :=
  Triangle.mk (X := (⟨cone u⟩ : HoP 𝒜)) (Y := ⟨cone (compZ0 _ _ _ v u)⟩) (Z := ⟨cone v⟩)
    (Submodule.Quotient.mk (compMor₁ u v)) (Submodule.Quotient.mk (compMor₂ u v))
    ((show (⟨cone v⟩ : HoP 𝒜) ⟶ (⟨X₂⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from
        Submodule.Quotient.mk (coneWZ0 v)) ≫
      (show (⟨X₂⟩ : HoP 𝒜) ⟶ ⟨cone u⟩ from Submodule.Quotient.mk (coneInrZ0 u))⟦(1 : ℤ)⟧')

/-- **Z2.g1.** Mathlib `mappingConeCompTriangleh_distinguished`: `compTriangle u v` is
distinguished, via `(id, id, compIso)` to `coneTriangle m₁`. -/
theorem compTriangle_distinguished : compTriangle u v ∈ distTriang (HoP 𝒜) := by
  refine (mem_distTriang_iff 𝒜 _).2 ⟨_, _, compMor₁ u v, ⟨Triangle.isoMk _ _ (Iso.refl _)
    (Iso.refl _) (compIso u v) ((Category.comp_id _).trans (Category.id_comp _).symm) ?_ ?_⟩⟩
  · have e1 : (Submodule.Quotient.mk (coneInrZ0 (compMor₁ u v)) :
          (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ ⟨cone (compMor₁ u v)⟩) ≫ (compIso u v).inv =
        (Submodule.Quotient.mk (compMor₂ u v) :
          (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ ⟨cone v⟩) :=
      (compMk (X := ⟨cone (compZ0 _ _ _ v u)⟩) (Y := ⟨cone (compMor₁ u v)⟩) (Z := ⟨cone v⟩)
        (coneInrZ0 (compMor₁ u v)) (compInv u v)).trans
        (compHmkEq' _ _ (compInv_coneInr u v))
    change (Submodule.Quotient.mk (compMor₂ u v) :
          (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ ⟨cone v⟩) ≫ (compIso u v).hom =
      𝟙 _ ≫ (Submodule.Quotient.mk (coneInrZ0 (compMor₁ u v)) :
          (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ ⟨cone (compMor₁ u v)⟩)
    refine Eq.trans ?_ (Category.id_comp _).symm
    exact ((congrArg (fun t => t ≫ (compIso u v).hom) e1.symm).trans (Category.assoc _ _ _)).trans
      ((congrArg _ (compIso u v).inv_hom_id).trans (Category.comp_id _))
  · rw [Iso.refl_hom]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact compHmkEq' (compZ0 _ _ _ (shiftZ0 (coneInrZ0 u) 1) (coneWZ0 v))
      (compZ0 _ _ _ (coneWZ0 (compMor₁ u v)) (compHom u v)) (coneW_compHom u v).symm

end Cohesive
