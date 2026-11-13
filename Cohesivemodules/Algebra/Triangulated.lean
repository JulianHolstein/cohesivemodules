import Cohesivemodules.Algebra.ConeCompTriangle
import Mathlib.CategoryTheory.Triangulated.Triangulated

set_option linter.style.header false

/-!
# Z2.g2: `Ho(P_A)` is triangulated

Blueprint item Z2.g (`blueprint/blueprint-tr.md` §3d), [B, §2.4], following the proof of
Mathlib's `IsTriangulated (HomotopyCategory C (ComplexShape.up ℤ))`: by `IsTriangulated.mk'` it
suffices to build an octahedron for composable representatives `u`, `v` and their cone
triangles; it is `Octahedron.mk [m₁] [m₂]` with `compTriangle_distinguished` (Z2.g1), and its
four squares hold exactly on representatives (`m₁ inr_u = inr_{uv} v`, `w_{uv} m₁ = w_u`,
`m₂ inr_{uv} = inr_v`, `u[1] w_{uv} = w_v m₂`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Pretriangulated

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- Z2.g2: a square with two identity isomorphisms commutes. -/
private theorem refl_comm {X Y : HoP 𝒜} (f : X ⟶ Y) :
    f ≫ (Iso.refl Y).hom = (Iso.refl X).hom ≫ f :=
  (Category.comp_id f).trans (Category.id_comp f).symm

/-- Z2.g2: the cone triangle of a closed map is distinguished (`Iso.refl`). -/
private theorem coneTriangle_mem {M N : CohesiveModule 𝒜}
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) : coneTriangle φ ∈ distTriang (HoP 𝒜) :=
  (mem_distTriang_iff 𝒜 _).2 ⟨_, _, φ, ⟨Iso.refl _⟩⟩

/-- Z2.g2: typing helper, the class of a closed map as a morphism `⟨M⟩ ⟶ ⟨N⟩` of `Ho(P_A)`. -/
private abbrev cl {M N : CohesiveModule 𝒜} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) :
    (⟨M⟩ : HoP 𝒜) ⟶ ⟨N⟩ := Submodule.Quotient.mk φ

/-- Z2.g2: octahedron square 1, `m₁ ∘ inr_u = inr_{uv} ∘ v` (on representatives). -/
private theorem oct_comm₁ {X₁ X₂ X₃ : CohesiveModule 𝒜}
    (u : Z0 X₁.toQuasiCohesive X₂.toQuasiCohesive) (v : Z0 X₂.toQuasiCohesive X₃.toQuasiCohesive) :
    (Submodule.Quotient.mk (coneInrZ0 u) : (⟨X₂⟩ : HoP 𝒜) ⟶ ⟨cone u⟩) ≫
      (Submodule.Quotient.mk (compMor₁ u v) : (⟨cone u⟩ : HoP 𝒜) ⟶ ⟨cone (compZ0 _ _ _ v u)⟩) =
    (Submodule.Quotient.mk v : (⟨X₂⟩ : HoP 𝒜) ⟶ ⟨X₃⟩) ≫
      cl 𝒜 (coneInrZ0 (compZ0 _ _ _ v u)) :=
  (compMk _ _).trans ((compHmkEq' _ _ (coneMap_coneInr u (compZ0 _ _ _ v u) (idZ0 _) v 0
    (Submodule.zero_mem _) (compMor₁_cond u v))).trans (compMk _ _).symm)

/-- Z2.g2: octahedron square 2, `w_{uv} ∘ m₁ = w_u` (on representatives). -/
private theorem oct_comm₂ {X₁ X₂ X₃ : CohesiveModule 𝒜}
    (u : Z0 X₁.toQuasiCohesive X₂.toQuasiCohesive) (v : Z0 X₂.toQuasiCohesive X₃.toQuasiCohesive) :
    (Submodule.Quotient.mk (compMor₁ u v) : (⟨cone u⟩ : HoP 𝒜) ⟶ ⟨cone (compZ0 _ _ _ v u)⟩) ≫
      (show (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ (⟨X₁⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from
        Submodule.Quotient.mk (coneWZ0 (compZ0 _ _ _ v u))) =
    (show (⟨cone u⟩ : HoP 𝒜) ⟶ (⟨X₁⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from Submodule.Quotient.mk (coneWZ0 u)) := by
  refine (compMk _ _).trans (compHmkEq' _ _ (LinearMap.ext fun z => ?_))
  have hf := LinearMap.congr_fun (coneFst_coneMap u (compZ0 _ _ _ v u) (idZ0 _) v 0
    (Submodule.zero_mem _) (compMor₁_cond u v)) z
  change -(shiftIota 𝒜 X₁.Q 1).symm (coneFst X₁ X₃ ((compMor₁ u v).1 z)) =
    -(shiftIota 𝒜 X₁.Q 1).symm (coneFst X₁ X₂ z)
  exact congrArg (fun t => -(shiftIota 𝒜 X₁.Q 1).symm t) hf

/-- Z2.g2: octahedron square 3, `m₂ ∘ inr_{uv} = inr_v` (on representatives). -/
private theorem oct_comm₃ {X₁ X₂ X₃ : CohesiveModule 𝒜}
    (u : Z0 X₁.toQuasiCohesive X₂.toQuasiCohesive) (v : Z0 X₂.toQuasiCohesive X₃.toQuasiCohesive) :
    cl 𝒜 (coneInrZ0 (compZ0 _ _ _ v u)) ≫
      (Submodule.Quotient.mk (compMor₂ u v) : (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ ⟨cone v⟩) =
    cl 𝒜 (coneInrZ0 v) :=
  (compMk _ _).trans (compHmkEq' _ _ ((coneMap_coneInr (compZ0 _ _ _ v u) v u (idZ0 _) 0
    (Submodule.zero_mem _) (compMor₂_cond u v)).trans (LinearMap.comp_id _)))

/-- Z2.g2: octahedron square 4, `u[1] ∘ w_{uv} = w_v ∘ m₂` (on representatives). -/
private theorem oct_comm₄ {X₁ X₂ X₃ : CohesiveModule 𝒜}
    (u : Z0 X₁.toQuasiCohesive X₂.toQuasiCohesive) (v : Z0 X₂.toQuasiCohesive X₃.toQuasiCohesive) :
    (show (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ (⟨X₁⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from
        Submodule.Quotient.mk (coneWZ0 (compZ0 _ _ _ v u))) ≫
      (shiftFunctor (HoP 𝒜) (1 : ℤ)).map
        (Submodule.Quotient.mk u : (⟨X₁⟩ : HoP 𝒜) ⟶ ⟨X₂⟩) =
    (Submodule.Quotient.mk (compMor₂ u v) : (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ ⟨cone v⟩) ≫
      (show (⟨cone v⟩ : HoP 𝒜) ⟶ (⟨X₂⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from Submodule.Quotient.mk (coneWZ0 v)) :=
  by
  refine (compMk (coneWZ0 (compZ0 _ _ _ v u)) (shiftZ0 u 1)).trans
    ((compHmkEq' _ _ (LinearMap.ext fun z => ?_)).trans (compMk _ _).symm)
  have hf := LinearMap.congr_fun (coneFst_coneMap (compZ0 _ _ _ v u) v u (idZ0 _) 0
    (Submodule.zero_mem _) (compMor₂_cond u v)) z
  change (shiftIota 𝒜 X₂.Q 1).symm (u.1 ((shiftIota 𝒜 X₁.Q 1)
      (-(shiftIota 𝒜 X₁.Q 1).symm (coneFst X₁ X₃ z)))) =
    -(shiftIota 𝒜 X₂.Q 1).symm (coneFst X₂ X₃ ((compMor₂ u v).1 z))
  simp only [map_neg, LinearEquiv.apply_symm_apply]
  exact congrArg (fun t => -(shiftIota 𝒜 X₂.Q 1).symm t) hf.symm

/-- **Z2.g2.** [B, §2.4], [BK]. `Ho(P_A)` is a triangulated category: the pretriangulated
structure of Z2.f4 satisfies the octahedron axiom. Generic in `GCDga` (so it also applies to the
curved `HoP` of Z3). -/
instance : IsTriangulated (HoP 𝒜) := by
  refine IsTriangulated.mk' ?_
  rintro ⟨X₁⟩ ⟨X₂⟩ ⟨X₃⟩ u' v'
  obtain ⟨u, rfl⟩ : ∃ u : Z0 X₁.toQuasiCohesive X₂.toQuasiCohesive,
      Submodule.Quotient.mk u = u' := Submodule.Quotient.mk_surjective _ u'
  obtain ⟨v, rfl⟩ : ∃ v : Z0 X₂.toQuasiCohesive X₃.toQuasiCohesive,
      Submodule.Quotient.mk v = v' := Submodule.Quotient.mk_surjective _ v'
  refine ⟨_, _, _, _, _, _, Submodule.Quotient.mk u, Submodule.Quotient.mk v, Iso.refl _,
    Iso.refl _, Iso.refl _, refl_comm 𝒜 _, refl_comm 𝒜 _,
    Submodule.Quotient.mk (coneInrZ0 u),
    show (⟨cone u⟩ : HoP 𝒜) ⟶ (⟨X₁⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from Submodule.Quotient.mk (coneWZ0 u),
    coneTriangle_mem 𝒜 u,
    Submodule.Quotient.mk (coneInrZ0 v),
    show (⟨cone v⟩ : HoP 𝒜) ⟶ (⟨X₂⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from Submodule.Quotient.mk (coneWZ0 v),
    coneTriangle_mem 𝒜 v,
    Submodule.Quotient.mk (coneInrZ0 (compZ0 _ _ _ v u)),
    show (⟨cone (compZ0 _ _ _ v u)⟩ : HoP 𝒜) ⟶ (⟨X₁⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from
      Submodule.Quotient.mk (coneWZ0 (compZ0 _ _ _ v u)),
    coneTriangle_mem 𝒜 (compZ0 _ _ _ v u), ⟨?_⟩⟩
  refine Triangulated.Octahedron.mk (Submodule.Quotient.mk (compMor₁ u v))
    (Submodule.Quotient.mk (compMor₂ u v)) ?_ ?_ ?_ ?_ ?_
  · exact oct_comm₁ 𝒜 u v
  · exact oct_comm₂ 𝒜 u v
  · exact oct_comm₃ 𝒜 u v
  · exact oct_comm₄ 𝒜 u v
  · exact compTriangle_distinguished u v

end Cohesive
