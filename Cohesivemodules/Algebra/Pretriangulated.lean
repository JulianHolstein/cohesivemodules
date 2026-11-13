import Cohesivemodules.Algebra.ConeShift
import Cohesivemodules.Algebra.HoPZero

set_option linter.style.header false

/-!
# Z2.f4: `Ho(P_A)` is pretriangulated

Blueprint item Z2.f (`blueprint/blueprint-tr.md` §3c, "Instance"), [B, §2.4]. Assembles the
`Pretriangulated (HoP 𝒜)` instance from Z2.f1–f3, copying the proof of Mathlib's instance on
`HomotopyCategory C (ComplexShape.up ℤ)`: inverse rotations are distinguished because
`T.invRotate ≅ (T.rotate.rotate)⟦−1⟧` (`invRotateIsoRotateRotateShiftFunctorNegOne`), and then
`T.rotate ∈ dist → T ∈ dist` by the unit of `triangleRotation`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Pretriangulated

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- **Z2.f4.** Inverse rotations of distinguished triangles of `Ho(P_A)` are distinguished
(as Mathlib's `HomotopyCategory.Pretriangulated.invRotate_distinguished_triangle'`). -/
theorem invRotate_distinguished' (T : Triangle (HoP 𝒜)) (hT : T ∈ distinguishedTriangles 𝒜) :
    T.invRotate ∈ distinguishedTriangles 𝒜 :=
  isomorphic_distinguished _
    (shift_distinguished _ (rotate_distinguished' _ (rotate_distinguished' _ hT)) _) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

/-- **Z2.f4.** A triangle of `Ho(P_A)` is distinguished iff its rotation is (the
`rotate_distinguished_triangle` axiom of `Pretriangulated`). -/
theorem rotate_distinguished_iff (T : Triangle (HoP 𝒜)) :
    T ∈ distinguishedTriangles 𝒜 ↔ T.rotate ∈ distinguishedTriangles 𝒜 := by
  constructor
  · exact rotate_distinguished' T
  · intro hT
    exact isomorphic_distinguished _ (invRotate_distinguished' 𝒜 T.rotate hT) _
      ((triangleRotation _).unitIso.app T)

/-- **Z2.f4.** [B, §2.4], [BK]. `Ho(P_A)` is a pretriangulated category: distinguished triangles
are those isomorphic to cone triangles `M →[φ] N →[inr] C(φ) →[w_φ] M⟦1⟧` (Z2.f1). Shift as
in Z2.b (`HasShift (HoP 𝒜) ℤ`, no signs on objects; conventions §3). -/
instance : Pretriangulated (HoP 𝒜) where
  distinguishedTriangles := distinguishedTriangles 𝒜
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_iff 𝒜
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

/-- **Z2.f4.** The distinguished triangles of the instance are the cone-triangle class (`rfl`). -/
theorem mem_distTriang_iff (T : Triangle (HoP 𝒜)) :
    T ∈ distTriang (HoP 𝒜) ↔ T ∈ distinguishedTriangles 𝒜 := Iff.rfl

end Cohesive
