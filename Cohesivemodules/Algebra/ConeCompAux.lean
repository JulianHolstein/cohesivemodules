import Cohesivemodules.Algebra.Pretriangulated

set_option linter.style.header false

/-!
# Z2.g1: generic helpers for `ConeComp`

Blueprint item Z2.g (`blueprint/blueprint-tr.md` §3d). Statement-independent helpers used in
`Algebra/ConeComp.lean`: `comp_mem` and `δ_comp` with the degree given up to an equation (to avoid
defeq checks on large terms), `δ inl = inr ∘ m` for a map `m` between two cones in generic form,
the abstract algebra behind `compHom ∘ compInv − id = δH`, and the classes of closed maps in
`H⁰` (copies of the private helpers of `ConeRotate.lean` and `ConeShift.lean`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- Z2.g1: `comp_mem` with the degree given up to a proof of `m + n = s` (avoids defeq checks). -/
theorem comp_mem_eq {M₁ M₂ M₃ : QuasiCohesive 𝒜} {m n : ℤ} (s : ℤ) (hs : m + n = s)
    {ψ : M₂.T →ₗ[k] M₃.T} {φ : M₁.T →ₗ[k] M₂.T} (hψ : ψ ∈ Hom M₂ M₃ m)
    (hφ : φ ∈ Hom M₁ M₂ n) : ψ ∘ₗ φ ∈ Hom M₁ M₃ s := by
  subst hs
  exact comp_mem M₁ M₂ M₃ hψ hφ

/-- Z2.g1: `δ_comp` with the degree given up to a proof of `m + n = s`. -/
theorem δ_comp_eq {M₁ M₂ M₃ : QuasiCohesive 𝒜} (m n s : ℤ) (hs : m + n = s)
    (ψ : M₂.T →ₗ[k] M₃.T) (φ : M₁.T →ₗ[k] M₂.T) :
    δ M₁ M₃ s (ψ ∘ₗ φ) = δ M₂ M₃ m ψ ∘ₗ φ + m.negOnePow • (ψ ∘ₗ δ M₁ M₂ n φ) := by
  subst hs
  exact δ_comp M₁ M₂ M₃ m n ψ φ

/-- Z2.g1: `δ inl = inr ∘ m` for the cone of a map `m` between two cones (generic form, to avoid
unification depth problems when `m = m₁`). -/
theorem δ_inl_cone_aux {M N P : CohesiveModule 𝒜} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (ψ : Z0 M.toQuasiCohesive P.toQuasiCohesive)
    (m : Z0 (cone φ).toQuasiCohesive (cone ψ).toQuasiCohesive) :
    δ (cone φ).toQuasiCohesive (cone m).toQuasiCohesive (-1) (coneInl (cone φ) (cone ψ)) =
      coneInr (cone φ) (cone ψ) ∘ₗ m.1 := δ_coneInl m

/-- Z2.g1: the abstract algebra behind `compHom_compInv` (coordinates `a = inl fa + inr sa`,
`b = inl fb + inr sb`, `z = inl a + inr b`). -/
theorem alg_aux {A B D X₁' X₂' X₃' : Type} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup D] [Module k D] [AddCommGroup X₁']
    [Module k X₁'] [AddCommGroup X₂'] [Module k X₂'] [AddCommGroup X₃'] [Module k X₃']
    (inlD : A →ₗ[k] D) (inrD : B →ₗ[k] D) (inlU : X₁' →ₗ[k] A) (inrU : X₂' →ₗ[k] A)
    (inlUV : X₁' →ₗ[k] B) (inrUV : X₃' →ₗ[k] B) (a : A) (b : B) (z : D) (fa fb : X₁')
    (sa w : X₂') (sb : X₃') (hz : inlD a + inrD b = z) (ha : inlU fa + inrU sa = a)
    (hb : inlUV fb + inrUV sb = b) :
    inlD (inrU (sa + w)) + inrD (inrUV sb) - z =
      -(inrD (inlUV fb) - inlD (inrU w) + inlD (inlU fa)) := by
  subst ha hb hz
  simp only [map_add]
  abel

/-- Z2.g1: closed maps differing by a coboundary `δH`, `H ∈ Hom^{−1}`, agree in `H⁰`
(copy of the private `hmk_eq` of `ConeRotate.lean`). -/
theorem compHmkEq {M₁ M₂ : QuasiCohesive 𝒜} (f g : Z0 M₁ M₂) (H : M₁.T →ₗ[k] M₂.T)
    (hH : H ∈ Hom M₁ M₂ (-1)) (h : f.1 - g.1 = δ M₁ M₂ (-1) H) :
    (Submodule.Quotient.mk f : H0 M₁ M₂) = Submodule.Quotient.mk g := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact ⟨H, hH, h.symm⟩

/-- Z2.g1: equal closed maps have equal classes in `H⁰` (copy of the private `hmk_eq'` of
`ConeShift.lean`). -/
theorem compHmkEq' {M₁ M₂ : QuasiCohesive 𝒜} (f g : Z0 M₁ M₂) (h : f.1 = g.1) :
    (Submodule.Quotient.mk f : H0 M₁ M₂) = Submodule.Quotient.mk g :=
  congrArg Submodule.Quotient.mk (Subtype.ext h)

/-- Z2.g1: composition of classes of representatives (copy of the private `comp_mk'` of
`ConeShift.lean`). -/
theorem compMk {X Y Z : HoP 𝒜} (φ' : Z0 X.as.toQuasiCohesive Y.as.toQuasiCohesive)
    (ψ : Z0 Y.as.toQuasiCohesive Z.as.toQuasiCohesive) :
    (Submodule.Quotient.mk φ' : X ⟶ Y) ≫ (Submodule.Quotient.mk ψ : Y ⟶ Z) =
      (show X ⟶ Z from Submodule.Quotient.mk (compZ0 _ _ _ ψ φ')) := rfl

end Cohesive
