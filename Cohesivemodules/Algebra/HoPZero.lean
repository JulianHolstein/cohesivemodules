import Cohesivemodules.Algebra.CohesiveDef
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic

set_option linter.style.header false

/-!
# Z2.c: the zero object of Ho(P_A)

Blueprint item Z2.c (`blueprint/blueprint-tr.md` §5, §7). The cohesive module with all generators
`Q^p = 0` (and `𝕏 = 0`) has total module `A ⊗_{A⁰} 0 = 0`, so its identity is `0` in `Ho(P_A)`
and it is a zero object: `HasZeroObject (HoP 𝒜)`, needed for `Pretriangulated (HoP 𝒜)` (Z2.f).
-/

noncomputable section

namespace Cohesive

open DirectSum TensorProduct CategoryTheory Limits

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- Z2.c: the zero family of generators, `Q^p = 0` for all `p`. -/
abbrev zeroQ : ℤ → Type := fun _ => PUnit

/-- Z2.c: the total module of the zero family is `0`. -/
instance : Subsingleton (Tot 𝒜 zeroQ) := by
  change Subsingleton (A ⊗[𝒜 0] ⨁ p, zeroQ p)
  refine subsingleton_of_forall_eq 0 fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a e => rw [Subsingleton.elim e 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- **Z2.c.** The zero cohesive module: generators `Q^p = 0`, operator `𝕏 = 0`. Leibniz and
flatness hold because the total module is `0`; bounded, finite and projective trivially. -/
def zeroCohesive : CohesiveModule 𝒜 where
  Q := zeroQ
  X := 0
  X_mem _ := zero_mem _
  leibniz _ _ := Subsingleton.elim _ _
  flat _ := Subsingleton.elim _ _
  bounded := ⟨0, 0, fun _ _ => inferInstance⟩
  finite _ := inferInstance
  projective _ := inferInstance

/-- **Z2.c.** The zero object of `Ho(P_A)`. -/
def zeroHoP : HoP 𝒜 := ⟨zeroCohesive 𝒜⟩

/-- **Z2.c.** `zeroHoP` is a zero object: its identity is `0`, since its total module is `0`. -/
theorem isZero_zeroHoP : IsZero (zeroHoP 𝒜) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  change Submodule.Quotient.mk (idZ0 _) = Submodule.Quotient.mk 0
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (LinearMap.ext fun x => Subsingleton.elim (α := Tot 𝒜 zeroQ) _ _))

/-- **Z2.c.** `Ho(P_A)` has a zero object. -/
instance : HasZeroObject (HoP 𝒜) := ⟨⟨zeroHoP 𝒜, isZero_zeroHoP 𝒜⟩⟩

variable {𝒜} in
/-- Helper for K12b: under the contraction hypothesis the identity is a boundary. -/
private theorem id_mem_B0_of_contraction (Q : QuasiCohesive 𝒜) {φ : Q.T →ₗ[k] Q.T}
    (hφ : φ ∈ Hom Q Q (-1))
    (hN : (δ Q Q (-1) φ - LinearMap.id) ∘ₗ (δ Q Q (-1) φ - LinearMap.id) = 0) :
    (LinearMap.id : Q.T →ₗ[k] Q.T) ∈ B0 Q Q := by
  obtain ⟨T, hTdef⟩ : ∃ T, T = δ Q Q (-1) φ := ⟨_, rfl⟩
  rw [← hTdef] at hN
  have hT : T ∈ Hom Q Q 0 := by rw [hTdef]; simpa using δ_mem Q Q hφ
  have hTc : δ Q Q 0 T = 0 := by rw [hTdef]; simpa using δ_δ Q Q hφ
  have hid : (LinearMap.id : Q.T →ₗ[k] Q.T) ∈ Hom Q Q 0 := id_mem Q
  have hψ : (LinearMap.id - (T - LinearMap.id)) ∈ Hom Q Q 0 :=
    sub_mem hid (sub_mem hT hid)
  have hψc : δ Q Q 0 (LinearMap.id - (T - LinearMap.id)) = 0 := by
    rw [map_sub, map_sub, δ_id, hTc]
    simp
  have hTψ : T ∘ₗ (LinearMap.id - (T - LinearMap.id)) = LinearMap.id := by
    have h3 : T ∘ₗ (LinearMap.id - (T - LinearMap.id)) =
        LinearMap.id - (T - LinearMap.id) ∘ₗ (T - LinearMap.id) := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
      abel
    rw [h3, hN, sub_zero]
  refine ⟨φ ∘ₗ (LinearMap.id - (T - LinearMap.id)), ?_, ?_⟩
  · simpa using comp_mem Q Q Q hφ hψ
  · have h := δ_comp Q Q Q (-1) 0 φ (LinearMap.id - (T - LinearMap.id))
    rw [add_zero] at h
    rw [h, hψc, ← hTdef, hTψ]
    simp

variable {𝒜} in
/-- **K12b (contraction criterion).** Not in [B] (`Ho(P_A)` is [B, §2.4]). If a cohesive
module `M` has `φ ∈ Hom⁻¹(M, M)` such that `N = δφ − id` squares to zero, then `M` is a zero
object of `Ho(P_A)`: `δφ = id + N` is invertible with inverse `id − N` (closed), so
`id = δ(φ ∘ (id − N))` is a boundary. -/
theorem isZero_of_contraction (M : CohesiveModule 𝒜) {φ : M.T →ₗ[k] M.T}
    (hφ : φ ∈ Hom M.toQuasiCohesive M.toQuasiCohesive (-1))
    (hN : (δ M.toQuasiCohesive M.toQuasiCohesive (-1) φ - LinearMap.id) ∘ₗ
      (δ M.toQuasiCohesive M.toQuasiCohesive (-1) φ - LinearMap.id) = 0) :
    IsZero (HoP.mk M) := by
  have hmem := id_mem_B0_of_contraction M.toQuasiCohesive hφ hN
  refine (IsZero.iff_id_eq_zero _).2 ?_
  change Submodule.Quotient.mk (idZ0 M.toQuasiCohesive) = Submodule.Quotient.mk 0
  refine (Submodule.Quotient.eq _).2 ?_
  rw [Submodule.mem_comap]
  change (LinearMap.id - 0 : M.T →ₗ[k] M.T) ∈ _
  rwa [sub_zero]

end Cohesive
