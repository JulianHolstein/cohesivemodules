import Cohesivemodules.Algebra.Dga
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Defs

set_option linter.style.header false

/-!
# A2: connections

Blueprint item A2. For a bounded graded-commutative, possibly curved dga `A` (A1; the curvature
plays no role here) and an `A⁰`-module `P`, a connection
 is an additive map `∇ : P → A¹ ⊗_{A⁰} P` with `∇(f e) = df ⊗ e + f ∇e` for `f ∈ A⁰`.

* A2.a: every finitely generated projective `A⁰`-module has a connection (`Connection.exists`).
* A2.b: the difference of two connections is `A⁰`-linear (`Connection.diff`).

Sources: connections on the components of a cohesive module are [B, after Def 2.3.1] and
[A, Rem 4.0.4] (`∇ : E → A¹ ⊗_{A⁰} E`, `𝕂`-linear, Leibniz rule). The existence of connections
on finitely generated projective modules is used in [B, proof of Lemma 3.2.8] ("pick an arbitrary
connection"); the construction `∇ = (1 ⊗ π) ∘ d^{⊕m} ∘ σ` below is the standard one.

## Deviations from the sources
* Left modules: `∇ : P → A¹ ⊗_{A⁰} P` (as in [A]); Block writes `E → E ⊗_A A¹` (conventions §3).
* We require `∇` to be additive and derive `k`-linearity from the Leibniz rule
  (`Connection.map_algebraMap_smul`), since `d` kills the scalars; the sources ask for
  `k`-linearity directly.
* The extension of `∇` to `A ⊗_{A⁰} P` by `∇(a ⊗ e) = da ⊗ e + (-1)^{|a|} a·∇e` is part of the
  construction of the operator `𝕏` of a cohesive module (A3.a, encoding 1 of conventions §4) and
  is done there.
-/

namespace Cohesive

open TensorProduct GCDga

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

namespace GCDga

/-- A2: `df ∈ A¹` for `f ∈ A⁰`, as an element of `piece 𝒜 1`. -/
def d0 (f : 𝒜 0) : piece 𝒜 1 := ⟨d (𝒜 := 𝒜) f, d_mem_one 𝒜 f.2⟩

/-- A2: the underlying element of `d0 f` is `df`. -/
@[simp] theorem coe_d0 (f : 𝒜 0) : (d0 𝒜 f : A) = d (𝒜 := 𝒜) f := rfl

/-- A2: `d0` is additive. -/
theorem d0_add (f g : 𝒜 0) : d0 𝒜 (f + g) = d0 𝒜 f + d0 𝒜 g :=
  Subtype.ext (map_add _ _ _)

/-- A2: `d0` vanishes on `0`. -/
@[simp] theorem d0_zero : d0 𝒜 0 = 0 := Subtype.ext (map_zero _)

/-- A2: the Leibniz rule on `A⁰`, written in `A¹` as an `A⁰`-module:
`d(fg) = g·df + f·dg`. -/
theorem d0_mul (f g : 𝒜 0) : d0 𝒜 (f * g) = g • d0 𝒜 f + f • d0 𝒜 g := by
  apply Subtype.ext
  simp only [coe_d0, Submodule.coe_add, coe_smul_piece]
  rw [show ((f * g : 𝒜 0) : A) = (f : A) * g from rfl, leibniz_zero 𝒜 f.2]
  congr 1
  exact (central 𝒜 g.2 _).symm

/-- A2: `d0` kills the scalars `k`. -/
@[simp] theorem d0_algebraMap (r : k) : d0 𝒜 (algebraMap k (𝒜 0) r) = 0 :=
  Subtype.ext (by simp [SetLike.GradeZero.coe_algebraMap])

end GCDga

/-- **A2.** A connection on an `A⁰`-module `P`: an additive map `∇ : P → A¹ ⊗_{A⁰} P` with
`∇(f e) = df ⊗ e + f ∇e` for `f ∈ A⁰`. [B, after Def 2.3.1], [A, Rem 4.0.4].

Deviations: left modules (conventions §3); additivity is assumed and `k`-linearity derived
(`map_algebraMap_smul`). -/
structure Connection (P : Type) [AddCommGroup P] [Module (𝒜 0) P] where
  /-- The underlying additive map. -/
  toAddMonoidHom : P →+ piece 𝒜 1 ⊗[𝒜 0] P
  /-- The Leibniz rule `∇(f e) = df ⊗ e + f ∇e`. -/
  leibniz' : ∀ (f : 𝒜 0) (e : P), toAddMonoidHom (f • e) = d0 𝒜 f ⊗ₜ e + f • toAddMonoidHom e

namespace Connection

variable {𝒜} {P : Type} [AddCommGroup P] [Module (𝒜 0) P]

/-- A2: a connection is a function `P → A¹ ⊗_{A⁰} P`. -/
instance : FunLike (Connection 𝒜 P) P (piece 𝒜 1 ⊗[𝒜 0] P) where
  coe D := D.toAddMonoidHom
  coe_injective D₁ D₂ h := by
    cases D₁; cases D₂; congr; exact DFunLike.coe_injective h

/-- A2: the Leibniz rule. -/
theorem leibniz (D : Connection 𝒜 P) (f : 𝒜 0) (e : P) : D (f • e) = d0 𝒜 f ⊗ₜ e + f • D e :=
  D.leibniz' f e

/-- A2: a connection is additive. -/
@[simp] theorem map_add (D : Connection 𝒜 P) (e e' : P) : D (e + e') = D e + D e' :=
  D.toAddMonoidHom.map_add e e'

/-- A2: a connection maps `0` to `0`. -/
@[simp] theorem map_zero (D : Connection 𝒜 P) : D 0 = 0 := D.toAddMonoidHom.map_zero

/-- A2: a connection is `k`-linear: it commutes with the scalars `k` (acting through `A⁰`). -/
theorem map_algebraMap_smul (D : Connection 𝒜 P) (r : k) (e : P) :
    D (algebraMap k (𝒜 0) r • e) = algebraMap k (𝒜 0) r • D e := by
  rw [leibniz, d0_algebraMap, zero_tmul, zero_add]

/-- **A2.b.** The difference of two connections is `A⁰`-linear. -/
def diff (D₁ D₂ : Connection 𝒜 P) : P →ₗ[𝒜 0] piece 𝒜 1 ⊗[𝒜 0] P where
  toFun e := D₁ e - D₂ e
  map_add' e e' := by simp only [map_add]; abel
  map_smul' f e := by simp only [leibniz, RingHom.id_apply, smul_sub]; abel

/-- A2.b: formula for `diff`. -/
@[simp] theorem diff_apply (D₁ D₂ : Connection 𝒜 P) (e : P) : diff D₁ D₂ e = D₁ e - D₂ e := rfl

/-- The connection `e ↦ Σ_i d(σ(e)_i) ⊗ sᵢ` built from generators `s` of `P` and a section `σ` of
`(A⁰)ⁿ → P`, `f ↦ Σ fᵢ sᵢ`. -/
def ofSection {n : ℕ} (s : Fin n → P) (σ : P →ₗ[𝒜 0] Fin n → 𝒜 0)
    (hσ : Fintype.linearCombination (𝒜 0) s ∘ₗ σ = LinearMap.id) : Connection 𝒜 P where
  toAddMonoidHom :=
    { toFun e := ∑ i, d0 𝒜 (σ e i) ⊗ₜ s i
      map_zero' := by simp
      map_add' e e' := by simp [d0_add, add_tmul, Finset.sum_add_distrib] }
  leibniz' f e := by
    have he : ∑ i, σ e i • s i = e := by
      simpa [Fintype.linearCombination_apply] using LinearMap.congr_fun hσ e
    have h1 : ∑ i, σ e i • (d0 𝒜 f ⊗ₜ[𝒜 0] s i) = d0 𝒜 f ⊗ₜ e := by
      conv_rhs => rw [← he]
      rw [tmul_sum]
      simp only [tmul_smul]
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul, Pi.smul_apply, smul_eq_mul,
      d0_mul, add_tmul, Finset.sum_add_distrib, ← smul_tmul', Finset.smul_sum, h1]

/-- **A2.a.** Every finitely generated projective `A⁰`-module has a connection.
Proof: choose generators `s : Fin n → P` and a section `σ` of `(A⁰)ⁿ → P` (projectivity); then
`∇ = (1 ⊗ π) ∘ d^{⊕n} ∘ σ` (`ofSection`). Used in [B, proof of Lemma 3.2.8]. -/
theorem exists_connection [Module.Finite (𝒜 0) P] [Module.Projective (𝒜 0) P] :
    Nonempty (Connection 𝒜 P) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := 𝒜 0) (M := P)
  have hπ : Function.Surjective (Fintype.linearCombination (𝒜 0) s) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hs]
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property _ LinearMap.id hπ
  exact ⟨ofSection s σ hσ⟩

end Connection

end Cohesive
