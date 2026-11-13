import Cohesivemodules.Algebra.UnitCohomology
import Cohesivemodules.Forms.Dolbeault

set_option linter.style.header false

/-!
# K4.b: Dolbeault cohomology and K4

Blueprint item K4.b (`blueprint/blueprint-tr.md` §4 (iii); §11 v1.16), blueprint §9 K4. For a
complex manifold `X` with Dolbeault algebra `A = 𝒜_X(X)` (curvature `0`):
* `dolbeaultCohomology E X n = H^{0,n}_∂̄(X)`: closed `(0,n)`-forms modulo `∂̄` of `(0,n−1)`-forms
  (`DgaCohomology` of `dolbeault E X`, ℤ-indexed);
* `dolbeaultUnit E X`: the unit module `𝒜` (`Q = 𝒜⁰` in degree `0`, `𝕏 = ∂̄`) in `Ho(P_A)`;
* **`k4Equiv E X n : (𝒜 ⟶ 𝒜⟦n⟧) ≃ₗ[ℂ] H^{0,n}_∂̄(X)`** (K4; the check `K4` is in `ChecksForms`);
* sanity: `H^{0,n}_∂̄(X) = 0` for `n < 0` and `n > dim_ℂ E`; `H^{0,0}_∂̄(X) ≅ O(X)` through `ρ`
  (F12: `dolbeaultRhoU_injective`, `exists_dolbeaultRhoU_of_dbar_eq_zero`).

No hypotheses on `X` (compactness, Hausdorff) are needed: the statement is about global forms.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **K4.b.** Dolbeault cohomology `H^{0,n}_∂̄(X)`: `∂̄`-closed forms of degree `n` modulo `∂̄` of
forms of degree `n − 1`, the cohomology of the Dolbeault dga `𝒜_X(X)` (ℤ-indexed). -/
abbrev dolbeaultCohomology (n : ℤ) : Type := DgaCohomology (dolbeault E X) n

/-- K4.b: the Dolbeault algebra has curvature `0` (rfl). -/
theorem dolbeault_c : GCDga.c (𝒜 := dolbeault E X) = 0 := rfl

/-- **K4.b.** The unit module `𝒜` of the Dolbeault algebra (one generator in degree `0`,
`𝕏 = ∂̄`), as an object of `Ho(P_A)`. -/
def dolbeaultUnit : HoP (dolbeault E X) := unitHoP (dolbeault E X) (dolbeault_c E X)

/-- **K4.** [B, §2.4, §4.1]; blueprint §9 K4. `Hom_{Ho(P_A)}(𝒜, 𝒜⟦n⟧) ≃ₗ[ℂ] H^{0,n}_∂̄(X)` for
every `n : ℤ`, where `⟦n⟧` is the shift of Z2.b (`HasShift (HoP 𝒜) ℤ`). Explicitly
`[φ] ↦ [(ι_n ∘ φ)(1 ⊗ gen)]`. -/
def k4Equiv (n : ℤ) :
    (dolbeaultUnit E X ⟶ (shiftFunctor (HoP (dolbeault E X)) n).obj (dolbeaultUnit E X)) ≃ₗ[ℂ]
      dolbeaultCohomology E X n :=
  unitShiftEquiv (dolbeault E X) (dolbeault_c E X) n

/-- K4 (sanity): `H^{0,n}_∂̄(X) = 0` for `n < 0`. -/
theorem subsingleton_dolbeaultCohomology_of_neg {n : ℤ} (hn : n < 0) :
    Subsingleton (dolbeaultCohomology E X n) :=
  subsingleton_dgaCohomology_of_neg _ hn

/-- K4 (sanity): `H^{0,n}_∂̄(X) = 0` for `n > dim_ℂ E`. -/
theorem subsingleton_dolbeaultCohomology_of_gt {n : ℤ} (hn : (Module.finrank ℂ E : ℤ) < n) :
    Subsingleton (dolbeaultCohomology E X n) :=
  subsingleton_dgaCohomology_of_gt _ hn

/-- K4 (sanity): `ρ : O(X) → 𝒜⁰(X)` lands in the `∂̄`-closed forms of degree `0` (F12). -/
def holToDgaZ (f : (holSheaf E X).obj.obj (op ⊤)) : DgaZ (dolbeault E X) 0 :=
  ⟨(dolbeaultRhoU E ⊤ f : DolbeaultAlg E (⊤ : Opens X)),
    (mem_DgaZ _).2 ⟨(dolbeaultRhoU E ⊤ f).2, dbar_dolbeaultRhoU E ⊤ f⟩⟩

/-- K4 (sanity): `ρ` is a bijection from `O(X)` onto the `∂̄`-closed forms of degree `0` (F12:
injectivity and exactness at `𝒜⁰`). -/
theorem bijective_holToDgaZ : Function.Bijective (holToDgaZ E X) := by
  constructor
  · intro f g h
    apply dolbeaultRhoU_injective (E := E) (⊤ : Opens X)
    have h' := congrArg (fun z : DgaZ (dolbeault E X) 0 => (z.1 : DolbeaultAlg E (⊤ : Opens X))) h
    exact Subtype.ext h'
  · intro ⟨a, ha⟩
    obtain ⟨f, hf⟩ := exists_dolbeaultRhoU_of_dbar_eq_zero (E := E) (U := (⊤ : Opens X))
      ⟨a, ((mem_DgaZ _).1 ha).1⟩ ((mem_DgaZ _).1 ha).2
    exact ⟨f, Subtype.ext (congrArg (fun z : ↥(dolbeaultGrade E (⊤ : Opens X) 0) => z.1) hf)⟩

/-- **K4 (sanity).** `H^{0,0}_∂̄(X) ≅ O(X)` as sets, `f ↦ [ρ f]` (F12). Stated as a bijection
only: the additive structure through `dolbeaultRhoU` runs into slow unfolding of
`dolbeault E X` vs `dolbeaultGrade E ⊤` and is not needed for the sanity check. -/
def holCohomologyZeroEquiv : (holSheaf E X).obj.obj (op ⊤) ≃ dolbeaultCohomology E X 0 :=
  dgaCohomologyZeroEquivOf (dolbeault E X) (holToDgaZ E X) (bijective_holToDgaZ E X)

/-- **K4 (sanity, `n = 0`).** `Hom_{Ho(P_A)}(𝒜, 𝒜⟦0⟧) ≃ O(X)` (F12). -/
def k4ZeroEquiv :
    (dolbeaultUnit E X ⟶ (shiftFunctor (HoP (dolbeault E X)) (0 : ℤ)).obj (dolbeaultUnit E X)) ≃
      (holSheaf E X).obj.obj (op ⊤) :=
  unitShiftZeroEquivOf (dolbeault E X) (dolbeault_c E X) (holToDgaZ E X)
    (bijective_holToDgaZ E X)

end Cohesive
