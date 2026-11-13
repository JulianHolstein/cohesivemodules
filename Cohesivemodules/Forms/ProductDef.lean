-- FROZEN (gate 3, 26 Oct 2026; F5 definitions, in the main statement). Do not edit without approval.
import Cohesivemodules.Forms.FibreDef
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

set_option linter.style.header false

/-!
# F5: the product on the total fibre `Λ^{0,•}(E)` (definitions)

Blueprint item F5 (conventions §6). This file holds the definitions of F5 that the main
statement depends on, with their basic API and the declarations their constructions need; it
will be frozen at gate 3. The results (homogeneous products, the Laplace formula F5.a,
continuity of the product) are in `Cohesivemodules/Forms/Product.lean`.

Definitions: `TotFibre` with its `NormedAddCommGroup`/`NormedSpace ℂ` instances,
`DolbeaultFibre.cast`, `TotFibre.ofDeg`, `TotFibre.extToTotFibre`, `TotFibre.extEquivTotFibre`,
and the instances `Mul`, `One`, `Pow _ ℕ`, `NatCast`, `IntCast`, `Ring`, `Algebra ℂ` on
`TotFibre E` (the multiplication transported along `Φ_tot` from the exterior algebra,
⚠ blueprint F5: replaces a hand-built shuffle product).

## Deviations
* The total fibre is indexed by `Fin (n + 1)`; `Λ^{0,q} = 0` for `q > n` (F2.c), so nothing is
  lost.
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **F5.** The total fibre `Λ^{0,•}(E) = Π_{q ≤ n} Λ^{0,q}(E; ℂ)`, `n = dim_ℂ E`. A `def` (type
synonym of the product), so that its ring structure (transported from the exterior algebra)
is not an instance on a bare Pi type. -/
def TotFibre : Type := ∀ q : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E q ℂ

/-- F5: the normed group structure of the total fibre (product norm). -/
instance : NormedAddCommGroup (TotFibre E) :=
  inferInstanceAs (NormedAddCommGroup (∀ q : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E q ℂ))

/-- F5: the normed `ℂ`-space structure of the total fibre. -/
instance : NormedSpace ℂ (TotFibre E) :=
  inferInstanceAs (NormedSpace ℂ (∀ q : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E q ℂ))

variable {E}

/-- F5: transport of a form along an equality of degrees. -/
def DolbeaultFibre.cast {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {p q : ℕ} (h : p = q) :
    DolbeaultFibre E p F ≃ₗᵢ[ℂ] DolbeaultFibre E q F :=
  h ▸ LinearIsometryEquiv.refl ℂ _

/-- F5: `DolbeaultFibre.cast rfl` is the identity. -/
@[simp] theorem DolbeaultFibre.cast_rfl {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {p : ℕ}
    (α : DolbeaultFibre E p F) : DolbeaultFibre.cast rfl α = α := rfl

namespace TotFibre

/-! ## Homogeneous elements -/

/-- **F5.** A `q`-form as an element of the total fibre, homogeneous of degree `q` (zero if
`q > n`). -/
def ofDeg (q : ℕ) : DolbeaultFibre E q ℂ →ₗ[ℂ] TotFibre E where
  toFun α i := if h : q = (i : ℕ) then DolbeaultFibre.cast h α else 0
  map_add' α β := by
    funext i
    show (if h : q = (i : ℕ) then DolbeaultFibre.cast h (α + β) else 0) =
      (if h : q = (i : ℕ) then DolbeaultFibre.cast h α else 0) +
        (if h : q = (i : ℕ) then DolbeaultFibre.cast h β else 0)
    by_cases h : q = (i : ℕ)
    · simp only [h, ↓reduceDIte, map_add]
    · simp only [h, ↓reduceDIte, add_zero]
  map_smul' c α := by
    funext i
    show (if h : q = (i : ℕ) then DolbeaultFibre.cast h (c • α) else 0) =
      c • (if h : q = (i : ℕ) then DolbeaultFibre.cast h α else 0)
    by_cases h : q = (i : ℕ)
    · simp only [h, ↓reduceDIte, map_smul]
    · simp only [h, ↓reduceDIte, smul_zero]

/-! ## The bridge from the exterior algebra -/

variable [FiniteDimensional ℂ E]

variable (E) in
/-- F5: each `Λ^{0,q}(E; ℂ)` is finite-dimensional (via `Φ_q`, F2.b). -/
instance instFiniteDimensionalDolbeaultFibre (q : ℕ) : FiniteDimensional ℂ (DolbeaultFibre E q ℂ) :=
  LinearEquiv.finiteDimensional (extEquivFibre E q)

variable (E) in
/-- F5: the total fibre is finite-dimensional. -/
instance instFiniteDimensional : FiniteDimensional ℂ (TotFibre E) :=
  inferInstanceAs (FiniteDimensional ℂ (∀ q : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E q ℂ))

variable (E) in
/-- F5: `Φ_tot` as a linear map: the degree-`q` component of the exterior algebra
(`DirectSum.decompose` for `ExteriorAlgebra.gradedAlgebra`), then `Φ_q`. -/
def extToTotFibre : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E)) →ₗ[ℂ] TotFibre E :=
  LinearMap.pi fun i : Fin (Module.finrank ℂ E + 1) =>
    extToFibre E i ∘ₗ DirectSum.component ℂ ℕ (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) i ∘ₗ
      (DirectSum.decomposeLinearEquiv (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E)))).toLinearMap

/-- F5: `Φ_tot` is bijective (`Φ_q` bijective, F2.b; `⋀^q = 0` for `q > n`). -/
theorem extToTotFibre_bijective : Function.Bijective (extToTotFibre E) := by
  have hsub : ∀ i : ℕ, Module.finrank ℂ E < i →
      Subsingleton (⋀[ℂ]^i (Module.Dual ℂ (Conj E))) := fun i hi =>
    haveI := dolbeaultFibre_subsingleton (E := E) (F := ℂ) hi
    (extEquivFibre E i).toEquiv.subsingleton
  have happ : ∀ (x : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E)))
      (i : Fin (Module.finrank ℂ E + 1)),
      (show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from extToTotFibre E x) i =
        extToFibre E i (DirectSum.decompose (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) x i) :=
      fun _ _ => rfl
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : ∀ i : Fin (Module.finrank ℂ E + 1),
        extToFibre E i (DirectSum.decompose (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) x i) = 0 :=
      fun i => by rw [← happ, hx]; rfl
    have hd : DirectSum.decompose (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) x = 0 := by
      refine DFinsupp.ext fun i => ?_
      by_cases hi : i < Module.finrank ℂ E + 1
      · exact (extToFibre_bijective (E := E) i).1 ((hx' ⟨i, hi⟩).trans (_root_.map_zero _).symm)
      · exact @Subsingleton.elim _ (hsub i (by omega)) _ _
    have := congrArg (DirectSum.decompose (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E)))).symm hd
    simpa using this
  · intro y
    let d : DirectSum ℕ fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E)) :=
      ∑ i : Fin (Module.finrank ℂ E + 1), DirectSum.of (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E)))
        (i : ℕ) ((extEquivFibre E i).symm
          ((show ∀ i : Fin (Module.finrank ℂ E + 1), DolbeaultFibre E i ℂ from y) i))
    let x := (DirectSum.decomposeLinearEquiv (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E)))).symm d
    have hx : DirectSum.decompose (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) x = d :=
      (DirectSum.decomposeLinearEquiv (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E)))).apply_symm_apply d
    refine ⟨x, funext fun j => ?_⟩
    refine (happ x j).trans ?_
    rw [hx]
    have hd : d (j : ℕ) = (extEquivFibre E j).symm ((show ∀ i : Fin (Module.finrank ℂ E + 1),
        DolbeaultFibre E i ℂ from y) j) := by
      show (∑ i : Fin (Module.finrank ℂ E + 1), DirectSum.of
        (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) (i : ℕ) _) (j : ℕ) = _
      rw [DirectSum.sum_apply, Finset.sum_eq_single j]
      · rw [DirectSum.of_eq_same]
      · intro i _ hij
        rw [DirectSum.of_eq_of_ne]
        exact fun h => hij (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hd]
    exact (extEquivFibre E j).apply_symm_apply _

variable (E) in
/-- **F5.** `Φ_tot : ⋀_ℂ (Ē)^* ≃ Λ^{0,•}(E)`, componentwise `Φ_q` (F2.b) on the homogeneous
components of the exterior algebra. -/
def extEquivTotFibre : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E)) ≃ₗ[ℂ] TotFibre E :=
  LinearEquiv.ofBijective (extToTotFibre E) extToTotFibre_bijective

/-! ## The ring structure, transported along `Φ_tot` -/

/-- F5: the product `x * y = Φ_tot (Φ_tot⁻¹ x · Φ_tot⁻¹ y)` (wedge product). -/
instance : Mul (TotFibre E) :=
  ⟨fun x y => extEquivTotFibre E ((extEquivTotFibre E).symm x * (extEquivTotFibre E).symm y)⟩

/-- F5: the unit `Φ_tot 1`. -/
instance : One (TotFibre E) := ⟨extEquivTotFibre E 1⟩

/-- F5: powers, transported. -/
instance : Pow (TotFibre E) ℕ := ⟨fun x n => extEquivTotFibre E ((extEquivTotFibre E).symm x ^ n)⟩

/-- F5: natural-number casts, transported. -/
instance : NatCast (TotFibre E) := ⟨fun n => extEquivTotFibre E n⟩

/-- F5: integer casts, transported. -/
instance : IntCast (TotFibre E) := ⟨fun n => extEquivTotFibre E n⟩

/-- F5: formula for the product. -/
theorem mul_def (x y : TotFibre E) :
    x * y = extEquivTotFibre E ((extEquivTotFibre E).symm x * (extEquivTotFibre E).symm y) := rfl

/-- **F5.** The total fibre is a ring (the additive structure is the product structure; the
multiplication is the wedge product transported from the exterior algebra). -/
instance : Ring (TotFibre E) :=
  Function.Injective.ring (extEquivTotFibre E).symm (extEquivTotFibre E).symm.injective (map_zero _)
    ((extEquivTotFibre E).symm_apply_apply 1) (map_add _)
    (fun _ _ => (extEquivTotFibre E).symm_apply_apply _)
    (map_neg _) (map_sub _) (fun n x => map_nsmul _ n x) (fun n x => map_zsmul _ n x)
    (fun _ _ => (extEquivTotFibre E).symm_apply_apply _)
    (fun _ => (extEquivTotFibre E).symm_apply_apply _)
    (fun _ => (extEquivTotFibre E).symm_apply_apply _)

/-- **F5.** The total fibre is a `ℂ`-algebra. -/
instance : Algebra ℂ (TotFibre E) :=
  Algebra.ofModule
    (fun r x y => by
      rw [mul_def, mul_def, map_smul, smul_mul_assoc, map_smul])
    (fun r x y => by
      rw [mul_def, mul_def, map_smul, mul_smul_comm, map_smul])

end TotFibre

end Cohesive
