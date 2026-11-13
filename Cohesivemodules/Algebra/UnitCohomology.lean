import Cohesivemodules.Algebra.UnitModule
import Cohesivemodules.Algebra.HomShift

set_option linter.style.header false

/-!
# K4.b: morphisms from the unit module into its shifts are the cohomology of `(𝒜, d)`

Blueprint item K4.b (`blueprint/blueprint-tr.md` §4 (ii)–(iii); §11 v1.16). For a dga `𝒜` with
zero curvature and its unit module `U` (`unitCohesive`, `Tot(U) ≅ A` by `unitEquiv`):
* `DgaCohomology 𝒜 n = Zⁿ / Bⁿ` with `Zⁿ = 𝒜ⁿ ∩ ker d`, `Bⁿ = d(𝒜ⁿ⁻¹)` (ℤ-indexed);
* `Hom^n(U, U) ≅ 𝒜ⁿ`: `φ ↦ φ(1 ⊗ gen)` (`unitEval`), inverse `u ↦ (x ↦ u·x)` (`unitMulOp`, left
  multiplication under `unitEquiv`), with `δ ↔ d` and **no sign** (`unitEval_δ`): `𝕏(1 ⊗ gen) = 0`,
  so `(δφ)(1 ⊗ gen) = 𝕏(φ(1 ⊗ gen))`;
* `unitCohomologyEquiv : Hⁿ Hom^•(U, U) ≃ₗ[k] DgaCohomology 𝒜 n`;
* **`unitShiftEquiv : (U ⟶ U⟦n⟧) ≃ₗ[k] DgaCohomology 𝒜 n`** in `Ho(P_A)` (with K4.a's
  `homShiftEquiv`); for the Dolbeault algebra this is K4 (`Forms/DolbeaultCohomology.lean`);
* sanity: `DgaCohomology 𝒜 n = 0` for `n < 0` and `n > N`, and `DgaCohomology 𝒜 0 ≅ 𝒜⁰ ∩ ker d`.

Why left multiplication: for `φ ∈ Hom^n` and `α ∈ 𝒜^j`, `φ(α ⊗ gen) = (−1)^{nj} α·u = u·α`
(graded commutativity), with `u = φ(1 ⊗ gen) ∈ 𝒜ⁿ`. Then
`δφ(x) = d(ux) − (−1)^n u·dx = (du)·x`.

⚠ Split of the blueprint's single file `Algebra/UnitModule.lean` into `UnitModule` (the module) and
`UnitCohomology` (this file), for size.
-/

noncomputable section

namespace Cohesive

open CategoryTheory UnitMod

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-! ## The cohomology of `(𝒜, d)` -/

/-- **K4.b.** The `n`-cocycles of `(𝒜, d)`: `Zⁿ = 𝒜ⁿ ∩ ker d`. -/
def DgaZ (n : ℤ) : Submodule k A := 𝒜 n ⊓ LinearMap.ker (GCDga.d (𝒜 := 𝒜))

/-- **K4.b.** The `n`-coboundaries of `(𝒜, d)`: `Bⁿ = d(𝒜ⁿ⁻¹)`. -/
def DgaB (n : ℤ) : Submodule k A := (𝒜 (n - 1)).map (GCDga.d (𝒜 := 𝒜))

/-- K4.b: membership in `Zⁿ` (rfl). -/
theorem mem_DgaZ {n : ℤ} {a : A} : a ∈ DgaZ 𝒜 n ↔ a ∈ 𝒜 n ∧ GCDga.d (𝒜 := 𝒜) a = 0 :=
  Iff.rfl

/-- K4.b: coboundaries are cocycles. -/
theorem DgaB_le_DgaZ (n : ℤ) : DgaB 𝒜 n ≤ DgaZ 𝒜 n := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨?_, LinearMap.mem_ker.2 (GCDga.d_d _)⟩
  simpa using GCDga.d_mem (𝒜 := 𝒜) ha

/-- **K4.b.** The `n`-th cohomology of `(𝒜, d)`, `Hⁿ(𝒜, d) = Zⁿ / Bⁿ` (ℤ-indexed). For the
Dolbeault algebra this is `H^{0,n}_∂̄(X)`. -/
abbrev DgaCohomology (n : ℤ) : Type := DgaZ 𝒜 n ⧸ (DgaB 𝒜 n).comap (DgaZ 𝒜 n).subtype

/-- K4.b (sanity): `Hⁿ(𝒜, d) = 0` for `n < 0`. -/
theorem subsingleton_dgaCohomology_of_neg {n : ℤ} (hn : n < 0) :
    Subsingleton (DgaCohomology 𝒜 n) := by
  have : Subsingleton (DgaZ 𝒜 n) :=
    ⟨fun a b => Subtype.ext ((GCDga.eq_zero_of_neg 𝒜 hn a.2.1).trans
      (GCDga.eq_zero_of_neg 𝒜 hn b.2.1).symm)⟩
  infer_instance

/-- K4.b (sanity): `Hⁿ(𝒜, d) = 0` above the top degree, `n > N`. -/
theorem subsingleton_dgaCohomology_of_gt {n : ℤ} (hn : (GCDga.N 𝒜 : ℤ) < n) :
    Subsingleton (DgaCohomology 𝒜 n) := by
  have : Subsingleton (DgaZ 𝒜 n) :=
    ⟨fun a b => Subtype.ext ((GCDga.eq_zero_of_gt 𝒜 hn a.2.1).trans
      (GCDga.eq_zero_of_gt 𝒜 hn b.2.1).symm)⟩
  infer_instance

/-- K4.b: there are no coboundaries in degree `0` (`𝒜⁻¹ = 0`). -/
theorem DgaB_zero : DgaB 𝒜 0 = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [GCDga.eq_zero_of_neg 𝒜 (by omega) ha, map_zero]
  exact zero_mem _

/-- **K4.b (sanity).** `H⁰(𝒜, d) ≅ 𝒜⁰ ∩ ker d`: the quotient map is bijective in degree `0`. -/
def dgaCohomologyZeroEquiv : DgaCohomology 𝒜 0 ≃ₗ[k] DgaZ 𝒜 0 :=
  Submodule.quotEquivOfEqBot _ (by rw [DgaB_zero, Submodule.comap_bot, Submodule.ker_subtype])

/-- K4.b (sanity): a bijection onto the degree-`0` cocycles gives a bijection onto `H⁰(𝒜, d)`.
(Generic form, so that instance search runs over a general dga; on the Dolbeault algebra it
times out.) -/
def dgaCohomologyZeroEquivOf {B : Type} (f : B → DgaZ 𝒜 0) (hf : Function.Bijective f) :
    B ≃ DgaCohomology 𝒜 0 :=
  (Equiv.ofBijective f hf).trans (dgaCohomologyZeroEquiv 𝒜).symm.toEquiv

/-! ## `Hom^•(U, U) ≅ (𝒜, d)` -/

variable (hc : GCDga.c (𝒜 := 𝒜) = 0)

/-- **K4.b.** Evaluation at the generator: `φ ↦ φ(1 ⊗ gen)`, read in `A` through `unitEquiv`. -/
def unitEval : ((unitCohesive 𝒜 hc).T →ₗ[k] (unitCohesive 𝒜 hc).T) →ₗ[k] A :=
  ((unitEquiv 𝒜).toLinearMap.restrictScalars k) ∘ₗ
    LinearMap.applyₗ (Tot.tmul 𝒜 (UnitQ 𝒜) 1 (gen 𝒜))

/-- K4.b: formula for `unitEval` (rfl). -/
theorem unitEval_apply (φ : (unitCohesive 𝒜 hc).T →ₗ[k] (unitCohesive 𝒜 hc).T) :
    unitEval 𝒜 hc φ = unitEquiv 𝒜 (φ (Tot.tmul 𝒜 (UnitQ 𝒜) 1 (gen 𝒜))) := rfl

/-- **K4.b.** Left multiplication by `u ∈ A`, as an operator on `Tot(U) ≅ A`. -/
def unitMulOp : A →ₗ[k] ((unitCohesive 𝒜 hc).T →ₗ[k] (unitCohesive 𝒜 hc).T) :=
  LinearMap.llcomp k _ A _ ((unitEquiv 𝒜).symm.toLinearMap.restrictScalars k) ∘ₗ
    (LinearMap.lcomp k A ((unitEquiv 𝒜).toLinearMap.restrictScalars k)) ∘ₗ
      LinearMap.mul k A

/-- K4.b: formula for `unitMulOp` (rfl). -/
theorem unitMulOp_apply (u : A) (x : (unitCohesive 𝒜 hc).T) :
    unitMulOp 𝒜 hc u x = (unitEquiv 𝒜).symm (u * unitEquiv 𝒜 x) := rfl

/-- Left multiplication by a homogeneous `u` commutes with `a • -` up to the Koszul sign. -/
private theorem unitMulOp_smul_aux {n p : ℤ} {u a : A} (hu : u ∈ 𝒜 n) (ha : a ∈ 𝒜 p)
    (x : Tot 𝒜 (UnitQ 𝒜)) :
    (unitEquiv 𝒜).symm (u * unitEquiv 𝒜 (a • x)) =
      (n * p).negOnePow • a • (unitEquiv 𝒜).symm (u * unitEquiv 𝒜 x) := by
  apply (unitEquiv 𝒜).injective
  simp only [LinearEquiv.apply_symm_apply, Units.smul_def, map_zsmul, map_smul, smul_eq_mul]
  rw [← mul_assoc, GCDga.gcomm hu ha, smul_mul_assoc, mul_assoc]
  rw [Units.smul_def]

/-- K4.b: `unitMulOp u ∈ Hom^n(U, U)` for `u ∈ 𝒜ⁿ` (graded commutativity gives the sign
`φ(α·x) = (−1)^{n|α|} α·φ(x)`). -/
theorem unitMulOp_mem {n : ℤ} {u : A} (hu : u ∈ 𝒜 n) :
    unitMulOp 𝒜 hc u ∈ Hom (unitCohesive 𝒜 hc).toQuasiCohesive
      (unitCohesive 𝒜 hc).toQuasiCohesive n := by
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · have h1 : unitEquiv 𝒜 x ∈ 𝒜 m := (unitEquiv_mem_iff 𝒜 m x).1 hx
    rw [unitMulOp_apply]
    refine (unitEquiv_mem_iff 𝒜 (m + n) _).2 ?_
    rw [LinearEquiv.apply_symm_apply, add_comm]
    exact SetLike.GradedMul.mul_mem hu h1
  · exact unitMulOp_smul_aux 𝒜 hu ha x

/-- K4.b: `unitEval φ ∈ 𝒜ⁿ` for `φ ∈ Hom^n(U, U)`. -/
theorem unitEval_mem {n : ℤ} {φ : (unitCohesive 𝒜 hc).T →ₗ[k] (unitCohesive 𝒜 hc).T}
    (hφ : φ ∈ Hom (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n) :
    unitEval 𝒜 hc φ ∈ 𝒜 n := by
  have h0 : Tot.tmul 𝒜 (UnitQ 𝒜) 1 (gen 𝒜) ∈ totDeg 𝒜 (UnitQ 𝒜) 0 := by
    have := tmul_mem_totDeg (Q := UnitQ 𝒜) (SetLike.GradedOne.one_mem (A := 𝒜))
      (fun _ => 1 : UnitQ 𝒜 0)
    rw [zero_add] at this
    exact this
  have h1 := hφ.1 h0
  rw [zero_add] at h1
  exact (unitEquiv_mem_iff 𝒜 n _).1 h1

/-- K4.b: `unitEval (unitMulOp u) = u`. -/
theorem unitEval_unitMulOp (u : A) : unitEval 𝒜 hc (unitMulOp 𝒜 hc u) = u := by
  rw [unitEval_apply]
  change unitEquiv 𝒜 ((unitEquiv 𝒜).symm
    (u * unitEquiv 𝒜 (Tot.tmul 𝒜 (UnitQ 𝒜) 1 (gen 𝒜)))) = u
  rw [LinearEquiv.apply_symm_apply, unitEquiv_tmul, coef_gen]
  rw [show ((1 : 𝒜 0) : A) = 1 from rfl, mul_one, mul_one]

/-- A `k`-linear map on `Tot(U)` of degree `n` with `φ(1 ⊗ gen) = u` is left multiplication
by `u`, in terms of plain types. -/
private theorem unitMulOp_unitEval_aux {n : ℤ} {u : A} (hu : u ∈ 𝒜 n)
    {φ : Tot 𝒜 (UnitQ 𝒜) →ₗ[k] Tot 𝒜 (UnitQ 𝒜)}
    (hφ : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 (UnitQ 𝒜),
      φ (a • x) = (n * p).negOnePow • a • φ x)
    (hy : φ (Tot.tmul 𝒜 (UnitQ 𝒜) 1 (gen 𝒜)) = (unitEquiv 𝒜).symm u)
    (x : Tot 𝒜 (UnitQ 𝒜)) : (unitEquiv 𝒜).symm (u * unitEquiv 𝒜 x) = φ x := by
  have hy' : φ ((unitEquiv 𝒜).symm 1) = (unitEquiv 𝒜).symm u := by
    rw [unitEquiv_symm_apply]; exact hy
  have key : ∀ (q : ℤ) (a : A), a ∈ 𝒜 q →
      φ (a • (unitEquiv 𝒜).symm 1) = (unitEquiv 𝒜).symm (u * a) := by
    intro q a ha
    rw [hφ ha, hy', Units.smul_def, ← map_smul, ← map_zsmul]
    congr 1
    rw [smul_eq_mul, GCDga.gcomm hu ha, Units.smul_def]
  have all : ∀ a : A, φ (a • (unitEquiv 𝒜).symm 1) = (unitEquiv 𝒜).symm (u * a) := by
    intro a
    conv_lhs => rw [← GCDga.sum_proj 𝒜 a]
    conv_rhs => rw [← GCDga.sum_proj 𝒜 a]
    rw [Finset.sum_smul, map_sum, Finset.mul_sum, map_sum]
    exact Finset.sum_congr rfl fun q _ => key q _ (GCDga.proj_mem 𝒜 q a)
  have hx : x = unitEquiv 𝒜 x • (unitEquiv 𝒜).symm 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have := all (unitEquiv 𝒜 x)
  rw [← hx] at this
  exact this.symm

/-- K4.b: `unitMulOp (unitEval φ) = φ` for `φ ∈ Hom^n(U, U)`: a map of degree `n` is left
multiplication by its value on the generator. -/
theorem unitMulOp_unitEval {n : ℤ} {φ : (unitCohesive 𝒜 hc).T →ₗ[k] (unitCohesive 𝒜 hc).T}
    (hφ : φ ∈ Hom (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n) :
    unitMulOp 𝒜 hc (unitEval 𝒜 hc φ) = φ := by
  refine LinearMap.ext fun x => ?_
  have h := unitMulOp_unitEval_aux 𝒜 (unitEval_mem 𝒜 hc hφ) (φ := φ)
    (fun {q a} ha y => hφ.2 ha y)
    (LinearEquiv.symm_apply_apply (unitEquiv 𝒜) _).symm x
  exact h

/-- `𝕏(1 ⊗ gen) = 0` in the unit module. -/
private theorem unitX_gen : (unitGenData 𝒜).extend (Tot.tmul 𝒜 (UnitQ 𝒜) 1 (gen 𝒜)) = 0 := by
  rw [GenData.extend_tmul_one, unitGenData_θ, coef_gen,
    show ((1 : 𝒜 0) : A) = 1 from rfl, GCDga.d_one, Tot.zero_tmul]

/-- **K4.b.** `δ ↔ d` with no sign: `(δφ)(1 ⊗ gen) = d(φ(1 ⊗ gen))`, for every `k`-linear `φ`. -/
theorem unitEval_δ (n : ℤ) (φ : (unitCohesive 𝒜 hc).T →ₗ[k] (unitCohesive 𝒜 hc).T) :
    unitEval 𝒜 hc (δ (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n
      φ) = GCDga.d (𝒜 := 𝒜) (unitEval 𝒜 hc φ) := by
  have hX : (unitCohesive 𝒜 hc).X (Tot.tmul 𝒜 (UnitQ 𝒜) 1 (gen 𝒜)) = 0 := unitX_gen 𝒜
  have h : ∀ g : (unitCohesive 𝒜 hc).T, (unitCohesive 𝒜 hc).X g = 0 →
      (δ (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n φ) g =
      (unitCohesive 𝒜 hc).X (φ g) := by
    intro g hg
    rw [δ_apply]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [hg, map_zero, smul_zero, sub_zero]
  exact (congrArg (unitEquiv 𝒜) (h _ hX)).trans (unitEquiv_X 𝒜 hc _)

/-- K4.b: `δ(unitMulOp u) = unitMulOp (du)` for `u ∈ 𝒜ⁿ`. -/
theorem δ_unitMulOp {n : ℤ} {u : A} (hu : u ∈ 𝒜 n) :
    δ (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n
      (unitMulOp 𝒜 hc u) = unitMulOp 𝒜 hc (GCDga.d (𝒜 := 𝒜) u) := by
  rw [← unitMulOp_unitEval 𝒜 hc (δ_mem _ _ (unitMulOp_mem 𝒜 hc hu)), unitEval_δ,
    unitEval_unitMulOp]

/-! ## Cohomology -/

/-- K4.b: `unitEval` maps `Zⁿ(U, U)` into `Zⁿ(𝒜, d)`. -/
theorem unitEval_mem_DgaZ {n : ℤ} {φ : (unitCohesive 𝒜 hc).T →ₗ[k] (unitCohesive 𝒜 hc).T}
    (hφ : φ ∈ HomZ (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n) :
    unitEval 𝒜 hc φ ∈ DgaZ 𝒜 n := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
  refine ⟨unitEval_mem 𝒜 hc h1, LinearMap.mem_ker.2 ?_⟩
  rw [← unitEval_δ 𝒜 hc n φ, LinearMap.mem_ker.1 h2, map_zero]

/-- K4.b: `unitEval` maps `Bⁿ(U, U)` into `Bⁿ(𝒜, d)`. -/
theorem unitEval_mem_DgaB {n : ℤ} {φ : (unitCohesive 𝒜 hc).T →ₗ[k] (unitCohesive 𝒜 hc).T}
    (hφ : φ ∈ HomB (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n) :
    unitEval 𝒜 hc φ ∈ DgaB 𝒜 n := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact ⟨unitEval 𝒜 hc ψ, unitEval_mem 𝒜 hc hψ, (unitEval_δ 𝒜 hc _ ψ).symm⟩

/-- K4.b: `unitMulOp` maps `Zⁿ(𝒜, d)` into `Zⁿ(U, U)`. -/
theorem unitMulOp_mem_HomZ {n : ℤ} {u : A} (hu : u ∈ DgaZ 𝒜 n) :
    unitMulOp 𝒜 hc u ∈
      HomZ (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n := by
  refine Submodule.mem_inf.2 ⟨unitMulOp_mem 𝒜 hc hu.1, LinearMap.mem_ker.2 ?_⟩
  rw [δ_unitMulOp 𝒜 hc hu.1, LinearMap.mem_ker.1 hu.2, map_zero]

/-- K4.b: `unitMulOp` maps `Bⁿ(𝒜, d)` into `Bⁿ(U, U)`. -/
theorem unitMulOp_mem_HomB {n : ℤ} {u : A} (hu : u ∈ DgaB 𝒜 n) :
    unitMulOp 𝒜 hc u ∈
      HomB (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n := by
  obtain ⟨a, ha, rfl⟩ := hu
  exact ⟨unitMulOp 𝒜 hc a, unitMulOp_mem 𝒜 hc ha, δ_unitMulOp 𝒜 hc ha⟩

/-- **K4.b.** `[φ] ↦ [φ(1 ⊗ gen)]` on cohomology. -/
def unitEvalH (n : ℤ) :
    HomCohomology (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n →ₗ[k]
      DgaCohomology 𝒜 n :=
  Submodule.mapQ _ _ ((unitEval 𝒜 hc).restrict fun _ hφ => unitEval_mem_DgaZ 𝒜 hc hφ)
    fun _ hφ => unitEval_mem_DgaB 𝒜 hc hφ

/-- **K4.b.** `[u] ↦ [u · −]` on cohomology. -/
def unitMulOpH (n : ℤ) :
    DgaCohomology 𝒜 n →ₗ[k]
      HomCohomology (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n :=
  Submodule.mapQ _ _ ((unitMulOp 𝒜 hc).restrict fun _ hu => unitMulOp_mem_HomZ 𝒜 hc hu)
    fun _ hu => unitMulOp_mem_HomB 𝒜 hc hu

/-- K4.b: the two maps are mutually inverse (first composite). -/
theorem unitMulOpH_comp (n : ℤ) : unitMulOpH 𝒜 hc n ∘ₗ unitEvalH 𝒜 hc n = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun φ => ?_)
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (unitMulOp_unitEval 𝒜 hc φ.2.1)

/-- K4.b: the two maps are mutually inverse (second composite). -/
theorem unitEvalH_comp (n : ℤ) : unitEvalH 𝒜 hc n ∘ₗ unitMulOpH 𝒜 hc n = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (unitEval_unitMulOp 𝒜 hc u.1)

/-- **K4.b.** `Hⁿ Hom^•(U, U) ≃ₗ[k] Hⁿ(𝒜, d)`, `[φ] ↦ [φ(1 ⊗ gen)]`. -/
def unitCohomologyEquiv (n : ℤ) :
    HomCohomology (unitCohesive 𝒜 hc).toQuasiCohesive (unitCohesive 𝒜 hc).toQuasiCohesive n ≃ₗ[k]
      DgaCohomology 𝒜 n :=
  LinearEquiv.ofLinearMap (unitEvalH 𝒜 hc n) (unitMulOpH 𝒜 hc n) (unitEvalH_comp 𝒜 hc n)
    (unitMulOpH_comp 𝒜 hc n)

/-- **K4.b.** The unit module `U = 𝒜` as an object of `Ho(P_A)` (zero curvature). -/
def unitHoP : HoP 𝒜 := ⟨unitCohesive 𝒜 hc⟩

/-- **K4.b.** `Hom_{Ho(P_A)}(U, U⟦n⟧) ≃ₗ[k] Hⁿ(𝒜, d)`, `[φ] ↦ [(ι_n ∘ φ)(1 ⊗ gen)]` (K4.a's
`homShiftEquiv` followed by `unitCohomologyEquiv`). [B, §2.4]; blueprint §9 K4 for a general
dga with zero curvature. -/
def unitShiftEquiv (n : ℤ) :
    (unitHoP 𝒜 hc ⟶ (shiftFunctor (HoP 𝒜) n).obj (unitHoP 𝒜 hc)) ≃ₗ[k] DgaCohomology 𝒜 n :=
  (homShiftEquiv (unitHoP 𝒜 hc) (unitHoP 𝒜 hc) n).trans (unitCohomologyEquiv 𝒜 hc n)

/-- K4.b (sanity): a bijection `f : B → Z⁰(𝒜, d)` gives `(U ⟶ U⟦0⟧) ≃ B`. (Generic form, so that
instance search runs over a general dga.) -/
def unitShiftZeroEquivOf {B : Type} (f : B → DgaZ 𝒜 0) (hf : Function.Bijective f) :
    (unitHoP 𝒜 hc ⟶ (shiftFunctor (HoP 𝒜) (0 : ℤ)).obj (unitHoP 𝒜 hc)) ≃ B :=
  (unitShiftEquiv 𝒜 hc 0).toEquiv.trans (dgaCohomologyZeroEquivOf 𝒜 f hf).symm

end Cohesive
