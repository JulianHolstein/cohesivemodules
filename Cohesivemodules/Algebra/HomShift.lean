import Cohesivemodules.Algebra.ShiftHoP

set_option linter.style.header false

/-!
# K4.a: morphisms into a shift are cohomology classes of the Hom complex

Blueprint item K4.a (`blueprint/blueprint-tr.md` §4 (i); §11 v1.16). For cohesive modules `M`,
`N` and `n : ℤ`:
* `HomCohomology M N n = Zⁿ / Bⁿ` with `Zⁿ = Hom^n ∩ ker δ` and `Bⁿ = δ(Hom^{n−1})`, the `n`-th
  cohomology of the Hom complex (for `n = 0` this is `H0`);
* `homShiftEquiv M N n : (M ⟶ N⟦n⟧) ≃ₗ[k] HomCohomology M N n`, `[φ] ↦ [ι_n ∘ φ]`, with inverse
  `[ψ] ↦ [ι_n⁻¹ ∘ ψ]`. Mathlib's analogue is `HomComplexCohomology` / `homAddEquiv`.

`ι_n ∈ Hom^n(N[n], N)` is closed (`δ_shiftIota`), so `δ(ι_n ∘ φ) = (−1)^n ι_n ∘ δφ`
(`δ_comp`), and `ι_n ∘ −` is a bijection `Hom^m(M, N[n]) ≃ Hom^{m+n}(M, N)`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable (M N : QuasiCohesive 𝒜)

/-- **K4.a.** The `n`-cocycles of the Hom complex: `Zⁿ = Hom^n ∩ ker δ`. -/
def HomZ (n : ℤ) : Submodule k (M.T →ₗ[k] N.T) := Hom M N n ⊓ LinearMap.ker (δ M N n)

/-- **K4.a.** The `n`-coboundaries of the Hom complex: `Bⁿ = δ(Hom^{n−1})`. -/
def HomB (n : ℤ) : Submodule k (M.T →ₗ[k] N.T) := (Hom M N (n - 1)).map (δ M N (n - 1))

/-- K4.a: coboundaries are cocycles. -/
theorem HomB_le_HomZ (n : ℤ) : HomB M N n ≤ HomZ M N n := by
  rintro _ ⟨ψ, hψ, rfl⟩
  have h1 := δ_mem M N hψ
  have h2 := δ_δ M N hψ
  rw [sub_add_cancel] at h1 h2
  exact Submodule.mem_inf.2 ⟨h1, LinearMap.mem_ker.2 h2⟩

/-- **K4.a.** The `n`-th cohomology of the Hom complex, `Hⁿ Hom^•(M, N) = Zⁿ / Bⁿ`. -/
abbrev HomCohomology (n : ℤ) : Type := HomZ M N n ⧸ (HomB M N n).comap (HomZ M N n).subtype

variable {M} (N' : CohesiveModule 𝒜) (n : ℤ)

/-- **K4.a.** Post-composition with `ι_n : N[n] → N`. -/
def iotaComp : (M.T →ₗ[k] (N'.shift n).T) →ₗ[k] (M.T →ₗ[k] N'.T) :=
  LinearMap.llcomp k M.T (N'.shift n).T N'.T (shiftIota 𝒜 N'.Q n).toLinearMap

/-- **K4.a.** Post-composition with `ι_n⁻¹ : N → N[n]`. -/
def iotaInvComp : (M.T →ₗ[k] N'.T) →ₗ[k] (M.T →ₗ[k] (N'.shift n).T) :=
  LinearMap.llcomp k M.T N'.T (N'.shift n).T (shiftIota 𝒜 N'.Q n).symm.toLinearMap

/-- K4.a: `iotaComp` (rfl). -/
theorem iotaComp_apply (φ : M.T →ₗ[k] (N'.shift n).T) :
    iotaComp N' n φ = (shiftIota 𝒜 N'.Q n).toLinearMap ∘ₗ φ := rfl

/-- K4.a: `iotaInvComp` (rfl). -/
theorem iotaInvComp_apply (ψ : M.T →ₗ[k] N'.T) :
    iotaInvComp N' n ψ = (shiftIota 𝒜 N'.Q n).symm.toLinearMap ∘ₗ ψ := rfl

/-- The inverse of a shift datum of degree `m` lies in `Hom^{-m}`. -/
private theorem symm_mem_hom {P' P : QuasiCohesive 𝒜} {v : P'.T ≃ₗ[k] P.T} {m : ℤ}
    (h : IsShiftData P' P v m) : v.symm.toLinearMap ∈ Hom P P' (-m) := by
  refine ⟨fun {j x} hx => ?_, fun {p β} hβ x => ?_⟩
  · refine (h.deg (j + -m) (v.symm x)).1 ?_
    rw [LinearEquiv.apply_symm_apply, neg_add_cancel_right]
    exact hx
  · have h' := h.smul hβ (v.symm x)
    rw [LinearEquiv.apply_symm_apply] at h'
    change v.symm (β • x) = _
    rw [LinearEquiv.symm_apply_eq, Units.smul_def, map_zsmul]
    erw [h']
    rw [← Units.smul_def, smul_smul, neg_mul, Int.negOnePow_neg, Int.units_mul_self, one_smul]

/-- The inverse of a closed shift datum is closed. -/
private theorem δ_symm_eq_zero {P' P : QuasiCohesive 𝒜} {v : P'.T ≃ₗ[k] P.T} {m : ℤ}
    (h0 : δ P' P m v.toLinearMap = 0) : δ P P' (-m) v.symm.toLinearMap = 0 := by
  ext x
  have h1 := LinearMap.congr_fun h0 (v.symm x)
  simp only [δ_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.zero_apply] at h1 ⊢
  have h2 : P.X x = m.negOnePow • v (P'.X (v.symm x)) := sub_eq_zero.1 h1
  rw [h2, Int.negOnePow_neg, Units.smul_def, Units.smul_def, map_zsmul,
    LinearEquiv.symm_apply_apply, ← Units.smul_def, ← Units.smul_def, smul_smul,
    Int.units_mul_self, one_smul, sub_self]

/-- `ι_n⁻¹ ∈ Hom^{-n}(N, N[n])`. -/
private theorem shiftIota_symm_mem :
    (shiftIota 𝒜 N'.Q n).symm.toLinearMap ∈
      Hom N'.toQuasiCohesive (N'.shift n).toQuasiCohesive (-n) :=
  symm_mem_hom (isShiftData_shiftIota N' n)

/-- `ι_n⁻¹` is closed. -/
private theorem δ_shiftIota_symm :
    δ N'.toQuasiCohesive (N'.shift n).toQuasiCohesive (-n)
      (shiftIota 𝒜 N'.Q n).symm.toLinearMap = 0 :=
  δ_symm_eq_zero (δ_shiftIota N' n)

/-- Composing a closed map of degree `a` with a closed map of degree `b` is closed of degree `c`. -/
private theorem comp_closed {P Q R : QuasiCohesive 𝒜} {ι : Q.T →ₗ[k] R.T} {φ : P.T →ₗ[k] Q.T}
    {a b c : ℤ} (hc : a + b = c) (hι : ι ∈ Hom Q R a) (h0 : δ Q R a ι = 0)
    (hφ : φ ∈ Hom P Q b) (h1 : δ P Q b φ = 0) : ι ∘ₗ φ ∈ Hom P R c ∧ δ P R c (ι ∘ₗ φ) = 0 := by
  subst hc
  refine ⟨comp_mem P Q R hι hφ, ?_⟩
  rw [δ_comp, h0, h1, LinearMap.zero_comp, LinearMap.comp_zero, smul_zero, add_zero]

/-- Composing a closed map of degree `a` with a coboundary `δ g` gives a coboundary. -/
private theorem comp_boundary {P Q R : QuasiCohesive 𝒜} {ι : Q.T →ₗ[k] R.T} {g : P.T →ₗ[k] Q.T}
    {a b c : ℤ} (hc : a + b = c) (hι : ι ∈ Hom Q R a) (h0 : δ Q R a ι = 0)
    (hg : g ∈ Hom P Q b) :
    ι ∘ₗ δ P Q b g ∈ (Hom P R c).map (δ P R c) := by
  refine ⟨a.negOnePow • (ι ∘ₗ g), zsmul_mem (hc ▸ comp_mem P Q R hι hg) _, ?_⟩
  subst hc
  rw [Units.smul_def, map_zsmul, δ_comp, h0, LinearMap.zero_comp, zero_add, ← Units.smul_def,
    smul_smul, Int.units_mul_self, one_smul]

/-- K4.a: `ι_n ∘ −` maps `Z⁰(M, N[n])` into `Zⁿ(M, N)`. -/
theorem iotaComp_mem_HomZ {φ : M.T →ₗ[k] (N'.shift n).T}
    (hφ : φ ∈ Z0 M (N'.shift n).toQuasiCohesive) :
    iotaComp N' n φ ∈ HomZ M N'.toQuasiCohesive n := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
  obtain ⟨a, b⟩ := comp_closed (add_zero n) (shiftIota_mem_hom N' n) (δ_shiftIota N' n) h1
    (LinearMap.mem_ker.1 h2)
  exact Submodule.mem_inf.2 ⟨a, LinearMap.mem_ker.2 b⟩

/-- K4.a: `ι_n ∘ −` maps `B⁰(M, N[n])` into `Bⁿ(M, N)`. -/
theorem iotaComp_mem_HomB {φ : M.T →ₗ[k] (N'.shift n).T}
    (hφ : φ ∈ B0 M (N'.shift n).toQuasiCohesive) :
    iotaComp N' n φ ∈ HomB M N'.toQuasiCohesive n := by
  obtain ⟨g, hg, rfl⟩ := hφ
  exact comp_boundary (sub_eq_add_neg n 1 ▸ rfl : n + -1 = n - 1) (shiftIota_mem_hom N' n)
    (δ_shiftIota N' n) hg

/-- K4.a: `ι_n⁻¹ ∘ −` maps `Zⁿ(M, N)` into `Z⁰(M, N[n])`. -/
theorem iotaInvComp_mem_Z0 {ψ : M.T →ₗ[k] N'.T} (hψ : ψ ∈ HomZ M N'.toQuasiCohesive n) :
    iotaInvComp N' n ψ ∈ Z0 M (N'.shift n).toQuasiCohesive := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hψ
  obtain ⟨a, b⟩ := comp_closed (neg_add_cancel n) (shiftIota_symm_mem N' n)
    (δ_shiftIota_symm N' n) h1 (LinearMap.mem_ker.1 h2)
  exact Submodule.mem_inf.2 ⟨a, LinearMap.mem_ker.2 b⟩

/-- K4.a: `ι_n⁻¹ ∘ −` maps `Bⁿ(M, N)` into `B⁰(M, N[n])`. -/
theorem iotaInvComp_mem_B0 {ψ : M.T →ₗ[k] N'.T} (hψ : ψ ∈ HomB M N'.toQuasiCohesive n) :
    iotaInvComp N' n ψ ∈ B0 M (N'.shift n).toQuasiCohesive := by
  obtain ⟨g, hg, rfl⟩ := hψ
  exact comp_boundary (by ring : -n + (n - 1) = -1) (shiftIota_symm_mem N' n)
    (δ_shiftIota_symm N' n) hg

/-- **K4.a.** `[φ] ↦ [ι_n ∘ φ]` on cohomology. -/
def homShiftH0 :
    H0 M (N'.shift n).toQuasiCohesive →ₗ[k] HomCohomology M N'.toQuasiCohesive n :=
  Submodule.mapQ _ _ ((iotaComp N' n).restrict fun _ hφ => iotaComp_mem_HomZ N' n hφ)
    fun _ hφ => iotaComp_mem_HomB N' n hφ

/-- **K4.a.** `[ψ] ↦ [ι_n⁻¹ ∘ ψ]` on cohomology. -/
def homShiftInvH0 :
    HomCohomology M N'.toQuasiCohesive n →ₗ[k] H0 M (N'.shift n).toQuasiCohesive :=
  Submodule.mapQ _ _ ((iotaInvComp N' n).restrict fun _ hψ => iotaInvComp_mem_Z0 N' n hψ)
    fun _ hψ => iotaInvComp_mem_B0 N' n hψ

/-- K4.a: the two maps are mutually inverse (first composite). -/
theorem homShiftInvH0_comp : homShiftInvH0 (M := M) N' n ∘ₗ homShiftH0 N' n = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun φ => ?_)
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (LinearMap.ext fun x => (shiftIota 𝒜 N'.Q n).symm_apply_apply (φ.1 x))

/-- K4.a: the two maps are mutually inverse (second composite). -/
theorem homShiftH0_comp : homShiftH0 (M := M) N' n ∘ₗ homShiftInvH0 N' n = LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun ψ => ?_)
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (LinearMap.ext fun x => (shiftIota 𝒜 N'.Q n).apply_symm_apply (ψ.1 x))

/-- **K4.a.** `Hom_{Ho(P_A)}(M, N⟦n⟧) ≃ₗ[k] Hⁿ Hom^•(M, N)`, `[φ] ↦ [ι_n ∘ φ]`. [B, §2.4];
Mathlib's `HomComplexCohomology` analogue. -/
def homShiftEquiv (M N : HoP 𝒜) (n : ℤ) :
    (M ⟶ (shiftFunctor (HoP 𝒜) n).obj N) ≃ₗ[k]
      HomCohomology M.as.toQuasiCohesive N.as.toQuasiCohesive n :=
  LinearEquiv.ofLinearMap (homShiftH0 N.as n) (homShiftInvH0 N.as n)
    (homShiftH0_comp N.as n) (homShiftInvH0_comp N.as n)

end Cohesive
