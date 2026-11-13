import Cohesivemodules.Algebra.Shift
import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor

set_option linter.style.header false

/-!
# Z2.b: the shift functor on `Ho(P_A)`

Blueprint item Z2.b (`blueprint/blueprint-tr.md` §2, §5; §11 v1.16). `HasShift (HoP 𝒜) ℤ` with
`M⟦a⟧ = M[a]` (`CohesiveModule.shift`, Z2.a) and `φ⟦a⟧ = ι_a⁻¹ ∘ φ ∘ ι_a`.

All comparison maps are instances of one construction. A *shift datum* `IsShiftData M' M v m`
is a bijection `v : Tot(M') ≃ Tot(M)` of degree `m` (degree `n` to `n + m`,
`v(β x) = (−1)^{m|β|} β v(x)`) with `𝕏' = (−1)^m v⁻¹ 𝕏 v`. Examples:
* `ι_a` for `M[a] → M` (`isShiftData_shiftIota`);
* composites (`IsShiftData.trans`) and the identity.
For two shift data `v₁, v₂` of the same degree onto the same `M`, `v₂⁻¹ ∘ v₁` is a closed
isomorphism of degree `0` (`shiftCompZ0`, `shiftCompIso`). The structure isomorphisms are of this
form:
* `M[0] ≅ M` from `(ι_0, id)`;
* `M[a+b] ≅ M[a][b]` from `(ι_{a+b}, ι_a ∘ ι_b)`. This one is sign-free on generators, since
  `(−1)^{(a+b)|α|} = (−1)^{a|α|}(−1)^{b|α|}`.
The coherence axioms of `hasShiftMk` then reduce to identities between composites of the `v`'s.
Morphisms are conjugated: `conjH0` (`δ(w⁻¹φv) = (−1)^m w⁻¹(δφ)v`, so cycles and boundaries are
preserved).

## Deviations
* None in substance. [B, §2.4] has `𝔼[1] = −𝔼` for right modules; the left-module shift is the
  transport along `ι_a` (Z2.a, blueprint-tr audit).
-/

noncomputable section

namespace Cohesive

open CategoryTheory DirectSum TensorProduct

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-! ## Shift data -/

/-- **Z2.b.** A shift datum of degree `m`: a bijection `v : Tot(M') ≃ Tot(M)` mapping total degree
`n` onto total degree `n + m`, with `v(β x) = (−1)^{m|β|} β v(x)` and `𝕏' = (−1)^m v⁻¹ 𝕏 v`. -/
structure IsShiftData (M' M : QuasiCohesive 𝒜) (v : M'.T ≃ₗ[k] M.T) (m : ℤ) : Prop where
  /-- `v` maps total degree `n` onto total degree `n + m`. -/
  deg : ∀ n x, v x ∈ totDeg 𝒜 M.Q (n + m) ↔ x ∈ totDeg 𝒜 M'.Q n
  /-- `v(β x) = (−1)^{m|β|} β v(x)`. -/
  smul : ∀ {p : ℤ} {β : A}, β ∈ 𝒜 p → ∀ x, v (β • x) = (m * p).negOnePow • β • v x
  /-- `𝕏' = (−1)^m v⁻¹ 𝕏 v`. -/
  X : M'.X = m.negOnePow • (v.symm.toLinearMap ∘ₗ M.X ∘ₗ v.toLinearMap)

/-- **Z2.b.** `ι_a : M[a] → M` is a shift datum of degree `a`. -/
theorem isShiftData_shiftIota (M : CohesiveModule 𝒜) (a : ℤ) :
    IsShiftData (M.shift a).toQuasiCohesive M.toQuasiCohesive (shiftIota 𝒜 M.Q a) a :=
  ⟨fun n x => shiftIota_mem_totDeg_iff M.Q a n x, shiftIota_smul M.Q a, rfl⟩

/-- Z2.b: the identity is a shift datum of degree `0`. -/
theorem isShiftData_refl (M : QuasiCohesive 𝒜) : IsShiftData M M (LinearEquiv.refl k M.T) 0 := by
  refine ⟨fun n x => by simp, fun {p β} _ x => by simp, ?_⟩
  ext x
  simp

/-- **Z2.b.** Shift data compose: degrees add. -/
theorem IsShiftData.trans {M'' M' M : QuasiCohesive 𝒜} {v₁ : M''.T ≃ₗ[k] M'.T}
    {v₂ : M'.T ≃ₗ[k] M.T} {m₁ m₂ : ℤ} (h₁ : IsShiftData M'' M' v₁ m₁)
    (h₂ : IsShiftData M' M v₂ m₂) : IsShiftData M'' M (v₁.trans v₂) (m₁ + m₂) := by
  refine ⟨fun n x => ?_, fun {p β} hβ x => ?_, ?_⟩
  · rw [LinearEquiv.trans_apply, ← add_assoc, h₂.deg, h₁.deg]
  · rw [LinearEquiv.trans_apply, h₁.smul hβ, Units.smul_def, map_zsmul, h₂.smul hβ,
      LinearEquiv.trans_apply, Units.smul_def, smul_smul, add_mul, Int.negOnePow_add,
      Units.smul_def (_ * _), Units.val_mul]
  · rw [h₁.X, h₂.X]
    ext x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_trans_apply, Units.smul_def, map_zsmul, LinearEquiv.trans_apply,
      smul_smul, Int.negOnePow_add, Units.val_mul]

/-- Z2.b: the degree of a shift datum may be rewritten. -/
theorem IsShiftData.congr_deg {M' M : QuasiCohesive 𝒜} {v : M'.T ≃ₗ[k] M.T} {m m' : ℤ}
    (h : IsShiftData M' M v m) (hm : m = m') : IsShiftData M' M v m' :=
  hm ▸ h

/-- The inverse of a shift datum has the same sign rule. -/
private theorem IsShiftData.symm_smul {M' M : QuasiCohesive 𝒜} {v : M'.T ≃ₗ[k] M.T} {m : ℤ}
    (h : IsShiftData M' M v m) {p : ℤ} {β : A} (hβ : β ∈ 𝒜 p) (y : M.T) :
    v.symm (β • y) = (m * p).negOnePow • β • v.symm y := by
  have h' := h.smul hβ (v.symm y)
  rw [LinearEquiv.apply_symm_apply] at h'
  rw [LinearEquiv.symm_apply_eq, Units.smul_def, map_zsmul, h', ← Units.smul_def, smul_smul,
    Int.units_mul_self, one_smul]

/-- The inverse of a shift datum lowers the degree by `m`. -/
private theorem IsShiftData.symm_mem {M' M : QuasiCohesive 𝒜} {v : M'.T ≃ₗ[k] M.T} {m : ℤ}
    (h : IsShiftData M' M v m) (n : ℤ) {y : M.T} (hy : y ∈ totDeg 𝒜 M.Q (n + m)) :
    v.symm y ∈ totDeg 𝒜 M'.Q n :=
  (h.deg n _).1 (by rwa [LinearEquiv.apply_symm_apply])

/-! ## Comparison maps -/

section Comparison

variable {M₁ M₂ M₃ M : QuasiCohesive 𝒜} {v₁ : M₁.T ≃ₗ[k] M.T} {v₂ : M₂.T ≃ₗ[k] M.T}
  {v₃ : M₃.T ≃ₗ[k] M.T} {m : ℤ}

/-- **Z2.b.** For shift data `v₁, v₂` of the same degree onto `M`, `v₂⁻¹ ∘ v₁` is closed of
degree `0`. -/
theorem shiftComp_mem_Z0 (h₁ : IsShiftData M₁ M v₁ m) (h₂ : IsShiftData M₂ M v₂ m) :
    v₂.symm.toLinearMap ∘ₗ v₁.toLinearMap ∈ Z0 M₁ M₂ := by
  refine Submodule.mem_inf.2 ⟨⟨fun {n x} hx => ?_, fun {p β} hβ x => ?_⟩, ?_⟩
  · rw [add_zero]
    exact h₂.symm_mem _ ((h₁.deg _ x).2 hx)
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h₁.smul hβ, Units.smul_def, map_zsmul, h₂.symm_smul hβ, ← Units.smul_def, smul_smul,
      Int.units_mul_self, one_smul, zero_mul, Int.negOnePow_zero, one_smul]
  · rw [LinearMap.mem_ker, δ_apply, h₁.X, h₂.X]
    ext x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Units.smul_def, map_zsmul, LinearEquiv.apply_symm_apply,
      Int.negOnePow_zero, one_smul, LinearMap.zero_apply]
    exact sub_self _

/-- **Z2.b.** The comparison `v₂⁻¹ ∘ v₁ ∈ Z⁰(M₁, M₂)` of two shift data. -/
def shiftCompZ0 (h₁ : IsShiftData M₁ M v₁ m) (h₂ : IsShiftData M₂ M v₂ m) : Z0 M₁ M₂ :=
  ⟨v₂.symm.toLinearMap ∘ₗ v₁.toLinearMap, shiftComp_mem_Z0 h₁ h₂⟩

/-- Z2.b: the comparison map (rfl). -/
theorem shiftCompZ0_coe (h₁ : IsShiftData M₁ M v₁ m) (h₂ : IsShiftData M₂ M v₂ m) :
    (shiftCompZ0 h₁ h₂).1 = v₂.symm.toLinearMap ∘ₗ v₁.toLinearMap := rfl

/-- Z2.b: comparisons compose. -/
theorem shiftCompZ0_comp (h₁ : IsShiftData M₁ M v₁ m) (h₂ : IsShiftData M₂ M v₂ m)
    (h₃ : IsShiftData M₃ M v₃ m) :
    (shiftCompZ0 h₂ h₃).1 ∘ₗ (shiftCompZ0 h₁ h₂).1 = (shiftCompZ0 h₁ h₃).1 := by
  ext x
  simp only [shiftCompZ0_coe, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

/-- Z2.b: the comparison of a shift datum with itself is the identity. -/
theorem shiftCompZ0_self (h₁ : IsShiftData M₁ M v₁ m) :
    (shiftCompZ0 h₁ h₁).1 = LinearMap.id := by
  ext x
  simp only [shiftCompZ0_coe, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.id_apply]

end Comparison

/-- **Z2.b.** The comparison of two shift data of the same degree onto the same module, as an
isomorphism in `Ho(P_A)`. -/
def shiftCompIso {M₁ M₂ : CohesiveModule 𝒜} {M : QuasiCohesive 𝒜}
    {v₁ : M₁.T ≃ₗ[k] M.T} {v₂ : M₂.T ≃ₗ[k] M.T} {m : ℤ}
    (h₁ : IsShiftData M₁.toQuasiCohesive M v₁ m) (h₂ : IsShiftData M₂.toQuasiCohesive M v₂ m) :
    (⟨M₁⟩ : HoP 𝒜) ≅ ⟨M₂⟩ where
  hom := Submodule.Quotient.mk (shiftCompZ0 h₁ h₂)
  inv := Submodule.Quotient.mk (shiftCompZ0 h₂ h₁)
  hom_inv_id := congrArg Submodule.Quotient.mk
    (Subtype.ext ((shiftCompZ0_comp h₁ h₂ h₁).trans (shiftCompZ0_self h₁)))
  inv_hom_id := congrArg Submodule.Quotient.mk
    (Subtype.ext ((shiftCompZ0_comp h₂ h₁ h₂).trans (shiftCompZ0_self h₂)))

/-- Z2.b: the morphism of `shiftCompIso` (rfl). -/
theorem shiftCompIso_hom {M₁ M₂ : CohesiveModule 𝒜} {M : QuasiCohesive 𝒜}
    {v₁ : M₁.T ≃ₗ[k] M.T} {v₂ : M₂.T ≃ₗ[k] M.T} {m : ℤ}
    (h₁ : IsShiftData M₁.toQuasiCohesive M v₁ m) (h₂ : IsShiftData M₂.toQuasiCohesive M v₂ m) :
    (shiftCompIso h₁ h₂).hom = Submodule.Quotient.mk (shiftCompZ0 h₁ h₂) := rfl

/-! ## Conjugating maps -/

section Conj

variable {M' M N' N : QuasiCohesive 𝒜} (v : M'.T ≃ₗ[k] M.T) (w : N'.T ≃ₗ[k] N.T)

/-- **Z2.b.** Conjugation `φ ↦ w⁻¹ ∘ φ ∘ v`, a `k`-linear map. -/
def conjL : (M.T →ₗ[k] N.T) →ₗ[k] (M'.T →ₗ[k] N'.T) where
  toFun φ := w.symm.toLinearMap ∘ₗ φ ∘ₗ v.toLinearMap
  map_add' φ ψ := by
    rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c φ := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

/-- Z2.b: formula for `conjL` (rfl). -/
theorem conjL_apply (φ : M.T →ₗ[k] N.T) :
    conjL v w φ = w.symm.toLinearMap ∘ₗ φ ∘ₗ v.toLinearMap := rfl

/-- Conjugation is compatible with composition. -/
private theorem conjL_comp {M₁ M₂ M₃ M₁' M₂' M₃' : QuasiCohesive 𝒜} (v₁ : M₁'.T ≃ₗ[k] M₁.T)
    (v₂ : M₂'.T ≃ₗ[k] M₂.T) (v₃ : M₃'.T ≃ₗ[k] M₃.T) (ψ : M₂.T →ₗ[k] M₃.T)
    (φ : M₁.T →ₗ[k] M₂.T) :
    conjL v₁ v₃ (ψ ∘ₗ φ) = conjL v₂ v₃ ψ ∘ₗ conjL v₁ v₂ φ := by
  ext x
  simp only [conjL_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

variable {v w} {m : ℤ} (hv : IsShiftData M' M v m) (hw : IsShiftData N' N w m)
include hv hw

/-- **Z2.b.** Conjugation by shift data of the same degree preserves `Hom^n`. -/
theorem conjL_mem {n : ℤ} {φ : M.T →ₗ[k] N.T} (hφ : φ ∈ Hom M N n) :
    conjL v w φ ∈ Hom M' N' n := by
  refine ⟨fun {j x} hx => ?_, fun {p β} hβ x => ?_⟩
  · simp only [conjL_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 := hφ.1 ((hv.deg j x).2 hx)
    refine hw.symm_mem _ ?_
    rwa [show j + n + m = j + m + n by ring]
  · simp only [conjL_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hv.smul hβ]
    simp only [Units.smul_def, map_zsmul, hφ.2 hβ, hw.symm_smul hβ, smul_smul]
    generalize (m * p).negOnePow = s
    generalize (n * p).negOnePow = t
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
      simp

/-- **Z2.b.** `δ(w⁻¹φv) = (−1)^m w⁻¹(δφ)v`. -/
theorem δ_conjL (n : ℤ) (φ : M.T →ₗ[k] N.T) :
    δ M' N' n (conjL v w φ) = m.negOnePow • conjL v w (δ M N n φ) := by
  rw [δ_apply, δ_apply, hv.X, hw.X]
  ext x
  simp only [conjL_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Units.smul_def, map_zsmul, map_sub, LinearEquiv.apply_symm_apply,
    smul_sub, smul_smul]
  generalize m.negOnePow = s
  generalize n.negOnePow = t
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
    simp

/-- Z2.b: conjugation preserves closed maps of degree `0`. -/
theorem conjL_mem_Z0 {φ : M.T →ₗ[k] N.T} (hφ : φ ∈ Z0 M N) : conjL v w φ ∈ Z0 M' N' := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
  refine Submodule.mem_inf.2 ⟨conjL_mem hv hw h1, ?_⟩
  rw [LinearMap.mem_ker, δ_conjL hv hw, LinearMap.mem_ker.1 h2, map_zero, smul_zero]

/-- Z2.b: conjugation preserves boundaries. -/
theorem conjL_mem_B0 {φ : M.T →ₗ[k] N.T} (hφ : φ ∈ B0 M N) : conjL v w φ ∈ B0 M' N' := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  refine ⟨m.negOnePow • conjL v w ψ, ?_, ?_⟩
  · rw [Units.smul_def]
    exact zsmul_mem (conjL_mem hv hw hψ) _
  · rw [Units.smul_def, map_zsmul, ← Units.smul_def, δ_conjL hv hw, smul_smul,
      Int.units_mul_self, one_smul]

omit hv hw in
/-- **Z2.b.** Conjugation on closed maps of degree `0`. -/
def conjZ0 (hv : IsShiftData M' M v m) (hw : IsShiftData N' N w m) : Z0 M N →ₗ[k] Z0 M' N' :=
  (conjL v w).restrict fun _ hφ => conjL_mem_Z0 hv hw hφ

omit hv hw in
/-- **Z2.b.** Conjugation on `H⁰`. -/
def conjH0 (hv : IsShiftData M' M v m) (hw : IsShiftData N' N w m) : H0 M N →ₗ[k] H0 M' N' :=
  Submodule.mapQ _ _ (conjZ0 hv hw) fun _ hφ => conjL_mem_B0 hv hw hφ

omit hv hw in
/-- Z2.b: `conjH0` on representatives (rfl). -/
theorem conjH0_mk (hv : IsShiftData M' M v m) (hw : IsShiftData N' N w m) (φ : Z0 M N) :
    conjH0 hv hw (Submodule.Quotient.mk φ) = Submodule.Quotient.mk (conjZ0 hv hw φ) := rfl

end Conj

/-! ## The shift functors -/

variable (𝒜) in
/-- **Z2.b.** The shift functor `⟦a⟧` on `Ho(P_A)`: `M ↦ M[a]`, `[φ] ↦ [ι_a⁻¹ φ ι_a]`. -/
def shiftFunctorHoP (a : ℤ) : HoP 𝒜 ⥤ HoP 𝒜 where
  obj M := ⟨M.as.shift a⟩
  map {M N} f := conjH0 (isShiftData_shiftIota M.as a) (isShiftData_shiftIota N.as a) f
  map_id M := by
    refine (conjH0_mk _ _ _).trans (congrArg Submodule.Quotient.mk (Subtype.ext ?_))
    ext x
    simp only [conjZ0, LinearMap.coe_restrict_apply, idZ0, LinearMap.id_apply]
    exact LinearEquiv.symm_apply_apply _ _
  map_comp f g := by
    induction f using Submodule.Quotient.induction_on
    induction g using Submodule.Quotient.induction_on
    refine (congrArg _ (HoP.comp_def _ _)).trans ?_
    refine Eq.trans ?_ (HoP.comp_def _ _).symm
    refine (conjH0_mk _ _ _).trans (congrArg Submodule.Quotient.mk (Subtype.ext ?_))
    rename_i X Y Z φ ψ
    exact conjL_comp (M₁ := X.as.toQuasiCohesive) (M₂ := Y.as.toQuasiCohesive)
      (M₃ := Z.as.toQuasiCohesive) (M₁' := (X.as.shift a).toQuasiCohesive)
      (M₂' := (Y.as.shift a).toQuasiCohesive) (M₃' := (Z.as.shift a).toQuasiCohesive)
      (shiftIota 𝒜 X.as.Q a) (shiftIota 𝒜 Y.as.Q a) (shiftIota 𝒜 Z.as.Q a) ψ.1 φ.1

/-- Z2.b: the object `M⟦a⟧` (rfl). -/
theorem shiftFunctorHoP_obj (a : ℤ) (M : HoP 𝒜) :
    (shiftFunctorHoP 𝒜 a).obj M = ⟨M.as.shift a⟩ := rfl

/-- Z2.b: `⟦a⟧` on representatives (rfl). -/
theorem shiftFunctorHoP_map_mk (a : ℤ) {M N : HoP 𝒜}
    (φ : Z0 M.as.toQuasiCohesive N.as.toQuasiCohesive) :
    (shiftFunctorHoP 𝒜 a).map (Submodule.Quotient.mk φ : M ⟶ N) =
      Submodule.Quotient.mk (conjZ0 (isShiftData_shiftIota M.as a)
        (isShiftData_shiftIota N.as a) φ) := rfl

/-- Naturality square of `⟦0⟧ ≅ 𝟭` on representatives, for abstract modules. -/
private theorem nat_zero_aux {P' P Q' Q : Type} [AddCommGroup P'] [Module k P'] [AddCommGroup P]
    [Module k P] [AddCommGroup Q'] [Module k Q'] [AddCommGroup Q] [Module k Q]
    (a : P' ≃ₗ[k] P) (c : Q' ≃ₗ[k] Q) (φ : P →ₗ[k] Q) :
    ((LinearEquiv.refl k Q).symm.toLinearMap ∘ₗ c.toLinearMap) ∘ₗ
        (c.symm.toLinearMap ∘ₗ φ ∘ₗ a.toLinearMap) =
      φ ∘ₗ ((LinearEquiv.refl k P).symm.toLinearMap ∘ₗ a.toLinearMap) := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply]

/-- Naturality square of `⟦a + b⟧ ≅ ⟦a⟧ ⋙ ⟦b⟧` on representatives, for abstract modules. -/
private theorem nat_add_aux {P2 P1 P' P Q2 Q1 Q' Q : Type} [AddCommGroup P2] [Module k P2]
    [AddCommGroup P1] [Module k P1] [AddCommGroup P'] [Module k P'] [AddCommGroup P]
    [Module k P] [AddCommGroup Q2] [Module k Q2] [AddCommGroup Q1] [Module k Q1]
    [AddCommGroup Q'] [Module k Q'] [AddCommGroup Q] [Module k Q]
    (e : P1 ≃ₗ[k] P) (ib : P2 ≃ₗ[k] P') (ia : P' ≃ₗ[k] P)
    (e' : Q1 ≃ₗ[k] Q) (ib' : Q2 ≃ₗ[k] Q') (ia' : Q' ≃ₗ[k] Q) (φ : P →ₗ[k] Q) :
    ((ib'.trans ia').symm.toLinearMap ∘ₗ e'.toLinearMap) ∘ₗ
        (e'.symm.toLinearMap ∘ₗ φ ∘ₗ e.toLinearMap) =
      (ib'.symm.toLinearMap ∘ₗ (ia'.symm.toLinearMap ∘ₗ φ ∘ₗ ia.toLinearMap) ∘ₗ
        ib.toLinearMap) ∘ₗ ((ib.trans ia).symm.toLinearMap ∘ₗ e.toLinearMap) := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_trans_apply]

variable (𝒜) in
/-- **Z2.b.** `⟦0⟧ ≅ 𝟭`, with components the comparisons of `ι_0` and the identity. -/
def shiftFunctorZeroHoP : shiftFunctorHoP 𝒜 0 ≅ 𝟭 (HoP 𝒜) :=
  NatIso.ofComponents
    (fun M => shiftCompIso (M₁ := M.as.shift 0) (M₂ := M.as) (isShiftData_shiftIota M.as 0)
      (isShiftData_refl M.as.toQuasiCohesive))
    (fun f => by
      induction f using Submodule.Quotient.induction_on with
      | H φ =>
        refine (HoP.comp_def _ _).trans (Eq.trans ?_ (HoP.comp_def _ _).symm)
        refine (compH0_mk _ _).trans (Eq.trans ?_ (compH0_mk _ _).symm)
        refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
        rename_i X Y
        exact nat_zero_aux (shiftIota 𝒜 X.as.Q 0) (shiftIota 𝒜 Y.as.Q 0) φ.1)

variable (𝒜) in
/-- **Z2.b.** `⟦a + b⟧ ≅ ⟦a⟧ ⋙ ⟦b⟧`, with components the comparisons of `ι_{a+b}` and
`ι_a ∘ ι_b` (sign-free on generators). -/
def shiftFunctorAddHoP (a b : ℤ) :
    shiftFunctorHoP 𝒜 (a + b) ≅ shiftFunctorHoP 𝒜 a ⋙ shiftFunctorHoP 𝒜 b :=
  NatIso.ofComponents
    (fun M => shiftCompIso (M₁ := M.as.shift (a + b)) (M₂ := (M.as.shift a).shift b)
      (isShiftData_shiftIota M.as (a + b))
      (((isShiftData_shiftIota (M.as.shift a) b).trans (isShiftData_shiftIota M.as a)).congr_deg
        (add_comm b a)))
    (fun f => by
      induction f using Submodule.Quotient.induction_on with
      | H φ =>
        refine (HoP.comp_def _ _).trans (Eq.trans ?_ (HoP.comp_def _ _).symm)
        refine (compH0_mk _ _).trans (Eq.trans ?_ (compH0_mk _ _).symm)
        refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
        rename_i X Y
        exact nat_add_aux (shiftIota 𝒜 X.as.Q (a + b)) (shiftIota 𝒜 (X.as.shift a).Q b)
          (shiftIota 𝒜 X.as.Q a) (shiftIota 𝒜 Y.as.Q (a + b))
          (shiftIota 𝒜 (Y.as.shift a).Q b) (shiftIota 𝒜 Y.as.Q a) φ.1)

/-- **Z2.b.** `eqToHom` between shifts by equal integers is the comparison of the two `ι`'s. -/
theorem eqToHom_shiftFunctorHoP_obj (M : HoP 𝒜) {a a' : ℤ} (h : a = a') :
    eqToHom (congrArg (fun a => (shiftFunctorHoP 𝒜 a).obj M) h) =
      (shiftCompIso (M₁ := M.as.shift a) (M₂ := M.as.shift a') (isShiftData_shiftIota M.as a)
        ((isShiftData_shiftIota M.as a').congr_deg h.symm)).hom := by
  subst h
  rw [eqToHom_refl]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (shiftCompZ0_self _).symm)

/-- Associativity coherence on representatives, for abstract modules. -/
private theorem assoc_aux {P P1 P12 S B Q R2 R3 U : Type} [AddCommGroup P] [Module k P]
    [AddCommGroup P1] [Module k P1] [AddCommGroup P12] [Module k P12] [AddCommGroup S]
    [Module k S] [AddCommGroup B] [Module k B] [AddCommGroup Q] [Module k Q]
    [AddCommGroup R2] [Module k R2] [AddCommGroup R3] [Module k R3] [AddCommGroup U]
    [Module k U] (G1 : P1 ≃ₗ[k] P) (G12 : P12 ≃ₗ[k] P) (E : S ≃ₗ[k] P) (E' : B ≃ₗ[k] P)
    (F3 : Q ≃ₗ[k] P12) (K2 : R2 ≃ₗ[k] P1) (H3 : R3 ≃ₗ[k] R2) (L : U ≃ₗ[k] P1) :
    (H3.symm.toLinearMap ∘ₗ ((K2.trans G1).symm.toLinearMap ∘ₗ G12.toLinearMap) ∘ₗ
        F3.toLinearMap) ∘ₗ ((F3.trans G12).symm.toLinearMap ∘ₗ E.toLinearMap) =
      ((H3.trans K2).symm.toLinearMap ∘ₗ L.toLinearMap) ∘ₗ
        (((L.trans G1).symm.toLinearMap ∘ₗ E'.toLinearMap) ∘ₗ
          (E'.symm.toLinearMap ∘ₗ E.toLinearMap)) := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_trans_apply]

/-- `0 + n` coherence on representatives, for abstract modules. -/
private theorem zero_add_aux {P P0 R S N : Type} [AddCommGroup P] [Module k P]
    [AddCommGroup P0] [Module k P0] [AddCommGroup R] [Module k R] [AddCommGroup S]
    [Module k S] [AddCommGroup N] [Module k N] (E : S ≃ₗ[k] P) (E' : N ≃ₗ[k] P)
    (J : P0 ≃ₗ[k] P) (H : R ≃ₗ[k] P0) :
    (H.trans J).symm.toLinearMap ∘ₗ E.toLinearMap =
      (H.symm.toLinearMap ∘ₗ (J.symm.toLinearMap ∘ₗ (LinearEquiv.refl k P).toLinearMap) ∘ₗ
        E'.toLinearMap) ∘ₗ (E'.symm.toLinearMap ∘ₗ E.toLinearMap) := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_trans_apply, LinearEquiv.refl_apply]

/-- `n + 0` coherence on representatives, for abstract modules. -/
private theorem add_zero_aux {P P1 R S : Type} [AddCommGroup P] [Module k P]
    [AddCommGroup P1] [Module k P1] [AddCommGroup R] [Module k R] [AddCommGroup S]
    [Module k S] (E : S ≃ₗ[k] P) (E' : P1 ≃ₗ[k] P) (Z : R ≃ₗ[k] P1) :
    (Z.trans E').symm.toLinearMap ∘ₗ E.toLinearMap =
      (Z.symm.toLinearMap ∘ₗ (LinearEquiv.refl k P1).toLinearMap) ∘ₗ
        (E'.symm.toLinearMap ∘ₗ E.toLinearMap) := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_trans_apply,
    LinearEquiv.refl_apply]

/-- **Z2.b.** Coherence of `⟦·⟧` with associativity (field `assoc_hom_app` of `ShiftMkCore`). -/
theorem shiftFunctorHoP_assoc (m₁ m₂ m₃ : ℤ) (X : HoP 𝒜) :
    (shiftFunctorAddHoP 𝒜 (m₁ + m₂) m₃).hom.app X ≫
        (shiftFunctorHoP 𝒜 m₃).map ((shiftFunctorAddHoP 𝒜 m₁ m₂).hom.app X) =
      eqToHom (by rw [add_assoc]) ≫ (shiftFunctorAddHoP 𝒜 m₁ (m₂ + m₃)).hom.app X ≫
        (shiftFunctorAddHoP 𝒜 m₂ m₃).hom.app ((shiftFunctorHoP 𝒜 m₁).obj X) := by
  rw [eqToHom_shiftFunctorHoP_obj X (add_assoc m₁ m₂ m₃)]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (assoc_aux (shiftIota 𝒜 X.as.Q m₁)
    (shiftIota 𝒜 X.as.Q (m₁ + m₂)) (shiftIota 𝒜 X.as.Q (m₁ + m₂ + m₃))
    (shiftIota 𝒜 X.as.Q (m₁ + (m₂ + m₃))) (shiftIota 𝒜 (X.as.shift (m₁ + m₂)).Q m₃)
    (shiftIota 𝒜 (X.as.shift m₁).Q m₂) (shiftIota 𝒜 ((X.as.shift m₁).shift m₂).Q m₃)
    (shiftIota 𝒜 (X.as.shift m₁).Q (m₂ + m₃))))

/-- **Z2.b.** Coherence of `⟦·⟧` with `0 + n = n` (field `zero_add_hom_app`). -/
theorem shiftFunctorHoP_zero_add (n : ℤ) (X : HoP 𝒜) :
    (shiftFunctorAddHoP 𝒜 0 n).hom.app X =
      eqToHom (by dsimp; rw [zero_add]) ≫
        (shiftFunctorHoP 𝒜 n).map ((shiftFunctorZeroHoP 𝒜).inv.app X) := by
  rw [eqToHom_shiftFunctorHoP_obj X (zero_add n)]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (zero_add_aux (shiftIota 𝒜 X.as.Q (0 + n))
    (shiftIota 𝒜 X.as.Q n) (shiftIota 𝒜 X.as.Q 0) (shiftIota 𝒜 (X.as.shift 0).Q n)))

/-- **Z2.b.** Coherence of `⟦·⟧` with `n + 0 = n` (field `add_zero_hom_app`). -/
theorem shiftFunctorHoP_add_zero (n : ℤ) (X : HoP 𝒜) :
    (shiftFunctorAddHoP 𝒜 n 0).hom.app X =
      eqToHom (by dsimp; rw [add_zero]) ≫
        (shiftFunctorZeroHoP 𝒜).inv.app ((shiftFunctorHoP 𝒜 n).obj X) := by
  rw [eqToHom_shiftFunctorHoP_obj X (add_zero n)]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (add_zero_aux (shiftIota 𝒜 X.as.Q (n + 0))
    (shiftIota 𝒜 X.as.Q n) (shiftIota 𝒜 (X.as.shift n).Q 0)))

variable (𝒜) in
/-- **Z2.b.** The data of the shift on `Ho(P_A)`. -/
def shiftMkCoreHoP : ShiftMkCore (HoP 𝒜) ℤ where
  F := shiftFunctorHoP 𝒜
  zero := shiftFunctorZeroHoP 𝒜
  add := shiftFunctorAddHoP 𝒜
  assoc_hom_app := fun m₁ m₂ m₃ X => by exact shiftFunctorHoP_assoc m₁ m₂ m₃ X
  zero_add_hom_app := fun n X => by
    rw [eqToHom_shiftFunctorHoP_obj X (zero_add n)]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (zero_add_aux (shiftIota 𝒜 X.as.Q (0 + n))
      (shiftIota 𝒜 X.as.Q n) (shiftIota 𝒜 X.as.Q 0) (shiftIota 𝒜 (X.as.shift 0).Q n)))
  add_zero_hom_app := fun n X => by
    rw [eqToHom_shiftFunctorHoP_obj X (add_zero n)]
    exact congrArg Submodule.Quotient.mk (Subtype.ext (add_zero_aux (shiftIota 𝒜 X.as.Q (n + 0))
      (shiftIota 𝒜 X.as.Q n) (shiftIota 𝒜 (X.as.shift n).Q 0)))

/-- **Z2.b.** The shift on `Ho(P_A)`: `M⟦a⟧ = M[a]` (`hasShiftMk`). [B, §2.4]. -/
instance : HasShift (HoP 𝒜) ℤ := hasShiftMk (HoP 𝒜) ℤ (shiftMkCoreHoP 𝒜)

/-- Z2.b: `M⟦a⟧ = M[a]` (rfl). -/
theorem shiftFunctor_obj_as (a : ℤ) (M : HoP 𝒜) :
    ((shiftFunctor (HoP 𝒜) a).obj M).as = M.as.shift a :=
  rfl

/-- **Z2.b.** The shift functors are additive. -/
instance (a : ℤ) : (shiftFunctorHoP 𝒜 a).Additive where
  map_add := fun {M N} {f g} =>
    map_add (conjH0 (isShiftData_shiftIota M.as a) (isShiftData_shiftIota N.as a)) f g

/-- **Z2.b.** The shift functors are `k`-linear. -/
instance (a : ℤ) : (shiftFunctorHoP 𝒜 a).Linear k where
  map_smul := fun {M N} f r =>
    map_smul (conjH0 (isShiftData_shiftIota M.as a) (isShiftData_shiftIota N.as a)) r f

/-- **Z2.b.** `shiftFunctor (HoP 𝒜) a` is additive. -/
instance (a : ℤ) : (shiftFunctor (HoP 𝒜) a).Additive :=
  inferInstanceAs (shiftFunctorHoP 𝒜 a).Additive

/-- **Z2.b.** `shiftFunctor (HoP 𝒜) a` is `k`-linear. -/
instance (a : ℤ) : (shiftFunctor (HoP 𝒜) a).Linear k :=
  inferInstanceAs ((shiftFunctorHoP 𝒜 a).Linear k)

end Cohesive
