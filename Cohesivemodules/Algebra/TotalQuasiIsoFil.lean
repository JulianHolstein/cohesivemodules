import Cohesivemodules.Algebra.LiftingCone
import Cohesivemodules.Algebra.Filtration
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

set_option linter.style.header false

/-!
# A12: the total quasi-isomorphism

The total complex `(Tot, 𝕏)` of a flat (`c = 0`) quasi-cohesive module, as a Mathlib cochain
complex of `k`-modules graded by total degree, and the theorem that a closed degree-`0` map
whose `(0,0)`-component is a quasi-isomorphism is a quasi-isomorphism of total complexes, when
every `A^b` is flat over `A⁰` (blueprint A12). Proof: A7 with the form-degree filtration (A6).

A split of blueprint §7's `Lifting.lean` (A11–A12), for size only.

Spelling (fixed): degree `m` of `totComplex` is `ModuleCat.of k (totDeg 𝒜 M.Q m)`; degree `m` of
the filtration piece `F^b` is `ModuleCat.of k (filDeg M b m)` with
`filDeg M b m = totDeg 𝒜 M.Q m ⊓ filTot 𝒜 M.Q b`; `gr^b` is the complex `A^b ⊗_{A⁰} (Q, 𝕏⁰)`
(`tensC`), restricted to `k` and shifted by `-b`. Mathlib's shift multiplies the differential
by `(-1)^b`, which is exactly the sign `𝕏` induces on `gr^b` (`extr_hatGen_d`).

Part 1 of 3 of the original `Algebra/TotalQuasiIso.lean`, split for size; continued in
`Algebra/TotalQuasiIsoGr.lean`.
-/

namespace Cohesive

open CategoryTheory DirectSum TensorProduct

noncomputable section

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-! ## The total complex -/

namespace QuasiCohesive

variable (M : QuasiCohesive 𝒜)

/-- A12: `𝕏` restricted to total degree `m`. -/
def totD (m : ℤ) : totDeg 𝒜 M.Q m →ₗ[k] totDeg 𝒜 M.Q (m + 1) :=
  (M.X ∘ₗ (totDeg 𝒜 M.Q m).subtype).codRestrict _ fun x => M.X_mem x.2

/-- A12: `totD` is `𝕏`. -/
@[simp] theorem totD_apply (m : ℤ) (x : totDeg 𝒜 M.Q m) : (M.totD m x : M.T) = M.X x := rfl

/-- A12: `𝕏 ∘ 𝕏 = 0` on total degrees when the curvature vanishes. -/
theorem totD_totD (hc : GCDga.c (𝒜 := 𝒜) = 0) (m : ℤ) : M.totD (m + 1) ∘ₗ M.totD m = 0 := by
  ext x
  show M.X (M.X x) = 0
  rw [M.flat, hc, zero_smul]

/-- **A12** The total complex `(A ⊗_{A⁰} ⨁_p Q^p, 𝕏)` of a quasi-cohesive module with vanishing
curvature, as a Mathlib cochain complex of `k`-modules: degree `m` is `totDeg m` (spanned by
`a ⊗ e`, `a ∈ A^q`, `e ∈ Q^p`, `q + p = m`), the differential is `𝕏`.
[A, proof of Prop 7.2.18]. ⚠ Needs `c = 0` (`𝕏 ∘ 𝕏 = c·(-)`); the sources use it only for
`c = 0` (curvature `h = 0`). -/
def totComplex (hc : GCDga.c (𝒜 := 𝒜) = 0) : CochainComplex (ModuleCat.{0} k) ℤ :=
  CochainComplex.of (fun m => ModuleCat.of k (totDeg 𝒜 M.Q m))
    (fun m => ModuleCat.ofHom (M.totD m))
    fun m => ModuleCat.hom_ext (M.totD_totD hc m)

/-- A12: the terms of the total complex. -/
theorem totComplex_X (hc : GCDga.c (𝒜 := 𝒜) = 0) (m : ℤ) :
    (M.totComplex hc).X m = ModuleCat.of k (totDeg 𝒜 M.Q m) := rfl

/-- A12: the differential of the total complex is `𝕏`. -/
theorem totComplex_d_apply (hc : GCDga.c (𝒜 := 𝒜) = 0) (m : ℤ) (x : totDeg 𝒜 M.Q m) :
    ((M.totComplex hc).d m (m + 1)).hom x = M.totD m x := by
  simp only [totComplex, CochainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

end QuasiCohesive

variable {M₁ M₂ : QuasiCohesive 𝒜} {φ : M₁.T →ₗ[k] M₂.T}

/-- A12: a degree-`0` map preserves total degrees. -/
theorem totMapD_mem (hφ : φ ∈ Hom M₁ M₂ 0) {m : ℤ} {x : M₁.T} (hx : x ∈ totDeg 𝒜 M₁.Q m) :
    φ x ∈ totDeg 𝒜 M₂.Q m := by
  have := hφ.1 hx
  rwa [add_zero] at this

/-- A12: a degree-`0` map restricted to total degree `m`. -/
def totMapD (hφ : φ ∈ Hom M₁ M₂ 0) (m : ℤ) : totDeg 𝒜 M₁.Q m →ₗ[k] totDeg 𝒜 M₂.Q m :=
  (φ ∘ₗ (totDeg 𝒜 M₁.Q m).subtype).codRestrict _ fun x => totMapD_mem hφ x.2

/-- A12: `totMapD` is `φ`. -/
@[simp] theorem totMapD_apply (hφ : φ ∈ Hom M₁ M₂ 0) (m : ℤ) (x : totDeg 𝒜 M₁.Q m) :
    (totMapD hφ m x : M₂.T) = φ x := rfl

/-- A12: a closed degree-`0` map commutes with `𝕏`. -/
theorem totMapD_comm (hφ : φ ∈ Z0 M₁ M₂) (m : ℤ) :
    totMapD hφ.1 (m + 1) ∘ₗ M₁.totD m = M₂.totD m ∘ₗ totMapD hφ.1 m := by
  have h : δ M₁ M₂ 0 φ = 0 := hφ.2
  have h' : ∀ x, M₂.X (φ x) = φ (M₁.X x) := fun x => by
    have := LinearMap.congr_fun h x
    simp only [δ_apply, LinearMap.sub_apply, LinearMap.comp_apply, Int.negOnePow_zero,
      one_smul, LinearMap.zero_apply] at this
    exact sub_eq_zero.1 this
  ext x
  exact (h' x).symm

/-- A12: `totMapD` commutes with the differentials of the total complexes. -/
theorem totMap_sq (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) (m : ℤ) :
    ModuleCat.ofHom (totMapD hφ.1 m) ≫ (M₂.totComplex hc).d m (m + 1) =
      (M₁.totComplex hc).d m (m + 1) ≫ ModuleCat.ofHom (totMapD hφ.1 (m + 1)) := by
  simp only [QuasiCohesive.totComplex, CochainComplex.of_d]
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
  exact congrArg ModuleCat.ofHom (totMapD_comm hφ m).symm

/-- **A12** The map of total complexes induced by a closed degree-`0` map `φ ∈ Z⁰(M₁, M₂)`. -/
def totMap (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) :
    M₁.totComplex hc ⟶ M₂.totComplex hc :=
  CochainComplex.ofHom (fun m => ModuleCat.ofHom (totMapD hφ.1 m)) (totMap_sq hc hφ)

/-- A12: the components of `totMap` are `φ`. -/
theorem totMap_f_apply (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) (m : ℤ)
    (x : totDeg 𝒜 M₁.Q m) : ((totMap hc hφ).f m).hom x = totMapD hφ.1 m x := by
  rfl

/-! ## The filtration subcomplexes `F^b` -/

namespace QuasiCohesive

variable (M : QuasiCohesive 𝒜)

/-- A12: degree `m` of `F^b`: total degree `m` and form degree `≥ b`. -/
def filDeg (b m : ℤ) : Submodule k M.T := totDeg 𝒜 M.Q m ⊓ filTot 𝒜 M.Q b

/-- A12: `𝕏` preserves `F^b` and raises the total degree by `1`. -/
theorem X_mem_filDeg {b m : ℤ} {x : M.T} (hx : x ∈ M.filDeg b m) :
    M.X x ∈ M.filDeg b (m + 1) :=
  ⟨M.X_mem hx.1, X_mem_filTot M hx.2⟩

/-- A12: `𝕏` on `F^b` in degree `m`. -/
def filD (b m : ℤ) : M.filDeg b m →ₗ[k] M.filDeg b (m + 1) :=
  (M.X ∘ₗ (M.filDeg b m).subtype).codRestrict _ fun x => M.X_mem_filDeg x.2

/-- A12: `filD` is `𝕏`. -/
@[simp] theorem filD_apply (b m : ℤ) (x : M.filDeg b m) : (M.filD b m x : M.T) = M.X x := rfl

/-- A12: `𝕏 ∘ 𝕏 = 0` on `F^b` when the curvature vanishes. -/
theorem filD_filD (hc : GCDga.c (𝒜 := 𝒜) = 0) (b m : ℤ) :
    M.filD b (m + 1) ∘ₗ M.filD b m = 0 := by
  ext x
  show M.X (M.X x) = 0
  rw [M.flat, hc, zero_smul]

/-- A12: the subcomplex `F^b` of the total complex. -/
def filComplex (hc : GCDga.c (𝒜 := 𝒜) = 0) (b : ℤ) : CochainComplex (ModuleCat.{0} k) ℤ :=
  CochainComplex.of (fun m => ModuleCat.of k (M.filDeg b m))
    (fun m => ModuleCat.ofHom (M.filD b m))
    fun m => ModuleCat.hom_ext (M.filD_filD hc b m)

/-- A12: `F^{b+1} ⊆ F^b`. -/
theorem filDeg_succ_le (b m : ℤ) : M.filDeg (b + 1) m ≤ M.filDeg b m :=
  fun _ hx => ⟨hx.1, filTot_anti (Int.le_add_one le_rfl) hx.2⟩

/-- A12: the inclusion `F^{b+1} → F^b` in degree `m`. -/
def filInclD (b m : ℤ) : M.filDeg (b + 1) m →ₗ[k] M.filDeg b m :=
  Submodule.inclusion (M.filDeg_succ_le b m)

/-- A12: the inclusion commutes with `𝕏`. -/
theorem filInclD_comm (b m : ℤ) :
    M.filInclD b (m + 1) ∘ₗ M.filD (b + 1) m = M.filD b m ∘ₗ M.filInclD b m := by
  ext x
  rfl

/-- A12: the inclusion commutes with the differentials of `F^{b+1}` and `F^b`. -/
theorem filIncl_sq (hc : GCDga.c (𝒜 := 𝒜) = 0) (b m : ℤ) :
    ModuleCat.ofHom (M.filInclD b m) ≫ (M.filComplex hc b).d m (m + 1) =
      (M.filComplex hc (b + 1)).d m (m + 1) ≫ ModuleCat.ofHom (M.filInclD b (m + 1)) := by
  simp only [QuasiCohesive.filComplex, CochainComplex.of_d]
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
  exact congrArg ModuleCat.ofHom (M.filInclD_comm b m).symm

/-- A12: the inclusion of complexes `F^{b+1} → F^b`. -/
def filIncl (hc : GCDga.c (𝒜 := 𝒜) = 0) (b : ℤ) :
    M.filComplex hc (b + 1) ⟶ M.filComplex hc b :=
  CochainComplex.ofHom (fun m => ModuleCat.ofHom (M.filInclD b m)) (M.filIncl_sq hc b)

/-- A12: `F^b = 0` in every degree for `b > N`. -/
theorem filDeg_eq_bot {b : ℤ} (hb : (GCDga.N 𝒜 : ℤ) < b) (m : ℤ) : M.filDeg b m = ⊥ := by
  unfold filDeg
  rw [filTot_eq_bot hb, inf_bot_eq]

/-- A12: `F^0` is the whole total degree. -/
theorem filDeg_zero (m : ℤ) : M.filDeg 0 m = totDeg 𝒜 M.Q m := by
  unfold filDeg
  have : filTot 𝒜 M.Q 0 = ⊤ := eq_top_iff.2 fun x _ => filTot_zero x
  rw [this, inf_top_eq]

end QuasiCohesive

/-- A12: a closed degree-`0` map preserves `F^b`. -/
theorem filMapD_mem (hφ : φ ∈ Hom M₁ M₂ 0) {b m : ℤ} {x : M₁.T} (hx : x ∈ M₁.filDeg b m) :
    φ x ∈ M₂.filDeg b m := by
  refine ⟨totMapD_mem hφ hx.1, ?_⟩
  have hx2 := hx.2
  clear hx
  induction hx2 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hbq, ha, rfl⟩ := hx
    rw [homT_tmul (𝒜 := 𝒜) (Q₁ := M₁.Q) (Q₂ := M₂.Q) hφ, GCDga.twist_zero]
    have := smul_mem_filTot ha (filTot_zero (φ (Tot.tmul 𝒜 M₁.Q 1 e)))
    rw [add_zero] at this
    exact filTot_anti hbq this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- A12: a degree-`0` map on `F^b` in degree `m`. -/
def filMapD (hφ : φ ∈ Hom M₁ M₂ 0) (b m : ℤ) : M₁.filDeg b m →ₗ[k] M₂.filDeg b m :=
  (φ ∘ₗ (M₁.filDeg b m).subtype).codRestrict _ fun x => filMapD_mem hφ x.2

/-- A12: `filMapD` is `φ`. -/
@[simp] theorem filMapD_apply (hφ : φ ∈ Hom M₁ M₂ 0) (b m : ℤ) (x : M₁.filDeg b m) :
    (filMapD hφ b m x : M₂.T) = φ x := rfl

/-- A12: a closed degree-`0` map commutes with `𝕏` on `F^b`. -/
theorem filMapD_comm (hφ : φ ∈ Z0 M₁ M₂) (b m : ℤ) :
    filMapD hφ.1 b (m + 1) ∘ₗ M₁.filD b m = M₂.filD b m ∘ₗ filMapD hφ.1 b m := by
  have h : δ M₁ M₂ 0 φ = 0 := hφ.2
  have h' : ∀ x, M₂.X (φ x) = φ (M₁.X x) := fun x => by
    have := LinearMap.congr_fun h x
    simp only [δ_apply, LinearMap.sub_apply, LinearMap.comp_apply, Int.negOnePow_zero,
      one_smul, LinearMap.zero_apply] at this
    exact sub_eq_zero.1 this
  ext x
  exact (h' x).symm

/-- A12: `filMapD` commutes with the differentials of `F^b`. -/
theorem filMap_sq (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) (b m : ℤ) :
    ModuleCat.ofHom (filMapD hφ.1 b m) ≫ (M₂.filComplex hc b).d m (m + 1) =
      (M₁.filComplex hc b).d m (m + 1) ≫ ModuleCat.ofHom (filMapD hφ.1 b (m + 1)) := by
  simp only [QuasiCohesive.filComplex, CochainComplex.of_d]
  rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
  exact congrArg ModuleCat.ofHom (filMapD_comm hφ b m).symm

/-- A12: the map `F^b M₁ → F^b M₂` induced by `φ ∈ Z⁰(M₁, M₂)`. -/
def filMap (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) (b : ℤ) :
    M₁.filComplex hc b ⟶ M₂.filComplex hc b :=
  CochainComplex.ofHom (fun m => ModuleCat.ofHom (filMapD hφ.1 b m)) (filMap_sq hc hφ b)

end
end Cohesive
