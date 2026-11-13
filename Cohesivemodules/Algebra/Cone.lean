import Cohesivemodules.Algebra.Shift
import Cohesivemodules.Algebra.TotProd
import Mathlib.RingTheory.Finiteness.Prod

set_option linter.style.header false

/-!
# Z2.d: the cone of a closed map of cohesive modules

Blueprint item Z2.d (`blueprint/blueprint-tr.md` §2, §3a, §5), [B, §2.4], following Mathlib's
`CochainComplex.mappingCone` (signs pinned in `Scratch/P14_TR.lean`). For a closed degree-`0` map
`φ ∈ Z⁰(M, N)` of cohesive modules over `𝒜` (any curvature):
* generators `Q_C^p = Q_N^p × Q_M^{p+1}` (`coneQ`), `Tot(C) ≃ Tot(N) × Tot(M)` (`coneEquiv`:
  `Tot.prodEquiv` followed by `ι₁ : Tot(Q_M[1]) ≃ Tot(M)`);
* structure maps `inl ∈ Hom^{−1}(M, C)`, `inr ∈ Hom^0(N, C)`, `fst ∈ Hom^1(C, M)`,
  `snd ∈ Hom^0(C, N)` (`coneInl`, `coneInr`, `coneFst`, `coneSnd`), with
  `fst∘inl = id`, `snd∘inr = id`, `fst∘inr = 0`, `snd∘inl = 0`, `inl∘fst + inr∘snd = id`;
* the operator `𝕏_C = inr 𝕏_N snd + inr φ fst − inl 𝕏_M fst` (`coneX`; on `inr f + inl e` this is
  Block's matrix `[[𝕏_N, φ], [0, 𝕏_M[1]]]`), and the cohesive module `cone φ`;
* `δ inl = inr ∘ φ`, `δ inr = 0`, `δ fst = 0`, `δ snd = −φ ∘ fst` (Mathlib's `δ_inl`, `δ_snd`).

## Deviations
* [B] writes `𝔼[1] = −𝔼` (right modules); here the shifted part enters through `ι₁` (Z2.a,
  conventions §2), and the structure maps are Mathlib's.
-/

noncomputable section

namespace Cohesive

open DirectSum TensorProduct

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable (M N : CohesiveModule 𝒜)

/-- **Z2.d.** The generators of the cone: `Q_C^p = Q_N^p × Q_M^{p+1}`. -/
abbrev coneQ : ℤ → Type := prodQ N.Q (shiftQ M.Q 1)

/-- **Z2.d.** `Tot(C) ≃ Tot(N) × Tot(M)`: `Tot.prodEquiv`, then `ι₁` on the second factor. -/
def coneEquiv : Tot 𝒜 (coneQ M N) ≃ₗ[k] M.T × N.T :=
  ((Tot.prodEquiv 𝒜 N.Q (shiftQ M.Q 1)).restrictScalars k).trans
    ((LinearEquiv.prodComm k _ _).trans
      (LinearEquiv.prodCongr (shiftIota 𝒜 M.Q 1) (LinearEquiv.refl k N.T)))

/-- **Z2.d.** `inl : Tot(M) → Tot(C)`, `e ↦ (0, ι₁⁻¹ e)` (degree `−1`). -/
def coneInl : M.T →ₗ[k] Tot 𝒜 (coneQ M N) :=
  (coneEquiv M N).symm.toLinearMap ∘ₗ LinearMap.inl k M.T N.T

/-- **Z2.d.** `inr : Tot(N) → Tot(C)`, `f ↦ (f, 0)` (degree `0`). -/
def coneInr : N.T →ₗ[k] Tot 𝒜 (coneQ M N) :=
  (coneEquiv M N).symm.toLinearMap ∘ₗ LinearMap.inr k M.T N.T

/-- **Z2.d.** `fst : Tot(C) → Tot(M)`, `(f, e) ↦ ι₁ e` (degree `1`). -/
def coneFst : Tot 𝒜 (coneQ M N) →ₗ[k] M.T :=
  LinearMap.fst k M.T N.T ∘ₗ (coneEquiv M N).toLinearMap

/-- **Z2.d.** `snd : Tot(C) → Tot(N)`, `(f, e) ↦ f` (degree `0`). -/
def coneSnd : Tot 𝒜 (coneQ M N) →ₗ[k] N.T :=
  LinearMap.snd k M.T N.T ∘ₗ (coneEquiv M N).toLinearMap

/-- Z2.d: `coneEquiv` on the second coordinate (rfl). -/
private theorem coneEquiv_snd (z : Tot 𝒜 (coneQ M N)) :
    (coneEquiv M N z).2 = (Tot.prodEquiv 𝒜 N.Q (shiftQ M.Q 1) z).1 := rfl

/-- Z2.d: `coneEquiv` on the first coordinate (rfl). -/
private theorem coneEquiv_fst (z : Tot 𝒜 (coneQ M N)) :
    (coneEquiv M N z).1 = shiftIota 𝒜 M.Q 1 (Tot.prodEquiv 𝒜 N.Q (shiftQ M.Q 1) z).2 := rfl

/-- Z2.d: `coneEquiv` and total degree. -/
private theorem coneEquiv_mem_iff (m : ℤ) (z : Tot 𝒜 (coneQ M N)) :
    z ∈ totDeg 𝒜 (coneQ M N) m ↔
      (coneEquiv M N z).1 ∈ totDeg 𝒜 M.Q (m + 1) ∧ (coneEquiv M N z).2 ∈ totDeg 𝒜 N.Q m := by
  rw [Tot.prodEquiv_mem_totDeg_iff, coneEquiv_fst, coneEquiv_snd,
    shiftIota_mem_totDeg_iff, and_comm]

/-- Z2.d: `coneEquiv` and the `A`-action, first coordinate. -/
private theorem coneEquiv_fst_smul {p : ℤ} {β : A} (hβ : β ∈ 𝒜 p) (z : Tot 𝒜 (coneQ M N)) :
    (coneEquiv M N (β • z)).1 = (1 * p).negOnePow • β • (coneEquiv M N z).1 := by
  rw [coneEquiv_fst, coneEquiv_fst, map_smul]
  exact shiftIota_smul M.Q 1 hβ _

/-- Z2.d: `coneEquiv` and the `A`-action, second coordinate. -/
private theorem coneEquiv_snd_smul (β : A) (z : Tot 𝒜 (coneQ M N)) :
    (coneEquiv M N (β • z)).2 = β • (coneEquiv M N z).2 := by
  rw [coneEquiv_snd, coneEquiv_snd, map_smul]
  rfl

/-- Z2.d: `fst ∘ inl = id`. -/
theorem coneFst_coneInl : coneFst M N ∘ₗ coneInl M N = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp [coneFst, coneInl]

/-- Z2.d: `snd ∘ inr = id`. -/
theorem coneSnd_coneInr : coneSnd M N ∘ₗ coneInr M N = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp [coneSnd, coneInr]

/-- Z2.d: `fst ∘ inr = 0`. -/
theorem coneFst_coneInr : coneFst M N ∘ₗ coneInr M N = 0 := by
  refine LinearMap.ext fun x => ?_
  simp [coneFst, coneInr]

/-- Z2.d: `snd ∘ inl = 0`. -/
theorem coneSnd_coneInl : coneSnd M N ∘ₗ coneInl M N = 0 := by
  refine LinearMap.ext fun x => ?_
  simp [coneSnd, coneInl]

/-- Z2.d: `inl ∘ fst + inr ∘ snd = id`. -/
theorem coneInl_coneFst_add : coneInl M N ∘ₗ coneFst M N + coneInr M N ∘ₗ coneSnd M N =
    LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  simp only [coneInl, coneInr, coneFst, coneSnd, LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.id_apply]
  rw [← map_add]
  convert (coneEquiv M N).symm_apply_apply z
  simp

/-- Z2.d: `inl` has degree `−1`. -/
theorem coneInl_mem_totDeg {m : ℤ} {x : M.T} (hx : x ∈ totDeg 𝒜 M.Q m) :
    coneInl M N x ∈ totDeg 𝒜 (coneQ M N) (m + -1) := by
  rw [coneEquiv_mem_iff]
  have : (coneEquiv M N (coneInl M N x)) = (x, 0) := by simp [coneInl]
  rw [this]
  exact ⟨by simpa using hx, zero_mem _⟩

/-- Z2.d: `inr` has degree `0`. -/
theorem coneInr_mem_totDeg {m : ℤ} {y : N.T} (hy : y ∈ totDeg 𝒜 N.Q m) :
    coneInr M N y ∈ totDeg 𝒜 (coneQ M N) (m + 0) := by
  rw [coneEquiv_mem_iff]
  have : (coneEquiv M N (coneInr M N y)) = (0, y) := by simp [coneInr]
  rw [this]
  exact ⟨zero_mem _, by simpa using hy⟩

/-- Z2.d: `fst` has degree `1`. -/
theorem coneFst_mem_totDeg {m : ℤ} {z : Tot 𝒜 (coneQ M N)} (hz : z ∈ totDeg 𝒜 (coneQ M N) m) :
    coneFst M N z ∈ totDeg 𝒜 M.Q (m + 1) :=
  ((coneEquiv_mem_iff M N m z).1 hz).1

/-- Z2.d: `snd` has degree `0`. -/
theorem coneSnd_mem_totDeg {m : ℤ} {z : Tot 𝒜 (coneQ M N)} (hz : z ∈ totDeg 𝒜 (coneQ M N) m) :
    coneSnd M N z ∈ totDeg 𝒜 N.Q (m + 0) := by
  rw [add_zero]
  exact ((coneEquiv_mem_iff M N m z).1 hz).2

/-- Z2.d: `fst(β z) = (−1)^{|β|} β fst(z)` (degree `1`). -/
theorem coneFst_smul {p : ℤ} {β : A} (hβ : β ∈ 𝒜 p) (z : Tot 𝒜 (coneQ M N)) :
    coneFst M N (β • z) = (1 * p).negOnePow • β • coneFst M N z :=
  coneEquiv_fst_smul M N hβ z

/-- Z2.d: `snd` is `A`-linear. -/
theorem coneSnd_smul (β : A) (z : Tot 𝒜 (coneQ M N)) : coneSnd M N (β • z) = β • coneSnd M N z :=
  coneEquiv_snd_smul M N β z

/-- Z2.d: `inl(β e) = (−1)^{|β|} β inl(e)` (degree `−1`). -/
theorem coneInl_smul {p : ℤ} {β : A} (hβ : β ∈ 𝒜 p) (x : M.T) :
    coneInl M N (β • x) = (-1 * p).negOnePow • β • coneInl M N x := by
  apply (coneEquiv M N).injective
  refine Prod.ext ?_ ?_
  · have h1 : (coneEquiv M N (coneInl M N (β • x))).1 = β • x := by simp [coneInl]
    have h2 : (coneEquiv M N (coneInl M N x)).1 = x := by simp [coneInl]
    rw [h1, Units.smul_def, map_zsmul, Prod.smul_fst, coneEquiv_fst_smul M N hβ, h2,
      ← Units.smul_def, smul_smul, neg_mul, Int.negOnePow_neg, one_mul]
    rw [Int.units_mul_self, one_smul]
  · have h1 : (coneEquiv M N (coneInl M N (β • x))).2 = 0 := by simp [coneInl]
    have h2 : (coneEquiv M N (coneInl M N x)).2 = 0 := by simp [coneInl]
    rw [h1, Units.smul_def, map_zsmul, Prod.smul_snd, coneEquiv_snd_smul, h2]
    simp

/-- Z2.d: `inr` is `A`-linear. -/
theorem coneInr_smul (β : A) (y : N.T) : coneInr M N (β • y) = β • coneInr M N y := by
  apply (coneEquiv M N).injective
  refine Prod.ext ?_ ?_
  · have h1 : (coneEquiv M N (coneInr M N (β • y))).1 = 0 := by simp [coneInr]
    have h2 : (coneEquiv M N (coneInr M N y)).1 = 0 := by simp [coneInr]
    rw [h1, coneEquiv_fst, map_smul]
    rw [coneEquiv_fst, map_eq_zero_iff _ (shiftIota 𝒜 M.Q 1).injective] at h2
    rw [Prod.smul_snd, h2, smul_zero, map_zero]
  · have h1 : (coneEquiv M N (coneInr M N (β • y))).2 = β • y := by simp [coneInr]
    have h2 : (coneEquiv M N (coneInr M N y)).2 = y := by simp [coneInr]
    rw [h1, coneEquiv_snd_smul, h2]

/-- Z2.d: pointwise `fst (inl x) = x`. -/
@[simp] private theorem coneFst_inl_apply (x : M.T) : coneFst M N (coneInl M N x) = x :=
  LinearMap.congr_fun (coneFst_coneInl M N) x

/-- Z2.d: pointwise `snd (inr y) = y`. -/
@[simp] private theorem coneSnd_inr_apply (y : N.T) : coneSnd M N (coneInr M N y) = y :=
  LinearMap.congr_fun (coneSnd_coneInr M N) y

/-- Z2.d: pointwise `fst (inr y) = 0`. -/
@[simp] private theorem coneFst_inr_apply (y : N.T) : coneFst M N (coneInr M N y) = 0 :=
  LinearMap.congr_fun (coneFst_coneInr M N) y

/-- Z2.d: pointwise `snd (inl x) = 0`. -/
@[simp] private theorem coneSnd_inl_apply (x : M.T) : coneSnd M N (coneInl M N x) = 0 :=
  LinearMap.congr_fun (coneSnd_coneInl M N) x

/-- Z2.d: pointwise `inl (fst z) + inr (snd z) = z`. -/
private theorem cone_decomp (z : Tot 𝒜 (coneQ M N)) :
    coneInl M N (coneFst M N z) + coneInr M N (coneSnd M N z) = z :=
  LinearMap.congr_fun (coneInl_coneFst_add M N) z

variable {M N} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive)

/-- **Z2.d.** [B, §2.4]. The operator of the cone, `𝕏_C = inr 𝕏_N snd + inr φ fst − inl 𝕏_M fst`
(Block's matrix `[[𝕏_N, φ], [0, 𝕏_M[1]]]` on `inr f + inl e`). -/
def coneX : Tot 𝒜 (coneQ M N) →ₗ[k] Tot 𝒜 (coneQ M N) :=
  coneInr M N ∘ₗ N.X ∘ₗ coneSnd M N + coneInr M N ∘ₗ φ.1 ∘ₗ coneFst M N -
    coneInl M N ∘ₗ M.X ∘ₗ coneFst M N

/-- Z2.d: `coneX` unfolded pointwise. -/
private theorem coneX_apply (z : Tot 𝒜 (coneQ M N)) :
    coneX φ z = coneInr M N (N.X (coneSnd M N z)) + coneInr M N (φ.1 (coneFst M N z)) -
      coneInl M N (M.X (coneFst M N z)) := rfl

/-- Z2.d: `𝕏_C (inl x) = inr (φ x) - inl (𝕏 x)`. -/
private theorem coneX_inl (x : M.T) :
    coneX φ (coneInl M N x) = coneInr M N (φ.1 x) - coneInl M N (M.X x) := by
  simp [coneX_apply]

/-- Z2.d: `𝕏_C (inr y) = inr (𝕏 y)`. -/
private theorem coneX_inr (y : N.T) : coneX φ (coneInr M N y) = coneInr M N (N.X y) := by
  simp [coneX_apply]

/-- Z2.d: `fst (𝕏_C z) = - 𝕏 (fst z)`. -/
private theorem coneFst_coneX (z : Tot 𝒜 (coneQ M N)) :
    coneFst M N (coneX φ z) = -M.X (coneFst M N z) := by
  simp [coneX_apply]

/-- Z2.d: `snd (𝕏_C z) = 𝕏 (snd z) + φ (fst z)`. -/
private theorem coneSnd_coneX (z : Tot 𝒜 (coneQ M N)) :
    coneSnd M N (coneX φ z) = N.X (coneSnd M N z) + φ.1 (coneFst M N z) := by
  simp [coneX_apply]

/-- Z2.d: the degree-`0` closed map `φ` is `A`-linear up to the trivial sign. -/
private theorem Z0_smul {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (x : M.T) :
    φ.1 (a • x) = a • φ.1 x := by
  have := (Submodule.mem_inf.1 φ.2).1.2 ha x
  simpa using this

/-- Z2.d: `𝕏_N ∘ φ = φ ∘ 𝕏_M` (from `δφ = 0`). -/
private theorem Z0_comm (x : M.T) : N.X (φ.1 x) = φ.1 (M.X x) := by
  have := LinearMap.congr_fun (LinearMap.mem_ker.1 (Submodule.mem_inf.1 φ.2).2) x
  rw [δ_apply] at this
  simpa [sub_eq_zero] using this

/-- Z2.d: `𝕏_C` has degree `1`. -/
theorem coneX_mem {m : ℤ} {z : Tot 𝒜 (coneQ M N)} (hz : z ∈ totDeg 𝒜 (coneQ M N) m) :
    coneX φ z ∈ totDeg 𝒜 (coneQ M N) (m + 1) := by
  have h1 := coneInr_mem_totDeg M N (N.X_mem (coneSnd_mem_totDeg M N hz))
  have h2 := coneInr_mem_totDeg M N
    ((Submodule.mem_inf.1 φ.2).1.1 (coneFst_mem_totDeg M N hz))
  have h3 := coneInl_mem_totDeg M N (M.X_mem (coneFst_mem_totDeg M N hz))
  rw [coneX_apply]
  refine sub_mem (add_mem ?_ ?_) ?_
  · rwa [add_zero, add_zero] at h1
  · rwa [add_zero, add_zero] at h2
  · rwa [show m + 1 + 1 + -1 = m + 1 by ring] at h3

/-- Z2.d: the Leibniz rule for `𝕏_C`. -/
theorem coneX_leibniz {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (z : Tot 𝒜 (coneQ M N)) :
    coneX φ (a • z) = GCDga.d (𝒜 := 𝒜) a • z + p.negOnePow • a • coneX φ z := by
  have hd := GCDga.d_mem (𝒜 := 𝒜) ha
  conv_lhs => rw [coneX_apply, coneSnd_smul, coneFst_smul M N ha, N.leibniz ha]
  rw [coneX_apply]
  have e4 := cone_decomp M N z
  have e5 : GCDga.d (𝒜 := 𝒜) a • z =
      GCDga.d (𝒜 := 𝒜) a • coneInl M N (coneFst M N z) +
        GCDga.d (𝒜 := 𝒜) a • coneInr M N (coneSnd M N z) := by rw [← smul_add, e4]
  rw [e5]
  simp only [Units.smul_def, map_zsmul, Z0_smul φ ha, M.leibniz ha, map_add, coneInr_smul,
    coneInl_smul M N ha, coneInl_smul M N hd, smul_add, smul_sub, smul_smul]
  simp only [one_mul, neg_mul, Int.negOnePow_neg, Int.negOnePow_succ]
  generalize p.negOnePow = s
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp <;> abel

/-- Z2.d: `𝕏_C² = c` (from `𝕏_M² = c`, `𝕏_N² = c`, `δφ = 0` and the identities). -/
theorem coneX_flat (z : Tot 𝒜 (coneQ M N)) :
    coneX φ (coneX φ z) = GCDga.c (𝒜 := 𝒜) • z := by
  have hc := GCDga.c_mem (𝒜 := 𝒜)
  have hz : coneX φ z = coneInr M N (N.X (coneSnd M N z) + φ.1 (coneFst M N z)) -
      coneInl M N (M.X (coneFst M N z)) := by rw [coneX_apply, map_add]
  have e5 : GCDga.c (𝒜 := 𝒜) • z = GCDga.c (𝒜 := 𝒜) • coneInl M N (coneFst M N z) +
      GCDga.c (𝒜 := 𝒜) • coneInr M N (coneSnd M N z) := by rw [← smul_add, cone_decomp]
  have hs : ((-1 * 2 : ℤ).negOnePow) = 1 := by decide
  rw [hz, map_sub, coneX_inr, coneX_inl, map_add, map_add, Z0_comm φ, M.flat, N.flat, e5,
    coneInl_smul M N hc, hs, coneInr_smul, one_smul]
  abel

/-- **Z2.d.** [B, §2.4]. The cone `C(φ)` of a closed degree-`0` map `φ : M → N`: generators
`Q_N^p × Q_M^{p+1}`, operator `coneX φ`. -/
def cone : CohesiveModule 𝒜 where
  Q := coneQ M N
  X := coneX φ
  X_mem := coneX_mem φ
  leibniz := coneX_leibniz φ
  flat := coneX_flat φ
  bounded := by
    obtain ⟨a₁, b₁, h₁⟩ := M.bounded
    obtain ⟨a₂, b₂, h₂⟩ := N.bounded
    refine ⟨min a₂ (a₁ - 1), max b₂ (b₁ - 1), fun p hp => ?_⟩
    have := h₂ p (by omega)
    have := h₁ (p + 1) (by omega)
    exact inferInstanceAs (Subsingleton (N.Q p × M.Q (p + 1)))
  finite p := by
    have := N.finite p
    have := M.finite (p + 1)
    exact inferInstanceAs (Module.Finite (𝒜 0) (N.Q p × M.Q (p + 1)))
  projective p := by
    have := N.projective p
    have := M.projective (p + 1)
    exact inferInstanceAs (Module.Projective (𝒜 0) (N.Q p × M.Q (p + 1)))

/-- Z2.d: the operator of `C(φ)` (rfl). -/
theorem cone_X : (cone φ).X = coneX φ := rfl

/-- **Z2.d.** `inl ∈ Hom^{−1}(M, C(φ))`. -/
theorem coneInl_mem_hom : coneInl M N ∈ Hom M.toQuasiCohesive (cone φ).toQuasiCohesive (-1) :=
  ⟨fun hx => coneInl_mem_totDeg M N hx, fun hβ x => coneInl_smul M N hβ x⟩

/-- **Z2.d.** `inr ∈ Hom^0(N, C(φ))`. -/
theorem coneInr_mem_hom : coneInr M N ∈ Hom N.toQuasiCohesive (cone φ).toQuasiCohesive 0 :=
  ⟨fun hy => coneInr_mem_totDeg M N hy, fun {_ a} _ y => by
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    exact coneInr_smul M N a y⟩

/-- **Z2.d.** `fst ∈ Hom^1(C(φ), M)`. -/
theorem coneFst_mem_hom : coneFst M N ∈ Hom (cone φ).toQuasiCohesive M.toQuasiCohesive 1 :=
  ⟨fun hz => coneFst_mem_totDeg M N hz, fun hβ z => coneFst_smul M N hβ z⟩

/-- **Z2.d.** `snd ∈ Hom^0(C(φ), N)`. -/
theorem coneSnd_mem_hom : coneSnd M N ∈ Hom (cone φ).toQuasiCohesive N.toQuasiCohesive 0 :=
  ⟨fun hz => coneSnd_mem_totDeg M N hz, fun {_ a} _ z => by
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    exact coneSnd_smul M N a z⟩

/-- **Z2.d.** Mathlib's `δ_inl`: `δ inl = inr ∘ φ`. -/
theorem δ_coneInl :
    δ M.toQuasiCohesive (cone φ).toQuasiCohesive (-1) (coneInl M N) = coneInr M N ∘ₗ φ.1 := by
  refine LinearMap.ext fun x => ?_
  change coneX φ (coneInl M N x) - (-1 : ℤ).negOnePow • coneInl M N (M.X x) =
    coneInr M N (φ.1 x)
  rw [coneX_inl]
  simp

/-- **Z2.d.** `δ inr = 0`. -/
theorem δ_coneInr : δ N.toQuasiCohesive (cone φ).toQuasiCohesive 0 (coneInr M N) = 0 := by
  refine LinearMap.ext fun y => ?_
  change coneX φ (coneInr M N y) - (0 : ℤ).negOnePow • coneInr M N (N.X y) = 0
  rw [coneX_inr]
  simp

/-- **Z2.d.** `δ fst = 0`. -/
theorem δ_coneFst : δ (cone φ).toQuasiCohesive M.toQuasiCohesive 1 (coneFst M N) = 0 := by
  refine LinearMap.ext fun (z : Tot 𝒜 (coneQ M N)) => ?_
  change M.X (coneFst M N z) - (1 : ℤ).negOnePow • coneFst M N (coneX φ z) = 0
  rw [coneFst_coneX]
  simp

/-- **Z2.d.** Mathlib's `δ_snd`: `δ snd = −φ ∘ fst`. -/
theorem δ_coneSnd :
    δ (cone φ).toQuasiCohesive N.toQuasiCohesive 0 (coneSnd M N) = -(φ.1 ∘ₗ coneFst M N) := by
  refine LinearMap.ext fun (z : Tot 𝒜 (coneQ M N)) => ?_
  change N.X (coneSnd M N z) - (0 : ℤ).negOnePow • coneSnd M N (coneX φ z) =
    -φ.1 (coneFst M N z)
  rw [coneSnd_coneX]
  simp

end Cohesive
