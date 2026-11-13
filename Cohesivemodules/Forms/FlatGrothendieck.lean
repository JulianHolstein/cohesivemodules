import Cohesivemodules.Analysis.CauchySolve
import Cohesivemodules.Forms.Contraction
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option linter.style.header false

/-!
# Z4.e: the flat Dolbeault–Grothendieck lemma on open subsets of `E`

Blueprint item Z4.e (§11, v1.14; `blueprint/blueprint-dg.md` §D with the audit's corrections B.1,
B.2 and simplifications S2, S3). For an open `U ⊆ E`, `x ∈ U` and a form `ω` of degree `q + 1`,
real `C^∞` on `U` with `∂̄ω = 0` on `U`, there are an open `U′ ∋ x` inside `U` and a form `η` of
degree `q`, `C^∞` on all of `E`, with `∂̄η = ω` on `U′` (`exists_dbar_eq`).

Proof (Hörmander, Thm 2.3.3; Griffiths–Harris, p. 25): induction on `k`, the number of basis
directions `dz̄_0, …, dz̄_{k−1}` that `ω` involves (`InvolvesOnly`, Z4.d). Step (`exists_step`):
`α = ι_{b_k} ω`; cut off (`exists_cutoff`, S2) and solve `∂̄_k G = α` near `x` with the parametric
solver (Z4.c), keeping `G` holomorphic in the directions `j > k` (`dbarPart_cauchySolve_comm`,
B5) and free of `dz̄_j`, `j ≥ k` (`involvesOnly_cauchySolve`); then `ω − ∂̄G` involves only
`dz̄_0, …, dz̄_{k−1}` near `x` (B4, Z4.d).

Basis: `e = Module.finBasis ℂ E` of `E`, and `conjBasis E = Conj.basis e` of `Ē` (the same
vectors, F2.c); `∂̄_j = D″(·)(conjBasis E j)`, `½ (D e_j + i D (i e_j))`.

## Deviations
* blueprint-dg works on `Fin n → ℂ` with sup-norm polydiscs and a cutoff in the `k`-th variable;
  here `E` is any finite-dimensional space, the cutoff is applied before solving (S2), and `η` is
  `C^∞` on all of `E` (S3). The induction step splits on `q = 0` / `q ≥ 1` (audit B.2).
-/

noncomputable section

namespace Cohesive

open Conj Filter Topology Set
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

variable (E) in
/-- **Z4.e.** The basis of `Ē` given by `Module.finBasis ℂ E` (F2.c: the same vectors). -/
def conjBasis : Module.Basis (Fin (Module.finrank ℂ E)) ℂ (Conj E) :=
  Conj.basis (Module.finBasis ℂ E)

/-- Z4.e: `conjBasis E j = toConj (finBasis j)`. -/
theorem conjBasis_apply (j : Fin (Module.finrank ℂ E)) :
    conjBasis E j = toConj (Module.finBasis ℂ E j) :=
  Conj.basis_apply _ j

omit [FiniteDimensional ℂ E] in
/-- **Z4.e (C2).** `D″` along `v` of the solver in direction `v` is `F` (Z4.c (iii) in the F3
normalization). -/
theorem dbarPart_cauchySolve {q : ℕ} {v : E} (hv : v ≠ 0) {F : E → DolbeaultFibre E q ℂ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (z : E) :
    dbarPart (cauchySolve v F) z (toConj v) = F z := by
  have := dbar_cauchySolve hv hF hc z
  simpa only [dbarPart, antiPart_apply, ofConj_toConj] using this

omit [FiniteDimensional ℂ E] in
/-- **Z4.e (C3).** `D″` of the solver along any `w` is the solver of `D″F` along `w`
(Z4.c (i′) and (ii)). -/
theorem dbarPart_cauchySolve_comm {q : ℕ} {v : E} (hv : v ≠ 0) {F : E → DolbeaultFibre E q ℂ}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) (w : Conj E) (z : E) :
    dbarPart (cauchySolve v F) z w = cauchySolve v (fun y => dbarPart F y w) z := by
  let T : (E →L[ℝ] DolbeaultFibre E q ℂ) →L[ℂ] DolbeaultFibre E q ℂ :=
    { toFun := fun A => antiPart A w
      map_add' := fun A B => by rw [antiPart_add]; rfl
      map_smul' := fun c A => by rw [antiPart_smul]; rfl
      cont := (ContinuousLinearMap.apply ℂ (DolbeaultFibre E q ℂ) w).continuous.comp
        (antiPartCLM E (DolbeaultFibre E q ℂ)).continuous }
  have h1 := map_cauchySolve T hv (hF.continuous_fderiv one_ne_zero) (hc.fderiv ℝ) z
  rw [← (hasFDerivAt_cauchySolve hv hF hc z).fderiv] at h1
  exact h1

/-- **Z4.e (C4).** If every value of `F` involves only `dz̄_0, …, dz̄_{k−1}`, so does every value of
its solver (Z4.c (ii) with the contractions). -/
theorem involvesOnly_cauchySolve {q : ℕ} {v : E} (hv : v ≠ 0)
    {F : E → DolbeaultFibre E (q + 1) ℂ} (hF : Continuous F) (hc : HasCompactSupport F) {k : ℕ}
    (hk : ∀ y, InvolvesOnly (conjBasis E) k (F y)) (z : E) :
    InvolvesOnly (conjBasis E) k (cauchySolve v F z) := by
  intro j hj
  rw [map_cauchySolve (ctr (conjBasis E j)) hv hF hc z]
  have : (fun y => ctr (conjBasis E j) (F y)) = fun _ => 0 := funext fun y => hk y j hj
  rw [this]
  simp [cauchySolve]

/-- **Z4.e (cutoff, audit S2).** For `x ∈ U` open and a basis index `k`, a real `C^∞` function
`ψ` with compact support in `U`, equal to `1` on an open `W ∋ x`, and an open slab `S ⊇ W`,
stable under `z ↦ z − t • e_k` (`t ∈ ℂ`), on which `ψ` has zero derivative in the directions
`e_j`, `i e_j` for `j ≠ k` (e.g. `ψ(z) = χ₁(c_k(z − x)) χ₂(P(z − x))`, `P` killing `e_k`). -/
theorem exists_cutoff {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (k : Fin (Module.finrank ℂ E)) :
    ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
      ∃ W S : Set E, IsOpen W ∧ x ∈ W ∧ IsOpen S ∧ W ⊆ S ∧ (∀ z ∈ W, ψ z = 1) ∧
        (∀ z ∈ S, ∀ t : ℂ, z - t • Module.finBasis ℂ E k ∈ S) ∧
        (∀ z ∈ S, ∀ j, j ≠ k → fderiv ℝ ψ z (Module.finBasis ℂ E j) = 0 ∧
          fderiv ℝ ψ z (Complex.I • Module.finBasis ℂ E j) = 0) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hU x hx
  set e := Module.finBasis ℂ E with he
  let c : E →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (e.coord k)
  have hc_apply : ∀ z, c z = e.coord k z := fun z => rfl
  have hc_self : c (e k) = 1 := by rw [hc_apply]; simp
  have hc_ne : ∀ j, j ≠ k → c (e j) = 0 := by
    intro j hj; rw [hc_apply]; simp [Module.Basis.coord_apply, hj]
  let P : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - c.smulRight (e k)
  have hP : ∀ z, P z = z - c z • e k := fun z => rfl
  have hPk : P (e k) = 0 := by rw [hP, hc_self]; simp
  have hdec : ∀ z, z = c z • e k + P z := fun z => by rw [hP]; abel
  set r : ℝ := ρ / (4 * (‖e k‖ + 1)) with hr
  have hr0 : 0 < r := by positivity
  let χ₁ : ContDiffBump (0 : ℂ) := ⟨r, 2 * r, hr0, by linarith⟩
  let χ₂ : ContDiffBump (0 : E) := ⟨r, 2 * r, hr0, by linarith⟩
  have hcc : Continuous fun z : E => c (z - x) :=
    c.continuous.comp (continuous_id.sub continuous_const)
  have hPc : Continuous fun z : E => P (z - x) :=
    P.continuous.comp (continuous_id.sub continuous_const)
  let ψ : E → ℝ := fun z => χ₁ (c (z - x)) * χ₂ (P (z - x))
  have hψ : ContDiff ℝ ∞ ψ := by
    refine (χ₁.contDiff.comp ?_).mul (χ₂.contDiff.comp ?_)
    · exact (c.restrictScalars ℝ).contDiff.comp (contDiff_id.sub contDiff_const)
    · exact (P.restrictScalars ℝ).contDiff.comp (contDiff_id.sub contDiff_const)
  have hsupp : tsupport ψ ⊆ {z | ‖c (z - x)‖ ≤ 2 * r ∧ ‖P (z - x)‖ ≤ 2 * r} := by
    refine closure_minimal ?_ ?_
    · intro z hz
      have h1 : χ₁ (c (z - x)) ≠ 0 := left_ne_zero_of_mul hz
      have h2 : χ₂ (P (z - x)) ≠ 0 := right_ne_zero_of_mul hz
      have h1' := (χ₁.support_eq ▸ h1 : c (z - x) ∈ Metric.ball (0 : ℂ) (2 * r))
      have h2' := (χ₂.support_eq ▸ h2 : P (z - x) ∈ Metric.ball (0 : E) (2 * r))
      simp only [mem_ball_zero_iff] at h1' h2'
      exact ⟨h1'.le, h2'.le⟩
    · exact (isClosed_le (continuous_norm.comp hcc) continuous_const).inter
        (isClosed_le (continuous_norm.comp hPc) continuous_const)
  have hR : ∀ z ∈ {z : E | ‖c (z - x)‖ ≤ 2 * r ∧ ‖P (z - x)‖ ≤ 2 * r},
      z ∈ Metric.closedBall x (2 * r * (‖e k‖ + 1)) := by
    rintro z ⟨h1, h2⟩
    rw [mem_closedBall_iff_norm]
    calc ‖z - x‖ = ‖c (z - x) • e k + P (z - x)‖ := by rw [← hdec]
      _ ≤ ‖c (z - x)‖ * ‖e k‖ + ‖P (z - x)‖ :=
        (norm_add_le _ _).trans (by rw [norm_smul])
      _ ≤ 2 * r * ‖e k‖ + 2 * r := by gcongr
      _ = _ := by ring
  have hRρ : 2 * r * (‖e k‖ + 1) < ρ := by
    have : 2 * r * (‖e k‖ + 1) = ρ / 2 := by rw [hr]; field_simp; ring
    rw [this]; linarith
  have hsubU : tsupport ψ ⊆ U := fun z hz =>
    hball (lt_of_le_of_lt (mem_closedBall_iff_norm.1 (hR z (hsupp hz)) |>.trans_eq'
      (by simp [dist_eq_norm])) hRρ)
  refine ⟨ψ, hψ, ?_, hsubU, {z | ‖c (z - x)‖ < r ∧ ‖P (z - x)‖ < r}, {z | ‖P (z - x)‖ < r},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall x (2 * r * (‖e k‖ + 1))).of_isClosed_subset isClosed_closure
      (closure_minimal (fun z hz => hR z (hsupp (subset_closure hz))) Metric.isClosed_closedBall)
  · exact (isOpen_lt (continuous_norm.comp hcc) continuous_const).inter
      (isOpen_lt (continuous_norm.comp hPc) continuous_const)
  · simpa using hr0
  · exact isOpen_lt (continuous_norm.comp hPc) continuous_const
  · exact fun z hz => hz.2
  · intro z hz
    have h1 : χ₁ (c (z - x)) = 1 := χ₁.one_of_mem_closedBall (by
      simpa [mem_closedBall_zero_iff] using hz.1.le)
    have h2 : χ₂ (P (z - x)) = 1 := χ₂.one_of_mem_closedBall (by
      simpa [mem_closedBall_zero_iff] using hz.2.le)
    show χ₁ (c (z - x)) * χ₂ (P (z - x)) = 1
    rw [h1, h2, one_mul]
  · intro z hz t
    change ‖P (z - x)‖ < r at hz
    change ‖P (z - t • e k - x)‖ < r
    have : P (z - t • e k - x) = P (z - x) := by
      have : z - t • e k - x = (z - x) - t • e k := by abel
      rw [this, map_sub, map_smul, hPk, smul_zero, sub_zero]
    rw [this]; exact hz
  · intro z hz j hj
    have hS : IsOpen {z : E | ‖P (z - x)‖ < r} :=
      isOpen_lt (continuous_norm.comp hPc) continuous_const
    have hev : ψ =ᶠ[𝓝 z] fun w => χ₁ (c (w - x)) := by
      filter_upwards [hS.mem_nhds hz] with w hw
      have h2 : χ₂ (P (w - x)) = 1 := χ₂.one_of_mem_closedBall (by
        simpa [mem_closedBall_zero_iff] using hw.le)
      show χ₁ (c (w - x)) * χ₂ (P (w - x)) = _
      rw [h2, mul_one]
    rw [hev.fderiv_eq]
    have hd : HasFDerivAt (fun w => χ₁ (c (w - x)))
        ((fderiv ℝ χ₁ (c (z - x))).comp (c.restrictScalars ℝ)) z :=
      ((χ₁.contDiff (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp z
        ((c.restrictScalars ℝ).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
    rw [hd.fderiv]
    simp [hc_ne j hj]

omit [FiniteDimensional ℂ E] in
/-- **Z4.e.** Cutting off a function `C^∞` on `U` by `ψ` with compact support in `U` gives a
function `C^∞` on `E` with compact support. -/
theorem contDiff_cutoff_smul {U : Set E} (hU : IsOpen U) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) {Λ : Type} [NormedAddCommGroup Λ]
    [NormedSpace ℂ Λ] {α : E → Λ} (hα : ContDiffOn ℝ ∞ α U) :
    ContDiff ℝ ∞ (fun z => (ψ z : ℂ) • α z) ∧ HasCompactSupport (fun z => (ψ z : ℂ) • α z) := by
  refine ⟨contDiff_iff_contDiffAt.2 fun z => ?_, ?_⟩
  · by_cases hz : z ∈ tsupport ψ
    · have h1 : ContDiffAt ℝ ∞ (fun y => (ψ y : ℂ)) z :=
        (Complex.ofRealCLM.contDiff.comp hψ).contDiffAt
      exact h1.smul (hα.contDiffAt (hU.mem_nhds (hψU hz)))
    · have : ψ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz
      refine (contDiffAt_const (c := (0 : Λ))).congr_of_eventuallyEq ?_
      filter_upwards [this] with y hy
      simp [hy]
  · refine hψc.mono ?_
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro h
    exact hy (by simp [h])

omit [FiniteDimensional ℂ E] in
/-- Z4.e helper (public for Z5.c): product rule for a real cutoff times a function. -/
theorem fderiv_cutoff_smul {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
    {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {α : E → Λ} {y : E} (hα : DifferentiableAt ℝ α y)
    (v : E) :
    fderiv ℝ (fun z => (ψ z : ℂ) • α z) y v =
      (fderiv ℝ ψ y v : ℂ) • α y + (ψ y : ℂ) • fderiv ℝ α y v := by
  have h1 : HasFDerivAt (fun z => (ψ z : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ ψ y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y
      (((hψ.differentiable (by simp)).differentiableAt (x := y)).hasFDerivAt)
  have := h1.smul hα.hasFDerivAt
  rw [show (fun z => (ψ z : ℂ) • α z) = (fun z => (ψ z : ℂ)) • α from rfl, this.fderiv]
  simp [add_comm]

omit [FiniteDimensional ℂ E] in
/-- Z4.e helper (public for Z5.c): a cut-off function vanishing near `y` has zero derivative at
`y`. -/
theorem fderiv_cutoff_smul_of_notMem {Λ : Type} [NormedAddCommGroup Λ]
    [NormedSpace ℂ Λ] {ψ : E → ℝ} {y : E} (hy : y ∉ tsupport ψ) (α : E → Λ) :
    fderiv ℝ (fun z => (ψ z : ℂ) • α z) y = 0 := by
  have : ψ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.1 hy
  have h2 : (fun z => (ψ z : ℂ) • α z) =ᶠ[𝓝 y] fun _ => (0 : Λ) := by
    filter_upwards [this] with z hz
    simp [hz]
  rw [h2.fderiv_eq]
  simp

omit [FiniteDimensional ℂ E] in
/-- Z4.e helper (public for Z5.c): the solver of a function vanishing on a slab stable under
`z ↦ z − t • v` vanishes on it. -/
theorem cauchySolve_eq_zero {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
    {v : E} {S : Set E} (hS : ∀ z ∈ S, ∀ t : ℂ, z - t • v ∈ S) {F : E → Λ}
    (hF : ∀ y ∈ S, F y = 0) {z : E} (hz : z ∈ S) : cauchySolve v F z = 0 := by
  unfold cauchySolve
  have : (fun t : ℂ => t⁻¹ • F (z - t • v)) = fun _ => 0 := by
    funext t; rw [hF _ (hS z hz t), smul_zero]
  rw [this]
  simp

/-- The `∂̄`-part of the cut-off form vanishes in the directions `b m`, `m > k`, on the slab. -/
private theorem dbarPart_cutoff_eq_zero {q : ℕ} (k : Fin (Module.finrank ℂ E)) {U : Set E}
    (hU : IsOpen U) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψU : tsupport ψ ⊆ U) {S : Set E}
    (hψS : ∀ z ∈ S, ∀ j, j ≠ k → fderiv ℝ ψ z (Module.finBasis ℂ E j) = 0 ∧
      fderiv ℝ ψ z (Complex.I • Module.finBasis ℂ E j) = 0)
    (β : E → DolbeaultFibre E (q + 1) ℂ) (hβ : ContDiffOn ℝ ∞ β U)
    (hk : ∀ z ∈ U, InvolvesOnly (conjBasis E) ((k : ℕ) + 1) (β z))
    (hc : ∀ z ∈ U, dbar β z = 0) (m : Fin (Module.finrank ℂ E)) (hm : (k : ℕ) < m)
    {y : E} (hy : y ∈ S) :
    dbarPart (fun z => (ψ z : ℂ) • ctr (conjBasis E k) (β z)) y (conjBasis E m) = 0 := by
  by_cases hyt : y ∈ tsupport ψ
  · have hyU : y ∈ U := hψU hyt
    have hβd : DifferentiableAt ℝ β y :=
      (hβ.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
    have hαd : DifferentiableAt ℝ (fun z => ctr (conjBasis E k) (β z)) y := by
      let L := (ctr (conjBasis E k) :
        DolbeaultFibre E (q + 1) ℂ →L[ℂ] DolbeaultFibre E q ℂ).restrictScalars ℝ
      exact L.differentiableAt.comp y hβd
    have hB5 := dbarPart_eq_zero_of_dbar_eq_zero hU
      (fun z hz => (hβ.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) hk hc m
      (by omega) y hyU
    have hα0 : dbarPart (fun z => ctr (conjBasis E k) (β z)) y (conjBasis E m) = 0 := by
      rw [dbarPart_comp_clm (ctr (conjBasis E k)) hβd]
      simp [hB5]
    have hne : m ≠ k := fun h => by omega
    obtain ⟨h1, h2⟩ := hψS y hy m hne
    unfold dbarPart at hα0 ⊢
    rw [conjBasis_apply m] at hα0 ⊢
    simp only [antiPart_apply, ofConj_toConj] at hα0 ⊢
    rw [fderiv_cutoff_smul hψ hαd, fderiv_cutoff_smul hψ hαd]
    simp only [h1, h2, Complex.ofReal_zero, zero_smul, zero_add]
    rw [smul_comm Complex.I, ← smul_add, smul_comm (2 : ℂ)⁻¹ (ψ y : ℂ), hα0, smul_zero]
  · unfold dbarPart
    rw [fderiv_cutoff_smul_of_notMem hyt (fun z => ctr (conjBasis E k) (β z))]
    simp

/-- A form `ψ • ι_{b_k} ω` involves only `dz̄_0, …, dz̄_{k−1}` when `ω` involves `≤ k`. -/
private theorem involvesOnly_cutoff {q : ℕ} (k : Fin (Module.finrank ℂ E)) {U : Set E}
    {ψ : E → ℝ} (hψU : tsupport ψ ⊆ U) (β : E → DolbeaultFibre E (q + 2) ℂ)
    (hk : ∀ z ∈ U, InvolvesOnly (conjBasis E) ((k : ℕ) + 1) (β z)) (y : E) :
    InvolvesOnly (conjBasis E) k ((ψ y : ℂ) • ctr (conjBasis E k) (β y)) := by
  intro j hj
  by_cases hy : y ∈ tsupport ψ
  · rw [map_smul, (hk y (hψU hy)).ctr_basis k j hj, smul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hy]
    simp

/-- **Z4.e (induction step, blueprint-dg D steps 1–5).** Let `ω` of degree `q + 1` be `C^∞` on the
open `U`, `∂̄ω = 0` on `U`, and involve only `dz̄_0, …, dz̄_k`. Then near `x ∈ U` there is a
`C^∞` form `G` of degree `q` on `E` such that `ω − ∂̄G` involves only `dz̄_0, …, dz̄_{k−1}`. -/
theorem exists_step {q : ℕ} (k : Fin (Module.finrank ℂ E)) {U : Set E} (hU : IsOpen U) {x : E}
    (hx : x ∈ U) (β : E → DolbeaultFibre E (q + 1) ℂ) (hβ : ContDiffOn ℝ ∞ β U)
    (hk : ∀ z ∈ U, InvolvesOnly (conjBasis E) ((k : ℕ) + 1) (β z))
    (hc : ∀ z ∈ U, dbar β z = 0) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ G : E → DolbeaultFibre E q ℂ, ContDiff ℝ ∞ G ∧
      ∀ z ∈ W, InvolvesOnly (conjBasis E) k (β z - dbar G z) := by
  obtain ⟨ψ, hψ, hψc, hψU, W, S, hWo, hxW, hSo, hWS, hψ1, hSst, hψS⟩ := exists_cutoff hU hx k
  have hv : Module.finBasis ℂ E k ≠ 0 := (Module.finBasis ℂ E).ne_zero k
  have hαU : ContDiffOn ℝ ∞ (fun z => ctr (conjBasis E k) (β z)) U := by
    let L := (ctr (conjBasis E k) :
        DolbeaultFibre E (q + 1) ℂ →L[ℂ] DolbeaultFibre E q ℂ).restrictScalars ℝ
    exact L.contDiff.comp_contDiffOn hβ
  obtain ⟨hF, hFc⟩ := contDiff_cutoff_smul hU hψ hψc hψU hαU
  have hF1 : ContDiff ℝ 1 (fun z => (ψ z : ℂ) • ctr (conjBasis E k) (β z)) :=
    hF.of_le (mod_cast le_top)
  have hGs := contDiff_cauchySolve hv hF hFc
  have hWU : W ⊆ U := fun z hz =>
    hψU (subset_tsupport _ (by rw [Function.mem_support, hψ1 z hz]; exact one_ne_zero))
  have ha : ∀ z ∈ W, dbarPart (cauchySolve (Module.finBasis ℂ E k)
      (fun z => (ψ z : ℂ) • ctr (conjBasis E k) (β z))) z (conjBasis E k) =
      ctr (conjBasis E k) (β z) := by
    intro z hz
    have h := dbarPart_cauchySolve hv hF1 hFc z
    rw [← conjBasis_apply] at h
    rw [h, hψ1 z hz]
    simp
  have hb : ∀ z ∈ W, ∀ m : Fin (Module.finrank ℂ E), (k : ℕ) < m →
      dbarPart (cauchySolve (Module.finBasis ℂ E k)
        (fun z => (ψ z : ℂ) • ctr (conjBasis E k) (β z))) z (conjBasis E m) = 0 := by
    intro z hz m hm
    rw [dbarPart_cauchySolve_comm hv hF1 hFc]
    exact cauchySolve_eq_zero hSst (fun y hy => dbarPart_cutoff_eq_zero k hU hψ hψU hψS β hβ hk hc
      m hm hy) (hWS hz)
  have hdb : ∀ z ∈ W, ∀ j : Fin (Module.finrank ℂ E), (k : ℕ) ≤ j →
      ctr (conjBasis E j) (dbar (cauchySolve (Module.finBasis ℂ E k)
        (fun z => (ψ z : ℂ) • ctr (conjBasis E k) (β z))) z) =
      dbarPart (cauchySolve (Module.finBasis ℂ E k)
        (fun z => (ψ z : ℂ) • ctr (conjBasis E k) (β z))) z (conjBasis E j) := by
    intro z hz j hj
    cases q with
    | zero => exact ctr_dbar_zero _ _ _
    | succ q' =>
      have hGd := (hGs.differentiable (by simp)) z
      have hz0 : (fun y => ctr (conjBasis E j) (cauchySolve (Module.finBasis ℂ E k)
          (fun z => (ψ z : ℂ) • ctr (conjBasis E k) (β z)) y)) =
          fun _ => (0 : DolbeaultFibre E q' ℂ) :=
        funext fun y => (involvesOnly_cauchySolve hv hF1.continuous hFc
          (fun y => involvesOnly_cutoff k hψU β hk y) y j hj :)
      have h0 : dbar (fun _ : E => (0 : DolbeaultFibre E q' ℂ)) z = 0 := by
        have e : dbarPart (fun _ : E => (0 : DolbeaultFibre E q' ℂ)) z = 0 := by
          unfold dbarPart
          rw [fderiv_fun_const]
          ext v
          simp
        rw [dbar, e]
        exact map_zero _
      rw [ctr_dbar hGd, hz0, h0, sub_zero]
  refine ⟨W, hWo, hxW, hWU, _, hGs, fun z hz j hj => ?_⟩
  rw [map_sub, hdb z hz j hj]
  rcases Nat.eq_or_lt_of_le hj with h | h
  · have : j = k := Fin.ext h.symm
    subst this
    rw [ha z hz, sub_self]
  · rw [hk z (hWU hz) j (by omega), hb z hz j h, sub_zero]

/-- **Z4.e (the induction, blueprint-dg D).** For every `k`: if `ω` of degree `q + 1` is `C^∞`
on the open `U`, `∂̄`-closed there, and involves only `dz̄_0, …, dz̄_{k−1}`, then near each
`x ∈ U` it is `∂̄η` for a form `η` of degree `q`, `C^∞` on `E`. -/
theorem exists_dbar_eq_of_involvesOnly {q : ℕ} (k : ℕ) {U : Set E} (hU : IsOpen U) {x : E}
    (hx : x ∈ U) (β : E → DolbeaultFibre E (q + 1) ℂ) (hβ : ContDiffOn ℝ ∞ β U)
    (hk : ∀ z ∈ U, InvolvesOnly (conjBasis E) k (β z)) (hc : ∀ z ∈ U, dbar β z = 0) :
    ∃ U' ⊆ U, IsOpen U' ∧ x ∈ U' ∧ ∃ η : E → DolbeaultFibre E q ℂ, ContDiff ℝ ∞ η ∧
      ∀ z ∈ U', dbar η z = β z := by
  induction k generalizing U x β with
  | zero =>
    refine ⟨U, subset_rfl, hU, hx, fun _ => 0, contDiff_const, fun z hz => ?_⟩
    rw [(hk z hz).eq_zero]
    have e : dbarPart (fun _ : E => (0 : DolbeaultFibre E q ℂ)) z = 0 := by
      unfold dbarPart
      rw [fderiv_fun_const]
      ext v
      simp
    rw [dbar, e]
    exact map_zero _
  | succ k ih =>
    by_cases h : k < Module.finrank ℂ E
    · obtain ⟨W, hWo, hxW, hWU, G, hGs, hG⟩ := exists_step ⟨k, h⟩ hU hx β hβ hk hc
      have hβ' : ContDiffOn ℝ ∞ (fun z => β z - dbar G z) W :=
        (hβ.mono hWU).sub (contDiffOn_dbar_infty hWo hGs.contDiffOn)
      have hdG : ∀ z ∈ W, DifferentiableAt ℝ (dbar G) z := fun z hz =>
        ((contDiffOn_dbar_infty hWo hGs.contDiffOn).contDiffAt
          (hWo.mem_nhds hz)).differentiableAt (by simp)
      have hc' : ∀ z ∈ W, dbar (fun z => β z - dbar G z) z = 0 := by
        intro z hz
        have hd' : DifferentiableAt ℝ (fun z => β z - dbar G z) z :=
          (hβ'.contDiffAt (hWo.mem_nhds hz)).differentiableAt (by simp)
        have h1 := dbar_add hd' (hdG z hz)
        have h2 : (fun z => β z - dbar G z) + dbar G = β := by
          funext y; simp
        rw [h2] at h1
        have h3 : dbar (fun y => dbar G y) z = 0 :=
          dbar_dbar (hGs.contDiffAt.of_le (by norm_num))
        rw [hc z (hWU hz)] at h1
        have h4 : dbar (dbar G) z = 0 := h3
        rw [h4, add_zero] at h1
        exact h1.symm
      obtain ⟨U', hU'W, hU'o, hxU', η', hη's, hη'⟩ := ih hWo hxW _ hβ' hG hc'
      refine ⟨U', hU'W.trans hWU, hU'o, hxU', fun z => η' z + G z, hη's.add hGs, fun z hz => ?_⟩
      have hd1 : DifferentiableAt ℝ η' z := hη's.differentiable (by simp) z
      have hd2 : DifferentiableAt ℝ G z := hGs.differentiable (by simp) z
      have := dbar_add hd1 hd2
      change dbar (η' + G) z = _
      rw [this, hη' z hz]
      simp
    · refine ih hU hx β hβ (fun z hz j hj => ?_) hc
      exact absurd (lt_of_lt_of_le j.2 (not_lt.1 h |>.trans hj)) (lt_irrefl _)

/-- **Z4.e. Flat Dolbeault–Grothendieck lemma.** [Hörmander, Thm 2.3.3], [Griffiths–Harris,
p. 25]. Let `U ⊆ E` be open, `x ∈ U`, and `ω` a form of degree `q + 1`, real `C^∞` on `U`, with
`∂̄ω = 0` on `U`. Then there are an open `U′` with `x ∈ U′ ⊆ U` and a form `η` of degree `q`,
real `C^∞` on all of `E`, with `∂̄η = ω` on `U′`. -/
theorem exists_dbar_eq {q : ℕ} {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U)
    (β : E → DolbeaultFibre E (q + 1) ℂ) (hβ : ContDiffOn ℝ ∞ β U)
    (hc : ∀ z ∈ U, dbar β z = 0) :
    ∃ U' ⊆ U, IsOpen U' ∧ x ∈ U' ∧ ∃ η : E → DolbeaultFibre E q ℂ, ContDiff ℝ ∞ η ∧
      ∀ z ∈ U', dbar η z = β z :=
  exists_dbar_eq_of_involvesOnly (Module.finrank ℂ E) hU hx β hβ
    (fun _ _ => involvesOnly_top _ _) hc

end Cohesive
