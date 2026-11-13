import Cohesivemodules.Analysis.KernelEstimate
import Cohesivemodules.Analysis.CauchySolveDeriv
import Cohesivemodules.Forms.FlatGrothendieck
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option linter.style.header false

/-!
# Z5.c: the one-variable gauge equation with parameters

Blueprint item Z5.c (`blueprint/blueprint-ll.md` §4 C, design decision L4; §11 v1.15).
For a finite-dimensional complex Banach algebra `𝔄` (with `‖1‖ = 1`), `a : E → 𝔄` smooth near `x`
and a basis direction `e_k`, `exists_gauge_solution` gives `g : E → 𝔄`, smooth on `E` and
pointwise invertible, with `∂̄_{e_k} g = g·a` near `x`, `g` in any subalgebra containing `a`, and
`g` holomorphic in every basis direction in which `a` is.

Proof (Neumann series, [DK, (2.2.7)–(2.2.8)], [BSW, Thm 5.3]):
* cut off `a` to `b = ψ a` with `ψ` from `exists_cutoff_radius` (C.0), whose support has radius
  `2r` in the coordinate `c_k`;
* `u₀ = 1`, `u_{i+1} = cauchySolve e_k (u_i · b)` (`neumannTerm`, C.3);
* `θ = 6 r sup‖b‖ < 1/2` gives `‖D^m u_i‖ ≤ C_m (i+1)^m θ^i` (Z5.a, Z5.b, Leibniz), so
  `g = Σ u_i` is `C^∞` by `contDiff_tsum` (C.4);
* `∂̄_k g = g b` termwise (C.5), `g ∈ S` (C.6), `‖g − 1‖ < 1` (C.7), holomorphy on the slab (C.8).

## Deviations
* [DK] uses an L^∞ contraction plus elliptic regularity, [BSW] asserts smoothness; here
  smoothness comes from summable bounds on all derivatives (blueprint-ll audit a5).
* In `Forms/` rather than `Analysis/` (blueprint-ll §5 table): it uses the Z4.e cutoff.
-/

noncomputable section

namespace Cohesive

open Complex Set Filter Topology
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Z5.c (C.0).** The coordinate functional `c_k` of `finBasis ℂ E` as a continuous linear map
(`c_k (e_k) = 1`). -/
def coordCLM (k : Fin (Module.finrank ℂ E)) : E →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℂ E).coord k)

/-- Z5.c: `c_k (e_k) = 1`. -/
theorem coordCLM_self (k : Fin (Module.finrank ℂ E)) :
    coordCLM k (Module.finBasis ℂ E k) = 1 := by
  show (Module.finBasis ℂ E).coord k (Module.finBasis ℂ E k) = 1
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]

/-- Z5.c helper: `c_k (e_j) = 0` for `j ≠ k`. -/
private theorem coordCLM_ne (k j : Fin (Module.finrank ℂ E)) (h : j ≠ k) :
    coordCLM k (Module.finBasis ℂ E j) = 0 := by
  show (Module.finBasis ℂ E).coord k (Module.finBasis ℂ E j) = 0
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [h]

/-- **Z5.c (C.0). Cutoff with radius control.** For a neighbourhood `K` of `x` and a basis index
`k`, for all small `r > 0` there is a real `C^∞` function `ψ` with `0 ≤ ψ ≤ 1`, compact support in
`K`, support of width `2r` in the coordinate `c_k`, equal to `1` on an open `W ∋ x`, and an open
slab `S ⊇ W`, stable under `z ↦ z − t • e_k`, on which `ψ` has zero derivative in the directions
`e_j`, `i e_j`, `j ≠ k` (as in Z4.e `exists_cutoff`). -/
theorem exists_cutoff_radius {K : Set E} {x : E} (hK : K ∈ 𝓝 x) (k : Fin (Module.finrank ℂ E)) :
    ∃ r₀ > (0 : ℝ), ∀ r, 0 < r → r < r₀ → ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ K ∧ (∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1) ∧
      (∀ w, ψ w ≠ 0 → ‖coordCLM k w - coordCLM k x‖ ≤ 2 * r) ∧
      ∃ W S : Set E, IsOpen W ∧ x ∈ W ∧ IsOpen S ∧ W ⊆ S ∧ (∀ z ∈ W, ψ z = 1) ∧
        (∀ z ∈ S, ∀ t : ℂ, z - t • Module.finBasis ℂ E k ∈ S) ∧
        (∀ z ∈ S, ∀ j, j ≠ k → fderiv ℝ ψ z (Module.finBasis ℂ E j) = 0 ∧
          fderiv ℝ ψ z (I • Module.finBasis ℂ E j) = 0) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hK
  set e := Module.finBasis ℂ E with he
  let c : E →L[ℂ] ℂ := coordCLM k
  have hc_self : c (e k) = 1 := coordCLM_self k
  have hc_ne : ∀ j, j ≠ k → c (e j) = 0 := fun j hj => coordCLM_ne k j hj
  let P : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - c.smulRight (e k)
  have hP : ∀ z, P z = z - c z • e k := fun z => rfl
  have hPk : P (e k) = 0 := by rw [hP, hc_self]; simp
  have hdec : ∀ z, z = c z • e k + P z := fun z => by rw [hP]; abel
  refine ⟨ρ / (4 * (‖e k‖ + 1)), by positivity, fun r hr0 hrr => ?_⟩
  have hr4 : r * (4 * (‖e k‖ + 1)) < ρ := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (‖e k‖ + 1))).1 hrr
    exact this
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
  have hRρ : 2 * r * (‖e k‖ + 1) < ρ := by nlinarith [norm_nonneg (e k)]
  have hsubU : tsupport ψ ⊆ K := fun z hz =>
    hball (lt_of_le_of_lt (mem_closedBall_iff_norm.1 (hR z (hsupp hz)) |>.trans_eq'
      (by simp [dist_eq_norm])) hRρ)
  refine ⟨ψ, hψ, ?_, hsubU, fun z => ⟨mul_nonneg (χ₁.nonneg) (χ₂.nonneg),
    (mul_le_mul χ₁.le_one χ₂.le_one χ₂.nonneg zero_le_one).trans_eq (one_mul 1)⟩, ?_,
    {z | ‖c (z - x)‖ < r ∧ ‖P (z - x)‖ < r}, {z | ‖P (z - x)‖ < r},
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isCompact_closedBall x (2 * r * (‖e k‖ + 1))).of_isClosed_subset isClosed_closure
      (closure_minimal (fun z hz => hR z (hsupp (subset_closure hz))) Metric.isClosed_closedBall)
  · intro w hw
    have h1 : χ₁ (c (w - x)) ≠ 0 := left_ne_zero_of_mul hw
    have h1' := (χ₁.support_eq ▸ h1 : c (w - x) ∈ Metric.ball (0 : ℂ) (2 * r))
    rw [mem_ball_zero_iff, map_sub] at h1'
    exact h1'.le
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

variable {𝔄 : Type} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- **Z5.c (C.3).** The terms of the Neumann series: `u₀ = 1`,
`u_{i+1} = cauchySolve v (u_i · b)`. -/
def neumannTerm (v : E) (b : E → 𝔄) : ℕ → E → 𝔄
  | 0 => fun _ => 1
  | i + 1 => cauchySolve v (fun y => neumannTerm v b i y * b y)

/-- **Z5.c (C.4).** The Neumann series `g = Σ_i u_i`. -/
def gaugeSeries (v : E) (b : E → 𝔄) (z : E) : 𝔄 := ∑' i, neumannTerm v b i z

/-- **Z5.c (C.3).** Each term is `C^∞` (Z4.c), for `v ≠ 0` and `b` smooth with compact support. -/
theorem contDiff_neumannTerm {v : E} (hv : v ≠ 0) {b : E → 𝔄} (hb : ContDiff ℝ ∞ b)
    (hbc : HasCompactSupport b) (i : ℕ) : ContDiff ℝ ∞ (neumannTerm v b i) := by
  induction i with
  | zero => exact contDiff_const
  | succ i ih => exact contDiff_cauchySolve hv (ih.mul hb) (hbc.mul_left)

/-- Z5.c helper: `u_{i+1} = T (u_i b)` and its derivatives are `T` of those of `u_i b`. -/
private theorem iteratedFDeriv_neumannTerm_succ {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (i m : ℕ) (z : E) :
    iteratedFDeriv ℝ m (neumannTerm v b (i + 1)) z =
      cauchySolve v (iteratedFDeriv ℝ m (fun y => neumannTerm v b i y * b y)) z :=
  iteratedFDeriv_cauchySolve hv ((contDiff_neumannTerm hv hb hbc i).mul hb) hbc.mul_left m z

/-- Z5.c helper: the derivatives of `f · b` vanish outside the support region of `b`. -/
private theorem iteratedFDeriv_mul_eq_zero {b : E → 𝔄} (ℓ : E →L[ℂ] ℂ) {c : ℂ} {ρ : ℝ}
    (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (f : E → 𝔄) (m : ℕ) (w : E)
    (hw : iteratedFDeriv ℝ m (fun y => f y * b y) w ≠ 0) : ‖ℓ w - c‖ ≤ ρ := by
  by_contra hlt
  rw [not_le] at hlt
  have hopen : IsOpen {y : E | ρ < ‖ℓ y - c‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (ℓ.continuous.sub continuous_const))
  have hev : (fun y => f y * b y) =ᶠ[𝓝 w] fun _ => (0 : 𝔄) := by
    filter_upwards [hopen.mem_nhds hlt] with y hy
    have : b y = 0 := by
      by_contra hne
      exact absurd (hsupp y hne) (not_le.2 hy)
    simp [this]
  apply hw
  rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev m).eq_of_nhds]
  simp [iteratedFDeriv_fun_zero]

/-- Z5.c helper: pointwise bounds `β_l` for the derivatives of `b`, with `3ρ β_l ≤ θ γ_l`. -/
private theorem exists_beta_gamma {b : E → 𝔄} (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    {ρ B : ℝ} (hB : ∀ w, ‖b w‖ ≤ B) :
    ∃ β γ : ℕ → ℝ, ∀ l, 0 ≤ β l ∧ 0 ≤ γ l ∧ (∀ w, ‖iteratedFDeriv ℝ l b w‖ ≤ β l) ∧
      3 * ρ * β l ≤ 3 * ρ * B * γ l := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hbd : ∀ l : ℕ, ∃ β : ℝ, 0 ≤ β ∧ ∀ w, ‖iteratedFDeriv ℝ l b w‖ ≤ β := by
    intro l
    have hcont : Continuous (iteratedFDeriv ℝ l b) :=
      hb.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ := (hbc.iteratedFDeriv l).exists_bound_of_continuous hcont
    exact ⟨max C 0, le_max_right _ _, fun w => (hC w).trans (le_max_left _ _)⟩
  choose β hβ0 hβ using hbd
  by_cases hB' : B = 0
  · refine ⟨fun _ => 0, fun _ => 0, fun l => ⟨le_rfl, le_rfl, fun w => ?_, by simp [hB']⟩⟩
    have hb0 : b = 0 := funext fun w => norm_le_zero_iff.1 ((hB w).trans_eq hB')
    simp [hb0, iteratedFDeriv_zero]
  · have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB')
    refine ⟨β, fun l => β l / B, fun l => ⟨hβ0 l, div_nonneg (hβ0 l) hB0, hβ l, ?_⟩⟩
    apply le_of_eq
    field_simp

/-- Z5.c helper: the leading terms of the bound for `D^m u_i` (recursion in `i`). -/
private theorem neumann_key {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (m : ℕ) (C β γ : ℕ → ℝ)
    (hC : ∀ l < m, 0 ≤ C l ∧ ∀ (i : ℕ) (z : E),
      ‖iteratedFDeriv ℝ l (neumannTerm v b i) z‖ ≤ C l * ((i : ℝ) + 1) ^ l * (3 * ρ * B) ^ i)
    (hβγ : ∀ l, 0 ≤ β l ∧ 0 ≤ γ l ∧ (∀ w, ‖iteratedFDeriv ℝ l b w‖ ≤ β l) ∧
      3 * ρ * β l ≤ 3 * ρ * B * γ l) (i : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ m (neumannTerm v b i) z‖ ≤ (3 * ρ * B) ^ i * (1 + (∑ l ∈ Finset.range m,
      (m.choose l : ℝ) * C l * γ (m - l)) * i * ((i : ℝ) + 1) ^ (m - 1)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set θ := 3 * ρ * B with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  set Λ : ℝ := ∑ l ∈ Finset.range m, (m.choose l : ℝ) * C l * γ (m - l) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    refine Finset.sum_nonneg fun l hl => ?_
    have := (hC l (Finset.mem_range.1 hl)).1
    have := (hβγ (m - l)).2.1
    positivity
  induction i generalizing z with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero, mul_one]
    cases m with
    | zero => simp [neumannTerm]
    | succ m => simp [neumannTerm, iteratedFDeriv_const_of_ne]
  | succ i ih =>
    rw [iteratedFDeriv_neumannTerm_succ hv hb hbc]
    have hu : ContDiff ℝ ∞ (neumannTerm v b i) := contDiff_neumannTerm hv hb hbc i
    set N : ℝ := θ ^ i * (1 + Λ * i * ((i : ℝ) + 1) ^ (m - 1)) with hN
    have hN0 : 0 ≤ N := by positivity
    set S : ℝ := ∑ l ∈ Finset.range m,
      (m.choose l : ℝ) * (C l * ((i : ℝ) + 1) ^ l * θ ^ i) * β (m - l) with hS
    have hGb : ∀ w, ‖iteratedFDeriv ℝ m (fun y => neumannTerm v b i y * b y) w‖ ≤ B * N + S := by
      intro w
      refine (norm_iteratedFDeriv_mul_le hu hb w (n := m) (by exact_mod_cast le_top)).trans ?_
      rw [Finset.sum_range_succ, add_comm]
      refine add_le_add ?_ (Finset.sum_le_sum fun l hl => ?_)
      · simp only [Nat.choose_self, Nat.cast_one, one_mul]
        rw [Nat.sub_self, norm_iteratedFDeriv_zero, mul_comm B N]
        exact mul_le_mul (ih w) (hB w) (norm_nonneg _) hN0
      · have hl' := Finset.mem_range.1 hl
        have h1 := (hC l hl').2 i w
        have h2 := (hβγ (m - l)).2.2.1 w
        have h3 := (hβγ (m - l)).1
        have h4 : (0 : ℝ) ≤ m.choose l := Nat.cast_nonneg _
        have h5 := (hC l hl').1
        gcongr
    have hcs := norm_cauchySolve_le ℓ hℓ hρ
      (G := iteratedFDeriv ℝ m (fun y => neumannTerm v b i y * b y)) (c := c)
      (fun w hw => iteratedFDeriv_mul_eq_zero ℓ hsupp _ m w hw) hGb z
    refine hcs.trans ?_
    have hlow : 3 * ρ * S ≤ Λ * ((i : ℝ) + 1) ^ (m - 1) * θ ^ (i + 1) := by
      rw [hS, Finset.mul_sum, hΛ, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun l hl => ?_
      have hl' := Finset.mem_range.1 hl
      obtain ⟨hCl0, -⟩ := hC l hl'
      have h1 : ((i : ℝ) + 1) ^ l ≤ ((i : ℝ) + 1) ^ (m - 1) :=
        pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]) (by omega)
      have h2 := (hβγ (m - l)).2.2.2
      have h3 := (hβγ (m - l)).2.1
      have h4 : (0 : ℝ) ≤ m.choose l := Nat.cast_nonneg _
      calc 3 * ρ * ((m.choose l : ℝ) * (C l * ((i : ℝ) + 1) ^ l * θ ^ i) * β (m - l))
          = (m.choose l : ℝ) * (C l * ((i : ℝ) + 1) ^ l * θ ^ i) * (3 * ρ * β (m - l)) := by ring
        _ ≤ (m.choose l : ℝ) * (C l * ((i : ℝ) + 1) ^ l * θ ^ i) * (θ * γ (m - l)) := by
          gcongr
        _ ≤ (m.choose l : ℝ) * (C l * ((i : ℝ) + 1) ^ (m - 1) * θ ^ i) * (θ * γ (m - l)) := by
          gcongr
        _ = (m.choose l : ℝ) * C l * γ (m - l) * ((i : ℝ) + 1) ^ (m - 1) * θ ^ (i + 1) := by ring
    have e1 : 3 * ρ * (B * N + S) = θ * N + 3 * ρ * S := by rw [hθdef]; ring
    calc 3 * ρ * (B * N + S) = θ * N + 3 * ρ * S := e1
      _ ≤ θ * N + Λ * ((i : ℝ) + 1) ^ (m - 1) * θ ^ (i + 1) := by gcongr
      _ = θ ^ (i + 1) * (1 + Λ * ((i : ℝ) + 1) * ((i : ℝ) + 1) ^ (m - 1)) := by rw [hN]; ring
      _ ≤ θ ^ (i + 1) * (1 + Λ * ((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + 1) ^ (m - 1)) := by
        push_cast
        gcongr
        linarith

/-- **Z5.c (C.3). Bounds.** If `ℓ v = 1`, `b` vanishes outside `{‖ℓ w − c‖ ≤ ρ}` and is bounded by
`B`, and `θ := 3ρB < 1`, then every derivative of `u_i` decays like `(i+1)^m θ^i`. -/
theorem norm_iteratedFDeriv_neumannTerm_le {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (hθ : 3 * ρ * B < 1) :
    ∃ C : ℕ → ℝ, ∀ (m i : ℕ) (z : E),
      ‖iteratedFDeriv ℝ m (neumannTerm v b i) z‖ ≤ C m * ((i : ℝ) + 1) ^ m * (3 * ρ * B) ^ i := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hθ0 : 0 ≤ 3 * ρ * B := by positivity
  obtain ⟨β, γ, hβγ⟩ := exists_beta_gamma hb hbc hB
  have step : ∀ (m : ℕ) (C : ℕ → ℝ), (∀ l < m, 0 ≤ C l ∧ ∀ (i : ℕ) (z : E),
      ‖iteratedFDeriv ℝ l (neumannTerm v b i) z‖ ≤ C l * ((i : ℝ) + 1) ^ l * (3 * ρ * B) ^ i) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ (i : ℕ) (z : E), ‖iteratedFDeriv ℝ m (neumannTerm v b i) z‖ ≤
        c * ((i : ℝ) + 1) ^ m * (3 * ρ * B) ^ i := by
    intro m C hC
    set θ := 3 * ρ * B with hθdef
    set Λ : ℝ := ∑ l ∈ Finset.range m, (m.choose l : ℝ) * C l * γ (m - l) with hΛ
    have hΛ0 : 0 ≤ Λ := by
      refine Finset.sum_nonneg fun l hl => ?_
      have := (hC l (Finset.mem_range.1 hl)).1
      have := (hβγ (m - l)).2.1
      positivity
    refine ⟨1 + Λ, by positivity, fun i z => (neumann_key hv hb hbc ℓ hℓ hρ hsupp hB m C β γ hC
      hβγ i z).trans ?_⟩
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hpow : ∀ n : ℕ, (1 : ℝ) ≤ ((i : ℝ) + 1) ^ n := fun n => one_le_pow₀ (by linarith)
    rw [← hΛ, show (1 + Λ) * ((i : ℝ) + 1) ^ m * θ ^ i = θ ^ i * ((1 + Λ) * ((i : ℝ) + 1) ^ m)
      from by ring]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hθ0 i)
    cases m with
    | zero => simp [hΛ]
    | succ m =>
      simp only [Nat.add_sub_cancel, pow_succ]
      have h1 := hpow m
      have h2 : Λ * i * ((i : ℝ) + 1) ^ m ≤ Λ * ((i : ℝ) + 1) * ((i : ℝ) + 1) ^ m := by
        gcongr
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ (i : ℝ) + 1)]
  have claim : ∀ m : ℕ, ∃ C : ℕ → ℝ, ∀ l ≤ m, 0 ≤ C l ∧ ∀ (i : ℕ) (z : E),
      ‖iteratedFDeriv ℝ l (neumannTerm v b i) z‖ ≤ C l * ((i : ℝ) + 1) ^ l * (3 * ρ * B) ^ i := by
    intro m
    induction m with
    | zero =>
      obtain ⟨c, hc0, hc⟩ := step 0 (fun _ => 0) (fun l hl => absurd hl (Nat.not_lt_zero _))
      exact ⟨fun _ => c, fun l hl => by
        obtain rfl : l = 0 := Nat.le_zero.1 hl
        exact ⟨hc0, hc⟩⟩
    | succ m ih =>
      obtain ⟨C, hC⟩ := ih
      obtain ⟨c, hc0, hc⟩ := step (m + 1) C (fun l hl => hC l (Nat.lt_succ_iff.1 hl))
      refine ⟨fun l => if l = m + 1 then c else C l, fun l hl => ?_⟩
      by_cases hlm : l = m + 1
      · subst hlm
        simpa using ⟨hc0, hc⟩
      · have : l ≤ m := by omega
        simpa [hlm] using hC l this
  choose C hC using claim
  exact ⟨fun m => C m m, fun m i z => (hC m m le_rfl).2 i z⟩

/-- Z5.c helper: the `L^∞` bound `‖u_i‖ ≤ θ^i` (Z5.a). -/
private theorem norm_neumannTerm_le {v : E} {b : E → 𝔄} (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (i : ℕ) (z : E) : ‖neumannTerm v b i z‖ ≤ (3 * ρ * B) ^ i := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  induction i generalizing z with
  | zero => simp [neumannTerm]
  | succ i ih =>
    have h := norm_cauchySolve_le ℓ hℓ hρ (G := fun y => neumannTerm v b i y * b y) (c := c)
      (fun w hw => hsupp w (right_ne_zero_of_mul hw))
      (C := (3 * ρ * B) ^ i * B) (fun w => (norm_mul_le _ _).trans
        (mul_le_mul (ih w) (hB w) (norm_nonneg _) (by positivity))) z
    refine h.trans_eq ?_
    rw [pow_succ]
    ring

/-- Z5.c helper: pointwise summability of the Neumann series for `θ < 1`. -/
private theorem summable_neumannTerm {v : E} {b : E → 𝔄} (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (hθ : 3 * ρ * B < 1) (z : E) : Summable fun i => neumannTerm v b i z := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  exact Summable.of_norm_bounded (summable_geometric_of_lt_one (by positivity) hθ)
    (fun i => norm_neumannTerm_le ℓ hℓ hρ hsupp hB i z)

/-- Z5.c helper: `Σ (i+1)^k θ^i` converges for `0 ≤ θ < 1`. -/
private theorem summable_succ_pow_mul_pow {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (k : ℕ) :
    Summable fun i : ℕ => ((i : ℝ) + 1) ^ k * θ ^ i := by
  rcases h0.eq_or_lt with rfl | hpos
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have : n ≠ 0 := by simpa using hn
    simp [this]
  · have h := (summable_nat_add_iff 1).2
      (summable_pow_mul_geometric_of_norm_lt_one k (r := θ) (by rwa [Real.norm_of_nonneg h0]))
    refine (h.div_const θ).congr fun n => ?_
    push_cast
    field_simp
    ring

/-- **Z5.c (C.4).** Under the hypotheses of the bounds, the Neumann series is `C^∞` on `E`. -/
theorem contDiff_gaugeSeries {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (hθ : 3 * ρ * B < 1) : ContDiff ℝ ∞ (gaugeSeries v b) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨C, hC⟩ := norm_iteratedFDeriv_neumannTerm_le hv hb hbc ℓ hℓ hρ hsupp hB hθ
  have hθ0 : 0 ≤ 3 * ρ * B := by positivity
  exact contDiff_tsum (N := ⊤) (v := fun k (i : ℕ) => C k * (((i : ℝ) + 1) ^ k * (3 * ρ * B) ^ i))
    (fun i => contDiff_neumannTerm hv hb hbc i)
    (fun k _ => (summable_succ_pow_mul_pow hθ0 hθ k).mul_left (C k))
    (fun k i x _ => by rw [← mul_assoc]; exact hC k i x)

/-- Z5.c helper: `∂̄_w` commutes with the Neumann series (termwise differentiation). -/
private theorem pdbar_gaugeSeries_tsum {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (hθ : 3 * ρ * B < 1) (w z : E) :
    pdbar w (gaugeSeries v b) z = ∑' i, pdbar w (neumannTerm v b i) z := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  obtain ⟨C, hC⟩ := norm_iteratedFDeriv_neumannTerm_le hv hb hbc ℓ hℓ hρ hsupp hB hθ
  have hθ0 : 0 ≤ 3 * ρ * B := by positivity
  have hsum : Summable fun i : ℕ => C 1 * (((i : ℝ) + 1) ^ 1 * (3 * ρ * B) ^ i) :=
    (summable_succ_pow_mul_pow hθ0 hθ 1).mul_left (C 1)
  have hbound : ∀ (i : ℕ) (x : E), ‖fderiv ℝ (neumannTerm v b i) x‖ ≤
      C 1 * (((i : ℝ) + 1) ^ 1 * (3 * ρ * B) ^ i) := by
    intro i x
    rw [← norm_iteratedFDeriv_one, ← mul_assoc]
    exact hC 1 i x
  have hdiff : ∀ i, Differentiable ℝ (neumannTerm v b i) := fun i =>
    (contDiff_neumannTerm hv hb hbc i).differentiable (by simp)
  have hsumF : Summable fun i => fderiv ℝ (neumannTerm v b i) z :=
    Summable.of_norm_bounded hsum fun i => hbound i z
  have hd : fderiv ℝ (gaugeSeries v b) z = ∑' i, fderiv ℝ (neumannTerm v b i) z :=
    fderiv_tsum_apply hsum hdiff hbound (summable_neumannTerm ℓ hℓ hρ hsupp hB hθ z) z
  let Φ : (E →L[ℝ] 𝔄) →L[ℂ] 𝔄 :=
    { toFun := fun A => (2 : ℂ)⁻¹ • (A w + Complex.I • A (Complex.I • w))
      map_add' := fun A B => by
        simp only [add_apply, smul_add]
        abel
      map_smul' := fun c A => by
        simp only [smul_apply, RingHom.id_apply, smul_add,
          smul_comm Complex.I c, smul_comm (2 : ℂ)⁻¹ c]
      cont := by fun_prop }
  have e : ∀ f : E → 𝔄, pdbar w f z = Φ (fderiv ℝ f z) := fun f => rfl
  rw [e, hd, Φ.map_tsum hsumF]
  simp only [e]

/-- **Z5.c (C.5).** `∂̄_v g = g · b` everywhere. -/
theorem pdbar_gaugeSeries {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (hθ : 3 * ρ * B < 1) (z : E) :
    pdbar v (gaugeSeries v b) z = gaugeSeries v b z * b z := by
  rw [pdbar_gaugeSeries_tsum hv hb hbc ℓ hℓ hρ hsupp hB hθ v z]
  have hsucc : ∀ i, pdbar v (neumannTerm v b (i + 1)) z = neumannTerm v b i z * b z :=
    fun i => pdbar_cauchySolve hv
      (((contDiff_neumannTerm hv hb hbc i).mul hb).of_le (by exact_mod_cast le_top))
      hbc.mul_left z
  have h0 : pdbar v (neumannTerm v b 0) z = 0 := by
    simp [pdbar, neumannTerm]
  have hs : Summable fun i => neumannTerm v b i z * b z :=
    (summable_neumannTerm ℓ hℓ hρ hsupp hB hθ z).mul_right (b z)
  rw [tsum_eq_zero_add' (by simpa only [hsucc] using hs)]
  simp only [hsucc, h0, zero_add]
  exact (summable_neumannTerm ℓ hℓ hρ hsupp hB hθ z).tsum_mul_right (b z)

/-- **Z5.c (C.6).** If `b` takes values in a subalgebra `S` (closed: finite dimension), so does
`g`. -/
theorem gaugeSeries_mem [FiniteDimensional ℂ 𝔄] {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (hθ : 3 * ρ * B < 1) (S : Subalgebra ℂ 𝔄) (hbS : ∀ w, b w ∈ S) (z : E) :
    gaugeSeries v b z ∈ S := by
  have hclosed : IsClosed (S.toSubmodule : Set 𝔄) := Submodule.closed_of_finiteDimensional _
  obtain ⟨f, hf⟩ := Submodule.ClosedComplemented.of_finiteDimensional_quotient hclosed
  let Q : 𝔄 →L[ℂ] 𝔄 := ContinuousLinearMap.id ℂ 𝔄 - S.toSubmodule.subtypeL ∘L f
  have hQ : ∀ a, Q a = 0 ↔ a ∈ S := by
    intro a
    constructor
    · intro h
      have : a = f a := sub_eq_zero.1 h
      rw [this]
      exact (f a).2
    · intro h
      have := hf ⟨a, h⟩
      show a - (f a : 𝔄) = 0
      rw [this]
      simp
  have hu : ∀ i z, Q (neumannTerm v b i z) = 0 := by
    intro i
    induction i with
    | zero =>
      intro z
      exact (hQ _).2 S.one_mem
    | succ i ih =>
      intro z
      have hF := (contDiff_neumannTerm hv hb hbc i).mul hb
      have h1 := map_cauchySolve Q hv (F := fun y => neumannTerm v b i y * b y) hF.continuous
        hbc.mul_left z
      have h2 : (fun y => Q (neumannTerm v b i y * b y)) = fun _ => 0 := by
        funext y
        exact (hQ _).2 (S.mul_mem ((hQ _).1 (ih y)) (hbS y))
      show Q (cauchySolve v (fun y => neumannTerm v b i y * b y) z) = 0
      rw [h1, h2]
      simp [cauchySolve]
  have hsum := summable_neumannTerm ℓ hℓ hρ hsupp hB hθ z
  refine (hQ _).1 ?_
  show Q (∑' i, neumannTerm v b i z) = 0
  rw [Q.map_tsum hsum]
  simp [hu]

/-- **Z5.c (C.7).** `‖g(z) − 1‖ ≤ θ / (1 − θ)`, so `g(z)` is invertible when `θ < 1/2`. -/
theorem isUnit_gaugeSeries {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (hθ : 3 * ρ * B < 1 / 2) (z : E) : IsUnit (gaugeSeries v b z) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hθ0 : 0 ≤ 3 * ρ * B := by positivity
  have hθ1 : 3 * ρ * B < 1 := by linarith
  have hsum := summable_neumannTerm ℓ hℓ hρ hsupp hB hθ1 z
  have hg : gaugeSeries v b z - 1 = ∑' i, neumannTerm v b (i + 1) z := by
    show ∑' i, neumannTerm v b i z - 1 = _
    rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hsum)]
    simp [neumannTerm]
  have hgeo : HasSum (fun i : ℕ => (3 * ρ * B) * (3 * ρ * B) ^ i)
      ((3 * ρ * B) * (1 - 3 * ρ * B)⁻¹) :=
    (hasSum_geometric_of_lt_one hθ0 hθ1).mul_left _
  have hnorm : ‖gaugeSeries v b z - 1‖ ≤ (3 * ρ * B) * (1 - 3 * ρ * B)⁻¹ := by
    rw [hg]
    refine tsum_of_norm_bounded hgeo fun i => ?_
    rw [← pow_succ']
    exact norm_neumannTerm_le ℓ hℓ hρ hsupp hB (i + 1) z
  have hlt : (3 * ρ * B) * (1 - 3 * ρ * B)⁻¹ < 1 := by
    have : 0 < 1 - 3 * ρ * B := by linarith
    rw [← div_eq_mul_inv, div_lt_one this]
    linarith
  have h1 : ‖1 - gaugeSeries v b z‖ < 1 := by
    rw [norm_sub_rev]
    exact lt_of_le_of_lt hnorm hlt
  have := (Units.oneSub (1 - gaugeSeries v b z) h1).isUnit
  simpa [Units.oneSub] using this

/-- Z5.c helper: the Leibniz rule for `pdbar` on a normed algebra. -/
private theorem pdbar_mul (w : E) {f g : E → 𝔄} {z : E} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    pdbar w (fun y => f y * g y) z = pdbar w f z * g z + f z * pdbar w g z := by
  unfold pdbar
  rw [show (fun y => f y * g y) = f * g from rfl, fderiv_mul' hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul, op_smul_eq_mul, smul_add,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  abel

/-- **Z5.c (C.8).** If `S` is stable under `z ↦ z − t • v` and `∂̄_w b = 0` on `S`, then
`∂̄_w g = 0` on `S`. -/
theorem pdbar_gaugeSeries_eq_zero {v : E} (hv : v ≠ 0) {b : E → 𝔄}
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (ℓ : E →L[ℂ] ℂ) (hℓ : ℓ v = 1) {c : ℂ}
    {ρ B : ℝ} (hρ : 0 ≤ ρ) (hsupp : ∀ w, b w ≠ 0 → ‖ℓ w - c‖ ≤ ρ) (hB : ∀ w, ‖b w‖ ≤ B)
    (hθ : 3 * ρ * B < 1) (w : E) {S : Set E} (hS : ∀ z ∈ S, ∀ t : ℂ, z - t • v ∈ S)
    (hbS : ∀ z ∈ S, pdbar w b z = 0) : ∀ z ∈ S, pdbar w (gaugeSeries v b) z = 0 := by
  have hdb : Differentiable ℝ b := hb.differentiable (by simp)
  have hterm : ∀ i, ∀ z ∈ S, pdbar w (neumannTerm v b i) z = 0 := by
    intro i
    induction i with
    | zero =>
      intro z _
      simp [pdbar, neumannTerm]
    | succ i ih =>
      intro z hz
      have hu := contDiff_neumannTerm hv hb hbc i
      have hF := hu.mul hb
      have h1 : pdbar w (cauchySolve v (fun y => neumannTerm v b i y * b y)) z =
          cauchySolve v (pdbar w (fun y => neumannTerm v b i y * b y)) z :=
        pdbar_cauchySolve_comm hv (hF.of_le (by exact_mod_cast le_top)) hbc.mul_left w z
      show pdbar w (cauchySolve v (fun y => neumannTerm v b i y * b y)) z = 0
      rw [h1]
      refine cauchySolve_eq_zero hS (fun y hy => ?_) hz
      rw [pdbar_mul w ((hu.differentiable (by simp)) y) (hdb y), ih y hy, hbS y hy]
      simp
  intro z hz
  rw [pdbar_gaugeSeries_tsum hv hb hbc ℓ hℓ hρ hsupp hB hθ w z]
  simp [hterm _ z hz]

/-- Z5.c helper: `∂̄_w (ψ α) = ψ ∂̄_w α` where `ψ` has zero derivative in the directions `w`,
`i w`. -/
private theorem pdbar_cutoff_smul {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) {α : E → 𝔄} {y : E}
    (hα : DifferentiableAt ℝ α y) (w : E) (h1 : fderiv ℝ ψ y w = 0)
    (h2 : fderiv ℝ ψ y (Complex.I • w) = 0) :
    pdbar w (fun z => (ψ z : ℂ) • α z) y = (ψ y : ℂ) • pdbar w α y := by
  unfold pdbar
  rw [fderiv_cutoff_smul hψ hα w, fderiv_cutoff_smul hψ hα (Complex.I • w), h1, h2]
  simp only [Complex.ofReal_zero, zero_smul, zero_add, smul_add]
  module

/-- **Z5.c (main).** [DK, §2.2.2], [BSW, Thm 5.3], [DP, Prop 16]. One-variable gauge equation with
parameters: for `a` smooth on an open `U ∋ x` with values in a subalgebra `S`, holomorphic in the
basis directions `j ∈ J ∌ k`, there are an open `W ∋ x` in `U` and `g : E → 𝔄`, `C^∞`, pointwise
invertible, with values in `S`, such that `∂̄_{e_k} g = g · a` and `∂̄_{e_j} g = 0` (`j ∈ J`) on
`W`. -/
theorem exists_gauge_solution [FiniteDimensional ℂ 𝔄] (k : Fin (Module.finrank ℂ E))
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (a : E → 𝔄) (ha : ContDiffOn ℝ ∞ a U)
    (S : Subalgebra ℂ 𝔄) (haS : ∀ z ∈ U, a z ∈ S) (J : Finset (Fin (Module.finrank ℂ E)))
    (hkJ : k ∉ J) (haJ : ∀ j ∈ J, ∀ z ∈ U, pdbar (Module.finBasis ℂ E j) a z = 0) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ g : E → 𝔄, ContDiff ℝ ∞ g ∧
      (∀ z, g z ∈ S) ∧ (∀ z, IsUnit (g z)) ∧
      (∀ z ∈ W, pdbar (Module.finBasis ℂ E k) g z = g z * a z) ∧
      (∀ j ∈ J, ∀ z ∈ W, pdbar (Module.finBasis ℂ E j) g z = 0) := by
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.1 hU x hx
  set K : Set E := Metric.closedBall x (ρ₀ / 2) with hKdef
  have hKU : K ⊆ U := fun z hz => hball (lt_of_le_of_lt (mem_closedBall_iff_norm.1 hz |>.trans_eq'
    (by simp [dist_eq_norm])) (by linarith))
  have hKc : IsCompact K := isCompact_closedBall x (ρ₀ / 2)
  have hKn : K ∈ 𝓝 x := Metric.closedBall_mem_nhds x (by linarith)
  obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn (ha.continuousOn.mono hKU)
  set B : ℝ := max C₀ 0 + 1 with hBdef
  have hBpos : 0 < B := by positivity
  have hCB : C₀ ≤ B := by rw [hBdef]; linarith [le_max_left C₀ 0]
  obtain ⟨r₀, hr₀, hr⟩ := exists_cutoff_radius hKn k
  set r : ℝ := min (r₀ / 2) (1 / (24 * B)) with hrdef
  have hr0 : 0 < r := lt_min (by linarith) (by positivity)
  have hrr : r < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨ψ, hψ, hψc, hψK, hψ01, hψs, W, T, hW, hxW, hT, hWT, hψ1, hTs, hTd⟩ := hr r hr0 hrr
  have hψU : tsupport ψ ⊆ U := hψK.trans hKU
  set b : E → 𝔄 := fun z => (ψ z : ℂ) • a z with hbdef
  obtain ⟨hb, hbc⟩ := contDiff_cutoff_smul hU hψ hψc hψU ha
  set e := Module.finBasis ℂ E with he
  have hv : e k ≠ 0 := e.ne_zero k
  have hℓ : coordCLM k (e k) = 1 := coordCLM_self k
  have hbz : ∀ z, ψ z = 0 → b z = 0 := fun z hz => by simp [hbdef, hz]
  have hsupp : ∀ w, b w ≠ 0 → ‖coordCLM k w - coordCLM k x‖ ≤ 2 * r := fun w hw =>
    hψs w (fun h => hw (hbz w h))
  have hmem : ∀ z, ψ z ≠ 0 → z ∈ K := fun z hz => hψK (subset_tsupport _ hz)
  have hB : ∀ z, ‖b z‖ ≤ B := by
    intro z
    by_cases hz : ψ z = 0
    · rw [hbz z hz, norm_zero]; exact hBpos.le
    · have h1 : ‖(ψ z : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (hψ01 z).1]; exact (hψ01 z).2
      calc ‖b z‖ = ‖(ψ z : ℂ)‖ * ‖a z‖ := norm_smul _ _
        _ ≤ 1 * B := mul_le_mul h1 ((hC₀ z (hmem z hz)).trans hCB) (norm_nonneg _) zero_le_one
        _ = B := one_mul B
  have hθ : 3 * (2 * r) * B < 1 / 2 := by
    have h1 : r ≤ 1 / (24 * B) := min_le_right _ _
    have h2 : r * (24 * B) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hθ' : 3 * (2 * r) * B < 1 := by linarith
  have hρ : 0 ≤ 2 * r := by linarith
  refine ⟨W, hW, hxW, fun z hz => hψU (subset_tsupport _ (by
      show ψ z ≠ 0
      rw [hψ1 z hz]
      exact one_ne_zero)),
    gaugeSeries (e k) b, contDiff_gaugeSeries hv hb hbc _ hℓ hρ hsupp hB hθ', ?_, ?_, ?_, ?_⟩
  · refine fun z => gaugeSeries_mem hv hb hbc _ hℓ hρ hsupp hB hθ' S (fun w => ?_) z
    by_cases hw : ψ w = 0
    · simp [hw]
    · exact S.smul_mem (haS w (hKU (hmem w hw))) _
  · exact fun z => isUnit_gaugeSeries hv hb hbc _ hℓ hρ hsupp hB hθ z
  · intro z hz
    rw [pdbar_gaugeSeries hv hb hbc _ hℓ hρ hsupp hB hθ' z]
    have : (ψ z : ℂ) • a z = a z := by simp [hψ1 z hz]
    rw [this]
  · intro j hj z hz
    have hjk : j ≠ k := fun h => hkJ (h ▸ hj)
    refine pdbar_gaugeSeries_eq_zero hv hb hbc _ hℓ hρ hsupp hB hθ' (e j) hTs ?_ z (hWT hz)
    intro y hy
    by_cases hyK : y ∈ tsupport ψ
    · have hyU : y ∈ U := hψU hyK
      have hdiff : DifferentiableAt ℝ a y :=
        (ha.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
      rw [pdbar_cutoff_smul hψ hdiff (e j) (hTd y hy j hjk).1 (hTd y hy j hjk).2,
        haJ j hj y hyU, smul_zero]
    · have := fderiv_cutoff_smul_of_notMem hyK a
      unfold pdbar
      rw [this]
      simp

end Cohesive
