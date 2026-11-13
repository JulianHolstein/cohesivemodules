import Cohesivemodules.Forms.Superconnection
import Cohesivemodules.Forms.GaugeSolve

set_option linter.style.header false

/-!
# Z5.f: removing `dz̄₁, …, dz̄ₙ` one variable at a time

Blueprint item Z5.f (`blueprint/blueprint-ll.md` §4 D; §11 v1.15). A flat ∂̄-superconnection
`∂̄ + 𝒜` on an open `U ⊆ E` (`𝒜` smooth, odd, of total degree `1`, `mcOp 𝒜 = 0`) is, near each
`x ∈ U`, gauge equivalent by a smooth invertible degree-0 Λ-linear `g` to `∂̄ + 𝒜′` with every
`dz̄ᵢ`-coefficient of `𝒜′` zero and `𝒜′` holomorphic (`exists_gauge_holomorphic`).

Proof: downward induction on `k` (`exists_gauge_of_aCoef`). In step `k`, the coefficient `a_k`
lies in `gaugeSubalg deg k` (B.6) and is holomorphic in `z_{<k}` (B.4); the one-variable solver
(Z5.c) gives `g` with `∂̄_k g = g a_k`, holomorphic in `z_{<k}`; then `g·𝒜` has `aᵢ = 0` for
`i ≤ k` (B.5) and is again flat (B.3).

## Deviations
* [B] and [DK] count variables from 1; here `Fin (finrank ℂ E)` from 0, and "involves only
  `dz̄_0 … dz̄_{k−1}`" is phrased as "`aᵢ = 0` for `i < k`" (the complement).
-/

noncomputable section

namespace Cohesive

open Complex Set Filter Topology
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {r : ℕ}

/-- **Z5.f.** The gauge algebra of step `k`: operators of total degree `0` commuting with every
`εⱼ` and with `ιᵢ` for `i ≤ k`. -/
def gaugeSubalg (deg : Fin r → ℤ) (k : ℕ) : Subalgebra ℂ (FibOp E r) where
  carrier := {T | IsOfTotDeg deg 0 T ∧ (∀ j, epsOp j * T = T * epsOp j) ∧
    ∀ i : Fin (Module.finrank ℂ E), (i : ℕ) ≤ k → iotaOp i * T = T * iotaOp i}
  mul_mem' := by
    rintro a b ⟨ha0, hae, hai⟩ ⟨hb0, hbe, hbi⟩
    refine ⟨?_, fun j => ?_, fun i hi => ?_⟩
    · simpa only [add_zero] using ha0.mul hb0
    · rw [← mul_assoc, hae j, mul_assoc, hbe j, ← mul_assoc]
    · rw [← mul_assoc, hai i hi, mul_assoc, hbi i hi, ← mul_assoc]
  add_mem' := by
    rintro a b ⟨ha0, hae, hai⟩ ⟨hb0, hbe, hbi⟩
    refine ⟨fun m s hs => ?_, fun j => ?_, fun i hi => ?_⟩
    · rw [add_apply]
      exact add_mem (ha0 m s hs) (hb0 m s hs)
    · rw [mul_add, add_mul, hae j, hbe j]
    · rw [mul_add, add_mul, hai i hi, hbi i hi]
  algebraMap_mem' := by
    intro c
    refine ⟨fun m s hs => ?_, fun j => ?_, fun i _ => ?_⟩
    · rw [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]
      exact Submodule.smul_mem _ c (by simpa only [add_zero] using hs)
    · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

/-- **Z5.f (B.0).** The hypotheses on `𝒜` kept along the induction, on an open set `U`: smooth,
total degree `1`, odd, flat. -/
structure IsFlatSuperconn (deg : Fin r → ℤ) (U : Set E) (𝒜 : E → FibOp E r) : Prop where
  smooth : ContDiffOn ℝ ∞ 𝒜 U
  deg_one : ∀ z ∈ U, IsOfTotDeg deg 1 (𝒜 z)
  odd : ∀ z ∈ U, ∀ j, epsOp j * 𝒜 z = -(𝒜 z * epsOp j)
  flat : ∀ z ∈ U, mcOp 𝒜 z = 0

/-- **Z5.f.** The gauges: smooth, pointwise invertible, of total degree `0`, Λ-linear. -/
structure IsGauge (deg : Fin r → ℤ) (g : E → FibOp E r) : Prop where
  smooth : ContDiff ℝ ∞ g
  unit : ∀ z, IsUnit (g z)
  deg_zero : ∀ z, IsOfTotDeg deg 0 (g z)
  comm : ∀ z j, epsOp j * g z = g z * epsOp j

/-- Helper: a submodule of a finite-dimensional space is the kernel of a continuous linear map. -/
private theorem exists_clm_ker {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [FiniteDimensional ℂ A] (V : Submodule ℂ A) :
    ∃ Q : A →L[ℂ] A, ∀ a, Q a = 0 ↔ a ∈ V := by
  have hclosed : IsClosed (V : Set A) := Submodule.closed_of_finiteDimensional _
  obtain ⟨f, hf⟩ := Submodule.ClosedComplemented.of_finiteDimensional_quotient hclosed
  refine ⟨ContinuousLinearMap.id ℂ A - V.subtypeL ∘L f, fun a => ?_⟩
  constructor
  · intro h
    have : a = f a := sub_eq_zero.1 h
    rw [this]
    exact (f a).2
  · intro h
    have := hf ⟨a, h⟩
    show a - (f a : A) = 0
    rw [this]
    simp

omit [FiniteDimensional ℂ E] in
/-- Helper: `pdbar` of a function with values in a submodule stays in the submodule. -/
private theorem pdbar_mem {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [FiniteDimensional ℂ A] (V : Submodule ℂ A) (v : E) {f : E → A} {z : E}
    (hf : ∀ w, f w ∈ V) (hd : DifferentiableAt ℝ f z) : pdbar v f z ∈ V := by
  obtain ⟨Q, hQ⟩ := exists_clm_ker V
  have h1 := pdbar_comp_clm Q v hd
  have h2 : (fun y => Q (f y)) = fun _ => 0 := funext fun y => (hQ _).2 (hf y)
  rw [h2] at h1
  refine (hQ _).1 ?_
  rw [← h1]
  unfold pdbar
  simp

/-- Helper: the submodule of operators of total degree `d`. -/
private def degSub (deg : Fin r → ℤ) (d : ℤ) : Submodule ℂ (FibOp E r) where
  carrier := {T | IsOfTotDeg deg d T}
  add_mem' := fun {a b} ha hb m s hs => by
    rw [add_apply]
    exact add_mem (ha m s hs) (hb m s hs)
  zero_mem' := fun m s _ => by
    rw [zero_apply]
    exact zero_mem _
  smul_mem' := fun c {a} ha m s hs => by
    rw [smul_apply]
    exact Submodule.smul_mem _ c (ha m s hs)

/-- Helper: `degSub` membership unfolded. -/
private theorem mem_degSub {deg : Fin r → ℤ} {d : ℤ} {T : FibOp E r} :
    T ∈ degSub (E := E) deg d ↔ IsOfTotDeg deg d T := Iff.rfl

/-- Helper: the identity has total degree `0`. -/
private theorem isOfTotDeg_one (deg : Fin r → ℤ) : IsOfTotDeg deg 0 (1 : FibOp E r) := by
  intro m s hs
  rw [one_apply_eq_self, add_zero]
  exact hs

/-- Helper: `IsOfTotDeg.mul` with the degree written as a hypothesis. -/
private theorem IsOfTotDeg.mul' {deg : Fin r → ℤ} {d d' d'' : ℤ} {T T' : FibOp E r}
    (hT : IsOfTotDeg deg d T) (hT' : IsOfTotDeg deg d' T') (h : d'' = d' + d) :
    IsOfTotDeg deg d'' (T * T') := h ▸ hT.mul hT'

/-- Helper: the inverse of a unit of total degree `0` has total degree `0` (finite dimension). -/
private theorem isOfTotDeg_inverse {deg : Fin r → ℤ} {T : FibOp E r} (hu : IsUnit T)
    (hT : IsOfTotDeg deg 0 T) : IsOfTotDeg deg 0 (Ring.inverse T) := by
  let L : degSub (E := E) deg 0 →ₗ[ℂ] degSub (E := E) deg 0 :=
    (LinearMap.mulLeft ℂ T).restrict (fun x hx => IsOfTotDeg.mul' hT hx (by norm_num))
  have hinj : Function.Injective L := by
    intro b b' hb
    have hb' : T * (b : FibOp E r) = T * (b' : FibOp E r) := congrArg Subtype.val hb
    have := congrArg (fun x => Ring.inverse T * x) hb'
    simp only [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul] at this
    exact Subtype.ext this
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective (K := ℂ) (V := degSub (E := E) deg 0) (f := L)).1 hinj
  obtain ⟨b, hb⟩ := hsurj ⟨1, isOfTotDeg_one deg⟩
  have hb' : T * (b : FibOp E r) = 1 := congrArg Subtype.val hb
  have h2 : Ring.inverse T = (b : FibOp E r) := by
    have := congrArg (fun x => Ring.inverse T * x) hb'
    simpa only [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul, mul_one] using this.symm
  rw [h2]
  exact b.2

omit [FiniteDimensional ℂ E] in
/-- Helper: `pdbar` of a `C^∞` function is `C^∞`. -/
private theorem contDiff_pdbar_infty {Λ : Type} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] (v : E)
    {f : E → Λ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun w => pdbar v f w) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w v) := h1.clm_apply contDiff_const
  have h3 : ContDiff ℝ ∞ (fun w => fderiv ℝ f w (Complex.I • v)) := h1.clm_apply contDiff_const
  unfold pdbar
  exact (h2.add (h3.const_smul Complex.I)).const_smul _

/-- Helper: `Ring.inverse ∘ g` is `C^∞` when `g` is and all `g w` are units. -/
private theorem contDiff_ringInverse_infty {g : E → FibOp E r} (hg : ContDiff ℝ ∞ g)
    (hu : ∀ w, IsUnit (g w)) : ContDiff ℝ ∞ (fun w => Ring.inverse (g w)) := by
  refine contDiff_iff_contDiffAt.2 fun w => ?_
  obtain ⟨u, hu'⟩ := hu w
  have h := contDiffAt_ringInverse ℝ (n := ∞) u
  rw [hu'] at h
  exact h.comp w hg.contDiffAt

/-- Helper: the gauge action of a `C^∞` gauge on a `C^∞` coefficient is `C^∞`. -/
private theorem contDiffOn_gaugeOp {U : Set E} {g 𝒜 : E → FibOp E r} (hg : ContDiff ℝ ∞ g)
    (hu : ∀ w, IsUnit (g w)) (h𝒜 : ContDiffOn ℝ ∞ 𝒜 U) : ContDiffOn ℝ ∞ (gaugeOp g 𝒜) U := by
  have hGi := (contDiff_ringInverse_infty hg hu).contDiffOn (s := U)
  have hD : ∀ j, ContDiffOn ℝ ∞ (fun w => pdbar (Module.finBasis ℂ E j) g w) U :=
    fun j => (contDiff_pdbar_infty _ hg).contDiffOn
  have h1 := (hg.contDiffOn.mul h𝒜).mul hGi
  have h2 := (ContDiffOn.sum fun j (_ : j ∈ Finset.univ) =>
    (contDiffOn_const (c := (epsOp j : FibOp E r))).mul (hD j)).mul hGi
  exact h1.sub h2

/-- Helper: total degree of `gaugeOp g 𝒜 z` for a degree-`0` unit `g z` and degree-`1` `𝒜 z`. -/
private theorem isOfTotDeg_gaugeOp {deg : Fin r → ℤ} {g 𝒜 : E → FibOp E r} {z : E}
    (hg : ∀ w, IsOfTotDeg deg 0 (g w)) (hu : IsUnit (g z)) (hd : DifferentiableAt ℝ g z)
    (h𝒜 : IsOfTotDeg deg 1 (𝒜 z)) : IsOfTotDeg deg 1 (gaugeOp g 𝒜 z) := by
  have hi := isOfTotDeg_inverse hu (hg z)
  have h0 : IsOfTotDeg deg 1 (g z * 𝒜 z) := IsOfTotDeg.mul' (hg z) h𝒜 (by norm_num)
  have h1 : IsOfTotDeg deg 1 (g z * 𝒜 z * Ring.inverse (g z)) :=
    IsOfTotDeg.mul' h0 hi (by norm_num)
  have hp : ∀ j, IsOfTotDeg deg 0 (pdbar (Module.finBasis ℂ E j) g z) := fun j =>
    pdbar_mem (degSub (E := E) deg 0) _ (fun w => hg w) hd
  have h2 : IsOfTotDeg deg 1 ((∑ j, epsOp j * pdbar (Module.finBasis ℂ E j) g z) *
      Ring.inverse (g z)) := by
    refine IsOfTotDeg.mul' (d := 1) ?_ hi (by norm_num)
    exact (degSub (E := E) deg 1).sum_mem fun j _ =>
      IsOfTotDeg.mul' (isOfTotDeg_epsOp deg j) (hp j) (by norm_num)
  exact (degSub (E := E) deg 1).sub_mem h1 h2

/-- **Z5.f (B.3).** A gauge transforms a flat superconnection on `U` into a flat superconnection
on `U`. -/
theorem IsFlatSuperconn.gauge {deg : Fin r → ℤ} {U : Set E} (hU : IsOpen U) {𝒜 g : E → FibOp E r}
    (h𝒜 : IsFlatSuperconn deg U 𝒜) (hg : IsGauge deg g) :
    IsFlatSuperconn deg U (gaugeOp g 𝒜) := by
  have hd : ∀ z, DifferentiableAt ℝ g z := fun z => (hg.smooth.differentiable (by simp)) z
  refine ⟨contDiffOn_gaugeOp hg.smooth hg.unit h𝒜.smooth, fun z hz => ?_, fun z hz => ?_,
    fun z hz => ?_⟩
  · exact isOfTotDeg_gaugeOp hg.deg_zero (hg.unit z) (hd z) (h𝒜.deg_one z hz)
  · exact gaugeOp_odd (hg.unit z) hg.comm (h𝒜.odd z hz)
  · rw [mcOp_gaugeOp hU hg.smooth.contDiffOn h𝒜.smooth hg.unit hg.comm h𝒜.odd z hz,
      h𝒜.flat z hz, mul_zero, zero_mul]

/-- **Z5.f (B.3).** Gauges compose. -/
theorem IsGauge.mul {deg : Fin r → ℤ} {g h : E → FibOp E r} (hg : IsGauge deg g)
    (hh : IsGauge deg h) : IsGauge deg (fun z => h z * g z) where
  smooth := hh.smooth.mul hg.smooth
  unit z := (hh.unit z).mul (hg.unit z)
  deg_zero z := by simpa only [add_zero] using (hh.deg_zero z).mul (hg.deg_zero z)
  comm z j := by rw [← mul_assoc, hh.comm z j, mul_assoc, hg.comm z j, ← mul_assoc]

/-- Helper: `Fib E r` is nontrivial for `r > 0`. -/
private theorem nontrivial_fib (hr : 0 < r) : Nontrivial (Fib E r) := by
  have h : Nontrivial (ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) := inferInstance
  have : Nontrivial (TotFibre E) := (TotFibre.extEquivTotFibre E).symm.toEquiv.nontrivial
  exact Pi.nontrivial_at ⟨0, hr⟩

/-- Helper: `FibOp E 0` has only one element. -/
private theorem subsingleton_fibOp : Subsingleton (FibOp E 0) :=
  ⟨fun _ _ => ContinuousLinearMap.ext fun _ => funext fun i => Fin.elim0 i⟩

/-- Helper: the constant gauge `1`. -/
private theorem isGauge_one (deg : Fin r → ℤ) : IsGauge deg (fun _ : E => (1 : FibOp E r)) where
  smooth := contDiff_const
  unit _ := isUnit_one
  deg_zero _ := isOfTotDeg_one deg
  comm _ j := by rw [mul_one, one_mul]

/-- Helper: `∂ⱼ aᵢ = ιᵢ ∂ⱼ𝒜 + ∂ⱼ𝒜 ιᵢ`. -/
private theorem pdbar_aCoef_eq (i : Fin (Module.finrank ℂ E)) (v : E) {𝒜 : E → FibOp E r} {z : E}
    (h𝒜 : DifferentiableAt ℝ 𝒜 z) :
    pdbar v (aCoef i 𝒜) z = iotaOp i * pdbar v 𝒜 z + pdbar v 𝒜 z * iotaOp i := by
  let Ψ : FibOp E r →L[ℂ] FibOp E r :=
    ContinuousLinearMap.mul ℂ (FibOp E r) (iotaOp i) +
      (ContinuousLinearMap.mul ℂ (FibOp E r)).flip (iotaOp i)
  have h := pdbar_comp_clm Ψ v h𝒜
  exact h

/-- Helper: `aᵢ(𝒜)` is smooth on `U` if `𝒜` is. -/
private theorem contDiffOn_aCoef (i : Fin (Module.finrank ℂ E)) {U : Set E} {𝒜 : E → FibOp E r}
    (h𝒜 : ContDiffOn ℝ ∞ 𝒜 U) : ContDiffOn ℝ ∞ (aCoef i 𝒜) U :=
  ((contDiffOn_const (c := (iotaOp i : FibOp E r))).mul h𝒜).add
    (h𝒜.mul (contDiffOn_const (c := (iotaOp i : FibOp E r))))

/-- Helper: `a_k(𝒜)` has total degree `0` when `𝒜` has total degree `1`. -/
private theorem isOfTotDeg_aCoef {deg : Fin r → ℤ} (i : Fin (Module.finrank ℂ E))
    {𝒜 : E → FibOp E r} {z : E} (h𝒜 : IsOfTotDeg deg 1 (𝒜 z)) :
    IsOfTotDeg deg 0 (aCoef i 𝒜 z) := by
  have h1 : IsOfTotDeg deg 0 (iotaOp i * 𝒜 z) :=
    IsOfTotDeg.mul' (isOfTotDeg_iotaOp deg i) h𝒜 (by norm_num)
  have h2 : IsOfTotDeg deg 0 (𝒜 z * iotaOp i) :=
    IsOfTotDeg.mul' h𝒜 (isOfTotDeg_iotaOp deg i) (by norm_num)
  exact (degSub (E := E) deg 0).add_mem h1 h2

/-- **Z5.f (D, step).** If `aᵢ(𝒜) = 0` on `U` for `i < k` (`k < n`), there are an open `W ∋ x` in
`U` and a gauge `g` such that `aᵢ(g·𝒜) = 0` on `W` for `i ≤ k`. -/
theorem exists_gauge_step (deg : Fin r → ℤ) (k : Fin (Module.finrank ℂ E)) {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) {𝒜 : E → FibOp E r} (h𝒜 : IsFlatSuperconn deg U 𝒜)
    (ha : ∀ i : Fin (Module.finrank ℂ E), i < k → ∀ z ∈ U, aCoef i 𝒜 z = 0) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ g : E → FibOp E r, IsGauge deg g ∧
      ∀ i : Fin (Module.finrank ℂ E), i ≤ k → ∀ z ∈ W, aCoef i (gaugeOp g 𝒜) z = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have := subsingleton_fibOp (E := E)
    exact ⟨U, hU, hx, subset_rfl, _, isGauge_one deg, fun _ _ _ _ => Subsingleton.elim _ _⟩
  have := nontrivial_fib (E := E) hr
  have hS : ∀ z ∈ U, aCoef k 𝒜 z ∈ gaugeSubalg (E := E) deg k := fun z hz => by
    have hc := aCoef_comm (k := k) (h𝒜.odd z hz) (fun i hi => ha i hi z hz)
    exact ⟨isOfTotDeg_aCoef k (h𝒜.deg_one z hz), hc.1, hc.2⟩
  have hJ : ∀ j ∈ Finset.univ.filter (fun j : Fin (Module.finrank ℂ E) => j < k), ∀ z ∈ U,
      pdbar (Module.finBasis ℂ E j) (aCoef k 𝒜) z = 0 := by
    intro j hj z hz
    have hjk : j < k := (Finset.mem_filter.1 hj).2
    have h1 : ContDiffOn ℝ 1 𝒜 U := h𝒜.smooth.of_le (by simp)
    have hdiff : DifferentiableAt ℝ 𝒜 z := (h𝒜.smooth.contDiffAt (hU.mem_nhds hz)).differentiableAt
      (by simp)
    rw [pdbar_aCoef_eq k _ hdiff, pdbar_eq_zero_of_aCoef hU h1 h𝒜.flat j (ha j hjk) z hz,
      mul_zero, zero_mul, add_zero]
  obtain ⟨W, hWo, hxW, hWU, g, hgs, hgS, hgu, hgk, hgJ⟩ := exists_gauge_solution k hU hx
    (aCoef k 𝒜) (contDiffOn_aCoef k h𝒜.smooth) (gaugeSubalg (E := E) deg k) hS
    (Finset.univ.filter (fun j : Fin (Module.finrank ℂ E) => j < k)) (by simp) hJ
  have hG : IsGauge deg g :=
    ⟨hgs, hgu, fun z => (hgS z).1, fun z j => (hgS z).2.1 j⟩
  refine ⟨W, hWo, hxW, hWU, g, hG, fun i hi z hz => ?_⟩
  have hd : DifferentiableAt ℝ g z := (hgs.differentiable (by simp)) z
  rw [aCoef_gaugeOp i hd hgu hG.comm (fun w => (hgS w).2.2 i hi)]
  rcases hi.lt_or_eq with hlt | rfl
  · rw [ha i hlt z (hWU hz), hgJ i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩) z hz]
    simp only [mul_zero, zero_mul, sub_self]
  · rw [hgk z hz]
    exact sub_self _

/-- Helper: restricting a flat superconnection to a smaller set. -/
private theorem IsFlatSuperconn.mono {deg : Fin r → ℤ} {U V : Set E} {𝒜 : E → FibOp E r}
    (h𝒜 : IsFlatSuperconn deg U 𝒜) (hVU : V ⊆ U) : IsFlatSuperconn deg V 𝒜 :=
  ⟨h𝒜.smooth.mono hVU, fun z hz => h𝒜.deg_one z (hVU hz), fun z hz => h𝒜.odd z (hVU hz),
    fun z hz => h𝒜.flat z (hVU hz)⟩

/-- Helper: the constant gauge `1` acts trivially. -/
private theorem gaugeOp_one (𝒜 : E → FibOp E r) (z : E) :
    gaugeOp (fun _ : E => (1 : FibOp E r)) 𝒜 z = 𝒜 z := by
  have h : ∀ j, pdbar (Module.finBasis ℂ E j) (fun _ : E => (1 : FibOp E r)) z = 0 := fun j => by
    unfold pdbar
    simp
  simp only [gaugeOp, h, mul_zero, Finset.sum_const_zero, sub_zero, one_mul,
    Ring.inverse_one, mul_one]

/-- Helper: induction on the number of remaining variables. -/
private theorem exists_gauge_aux (deg : Fin r → ℤ) (m : ℕ) : ∀ (k : ℕ),
    Module.finrank ℂ E ≤ k + m → ∀ {U : Set E}, IsOpen U → ∀ {x : E}, x ∈ U →
    ∀ {𝒜 : E → FibOp E r}, IsFlatSuperconn deg U 𝒜 →
    (∀ i : Fin (Module.finrank ℂ E), (i : ℕ) < k → ∀ z ∈ U, aCoef i 𝒜 z = 0) →
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ g : E → FibOp E r, IsGauge deg g ∧
      ∀ i, ∀ z ∈ W, aCoef i (gaugeOp g 𝒜) z = 0 := by
  induction m with
  | zero =>
    intro k hk U hU x hx 𝒜 h𝒜 ha
    refine ⟨U, hU, hx, subset_rfl, _, isGauge_one deg, fun i z hz => ?_⟩
    have := ha i (lt_of_lt_of_le i.2 hk) z hz
    simpa only [aCoef, gaugeOp_one] using this
  | succ m ih =>
    intro k hk U hU x hx 𝒜 h𝒜 ha
    by_cases hkn : Module.finrank ℂ E ≤ k
    · refine ⟨U, hU, hx, subset_rfl, _, isGauge_one deg, fun i z hz => ?_⟩
      have := ha i (lt_of_lt_of_le i.2 hkn) z hz
      simpa only [aCoef, gaugeOp_one] using this
    · have hkl : k < Module.finrank ℂ E := not_le.1 hkn
      obtain ⟨W₁, hW₁, hxW₁, hW₁U, g₁, hg₁, hstep⟩ := exists_gauge_step deg ⟨k, hkl⟩ hU hx h𝒜
        (fun i hi z hz => ha i hi z hz)
      have hflat : IsFlatSuperconn deg W₁ (gaugeOp g₁ 𝒜) := (h𝒜.gauge hU hg₁).mono hW₁U
      obtain ⟨W₂, hW₂, hxW₂, hW₂W₁, g₂, hg₂, hfin⟩ := ih (k + 1) (by omega) hW₁ hxW₁ hflat
        (fun i hi z hz => hstep i (Fin.le_def.2 (by simpa using Nat.lt_succ_iff.1 hi)) z hz)
      refine ⟨W₂, hW₂, hxW₂, hW₂W₁.trans hW₁U, fun z => g₂ z * g₁ z, hg₁.mul hg₂, fun i z hz => ?_⟩
      have hd₁ : DifferentiableAt ℝ g₁ z := (hg₁.smooth.differentiable (by simp)) z
      have hd₂ : DifferentiableAt ℝ g₂ z := (hg₂.smooth.differentiable (by simp)) z
      have e : gaugeOp (fun w => g₂ w * g₁ w) 𝒜 z = gaugeOp g₂ (gaugeOp g₁ 𝒜) z :=
        gaugeOp_mul hd₁ hd₂ hg₁.unit hg₂.unit hg₁.comm hg₂.comm
      have := hfin i z hz
      simp only [aCoef] at this ⊢
      rw [e]
      exact this

/-- **Z5.f (D, induction).** If `aᵢ(𝒜) = 0` on `U` for `i < k`, there are an open `W ∋ x` in `U`
and a gauge `g` with `aᵢ(g·𝒜) = 0` on `W` for every `i`. -/
theorem exists_gauge_of_aCoef (deg : Fin r → ℤ) (k : ℕ) {U : Set E} (hU : IsOpen U) {x : E}
    (hx : x ∈ U) {𝒜 : E → FibOp E r} (h𝒜 : IsFlatSuperconn deg U 𝒜)
    (ha : ∀ i : Fin (Module.finrank ℂ E), (i : ℕ) < k → ∀ z ∈ U, aCoef i 𝒜 z = 0) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ g : E → FibOp E r, IsGauge deg g ∧
      ∀ i, ∀ z ∈ W, aCoef i (gaugeOp g 𝒜) z = 0 :=
  exists_gauge_aux deg (Module.finrank ℂ E) k (by omega) hU hx h𝒜 ha

/-- **Z5.f (main).** [B, Lemma 4.1.5 (proof)], [BSW, Thm 5.3], [DK, §2.2.2]. A flat
∂̄-superconnection on an open `U` is, near each `x ∈ U`, gauge equivalent to one whose
`dz̄ᵢ`-coefficients all vanish and which is holomorphic (and still flat, of degree `1`, odd). -/
theorem exists_gauge_holomorphic (deg : Fin r → ℤ) {U : Set E} (hU : IsOpen U) {x : E}
    (hx : x ∈ U) {𝒜 : E → FibOp E r} (h𝒜 : IsFlatSuperconn deg U 𝒜) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ g : E → FibOp E r, IsGauge deg g ∧
      IsFlatSuperconn deg W (gaugeOp g 𝒜) ∧
      ∀ z ∈ W, (∀ i, aCoef i (gaugeOp g 𝒜) z = 0) ∧
        ∀ i, pdbar (Module.finBasis ℂ E i) (gaugeOp g 𝒜) z = 0 := by
  obtain ⟨W, hW, hxW, hWU, g, hg, hfin⟩ := exists_gauge_of_aCoef deg 0 hU hx h𝒜
    (fun i hi => absurd hi (Nat.not_lt_zero _))
  have hflat : IsFlatSuperconn deg W (gaugeOp g 𝒜) := (h𝒜.gauge hU hg).mono hWU
  refine ⟨W, hW, hxW, hWU, g, hg, hflat, fun z hz => ⟨fun i => hfin i z hz, fun i => ?_⟩⟩
  exact pdbar_eq_zero_of_aCoef hW (hflat.smooth.of_le (by simp)) hflat.flat i
    (fun w hw => hfin i w hw) z hz

end Cohesive
