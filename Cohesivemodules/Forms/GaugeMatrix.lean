import Cohesivemodules.Forms.FrameModel

set_option linter.style.header false

/-!
# Z5.i (fibre part): matrices of fibre operators

Blueprint item Z5.i, E.3–E.4 (`blueprint/blueprint-ll.md` §4 E; §11 v1.15). The matrix of a
fibre operator `T : FibOp E r` is `opMat T i j = T(eⱼ)ᵢ ∈ Λ` (`eⱼ` the `j`-th unit vector with
value `1`). For Λ-linear `T`:
* even (`[εⱼ, T] = 0`, e.g. a gauge `g`): `T(t)ᵢ = Σⱼ tⱼ·Tᵢⱼ` (`apply_eq_sum_of_comm`), and
  matrices multiply (`opMat_mul_of_comm`);
* odd (`εⱼT = −Tεⱼ`, e.g. a superconnection): `T = matOp (opMat T)` (`eq_matOp_of_odd`), i.e.
  `T(t)ⱼ = Σᵢ σ(tᵢ)·Tⱼᵢ`.
Degrees (`opMat_hasDeg`), smoothness and `∂̄` of matrix entries (`dbarTot_opMat`), and B.7: if
all `aᵢ` vanish, the matrix of `𝒜` has form degree `0` (`opMat_deg_zero`).
-/

noncomputable section

namespace Cohesive

open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {r : ℕ}

/-- **Z5.i.** The matrix of a fibre operator: `opMat T i j = T(eⱼ)ᵢ`, `eⱼ = Pi.single j 1`. -/
def opMat (T : FibOp E r) (i j : Fin r) : TotFibre E := T (Pi.single j 1) i

/-- Z5.i: formula for `opMat` (rfl). -/
theorem opMat_apply (T : FibOp E r) (i j : Fin r) : opMat T i j = T (Pi.single j 1) i := rfl

/-- Helper: a vector is the sum of its components times the unit vectors. -/
private theorem sum_mulLeftOp_single (t : Fib E r) :
    ∑ j, (mulLeftOp (t j) : FibOp E r) (Pi.single j 1) = t := by
  funext i
  rw [Finset.sum_apply]
  have : ∀ j, (mulLeftOp (t j) : FibOp E r) (Pi.single j 1 : Fib E r) i =
      t j * (Pi.single j 1 : Fib E r) i := fun j => rfl
  simp only [this, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

/-- **Z5.i.** An even Λ-linear operator acts by its matrix: `T(t)ᵢ = Σⱼ tⱼ·Tᵢⱼ`. -/
theorem apply_eq_sum_of_comm {T : FibOp E r} (h : ∀ j, epsOp j * T = T * epsOp j) (t : Fib E r)
    (i : Fin r) : T t i = ∑ j, t j * opMat T i j := by
  conv_lhs => rw [← sum_mulLeftOp_single t]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : T ((mulLeftOp (t j) : FibOp E r) (Pi.single j 1)) =
      (mulLeftOp (t j) : FibOp E r) (T (Pi.single j 1)) := by
    have := congrArg (fun S : FibOp E r => S (Pi.single j 1)) (commute_mulLeftOp_of_eps h (t j))
    exact this.symm
  rw [h1]
  exact (rfl : (mulLeftOp (t j) : FibOp E r) (T (Pi.single j 1)) i = t j * T (Pi.single j 1) i)

/-- **Z5.i.** An odd Λ-linear operator is the `matOp` of its matrix: `T(t)ⱼ = Σᵢ σ(tᵢ)·Tⱼᵢ`. -/
theorem eq_matOp_of_odd {T : FibOp E r} (h : ∀ j, epsOp j * T = -(T * epsOp j)) :
    T = matOp (fun j i => opMat T j i) := by
  refine ContinuousLinearMap.ext fun t => funext fun j => ?_
  rw [matOp_apply]
  conv_lhs => rw [← sum_mulLeftOp_single t]
  rw [map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : T ((mulLeftOp (t i) : FibOp E r) (Pi.single i 1)) =
      (mulLeftOp (sgnTot E (t i)) : FibOp E r) (T (Pi.single i 1)) := by
    have := congrArg (fun S : FibOp E r => S (Pi.single i 1))
      (mulLeftOp_of_eps_anticomm h (t i))
    exact this
  rw [h1]
  show sgnTot E (t i) * T (Pi.single i 1) j = sgnTot E (t i) * opMat T j i
  rfl

/-- **Z5.i.** Matrices of even operators multiply: `(TS)ᵢⱼ = Σₖ Sₖⱼ·Tᵢₖ`. -/
theorem opMat_mul_of_comm {T : FibOp E r} (hT : ∀ j, epsOp j * T = T * epsOp j) (S : FibOp E r)
    (i j : Fin r) : opMat (T * S) i j = ∑ k, opMat S k j * opMat T i k := by
  have := apply_eq_sum_of_comm hT (S (Pi.single j 1)) i
  exact this

/-- Z5.i: the matrix of the identity. -/
theorem opMat_one (i j : Fin r) : opMat (1 : FibOp E r) i j = if i = j then 1 else 0 := by
  simp only [opMat, one_apply_eq_self, Pi.single_apply]

/-- **Z5.i.** If `T` has total degree `d`, the entry `Tᵢⱼ` has form degree `deg j + d − deg i`. -/
theorem opMat_hasDeg {deg : Fin r → ℤ} {d : ℤ} {T : FibOp E r} (hT : IsOfTotDeg deg d T)
    (i j : Fin r) (q : Fin (Module.finrank ℂ E + 1)) (hq : ((q : ℕ) : ℤ) ≠ deg j + d - deg i) :
    opMat T i j q = 0 := by
  have hmem : (Pi.single j 1 : Fib E r) ∈ totDegSub (E := E) deg (deg j) := by
    intro k p hp
    by_cases hk : k = j
    · subst hk
      rw [Pi.single_eq_same, TotFibre.one_eq]
      exact ofDeg_apply_ne _ p (by omega)
    · rw [Pi.single_eq_of_ne hk]
      rfl
  have := hT (deg j) _ hmem i q (by omega)
  exact this

/-- **Z5.i (B.7).** If every `aᵢ = ιᵢ𝒜 + 𝒜ιᵢ` vanishes at `z`, the matrix of `𝒜 z` has form
degree `0` (`preserves_deg_zero`). -/
theorem opMat_deg_zero {𝒜 : E → FibOp E r} {z : E} (ha : ∀ i, aCoef i 𝒜 z = 0) (i j : Fin r)
    (q : Fin (Module.finrank ℂ E + 1)) (hq : (q : ℕ) ≠ 0) : opMat (𝒜 z) i j q = 0 := by
  have hs : ∀ k, (Pi.single j 1 : Fib E r) k =
      TotFibre.ofDeg 0 (TotFibre.deg 0 ((Pi.single j 1 : Fib E r) k)) := by
    intro k
    by_cases hk : k = j
    · subst hk
      rw [Pi.single_eq_same, TotFibre.one_eq, TotFibre.deg_ofDeg_self (Nat.zero_le _)]
    · rw [Pi.single_eq_of_ne hk, map_zero, map_zero]
  have := preserves_deg_zero ha _ hs i
  rw [opMat, this]
  exact ofDeg_apply_ne _ q (by omega)

/-- Z5.i: matrix entries of a smooth operator family are smooth. -/
theorem contDiffOn_opMat {g : E → FibOp E r} {s : Set E} (hg : ContDiffOn ℝ ∞ g s)
    (i j : Fin r) : ContDiffOn ℝ ∞ (fun z => opMat (g z) i j) s := by
  let L : FibOp E r →L[ℂ] TotFibre E :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => TotFibre E) i).comp
      (ContinuousLinearMap.apply ℂ (Fib E r) (Pi.single j 1))
  exact (L.restrictScalars ℝ).contDiff.comp_contDiffOn hg

/-- Z5.i: `∂ᵥ` of a matrix entry is the entry of `∂ᵥ`. -/
theorem pdbar_opMat {g : E → FibOp E r} {z : E} (hg : DifferentiableAt ℝ g z) (v : E)
    (i j : Fin r) : pdbar v (fun w => opMat (g w) i j) z = opMat (pdbar v g z) i j := by
  let L : FibOp E r →L[ℂ] TotFibre E :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => TotFibre E) i).comp
      (ContinuousLinearMap.apply ℂ (Fib E r) (Pi.single j 1))
  exact pdbar_comp_clm L v hg

/-- **Z5.i.** `∂̄` of a matrix entry: `∂̄Tᵢⱼ = (Σₖ εₖ ∂ₖT)ᵢⱼ` (B.1, `dbarFib_eq_sum`). -/
theorem dbarTot_opMat {g : E → FibOp E r} {z : E} (hg : DifferentiableAt ℝ g z) (i j : Fin r) :
    dbarTot E (fun w => opMat (g w) i j) z =
      opMat (∑ k, epsOp k * pdbar (Module.finBasis ℂ E k) g z) i j := by
  let L : FibOp E r →L[ℂ] Fib E r := ContinuousLinearMap.apply ℂ (Fib E r) (Pi.single j 1)
  have hs : DifferentiableAt ℝ (fun w => L (g w)) z :=
    (L.restrictScalars ℝ).differentiableAt.comp z hg
  have h1 := dbarFib_eq_sum hs
  have h2 : ∀ k, pdbar (Module.finBasis ℂ E k) (fun w => L (g w)) z =
      L (pdbar (Module.finBasis ℂ E k) g z) := fun k => pdbar_comp_clm L _ hg
  have h3 : dbarFib (fun w => L (g w)) z i = dbarTot E (fun w => opMat (g w) i j) z := rfl
  rw [← h3, h1]
  simp only [h2, Finset.sum_apply]
  simp only [opMat, sum_apply, mul_apply_eq_comp, Finset.sum_apply]
  rfl

/-- Helper: the submodule of operators of total degree `d`. -/
private def degSub' (deg : Fin r → ℤ) (d : ℤ) : Submodule ℂ (FibOp E r) where
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

/-- Helper: the identity has total degree `0`. -/
private theorem isOfTotDeg_one' (deg : Fin r → ℤ) : IsOfTotDeg deg 0 (1 : FibOp E r) := by
  intro m s hs
  rw [one_apply_eq_self, add_zero]
  exact hs

/-- Helper: `IsOfTotDeg.mul` with the degree written as a hypothesis. -/
private theorem isOfTotDeg_mul' {deg : Fin r → ℤ} {d d' d'' : ℤ} {T T' : FibOp E r}
    (hT : IsOfTotDeg deg d T) (hT' : IsOfTotDeg deg d' T') (h : d'' = d' + d) :
    IsOfTotDeg deg d'' (T * T') := h ▸ hT.mul hT'

/-- Helper: the inverse of a unit of total degree `0` has total degree `0` (finite dimension). -/
private theorem isOfTotDeg_inverse' {deg : Fin r → ℤ} {T : FibOp E r} (hu : IsUnit T)
    (hT : IsOfTotDeg deg 0 T) : IsOfTotDeg deg 0 (Ring.inverse T) := by
  let L : degSub' (E := E) deg 0 →ₗ[ℂ] degSub' (E := E) deg 0 :=
    (LinearMap.mulLeft ℂ T).restrict (fun x hx => isOfTotDeg_mul' hT hx (by norm_num))
  have hinj : Function.Injective L := by
    intro b b' hb
    have hb' : T * (b : FibOp E r) = T * (b' : FibOp E r) := congrArg Subtype.val hb
    have := congrArg (fun x => Ring.inverse T * x) hb'
    simp only [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul] at this
    exact Subtype.ext this
  have hsurj : Function.Surjective L :=
    (LinearMap.injective_iff_surjective (K := ℂ) (V := degSub' (E := E) deg 0) (f := L)).1 hinj
  obtain ⟨b, hb⟩ := hsurj ⟨1, isOfTotDeg_one' deg⟩
  have hb' : T * (b : FibOp E r) = 1 := congrArg Subtype.val hb
  have h2 : Ring.inverse T = (b : FibOp E r) := by
    have := congrArg (fun x => Ring.inverse T * x) hb'
    simpa only [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul, mul_one] using this.symm
  rw [h2]
  exact b.2

/-- Helper: `Ring.inverse ∘ g` is `C^∞` when `g` is and all `g w` are units. -/
private theorem contDiff_ringInverse_infty' {g : E → FibOp E r} (hg : ContDiff ℝ ∞ g)
    (hu : ∀ w, IsUnit (g w)) : ContDiff ℝ ∞ (fun w => Ring.inverse (g w)) := by
  refine contDiff_iff_contDiffAt.2 fun w => ?_
  obtain ⟨u, hu'⟩ := hu w
  have h := contDiffAt_ringInverse ℝ (n := ∞) u
  rw [hu'] at h
  exact h.comp w hg.contDiffAt

/-- **Z5.i.** The pointwise inverse of a gauge is a gauge (cf. the private `isOfTotDeg_inverse` in
`Forms/GaugeInduction.lean`). -/
theorem IsGauge.inverse {deg : Fin r → ℤ} {g : E → FibOp E r} (hg : IsGauge deg g) :
    IsGauge deg (fun z => Ring.inverse (g z)) where
  smooth := contDiff_ringInverse_infty' hg.smooth hg.unit
  unit z := (hg.unit z).ringInverse
  deg_zero z := isOfTotDeg_inverse' (hg.unit z) (hg.deg_zero z)
  comm z j := by
    have hu := hg.unit z
    have h1 := Ring.inverse_mul_cancel _ hu
    have h2 := Ring.mul_inverse_cancel _ hu
    calc epsOp j * Ring.inverse (g z)
        = Ring.inverse (g z) * (g z * epsOp j) * Ring.inverse (g z) := by
          simp only [← mul_assoc, h1, one_mul]
      _ = Ring.inverse (g z) * (epsOp j * g z) * Ring.inverse (g z) := by rw [hg.comm z j]
      _ = Ring.inverse (g z) * epsOp j := by
          simp only [mul_assoc, h2, mul_one]

end Cohesive
