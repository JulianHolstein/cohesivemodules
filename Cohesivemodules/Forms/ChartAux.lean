import Cohesivemodules.Forms.ChartAuxBasic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Chart-transport and smoothness helpers (blueprint F9, F11, F12 support) (part 2 of 2)

Split from `Forms/ChartAux.lean` for size; continues `Forms/ChartAuxBasic.lean`.
-/

noncomputable section
namespace Cohesive
open TopologicalSpace Manifold
open scoped ContDiff
variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
variable {E} {U : Opens X}

/-! ## `∂̄` on the total fibre -/

/-- F9 helper: `∂̄` of the zero function is zero. -/
theorem dbar_zero_fn {q : ℕ} (z : E) :
    dbar (fun _ : E => (0 : DolbeaultFibre E q ℂ)) z = 0 := by
  have h := dbar_const_smul (0 : ℂ) (α := fun _ : E => (0 : DolbeaultFibre E q ℂ)) (x := z)
    (differentiableAt_const _)
  have h2 : ((0 : ℂ) • fun _ : E => (0 : DolbeaultFibre E q ℂ)) =
      fun _ : E => (0 : DolbeaultFibre E q ℂ) := by
    funext w
    simp only [Pi.smul_apply, smul_zero]
  rw [h2, zero_smul] at h
  exact h

/-- F9 helper: `dbarTot` only depends on the germ. -/
theorem dbarTot_congr {f g : E → TotFibre E} {z : E} (h : f =ᶠ[nhds z] g) :
    dbarTot E f z = dbarTot E g z := by
  unfold dbarTot
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [dbar_congr (α := fun w => f w q) (β := fun w => g w q)
    (h.mono fun w hw => by simp only [hw])]

/-- F9 helper: `dbarTot` of the zero function is zero. -/
theorem dbarTot_zero (z : E) : dbarTot E (0 : E → TotFibre E) z = 0 := by
  unfold dbarTot
  refine Finset.sum_eq_zero fun q _ => ?_
  have : dbar (fun w => (0 : E → TotFibre E) w q) z = 0 := dbar_zero_fn z
  rw [this, map_zero]

/-- F9 helper: `dbarTot` is additive at points of differentiability. -/
theorem dbarTot_add {f g : E → TotFibre E} {z : E} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbarTot E (f + g) z = dbarTot E f z + dbarTot E g z := by
  unfold dbarTot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← map_add]
  congr 1
  exact dbar_add (α := fun w => f w q) (β := fun w => g w q)
    (differentiableAt_tot_iff.1 hf q) (differentiableAt_tot_iff.1 hg q)

/-- F9 helper: `dbarTot` is `ℂ`-homogeneous at points of differentiability. -/
theorem dbarTot_smul (c : ℂ) {f : E → TotFibre E} {z : E} (hf : DifferentiableAt ℝ f z) :
    dbarTot E (c • f) z = c • dbarTot E f z := by
  unfold dbarTot
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← map_smul]
  congr 1
  exact dbar_const_smul c (α := fun w => f w q) (differentiableAt_tot_iff.1 hf q)

/-- F9 helper: `∂̄` on the total fibre commutes with holomorphic pullback (F7.a, degreewise). -/
theorem dbarTot_pullback {β : E → TotFibre E} {G : E → E} {z : E}
    (hβ : DifferentiableAt ℝ β (G z)) (hG : ContDiffAt ℂ 2 G z) :
    dbarTot E (fun w => TotFibre.pull (fderiv ℂ G w) (β (G w))) z =
      TotFibre.pull (fderiv ℂ G z) (dbarTot E β (G z)) := by
  unfold dbarTot
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [TotFibre.pull_ofDeg]
  congr 1
  exact dbar_pullback (α := fun u => β u q) (G := G) (x := z)
    (differentiableAt_tot_iff.1 hβ q) hG

/-- F9 helper: `dbarTot` of a function smooth at `z` is smooth at `z`. -/
theorem contDiffAt_dbarTot {f : E → TotFibre E} {z : E} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (dbarTot E f) z := by
  refine contDiffAt_infty.2 fun n => ?_
  have hn : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f z := hf.of_le (by exact_mod_cast le_top)
  obtain ⟨u, hu, huo, hzu⟩ := eventually_nhds_iff.1 (hn.eventually (by simp))
  show ContDiffAt ℝ n (fun w => ∑ q : Fin (Module.finrank ℂ E + 1),
    TotFibre.ofDeg ((q : ℕ) + 1) (dbar (fun w' ↦ f w' q) w)) z
  refine ContDiffAt.sum fun q _ => ?_
  have h1 : ContDiffOn ℝ ((n : WithTop ℕ∞) + 1) (fun w => f w q) u := fun w hw =>
    ((contDiffAt_tot_iff.1 (hu w hw)) q).contDiffWithinAt
  have h2 : ContDiffAt ℝ n (dbar (fun w => f w q)) z :=
    (contDiffOn_dbar huo h1).contDiffAt (huo.mem_nhds hzu)
  let L : DolbeaultFibre E ((q : ℕ) + 1) ℂ →L[ℝ] TotFibre E :=
    (LinearMap.toContinuousLinearMap (TotFibre.ofDeg (E := E) ((q : ℕ) + 1))).restrictScalars ℝ
  exact L.contDiff.contDiffAt.comp z h2

/-- F9 helper: the component of `dbarTot f w` in degree `r + 1` is `∂̄` of the component of `f`
in degree `r`. -/
theorem dbarTot_apply_succ (f : E → TotFibre E) (w : E) {r : ℕ}
    (h : r + 1 < Module.finrank ℂ E + 1) :
    (dbarTot E f w ⟨r + 1, h⟩ : DolbeaultFibre E (r + 1) ℂ) =
      dbar (fun w' => (f w' ⟨r, by omega⟩ : DolbeaultFibre E r ℂ)) w := by
  refine (TotFibre.deg_eq_apply (dbarTot E f w) h).symm.trans ?_
  unfold dbarTot
  rw [map_sum, Finset.sum_eq_single ⟨r, by omega⟩]
  · exact TotFibre.deg_ofDeg_self (by omega) _
  · intro q _ hq
    refine TotFibre.deg_ofDeg_ne ?_ _
    intro hc
    exact hq (Fin.ext (by simpa using hc.symm))
  · intro hr
    exact absurd (Finset.mem_univ _) hr

/-- F9 helper: the component of `dbarTot f w` in degree `0` vanishes. -/
theorem dbarTot_apply_zero (f : E → TotFibre E) (w : E)
    (h : 0 < Module.finrank ℂ E + 1) :
    (dbarTot E f w ⟨0, h⟩ : DolbeaultFibre E 0 ℂ) = 0 := by
  refine (TotFibre.deg_eq_apply (dbarTot E f w) h).symm.trans ?_
  unfold dbarTot
  rw [map_sum]
  exact Finset.sum_eq_zero fun q _ => TotFibre.deg_ofDeg_ne (by omega) _

/-- F9 helper: `∂̄∂̄ = 0` on the total fibre (F4, degreewise). -/
theorem dbarTot_dbarTot {f : E → TotFibre E} {z : E} (hf : ContDiffAt ℝ 2 f z) :
    dbarTot E (dbarTot E f) z = 0 := by
  show ∑ q : Fin (Module.finrank ℂ E + 1),
    TotFibre.ofDeg ((q : ℕ) + 1) (dbar (fun w => dbarTot E f w q) z) = 0
  refine Finset.sum_eq_zero fun q _ => ?_
  have : dbar (fun w => dbarTot E f w q) z = 0 := by
    obtain ⟨k, hk⟩ := q
    cases k with
    | zero =>
      have h0 : (fun w => (dbarTot E f w ⟨0, hk⟩ : DolbeaultFibre E 0 ℂ)) =
          fun _ => (0 : DolbeaultFibre E 0 ℂ) := funext fun w => dbarTot_apply_zero f w hk
      exact (congrArg (fun g => dbar g z) h0).trans (dbar_zero_fn z)
    | succ r =>
      have h0 : (fun w => (dbarTot E f w ⟨r + 1, hk⟩ : DolbeaultFibre E (r + 1) ℂ)) =
          fun w => dbar (fun w' => (f w' ⟨r, by omega⟩ : DolbeaultFibre E r ℂ)) w :=
        funext fun w => dbarTot_apply_succ f w hk
      refine (congrArg (fun g => dbar g z) h0).trans (dbar_dbar ?_)
      exact (contDiffAt_tot_iff.1 hf) ⟨r, by omega⟩
  rw [this, map_zero]

/-- F9 helper: `∂̄` of a function supported in degree `q` is supported in degree `q + 1`. -/
theorem dbarTot_support {f : E → TotFibre E} {q : ℤ}
    (hf : ∀ (w : E) (j : Fin (Module.finrank ℂ E + 1)), ((j : ℕ) : ℤ) ≠ q → f w j = 0)
    (z : E) (i : Fin (Module.finrank ℂ E + 1)) (hi : ((i : ℕ) : ℤ) ≠ q + 1) :
    dbarTot E f z i = 0 := by
  have hz : ∀ j : Fin (Module.finrank ℂ E + 1), ((j : ℕ) : ℤ) ≠ q →
      dbar (fun w => (f w j : DolbeaultFibre E j ℂ)) z = 0 := fun j hj => by
    have : (fun w => (f w j : DolbeaultFibre E j ℂ)) = fun _ => 0 :=
      funext fun w => hf w j hj
    exact (congrArg (fun g => dbar g z) this).trans (dbar_zero_fn z)
  by_cases hq : ∃ j : Fin (Module.finrank ℂ E + 1), ((j : ℕ) : ℤ) = q
  · obtain ⟨j, hj⟩ := hq
    have : dbarTot E f z = TotFibre.ofDeg ((j : ℕ) + 1) (dbar (fun w => f w j) z) := by
      unfold dbarTot
      rw [Finset.sum_eq_single j]
      · intro j' _ hj'
        rw [hz j' (fun h => hj' (Fin.ext (by omega))), map_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [this]
    exact ofDeg_apply_ne _ i (by omega)
  · have : dbarTot E f z = 0 := by
      unfold dbarTot
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hz j (fun h => hq ⟨j, h⟩), map_zero]
    rw [this]
    rfl

/-- F9 helper: `dbarTot` commutes with finite sums of differentiable functions. -/
theorem dbarTot_finset_sum {ι : Type} (s : Finset ι) (F : ι → E → TotFibre E) {z : E}
    (hF : ∀ i ∈ s, DifferentiableAt ℝ (F i) z) :
    dbarTot E (fun w => ∑ i ∈ s, F i w) z = ∑ i ∈ s, dbarTot E (F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : (fun w => ∑ i ∈ (∅ : Finset ι), F i w) = (0 : E → TotFibre E) := by
      funext w
      simp only [Finset.sum_empty, Pi.zero_apply]
    rw [h, dbarTot_zero]
    simp only [Finset.sum_empty]
  | insert a s ha ih =>
    have h1 : (fun w => ∑ i ∈ insert a s, F i w) = F a + fun w => ∑ i ∈ s, F i w := by
      funext w
      simp only [Finset.sum_insert ha, Pi.add_apply]
    rw [h1, dbarTot_add (hF a (Finset.mem_insert_self a s))
      (DifferentiableAt.fun_sum fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)), Finset.sum_insert ha]

/-- F9 helper: `∂̄` of a homogeneous function. -/
theorem dbarTot_ofDeg (r : ℕ) (c : E → DolbeaultFibre E r ℂ) (z : E) :
    dbarTot E (fun w => TotFibre.ofDeg r (c w)) z = TotFibre.ofDeg (r + 1) (dbar c z) := by
  by_cases hr : r < Module.finrank ℂ E + 1
  · unfold dbarTot
    rw [Finset.sum_eq_single ⟨r, hr⟩]
    · have h : (fun w => (TotFibre.ofDeg r (c w) ⟨r, hr⟩ : DolbeaultFibre E r ℂ)) = c :=
        funext fun w => (TotFibre.deg_eq_apply _ hr).symm.trans
          (TotFibre.deg_ofDeg_self (by omega) _)
      exact congrArg (fun g => TotFibre.ofDeg (r + 1) (dbar g z)) h
    · intro j _ hj
      have h : (fun w => (TotFibre.ofDeg r (c w) j : DolbeaultFibre E j ℂ)) = fun _ => 0 :=
        funext fun w => ofDeg_apply_ne _ j (fun hc => hj (Fin.ext (by dsimp only; omega)))
      rw [(congrArg (fun g => dbar g z) h).trans (dbar_zero_fn z), map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have hz : (fun w => (TotFibre.ofDeg r (c w) : TotFibre E)) = 0 :=
      funext fun w => funext fun i => ofDeg_apply_ne _ i (by have := i.2; omega)
    rw [hz, dbarTot_zero]
    funext i
    exact (ofDeg_apply_ne _ i (by have := i.2; omega)).symm

/-- F9 helper: **Leibniz rule on the total fibre** for `f` supported in degree `p`. -/
theorem dbarTot_mul_of_support {f g : E → TotFibre E} {z : E} {p : ℕ}
    (hp : p ≤ Module.finrank ℂ E) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hs : ∀ (w : E) (j : Fin (Module.finrank ℂ E + 1)), ((j : ℕ) : ℤ) ≠ (p : ℤ) → f w j = 0) :
    dbarTot E (f * g) z =
      dbarTot E f z * g z + (-1 : ℂ) ^ p • (f z * dbarTot E g z) := by
  have hfa : ∀ w, f w = TotFibre.ofDeg p (TotFibre.deg p (f w)) := fun w =>
    totDeg_eq_ofDeg hp (hs w)
  have ha : DifferentiableAt ℝ (fun w => TotFibre.deg (E := E) p (f w)) z :=
    differentiableAt_lin_of_tot _ hf
  have hb : ∀ q : ℕ, DifferentiableAt ℝ (fun w => TotFibre.deg (E := E) q (g w)) z := fun q =>
    differentiableAt_lin_of_tot _ hg
  have hfo : DifferentiableAt ℝ
      (fun w => (TotFibre.ofDeg p (TotFibre.deg p (f w)) : TotFibre E)) z :=
    differentiableAt_lin_to_tot _ ha
  have hbo : ∀ q : ℕ, DifferentiableAt ℝ
      (fun w => (TotFibre.ofDeg q (TotFibre.deg q (g w)) : TotFibre E)) z := fun q =>
    differentiableAt_lin_to_tot _ (hb q)
  have e2 : f * g = fun w => ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
      TotFibre.ofDeg (p + q) (wedge (TotFibre.deg p (f w)) (TotFibre.deg q (g w))) :=
    funext fun w => ofDeg_mul_decomp (f w) (g w) _ (hfa w)
  have e3 : g = fun w => ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
      TotFibre.ofDeg q (TotFibre.deg q (g w)) := funext fun w => (TotFibre.sum_ofDeg_deg (g w)).symm
  have e1 : f = fun w => TotFibre.ofDeg p (TotFibre.deg p (f w)) := funext hfa
  have hF : ∀ q ∈ Finset.range (Module.finrank ℂ E + 1), DifferentiableAt ℝ (fun w =>
      (TotFibre.ofDeg (p + q) (wedge (TotFibre.deg p (f w)) (TotFibre.deg q (g w))) : TotFibre E))
      z := by
    intro q _
    have := differentiableAt_mul_tot hfo (hbo q)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
    exact ofDeg_wedge _ _
  have key1 : dbarTot E (f * g) z = ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
      TotFibre.ofDeg (p + q + 1)
        (dbar (fun w => wedge (TotFibre.deg p (f w)) (TotFibre.deg q (g w))) z) := by
    rw [e2, dbarTot_finset_sum (Finset.range (Module.finrank ℂ E + 1)) (fun q w =>
      TotFibre.ofDeg (p + q) (wedge (TotFibre.deg p (f w)) (TotFibre.deg q (g w)))) hF]
    exact Finset.sum_congr rfl fun q _ =>
      dbarTot_ofDeg (p + q) (fun w => wedge (TotFibre.deg p (f w)) (TotFibre.deg q (g w))) z
  have key2 : dbarTot E f z = TotFibre.ofDeg (p + 1) (dbar (fun w => TotFibre.deg p (f w)) z) :=
    (congrArg (fun h => dbarTot E h z) e1).trans (dbarTot_ofDeg p _ z)
  have key4 : dbarTot E g z = ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
      TotFibre.ofDeg (q + 1) (dbar (fun w => TotFibre.deg q (g w)) z) := by
    refine (congrArg (fun h => dbarTot E h z) e3).trans ?_
    rw [dbarTot_finset_sum (Finset.range (Module.finrank ℂ E + 1)) (fun q w =>
      TotFibre.ofDeg q (TotFibre.deg q (g w))) (fun q _ => hbo q)]
    exact Finset.sum_congr rfl fun q _ => dbarTot_ofDeg q (fun w => TotFibre.deg q (g w)) z
  calc dbarTot E (f * g) z
      = ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
        (TotFibre.ofDeg (p + 1) (dbar (fun w => TotFibre.deg p (f w)) z) *
            TotFibre.ofDeg q (TotFibre.deg q (g z)) +
          (-1 : ℂ) ^ p • (TotFibre.ofDeg p (TotFibre.deg p (f z)) *
            TotFibre.ofDeg (q + 1) (dbar (fun w => TotFibre.deg q (g w)) z))) := by
        rw [key1]
        exact Finset.sum_congr rfl fun q _ =>
          dbar_wedge (α := fun w => TotFibre.deg p (f w)) (β := fun w => TotFibre.deg q (g w))
            ha (hb q)
    _ = TotFibre.ofDeg (p + 1) (dbar (fun w => TotFibre.deg p (f w)) z) *
          (∑ q ∈ Finset.range (Module.finrank ℂ E + 1), TotFibre.ofDeg q (TotFibre.deg q (g z))) +
        (-1 : ℂ) ^ p • (TotFibre.ofDeg p (TotFibre.deg p (f z)) *
          ∑ q ∈ Finset.range (Module.finrank ℂ E + 1),
            TotFibre.ofDeg (q + 1) (dbar (fun w => TotFibre.deg q (g w)) z)) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.smul_sum, Finset.sum_add_distrib]
    _ = dbarTot E f z * g z + (-1 : ℂ) ^ p • (f z * dbarTot E g z) := by
        rw [key2, key4, TotFibre.sum_ofDeg_deg, ← hfa z]

end Cohesive
