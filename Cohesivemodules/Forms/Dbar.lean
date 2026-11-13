import Cohesivemodules.Forms.DbarDef
import Cohesivemodules.Forms.Fibre
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option linter.style.header false

/-!
# F3–F4: the operator `∂̄` on open subsets of `E`, and `∂̄∂̄ = 0`

Blueprint items F3, F4 (conventions §6; prototype `Scratch/P2_Fibres.lean`, Parts B–D).
The definitions (and their basic API) are in `Cohesivemodules/Forms/DbarDef.lean`.

* `antiPart L = L″`, `L″ v = ½ (L v + i·L (i v))`, the antilinear part of an `ℝ`-linear map
  `L : E → G`, as a `ℂ`-linear map on `Ē` (F3.a).
* `dbar α x = alternatizeUncurryFin (D″α(x))` with `D″α(x) = antiPart (fderiv ℝ α x)`, over `ℂ` on
  `Ē`, for `α : E → Λ^{0,q}(E; F)`. No factorials: Mathlib's `extDeriv` normalization,
  `∂̄α(x; v₀, …, v_q) = Σ_i (-1)^i D″_{v_i} α(x; …, v̂_i, …)` (conventions §6).
* F3.b `ℂ`-linear in `α`, local, smooth in ⇒ smooth out; F3.c (sanity) `∂̄α` is the
  `(0, q+1)`-part of Mathlib's `extDeriv` of `α` read as a real form; F4 `∂̄∂̄ = 0`.

## Junk values
`fderiv` is `0` where `α` is not differentiable, so `dbar α x` is junk there. Every statement
below carries the differentiability or smoothness it needs (CLAUDE.md, faithfulness 5).

## Naming
Forms are called `α`, `β` (not `ω`): under `open scoped ContDiff`, `ω` is the notation for
analytic smoothness.

## Deviations
* ∂̄ is defined on all functions `E → Λ^{0,q}(E; F)` (not only on open subsets); locality
  (`dbar_congr`) makes it depend only on the germ, which gives ∂̄ on open subsets.
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap Complex ComplexConjugate Conj Filter Topology
open scoped ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-! ## The antilinear part (F3.a) -/

/-- F3: `antiPart` commutes with post-composition by a `ℂ`-linear map. -/
theorem antiPart_comp {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (T : G →L[ℂ] H)
    (L : E →L[ℝ] G) : antiPart ((T.restrictScalars ℝ).comp L) = T.comp (antiPart L) := by
  ext v
  simp [map_add, map_smul]

/-- F3: the antilinear part of a `ℂ`-linear map vanishes. -/
theorem antiPart_restrictScalars (T : E →L[ℂ] G) : antiPart (T.restrictScalars ℝ) = 0 := by
  ext v
  simp only [antiPart_apply, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_smul,
    I_mul_I, neg_smul, one_smul, add_neg_cancel, smul_zero, zero_apply]

/-- F3: `antiPart` is additive. -/
theorem antiPart_add (L L' : E →L[ℝ] G) : antiPart (L + L') = antiPart L + antiPart L' := by
  ext v
  simp only [antiPart_apply, _root_.add_apply, smul_add]
  abel

/-- F3: `antiPart` commutes with complex scalars acting on the values. -/
theorem antiPart_smul (c : ℂ) (L : E →L[ℝ] G) : antiPart (c • L) = c • antiPart L := by
  ext v
  simp only [antiPart_apply, _root_.smul_apply, smul_add, smul_comm c (I : ℂ),
    smul_comm c (2 : ℂ)⁻¹]

variable (E G) in
/-- F3: `antiPart` as a continuous `ℝ`-linear map `(E →L[ℝ] G) →L[ℝ] (Ē →L[ℂ] G)`
(`‖L″‖ ≤ ‖L‖`); used for smoothness of `∂̄α`. -/
def antiPartCLM : (E →L[ℝ] G) →L[ℝ] (Conj E →L[ℂ] G) :=
  LinearMap.mkContinuous
    { toFun := antiPart
      map_add' := antiPart_add
      map_smul' := fun r L => by
        rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, ← antiPart_smul] }
    1 (fun L => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
      have h1 : ‖L (ofConj v)‖ ≤ ‖L‖ * ‖v‖ := by
        simpa using L.le_opNorm (ofConj v)
      have h2 : ‖I • L (I • ofConj v)‖ ≤ ‖L‖ * ‖v‖ := by
        have := L.le_opNorm (I • ofConj v)
        simpa [norm_smul] using this
      show ‖(2 : ℂ)⁻¹ • (L (ofConj v) + I • L (I • ofConj v))‖ ≤ _
      rw [norm_smul]
      have h3 := norm_add_le (L (ofConj v)) (I • L (I • ofConj v))
      have : ‖(2 : ℂ)⁻¹‖ = 2⁻¹ := by simp
      rw [this]
      linarith)

/-- F3: `antiPartCLM` is `antiPart`. -/
@[simp] theorem antiPartCLM_apply (L : E →L[ℝ] G) : antiPartCLM E G L = antiPart L := rfl

/-! ## `D″` and `∂̄` (F3) -/

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {q : ℕ}

/-- F3: `∂̄` as a composite of continuous `ℝ`-linear maps applied to `fderiv ℝ α x`. -/
theorem dbar_eq_comp (α : E → DolbeaultFibre E q F) (x : E) :
    dbar α x = alternatizeUncurryFinCLM ℂ (Conj E) F
      (antiPartCLM E (DolbeaultFibre E q F) (fderiv ℝ α x)) :=
  rfl

/-! ### F3.b -/

/-- **F3.b.** `∂̄` is additive (at points where both forms are differentiable). -/
theorem dbar_add {α β : E → DolbeaultFibre E q F} {x : E} (hα : DifferentiableAt ℝ α x)
    (hβ : DifferentiableAt ℝ β x) : dbar (α + β) x = dbar α x + dbar β x := by
  rw [dbar_eq_comp, dbar_eq_comp, dbar_eq_comp, fderiv_add hα hβ, map_add, map_add]

/-- **F3.b.** `∂̄` is `ℂ`-linear: `∂̄(c α) = c ∂̄α` (at points where `α` is differentiable). -/
theorem dbar_const_smul (c : ℂ) {α : E → DolbeaultFibre E q F} {x : E}
    (hα : DifferentiableAt ℝ α x) :
    dbar (c • α) x = c • dbar α x := by
  rw [dbar_eq_comp, dbar_eq_comp, fderiv_const_smul hα, antiPartCLM_apply, antiPartCLM_apply,
    antiPart_smul, map_smul]

/-- **F3.b.** Locality: `∂̄α(x)` depends only on the germ of `α` at `x`. -/
theorem dbar_congr {α β : E → DolbeaultFibre E q F} {x : E} (h : α =ᶠ[𝓝 x] β) :
    dbar α x = dbar β x := by
  rw [dbar_eq_comp, dbar_eq_comp, h.fderiv_eq]

/-- **F3.b.** Smooth in, smooth out: on an open set, `α` of class `C^{n+1}` gives `∂̄α` of class
`C^n`. -/
theorem contDiffOn_dbar {α : E → DolbeaultFibre E q F} {U : Set E} (hU : IsOpen U) {n : WithTop ℕ∞}
    (h : ContDiffOn ℝ (n + 1) α U) : ContDiffOn ℝ n (dbar α) U := by
  have h1 : ContDiffOn ℝ n (fderiv ℝ α) U := h.fderiv_of_isOpen hU le_rfl
  exact ((alternatizeUncurryFinCLM ℂ (Conj E) F).restrictScalars ℝ ∘L
    antiPartCLM E (DolbeaultFibre E q F)).contDiff.comp_contDiffOn h1

/-- **F3.b.** Smooth in, smooth out, `C^∞` form. -/
theorem contDiffOn_dbar_infty {α : E → DolbeaultFibre E q F} {U : Set E} (hU : IsOpen U)
    (h : ContDiffOn ℝ ∞ α U) : ContDiffOn ℝ ∞ (dbar α) U :=
  contDiffOn_dbar hU (n := ∞) (by simpa using h)

/-! ### F3.c (sanity): `∂̄` is the `(0, q+1)`-part of `extDeriv` -/

/-- F3.c: the identity `E → Ē` as a continuous `ℝ`-linear map. -/
def toConjR : E →L[ℝ] Conj E where
  toFun := toConj
  map_add' _ _ := rfl
  map_smul' r v := by
    rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, toConj_smul, conj_ofReal]
  cont := continuous_id

/-- F3.c: a `(0,q)`-form at a point, read as a real `F`-valued alternating form on `E`
(`v ↦ α (v̄)`, the slots taken in `Ē`). -/
def DolbeaultFibre.toReal (α : DolbeaultFibre E q F) : E [⋀^Fin q]→L[ℝ] F :=
  (α.restrictScalars ℝ).compContinuousLinearMap toConjR

/-- F3.c: formula for `DolbeaultFibre.toReal`. -/
@[simp] theorem DolbeaultFibre.toReal_apply (α : DolbeaultFibre E q F) (v : Fin q → E) :
    DolbeaultFibre.toReal α v = α (fun j => toConj (v j)) := rfl

/-- F3.c helper: scaling the slots of a `(0,q)`-form by `c j` on `E` scales by `∏ conj (c j)`. -/
private theorem alt_apply_conj_smul (g : DolbeaultFibre E q F) (u : Fin q → E) (c : Fin q → ℂ) :
    g (fun j => toConj (c j • u j)) = (∏ j, conj (c j)) • g (fun j => toConj (u j)) := by
  simp only [toConj_smul]
  exact g.toContinuousMultilinearMap.map_smul_univ _ _

/-- F3.c helper: `DolbeaultFibre.toReal` as a continuous `ℝ`-linear map. -/
private def toRealCLM : DolbeaultFibre E q F →L[ℝ] (E [⋀^Fin q]→L[ℝ] F) :=
  (ContinuousAlternatingMap.compContinuousLinearMapCLM (toConjR (E := E))).comp
    (ContinuousAlternatingMap.restrictScalarsLI (𝕜 := ℂ) (E := Conj E) (F := F) ℝ
      ).toContinuousLinearMap

/-- F3.c helper: `toRealCLM` is `DolbeaultFibre.toReal`. -/
private theorem toRealCLM_apply (β : DolbeaultFibre E q F) :
    toRealCLM β = DolbeaultFibre.toReal β := rfl

/-- F3.c helper: the exterior derivative of `α` read as a real form, in terms of `D α(x)`. -/
private theorem extDeriv_toReal_apply {α : E → DolbeaultFibre E q F} {x : E}
    (hα : DifferentiableAt ℝ α x)
    (w : Fin (q + 1) → E) :
    extDeriv (fun y => DolbeaultFibre.toReal (α y)) x w =
      ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) •
        (fderiv ℝ α x (w i)) (fun j => toConj (w (i.succAbove j))) := by
  set R : DolbeaultFibre E q F →L[ℝ] (E [⋀^Fin q]→L[ℝ] F) := toRealCLM with hR
  have hg : HasFDerivAt (𝕜 := ℝ) R R (α x) := R.hasFDerivAt
  have hd := HasFDerivAt.comp (𝕜 := ℝ) x hg hα.hasFDerivAt
  have h1 : fderiv ℝ (fun y => DolbeaultFibre.toReal (α y)) x = R ∘L fderiv ℝ α x := hd.fderiv
  rw [extDeriv, h1, alternatizeUncurryFin_apply]
  rfl

/-- F3.c helper: `I ^ |S|` as a product over slots, split at slot `i`. -/
private theorem I_pow_card_eq (i : Fin (q + 1)) (S : Finset (Fin (q + 1))) :
    (I : ℂ) ^ S.card =
      (if i ∈ S then I else 1) * ∏ j : Fin q, (if i.succAbove j ∈ S then I else 1) := by
  rw [← Fin.prod_univ_succAbove (fun j => if j ∈ S then (I : ℂ) else 1) i,
    Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- F3.c helper: sum of a function of `i ∈ S` over all subsets. -/
private theorem sum_ite_mem_finset {M : Type} [AddCommGroup M] [Module ℂ M] (i : Fin (q + 1))
    (A B : M) :
    ∑ S : Finset (Fin (q + 1)), (if i ∈ S then A else B) = (2 : ℂ) ^ q • (A + B) := by
  have hu : (Finset.univ : Finset (Fin (q + 1))) = insert i (Finset.univ.erase i) :=
    (Finset.insert_erase (Finset.mem_univ i)).symm
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert (Finset.notMem_erase i _)]
  have h1 : ∀ S ∈ (Finset.univ.erase i).powerset, (if i ∈ S then A else B) = B := by
    intro S hS
    have : i ∉ S := fun h => Finset.notMem_erase i _ (Finset.mem_powerset.1 hS h)
    simp only [this, ite_false]
  have h2 : ∀ S ∈ (Finset.univ.erase i).powerset, (if i ∈ insert i S then A else B) = A := by
    intro S _
    simp only [Finset.mem_insert, true_or, ite_true]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    Finset.card_powerset, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  simp only [Nat.add_sub_cancel, Nat.cast_ofNat, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_pow,
    smul_add, add_comm]

/-- F3.c helper: a single subset term, with the slots other than `i` normalised. -/
private theorem slot_term (L : E →L[ℝ] DolbeaultFibre E q F) (v : Fin (q + 1) → E) (i : Fin (q + 1))
    (S : Finset (Fin (q + 1))) :
    (I : ℂ) ^ S.card • (L (if i ∈ S then I • v i else v i))
        (fun j => toConj (if i.succAbove j ∈ S then I • v (i.succAbove j)
          else v (i.succAbove j))) =
      (if i ∈ S then I else 1) • (L (if i ∈ S then I • v i else v i))
        (fun j => toConj (v (i.succAbove j))) := by
  set c : Fin q → ℂ := fun j => if i.succAbove j ∈ S then I else 1 with hc
  have e1 : (fun j => toConj (if i.succAbove j ∈ S then I • v (i.succAbove j)
      else v (i.succAbove j))) = fun j => toConj (c j • v (i.succAbove j)) := by
    funext j
    by_cases h : i.succAbove j ∈ S <;> simp only [hc, h, ite_true, ite_false, one_smul]
  have e2 : (∏ j, c j) * ∏ j, conj (c j) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    by_cases h : i.succAbove j ∈ S <;>
      simp only [hc, h, ite_true, ite_false, map_one, mul_one, conj_I, mul_neg, I_mul_I, neg_neg]
  rw [e1, alt_apply_conj_smul (L _) (fun j => v (i.succAbove j)) c, I_pow_card_eq i S, smul_smul,
    mul_assoc, e2, mul_one]

/-- F3.c helper: the sum over subsets for a fixed derivative slot `i`. -/
private theorem slot_sum (L : E →L[ℝ] DolbeaultFibre E q F) (v : Fin (q + 1) → E)
    (i : Fin (q + 1)) :
    ∑ S : Finset (Fin (q + 1)), (I : ℂ) ^ S.card •
      (L ((fun j => if j ∈ S then I • v j else v j) i))
        (fun j => toConj ((fun j => if j ∈ S then I • v j else v j) (i.succAbove j))) =
      (2 : ℂ) ^ (q + 1) • (antiPart L (toConj (v i))) (fun j => toConj (v (i.succAbove j))) := by
  simp only [slot_term]
  set U : Fin q → Conj E := fun j => toConj (v (i.succAbove j)) with hU
  have h1 : ∀ S : Finset (Fin (q + 1)), (if i ∈ S then (I : ℂ) else 1) •
      (L (if i ∈ S then I • v i else v i)) U =
      if i ∈ S then I • (L (I • v i)) U else (L (v i)) U := by
    intro S
    by_cases h : i ∈ S <;> simp only [h, ite_true, ite_false, one_smul]
  rw [Finset.sum_congr rfl (fun S _ => h1 S), sum_ite_mem_finset, antiPart_apply]
  simp only [ofConj_toConj, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
    smul_add, smul_smul, pow_succ]
  module

/-- **F3.c (sanity).** `∂̄α` is the `(0, q+1)`-part of Mathlib's exterior derivative of `α` read
as a real form: projecting each slot to its antilinear part `½ (1 + i J)`,
`∂̄α(x)(v̄) = 2^{-(q+1)} Σ_{S ⊆ {0,…,q}} i^{|S|} dα(x)(J_S v)`, where `J_S` multiplies the slots
in `S` by `i`. Ties the normalization of `∂̄` to `extDeriv` (conventions §6). -/
theorem dbar_eq_extDeriv {α : E → DolbeaultFibre E q F} {x : E} (hα : DifferentiableAt ℝ α x)
    (v : Fin (q + 1) → E) :
    dbar α x (fun j => toConj (v j)) =
      ((2 : ℂ) ^ (q + 1))⁻¹ • ∑ S : Finset (Fin (q + 1)), I ^ S.card •
        extDeriv (fun y => DolbeaultFibre.toReal (α y)) x
          (fun j => if j ∈ S then I • v j else v j) := by
  simp only [extDeriv_toReal_apply hα, Finset.smul_sum]
  rw [Finset.sum_comm, dbar, dbarPart, alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := slot_sum (fderiv ℝ α x) v i
  beta_reduce at h
  simp only [smul_comm (_ : ℂ) ((-1 : ℤ) ^ (i : ℕ)), ← Finset.smul_sum, h]
  rw [smul_comm ((2 : ℂ) ^ (q + 1))⁻¹, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero),
    one_smul]
  rfl

/-! ## F4: `∂̄∂̄ = 0` -/

/-- **F4.** `∂̄∂̄ = 0`: for `α` of class `C²` near `x`, `∂̄(∂̄α)(x) = 0`. Proof as Mathlib's
`extDeriv_extDeriv_apply`, with `D″` in place of `D`: the `ℂ`-bilinear map
`(u, v) ↦ D″D″α(x)(u, v)` on `Ē` is symmetric (`ContDiffAt.isSymmSndFDerivAt` over `ℝ`), and
`alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric` concludes. -/
theorem dbar_dbar {α : E → DolbeaultFibre E q F} {x : E} (h : ContDiffAt ℝ 2 α x) :
    dbar (fun y => dbar α y) x = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ α) x :=
    (h.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hs : IsSymmSndFDerivAt ℝ α x :=
    h.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact le_rfl)
  set D2 : E →L[ℝ] E →L[ℝ] DolbeaultFibre E q F := fderiv ℝ (fderiv ℝ α) x with hD2
  set Ψ : (E →L[ℝ] DolbeaultFibre E q F) →L[ℝ] DolbeaultFibre E (q + 1) F :=
    (alternatizeUncurryFinCLM ℂ (Conj E) F).restrictScalars ℝ ∘L
      antiPartCLM E (DolbeaultFibre E q F)
    with hΨ
  have hg : HasFDerivAt (𝕜 := ℝ) Ψ Ψ (fderiv ℝ α x) := Ψ.hasFDerivAt
  have hf : HasFDerivAt (𝕜 := ℝ) (fderiv ℝ α) D2 x := hd.hasFDerivAt
  have h0 := HasFDerivAt.comp (𝕜 := ℝ) (f := fderiv ℝ α) (g := Ψ) x hg hf
  have h1' : HasFDerivAt (fun y => dbar α y) (Ψ ∘L D2) x := h0
  have h1 : fderiv ℝ (fun y => dbar α y) x = Ψ ∘L D2 := h1'.fderiv
  have h2 : dbar (fun y => dbar α y) x =
      alternatizeUncurryFin (antiPart (Ψ ∘L D2)) := by
    rw [dbar, dbarPart, h1]
  set T : (Conj E →L[ℂ] DolbeaultFibre E q F) →L[ℂ] DolbeaultFibre E (q + 1) F :=
    alternatizeUncurryFinCLM ℂ (Conj E) F
  have h3 : Ψ ∘L D2 = T.restrictScalars ℝ ∘L (antiPartCLM E (DolbeaultFibre E q F) ∘L D2) := rfl
  have h4 := antiPart_comp T (antiPartCLM E (DolbeaultFibre E q F) ∘L D2)
  rw [h2, h3, h4]
  refine alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
    (f := antiPart (antiPartCLM E (DolbeaultFibre E q F) ∘L D2)) (fun u w => ?_)
  simp only [antiPart_apply, ContinuousLinearMap.comp_apply, antiPartCLM_apply, _root_.add_apply,
    _root_.smul_apply, smul_add, smul_smul]
  have e1 := hs (ofConj u) (ofConj w)
  have e2 := hs (I • ofConj u) (ofConj w)
  have e3 := hs (ofConj u) (I • ofConj w)
  have e4 := hs (I • ofConj u) (I • ofConj w)
  rw [← hD2] at e1 e2 e3 e4
  rw [e1, e2, e3, e4]
  module

/-! ## `0`-forms (F2.a), for the checks K2 -/

/-- F3: the `0`-form `z ↦ f z` (F2.a: `Λ^{0,0}(E; F) ≅ F`). -/
def form0 (f : E → F) : E → DolbeaultFibre E 0 F := fun z => form0Equiv E F (f z)

/-- F3: on `0`-forms `∂̄` is `D″f(x)` viewed as a `1`-form. -/
theorem dbar_form0 {f : E → F} {x : E} (hf : DifferentiableAt ℝ f x) :
    dbar (form0 f) x = ofSubsingleton ℂ (Conj E) F (0 : Fin 1) (antiPart (fderiv ℝ f x)) := by
  set T : F →L[ℂ] DolbeaultFibre E 0 F := (form0Equiv E F : F →L[ℂ] DolbeaultFibre E 0 F)
  have hD : fderiv ℝ (form0 f) x = (T.restrictScalars ℝ).comp (fderiv ℝ f x) :=
    ((T.restrictScalars ℝ).hasFDerivAt.comp x hf.hasFDerivAt).fderiv
  rw [dbar, dbarPart, hD, antiPart_comp]
  exact alternatizeUncurryFin_constOfIsEmptyLIE_comp _

end Cohesive
