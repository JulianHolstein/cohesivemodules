import Cohesivemodules.Forms.Dbar
import Cohesivemodules.Forms.Product

set_option linter.style.header false

/-!
# F6: the Leibniz rule for `∂̄`

Blueprint item F6 (conventions §6). `∂̄(α ∧ β) = ∂̄α ∧ β + (-1)^p α ∧ ∂̄β` for a `p`-form `α` and a
`q`-form `β`. Stated in the total fibre (`TotFibre.ofDeg`), so the three terms, of degrees
`p + q + 1`, `(p + 1) + q`, `p + (q + 1)`, need no casts.

Proof plan (blueprint): (i) `∂̄(f·η) = ∂̄f ∧ η + f·∂̄η` for a function `f`, by the product rule and
the Laplace formula F5.a; (ii) constant forms are `∂̄`-closed; (iii) locally every form is
`Σ_I f_I dz̄_I` (F2.c); expand and use graded commutativity.

A split of blueprint §7's `Product.lean (F5–F6)` (size only).
-/

noncomputable section

namespace Cohesive

open TotFibre
open ContinuousAlternatingMap (alternatizeUncurryFin alternatizeUncurryFin_add ofSubsingletonLIE)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {p q : ℕ}

/-- **F6.** The wedge product of a `p`-form and a `q`-form at a point, as a `(p+q)`-form: the
degree-`(p+q)` component of the product in the total fibre (F5). -/
def wedge (α : DolbeaultFibre E p ℂ) (β : DolbeaultFibre E q ℂ) : DolbeaultFibre E (p + q) ℂ :=
  deg (p + q) (ofDeg p α * ofDeg q β : TotFibre E)

/-- F6: `ofDeg` of the wedge is the product in the total fibre (`ofDeg_mul_ofDeg`). -/
theorem ofDeg_wedge (α : DolbeaultFibre E p ℂ) (β : DolbeaultFibre E q ℂ) :
    (ofDeg (p + q) (wedge α β) : TotFibre E) = ofDeg p α * ofDeg q β :=
  (ofDeg_mul_ofDeg α β).symm

/-- F6 helper: the wedge product as a `ℂ`-bilinear map. -/
private def wedgeL (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (p q : ℕ) : DolbeaultFibre E p ℂ →ₗ[ℂ] DolbeaultFibre E q ℂ →ₗ[ℂ] DolbeaultFibre E (p + q) ℂ :=
  LinearMap.mk₂ ℂ wedge
    (fun a a' b => by simp only [wedge, map_add, add_mul])
    (fun c a b => by simp only [wedge, map_smul, smul_mul_assoc])
    (fun a b b' => by simp only [wedge, map_add, mul_add])
    (fun c a b => by simp only [wedge, map_smul, mul_smul_comm])

/-- F6 helper: the wedge product as a continuous `ℂ`-bilinear map (finite dimension). -/
private def wedgeCLM (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (p q : ℕ) : DolbeaultFibre E p ℂ →L[ℂ] DolbeaultFibre E q ℂ →L[ℂ] DolbeaultFibre E (p + q) ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := DolbeaultFibre E q ℂ)
      (F' := DolbeaultFibre E (p + q) ℂ)).toLinearMap
      ∘ₗ wedgeL E p q)

private theorem wedgeCLM_apply (a : DolbeaultFibre E p ℂ) (b : DolbeaultFibre E q ℂ) :
    wedgeCLM E p q a b = wedge a b :=
  rfl

/-- F6: the wedge of real-`C^n` forms is real `C^n` (the product is a continuous bilinear map,
`mulCLM`). -/
theorem contDiffOn_wedge {α : E → DolbeaultFibre E p ℂ} {β : E → DolbeaultFibre E q ℂ} {U : Set E}
    {n : WithTop ℕ∞} (hα : ContDiffOn ℝ n α U) (hβ : ContDiffOn ℝ n β U) :
    ContDiffOn ℝ n (fun y => wedge (α y) (β y)) U := by
  let B : DolbeaultFibre E p ℂ →L[ℝ] DolbeaultFibre E q ℂ →L[ℝ] DolbeaultFibre E (p + q) ℂ :=
    (ContinuousLinearMap.restrictScalarsL ℂ (DolbeaultFibre E q ℂ)
      (DolbeaultFibre E (p + q) ℂ) ℝ ℝ).comp
      ((wedgeCLM E p q).restrictScalars ℝ)
  exact (B.isBoundedBilinearMap.contDiff.comp_contDiffOn (hα.prodMk hβ) :)

/-- F6 helper: the product rule for the real derivative of `y ↦ α y ∧ β y`. -/
private theorem fderiv_wedge {α : E → DolbeaultFibre E p ℂ} {β : E → DolbeaultFibre E q ℂ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    fderiv ℝ (fun y => wedge (α y) (β y)) x =
      ((wedgeCLM E p q (α x)).restrictScalars ℝ).comp (fderiv ℝ β x) +
        (((wedgeCLM E p q).flip (β x)).restrictScalars ℝ).comp (fderiv ℝ α x) := by
  let B : DolbeaultFibre E p ℂ →L[ℝ] DolbeaultFibre E q ℂ →L[ℝ] DolbeaultFibre E (p + q) ℂ :=
    (ContinuousLinearMap.restrictScalarsL ℂ (DolbeaultFibre E q ℂ)
      (DolbeaultFibre E (p + q) ℂ) ℝ ℝ).comp
      ((wedgeCLM E p q).restrictScalars ℝ)
  have h := (B.isBoundedBilinearMap.hasFDerivAt (α x, β x)).comp x
    (hα.hasFDerivAt.prodMk hβ.hasFDerivAt)
  have h' : HasFDerivAt (fun y => wedge (α y) (β y)) _ x := h
  rw [h'.fderiv]
  ext v
  simp only [IsBoundedBilinearMap.deriv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_restrict_scalarsL',
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_deriv₂,
    IsBoundedBilinearMap.toContinuousLinearMap_apply, ContinuousAlternatingMap.add_apply,
    add_apply, ContinuousLinearMap.flip_apply, B]

/-- F6 helper: induction principle for linear maps out of `Ē`: sums of `φ.smulRight f`. -/
private theorem clm_induction {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (P : (Conj E →L[ℂ] F) → Prop) (h0 : P 0) (hadd : ∀ A A', P A → P A' → P (A + A'))
    (hbasic : ∀ (φ : Conj E →L[ℂ] ℂ) (f : F), P (φ.smulRight f)) (A : Conj E →L[ℂ] F) :
    P A := by
  let b := Module.finBasis ℂ (Conj E)
  have hA : A = ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (A (b i)) := by
    ext v
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply]
  rw [hA]
  exact Finset.sum_induction _ P hadd h0 (fun i _ => hbasic _ _)

omit [FiniteDimensional ℂ E] in
/-- F6 helper: `alternatizeUncurryFin 0 = 0`. -/
private theorem alt_zero {r : ℕ} :
    alternatizeUncurryFin (0 : Conj E →L[ℂ] DolbeaultFibre E r ℂ) = 0 :=
  map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℂ (Conj E) ℂ)

/-- F6 helper (I):`∂̄`-type algebra, the wedge with a fixed `q`-form on the right. -/
private theorem alt_wedge_right (A : Conj E →L[ℂ] DolbeaultFibre E p ℂ) (b : DolbeaultFibre E q ℂ) :
    (ofDeg (p + q + 1) (alternatizeUncurryFin ((wedgeCLM E p q).flip b ∘L A)) : TotFibre E) =
      ofDeg (p + 1) (alternatizeUncurryFin A) * ofDeg q b := by
  refine clm_induction (fun A => (ofDeg (p + q + 1)
    (alternatizeUncurryFin ((wedgeCLM E p q).flip b ∘L A)) : TotFibre E) =
      ofDeg (p + 1) (alternatizeUncurryFin A) * ofDeg q b) ?_ ?_ ?_ A
  · simp only [ContinuousLinearMap.comp_zero, alt_zero, map_zero, zero_mul]
  · intro A A' h h'
    simp only [ContinuousLinearMap.comp_add, alternatizeUncurryFin_add, map_add, add_mul, h, h']
  · intro φ a'
    have key : (wedgeCLM E p q).flip b ∘L (φ.smulRight a') = φ.smulRight (wedge a' b) := by
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.flip_apply, map_smul, wedgeCLM_apply]
    have hφ : (ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1)).symm
        ((ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1)) φ) = φ :=
      LinearIsometryEquiv.symm_apply_apply _ _
    rw [key]
    have h1 := ofDeg_one_mul (ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1) φ)
      (wedge a' b)
    have h2 := ofDeg_one_mul (ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1) φ) a'
    rw [hφ] at h1 h2
    rw [← h1, ← h2, ofDeg_wedge, mul_assoc]

/-- F6 helper (II): the wedge with a fixed `p`-form on the left, with the Koszul sign. -/
private theorem alt_wedge_left (a : DolbeaultFibre E p ℂ) (B : Conj E →L[ℂ] DolbeaultFibre E q ℂ) :
    (ofDeg (p + q + 1) (alternatizeUncurryFin (wedgeCLM E p q a ∘L B)) : TotFibre E) =
      (-1 : ℂ) ^ p • (ofDeg p a * ofDeg (q + 1) (alternatizeUncurryFin B)) := by
  refine clm_induction (fun B => (ofDeg (p + q + 1)
    (alternatizeUncurryFin (wedgeCLM E p q a ∘L B)) : TotFibre E) =
      (-1 : ℂ) ^ p • (ofDeg p a * ofDeg (q + 1) (alternatizeUncurryFin B))) ?_ ?_ ?_ B
  · simp only [ContinuousLinearMap.comp_zero, alt_zero, map_zero, mul_zero, smul_zero]
  · intro A A' h h'
    simp only [ContinuousLinearMap.comp_add, alternatizeUncurryFin_add, map_add, mul_add,
      smul_add, h, h']
  · intro φ b'
    have key : wedgeCLM E p q a ∘L (φ.smulRight b') = φ.smulRight (wedge a b') := by
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
        map_smul, wedgeCLM_apply]
    have hφ : (ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1)).symm
        ((ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1)) φ) = φ :=
      LinearIsometryEquiv.symm_apply_apply _ _
    rw [key]
    have h1 := ofDeg_one_mul (ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1) φ)
      (wedge a b')
    have h2 := ofDeg_one_mul (ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1) φ) b'
    rw [hφ] at h1 h2
    rw [← h1, ← h2, ofDeg_wedge]
    generalize (ofSubsingletonLIE (𝕜 := ℂ) (E := Conj E) (F := ℂ) (0 : Fin 1) φ) = φ'
    rw [← mul_assoc (ofDeg p a), ofDeg_mul_comm a φ', smul_mul_assoc, mul_assoc,
      smul_smul, ← pow_add, mul_one, ← two_mul, pow_mul]
    simp only [neg_one_sq, one_pow, one_smul]

/-- **F6 (Leibniz rule).** For a `p`-form `α` and a `q`-form `β`, real-differentiable at `x`,
`∂̄(α ∧ β)(x) = ∂̄α(x) ∧ β(x) + (-1)^p α(x) ∧ ∂̄β(x)`, in the total fibre. [B, §4.1] (the
Dolbeault algebra is a dga); conventions §6 (normalizations of `∂̄` and `∧` agree). -/
theorem dbar_wedge {α : E → DolbeaultFibre E p ℂ} {β : E → DolbeaultFibre E q ℂ} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    (ofDeg (p + q + 1) (dbar (fun y => wedge (α y) (β y)) x) : TotFibre E) =
      ofDeg (p + 1) (dbar α x) * ofDeg q (β x) +
        (-1 : ℂ) ^ p • (ofDeg p (α x) * ofDeg (q + 1) (dbar β x)) := by
  have h : dbar (fun y => wedge (α y) (β y)) x =
      alternatizeUncurryFin (wedgeCLM E p q (α x) ∘L dbarPart β x) +
        alternatizeUncurryFin ((wedgeCLM E p q).flip (β x) ∘L dbarPart α x) := by
    rw [dbar, dbarPart, fderiv_wedge hα hβ, antiPart_add, antiPart_comp, antiPart_comp,
      alternatizeUncurryFin_add]
    rfl
  rw [h, map_add, alt_wedge_left, alt_wedge_right, add_comm]
  rfl

end Cohesive
