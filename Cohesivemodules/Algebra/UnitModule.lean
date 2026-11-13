import Cohesivemodules.Algebra.GeneratorsDef
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.StablyFree.Basic

set_option linter.style.header false

/-!
# K4.b: the unit module `𝒜`

Blueprint item K4.b (`blueprint/blueprint-tr.md` §4 (ii); §11 v1.16). For zero curvature, `𝒜`
itself is a cohesive module `U`: one generator `1` in degree `0` (`Q⁰ = A⁰`, `Qᵖ = 0` otherwise),
`𝕏 = d`. Moved here unchanged from `ChecksAlgebra.lean` (where it was the non-vacuity check of
A3–A5), with the generic helper names (`gen`, `coef`, `i₀`, …) now in the namespace `UnitMod`.

New: the identification of the total module with `A`,
* `UnitMod.coefEquiv : ⨁_p Qᵖ ≃ₗ[A⁰] A⁰`, `e ↦ coef e`, inverse `f ↦ f • gen`;
* `unitEquiv : Tot(U) ≃ₗ[A] A`, `a ⊗ e ↦ a · coef e`, under which `𝕏` is `d` (`unitEquiv_X`) and
  total degree is form degree (`unitEquiv_mem_iff`).
-/

noncomputable section

namespace Cohesive

open DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- K4.b: rank of the generators of `𝒜` in degree `p`: `1` in degree `0`, else `0`. -/
def unitRank (p : ℤ) : ℕ := if p = 0 then 1 else 0

/-- K4.b: the generators of `𝒜` itself: `A⁰` in degree `0`, zero elsewhere. -/
abbrev UnitQ (p : ℤ) : Type := Fin (unitRank p) → 𝒜 0

/-- K4.b: the generator rank in degree `0` is `1`. -/
theorem unitRank_zero : unitRank 0 = 1 := rfl

namespace UnitMod

/-- K4.b: the index of the generator. -/
def i₀ : Fin (unitRank 0) := ⟨0, by simp [unitRank]⟩

/-- K4.b: the index set in degree `0` has one element. -/
instance : Subsingleton (Fin (unitRank 0)) := by rw [unitRank_zero]; infer_instance

/-- K4.b: the index set outside degree `0` is empty. -/
theorem isEmpty_of_ne {p : ℤ} (h : p ≠ 0) : IsEmpty (Fin (unitRank p)) := by
  rw [unitRank, ite_eq_right_iff.2 (fun h' => absurd h' h)]; infer_instance

/-- K4.b: the generator `1` in degree `0`. -/
def gen : ⨁ p, UnitQ 𝒜 p := lof (𝒜 0) ℤ (UnitQ 𝒜) 0 (fun _ => 1)

/-- K4.b: the coefficient of an element on the generator. -/
def coef : (⨁ p, UnitQ 𝒜 p) →ₗ[𝒜 0] 𝒜 0 :=
  (LinearMap.proj (R := 𝒜 0) (φ := fun _ : Fin (unitRank 0) => 𝒜 0) i₀).comp
    (component (𝒜 0) ℤ (UnitQ 𝒜) 0)

omit [GCDga 𝒜] in
/-- K4.b: formula for `coef`. -/
theorem coef_apply (e : ⨁ p, UnitQ 𝒜 p) : coef 𝒜 e = e 0 i₀ := rfl

omit [GCDga 𝒜] in
/-- K4.b: every element is a multiple of the generator. -/
theorem eq_coef_smul_gen (e : ⨁ p, UnitQ 𝒜 p) : e = coef 𝒜 e • gen 𝒜 := by
  ext p i
  by_cases hp : p = 0
  · subst hp
    rw [Subsingleton.elim i i₀]
    simp [gen, coef_apply, DirectSum.smul_apply, DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · have := isEmpty_of_ne hp
    exact isEmptyElim i

omit [GCDga 𝒜] in
/-- K4.b: the generator has coefficient `1`. -/
theorem coef_gen : coef 𝒜 (gen 𝒜) = 1 := by
  simp [coef_apply, gen, DirectSum.lof_eq_of, DirectSum.of_eq_same]

/-- K4.b: `⨁_p Qᵖ ≃ₗ[A⁰] A⁰`, `e ↦ coef e`, inverse `f ↦ f • gen`. -/
def coefEquiv : (⨁ p, UnitQ 𝒜 p) ≃ₗ[𝒜 0] 𝒜 0 :=
  LinearEquiv.ofLinear (coef 𝒜) (LinearMap.toSpanSingleton (𝒜 0) _ (gen 𝒜))
    (LinearMap.ext fun f => by
      simp [LinearMap.toSpanSingleton_apply, map_smul, coef_gen])
    (LinearMap.ext fun e => (eq_coef_smul_gen 𝒜 e).symm)

/-- K4.b: `coefEquiv` is `coef` (rfl). -/
theorem coefEquiv_apply (e : ⨁ p, UnitQ 𝒜 p) : coefEquiv 𝒜 e = coef 𝒜 e := rfl

end UnitMod

open UnitMod

/-- K4.b: generator data `θ(e) = d(coef e) ⊗ 1`. -/
def unitGenData : GenData 𝒜 (UnitQ 𝒜) where
  θ := AddMonoidHom.mk' (fun e => Tot.tmul 𝒜 _ (GCDga.d (𝒜 := 𝒜) (coef 𝒜 e)) (gen 𝒜))
    (fun e e' => by rw [map_add, Submodule.coe_add, map_add, Tot.add_tmul])
  leibniz f e := by
    rw [AddMonoidHom.mk'_apply, map_smul, smul_eq_mul,
      show ((f * coef 𝒜 e : 𝒜 0) : A) = (f : A) * coef 𝒜 e from rfl,
      GCDga.leibniz_zero 𝒜 f.2, Tot.add_tmul, ← Tot.tmul_smul0, ← eq_coef_smul_gen,
      Tot.smul_tmul]

/-- K4.b: formula for `θ`. -/
theorem unitGenData_θ (e : ⨁ p, UnitQ 𝒜 p) : (unitGenData 𝒜).θ e =
    Tot.tmul 𝒜 _ (GCDga.d (𝒜 := 𝒜) (coef 𝒜 e)) (gen 𝒜) := rfl

/-- K4.b: `θ` has total degree `1` on the generators. -/
theorem unitGenData_mem (p : ℤ) (e : UnitQ 𝒜 p) :
    (unitGenData 𝒜).θ (lof (𝒜 0) ℤ (UnitQ 𝒜) p e) ∈ totDeg 𝒜 (UnitQ 𝒜) (p + 1) := by
  by_cases hp : p = 0
  · subst hp
    have := tmul_mem_totDeg (Q := UnitQ 𝒜) (GCDga.d_mem_one 𝒜 (coef 𝒜 (lof (𝒜 0) ℤ _ 0 e)).2)
      (fun _ => 1 : UnitQ 𝒜 0)
    simpa [unitGenData_θ, gen, add_comm] using this
  · have : e = 0 := by
      have := isEmpty_of_ne hp
      exact Subsingleton.elim _ _
    simp [this]

/-- K4.b: with zero curvature, `θ` is flat on the generators. -/
theorem unitGenData_flat (hc : GCDga.c (𝒜 := 𝒜) = 0) (e : ⨁ p, UnitQ 𝒜 p) :
    (unitGenData 𝒜).extend ((unitGenData 𝒜).θ e) =
      GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 _ 1 e := by
  rw [unitGenData_θ, GenData.extend_tmul, GCDga.d_d, Tot.zero_tmul, zero_add, unitGenData_θ,
    coef_gen, show ((1 : 𝒜 0) : A) = 1 from rfl, GCDga.d_one, Tot.zero_tmul, smul_zero, hc,
    zero_smul]

/-- **K4.b (blueprint §9: non-vacuity of A3–A5).** For zero curvature, `𝒜` itself is a cohesive
module `U`: one generator in degree `0`, `𝕏 = d`. Built with the A3.a constructor. -/
def unitCohesive (hc : GCDga.c (𝒜 := 𝒜) = 0) : CohesiveModule 𝒜 where
  toQuasiCohesive := QuasiCohesive.ofGenerators (UnitQ 𝒜) (unitGenData 𝒜)
    (unitGenData_mem 𝒜) (unitGenData_flat 𝒜 hc)
  bounded := ⟨0, 0, fun p hp => by
    have := isEmpty_of_ne (show p ≠ 0 by omega)
    show Subsingleton (Fin (unitRank p) → 𝒜 0)
    infer_instance⟩
  finite _ := inferInstanceAs (Module.Finite (𝒜 0) (Fin _ → 𝒜 0))
  projective _ := inferInstanceAs (Module.Projective (𝒜 0) (Fin _ → 𝒜 0))

/-- K4.b: the generators of `unitCohesive` are `UnitQ` (rfl). -/
theorem unitCohesive_Q (hc : GCDga.c (𝒜 := 𝒜) = 0) : (unitCohesive 𝒜 hc).Q = UnitQ 𝒜 := rfl

/-- K4.b: the operator of `unitCohesive` is the extension of `unitGenData` (rfl). -/
theorem unitCohesive_X (hc : GCDga.c (𝒜 := 𝒜) = 0) :
    (unitCohesive 𝒜 hc).X = (unitGenData 𝒜).extend := rfl

/-! ## The total module of `U` is `A` -/

/-- **K4.b.** `Tot(U) ≃ₗ[A] A`, `a ⊗ e ↦ a · coef e`: the total module of the unit module is
`A`, as a left `A`-module. -/
def unitEquiv : Tot 𝒜 (UnitQ 𝒜) ≃ₗ[A] A :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) (coefEquiv 𝒜)).trans
    (TensorProduct.AlgebraTensorModule.rid (𝒜 0) A A)

/-- K4.b: `unitEquiv (a ⊗ e) = a · coef e`. -/
theorem unitEquiv_tmul (a : A) (e : ⨁ p, UnitQ 𝒜 p) :
    unitEquiv 𝒜 (Tot.tmul 𝒜 _ a e) = a * (coef 𝒜 e : A) :=
  (GCDga.smul0_def 𝒜 _ a).trans (GCDga.central 𝒜 (coef 𝒜 e).2 a)

/-- K4.b: `unitEquiv⁻¹ a = a ⊗ gen`. -/
theorem unitEquiv_symm_apply (a : A) :
    (unitEquiv 𝒜).symm a = Tot.tmul 𝒜 _ a (gen 𝒜) := by
  rw [LinearEquiv.symm_apply_eq, unitEquiv_tmul, coef_gen]; exact (mul_one a).symm

/-- K4.b: `unitEquiv` is `k`-linear. -/
theorem unitEquiv_smul_k (r : k) (x : Tot 𝒜 (UnitQ 𝒜)) :
    unitEquiv 𝒜 (r • x) = r • unitEquiv 𝒜 x :=
  LinearMap.map_smul_of_tower (unitEquiv 𝒜).toLinearMap r x

/-- Leibniz rule for non-homogeneous `a`: `d (a b) = d a · b + σ(a) · d b`. -/
private theorem d_mul_general (a b : A) :
    GCDga.d (𝒜 := 𝒜) (a * b) =
      GCDga.d (𝒜 := 𝒜) a * b + GCDga.sigma 𝒜 a * GCDga.d (𝒜 := 𝒜) b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; abel
  | homogeneous x =>
    rw [GCDga.leibniz x.2, GCDga.sigma_of_mem 𝒜 x.2, smul_mul_assoc]

/-- The operator `extend` of `unitGenData` is `d` under `unitEquiv`. -/
private theorem unitEquiv_extend (x : Tot 𝒜 (UnitQ 𝒜)) :
    unitEquiv 𝒜 ((unitGenData 𝒜).extend x) = GCDga.d (𝒜 := 𝒜) (unitEquiv 𝒜 x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [GenData.extend_tmul, map_add, unitEquiv_tmul, unitGenData_θ,
      map_smul, unitEquiv_tmul, unitEquiv_tmul, d_mul_general, smul_eq_mul, coef_gen]
    rw [show ((1 : 𝒜 0) : A) = 1 from rfl, mul_one]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **K4.b.** Under `unitEquiv`, the operator `𝕏` of `U` is `d`. -/
theorem unitEquiv_X (hc : GCDga.c (𝒜 := 𝒜) = 0) (x : Tot 𝒜 (UnitQ 𝒜)) :
    unitEquiv 𝒜 ((unitCohesive 𝒜 hc).X x) = GCDga.d (𝒜 := 𝒜) (unitEquiv 𝒜 x) :=
  unitEquiv_extend 𝒜 x

/-- **K4.b.** Under `unitEquiv`, total degree `m` is form degree `m`. -/
theorem unitEquiv_mem_iff (m : ℤ) (x : Tot 𝒜 (UnitQ 𝒜)) :
    x ∈ totDeg 𝒜 (UnitQ 𝒜) m ↔ unitEquiv 𝒜 x ∈ 𝒜 m := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, p, a, e, hqp, ha, rfl⟩ := hx
      by_cases hp : p = 0
      · subst hp
        have : m = q := by omega
        subst this
        change unitEquiv 𝒜 (Tot.tmul 𝒜 _ a _) ∈ _
        rw [unitEquiv_tmul]
        have := SetLike.GradedMul.mul_mem ha (coef 𝒜 (lof (𝒜 0) ℤ (UnitQ 𝒜) 0 e)).2
        rwa [add_zero] at this
      · have := isEmpty_of_ne hp
        have he : e = 0 := Subsingleton.elim _ _
        subst he
        simp only [map_zero]
        change unitEquiv 𝒜 (Tot.tmul 𝒜 _ a 0) ∈ _
        rw [Tot.tmul_zero, map_zero]
        exact zero_mem _
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [unitEquiv_smul_k]; exact (𝒜 m).smul_mem r hx
  · intro hx
    rw [← (unitEquiv 𝒜).symm_apply_apply x, unitEquiv_symm_apply]
    have := tmul_mem_totDeg (Q := UnitQ 𝒜) hx (fun _ => 1 : UnitQ 𝒜 0)
    rwa [add_zero] at this

end Cohesive
