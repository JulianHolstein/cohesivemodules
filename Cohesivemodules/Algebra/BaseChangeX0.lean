import Cohesivemodules.Algebra.BaseChange
import Cohesivemodules.Algebra.LiftingCone

set_option linter.style.header false

/-!
# A9/A11: the degree-`0` operator `𝕏⁰` of a base change

Blueprint items A9 and A11 (used by C5 and C7.f). For a map of (possibly curved) dgas
`f : 𝒜 → ℬ` and a quasi-cohesive
`𝒜`-module `M`, the operator `𝕏⁰` of the base change `f^*M` on the generators
`⨁_p ℬ⁰ ⊗_{𝒜⁰} Q^p`: `𝕏⁰(ι e) = ι(𝕏⁰ e)` and `𝕏⁰(β ⊗ q) = β ⊗ 𝕏⁰ q`. Shared by
`Comparison/ModelFil.lean`, `Comparison/EssSurjCore.lean` and `Comparison/PerfectModel.lean`
(formerly copied between them). Not part of the statement.
-/

noncomputable section

namespace Cohesive

open DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  (f : DgaHom 𝒜 ℬ)

/-- A9: `ε ∘ F = ι ∘ ε` for the comparison `F : Tot 𝒜 Q → Tot ℬ (BCGen f Q)`. -/
theorem eps_bcF (M : QuasiCohesive 𝒜) (x : Tot 𝒜 M.Q) :
    Tot.eps ℬ (BCGen f M.Q) (bcF f M.Q x) = bcι f M.Q (Tot.eps 𝒜 M.Q x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul, Tot.eps_tmul, Tot.eps_tmul, bcι_smul]
    exact congrArg (· • bcι f M.Q e) (Subtype.ext (f.map_proj 0 a).symm)
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- A9: `1 ⊗ (1 ⊗ q) = F(1 ⊗ q)` in the base change. -/
theorem tmul_one_lof_eq_bcF (M : QuasiCohesive 𝒜) (p : ℤ) (q : M.Q p) :
    Tot.tmul ℬ (BCGen f M.Q) 1 (lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q)) =
      bcF f M.Q (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q)) := by
  rw [bcF_tmul, DgaHom.map_one', bcι_lof]

/-- A11: `𝕏⁰` of the base change `f^*M`, typed on the generators `⨁ BCGen f M.Q`. -/
def bcX0 (M : QuasiCohesive 𝒜) :
    (⨁ p, BCGen f M.Q p) →ₗ[ℬ 0] (⨁ p, BCGen f M.Q p) := (M.baseChange f).X0

/-- A11: `𝕏⁰` of the base change on `ι e` is `ι (𝕏⁰ e)`. -/
theorem X0_bc_bcι (M : QuasiCohesive 𝒜) (e : ⨁ p, M.Q p) :
    bcX0 f M (bcι f M.Q e) = bcι f M.Q (M.X0 e) := by
  show Tot.eps ℬ (BCGen f M.Q) ((bcGenData f M).extend (Tot.oneTmul ℬ _ (bcι f M.Q e))) = _
  rw [Tot.oneTmul_apply, GenData.extend_tmul_one, bcGenData_θ, bcθ_bcι, eps_bcF]
  show _ = bcι f M.Q (Tot.eps 𝒜 M.Q (M.X (Tot.oneTmul 𝒜 M.Q e)))
  rw [Tot.oneTmul_apply]

/-- A11: the component `𝕏⁰ : B⁰ ⊗ Q^p → B⁰ ⊗ Q^{p+1}` of the base change, typed on `BCGen`. -/
def bcX0comp (M : QuasiCohesive 𝒜) (p : ℤ) :
    BCGen f M.Q p →ₗ[ℬ 0] BCGen f M.Q (p + 1) := (M.baseChange f).X0comp p

/-- A11: `𝕏⁰ ∘ 𝕏⁰ = 0` on the generators of the base change (`complex0`). -/
theorem bcX0comp_bcX0comp (M : QuasiCohesive 𝒜) (p : ℤ) (z : BCGen f M.Q p) :
    bcX0comp f M (p + 1) (bcX0comp f M p z) = 0 := by
  have h : ((M.baseChange f).complex0.d (p + 1) (p + 1 + 1)).hom
      (((M.baseChange f).complex0.d p (p + 1)).hom z) = 0 :=
    congrArg (fun φ => φ.hom z)
      (HomologicalComplex.d_comp_d (M.baseChange f).complex0 p (p + 1) (p + 1 + 1))
  exact ((M.baseChange f).complex0_d (p + 1) _).symm.trans
    ((congrArg _ ((M.baseChange f).complex0_d p z).symm).trans h)

/-- A11: `𝕏⁰` of the base change on a pure tensor of generators: `𝕏⁰(β ⊗ q) = β ⊗ 𝕏⁰ q`. -/
theorem X0comp_bc_tmul (M : QuasiCohesive 𝒜) (p : ℤ) (β : ℬ 0) (q : M.Q p) :
    bcX0comp f M p (BCGen.tmul f M.Q β q) =
      BCGen.tmul f M.Q β (M.X0comp p q) := by
  have hx : lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q β q) =
      β • bcι f M.Q (lof (𝒜 0) ℤ M.Q p q) := by
    rw [bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul]
  show DirectSum.component (ℬ 0) ℤ (BCGen f M.Q) (p + 1)
    (bcX0 f M (lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q β q))) = _
  rw [hx, map_smul, X0_bc_bcι, M.X0_lof, bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul,
    DirectSum.component.lof_self]

end Cohesive
