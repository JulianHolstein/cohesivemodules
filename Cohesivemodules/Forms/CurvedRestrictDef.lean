import Cohesivemodules.Algebra.Gauge
import Cohesivemodules.Comparison.TwistDatumDef

set_option linter.style.header false

/-!
# Z3.e: curved restriction and the gauged restriction `gauge_{h⁰_α}(M|U_α)`

Blueprint item Z3.e (`blueprint/blueprint-tw.md` §3 D.6, E.1; blueprint §11 v1.19, audit a14).
* `curvedInstU h U`: the curved instance on `𝒜_X(U)` with curvature `h|U`, spelled as
  `withC` of the flat Dolbeault instance;
* `curvedRes h U : (𝒜_X(X), h) → (𝒜_X(U), h|U)`, the restriction as a curved dga map (A9);
* `curvedRestrict h U M = M|U` (A9 base change);
* `gaugedRestrict h T α M = gauge_{h⁰_α}(M|U_α)`, a cohesive module over the flat `𝒜_X(U_α)`
  (Z3.b, `d h⁰_α = h|U_α`).

## Lean notes
`curvedRes` is built with `@DgaHom.mk` and all instances explicit, with every `le_top` ascribed
(`(le_top : U ≤ ⊤)`): the restriction of `curvedDolbeaultPresheaf h` ascribed to `curvedInstU`
times out in `isDefEq` (prototype P18). The curvature of `curvedInstU h U` is
`dolbeaultRes E le_top h.1`, which is `(curvedDolbeaultPresheaf h).dga U`'s curvature as a term.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- Z3.e: `h|U` has degree `2`. -/
theorem dolbeaultRes_closed2_mem (h : DolbeaultClosed2 E X) (U : Opens X) :
    dolbeaultRes E (le_top : U ≤ ⊤) h.1 ∈ dolbeaultGrade E U 2 :=
  (dolbeaultRes E (le_top : U ≤ ⊤)).map_mem h.2.1

/-- Z3.e: `h|U` is `∂̄`-closed. -/
theorem dbar_dolbeaultRes_closed2 (h : DolbeaultClosed2 E X) (U : Opens X) :
    GCDga.d (𝒜 := dolbeaultGrade E U) (dolbeaultRes E (le_top : U ≤ ⊤) h.1) = 0 := by
  rw [← (dolbeaultRes E (le_top : U ≤ ⊤)).map_d]
  exact (congrArg _ h.2.2).trans (map_zero _)

/-- **Z3.e.** [A, §7.4]. The curved Dolbeault algebra `(𝒜_X(U), ∂̄, h|U)` over an open `U`: the
flat instance on `dolbeaultGrade E U` with curvature replaced by `h|U` (`GCDga.withC`). -/
abbrev curvedInstU (h : DolbeaultClosed2 E X) (U : Opens X) : GCDga (dolbeaultGrade E U) :=
  (inferInstance : GCDga (dolbeaultGrade E U)).withC (dolbeaultRes E (le_top : U ≤ ⊤) h.1)
    (dolbeaultRes_closed2_mem h U) (dbar_dolbeaultRes_closed2 h U)

/-- Z3.e: restriction preserves degrees (field of `curvedRes`). -/
theorem curvedRes_map_mem (h : DolbeaultClosed2 E X) (U : Opens X) {q : ℤ}
    {a : DolbeaultAlg E (⊤ : Opens X)} (ha : a ∈ curvedDolbeault h q) :
    dolbeaultRes E (le_top : U ≤ ⊤) a ∈ dolbeaultGrade E U q :=
  (dolbeaultRes E (le_top : U ≤ ⊤)).map_mem ha

/-- Z3.e: restriction commutes with `∂̄` (field of `curvedRes`). -/
theorem curvedRes_map_d (h : DolbeaultClosed2 E X) (U : Opens X)
    (a : DolbeaultAlg E (⊤ : Opens X)) :
    dolbeaultRes E (le_top : U ≤ ⊤) (GCDga.d (𝒜 := curvedDolbeault h) a) =
      GCDga.d (𝒜 := dolbeaultGrade E U) (dolbeaultRes E (le_top : U ≤ ⊤) a) :=
  (dolbeaultRes E (le_top : U ≤ ⊤)).map_d a

/-- Z3.e: restriction maps the curvature `h` to `h|U` (field of `curvedRes`). -/
theorem curvedRes_map_c (h : DolbeaultClosed2 E X) (U : Opens X) :
    dolbeaultRes E (le_top : U ≤ ⊤) (GCDga.c (𝒜 := curvedDolbeault h)) =
      dolbeaultRes E (le_top : U ≤ ⊤) h.1 :=
  congrArg _ (curvedDolbeault_c E X h)

/-- **Z3.e.** [A, §7.2], [B, §2.7]. Restriction `(𝒜_X(X), ∂̄, h) → (𝒜_X(U), ∂̄, h|U)` as a map of
curved dgas (A9 `DgaHom`): the underlying map is `dolbeaultRes E le_top`. -/
def curvedRes (h : DolbeaultClosed2 E X) (U : Opens X) :
    @DgaHom ℂ _ _ _ _ (curvedDolbeault h) _ _ (DolbeaultAlg E U) _ _ (dolbeaultGrade E U) _
      (curvedInstU h U) :=
  @DgaHom.mk ℂ _ _ _ _ (curvedDolbeault h) _ _ (DolbeaultAlg E U) _ _ (dolbeaultGrade E U) _
    (curvedInstU h U) (dolbeaultRes E (le_top : U ≤ ⊤)).toAlgHom
    (curvedRes_map_mem h U) (curvedRes_map_d h U) (curvedRes_map_c h U)

/-- Z3.e: the underlying map of `curvedRes` is the restriction (rfl). -/
theorem curvedRes_apply (h : DolbeaultClosed2 E X) (U : Opens X)
    (a : DolbeaultAlg E (⊤ : Opens X)) :
    @DgaHom.toAlgHom ℂ _ _ _ _ (curvedDolbeault h) _ _ (DolbeaultAlg E U) _ _ (dolbeaultGrade E U)
      _ (curvedInstU h U) (curvedRes h U) a = dolbeaultRes E (le_top : U ≤ ⊤) a := rfl

/-- **Z3.e.** [A, §7.4], [B, §2.7]. The restriction `M|U` of a cohesive module over the curved
Dolbeault algebra `(𝒜_X(X), h)`: the base change (A9) along `curvedRes h U`, a cohesive module over
`(𝒜_X(U), h|U)`. -/
def curvedRestrict (h : DolbeaultClosed2 E X) (U : Opens X)
    (M : CohesiveModule (curvedDolbeault h)) :
    @CohesiveModule ℂ _ _ _ _ (dolbeaultGrade E U) _ (curvedInstU h U) :=
  @CohesiveModule.baseChange ℂ _ _ _ _ (curvedDolbeault h) _ _ (DolbeaultAlg E U) _ _
    (dolbeaultGrade E U) _ (curvedInstU h U) (curvedRes h U) M

variable [T2Space X] [CompactSpace X]

/-- Z3.e: `h|U_α = c + ∂̄ h⁰_α` for the flat instance (`c = 0`, field `d_h0` of the datum). -/
theorem twistData_hcβ (h : DolbeaultClosed2 E X) (T : TwistData E X h) (α : T.ι) :
    dolbeaultRes E (le_top : T.U α ≤ ⊤) h.1 =
      GCDga.c (𝒜 := dolbeaultGrade E (T.U α)) +
        GCDga.d (𝒜 := dolbeaultGrade E (T.U α)) (T.h0 α) :=
  (T.d_h0 α).symm.trans (zero_add _).symm

/-- **Z3.e.** [A, §7.2 proofs of Lemma 7.2.17 and Prop 7.2.19], blueprint-tw D.6/E.1
(audit a14). For a twist datum `T` of `h` and an index `α`, the gauged restriction `gauge_{h⁰_α}(M|U_α)`: the restriction of `M`
to `U_α` (curvature `h|U_α = ∂̄ h⁰_α`) with operator `𝕏 − h⁰_α·`, a cohesive module over the flat
Dolbeault algebra `𝒜_X(U_α)` (Z3.b with `β = h⁰_α`, `c = 0`, `2` invertible in `ℂ`). -/
def gaugedRestrict (h : DolbeaultClosed2 E X) (T : TwistData E X h) (α : T.ι)
    (M : CohesiveModule (curvedDolbeault h)) : CohesiveModule (dolbeaultGrade E (T.U α)) :=
  CohesiveModule.gauge (T.h0 α) (T.h0_mem α) (twistData_hcβ h T α) (isUnit_of_invertible 2)
    (curvedRestrict h (T.U α) M)

end Cohesive
