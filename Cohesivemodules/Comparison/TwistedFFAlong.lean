import Cohesivemodules.Comparison.TwistedLocal
import Cohesivemodules.Comparison.TwistedPsiAux
import Cohesivemodules.Comparison.FullyFaithfulPhiH

set_option linter.style.header false

/-!
# Z3.s: C4^tw step 3, the `ℋ^h` side (`jK^tw`)

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F′ (j); twisted copy of C4's `jK`,
`Comparison/FullyFaithfulPhiH.lean`). Fix `α`, `U′ ≤ U_α` and `Y : Over U′`, `V = Y.left`. Write
`gM := gauge_{h⁰_α}(M|U_α)` (`gaugedRes`, flat over `𝒜(U_α)`), `twSrc = gM₁|U′` and
`twNY = gM₂|V`. Then:
* `twF : Tot(M₁) → Tot(gM₁|U′)`, `x ↦ twCmp(F(x))` (A9's `F` along `res_{U′}` followed by the
  comparison `Tot(M₁|U′) → Tot(gM₁|U′)`); `twF_X`: `𝕏(twF x) = twF(𝕏 x) − h⁰_α · twF x`;
* `twAlong_ext`: maps out of `Tot(gM₁|U′)` semilinear along `res_{V ≤ U′}` are determined by
  their values on `twF`;
* `jKtw : Hom^•_{along res_{V ≤ U′}}(gM₁|U′, gM₂|V) ⟶ ℋ^h(M₁, M₂)(V)`,
  `χ' ↦ twCmpInv ∘ χ' ∘ twF`, a chain map (the gauge terms `h⁰_α` cancel since `χ'` is
  semilinear of degree `n`) and an isomorphism (`isIso_jKtw`);
* `extAlong_jKtw`: `extAlong (jKtw χ')` on `twCmpInv (y|V)` is `twCmpInv (χ' y)`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] (P : PreResolvingData X) {h : P.D.A ⊤}
  (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (α : T.ι) {U' : Opens X} (hU' : U' ≤ T.U α)

/-- **Z3.s.** `twCmp` as a `ℂ`-linear map. -/
def twCmpL (M : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X) {V : Opens X}
    (hV : V ≤ T.U α) :
    (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤) →ₗ[ℂ]
      P.TotSec (gaugedRes P T hh hd α M) hV where
  toFun := twCmp P T hh hd α M hV
  map_add' := map_add _
  map_smul' c x := by
    rw [← algebraMap_smul ((P.toSheafData.withCurvature h hh hd).D.A V) c x, twCmp_smul]
    exact algebraMap_smul (P.D.A V) c _

/-- **Z3.s.** `twCmpInv` as a `ℂ`-linear map. -/
def twCmpInvL (M : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X) {V : Opens X}
    (hV : V ≤ T.U α) :
    P.TotSec (gaugedRes P T hh hd α M) hV →ₗ[ℂ]
      (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤) where
  toFun := twCmpInv P T hh hd α M hV
  map_add' := map_add _
  map_smul' c y := by
    rw [← algebraMap_smul (P.D.A V) c y]
    refine (cmpTotInv_smul _ _ _ (curved_res_comp_eq P T hh hd α hV) M.toQuasiCohesive
      (algebraMap ℂ (P.D.A V) c) y).trans ?_
    exact algebraMap_smul ((P.toSheafData.withCurvature h hh hd).D.A V) c _

/-- `twCmpInv` is `𝒜(V)`-linear. -/
theorem twCmpInv_smul (M : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X)
    {V : Opens X} (hV : V ≤ T.U α) (a : P.D.A V) (y : P.TotSec (gaugedRes P T hh hd α M) hV) :
    twCmpInv P T hh hd α M hV (a • y) =
      (show (P.toSheafData.withCurvature h hh hd).D.A V from a) • twCmpInv P T hh hd α M hV y :=
  cmpTotInv_smul _ _ _ (curved_res_comp_eq P T hh hd α hV) M.toQuasiCohesive a y

variable (M₁ M₂ : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X)

/-- **Z3.s.** The source `gM₁|U′` of the along complex. -/
abbrev twSrc : QuasiCohesive (P.D.𝒜 U') :=
  ((gaugedRes P T hh hd α M₁).baseChange (P.D.res hU')).toQuasiCohesive

/-- **Z3.s.** The target `gM₂|V` (`V = Y.left`), flat over `𝒜(V)`. -/
abbrev twNY (Y : Over U') : QuasiCohesive (P.D.𝒜 Y.left) :=
  ((gaugedRes P T hh hd α M₂).baseChange (P.D.res ((leOfHom Y.hom).trans hU'))).toQuasiCohesive

/-- **Z3.s.** `twF : Tot(M₁) → Tot(gM₁|U′)`, `x ↦ twCmp(F(x))` (`F = bcF` along `res_{U′}`). -/
def twF : M₁.T →ₗ[ℂ] (twSrc P T hh hd α hU' M₁).T :=
  twCmpL P T hh hd α M₁ hU' ∘ₗ
    bcFLin ((P.toSheafData.withCurvature h hh hd).D.res (le_top : U' ≤ ⊤)) M₁.toQuasiCohesive

/-- `twF` on an element (rfl). -/
theorem twF_apply (x : M₁.T) :
    twF P T hh hd α hU' M₁ x = twCmp P T hh hd α M₁ hU'
      (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : U' ≤ ⊤)) M₁.Q x) := rfl

/-- `twF` is semilinear along `res_{U′}`. -/
theorem twF_smul (a : P.D.A ⊤) (x : M₁.T) :
    twF P T hh hd α hU' M₁ ((show (P.toSheafData.withCurvature h hh hd).D.A ⊤ from a) • x) =
      P.D.res (le_top : U' ≤ ⊤) a • twF P T hh hd α hU' M₁ x := by
  rw [twF_apply, twF_apply]
  exact (congrArg (twCmp P T hh hd α M₁ hU') (bcF_smul
    ((P.toSheafData.withCurvature h hh hd).D.res (le_top : U' ≤ ⊤)) M₁.Q a x)).trans
    (twCmp_smul P T hh hd α M₁ hU' _ _)

/-- `twF` preserves the total degree. -/
theorem twF_mem {m : ℤ} {x : M₁.T}
    (hx : x ∈ totDeg ((P.toSheafData.withCurvature h hh hd).D.𝒜 ⊤) M₁.Q m) :
    twF P T hh hd α hU' M₁ x ∈ totDeg (P.D.𝒜 U') (twSrc P T hh hd α hU' M₁).Q m :=
  twCmp_mem P T hh hd α M₁ hU' (bcF_mem_totDeg _ M₁.Q hx)

/-- **Z3.s.** `𝕏(twF x) = twF(𝕏 x) − h⁰_α|U′ · twF x` (`twCmp_X`, `bc_extend_bcF`). -/
theorem twF_X (x : M₁.T) :
    (twSrc P T hh hd α hU' M₁).X (twF P T hh hd α hU' M₁ x) =
      twF P T hh hd α hU' M₁ (M₁.X x) - P.D.res hU' (T.h0 α) • twF P T hh hd α hU' M₁ x := by
  rw [twF_apply, twF_apply]
  refine (twCmp_X P T hh hd α M₁ hU' _).trans ((map_sub _ _ _).trans ?_)
  exact congrArg₂ (· - ·)
    (congrArg (twCmp P T hh hd α M₁ hU') (bc_extend_bcF _ M₁.toQuasiCohesive x))
    (twCmp_smul P T hh hd α M₁ hU' _ _)

/-- `twF` is the composite of the two base changes `Tot(M₁) → Tot(M₁|U_α) = Tot(gM₁) →
Tot(gM₁|U′)` (`cmpTotInv_bcF`). -/
theorem twF_eq (x : M₁.T) :
    twF P T hh hd α hU' M₁ x = bcF (P.D.res hU') (gaugedRes P T hh hd α M₁).Q
      (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) M₁.Q x) := by
  have e := cmpTotInv_bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res hU')
    ((P.toSheafData.withCurvature h hh hd).D.res (le_top : U' ≤ ⊤))
    (curved_res_comp_eq P T hh hd α hU') M₁.toQuasiCohesive
    (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) M₁.Q x)
  have e2 := bcTotRes_bcF ((P.toSheafData.withCurvature h hh hd).D.res hU')
    ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res (le_top : U' ≤ ⊤))
    (fun a => by rw [← curved_res_comp_eq P T hh hd α hU']; rfl) M₁.Q x
  have e3 : twCmpInv P T hh hd α M₁ hU' (bcF (P.D.res hU') (gaugedRes P T hh hd α M₁).Q
      (bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) M₁.Q x)) =
      bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : U' ≤ ⊤)) M₁.Q x :=
    e.trans e2
  rw [twF_apply, ← e3]
  exact twCmp_twCmpInv P T hh hd α M₁ hU' _

variable (Y : Over U')

/-- **Z3.s (uniqueness).** Two additive maps out of `Tot(gM₁|U′)`, semilinear of degree `n`
along `res_{V ≤ U′}` and agreeing on `twF`, are equal (`bc_ext_semilinear` twice). -/
theorem twAlong_ext {N : Type} [AddCommGroup N] [Module (P.D.A Y.left) N] (n : ℤ)
    (ψ ψ' : (twSrc P T hh hd α hU' M₁).T →+ N)
    (hs : ∀ {p : ℤ} {b : P.D.A U'}, b ∈ P.D.𝒜 U' p → ∀ y,
      ψ (b • y) = (n * p).negOnePow • P.D.res (leOfHom Y.hom) b • ψ y)
    (hs' : ∀ {p : ℤ} {b : P.D.A U'}, b ∈ P.D.𝒜 U' p → ∀ y,
      ψ' (b • y) = (n * p).negOnePow • P.D.res (leOfHom Y.hom) b • ψ' y)
    (hag : ∀ x, ψ (twF P T hh hd α hU' M₁ x) = ψ' (twF P T hh hd α hU' M₁ x)) :
    ψ = ψ' := by
  letI : Module ((P.toSheafData.withCurvature h hh hd).D.A Y.left) N :=
    ‹Module (P.D.A Y.left) N›
  let C : (P.toSheafData.withCurvature h hh hd).TotSec M₁ (le_top : U' ≤ ⊤) →+
      (twSrc P T hh hd α hU' M₁).T := twCmp P T hh hd α M₁ hU'
  have hC : ∀ (χ : (twSrc P T hh hd α hU' M₁).T →+ N),
      (∀ {p : ℤ} {b : P.D.A U'}, b ∈ P.D.𝒜 U' p → ∀ y,
        χ (b • y) = (n * p).negOnePow • P.D.res (leOfHom Y.hom) b • χ y) →
      ∀ {p : ℤ} {b : (P.toSheafData.withCurvature h hh hd).D.A U'},
        b ∈ (P.toSheafData.withCurvature h hh hd).D.𝒜 U' p → ∀ z,
        (χ.comp C) (b • z) = (n * p).negOnePow •
          (P.toSheafData.withCurvature h hh hd).D.res (leOfHom Y.hom) b • (χ.comp C) z := by
    intro χ hχ p b hb z
    exact (congrArg χ (twCmp_smul P T hh hd α M₁ hU' b z)).trans (hχ hb _)
  have key : ψ.comp C = ψ'.comp C :=
    bc_ext_semilinear ((P.toSheafData.withCurvature h hh hd).D.res (leOfHom Y.hom))
      ((P.toSheafData.withCurvature h hh hd).D.res (le_top : U' ≤ ⊤)) M₁.Q n
      (ψ.comp C) (ψ'.comp C) (hC ψ hs) (hC ψ' hs') (fun x => hag x)
  ext y
  rw [← twCmp_twCmpInv P T hh hd α M₁ hU' y]
  exact DFunLike.congr_fun key _

/-- **Z3.s.** `twCmpInv((twF x)|V) = F(x)` along `res_V`. -/
theorem twCmpInv_totRes_twF (x : M₁.T) :
    twCmpInv P T hh hd α M₁ ((leOfHom Y.hom).trans hU')
        (P.totRes (gaugedRes P T hh hd α M₁) hU' (leOfHom Y.hom) (twF P T hh hd α hU' M₁ x)) =
      bcF ((P.toSheafData.withCurvature h hh hd).D.res (le_top : Y.left ≤ ⊤)) M₁.Q x := by
  rw [twF_apply]
  refine (congrArg (twCmpInv P T hh hd α M₁ _)
    (twCmp_totRes P T hh hd α M₁ hU' (leOfHom Y.hom) _).symm).trans ?_
  refine (twCmpInv_twCmp P T hh hd α M₁ _ _).trans ?_
  exact bcTotRes_bcF ((P.toSheafData.withCurvature h hh hd).D.res (leOfHom Y.hom))
    ((P.toSheafData.withCurvature h hh hd).D.res (le_top : U' ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res (le_top : Y.left ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res_comp le_top (leOfHom Y.hom)) M₁.Q x

end Cohesive
