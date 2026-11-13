import Cohesivemodules.Comparison.TwistedFFAlong

set_option linter.style.header false

/-!
# Z3.s: C4^tw step 3, the chain isomorphism `jK^tw`

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F′ (j); twisted copy of C4's `jK`,
`Comparison/FullyFaithfulPhiH.lean`). Notation as in `Comparison/TwistedFFAlong.lean`
(`U′ ≤ U_α`, `Y : Over U′`, `V = Y.left`):
* `jKtw : Hom^•_{along res_{V ≤ U′}}(gM₁|U′, gM₂|V) ⟶ ℋ^h(M₁, M₂)|U′ (Y)`,
  `χ' ↦ twCmpInv ∘ χ' ∘ twF`; a chain map (`jKtwf_comm`: the gauge terms `h⁰_α` cancel since
  `χ'` is semilinear of degree `n`, `twCmp_X`, `twF_X`) and an isomorphism (`isIso_jKtw`;
  inverse `χ ↦ twCmp ∘ extAlong χ ∘ twCmpInv ∘ res`);
* `extAlong_jKtw`: `extAlong (jKtw χ')` on `twCmpInv (y|V)` is `twCmpInv (χ' y)`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] (P : PreResolvingData X) {h : P.D.A ⊤}
  (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (α : T.ι) {U' : Opens X} (hU' : U' ≤ T.U α)
  (M₁ M₂ : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X) (Y : Over U')

/-- Additive maps commute with the action of `ℤˣ`. -/
theorem addMonoidHom_units_smul {G H : Type*} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    (u : ℤˣ) (x : G) : f (u • x) = u • f x := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/-- `twCmpInv ∘ χ' ∘ twF` lies in `ℋ^{h,n}(V)`. -/
theorem jKtw_mem {n : ℤ}
    (χ' : HomAlongT (P.D.res (leOfHom Y.hom)) (twSrc P T hh hd α hU' M₁)
      (twNY P T hh hd α hU' M₂ Y) n) :
    twCmpInvL P T hh hd α M₂ ((leOfHom Y.hom).trans hU') ∘ₗ χ'.1 ∘ₗ twF P T hh hd α hU' M₁ ∈
      (P.toSheafData.withCurvature h hh hd).homAlong M₁ M₂ n (le_top : Y.left ≤ ⊤) := by
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · exact twCmpInv_mem P T hh hd α M₂ _ (χ'.2.1 (twF_mem P T hh hd α hU' M₁ hx))
  · change twCmpInv P T hh hd α M₂ _ (χ'.1 (twF P T hh hd α hU' M₁ (a • x))) = _
    refine (congrArg (twCmpInv P T hh hd α M₂ _) ((congrArg χ'.1
      (twF_smul P T hh hd α hU' M₁ a x)).trans (χ'.2.2 ((P.D.res le_top).map_mem ha) _))).trans ?_
    refine (addMonoidHom_units_smul _ _ _).trans (congrArg _ ?_)
    refine (twCmpInv_smul P T hh hd α M₂ _ _ _).trans ?_
    exact congrArg (· • _) (P.D.res_comp _ _ a)

/-- **Z3.s.** `jK^tw` in degree `n`: `χ' ↦ twCmpInv ∘ χ' ∘ twF`. -/
def jKtwf (n : ℤ) :
    (alongComplex (P.D.res (leOfHom Y.hom)) (twSrc P T hh hd α hU' M₁)
      (twNY P T hh hd α hU' M₂ Y)).X n ⟶
      ((secAb ((ringOf P.toSheafData.O).over U') (op Y)).obj
        (((restr (ringOf P.toSheafData.O) U').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((P.toSheafData.withCurvature h hh hd).ℋ M₁ M₂))).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun χ' => (⟨twCmpInvL P T hh hd α M₂ ((leOfHom Y.hom).trans hU') ∘ₗ χ'.1 ∘ₗ
          twF P T hh hd α hU' M₁, jKtw_mem P T hh hd α hU' M₁ M₂ Y χ'⟩ :
        (P.toSheafData.withCurvature h hh hd).HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤))
      map_zero' := Subtype.ext (by
        change twCmpInvL P T hh hd α M₂ _ ∘ₗ (0 : _ →ₗ[ℂ] _) ∘ₗ twF P T hh hd α hU' M₁ = 0
        rw [LinearMap.zero_comp, LinearMap.comp_zero])
      map_add' := fun χ ψ => Subtype.ext (by
        change twCmpInvL P T hh hd α M₂ _ ∘ₗ (χ.1 + ψ.1) ∘ₗ twF P T hh hd α hU' M₁ = _ + _
        rw [LinearMap.add_comp, LinearMap.comp_add]) }

/-- `jKtwf` on an element (rfl). -/
theorem jKtwf_apply (n : ℤ)
    (χ' : HomAlongT (P.D.res (leOfHom Y.hom)) (twSrc P T hh hd α hU' M₁)
      (twNY P T hh hd α hU' M₂ Y) n) (x : M₁.T) :
    (show (P.toSheafData.withCurvature h hh hd).HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤) from
      (jKtwf P T hh hd α hU' M₁ M₂ Y n).hom χ').1 x =
      twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU') (χ'.1 (twF P T hh hd α hU' M₁ x)) :=
  rfl

/-- Sign bookkeeping for `jKtwf_comm`: the gauge terms cancel. -/
private theorem gauge_cancel {G : Type*} [AddCommGroup G] (A B w : G) (u : ℤˣ) :
    (A - w) - u • (B - u • w) = A - u • B := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul, smul_sub,
      neg_neg, sub_neg_eq_add] <;> abel

/-- **Z3.s.** `jKtwf` commutes with the differentials: under `twCmp`, the operator of `gM₂|V`
is `𝕏 − h⁰_α` (`twCmp_X`), that of `gM₁|U′` on `twF x` is `twF(𝕏 x) − h⁰_α · twF x` (`twF_X`),
and `χ'(h⁰_α · y) = (-1)ⁿ h⁰_α · χ'(y)`, so the `h⁰_α`-terms cancel. -/
theorem jKtwf_comm (n : ℤ) :
    jKtwf P T hh hd α hU' M₁ M₂ Y n ≫
      ((secAb ((ringOf P.toSheafData.O).over U') (op Y)).obj
        (((restr (ringOf P.toSheafData.O) U').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((P.toSheafData.withCurvature h hh hd).ℋ M₁ M₂))).d n (n + 1) =
      (alongComplex (P.D.res (leOfHom Y.hom)) (twSrc P T hh hd α hU' M₁)
        (twNY P T hh hd α hU' M₂ Y)).d n (n + 1) ≫ jKtwf P T hh hd α hU' M₁ M₂ Y (n + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro χ'
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have hd' : ((P.toSheafData.withCurvature h hh hd).ℋ M₁ M₂).d n (n + 1) =
      (P.toSheafData.withCurvature h hh hd).homD M₁ M₂ n := by
    simp only [DgaSheafData.ℋ, CochainComplex.of_d]
  simp only [alongComplex, CochainComplex.of_d, secAb, Functor.comp_obj,
    Functor.mapHomologicalComplex_obj_d, hd']
  change (M₂.baseChange ((P.toSheafData.withCurvature h hh hd).D.res (le_top : Y.left ≤ ⊤))).X
      (twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU') (χ'.1 (twF P T hh hd α hU' M₁ x))) -
      n.negOnePow • twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
        (χ'.1 (twF P T hh hd α hU' M₁ (M₁.X x))) =
    twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
      ((twNY P T hh hd α hU' M₂ Y).X (χ'.1 (twF P T hh hd α hU' M₁ x)) -
        n.negOnePow • χ'.1 ((twSrc P T hh hd α hU' M₁).X (twF P T hh hd α hU' M₁ x)))
  have e1 : twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
      ((twNY P T hh hd α hU' M₂ Y).X (χ'.1 (twF P T hh hd α hU' M₁ x))) =
      (M₂.baseChange ((P.toSheafData.withCurvature h hh hd).D.res (le_top : Y.left ≤ ⊤))).X
        (twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU') (χ'.1 (twF P T hh hd α hU' M₁ x)))
        - (P.toSheafData.withCurvature h hh hd).D.res ((leOfHom Y.hom).trans hU') (T.h0 α) •
        twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU') (χ'.1 (twF P T hh hd α hU' M₁ x)) :=
    (congrArg (twCmpInv P T hh hd α M₂ _) ((congrArg (twNY P T hh hd α hU' M₂ Y).X
      (twCmp_twCmpInv P T hh hd α M₂ _ _).symm).trans (twCmp_X P T hh hd α M₂ _ _))).trans
      (twCmpInv_twCmp P T hh hd α M₂ _ _)
  have e2 : twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
      (χ'.1 ((twSrc P T hh hd α hU' M₁).X (twF P T hh hd α hU' M₁ x))) =
      twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
        (χ'.1 (twF P T hh hd α hU' M₁ (M₁.X x))) -
      n.negOnePow • ((P.toSheafData.withCurvature h hh hd).D.res ((leOfHom Y.hom).trans hU')
        (T.h0 α) • twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
          (χ'.1 (twF P T hh hd α hU' M₁ x))) := by
    refine (congrArg (twCmpInv P T hh hd α M₂ _) ((congrArg χ'.1
      (twF_X P T hh hd α hU' M₁ x)).trans ((map_sub _ _ _).trans (congrArg (_ - ·)
        (χ'.2.2 ((P.D.res hU').map_mem (T.h0_mem α)) _))))).trans ((map_sub _ _ _).trans ?_)
    refine congrArg (_ - ·) ((addMonoidHom_units_smul _ _ _).trans ?_)
    rw [mul_one]
    exact congrArg _ ((twCmpInv_smul P T hh hd α M₂ _ _ _).trans
      (congrArg (· • _) (P.D.res_comp _ _ _)))
  refine Eq.trans ?_ ((map_sub _ _ _).trans (congrArg₂ (· - ·) e1
    ((addMonoidHom_units_smul _ _ _).trans (congrArg _ e2)))).symm
  exact (gauge_cancel _ _ _ _).symm

/-- **Z3.s.** The chain map `jK^tw`. -/
def jKtw :
    alongComplex (P.D.res (leOfHom Y.hom)) (twSrc P T hh hd α hU' M₁)
        (twNY P T hh hd α hU' M₂ Y) ⟶
      (secAb ((ringOf P.toSheafData.O).over U') (op Y)).obj
        (((restr (ringOf P.toSheafData.O) U').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((P.toSheafData.withCurvature h hh hd).ℋ M₁ M₂)) where
  f n := jKtwf P T hh hd α hU' M₁ M₂ Y n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact jKtwf_comm P T hh hd α hU' M₁ M₂ Y i

/-- `totRes` of `gM₁` from `U′` to `V` is semilinear along `res_{V ≤ U′}`. -/
private theorem totRes_g_smul (b : P.D.A U') (y : (twSrc P T hh hd α hU' M₁).T) :
    P.totRes (gaugedRes P T hh hd α M₁) hU' (leOfHom Y.hom) (b • y) =
      P.D.res (leOfHom Y.hom) b • P.totRes (gaugedRes P T hh hd α M₁) hU' (leOfHom Y.hom) y :=
  bcTotRes_smul (P.D.res (leOfHom Y.hom)) (P.D.res hU') (P.D.res ((leOfHom Y.hom).trans hU'))
    (P.D.res_comp _ _) (gaugedRes P T hh hd α M₁).Q b y

/-- **Z3.s.** `extAlong (jK^tw χ')` on `twCmpInv (y|V)` is `twCmpInv (χ' y)` (both are
semilinear along `res_{V ≤ U′}` and agree on `twF`, `twAlong_ext`). -/
theorem extAlong_jKtw (n : ℤ)
    (χ' : HomAlongT (P.D.res (leOfHom Y.hom)) (twSrc P T hh hd α hU' M₁)
      (twNY P T hh hd α hU' M₂ Y) n) (hW : Y.left ≤ Y.left) (y : (twSrc P T hh hd α hU' M₁).T) :
    extAlong ((P.toSheafData.withCurvature h hh hd).homAt M₁ M₂ n hW
        ((jKtwf P T hh hd α hU' M₁ M₂ Y n).hom χ'))
      (twCmpInv P T hh hd α M₁ ((leOfHom Y.hom).trans hU')
        (P.totRes (gaugedRes P T hh hd α M₁) hU' (leOfHom Y.hom) y)) =
      twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU') (χ'.1 y) := by
  letI : Module (P.D.A Y.left)
      ((P.toSheafData.withCurvature h hh hd).TotSec M₂ (le_top : Y.left ≤ ⊤)) :=
    inferInstanceAs (Module ((P.toSheafData.withCurvature h hh hd).D.A Y.left) _)
  let E := extAlong ((P.toSheafData.withCurvature h hh hd).homAt M₁ M₂ n hW
        ((jKtwf P T hh hd α hU' M₁ M₂ Y n).hom χ'))
  have key := twAlong_ext P T hh hd α hU' M₁ Y
    (N := (P.toSheafData.withCurvature h hh hd).TotSec M₂ (le_top : Y.left ≤ ⊤)) n
    (E.toAddMonoidHom.comp ((twCmpInv P T hh hd α M₁ ((leOfHom Y.hom).trans hU')).comp
      (P.totRes (gaugedRes P T hh hd α M₁) hU' (leOfHom Y.hom))))
    ((twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU')).comp χ'.1.toAddMonoidHom)
    (fun {p b} hb y => by
      change E (twCmpInv P T hh hd α M₁ _ (P.totRes _ hU' _ (b • y))) = _
      rw [totRes_g_smul]
      refine (congrArg E (twCmpInv_smul P T hh hd α M₁ _ _ _)).trans ?_
      exact (extAlong_mem _).2 (((P.toSheafData.withCurvature h hh hd).D.res
        (leOfHom Y.hom)).map_mem
          (show b ∈ (P.toSheafData.withCurvature h hh hd).D.𝒜 U' p from hb)) _)
    (fun {p b} hb y => by
      change twCmpInv P T hh hd α M₂ _ (χ'.1 (b • y)) = _
      refine (congrArg _ (χ'.2.2 hb y)).trans ((addMonoidHom_units_smul _ _ _).trans ?_)
      exact congrArg _ (twCmpInv_smul P T hh hd α M₂ _ _ _))
    (fun x => by
      change E (twCmpInv P T hh hd α M₁ _ (P.totRes _ hU' _ (twF P T hh hd α hU' M₁ x))) = _
      rw [twCmpInv_totRes_twF]
      refine (extAlong_bcF _ x).trans ?_
      exact (P.toSheafData.withCurvature h hh hd).totRes_id M₂ le_top _)
  exact DFunLike.congr_fun key y

/-- `jKtwf` is injective (`twAlong_ext`). -/
private theorem jKtwf_injective (n : ℤ) :
    Function.Injective (jKtwf P T hh hd α hU' M₁ M₂ Y n).hom := by
  intro χ₁ χ₂ hχ
  have h1 : ∀ x, χ₁.1 (twF P T hh hd α hU' M₁ x) = χ₂.1 (twF P T hh hd α hU' M₁ x) := by
    intro x
    have := LinearMap.congr_fun (congrArg Subtype.val hχ) x
    have e := congrArg (twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU')) this
    exact (twCmp_twCmpInv P T hh hd α M₂ _ _).symm.trans
      (e.trans (twCmp_twCmpInv P T hh hd α M₂ _ _))
  have key := twAlong_ext P T hh hd α hU' M₁ Y (N := (twNY P T hh hd α hU' M₂ Y).T) n
    χ₁.1.toAddMonoidHom χ₂.1.toAddMonoidHom (fun hb y => χ₁.2.2 hb y)
    (fun hb y => χ₂.2.2 hb y) h1
  exact Subtype.ext (LinearMap.ext fun y => DFunLike.congr_fun key y)

/-- The preimage of `χ ∈ ℋ^{h,n}(V)`: `twCmp ∘ extAlong χ ∘ twCmpInv ∘ res_{V ≤ U′}`. -/
private def jKtwPre (n : ℤ)
    (χ : (P.toSheafData.withCurvature h hh hd).HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤)) :
    HomAlongT (P.D.res (leOfHom Y.hom)) (twSrc P T hh hd α hU' M₁)
      (twNY P T hh hd α hU' M₂ Y) n :=
  ⟨twCmpL P T hh hd α M₂ ((leOfHom Y.hom).trans hU') ∘ₗ
      extAlong (f := (P.toSheafData.withCurvature h hh hd).D.res (le_top : Y.left ≤ ⊤))
        (n := n) ⟨χ.1, χ.2⟩ ∘ₗ twCmpInvL P T hh hd α M₁ ((leOfHom Y.hom).trans hU') ∘ₗ
      P.toSheafData.totResL (gaugedRes P T hh hd α M₁) hU' (leOfHom Y.hom),
    fun {m x} hx => twCmp_mem P T hh hd α M₂ _ ((extAlong_mem _).1
      (twCmpInv_mem P T hh hd α M₁ _ (P.toSheafData.totRes_mem _ hU' _ hx))),
    fun {p b} hb y => by
      change twCmp P T hh hd α M₂ _ (extAlong _ (twCmpInv P T hh hd α M₁ _
        (P.totRes _ hU' _ (b • y)))) = _
      rw [totRes_g_smul]
      refine (congrArg (fun w => twCmp P T hh hd α M₂ _ (extAlong _ w))
        (twCmpInv_smul P T hh hd α M₁ _ _ _)).trans ?_
      refine (congrArg (twCmp P T hh hd α M₂ _)
        ((extAlong_mem _).2 (((P.toSheafData.withCurvature h hh hd).D.res
          (leOfHom Y.hom)).map_mem
            (show b ∈ (P.toSheafData.withCurvature h hh hd).D.𝒜 U' p from hb)) _)).trans ?_
      refine (addMonoidHom_units_smul _ _ _).trans (congrArg _ ?_)
      exact twCmp_smul P T hh hd α M₂ _ _ _⟩

/-- `jKtwPre` is a preimage. -/
private theorem jKtwPre_spec (n : ℤ)
    (χ : (P.toSheafData.withCurvature h hh hd).HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤)) :
    (jKtwf P T hh hd α hU' M₁ M₂ Y n).hom (jKtwPre P T hh hd α hU' M₁ M₂ Y n χ) = χ := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  change twCmpInv P T hh hd α M₂ _ (twCmp P T hh hd α M₂ _ (extAlong _ (twCmpInv P T hh hd α M₁ _
    (P.totRes _ hU' _ (twF P T hh hd α hU' M₁ x))))) = χ.1 x
  exact (twCmpInv_twCmp P T hh hd α M₂ _ _).trans
    ((congrArg (extAlong _) (twCmpInv_totRes_twF P T hh hd α hU' M₁ Y x)).trans
      (extAlong_bcF _ x))

/-- **Z3.s.** `jK^tw` is an isomorphism. -/
theorem isIso_jKtw : IsIso (jKtw P T hh hd α hU' M₁ M₂ Y) := by
  have : ∀ n, IsIso ((jKtw P T hh hd α hU' M₁ M₂ Y).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective (jKtwf P T hh hd α hU' M₁ M₂ Y n)).2
      ⟨jKtwf_injective P T hh hd α hU' M₁ M₂ Y n, fun χ =>
        ⟨jKtwPre P T hh hd α hU' M₁ M₂ Y n χ, jKtwPre_spec P T hh hd α hU' M₁ M₂ Y n χ⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end Cohesive
