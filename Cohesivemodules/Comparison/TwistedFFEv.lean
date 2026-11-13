import Cohesivemodules.Comparison.TwistedFFJK
import Cohesivemodules.Comparison.FullyFaithfulPhi
import Cohesivemodules.Comparison.AlphaOverRestr
import Cohesivemodules.Sheaf.Twisted.HomComplexTw
import Cohesivemodules.Sheaf.Twisted.HomRestrOver

set_option linter.style.header false

/-!
# Z3.s: C4^tw step 3, the `L` side (`evL^tw`) and the value of `ι`

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F′ (j); twisted copy of C4's `evL`,
`ι_app_res`, `Comparison/FullyFaithfulPhi.lean`). Fix `U′ ≤ U_α`, `Y : Over U′`, `V = Y.left`,
a complex `W` of `O(U′)`-modules, `L` on `Over U′` with `ε : Γ_{U′}(L) ≅ W`.
* `evLtw : Cochain(L|Y, (J_T M₂)_α|U′|Y) ⟶ Hom^•_{O(U′)}(W, gM₂|V)`,
  `c ↦ (w ↦ twCmp (c_{p,p+n}((ε⁻¹ w)|Y)))` (D.6: `twCmp` intertwines the differential
  `𝕏 − h⁰_α` of `J_T(M₂)` with that of the gauged module); an isomorphism for strictly perfect
  `L` (`isIso_evLtw`, S4.c);
* `ιtw_app_res`: `ι = u ≫ α_{U′}(φ) ≫ (α_{U_α}(gM₁)|U′ ≅ α_{U′}(gM₁|U′))⁻¹ ≫ (twLocalIso|U′)⁻¹`
  sends `(ε⁻¹ w)|Y` to `twCmpInv(φ(1 ⊗ 1 ⊗ w))|V`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X] (P : PreResolvingData X) {h : P.D.A ⊤}
  (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (α : T.ι) {U' : Opens X} (hU' : U' ≤ T.U α)

/-- **Z3.s.** `twCmpInv` commutes with restriction. -/
theorem twCmpInv_totRes (M : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X)
    {V W : Opens X} (hV : V ≤ T.U α) (hW : W ≤ V) (z : P.TotSec (gaugedRes P T hh hd α M) hV) :
    (P.toSheafData.withCurvature h hh hd).totRes M le_top hW (twCmpInv P T hh hd α M hV z) =
      twCmpInv P T hh hd α M (hW.trans hV) (P.totRes (gaugedRes P T hh hd α M) hV hW z) := by
  have e := twCmp_totRes P T hh hd α M hV hW (twCmpInv P T hh hd α M hV z)
  rw [twCmp_twCmpInv] at e
  rw [← e, twCmpInv_twCmp]

/-! ### The `L` side -/

section LSide

variable (W : CochainComplex (ModuleCat.{0} (P.O.obj.obj (op U'))) ℤ)
  (L : CochainComplex (Mod ((ringOf P.toSheafData.O).over U')) ℤ)
  (ε : ((gammaT ((ringOf P.toSheafData.O).over U') (Over.mk (𝟙 U'))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L ≅ W)
  (M₂ : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X) (Y : Over U')

/-- The component complex `(J_T M₂)_α|U′` on `Over U′`. -/
abbrev twK₂ : CochainComplex (Mod ((ringOf P.toSheafData.O).over U')) ℤ :=
  (restrOverC hU').obj ((compC α).obj (T.twistedSheafOf hh hd M₂))

/-- The value `twCmp(c_{p,p+n}((ε⁻¹ w)|Y)) ∈ Tot(gM₂|V)`. -/
def evLtwVal {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n) (p : ℤ)
    (w : W.X p) : (twNY P T hh hd α hU' M₂ Y).T :=
  twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
    (show (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤) from
      restrEval (Over.mkIdTerminal (X := U')) Y (c.v p (p + n) rfl) ((ε.inv.f p).hom w)).1

/-- `evLtwVal` is additive in `w`. -/
theorem evLtwVal_add {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n) (p : ℤ)
    (w w' : W.X p) :
    evLtwVal P T hh hd α hU' W L ε M₂ Y c p (w + w') =
      evLtwVal P T hh hd α hU' W L ε M₂ Y c p w + evLtwVal P T hh hd α hU' W L ε M₂ Y c p w' := by
  have e := restrEval_add (Over.mkIdTerminal (X := U')) Y (c.v p (p + n) rfl)
    ((ε.inv.f p).hom w) ((ε.inv.f p).hom w')
  refine (congrArg (fun z : (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + n)
    (le_top : Y.left ≤ ⊤) => twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU') z.1)
    ((congrArg (restrEval (Over.mkIdTerminal (X := U')) Y (c.v p (p + n) rfl))
      ((ε.inv.f p).hom.map_add w w')).trans e)).trans ?_
  exact map_add _ _ _

/-- `evLtwVal` is semilinear in `w`. -/
theorem evLtwVal_smul {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n) (p : ℤ)
    (r : P.O.obj.obj (op U')) (w : W.X p) :
    evLtwVal P T hh hd α hU' W L ε M₂ Y c p (r • w) =
      (P.D.res (leOfHom Y.hom)).f0.comp (P.ρ U') r • evLtwVal P T hh hd α hU' W L ε M₂ Y c p w := by
  have h1 := (ε.inv.f p).hom.map_smul r w
  have e := restrEval_smul (Over.mkIdTerminal (X := U')) Y (c.v p (p + n) rfl) r
    ((ε.inv.f p).hom w)
  refine (congrArg (fun z : (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + n)
    (le_top : Y.left ≤ ⊤) => twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU') z.1)
    ((congrArg (restrEval (Over.mkIdTerminal (X := U')) Y (c.v p (p + n) rfl)) h1).trans
      e)).trans ?_
  refine (twCmp_smul P T hh hd α M₂ _ _ _).trans ?_
  change ((P.ρ Y.left (P.O.obj.map (homOfLE (leOfHom Y.hom)).op r) : ↥(P.D.𝒜 Y.left 0)) :
    P.D.A Y.left) • _ = _
  rw [← P.ρ_natural]
  rfl

/-- `evLtwVal` as a semilinear map. -/
def evLtwV {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n) (p : ℤ) :
    W.X p →ₛₗ[(P.D.res (leOfHom Y.hom)).f0.comp (P.ρ U')] (twNY P T hh hd α hU' M₂ Y).T where
  toFun := evLtwVal P T hh hd α hU' W L ε M₂ Y c p
  map_add' := evLtwVal_add P T hh hd α hU' W L ε M₂ Y c p
  map_smul' := evLtwVal_smul P T hh hd α hU' W L ε M₂ Y c p

/-- `evLtwV` lands in `Hom^n_{O(U′)}(W, gM₂|V)`. -/
theorem evLtwV_mem {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n) :
    evLtwV P T hh hd α hU' W L ε M₂ Y c ∈
      HomR ((P.D.res (leOfHom Y.hom)).f0.comp (P.ρ U')) W (twNY P T hh hd α hU' M₂ Y) n := by
  intro p w
  exact twCmp_mem P T hh hd α M₂ _
    (restrEval (Over.mkIdTerminal (X := U')) Y (c.v p (p + n) rfl) ((ε.inv.f p).hom w) :
      (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)).2

/-- `evLtwV` is additive in the cochain. -/
theorem evLtwV_add {n : ℤ}
    (c c' : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n) :
    evLtwV P T hh hd α hU' W L ε M₂ Y (c + c') =
      evLtwV P T hh hd α hU' W L ε M₂ Y c + evLtwV P T hh hd α hU' W L ε M₂ Y c' := by
  funext p
  refine LinearMap.ext fun w => ?_
  change twCmp P T hh hd α M₂ _ (restrEval (Over.mkIdTerminal (X := U')) Y
    ((c + c').v p (p + n) rfl) ((ε.inv.f p).hom w) :
      (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + n)
      (le_top : Y.left ≤ ⊤)).1 = _
  rw [Cochain.add_v]
  exact map_add _ _ _

/-- `evLtwV` of the zero cochain is zero. -/
theorem evLtwV_zero (n : ℤ) :
    evLtwV P T hh hd α hU' W L ε M₂ Y
      (0 : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n) = 0 := by
  funext p
  refine LinearMap.ext fun w => ?_
  change twCmp P T hh hd α M₂ _ (restrEval (Over.mkIdTerminal (X := U')) Y
    ((0 : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n).v p (p + n) rfl)
    ((ε.inv.f p).hom w) : (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + n)
      (le_top : Y.left ≤ ⊤)).1 = 0
  rw [Cochain.zero_v]
  exact map_zero _

/-- **Z3.s.** `evL^tw` in degree `n`. -/
def evLtwf (n : ℤ) :
    (CochainComplex.HomComplex ((overC Y).obj L)
      ((overC Y).obj (twK₂ P T hh hd α hU' M₂))).X n ⟶
      (famComplex W (d_f0_comp (P.D.res (leOfHom Y.hom)) (P.d_ρ U')) (P.c_eq_zero Y.left)
        (twNY P T hh hd α hU' M₂ Y)).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun c => ⟨evLtwV P T hh hd α hU' W L ε M₂ Y c,
        evLtwV_mem P T hh hd α hU' W L ε M₂ Y c⟩
      map_zero' := Subtype.ext (evLtwV_zero P T hh hd α hU' W L ε M₂ Y n)
      map_add' := fun c c' => Subtype.ext (evLtwV_add P T hh hd α hU' W L ε M₂ Y c c') }

/-- `evLtwf` on an element (rfl). -/
theorem evLtwf_apply (n : ℤ)
    (c : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n) (p : ℤ)
    (w : W.X p) :
    (show HomR ((P.D.res (leOfHom Y.hom)).f0.comp (P.ρ U')) W (twNY P T hh hd α hU' M₂ Y) n from
      (evLtwf P T hh hd α hU' W L ε M₂ Y n).hom c).1 p w =
      evLtwVal P T hh hd α hU' W L ε M₂ Y c p w := rfl

/-- The differential of `(J_T M₂)_α|U′` on sections over `Y` is, under `twCmp`, the operator of
`gM₂|V` (`twCmp_X`, D.6). -/
theorem twK₂_d_val (i j : ℤ) (hij : i + 1 = j)
    (x : (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ i (le_top : Y.left ≤ ⊤)) :
    twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
      (show (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ j (le_top : Y.left ≤ ⊤) from
        ((((twK₂ P T hh hd α hU' M₂).d i j).val.app (op Y)).hom x)).1 =
      (twNY P T hh hd α hU' M₂ Y).X (twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU') x.1) := by
  subst hij
  have e2 : (T.twistedSheafOf hh hd M₂).d i (i + 1) = T.twDiff hh hd M₂ i :=
    CochainComplex.of_d _ _ _
  change twCmp P T hh hd α M₂ _ (show (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (i + 1)
    (le_top : Y.left ≤ ⊤) from (((restrOver (ringOf P.toSheafData.O) hU').map
      ((TwMod.comp P.toSheafData.O T.U T.ch α).map
        ((T.twistedSheafOf hh hd M₂).d i (i + 1)))).val.app (op Y)).hom x).1 = _
  rw [e2]
  exact (twCmp_X P T hh hd α M₂ _ x.1).symm

/-- The raw value of `restrEval` does not depend on the target index. -/
private lemma evVal_congr' {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) n)
    (p q q' : ℤ) (hq : p + n = q) (hq' : p + n = q')
    (m : (L.X p).val.obj (op (Over.mk (𝟙 U')))) :
    (restrEval (Over.mkIdTerminal (X := U')) Y (c.v p q hq) m :
      (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ q (le_top : Y.left ≤ ⊤)).1 =
    (restrEval (Over.mkIdTerminal (X := U')) Y (c.v p q' hq') m :
      (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ q' (le_top : Y.left ≤ ⊤)).1 := by
  subst hq
  subst hq'
  rfl

/-- **Z3.s.** `evLtwf` commutes with the differentials (as C4's `evLf_comm`, with
`twK₂_d_val`). -/
theorem evLtwf_comm (n : ℤ) :
    evLtwf P T hh hd α hU' W L ε M₂ Y n ≫
      (famComplex W (d_f0_comp (P.D.res (leOfHom Y.hom)) (P.d_ρ U')) (P.c_eq_zero Y.left)
        (twNY P T hh hd α hU' M₂ Y)).d n (n + 1) =
      (CochainComplex.HomComplex ((overC Y).obj L)
        ((overC Y).obj (twK₂ P T hh hd α hU' M₂))).d n (n + 1) ≫
        evLtwf P T hh hd α hU' W L ε M₂ Y (n + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  funext p
  apply LinearMap.ext
  intro w
  simp only [famComplex, CochainComplex.of_d]
  change (twNY P T hh hd α hU' M₂ Y).X (evLtwVal P T hh hd α hU' W L ε M₂ Y c p w) -
      n.negOnePow • evLtwVal P T hh hd α hU' W L ε M₂ Y c (p + 1) (dW W p w) =
    evLtwVal P T hh hd α hU' W L ε M₂ Y (CochainComplex.HomComplex.δ n (n + 1) c) p w
  have hv := CochainComplex.HomComplex.δ_v n (n + 1) rfl c p (p + (n + 1)) rfl (p + n) (p + 1)
    (by omega) rfl
  have hε : ((L.d p (p + 1)).val.app (op (Over.mk (𝟙 U')))).hom ((ε.inv.f p).hom w) =
      (ε.inv.f (p + 1)).hom (dW W p w) :=
    congrArg (fun q => q.hom w) (ε.inv.comm p (p + 1))
  have e1 : restrEval (Over.mkIdTerminal (X := U')) Y
      ((CochainComplex.HomComplex.δ n (n + 1) c).v p (p + (n + 1)) rfl) ((ε.inv.f p).hom w) =
    restrEval (Over.mkIdTerminal (X := U')) Y (c.v p (p + n) (by omega) ≫
        ((overC Y).obj (twK₂ P T hh hd α hU' M₂)).d (p + n) (p + (n + 1)))
        ((ε.inv.f p).hom w) +
      (n + 1).negOnePow • restrEval (Over.mkIdTerminal (X := U')) Y
        (((overC Y).obj L).d p (p + 1) ≫ c.v (p + 1) (p + (n + 1)) (by omega))
        ((ε.inv.f p).hom w) := by
    rw [hv]
    exact (restrEval_hom_add _ Y _ _ _).trans
      (congrArg (HAdd.hAdd _) (restrEval_hom_units _ Y _ _ _))
  have e2 : restrEval (Over.mkIdTerminal (X := U')) Y
      (((overC Y).obj L).d p (p + 1) ≫ c.v (p + 1) (p + (n + 1)) (by omega))
        ((ε.inv.f p).hom w) =
      restrEval (Over.mkIdTerminal (X := U')) Y (c.v (p + 1) (p + (n + 1)) (by omega))
        ((ε.inv.f (p + 1)).hom (dW W p w)) :=
    (restrEval_over_comp (Over.mkIdTerminal (X := U')) Y (L.d p (p + 1)) _ _).trans
      (congrArg _ hε)
  have t1 := twK₂_d_val P T hh hd α hU' M₂ Y (p + n) (p + (n + 1)) (by omega)
    (restrEval (Over.mkIdTerminal (X := U')) Y (c.v p (p + n) rfl) ((ε.inv.f p).hom w))
  have t2 : twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
      (restrEval (Over.mkIdTerminal (X := U')) Y (c.v (p + 1) (p + (n + 1)) (by omega))
        ((ε.inv.f (p + 1)).hom (dW W p w)) :
          (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + (n + 1))
            (le_top : Y.left ≤ ⊤)).1 =
      evLtwVal P T hh hd α hU' W L ε M₂ Y c (p + 1) (dW W p w) :=
    congrArg (twCmp P T hh hd α M₂ _) (evVal_congr' P T hh hd α hU' L M₂ Y c (p + 1) _ _ _ _ _)
  have t3 := congrArg (fun z : (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + (n + 1))
    (le_top : Y.left ≤ ⊤) => twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU') z.1) e1
  rw [e2] at t3
  simp only at t3
  change _ = twCmp P T hh hd α M₂ _ (_ + _) at t3
  rw [map_add] at t3
  change _ = _ + twCmp P T hh hd α M₂ _ ((n + 1).negOnePow • _) at t3
  rw [addMonoidHom_units_smul, t2] at t3
  have t4 := t3.trans (congrArg (· + (n + 1).negOnePow •
    evLtwVal P T hh hd α hU' W L ε M₂ Y c (p + 1) (dW W p w)) t1)
  refine Eq.trans ?_ t4.symm
  rw [Int.negOnePow_succ, Units.neg_smul, sub_eq_add_neg]
  rfl

/-- **Z3.s.** `evL^tw : Cochain(L|Y, (J_T M₂)_α|U′|Y) ⟶ Hom^•_{O(U′)}(W, gM₂|V)`,
`c ↦ (w ↦ twCmp (c_{p,p+n}((ε⁻¹ w)|Y)))`. -/
def evLtw :
    CochainComplex.HomComplex ((overC Y).obj L) ((overC Y).obj (twK₂ P T hh hd α hU' M₂)) ⟶
    famComplex W (d_f0_comp (P.D.res (leOfHom Y.hom)) (P.d_ρ U')) (P.c_eq_zero Y.left)
      (twNY P T hh hd α hU' M₂ Y) where
  f n := evLtwf P T hh hd α hU' W L ε M₂ Y n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact evLtwf_comm P T hh hd α hU' W L ε M₂ Y i

/-- `evLtwf` is injective for strictly perfect `L` (`restrEval_injective`). -/
private theorem evLtwf_injective (hL : IsStrictlyPerfect L) (n : ℤ) :
    Function.Injective (evLtwf P T hh hd α hU' W L ε M₂ Y n).hom := by
  intro c c' hcc
  have hh' : ∀ p (w : W.X p), evLtwVal P T hh hd α hU' W L ε M₂ Y c p w =
      evLtwVal P T hh hd α hU' W L ε M₂ Y c' p w := fun p w =>
    congrArg (fun χ : HomR ((P.D.res (leOfHom Y.hom)).f0.comp (P.ρ U')) W
      (twNY P T hh hd α hU' M₂ Y) n => χ.1 p w) hcc
  refine Cochain.ext _ _ fun p q hpq => ?_
  subst hpq
  refine restrEval_injective (Over.mkIdTerminal (X := U')) (hL.2 p) _ Y ?_
  funext m
  have hm : (ε.inv.f p).hom ((ε.hom.f p).hom m) = m :=
    congrArg (fun φ => (φ.f p).hom m) ε.hom_inv_id
  have := congrArg (twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU'))
    (hh' p ((ε.hom.f p).hom m))
  rw [← hm]
  refine Subtype.ext ?_
  exact (twCmpInv_twCmp P T hh hd α M₂ _ _).symm.trans
    (this.trans (twCmpInv_twCmp P T hh hd α M₂ _ _))

/-- `evLtwf` is surjective for strictly perfect `L` (`restrEval_surjective`). -/
private theorem evLtwf_surjective (hL : IsStrictlyPerfect L) (n : ℤ) :
    Function.Surjective (evLtwf P T hh hd α hU' W L ε M₂ Y n).hom := by
  intro (g : HomR ((P.D.res (leOfHom Y.hom)).f0.comp (P.ρ U')) W (twNY P T hh hd α hU' M₂ Y) n)
  have key : ∀ p : ℤ, ∃ G : ((overC Y).obj L).X p ⟶
      ((overC Y).obj (twK₂ P T hh hd α hU' M₂)).X (p + n),
      restrEval (Over.mkIdTerminal (X := U')) Y G = fun m =>
        (⟨twCmpInv P T hh hd α M₂ ((leOfHom Y.hom).trans hU') ((g.1 p) ((ε.hom.f p).hom m)),
          twCmpInv_mem P T hh hd α M₂ _ (g.2 p _)⟩ :
          (P.toSheafData.withCurvature h hh hd).sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)) := by
    intro p
    refine restrEval_surjective (Over.mkIdTerminal (X := U')) (hL.2 p) _ Y _ ?_ ?_
    · intro m m'
      refine Subtype.ext ?_
      exact (congrArg (twCmpInv P T hh hd α M₂ _) ((congrArg (g.1 p)
        ((ε.hom.f p).hom.map_add m m')).trans ((g.1 p).map_add _ _))).trans (map_add _ _ _)
    · intro r m
      refine Subtype.ext ?_
      refine (congrArg (twCmpInv P T hh hd α M₂ _) ((congrArg (g.1 p)
        ((ε.hom.f p).hom.map_smul r m)).trans (map_smulₛₗ (g.1 p) r _))).trans ?_
      refine (twCmpInv_smul P T hh hd α M₂ _ _ _).trans ?_
      exact congrArg (fun a : ↥(P.D.𝒜 Y.left 0) =>
        (show (P.toSheafData.withCurvature h hh hd).D.A Y.left from (a : P.D.A Y.left)) •
        twCmpInv P T hh hd α M₂ _ ((g.1 p) ((ε.hom.f p).hom m))) (P.ρ_natural (leOfHom Y.hom) r)
  choose G hG using key
  refine ⟨Cochain.mk fun p q hpq => hpq ▸ G p, Subtype.ext (funext fun p => ?_)⟩
  refine LinearMap.ext fun w => ?_
  have hm : (ε.hom.f p).hom ((ε.inv.f p).hom w) = w :=
    congrArg (fun φ => (φ.f p).hom w) ε.inv_hom_id
  have := congrArg (fun F => twCmp P T hh hd α M₂ ((leOfHom Y.hom).trans hU')
    (F ((ε.inv.f p).hom w)).1) (hG p)
  change _ = twCmp P T hh hd α M₂ _ (twCmpInv P T hh hd α M₂ _
    ((g.1 p) ((ε.hom.f p).hom ((ε.inv.f p).hom w)))) at this
  rw [hm, twCmp_twCmpInv] at this
  exact this

/-- **Z3.s.** For strictly perfect `L`, `evL^tw` is an isomorphism. -/
theorem isIso_evLtw (hL : IsStrictlyPerfect L) : IsIso (evLtw P T hh hd α hU' W L ε M₂ Y) := by
  have : ∀ n, IsIso ((evLtw P T hh hd α hU' W L ε M₂ Y).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective (evLtwf P T hh hd α hU' W L ε M₂ Y n)).2
      ⟨evLtwf_injective P T hh hd α hU' W L ε M₂ Y hL n,
        evLtwf_surjective P T hh hd α hU' W L ε M₂ Y hL n⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end LSide

end Cohesive
