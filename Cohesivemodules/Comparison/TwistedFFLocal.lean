import Cohesivemodules.Comparison.TwistedFFSquare
import Cohesivemodules.Comparison.FullyFaithfulLocal
import Cohesivemodules.Comparison.PerfectModel
import Cohesivemodules.Sheaf.Twisted.HomRestrTw
import Cohesivemodules.Sheaf.Twisted.InjectiveRestr
import Cohesivemodules.Sheaf.Twisted.PerfectOver
import Cohesivemodules.Sheaf.Twisted.Perfect
import Cohesivemodules.Sheaf.HomOver

set_option linter.style.header false

/-!
# Z3.s: C4^tw step 3, the local quasi-isomorphism

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F′ (j); twisted copy of C4's `quasiIso_Φ`
and `quasiIso_restr_Ψ_comp`, `Comparison/FullyFaithfulLocal.lean`). For `U′ ≤ U_α` with
`gM₁|U′ ≅ 𝒜(U′) ⊗ W` in `Ho(P_{𝒜(U′)})` (LL over opens for the gauged module `gM₁`):
* `quasiIso_Φtw`: `Φ^tw = Ψ^tw|U′ ≫ twHomRestrOverIso ≫ ιtw^*` is a quasi-isomorphism
  (sectionwise, by the square `jKtw_Φtw_evLtw`: `jK^tw`, `evL^tw`, `alongEv` are isomorphisms
  and `alongPre φ` is a homotopy equivalence);
* `quasiIso_restr_Ψtw_comp`: for a bounded below injective resolution `r : J_T(M₂) → I` in
  `TwMod`, `(Ψ^tw ≫ r_*)|U′` is a quasi-isomorphism (S7.b′ for `r_*`, S7.c′ for `ιtw^*` with
  the twisted S5.c `injective_restrOver_comp`, 2-out-of-3).

## Deviations
* As C4: `X` compact Hausdorff (C2's map `u` goes through C7).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X]

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}} (hR : IsCommSheaf R)

/-- The two functorialities of `𝓗om` commute (copy of the private C4 lemma). -/
private theorem homComplexMap₂_comp_homComplexMap₁' {K K' : CochainComplex (Mod R) ℤ}
    (f : K' ⟶ K) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') :
    homComplexMap₂ hR K g ≫ homComplexMap₁ hR f L' =
      homComplexMap₁ hR f L ≫ homComplexMap₂ hR K' g := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine Limits.Pi.hom_ext _ _ fun T => ?_
  change (Limits.Pi.map _ ≫ Limits.Pi.map _) ≫ _ = (Limits.Pi.map _ ≫ Limits.Pi.map _) ≫ _
  rw [Category.assoc, Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π, ← Category.assoc,
    ← Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π, Category.assoc, Category.assoc]
  congr 1

end Site

section Generic

variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- Restriction between over-sites preserves quasi-isomorphisms (instance search, packaged). -/
theorem quasiIso_restrOverC_map {U₀ V : Opens X} (hV : V ≤ U₀)
    {K L : CochainComplex (Mod ((ringOf R).over U₀)) ℤ} (f : K ⟶ L) (hf : QuasiIso f) :
    QuasiIso ((restrOverC hV).map f) := inferInstance

/-- The component functors preserve quasi-isomorphisms (instance search, packaged). -/
theorem quasiIso_compC_map (α : ι) {K L : CochainComplex (TwMod R U ch) ℤ} (f : K ⟶ L)
    (hf : QuasiIso f) : QuasiIso ((compC α).map f) := inferInstance

/-- Restrictions of components of a complex strictly `≥ a` are strictly `≥ a`. -/
theorem isStrictlyGE_restrOverC_compC (α : ι) {V : Opens X} (hV : V ≤ U α)
    (I : CochainComplex (TwMod R U ch) ℤ) (a : ℤ) (hI : I.IsStrictlyGE a) :
    ((restrOverC hV).obj ((compC α).obj I)).IsStrictlyGE a :=
  (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
    (restrOver (ringOf R) hV).map_isZero
      ((TwMod.comp R U ch α).map_isZero (CochainComplex.isZero_of_isStrictlyGE I a i hi))

end Generic

section Wrappers

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}} (hR : IsCommSheaf R)

/-- The inverse of an isomorphism of complexes of sheaves is a quasi-isomorphism (packaged, with
the isomorphism as an explicit argument). -/
theorem quasiIso_iso_inv {K L : CochainComplex (Mod R) ℤ} (e : K ≅ L) : QuasiIso e.inv :=
  quasiIso_of_isIso _

/-- The hom of an isomorphism of complexes of sheaves is a quasi-isomorphism (packaged). -/
theorem quasiIso_iso_hom {K L : CochainComplex (Mod R) ℤ} (e : K ≅ L) : QuasiIso e.hom :=
  quasiIso_of_isIso _

/-- S7.b′ with the quasi-isomorphism as an explicit hypothesis. -/
theorem quasiIso_homComplexMap₂_site' {P : CochainComplex (Mod R) ℤ} (hP : IsStrictlyPerfect P)
    {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') (hg : QuasiIso g) :
    QuasiIso (homComplexMap₂ hR P g) :=
  quasiIso_homComplexMap₂_site hR hP g

/-- S7.c′ with the quasi-isomorphism and the bound as explicit hypotheses. -/
theorem quasiIso_homComplexMap₁_site' {K K' : CochainComplex (Mod R) ℤ} (f : K' ⟶ K)
    (hf : QuasiIso f) (I : CochainComplex (Mod R) ℤ) (n : ℤ) (hn : I.IsStrictlyGE n)
    (hI : ∀ (V : C) (i : ℤ), Injective ((SheafOfModules.overFunctor.{0} R V).obj (I.X i))) :
    QuasiIso (homComplexMap₁ hR f I) :=
  quasiIso_homComplexMap₁_site hR f n hI

/-- 2-out-of-3 with explicit hypotheses. -/
theorem quasiIso_of_comp_right' {K L M : CochainComplex (Mod R) ℤ} (φ : K ⟶ L) (φ' : L ⟶ M)
    (h' : QuasiIso φ') (h : QuasiIso (φ ≫ φ')) : QuasiIso φ :=
  (quasiIso_iff_comp_right φ φ').1 h

/-- Rearranging a composite using two commuting squares (generic category). -/
theorem comp_rearrange {𝒞 : Type*} [Category 𝒞] {a b c d e b' c' : 𝒞} (A : a ⟶ b) (B : b ⟶ c)
    (Cc : c ⟶ d) (Dd : d ⟶ e) (Rm : b ⟶ b') (BI : b' ⟶ c') (CI : c' ⟶ e) (E : c ⟶ c')
    (hn : Rm ≫ BI = B ≫ E) (hm : E ≫ CI = Cc ≫ Dd) :
    (A ≫ B ≫ Cc) ≫ Dd = (A ≫ Rm) ≫ BI ≫ CI := by
  simp only [Category.assoc]
  rw [← hm, reassoc_of% hn]

end Wrappers

namespace PreResolvingData

variable (P : PreResolvingData X)

/-- A homotopy equivalence in `Ho(P_{𝒜(U)})` gives a quasi-isomorphism `α_U(φ)` (copy of the
private C4 lemma). -/
theorem quasiIso_sheafOfOverMap_of_homotopyEquiv' (U : Opens X)
    {A B : CohesiveModule (P.D.𝒜 U)}
    (φ : Z0 A.toQuasiCohesive B.toQuasiCohesive) (ψ : Z0 B.toQuasiCohesive A.toQuasiCohesive)
    (h1 : (Submodule.Quotient.mk (compZ0 _ _ _ ψ φ) : H0 A.toQuasiCohesive A.toQuasiCohesive) =
      Submodule.Quotient.mk (idZ0 A.toQuasiCohesive))
    (h2 : (Submodule.Quotient.mk (compZ0 _ _ _ φ ψ) : H0 B.toQuasiCohesive B.toQuasiCohesive) =
      Submodule.Quotient.mk (idZ0 B.toQuasiCohesive)) :
    QuasiIso (P.sheafOfOverMap U φ) := by
  have key : ∀ {A B : CohesiveModule (P.D.𝒜 U)} (φ : Z0 A.toQuasiCohesive B.toQuasiCohesive)
      (ψ : Z0 B.toQuasiCohesive A.toQuasiCohesive),
      (Submodule.Quotient.mk (compZ0 _ _ _ ψ φ) : H0 A.toQuasiCohesive A.toQuasiCohesive) =
        Submodule.Quotient.mk (idZ0 A.toQuasiCohesive) →
      Nonempty (Homotopy (P.sheafOfOverMap U φ ≫ P.sheafOfOverMap U ψ)
        (𝟙 (P.sheafOfOver U A))) := by
    intro A B φ ψ hφψ
    have hab := Submodule.Quotient.eq _ |>.1 hφψ
    rw [Submodule.mem_comap] at hab
    obtain ⟨h, hh, hδ⟩ := hab
    obtain ⟨H⟩ := P.sheafOfOverMap_homotopic U (compZ0 _ _ _ ψ φ) (idZ0 A.toQuasiCohesive) ⟨h, hh⟩
      (by
        change δ _ _ (-1) h = _ - _
        exact hδ)
    rw [P.sheafOfOverMap_comp, P.sheafOfOverMap_id] at H
    exact ⟨H⟩
  obtain ⟨H1⟩ := key φ ψ h1
  obtain ⟨H2⟩ := key ψ φ h2
  exact (HomotopyEquiv.mk (P.sheafOfOverMap U φ) (P.sheafOfOverMap U ψ) H1 H2).quasiIso_hom

end PreResolvingData

section Phi

variable (P : PreResolvingData X) {h : P.D.A ⊤}
  (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (α : T.ι) {U' : Opens X} (hU' : U' ≤ T.U α)
  (W : CochainComplex (ModuleCat.{0} (P.O.obj.obj (op U'))) ℤ)
  (hW : IsBoundedFGProj (P.O.obj.obj (op U')) W)
  (L : CochainComplex (Mod ((ringOf P.toSheafData.O).over U')) ℤ)
  (ε : ((gammaT ((ringOf P.toSheafData.O).over U') (Over.mk (𝟙 U'))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj L ≅ W)
  (u : L ⟶ P.sheafOfOver U' (P.fcMod U' W hW))
  (M₁ M₂ : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X)

/-- **Z3.s (C4^tw step 3, sectionwise part).** With `L`, `u` as in C2 and a homotopy equivalence
`φ : 𝒜(U′) ⊗ W → gM₁|U′` (inverse `ψ`), `Φ^tw = Ψ^tw|U′ ≫ twHomRestrOverIso ≫ ιtw^*` is a
quasi-isomorphism (sectionwise, `jKtw_Φtw_evLtw`). -/
theorem quasiIso_Φtw (hL : IsStrictlyPerfect L)
    (hu : ((gammaT ((ringOf P.toSheafData.O).over U') (Over.mk (𝟙 U'))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u = ε.hom ≫ P.unitMap U' W hW)
    (φ : Z0 (P.fcMod U' W hW).toQuasiCohesive
      ((gaugedRes P T hh hd α M₁).baseChange (P.D.res hU')).toQuasiCohesive)
    (ψ : Z0 ((gaugedRes P T hh hd α M₁).baseChange (P.D.res hU')).toQuasiCohesive
      (P.fcMod U' W hW).toQuasiCohesive)
    (hψφ : (Submodule.Quotient.mk (compZ0 _ _ _ ψ φ) : H0 _ _) =
      Submodule.Quotient.mk (idZ0 (P.fcMod U' W hW).toQuasiCohesive))
    (hφψ : (Submodule.Quotient.mk (compZ0 _ _ _ φ ψ) : H0 _ _) =
      Submodule.Quotient.mk
        (idZ0 ((gaugedRes P T hh hd α M₁).baseChange (P.D.res hU')).toQuasiCohesive)) :
    QuasiIso (((restr (ringOf P.toSheafData.O) U').mapHomologicalComplex (ComplexShape.up ℤ)).map
        (T.Ψtw hh hd M₁ M₂) ≫
      (twHomRestrOverIso T.ch_aba T.iSup_eq α hU' (T.twistedSheafOf hh hd M₁)
        (T.twistedSheafOf hh hd M₂)).hom ≫
      homComplexMap₁ (isCommSheaf_over U') (ιtw P T hh hd α hU' W hW L u M₁ φ)
        (twK₂ P T hh hd α hU' M₂)) := by
  refine quasiIso_of_sectionwise _ fun V => ?_
  obtain ⟨Y⟩ := V
  refine (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat ↑(((ringOf P.toSheafData.O).over U').obj.obj (op Y)))
      AddCommGrpCat)).1 ?_
  have hsq := jKtw_Φtw_evLtw P T hh hd α hU' W hW L ε u M₁ M₂ φ hu Y
  haveI := isIso_jKtw P T hh hd α hU' M₁ M₂ Y
  haveI := isIso_evLtw P T hh hd α hU' W L ε M₂ Y hL
  haveI := isIso_alongEv (P.D.res (leOfHom Y.hom)) W (P.d_ρ U') (P.c_eq_zero U')
    (P.c_eq_zero Y.left) (twNY P T hh hd α hU' M₂ Y)
  haveI : QuasiIso (jKtw P T hh hd α hU' M₁ M₂ Y) := quasiIso_of_isIso _
  haveI : QuasiIso (evLtw P T hh hd α hU' W L ε M₂ Y) := quasiIso_of_isIso _
  haveI : QuasiIso (homSectionsIso (isCommSheaf_over U') L (twK₂ P T hh hd α hU' M₂) Y).hom :=
    quasiIso_of_isIso _
  have hev : QuasiIso (alongEv (P.D.res (leOfHom Y.hom)) W (P.d_ρ U') (P.c_eq_zero U')
      (P.c_eq_zero Y.left) (twNY P T hh hd α hU' M₂ Y)) := quasiIso_of_isIso _
  have hpre := quasiIso_alongPre (P.D.res (leOfHom Y.hom)) (twNY P T hh hd α hU' M₂ Y) φ ψ
    hψφ hφψ
  have h1 : QuasiIso (alongPre (P.D.res (leOfHom Y.hom)) (twNY P T hh hd α hU' M₂ Y) φ ≫
      alongEv (P.D.res (leOfHom Y.hom)) W (P.d_ρ U') (P.c_eq_zero U') (P.c_eq_zero Y.left)
        (twNY P T hh hd α hU' M₂ Y)) := quasiIso_comp (hφ := hpre) (hφ' := hev) _ _
  rw [← hsq, quasiIso_iff_comp_left, ← Category.assoc, quasiIso_iff_comp_right,
    quasiIso_iff_comp_right] at h1
  exact h1

end Phi

/-- **Z3.s (C4^tw step 3, local).** If `gM₁|U′ ≅ 𝒜(U′) ⊗ W` in `Ho(P_{𝒜(U′)})` for `U′ ≤ U_α`
(LL over opens for `gM₁ = gauge_{h⁰_α}(M₁|U_α)`), then for a bounded below injective resolution
`r : J_T(M₂) → I` of twisted sheaves, `(Ψ^tw ≫ r_*)|U′` is a quasi-isomorphism
(`quasiIso_Φtw`, S7.b′, S7.c′ with `injective_restrOver_comp`, 2-out-of-3). -/
theorem quasiIso_restr_Ψtw_comp [CompactSpace X] [T2Space X] (D : ResolvingData X)
    {h : D.D.A ⊤} (T : TwistDatum D.toSheafData h) (hh : h ∈ D.D.𝒜 ⊤ 2)
    (hd : GCDga.d (𝒜 := D.D.𝒜 ⊤) h = 0)
    (M₁ M₂ : CohesiveModule (D.toSheafData.withCurvature h hh hd).𝒜X)
    {I : CochainComplex (TwMod D.toSheafData.O T.U T.ch) ℤ} (r : T.twistedSheafOf hh hd M₂ ⟶ I)
    [QuasiIso r] (hI : ∀ n, Injective (I.X n)) (a : ℤ) [I.IsStrictlyGE a] (α : T.ι)
    {U' : Opens X} (hU' : U' ≤ T.U α)
    (W : CochainComplex (ModuleCat.{0} (D.O.obj.obj (op U'))) ℤ)
    (hW : IsBoundedFGProj (D.O.obj.obj (op U')) W)
    (e : HoP.mk ((gaugedRes D.toPreResolvingData T hh hd α M₁).baseChange (D.D.res hU')) ≅
      HoP.mk (D.fcMod U' W hW)) :
    QuasiIso (((restr (ringOf D.toSheafData.O) U').mapHomologicalComplex (ComplexShape.up ℤ)).map
      (T.Ψtw hh hd M₁ M₂ ≫ twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r)) := by
  obtain ⟨φ, ψ, hψφ, hφψ⟩ := D.exists_homotopyEquiv_of_iso U' e.symm
  obtain ⟨b, c, hbc⟩ := hW.bounded
  obtain ⟨L, hL, ⟨ε⟩⟩ := exists_lift_complex (R := D.R.over U') (Over.mkIdTerminal (X := U')) W
    hW.finite hW.projective b c hbc
  obtain ⟨u, hu⟩ := exists_lift_hom (Over.mkIdTerminal (X := U')) hL.2
    (ε.hom ≫ D.unitMap U' W hW)
  have hu' : QuasiIso u := D.quasiIso_of_gamma_eq U' W hW L hL ε u hu
  have hφ : QuasiIso (D.sheafOfOverMap U' φ) :=
    D.quasiIso_sheafOfOverMap_of_homotopyEquiv' U' φ ψ hψφ hφψ
  let ι := ιtw D.toPreResolvingData T hh hd α hU' W hW L u M₁ φ
  have h3 : QuasiIso
      (D.restrOverSheafOfIso hU' (gaugedRes D.toPreResolvingData T hh hd α M₁)).inv :=
    quasiIso_of_isIso _
  have h4 : QuasiIso
      ((restrOverC hU').map (twLocalIso D.toPreResolvingData T hh hd α M₁).inv) :=
    quasiIso_restrOverC_map hU' _
      (quasiIso_iso_inv (twLocalIso D.toPreResolvingData T hh hd α M₁))
  have hι : QuasiIso ι := quasiIso_comp (hφ := hu')
    (hφ' := quasiIso_comp (hφ := hφ) (hφ' := quasiIso_comp (hφ := h3) (hφ' := h4) _ _) _ _) _ _
  have hΦ := quasiIso_Φtw D.toPreResolvingData T hh hd α hU' W hW L ε u M₁ M₂ hL hu φ ψ hψφ hφψ
  have hr : QuasiIso ((restrOverC hU').map ((compC α).map r)) :=
    quasiIso_restrOverC_map hU' _ (quasiIso_compC_map α r inferInstance)
  have hb := quasiIso_homComplexMap₂_site' (isCommSheaf_over U') hL
    ((restrOverC hU').map ((compC α).map r)) hr
  have hIge : ((restrOverC hU').obj ((compC α).obj I)).IsStrictlyGE a :=
    isStrictlyGE_restrOverC_compC α hU' I a inferInstance
  have hIinj : ∀ (V : Over U') (i : ℤ), Injective ((SheafOfModules.overFunctor.{0}
      ((ringOf D.toSheafData.O).over U') V).obj (((restrOverC hU').obj ((compC α).obj I)).X i)) :=
    fun V i => by
      haveI := hI i
      exact injective_overFunctor_restrOver ((I.X i).M α)
        (fun h' => injective_restrOver_comp T.toTwistCocycle (I.X i) α h') hU' V
  have hc := quasiIso_homComplexMap₁_site' (isCommSheaf_over U') ι hι
    ((restrOverC hU').obj ((compC α).obj I)) a hIge hIinj
  have hcomp : QuasiIso ((((restr (ringOf D.toSheafData.O) U').mapHomologicalComplex
      (ComplexShape.up ℤ)).map (T.Ψtw hh hd M₁ M₂) ≫
      (twHomRestrOverIso T.ch_aba T.iSup_eq α hU' (T.twistedSheafOf hh hd M₁)
        (T.twistedSheafOf hh hd M₂)).hom ≫
      homComplexMap₁ (isCommSheaf_over U') ι (twK₂ D.toPreResolvingData T hh hd α hU' M₂)) ≫
      homComplexMap₂ (isCommSheaf_over U') L ((restrOverC hU').map ((compC α).map r))) :=
    quasiIso_comp (hφ := hΦ) (hφ' := hb) _ _
  have heq : (((restr (ringOf D.toSheafData.O) U').mapHomologicalComplex
      (ComplexShape.up ℤ)).map (T.Ψtw hh hd M₁ M₂) ≫
      (twHomRestrOverIso T.ch_aba T.iSup_eq α hU' (T.twistedSheafOf hh hd M₁)
        (T.twistedSheafOf hh hd M₂)).hom ≫
      homComplexMap₁ (isCommSheaf_over U') ι (twK₂ D.toPreResolvingData T hh hd α hU' M₂)) ≫
      homComplexMap₂ (isCommSheaf_over U') L ((restrOverC hU').map ((compC α).map r)) =
      ((restr (ringOf D.toSheafData.O) U').mapHomologicalComplex (ComplexShape.up ℤ)).map
        (T.Ψtw hh hd M₁ M₂ ≫ twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r) ≫
      ((twHomRestrOverIso T.ch_aba T.iSup_eq α hU' (T.twistedSheafOf hh hd M₁) I).hom ≫
        homComplexMap₁ (isCommSheaf_over U') ι ((restrOverC hU').obj ((compC α).obj I))) := by
    have hn := twHomRestrOverIso_naturality₂ T.ch_aba T.iSup_eq α hU'
      (T.twistedSheafOf hh hd M₁) r
    have hm := homComplexMap₂_comp_homComplexMap₁' (isCommSheaf_over U') ι
      ((restrOverC hU').map ((compC α).map r))
    exact (comp_rearrange _ _ _ _ _ _ _ _ hn hm).trans
      (congrArg (· ≫ _) (Functor.map_comp _ _ _).symm)
  rw [heq] at hcomp
  have hiso : QuasiIso ((twHomRestrOverIso T.ch_aba T.iSup_eq α hU'
      (T.twistedSheafOf hh hd M₁) I).hom ≫
      homComplexMap₁ (isCommSheaf_over U') ι ((restrOverC hU').obj ((compC α).obj I))) :=
    quasiIso_comp (hφ := quasiIso_iso_hom _) (hφ' := hc) _ _
  exact quasiIso_of_comp_right' _ _ hiso hcomp

end Cohesive
