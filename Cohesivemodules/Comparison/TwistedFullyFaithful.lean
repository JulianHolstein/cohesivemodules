import Cohesivemodules.Comparison.TwistedPsi
import Cohesivemodules.Comparison.TwistedLocal
import Cohesivemodules.Comparison.FullyFaithfulLocal
import Cohesivemodules.Sheaf.Twisted.HomSoftTw
import Cohesivemodules.Sheaf.Twisted.HomRestrTw
import Cohesivemodules.Sheaf.Twisted.InjectiveRestr
import Cohesivemodules.Comparison.TwistedFFGlobal
import Cohesivemodules.Comparison.TwistedFFLocal

set_option linter.style.header false

/-!
# Z3.s: C4^tw, the twisted functor `J_T` is fully faithful

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F, F′ (j), (k); [A, Prop 7.2.19, §7.4]). For
resolving data `D` on a compact Hausdorff space, a closed `h ∈ 𝒜²(X)`, a twist datum `T` for `h`
and the local gauge lemma over opens (`LLOpen`, a hypothesis here; for the Dolbeault data it is
Z3.e's `localGaugeLemmaOpen`):
* `quasiIso_Ψtw_comp` (F′ (j)): for a bounded below injective resolution `r : J_T(M₂) → I` in
  `TwMod`, `Ψ^tw ≫ r_* : ℋ^h(M₁, M₂) → 𝓗om^tw(J_T M₁, I)` is a quasi-isomorphism (locally on
  `U′ ⊂ U_α` it is C4's local map for the gauged flat modules, S6);
* `bijective_twistedJ_map` (F′ (k)): `J_T` is bijective on morphisms (softness, `H⁰` dictionary);
* `full_twistedJ`, `faithful_twistedJ`.

## Deviations
* As C4: `X` compact Hausdorff (C2's local model goes through C7).
* LL over opens is a hypothesis of the generic statement (`LLOpen`), proved for the Dolbeault
  data (Z3.e); the untwisted C4 needs it only over `X` (field `LL`).
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X]

variable (D : ResolvingData X) in
/-- **Z3.s.** The local gauge lemma over opens for resolving data `D` (blueprint-tw E.1, Z3.e):
every cohesive module `N` over `𝒜(U₀)` is, near each `x ∈ U₀`, isomorphic in `Ho(P_{𝒜(U′)})` to
`𝒜(U′) ⊗_{O(U′)} W` for a bounded complex `W` of finitely generated projective `O(U′)`-modules
(the form of the field `LL` of C0.b, with base `U₀` instead of `X`). -/
def LLOpen : Prop :=
  ∀ (U₀ : Opens X) (N : CohesiveModule (D.D.𝒜 U₀)) (x : X), x ∈ U₀ →
    ∃ (U' : Opens X) (hU' : U' ≤ U₀), x ∈ U' ∧
      ∃ (W : CochainComplex (ModuleCat.{0} (D.O.obj.obj (op U'))) ℤ)
        (hW : IsBoundedFGProj (D.O.obj.obj (op U')) W),
        Nonempty (HoP.mk (N.baseChange (D.D.res hU')) ≅ HoP.mk (D.fcMod U' W hW))

variable [CompactSpace X] [T2Space X] (D : ResolvingData X) {h : D.D.A ⊤}
  (T : TwistDatum D.toSheafData h) (hh : h ∈ D.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := D.D.𝒜 ⊤) h = 0)

/-- **Z3.s (C4^tw step 3, F′ (j)).** For a bounded below injective resolution `r : J_T(M₂) → I`
of twisted sheaves, `Ψ^tw ≫ r_* : ℋ^h(M₁, M₂) → 𝓗om^tw(J_T M₁, I)` is a quasi-isomorphism of
complexes of sheaves on `X`. -/
theorem quasiIso_Ψtw_comp (hLL : LLOpen D)
    (M₁ M₂ : CohesiveModule (D.toSheafData.withCurvature h hh hd).𝒜X)
    {I : CochainComplex (TwMod D.toSheafData.O T.U T.ch) ℤ} (r : T.twistedSheafOf hh hd M₂ ⟶ I)
    [QuasiIso r] (hI : ∀ n, Injective (I.X n)) (a : ℤ) [I.IsStrictlyGE a] :
    QuasiIso (T.Ψtw hh hd M₁ M₂ ≫
      twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r) := by
  refine quasiIso_of_locally _ fun x => ?_
  have hx : x ∈ ⨆ β, T.U β := by rw [T.iSup_eq]; trivial
  obtain ⟨α, hα⟩ := Opens.mem_iSup.1 hx
  obtain ⟨U', hU', hxU', W, hW, ⟨e⟩⟩ :=
    hLL (T.U α) (gaugedRes D.toPreResolvingData T hh hd α M₁) x hα
  exact ⟨U', hxU', quasiIso_restr_Ψtw_comp D T hh hd M₁ M₂ r hI a α hU' W hW e⟩

/-- **Z3.s (C4^tw, F′ (k)).** [A, Prop 7.2.19, §7.4]. `J_T` is bijective on morphisms. -/
theorem bijective_twistedJ_map (hLL : LLOpen D)
    [HasDerivedCategory.{w} (TwMod D.toSheafData.O T.U T.ch)]
    (M N : HoP (D.toSheafData.withCurvature h hh hd).𝒜X) :
    Function.Bijective (fun f : M ⟶ N ↦ (T.twistedJ hh hd).map f) := by
  haveI : EnoughInjectives (TwMod D.toSheafData.O T.U T.ch) := enoughInjectives T.toTwistCocycle
  obtain ⟨n, hn⟩ := exists_isStrictlyGE_twistedSheafOf D T hh hd N.as
  obtain ⟨I, r, hIn, hI, hr⟩ := exists_injective_resolution (T.twistedSheafOf hh hd N.as) n
  have hq := quasiIso_Ψtw_comp D T hh hd hLL M.as N.as r hI n
  have hΓ := quasiIso_Γ_Ψtw_comp D T hh hd M.as N.as r n hq
  haveI := CochainComplex.isKInjective_of_injective I n
  let Qt := HomotopyCategory.quotient (TwMod D.toSheafData.O T.U T.ch) (ComplexShape.up ℤ)
  have hQ := CochainComplex.IsKInjective.Qh_map_bijective
    (C := TwMod D.toSheafData.O T.U T.ch) (Qt.obj (T.twistedSheafOf hh hd M.as)) I
  have hfac : (fun f : M ⟶ N ↦ (T.twistedJ hh hd).map f ≫ DerivedCategory.Q.map r) =
      DerivedCategory.Qh.map ∘ (fun f : M ⟶ N ↦ (T.twistedJK hh hd).map f ≫ Qt.map r) := by
    funext f
    refine Eq.trans ?_ (Functor.map_comp DerivedCategory.Qh ((T.twistedJK hh hd).map f)
      (Qt.map r)).symm
    rfl
  have hb : Function.Bijective
      (fun f : M ⟶ N ↦ (T.twistedJ hh hd).map f ≫ DerivedCategory.Q.map r) := by
    rw [hfac]
    refine hQ.comp ⟨fun f f' hff => ?_, fun g => ?_⟩
    · induction f using Submodule.Quotient.induction_on with
      | H φ =>
      induction f' using Submodule.Quotient.induction_on with
      | H φ' =>
      have h1 : Qt.map (T.twMap hh hd φ ≫ r) = Qt.map (T.twMap hh hd φ' ≫ r) := hff
      exact mk_eq_of_homotopy_twMap_comp D T hh hd M.as N.as r hΓ φ φ'
        (HomotopyCategory.homotopyOfEq _ _ h1)
    · obtain ⟨g, rfl⟩ := Qt.map_surjective g
      obtain ⟨φ, ⟨H⟩⟩ := exists_homotopy_twMap_comp D T hh hd M.as N.as r hΓ g
      exact ⟨(Submodule.Quotient.mk φ : M ⟶ N), HomotopyCategory.eq_of_homotopy _ _ H⟩
  have hiso : IsIso (DerivedCategory.Q.map r) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hr
  refine ⟨fun f g hfg => hb.1 ?_, fun g => ?_⟩
  · change (T.twistedJ hh hd).map f = (T.twistedJ hh hd).map g at hfg
    change (T.twistedJ hh hd).map f ≫ DerivedCategory.Q.map r =
      (T.twistedJ hh hd).map g ≫ DerivedCategory.Q.map r
    rw [hfg]
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ DerivedCategory.Q.map r)
    refine ⟨f, ?_⟩
    change (T.twistedJ hh hd).map f ≫ DerivedCategory.Q.map r = g ≫ DerivedCategory.Q.map r at hf
    exact (cancel_mono (f := DerivedCategory.Q.map r)).1 hf

/-- **Z3.s (C4^tw).** `J_T` is full. -/
theorem full_twistedJ (hLL : LLOpen D) [HasDerivedCategory.{w} (TwMod D.toSheafData.O T.U T.ch)] :
    (T.twistedJ hh hd).Full :=
  ⟨fun {M N} => (bijective_twistedJ_map D T hh hd hLL M N).2⟩

/-- **Z3.s (C4^tw).** `J_T` is faithful. -/
theorem faithful_twistedJ (hLL : LLOpen D)
    [HasDerivedCategory.{w} (TwMod D.toSheafData.O T.U T.ch)] : (T.twistedJ hh hd).Faithful :=
  ⟨fun {M N} => (bijective_twistedJ_map D T hh hd hLL M N).1⟩

end Cohesive
