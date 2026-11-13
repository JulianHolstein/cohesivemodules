import Cohesivemodules.StatementsTwisted
import Cohesivemodules.Statements
import Cohesivemodules.Sheaf.Twisted.GlueEquiv
import Cohesivemodules.Sheaf.Twisted.PerfectOver
import Cohesivemodules.Comparison.TwistDatumBasic
import Cohesivemodules.Algebra.Gauge
import Cohesivemodules.Comparison.GaugeExactIso
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

set_option linter.style.header false

/-!
# K14 and K8: the twisted statement at exact `h` is the untwisted one

Blueprint checks K14 and K8 (`blueprint/blueprint-tw.md` §3 H.3, §5). For `h = dβ`
(`β ∈ 𝒜^{0,1}(X)`) and the twist datum `exactTwistDatum β` (cover `{⊤}`, `h⁰ = β`, `u = 1`,
`ȟ = 1`), the twisted functor is the gauge equivalence `Ho(P_{(A, dβ)}) ≌ Ho(P_A)` (Z3.b), followed
by `blockFunctor` and the equivalence `ofSheaf : Mod O_X ≌ TwMod O_X {⊤} 1` (`glueEquiv`) lifted to
derived categories, which matches `TwPerf` with `Perf`. Hence (K14) the conclusion of the twisted
statement at `(dβ, exactTwistDatum β)` is equivalent to that of the untwisted statement, and (K8,
`β = 0`) `MainStatementTwisted → MainStatement`.
* `isEquivalence_mapDerivedCategory`: equivalences of abelian categories induce equivalences of
  derived categories;
* `nonempty_twistedJK_exact_iso`: `J_{T_β} ≅ gauge_β ⋙ J ⋙ ofSheaf` on homotopy categories;
* `twIsPerfect_ofSheafExact_iff`: `ofSheaf K` is twisted perfect iff `K` is perfect;
* `K14_exact_iff`, `K8_twisted_implies_unconditional`.

Lean note: `ofSheafExact` is stated over the cover of `exactDatum β` itself (not over the trivial
twist datum): matching `TwMod` over two different twist data with the same `U`, `ȟ` makes the
kernel time out.
-/

noncomputable section

universe u₁ v₁ u₂ v₂

namespace Cohesive

open CategoryTheory Manifold
open scoped ContDiff

/-- Isomorphic exact functors induce isomorphic functors on derived categories. -/
private def mapDerivedIso {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    {F G : C₁ ⥤ C₂} [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F] [G.Additive] [Limits.PreservesFiniteLimits G]
    [Limits.PreservesFiniteColimits G] (α : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
      (F.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
      (G.mapHomologicalComplex _ ⋙ DerivedCategory.Q) _ _
      (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex α (ComplexShape.up ℤ)) _)

/-- **K8/K14 (generic).** An exact equivalence `e : C₁ ≌ C₂` of abelian categories induces an
equivalence `e.functor.mapDerivedCategory : D(C₁) ⥤ D(C₂)` (inverse `e.inverse.mapDerivedCategory`,
via `mapDerivedCategoryCompIso` and `mapDerivedCategoryIdIso`). -/
theorem isEquivalence_mapDerivedCategory {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (e : C₁ ≌ C₂) [e.functor.Additive] [Limits.PreservesFiniteLimits e.functor]
    [Limits.PreservesFiniteColimits e.functor] [e.inverse.Additive]
    [Limits.PreservesFiniteLimits e.inverse] [Limits.PreservesFiniteColimits e.inverse] :
    e.functor.mapDerivedCategory.IsEquivalence := by
  have i1 : (𝟭 C₁).mapDerivedCategory ≅ (e.functor ⋙ e.inverse).mapDerivedCategory :=
    mapDerivedIso e.unitIso
  have i2 : (e.inverse ⋙ e.functor).mapDerivedCategory ≅ (𝟭 C₂).mapDerivedCategory :=
    mapDerivedIso e.counitIso
  exact (CategoryTheory.Equivalence.mk e.functor.mapDerivedCategory e.inverse.mapDerivedCategory
    ((Functor.mapDerivedCategoryIdIso C₁).symm ≪≫ i1 ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    ((Functor.mapDerivedCategoryCompIso _ _) ≪≫ i2 ≪≫
      Functor.mapDerivedCategoryIdIso C₂)).isEquivalence_functor

/-- An equivalence of abelian categories with additive functor induces an equivalence of derived
categories. -/
private theorem isEquivalence_mapDerivedCategory_of_additive {C₁ : Type u₁} [Category.{v₁} C₁]
    [Abelian C₁] {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] (e : C₁ ≌ C₂) [e.functor.Additive] :
    e.functor.mapDerivedCategory.IsEquivalence := by
  have : e.inverse.Additive := inferInstance
  exact isEquivalence_mapDerivedCategory e

/-- Full and faithful are invariant under pre- and post-composition with equivalences. -/
private theorem abs_full_faithful {H H' D₁ D₂ : Type*} [Category H] [Category H'] [Category D₁]
    [Category D₂] (G : H ⥤ H') [G.IsEquivalence] (B : H' ⥤ D₁) (Φ : D₁ ⥤ D₂)
    [Φ.IsEquivalence] :
    ((G ⋙ B ⋙ Φ).Full ↔ B.Full) ∧ ((G ⋙ B ⋙ Φ).Faithful ↔ B.Faithful) := by
  have i : G.asEquivalence.inverse ⋙ ((G ⋙ B ⋙ Φ) ⋙ Φ.asEquivalence.inverse) ≅ B :=
    NatIso.ofComponents (fun X => Φ.asEquivalence.unitIso.symm.app (B.obj _) ≪≫
      B.mapIso (G.asEquivalence.counitIso.app X)) (by
      intro X Y f
      have h1 := Φ.asEquivalence.unitIso.inv.naturality
        (B.map (G.map (G.asEquivalence.inverse.map f)))
      have h2 := G.asEquivalence.counitIso.hom.naturality f
      simp only [Functor.comp_map, Functor.id_map] at h1 h2
      simp
      rw [← Category.assoc]
      erw [h1]
      rw [Category.assoc, ← B.map_comp, ← B.map_comp]
      exact congrArg (fun g => _ ≫ B.map g) h2)
  refine ⟨⟨fun h => ?_, fun h => inferInstance⟩, ⟨fun h => ?_, fun h => inferInstance⟩⟩
  · exact Functor.Full.of_iso i
  · exact Functor.Faithful.of_iso i

/-- The essential image of `G ⋙ B ⋙ Φ` (`G`, `Φ` equivalences) is `P₂` iff that of `B` is `P₁`. -/
private theorem abs_essImage {H H' D₁ D₂ : Type*} [Category H] [Category H'] [Category D₁]
    [Category D₂] (G : H ⥤ H') [G.IsEquivalence] (B : H' ⥤ D₁) (Φ : D₁ ⥤ D₂)
    [Φ.IsEquivalence] (F : H ⥤ D₂) (e : F ≅ G ⋙ B ⋙ Φ) (P₁ : ObjectProperty D₁)
    (P₂ : ObjectProperty D₂) [P₂.IsClosedUnderIsomorphisms] (hP : ∀ D, P₂ (Φ.obj D) ↔ P₁ D) :
    F.essImage = P₂ ↔ B.essImage = P₁ := by
  have h0 : F.essImage = (B ⋙ Φ).essImage := by
    rw [Functor.essImage_eq_of_natIso e]
    exact Functor.essImage_comp_of_essSurj (F := G) (G := B ⋙ Φ)
  have h1 : ∀ D, B.essImage D ↔ (B ⋙ Φ).essImage (Φ.obj D) := by
    intro D
    constructor
    · rintro ⟨X, ⟨i⟩⟩
      exact ⟨X, ⟨Φ.mapIso i⟩⟩
    · rintro ⟨X, ⟨i⟩⟩
      exact ⟨X, ⟨(Φ.asEquivalence.fullyFaithfulFunctor.preimageIso i)⟩⟩
  rw [h0]
  constructor
  · intro h
    ext D
    rw [h1 D, h]
    exact hP D
  · intro h
    ext Y
    constructor
    · rintro ⟨X, ⟨i⟩⟩
      have : P₁ (B.obj X) := h ▸ Functor.obj_mem_essImage B X
      exact ObjectProperty.prop_of_iso P₂ i ((hP _).2 this)
    · intro hY
      have h2 : P₂ (Φ.obj (Φ.asEquivalence.inverse.obj Y)) :=
        ObjectProperty.prop_of_iso P₂ (Φ.asEquivalence.counitIso.app Y).symm hY
      have h3 := (h ▸ (hP _).1 h2 : B.essImage _)
      obtain ⟨X, ⟨i⟩⟩ := (h1 _).1 h3
      exact ⟨X, ⟨i ≪≫ Φ.asEquivalence.counitIso.app Y⟩⟩

/-- Abstract form of K14: the conclusion for `F ≅ G ⋙ B ⋙ Φ` iff that for `B`. -/
private theorem abs_K14 {H H' D₁ D₂ : Type*} [Category H] [Category H'] [Category D₁]
    [Category D₂] (G : H ⥤ H') [G.IsEquivalence] (B : H' ⥤ D₁) (Φ : D₁ ⥤ D₂)
    [Φ.IsEquivalence] (F : H ⥤ D₂) (e : F ≅ G ⋙ B ⋙ Φ) (P₁ : ObjectProperty D₁)
    (P₂ : ObjectProperty D₂) [P₂.IsClosedUnderIsomorphisms] (hP : ∀ D, P₂ (Φ.obj D) ↔ P₁ D) :
    (F.Full ∧ F.Faithful ∧ F.essImage = P₂) ↔ (B.Full ∧ B.Faithful ∧ B.essImage = P₁) := by
  have h1 := abs_full_faithful G B Φ
  have h2 := abs_essImage G B Φ F e P₁ P₂ hP
  have hF : F.Full ↔ (G ⋙ B ⋙ Φ).Full :=
    ⟨fun h => Functor.Full.of_iso e, fun h => Functor.Full.of_iso e.symm⟩
  have hFa : F.Faithful ↔ (G ⋙ B ⋙ Φ).Faithful :=
    ⟨fun h => Functor.Faithful.of_iso e, fun h => Functor.Faithful.of_iso e.symm⟩
  rw [hF, hFa, h1.1, h1.2, h2]

/-- Generic K14: if `J_t ≅ G ⋙ J ⋙ e.mapHomotopyCategory` for an equivalence `G` and an
equivalence of abelian categories `e` matching `P₂` with `P₁` on complexes, the conclusions for
`J_t ⋙ Qh` and `J ⋙ Qh` are equivalent. -/
private theorem K14_generic {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    {H H' : Type*} [Category H] [Category H'] (G : H ⥤ H') [G.IsEquivalence]
    (JK : H' ⥤ HomotopyCategory C₁ (ComplexShape.up ℤ))
    (JKt : H ⥤ HomotopyCategory C₂ (ComplexShape.up ℤ)) (e : C₁ ≌ C₂) [e.functor.Additive]
    (iso3 : JKt ≅ G ⋙ JK ⋙ e.functor.mapHomotopyCategory (ComplexShape.up ℤ))
    (P₁ : ObjectProperty (DerivedCategory C₁)) (P₂ : ObjectProperty (DerivedCategory C₂))
    [P₁.IsClosedUnderIsomorphisms] [P₂.IsClosedUnderIsomorphisms]
    (hP : ∀ K : CochainComplex C₁ ℤ, P₂ (DerivedCategory.Q.obj
      ((e.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ↔
        P₁ (DerivedCategory.Q.obj K)) :
    ((JKt ⋙ DerivedCategory.Qh).Full ∧ (JKt ⋙ DerivedCategory.Qh).Faithful ∧
      (JKt ⋙ DerivedCategory.Qh).essImage = P₂) ↔
    ((JK ⋙ DerivedCategory.Qh).Full ∧ (JK ⋙ DerivedCategory.Qh).Faithful ∧
      (JK ⋙ DerivedCategory.Qh).essImage = P₁) := by
  have : e.inverse.Additive := inferInstance
  have hΦ := isEquivalence_mapDerivedCategory_of_additive e
  have i : JKt ⋙ DerivedCategory.Qh ≅
      G ⋙ (JK ⋙ DerivedCategory.Qh) ⋙ e.functor.mapDerivedCategory :=
    Functor.isoWhiskerRight iso3 DerivedCategory.Qh ≪≫
    (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft G
      ((Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft JK
        (e.functor.mapDerivedCategoryFactorsh).symm ≪≫ (Functor.associator _ _ _).symm)
  refine abs_K14 G (JK ⋙ DerivedCategory.Qh) e.functor.mapDerivedCategory _ i P₁ P₂ ?_
  intro D
  obtain ⟨K, ⟨j⟩⟩ : ∃ K : CochainComplex C₁ ℤ, Nonempty (DerivedCategory.Q.obj K ≅ D) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso D⟩⟩
  rw [← ObjectProperty.prop_iff_of_iso P₁ j,
    ← ObjectProperty.prop_iff_of_iso P₂ (e.functor.mapDerivedCategory.mapIso j)]
  exact (ObjectProperty.prop_iff_of_iso P₂ ((e.functor.mapDerivedCategoryFactors).app K)).trans
    (hP K)

/-- `Perf R` is closed under isomorphism. -/
private instance perf_isClosedUnderIsomorphisms {X : Type} [TopologicalSpace X] {R : RingSheaf X}
    [HasDerivedCategory.{u₁} (Mod R)] : (Perf R).IsClosedUnderIsomorphisms :=
  ⟨fun {_ _} e ⟨K, hK, ⟨i⟩⟩ => ⟨K, hK, ⟨e.symm ≪≫ i⟩⟩⟩

/-- `TwPerf R U ch` is closed under isomorphism. -/
private instance twPerf_isClosedUnderIsomorphisms {X : Type} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} {ι : Type}
    {U : ι → TopologicalSpace.Opens X}
    {ch : ∀ α β γ, (R.obj.obj (Opposite.op (U α ⊓ U β ⊓ U γ)))ˣ}
    [HasDerivedCategory.{u₁} (TwMod R U ch)] : (TwPerf R U ch).IsClosedUnderIsomorphisms :=
  ⟨fun {_ _} e ⟨K, hK, ⟨i⟩⟩ => ⟨K, hK, ⟨e.symm ≪≫ i⟩⟩⟩

/-- The component functors preserve finite limits (copy of `comp_preservesFiniteLimits`). -/
private instance comp_preservesFiniteLimits' {X : Type} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} {ι : Type}
    {U : ι → TopologicalSpace.Opens X}
    {ch : ∀ α β γ, (R.obj.obj (Opposite.op (U α ⊓ U β ⊓ U γ)))ˣ} (α : ι) :
    Limits.PreservesFiniteLimits (TwMod.comp R U ch α) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The component functors preserve finite colimits (copy of `comp_preservesFiniteColimits`). -/
private instance comp_preservesFiniteColimits' {X : Type} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} {ι : Type}
    {U : ι → TopologicalSpace.Opens X}
    {ch : ∀ α β γ, (R.obj.obj (Opposite.op (U α ⊓ U β ⊓ U γ)))ˣ} (α : ι) :
    Limits.PreservesFiniteColimits (TwMod.comp R U ch α) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- `Q K` is in `Perf R` iff `K` is perfect, for a derived category in any universe. -/
private theorem perf_Q_obj_iff_any {X : Type} [TopologicalSpace X] {R : RingSheaf X}
    [HasDerivedCategory.{u₁} (Mod R)] (K : CochainComplex (Mod R) ℤ) :
    Perf R (DerivedCategory.Q.obj K) ↔ IsPerfect K := by
  constructor
  · rintro ⟨K', hK', ⟨e⟩⟩
    obtain ⟨M, s, hs, g, hg⟩ := DerivedCategory.right_fac e.hom
    have h4 : IsIso (DerivedCategory.Q.map g) := by
      have : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ e.hom := by
        rw [hg, IsIso.hom_inv_id_assoc]
      rw [this]; infer_instance
    have h5 : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
    have h6 : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 h4
    exact IsPerfect.of_quasiIso_left s (IsPerfect.of_quasiIso_right g hK')
  · intro hK
    exact ⟨K, hK, ⟨Iso.refl _⟩⟩

/-- `Q K` is in `TwPerf` iff `K` is twisted perfect, for a derived category in any universe. -/
private theorem twPerf_Q_obj_iff_any {X : Type} [TopologicalSpace X]
    {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} {ι : Type}
    {U : ι → TopologicalSpace.Opens X}
    {ch : ∀ α β γ, (R.obj.obj (Opposite.op (U α ⊓ U β ⊓ U γ)))ˣ}
    [HasDerivedCategory.{u₁} (TwMod R U ch)] (K : CochainComplex (TwMod R U ch) ℤ) :
    TwPerf R U ch (DerivedCategory.Q.obj K) ↔ TwIsPerfect K := by
  constructor
  · rintro ⟨K', hK', ⟨e⟩⟩
    obtain ⟨M, s, hs, g, hg⟩ := DerivedCategory.right_fac e.hom
    have h4 : IsIso (DerivedCategory.Q.map g) := by
      have : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ e.hom := by
        rw [hg, IsIso.hom_inv_id_assoc]
      rw [this]; infer_instance
    have h5 : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
    have h6 : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 h4
    intro α
    exact IsPerfectOver.of_quasiIso_left
      (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).map s)
      (IsPerfectOver.of_quasiIso_right
        (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).map g) (hK' α))
  · intro hK
    exact ⟨K, hK, ⟨Iso.refl _⟩⟩

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  [T2Space X] [CompactSpace X]

/-- K14: the conclusion of the twisted main statement at `(h, T)` (the body of
`MainStatementTwisted`). -/
def TwistedConclusion (h : DolbeaultClosed2 E X) (T : TwistData E X h) : Prop :=
  letI := HasDerivedCategory.standard (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)
  (twistedBlockFunctor h T).Full ∧ (twistedBlockFunctor h T).Faithful ∧
    (twistedBlockFunctor h T).essImage = TwPerf (dolbeaultPreData E X).toSheafData.O T.U T.ch

/-- K14: the conclusion of the untwisted main statement for `X` (the body of
`MainStatement`). -/
def UntwistedConclusion : Prop :=
  letI := HasDerivedCategory.standard (Mod (ringOf (holSheaf E X)))
  (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
    (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X))

variable (β : DolbeaultAlg E (⊤ : TopologicalSpace.Opens X))
  (hβ : β ∈ (dolbeaultPreData E X).toSheafData.D.𝒜 ⊤ 1) (h : DolbeaultClosed2 E X)
  (hdβ : GCDga.d (𝒜 := (dolbeaultPreData E X).toSheafData.D.𝒜 ⊤) β = h.1)

/-- K14: the twist datum `exactTwistDatum β` for `h = dβ` over the Dolbeault data (cover `{⊤}`,
`h⁰ = β`, `u = 1`, `ȟ = 1`). -/
abbrev exactDatum : TwistData E X h :=
  exactTwistDatum (dolbeaultPreData E X).toSheafData β hβ h.1 hdβ

/-- K14: `ofSheaf : Mod O_X ⥤ TwMod O_X {⊤} 1` (`N ↦ (N|⊤, φ = id)`) over the cover of
`exactDatum β`, the inverse of the gluing equivalence `glueEquiv`. -/
abbrev ofSheafExact : Mod (ringOf (holSheaf E X)) ⥤
    TwMod (dolbeaultPreData E X).toSheafData.O (exactDatum E X β hβ h hdβ).U
      (exactDatum E X β hβ h hdβ).ch :=
  (glueEquiv (R := holSheaf E X) (exactDatum E X β hβ h hdβ).iSup_eq).inverse

/-- K14: `ofSheaf` is additive (an equivalence of preadditive categories). -/
instance : (ofSheafExact E X β hβ h hdβ).Additive := by
  rw [show ofSheafExact E X β hβ h hdβ = TwMod.ofSheafFunctor (holSheaf E X)
    (exactDatum E X β hβ h hdβ).U from glueEquiv_inverse _]
  exact ⟨fun {_ _ _ _} => TwMod.hom_ext fun α =>
    Functor.map_add (restr (ringOf (holSheaf E X)) ((exactDatum E X β hβ h hdβ).U α))⟩

/-- The equivalence `Mod O_X ≌ TwMod O_X {⊤} 1` with functor `ofSheafExact`. -/
private abbrev exactEquiv : Mod (ringOf (holSheaf E X)) ≌
    TwMod (dolbeaultPreData E X).toSheafData.O (exactDatum E X β hβ h hdβ).U
      (exactDatum E X β hβ h hdβ).ch :=
  (glueEquiv (R := holSheaf E X) (exactDatum E X β hβ h hdβ).iSup_eq).symm

/-- The functor of `exactEquiv` is additive. -/
private instance : (exactEquiv E X β hβ h hdβ).functor.Additive :=
  inferInstanceAs ((ofSheafExact E X β hβ h hdβ).Additive)

include hdβ in
/-- K14: `h|⊤ = 0 + dβ` for the flat Dolbeault instance (`c = 0`), the hypothesis of the gauge.
Stated with `h|⊤ = res h` (the curvature of `curvedInst ⊤`), so that the gauge's source is
syntactically `Ho(P_{(A, h)})` as `twistedJK` spells it. -/
theorem exact_hcβ :
    (dolbeaultPreData E X).toSheafData.D.res le_top h.1 =
      ((dolbeaultPreData E X).toSheafData.D.dga ⊤).c +
        ((dolbeaultPreData E X).toSheafData.D.dga ⊤).d β :=
  ((dolbeaultPreData E X).toSheafData.D.res_id ⊤ h.1).trans (hdβ.symm.trans (zero_add _).symm)

/-- K14: the gauge `Ho(P_{(A, h)}) ⥤ Ho(P_A)`, `M ↦ (M, 𝕏 − β)` (Z3.b, `gaugeFunctor`), in the
spelling of `twistedJK`'s source (`curvedInst ⊤ = (D.dga ⊤).withC (h|⊤)`). -/
abbrev gaugeExact : HoP ((dolbeaultPreData E X).toSheafData.withCurvature h.1 h.2.1 h.2.2).𝒜X ⥤
    HoP (dolbeaultPreData E X).toSheafData.𝒜X :=
  gaugeFunctor (i := (dolbeaultPreData E X).toSheafData.D.dga ⊤)
    (c' := (dolbeaultPreData E X).toSheafData.D.res le_top h.1)
    (hc := ((dolbeaultPreData E X).toSheafData.D.res le_top).map_mem h.2.1)
    (hd := ((dolbeaultPreData E X).toSheafData.D.curvedInst h.1 h.2.1 h.2.2 ⊤).d_c) β hβ
    (exact_hcβ E X β h hdβ) (isUnit_of_invertible 2)

/-- **K14.** [B, §2.7], [A, §7.4]. For `h = dβ` and the twist datum `exactTwistDatum β`,
`J_{T_β} : Ho(P_{(A, dβ)}) ⥤ K(TwMod O_X {⊤} 1)` is the gauge `M ↦ gauge_β M` (Z3.b) followed by
`J ⋙ ofSheaf` on homotopy categories: componentwise `J_{T_β}(M) = α(M)|⊤` with differential
`𝕏 − β = 𝕏_{gauge_β M}` and gluing `u· = id`. -/
theorem nonempty_twistedJK_exact_iso :
    Nonempty ((exactDatum E X β hβ h hdβ).twistedJK h.2.1 h.2.2 ≅
      gaugeExact E X β hβ h hdβ ⋙ (dolbeaultPreData E X).JK ⋙
        (ofSheafExact E X β hβ h hdβ).mapHomotopyCategory (ComplexShape.up ℤ)) :=
  ⟨gaugeExactNatIso (P := dolbeaultPreData E X) h.2.1 h.2.2 β hβ (exact_hcβ E X β h hdβ) hdβ⟩

/-- **K14.** `ofSheaf K` is twisted perfect iff `K` is perfect (its only component is `K|⊤`,
`isPerfectOver_restr_top_iff`). -/
theorem twIsPerfect_ofSheafExact_iff (K : CochainComplex (Mod (ringOf (holSheaf E X))) ℤ) :
    TwIsPerfect (((ofSheafExact E X β hβ h hdβ).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ↔
      IsPerfect K := by
  rw [← isPerfectOver_restr_top_iff K]
  exact ⟨fun hK => hK (), fun hK _ => hK⟩

/-- **K14.** [B, §2.7], [A, Thm 7.4.3 at exact `h`]. For `h = dβ` and the twist datum
`exactTwistDatum β`, the conclusion of the twisted main statement at `(h, T_β)` holds iff the
conclusion of the untwisted main statement holds for `X`: `twistedBlockFunctor h T_β` is
`blockFunctor` conjugated by the gauge equivalence on the source and by an equivalence of derived
categories matching `TwPerf` with `Perf` on the target. -/
theorem K14_exact_iff :
    TwistedConclusion E X h (exactDatum E X β hβ h hdβ) ↔ UntwistedConclusion E X := by
  let _ := HasDerivedCategory.standard (TwMod (dolbeaultPreData E X).toSheafData.O
    (exactDatum E X β hβ h hdβ).U (exactDatum E X β hβ h hdβ).ch)
  let _ := HasDerivedCategory.standard (Mod (ringOf (holSheaf E X)))
  have : (gaugeExact E X β hβ h hdβ).IsEquivalence :=
    (gaugeHoP (i := (dolbeaultPreData E X).toSheafData.D.dga ⊤)
      (c' := (dolbeaultPreData E X).toSheafData.D.res le_top h.1)
      (hc := ((dolbeaultPreData E X).toSheafData.D.res le_top).map_mem h.2.1)
      (hd := ((dolbeaultPreData E X).toSheafData.D.curvedInst h.1 h.2.1 h.2.2 ⊤).d_c) β hβ
      (exact_hcβ E X β h hdβ) (isUnit_of_invertible 2)).isEquivalence_functor
  obtain ⟨iso3⟩ := nonempty_twistedJK_exact_iso E X β hβ h hdβ
  let JK : HoP (dolbeaultPreData E X).toSheafData.𝒜X ⥤
      HomotopyCategory (Mod (ringOf (holSheaf E X))) (ComplexShape.up ℤ) :=
    (dolbeaultPreData E X).JK
  exact K14_generic (C₁ := Mod (ringOf (holSheaf E X))) (gaugeExact E X β hβ h hdβ) JK
    ((exactDatum E X β hβ h hdβ).twistedJK h.2.1 h.2.2) (exactEquiv E X β hβ h hdβ) iso3 _ _
    (fun K => (twPerf_Q_obj_iff_any _).trans
      ((twIsPerfect_ofSheafExact_iff E X β hβ h hdβ K).trans (perf_Q_obj_iff_any K).symm))

/-- **K8.** [A, Thm 7.4.3 at h = 0]. The twisted main statement implies the untwisted one (K14 at
`β = 0`, `h = 0`, where `exactTwistDatum 0` is the trivial twist datum). -/
theorem K8_twisted_implies_unconditional :
    MainStatementTwisted → MainStatement := by
  intro hT E _ _ _ X _ _ _ _ _
  have h1 : TwistedConclusion E X (0 : DolbeaultClosed2 E X)
      (exactDatum E X 0 (Submodule.zero_mem _) 0 (map_zero _)) :=
    hT E X 0 (exactDatum E X 0 (Submodule.zero_mem _) 0 (map_zero _))
  exact (K14_exact_iff E X 0 (Submodule.zero_mem _) 0 (map_zero _)).mp h1

end Cohesive
