import Cohesivemodules.Comparison.ModelTensorIso
import Cohesivemodules.Comparison.EssSurjAux

set_option linter.style.header false

/-!
# C7.d: `T(K) ≅ 𝒜^•|U ⊗ K`

Blueprint item C7.d (§4, v1.11). Split from `ModelBC.lean` for size, and itself split into
`ModelTensor{Pair, Kappa, Coord, Iso}` (27 Oct 2026). For a connection on `F_K = 𝒜⁰ ⊗_R K` with
`∇(η k) = 0`, `T(K)` is isomorphic to `tensorC (𝒜^•|U) K`, compatibly with `ιT` and `ρ̂|U ⊗ K`
(`exists_TC_iso_tensorC`); hence `ιT` is a quasi-isomorphism for K-flat `K` (`quasiIso_ιT`).

## Deviations
* None beyond those of `ModelDef.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X) (K : CochainComplex (Mod (P.R.over U)) ℤ)

/-! ### The chain map `Φ : 𝒜^•|U ⊗ K ⟶ T(K)` -/

section Chain

variable [CompactSpace X] (θ : P.Conn U (P.FK U K)) (hθ : P.IsBCConn U K θ)

/-- Evaluating a sum of presheaf-of-modules morphisms at an element. -/
private theorem pom_add_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    {M N : PresheafOfModules R} (f g : M ⟶ N) (V : Cᵒᵖ) (x : M.obj V) :
    ((f + g).app V).hom x = (f.app V).hom x + (g.app V).hom x := rfl

/-- Evaluating an integer multiple of a presheaf-of-modules morphism at an element. -/
private theorem pom_zsmul_apply {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    {M N : PresheafOfModules R} (z : ℤ) (f : M ⟶ N) (V : Cᵒᵖ) (x : M.obj V) :
    ((z • f).app V).hom x = z • (f.app V).hom x := by
  rw [PresheafOfModules.zsmul_app]
  rfl

include hθ in
/-- The Leibniz rule on generators, presheaf level: `𝕏(a ⊗ η k) = da ⊗ η k + (-1)^q a ⊗ η(dk)`
(`GenData.extend_tmul` and `∇(η k) = 0`); the sign is Mathlib's `ε₂ (q, p) = (-1)^q`. -/
private theorem φPre_TD (q p n : ℤ) (h : q + p = n) :
    P.φPre U K q p n h ≫ (SheafOfModules.forget _).map (θ.TD n) =
      (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          ((P.Atil U).d q (q + 1)).val (K.X p).val ≫
          P.φPre U K (q + 1) p (n + 1) (by omega) :
        P.PreT U K q p ⟶ (SheafOfModules.forget _).obj (P.TSh U (P.FK U K) (n + 1))) +
      (MonoidalCategory.whiskerLeft (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          (P.AqU U q).val (K.d p (p + 1)).val ≫
          ((q.negOnePow : ℤ) • P.φPre U K q (p + 1) (n + 1) (by omega)) :
        P.PreT U K q p ⟶ (SheafOfModules.forget _).obj (P.TSh U (P.FK U K) (n + 1))) := by
  refine PresheafOfModules.hom_ext fun V => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a k => ?_
  apply Subtype.ext
  erw [pom_add_apply]
  erw [Submodule.coe_add, pom_zsmul_apply]
  have hd1 : (P.Atil U).d q (q + 1) = (restr P.R U).map (P.dgaD q) := by
    change (restr P.R U).map (P.dgaComplex.d q (q + 1)) = _
    rw [show P.dgaComplex.d q (q + 1) = P.dgaD q from CochainComplex.of_d _ _ _]
    rfl
  rw [hd1]
  change (θ.N V).X (P.pairElt U K q p V a k) =
    P.pairElt U K (q + 1) p V (P.dgaDV q V.unop.left a) k +
    (q.negOnePow : ℤ) • P.pairElt U K q (p + 1) V a ((K.d p (p + 1)).val.app V k)
  have hX : (θ.N V).X (P.pairElt U K q p V a k) = (θ.θ V).extend (P.pairElt U K q p V a k) := rfl
  rw [hX]
  unfold pairElt
  rw [GenData.extend_tmul, hθ V p k, GCDga.sigma_of_mem (P.D.𝒜 V.unop.left) a.2,
    Tot.smul_tmul]
  congr 1
  rw [mul_one, Tot.tmul_units_smul, Units.smul_def]
  rfl

/-- An adjunction hom-equivalence with additive right adjoint is additive. -/
private theorem adj_homEquiv_add {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive] {A : C} {B : D}
    (f g : F.obj A ⟶ B) :
    adj.homEquiv A B (f + g) = adj.homEquiv A B f + adj.homEquiv A B g := by
  simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add]

/-- An adjunction hom-equivalence with additive right adjoint commutes with `ℤ`-scalars. -/
private theorem adj_homEquiv_zsmul {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.Additive] {A : C} {B : D}
    (z : ℤ) (f : F.obj A ⟶ B) :
    adj.homEquiv A B (z • f) = z • adj.homEquiv A B f := by
  simp only [Adjunction.homEquiv_unit, Functor.map_zsmul, Preadditive.comp_zsmul]

-- heavy defeq between the adjunction's `forget ⋙ restrictScalars 𝟙` and `forget`
set_option maxHeartbeats 2000000 in
include hθ in
/-- The Leibniz rule for the components `Φc` (transpose of `φPre_TD`). -/
private theorem Φc_TD (q p n : ℤ) (h : q + p = n) :
    P.Φc U K q p n h ≫ θ.TD n =
      (((tensorBifunctor (P.O.over U)).map ((P.Atil U).d q (q + 1))).app (K.X p) ≫
          P.Φc U K (q + 1) p (n + 1) (by omega) :
        ((tensorBifunctor (P.O.over U)).obj (P.AqU U q)).obj (K.X p) ⟶ P.TShO U K (n + 1)) +
      (((q.negOnePow : ℤ) • ((tensorBifunctor (P.O.over U)).obj (P.AqU U q)).map
            (K.d p (p + 1))) ≫ P.Φc U K q (p + 1) (n + 1) (by omega) :
        ((tensorBifunctor (P.O.over U)).obj (P.AqU U q)).obj (K.X p) ⟶ P.TShO U K (n + 1)) := by
  have e1 : ((tensorBifunctor (P.O.over U)).map ((P.Atil U).d q (q + 1))).app (K.X p) =
      (sheafifyF (P.O.over U)).map
        (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          ((P.Atil U).d q (q + 1)).val (K.X p).val) := rfl
  have e2 : ((tensorBifunctor (P.O.over U)).obj (P.AqU U q)).map (K.d p (p + 1)) =
      (sheafifyF (P.O.over U)).map
        (MonoidalCategory.whiskerLeft (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          (P.AqU U q).val (K.d p (p + 1)).val) := rfl
  rw [e1, e2]
  apply ((PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv _ _).injective
  erw [adj_homEquiv_add, Preadditive.zsmul_comp]
  have hz := adj_homEquiv_zsmul (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)) (q.negOnePow : ℤ)
    ((sheafifyF (P.O.over U)).map
        (MonoidalCategory.whiskerLeft (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          (P.AqU U q).val (K.d p (p + 1)).val) ≫ P.Φc U K q (p + 1) (n + 1) (by omega))
  erw [hz]
  have h2 : ∀ q p n (h : q + p = n), ((PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf (P.O.over U)).obj)).homEquiv _ _) (P.Φc U K q p n h) = P.φPre U K q p n h :=
    fun q p n h => P.Φc_equiv U K q p n h
  have hA1 := (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv_naturality_left
    (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          ((P.Atil U).d q (q + 1)).val (K.X p).val) (P.Φc U K (q + 1) p (n + 1) (by omega))
  have hA2 := (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv_naturality_left
    (MonoidalCategory.whiskerLeft (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          (P.AqU U q).val (K.d p (p + 1)).val) (P.Φc U K q (p + 1) (n + 1) (by omega))
  have hB := (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv_naturality_right (P.Φc U K q p n h) (θ.TD n)
  erw [hA1, hA2, hB, h2, h2, h2]
  have key := P.φPre_TD U K θ hθ q p n h
  erw [Preadditive.comp_zsmul] at key
  exact key

-- many `erw` steps through the `tensorC` / `mapBifunctor` unfolding exceed the default budget
set_option maxHeartbeats 1000000 in
include hθ in
/-- `Φn` commutes with the differentials. -/
private theorem Φn_TD (n : ℤ) :
    P.Φn U K n ≫ θ.TD n = (tensorC (P.O.over U) (P.Atil U) K).d n (n + 1) ≫ P.Φn U K (n + 1) := by
  refine tensorC_hom_ext (P.O.over U) (P.Atil U) K n fun q p hqp => ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (· ≫ θ.TD n) (P.ι_Φn U K n q p hqp)) ?_
  refine Eq.trans (P.Φc_TD U K θ hθ q p n hqp) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  have h1 : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
  have h2 : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
  have hd : tensorCι (P.O.over U) (P.Atil U) K q p n hqp ≫
      (tensorC (P.O.over U) (P.Atil U) K).d n (n + 1) =
      (((tensorBifunctor (P.O.over U)).map ((P.Atil U).d q (q + 1))).app (K.X p) ≫
        tensorCι (P.O.over U) (P.Atil U) K (q + 1) p (n + 1) (by omega) :
        ((tensorBifunctor (P.O.over U)).obj (P.AqU U q)).obj (K.X p) ⟶
          (tensorC (P.O.over U) (P.Atil U) K).X (n + 1)) +
      (q.negOnePow : ℤ) • (((tensorBifunctor (P.O.over U)).obj (P.AqU U q)).map
        (K.d p (p + 1)) ≫ tensorCι (P.O.over U) (P.Atil U) K q (p + 1) (n + 1) (by omega)) := by
    unfold tensorCι tensorC
    erw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ h1 p (n + 1)
        (show q + 1 + p = n + 1 by omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ q h2 (n + 1)
        (show q + (p + 1) = n + 1 by omega)]
    have e1 : (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q, p) = 1 := rfl
    have e2 : (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q, p) =
        q.negOnePow := rfl
    rw [e1, e2, one_smul]
    congr 1
  rw [hd]
  erw [Preadditive.add_comp, Preadditive.zsmul_comp, Preadditive.zsmul_comp, Category.assoc,
    Category.assoc]
  erw [P.ι_Φn U K (n + 1) (q + 1) p (by omega), P.ι_Φn U K (n + 1) q (p + 1) (by omega)]
  exact rfl

/-- The chain map `Φ : 𝒜^•|U ⊗ K ⟶ T(K)`, `a ⊗ k ↦ a ⊗ η k`. -/
private def ΦC (hθ : P.IsBCConn U K θ) : tensorC (P.O.over U) (P.Atil U) K ⟶ θ.TC where
  f n := P.Φn U K n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e1 : θ.TC.d i (i + 1) = θ.TD i := CochainComplex.of_d _ _ _
    rw [e1]
    exact P.Φn_TD U K θ hθ i

/-- `Φ` is an isomorphism of complexes (`isIso_Φn` in each degree). -/
private theorem isIso_ΦC (hθ : P.IsBCConn U K θ) : IsIso (P.ΦC U K θ hθ) := by
  haveI : ∀ n, IsIso ((P.ΦC U K θ hθ).f n) := fun n => P.isIso_Φn U K n
  exact HomologicalComplex.Hom.isIso_of_components _

end Chain

/-! ### `K ≅ O|U[0] ⊗ K` and compatibility with `ιT` -/

/-- `K ≅ O|U[0] ⊗ K`: the unit isomorphism `O ⊗ - ≅ 𝟭`, `tensorCSingleIso`, and
`(O[0])|U ≅ (O|U)[0]`. -/
private def uIso : K ≅ tensorC (P.O.over U)
    (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single (Mod P.R) (ComplexShape.up ℤ) 0).obj
        (SheafOfModules.unit P.R))) K :=
  ((NatIso.mapHomologicalComplex (unitTensorIso (P.O.over U)) (ComplexShape.up ℤ)).app K).symm ≪≫
    (tensorCSingleIso (P.O.over U) (SheafOfModules.unit _) K).symm ≪≫
    tensorCIso₁ (P.O.over U) ((HomologicalComplex.singleMapHomologicalComplex (restr P.R U)
      (ComplexShape.up ℤ) 0).app (SheafOfModules.unit P.R)).symm K

/-- The transpose of the unit isomorphism `unit ⊗ N ≅ N` is the left unitor `leftU'`. -/
private theorem homEquiv_unitTensorIso (N : Mod (ringOf (P.O.over U))) :
    ((PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf (P.O.over U)).obj)).homEquiv _ _) ((unitTensorIso (P.O.over U)).hom.app N) =
      leftU' (P.O.over U) N := by
  have := isIso_tensorUnit (P.O.over U) (isFinFreeSummand_unit _) N
  have h1 : (SheafOfModules.forget (ringOf (P.O.over U))).map
      ((unitTensorIso (P.O.over U)).hom.app N) = (unitTensorPre (P.O.over U) N).hom :=
    Functor.map_preimage _ _
  have e1 : (unitTensorPre (P.O.over U) N).hom =
      inv (tensorUnit (P.O.over U) (SheafOfModules.unit (ringOf (P.O.over U))) N) ≫
        leftU' (P.O.over U) N := rfl
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  show tensorUnit (P.O.over U) (SheafOfModules.unit (ringOf (P.O.over U))) N ≫
    (SheafOfModules.forget (ringOf (P.O.over U))).map
      ((unitTensorIso (P.O.over U)).hom.app N) = _
  rw [h1, e1, IsIso.hom_inv_id_assoc]

/-- `Φc_ρ` at the presheaf level, on generators `r ⊗ k`. -/
private theorem Φc_ρ_pre [CompactSpace X] (p : ℤ) :
    MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
        ((restr P.R U).map P.ρO).val (K.X p).val ≫ P.φPre U K 0 p p (zero_add p) =
      leftU' (P.O.over U) (K.X p) ≫ (SheafOfModules.forget _).map (ιTn p) := by
  refine PresheafOfModules.hom_ext fun V => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun r k => ?_
  refine Subtype.ext ?_
  change P.pairElt U K 0 p V (P.ρV V.unop.left (r : P.O.obj.obj (op V.unop.left))) k =
    (ιTV p V ((show (P.R.over U).obj.obj V from r) • k)).1
  have h := congrArg Subtype.val (ιTfun_smul (P := P) (U := U) (K := K) p V
    (show (P.R.over U).obj.obj V from r) k)
  refine Eq.trans ?_ h.symm
  show Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V)
      ((P.ρ V.unop.left (r : P.O.obj.obj (op V.unop.left)) : P.D.A V.unop.left))
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k)) =
    (P.ρ V.unop.left (r : P.O.obj.obj (op V.unop.left)) : P.D.A V.unop.left) •
      Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k))
  rw [Tot.smul_tmul, mul_one]

/-- On generators: `(ρ|U ⊗ K^p) ≫ Φ_{0,p} = (O ⊗ K^p ≅ K^p) ≫ ιT^p`, i.e.
`ρ(r) ⊗ η k = r · (1 ⊗ η k)`. -/
private theorem Φc_ρ [CompactSpace X] (p : ℤ) :
    ((tensorBifunctor (P.O.over U)).map ((restr P.R U).map P.ρO)).app (K.X p) ≫
        P.Φc U K 0 p p (zero_add p) =
      (unitTensorIso (P.O.over U)).hom.app (K.X p) ≫ ιTn p := by
  have e1 : ((tensorBifunctor (P.O.over U)).map ((restr P.R U).map P.ρO)).app (K.X p) =
      (sheafifyF (P.O.over U)).map
        (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          ((restr P.R U).map P.ρO).val (K.X p).val) := rfl
  rw [e1]
  apply ((PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv _ _).injective
  have hA := (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv_naturality_left
    (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
      ((restr P.R U).map P.ρO).val (K.X p).val) (P.Φc U K 0 p p (zero_add p))
  have hB := (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv_naturality_right
    ((unitTensorIso (P.O.over U)).hom.app (K.X p)) (ιTn p)
  erw [hA, hB, P.Φc_equiv U K 0 p p (zero_add p), P.homEquiv_unitTensorIso U (K.X p)]
  exact P.Φc_ρ_pre U K p

/-- Degree `p` of `A[0] ⊗ K ≅ F(A)(K) ⟵ ⋯ ⟶ 𝒜^•|U ⊗ K ⟶ T`: it is `F(sOS⁻¹ ≫ γ₀)` followed by
`Φc`. -/
private theorem single_comp_Φ [CompactSpace X] (A : Mod (ringOf (P.O.over U)))
    (γ : (HomologicalComplex.single (Mod (ringOf (P.O.over U))) (ComplexShape.up ℤ) 0).obj A ⟶
      P.Atil U) (p : ℤ) (θ : P.Conn U (P.FK U K)) (hθ : P.IsBCConn U K θ) :
    (tensorCSingleIso (P.O.over U) A K).inv.f p ≫ (tensorCMap₁ (P.O.over U) γ K).f p ≫
        (P.ΦC U K θ hθ).f p =
      ((tensorBifunctor (P.O.over U)).map
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫ γ.f 0)).app (K.X p) ≫
        P.Φc U K 0 p p (zero_add p) := by
  refine (single_comp_tensorC (P.O.over U) γ p ((P.ΦC U K θ hθ).f p)).trans ?_
  exact congrArg _ (P.ι_Φn U K p 0 p (zero_add p))

/-- `ιT = u ≫ (ρ̂|U ⊗ K) ≫ Φ`. -/
private theorem ιT_eq [CompactSpace X] (θ : P.Conn U (P.FK U K)) (hθ : P.IsBCConn U K θ) :
    ιT θ hθ = (P.uIso U K).hom ≫ tensorCMap₁ (P.O.over U)
        (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map P.ρhat) K ≫
      P.ΦC U K θ hθ := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  have hγ : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((restr P.R U).obj (SheafOfModules.unit P.R))).inv ≫
      (((HomologicalComplex.singleMapHomologicalComplex (restr P.R U) (ComplexShape.up ℤ) 0).inv.app
        (SheafOfModules.unit P.R)) ≫
        ((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map P.ρhat).f 0 =
      (restr P.R U).map P.ρO := by
    rw [HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp only [Functor.mapHomologicalComplex_map_f, PreResolvingData.ρhat,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Functor.map_comp]
    refine congrArg _ ?_
    erw [HomologicalComplex.mkHomFromSingle_f]
    exact Iso.inv_hom_id_assoc _ _
  have hu : (P.uIso U K).hom =
      ((NatIso.mapHomologicalComplex (unitTensorIso (P.O.over U)) (ComplexShape.up ℤ)).app K).inv ≫
        ((tensorCSingleIso (P.O.over U) (SheafOfModules.unit _) K).inv ≫
          tensorCMap₁ (P.O.over U) ((HomologicalComplex.singleMapHomologicalComplex (restr P.R U)
            (ComplexShape.up ℤ) 0).inv.app (SheafOfModules.unit P.R)) K) := rfl
  rw [hu]
  refine Eq.trans ?_ (chain_f (P.O.over U)
    ((NatIso.mapHomologicalComplex (unitTensorIso (P.O.over U)) (ComplexShape.up ℤ)).app K).inv
    (tensorCSingleIso (P.O.over U) (SheafOfModules.unit _) K).inv
    ((HomologicalComplex.singleMapHomologicalComplex (restr P.R U) (ComplexShape.up ℤ) 0).inv.app
      (SheafOfModules.unit P.R))
    (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map P.ρhat)
    (P.ΦC U K θ hθ) p).symm
  have h3 := P.single_comp_Φ U K (SheafOfModules.unit _)
    (((HomologicalComplex.singleMapHomologicalComplex (restr P.R U) (ComplexShape.up ℤ) 0).inv.app
      (SheafOfModules.unit P.R)) ≫
      ((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map P.ρhat) p θ hθ
  erw [hγ] at h3
  refine Eq.trans ?_ (congrArg (fun t => ((NatIso.mapHomologicalComplex
    (unitTensorIso (P.O.over U)) (ComplexShape.up ℤ)).app K).inv.f p ≫ t) h3).symm
  show ιTn p = (unitTensorIso (P.O.over U)).inv.app (K.X p) ≫ _
  refine Eq.trans ?_ (congrArg (fun t => (unitTensorIso (P.O.over U)).inv.app (K.X p) ≫ t)
    (P.Φc_ρ U K p)).symm
  exact (Iso.inv_hom_id_app_assoc (unitTensorIso (P.O.over U)) (K.X p) (ιTn p)).symm

/-- **C7.d. `T(K) ≅ 𝒜^•|U ⊗ K`.** For a connection with `∇(η k) = 0`, `T(K)` is isomorphic to
`tensorC (𝒜^•|U) K` (S8), and under this isomorphism and `K ≅ O|U[0] ⊗ K`, `ιT` is `ρ̂|U ⊗ K`.
Proof: the presheaf map `𝒜^q(V) ⊗_{R(V)} K^p(V) → T(K)(V)`, `a ⊗ k ↦ a ⊗ η k`, is locally
bijective (a retract of a finite power of the unit of sheafification, C7.a), so it induces an
isomorphism from the sheafification; differentials compared on `a ⊗ k`. -/
theorem exists_TC_iso_tensorC [CompactSpace X] (θ : P.Conn U (P.FK U K))
    (hθ : P.IsBCConn U K θ) :
    ∃ (e : θ.TC ≅ tensorC (P.O.over U)
        (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.dgaComplex) K)
      (u : K ≅ tensorC (P.O.over U)
        (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (Mod P.R) (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit P.R))) K),
      ιT θ hθ ≫ e.hom = u.hom ≫ tensorCMap₁ (P.O.over U)
        (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map P.ρhat) K := by
  haveI := P.isIso_ΦC U K θ hθ
  refine ⟨(asIso (P.ΦC U K θ hθ)).symm, P.uIso U K, ?_⟩
  refine (Iso.comp_inv_eq (asIso (P.ΦC U K θ hθ))).2 ?_
  exact (P.ιT_eq U K θ hθ).trans (Category.assoc _ _ _).symm

end PreResolvingData

namespace ResolvingData

variable (D : ResolvingData X) (U : Opens X) (K : CochainComplex (Mod (D.R.over U)) ℤ)

/-- **C7.d.** For `K` K-flat, `ιT : K → T(K)` is a quasi-isomorphism: by
`exists_TC_iso_tensorC` it is `ρ̂|U ⊗ K`, and `ρ̂|U` is a quasi-isomorphism (`quasiIso_ρhat`,
restriction is exact), preserved by `- ⊗ K` for K-flat `K` (S8, as in C5 step 6). -/
theorem quasiIso_ιT [CompactSpace X] (hK : IsKFlat (D.O.over U) K)
    (θ : D.Conn U (D.FK U K)) (hθ : D.IsBCConn U K θ) : QuasiIso (D.ιT θ hθ) := by
  obtain ⟨e, u, h⟩ := D.exists_TC_iso_tensorC U K θ hθ
  have hρ : QuasiIso (((restr D.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map D.ρhat) :=
    haveI := D.quasiIso_ρhat
    inferInstance
  have hc := (quasiIso_iff_acyclic_mappingCone
    (((restr D.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map D.ρhat)).1 hρ
  have h1 := hK _ hc
  have h2 : QuasiIso (tensorCMap₁ (D.O.over U)
      (((restr D.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map D.ρhat) K) := by
    refine (quasiIso_iff_acyclic_mappingCone _).2 ?_
    exact fun i => (h1 i).of_iso
      ((tensorCSymIso (D.O.over U) _ _).symm ≪≫ tensorCConeIso₁ (D.O.over U) _ K)
  have hu : QuasiIso u.hom := by
    have := Iso.isIso_hom u
    exact quasiIso_of_isIso _
  have he : QuasiIso e.hom := by
    have := Iso.isIso_hom e
    exact quasiIso_of_isIso _
  have h3 : QuasiIso (D.ιT θ hθ ≫ e.hom) := by
    rw [h]
    exact quasiIso_comp _ _ (hφ := hu) (hφ' := h2)
  exact (quasiIso_iff_comp_right (D.ιT θ hθ) e.hom).1 h3

end ResolvingData

end Cohesive
