import Cohesivemodules.Comparison.ModelCritFil

set_option linter.style.header false

/-!
# C7.f: the quasi-isomorphism criterion for maps of `T`-complexes (part 4 of 4)

Split from `Comparison/ModelCrit.lean` for size;
continues `Comparison/ModelCritFil.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace DirectSum
variable {X : Type} [TopologicalSpace X]
namespace PreResolvingData
variable {P : PreResolvingData X} {U : Opens X}
  {F₁ F₂ : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ}
namespace ConnHom
variable {θ₁ : P.Conn U F₁} {θ₂ : P.Conn U F₂} (Φ : ConnHom θ₁ θ₂)

section GrQuasi

variable [CompactSpace X]

/-- The functionals of `D` are compatible with the restriction along `f`. -/
private theorem DualData.hc' {b : ℕ} (D : DualData P b) (j : Fin D.m) {V W : (Over U)ᵒᵖ}
    (f : V ⟶ W) (a : ↥(GCDga.piece (P.D.𝒜 V.unop.left) (b : ℤ)))
    (b' : ↥(GCDga.piece (P.D.𝒜 W.unop.left) (b : ℤ)))
    (hab : (b' : P.D.A W.unop.left) = P.D.res (leOfHom f.unop.left) a) :
    D.c j W.unop.left b' = (P.D.res (leOfHom f.unop.left)).f0 (D.c j V.unop.left a) := by
  have : b' = P.resPiece b (leOfHom f.unop.left) a := Subtype.ext hab
  subst this
  exact D.hc j _ _ _ a

/-- The coordinate `c_j(x)_{n-b}` on sections of `gr^b T^n`. -/
private def iV {b : ℕ} (D : DualData P b) (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    (j : Fin D.m) (n : ℤ) (V : (Over U)ᵒᵖ) :
    ↥((GrSub F b n).obj V) →ₗ[(P.R.over U).obj.obj V]
      ↑(((resρ P U).obj (F.X (n + -(b : ℤ)))).val.obj V) where
  toFun x := crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ)) x.1.1
  map_add' x y := map_add (crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ))) x.1.1 y.1.1
  map_smul' r x := by
    show crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ)) (P.ρ V.unop.left r • x.1.1) =
      P.ρ V.unop.left r • crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ)) x.1.1
    exact map_smul _ _ _

/-- The coordinate map `gr^b T^n → Res F^{n-b}`. -/
private def iMor {b : ℕ} (D : DualData P b) (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    (j : Fin D.m) (n : ℤ) :
    (GrSub F b n).toSheafOfModules ⟶ (resρ P U).obj (F.X (n + -(b : ℤ))) :=
  ⟨{ app := fun V ↦ ConcreteCategory.ofHom (iV D F j n V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact crdL_map b (fun j => D.c j V.unop.left) (fun j => D.c j W.unop.left)
         (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
         (fun p => P.fRes_smul U F f p) (fun j a b' hab => D.hc' j f a b' hab) j
         (n + -(b : ℤ)) x.1.1 }⟩

/-- `s_j ⊗ z` has total degree `n`. -/
private theorem recL_mem_totDeg {b : ℕ} (D : DualData P b)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (j : Fin D.m) (n : ℤ)
    (V : (Over U)ᵒᵖ) (z : P.FSec U F (n + -(b : ℤ)) V) :
    recL b (fun j => D.s j V.unop.left) j (n + -(b : ℤ)) z ∈
      totDeg (P.D.𝒜 V.unop.left) (P.FSec U F · V) n := by
  have hs : ((D.s j V.unop.left : ↥(GCDga.piece (P.D.𝒜 V.unop.left) (b : ℤ))) :
      P.D.A V.unop.left) ∈ P.D.𝒜 V.unop.left (b : ℤ) := (D.s j V.unop.left).2
  have := tmul_mem_totDeg (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U F · V)) hs z
  rw [show (b : ℤ) + (n + -(b : ℤ)) = n by ring] at this
  exact this

/-- `s_j ⊗ z` is pure of form degree `b`. -/
private theorem recL_pure {b : ℕ} (D : DualData P b)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (j : Fin D.m) (p : ℤ)
    (V : (Over U)ᵒᵖ) (z : P.FSec U F p V) :
    Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ)
        (recL b (fun j => D.s j V.unop.left) j p z) =
      recL b (fun j => D.s j V.unop.left) j p z := by
  have hs : ((D.s j V.unop.left : ↥(GCDga.piece (P.D.𝒜 V.unop.left) (b : ℤ))) :
      P.D.A V.unop.left) ∈ P.D.𝒜 V.unop.left (b : ℤ) := (D.s j V.unop.left).2
  show Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) (Tot.tmul _ _ _ _) = Tot.tmul _ _ _ _
  rw [Tot.projF_tmul_of_mem hs, if_pos rfl]

/-- The reconstruction `z ↦ s_j ⊗ z` on sections. -/
private def rV {b : ℕ} (D : DualData P b) (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    (j : Fin D.m) (n : ℤ) (V : (Over U)ᵒᵖ) :
    ↑(((resρ P U).obj (F.X (n + -(b : ℤ)))).val.obj V) →ₗ[(P.R.over U).obj.obj V]
      ↥((GrSub F b n).obj V) where
  toFun z := ⟨⟨recL (Q := (P.FSec U F · V)) b (fun j => D.s j V.unop.left) j (n + -(b : ℤ)) z,
    recL_mem_totDeg D F j n V z⟩, (mem_GrSub F b n V _).2 (recL_pure D F j _ V z)⟩
  map_add' z z' := Subtype.ext (Subtype.ext
    (map_add (recL (Q := (P.FSec U F · V)) b (fun j => D.s j V.unop.left) j
      (n + -(b : ℤ))) z z'))
  map_smul' r z := Subtype.ext (Subtype.ext
    (map_smul (recL (Q := (P.FSec U F · V)) b (fun j => D.s j V.unop.left) j
      (n + -(b : ℤ))) (P.ρ V.unop.left r) (show P.FSec U F (n + -(b : ℤ)) V from z)))

/-- Coordinates of `𝕏 x` for `x ∈ F^b` (index form: `p + 1 = p'`). -/
private theorem crd_X_rel {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} (θ : P.Conn U F)
    {b : ℕ} (D : DualData P b) (j : Fin D.m) (V : (Over U)ᵒᵖ) (p p' : ℤ) (hp : p + 1 = p')
    {x : P.TTot U F V}
    (hx : x ∈ filTot (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ)) :
    crdL b (fun j => D.c j V.unop.left) j p' ((θ.N V).X x) =
      (b : ℤ).negOnePow • ((F.d p p').val.app V).hom
        (crdL b (fun j => D.c j V.unop.left) j p x) := by
  subst hp
  refine (crdL_X b (fun j => D.c j V.unop.left) (θ.N V) j p hx).trans ?_
  exact congrArg _ (X0comp_N θ V p _)

/-- `π_b 𝕏 (s_j ⊗ z)` (index form: `p + 1 = p'`). -/
private theorem projF_X_recL_rel {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ}
    (θ : P.Conn U F) {b : ℕ} (D : DualData P b) (j : Fin D.m) (V : (Over U)ᵒᵖ) (p p' : ℤ)
    (hp : p + 1 = p') (z : P.FSec U F p V) :
    Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ)
        ((θ.N V).X (recL b (fun j => D.s j V.unop.left) j p z)) =
      (b : ℤ).negOnePow • recL (Q := (P.FSec U F · V)) b (fun j => D.s j V.unop.left) j p'
        (((F.d p p').val.app V).hom z) := by
  subst hp
  refine (projF_X_recL b (fun j => D.s j V.unop.left) (θ.N V) j p z).trans ?_
  exact congrArg _ (congrArg _ (X0comp_N θ V p _))

/-- The reconstruction `Res F^{n-b} → gr^b T^n`. -/
private def rMor {b : ℕ} (D : DualData P b) (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    (j : Fin D.m) (n : ℤ) :
    (resρ P U).obj (F.X (n + -(b : ℤ))) ⟶ (GrSub F b n).toSheafOfModules :=
  ⟨{ app := fun V ↦ ConcreteCategory.ofHom (rV D F j n V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun z => ?_
       refine Subtype.ext (Subtype.ext ?_)
       exact (recL_map b (fun j => D.s j V.unop.left) (fun j => D.s j W.unop.left)
         (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
         (fun p => P.fRes_smul U F f p) (fun j => D.hs j _ _ _) j (n + -(b : ℤ)) z).symm }⟩

/-- The shifted restricted complex `Res F⟦-b⟧`. -/
private abbrev Kc (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (b : ℕ) :
    CochainComplex (Mod (P.R.over U)) ℤ :=
  (shiftFunctor (CochainComplex (Mod (P.R.over U)) ℤ) (-(b : ℤ))).obj
    (((resρ P U).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)

/-- The coordinate map as a chain map `gr^b T(θ) → Res F⟦-b⟧`. -/
private def iC {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} (θ : P.Conn U F) {b : ℕ}
    (D : DualData P b) (j : Fin D.m) : GrC θ b ⟶ Kc F b where
  f n := iMor D F j n
  comm' i k hik := by
    obtain rfl : i + 1 = k := hik
    show iMor D F j i ≫ ((-(b : ℤ)).negOnePow •
      (resρ P U).map (F.d (i + -(b : ℤ)) (i + 1 + -(b : ℤ)))) =
      (GrC θ b).d i (i + 1) ≫ iMor D F j (i + 1)
    simp only [GrC, CochainComplex.of_d]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    have hxf : x.1.1 ∈ filTot (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) := by
      have h1 := (mem_GrSub F b i V _).1 x.2
      have h2 : Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) x.1.1 ∈
          filTot (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) := projF_mem_filTot _ _
      rwa [h1] at h2
    refine (units_smul_app ((resρ P U).map (F.d (i + -(b : ℤ)) (i + 1 + -(b : ℤ))))
      ((-(b : ℤ)).negOnePow) V (iV D F j i V x)).trans ?_
    show (((-(b : ℤ)).negOnePow : ℤˣ) : ℤ) • ((F.d (i + -(b : ℤ)) (i + 1 + -(b : ℤ))).val.app V).hom
        (crdL b (fun j => D.c j V.unop.left) j (i + -(b : ℤ)) x.1.1) =
      crdL b (fun j => D.c j V.unop.left) j (i + 1 + -(b : ℤ))
        (Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) ((θ.N V).X x.1.1))
    have e1 : crdL b (fun j => D.c j V.unop.left) j (i + 1 + -(b : ℤ))
        (Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ)
          ((θ.N V).X (x.1.1 : P.TTot U F V))) =
        crdL b (fun j => D.c j V.unop.left) j (i + 1 + -(b : ℤ))
          ((θ.N V).X (x.1.1 : P.TTot U F V)) :=
      crdL_projF b (fun j => D.c j V.unop.left) j _ _
    refine Eq.trans ?_ e1.symm
    refine Eq.trans ?_ (crd_X_rel θ D j V (i + -(b : ℤ)) (i + 1 + -(b : ℤ)) (by ring) hxf).symm
    rw [Int.negOnePow_neg, Units.smul_def]

/-- The reconstruction as a chain map `Res F⟦-b⟧ → gr^b T(θ)`. -/
private def rC {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} (θ : P.Conn U F) {b : ℕ}
    (D : DualData P b) (j : Fin D.m) : Kc F b ⟶ GrC θ b where
  f n := rMor D F j n
  comm' i k hik := by
    obtain rfl : i + 1 = k := hik
    show rMor D F j i ≫ (GrC θ b).d i (i + 1) =
      ((-(b : ℤ)).negOnePow • (resρ P U).map (F.d (i + -(b : ℤ)) (i + 1 + -(b : ℤ)))) ≫
        rMor D F j (i + 1)
    simp only [GrC, CochainComplex.of_d]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun z => ?_
    refine Subtype.ext (Subtype.ext ?_)
    have e1 := units_smul_app ((resρ P U).map (F.d (i + -(b : ℤ)) (i + 1 + -(b : ℤ))))
      ((-(b : ℤ)).negOnePow) V z
    refine (projF_X_recL_rel θ D j V (i + -(b : ℤ)) (i + 1 + -(b : ℤ)) (by ring) z).trans ?_
    show _ = recL (Q := (P.FSec U F · V)) b (fun j => D.s j V.unop.left) j (i + 1 + -(b : ℤ))
      (((((-(b : ℤ)).negOnePow • (resρ P U).map (F.d (i + -(b : ℤ)) (i + 1 + -(b : ℤ)))).val.app
        V).hom) z)
    rw [e1, Int.negOnePow_neg, Units.smul_def]
    exact (map_zsmul _ _ _).symm

/-- `∑_j s_j ⊗ c_j(x) = x` on sections of `gr^b T^n`. -/
private theorem sum_rV_iV {b : ℕ} (D : DualData P b)
    (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (n : ℤ) (V : (Over U)ᵒᵖ)
    (x : ↥((GrSub F b n).obj V)) : ∑ j, rV D F j n V (iV D F j n V x) = x := by
  refine Subtype.ext (Subtype.ext ?_)
  have h1 := (mem_GrSub F b n V _).1 x.2
  have h2 := projF_eq_sum b (fun j => D.c j V.unop.left) (fun j => D.s j V.unop.left)
    (D.he V.unop.left) x.1.2
  rw [h1] at h2
  refine Eq.trans ?_ h2.symm
  let y : Fin D.m → ↥((GrSub F b n).obj V) := fun j => rV D F j n V (iV D F j n V x)
  have h3 : (∑ j, y j).1 = ∑ j, (y j).1 := map_sum ((GrSub F b n).obj V).subtype y _
  have h4 : ∀ z : Fin D.m → P.TSec U F n V, (∑ j, z j).1 = ∑ j, (z j).1 :=
    fun z => map_sum (P.tDeg U F n V).subtype z _
  show (∑ j, y j).1.1 = _
  exact ((congrArg Subtype.val h3).trans (h4 (fun j => (y j).1))).trans rfl

/-- `∑_j i_j ≫ r_j = 𝟙` on `gr^b T(θ)`. -/
private theorem iC_rC_sum {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ}
    (θ : P.Conn U F) {b : ℕ} (D : DualData P b) :
    ∑ j : Fin D.m, (iC θ D j ≫ rC θ D j) = 𝟙 (GrC θ b) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  have h : (HomologicalComplex.eval (Mod (P.R.over U)) (ComplexShape.up ℤ) n).map
      (∑ j : Fin D.m, (iC θ D j ≫ rC θ D j)) =
      ∑ j : Fin D.m, (HomologicalComplex.eval (Mod (P.R.over U)) (ComplexShape.up ℤ) n).map
        (iC θ D j ≫ rC θ D j) := Functor.map_sum _ _ _
  refine h.trans ?_
  show ∑ j : Fin D.m, (iMor D F j n ≫ rMor D F j n) = 𝟙 _
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  rw [sum_app_apply]
  exact sum_rV_iV D F n V x

/-- The map `Res F₁⟦-b⟧ → Res F₂⟦-b⟧` induced by the `(0,0)`-component. -/
private abbrev Sc (Φ : ConnHom θ₁ θ₂) (b : ℕ) : Kc F₁ b ⟶ Kc F₂ b :=
  (shiftFunctor (CochainComplex (Mod (P.R.over U)) ℤ) (-(b : ℤ))).map
    (((resρ P U).mapHomologicalComplex (ComplexShape.up ℤ)).map Φ.T0Map)

private theorem iC_Sc (Φ : ConnHom θ₁ θ₂) {b : ℕ} (D : DualData P b) (j : Fin D.m) :
    iC θ₁ D j ≫ Sc Φ b = GrMap Φ b ≫ iC θ₂ D j := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  show iMor D F₁ j n ≫ (resρ P U).map (Φ.T0n (n + -(b : ℤ))) = GrMapN Φ b n ≫ iMor D F₂ j n
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  have h1 := (mem_GrSub F₁ b n V _).1 x.2
  have key : ∀ y : P.TTot U F₁ V, Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F₁ · V) (b : ℤ) y = y →
      Φ.T0V (n + -(b : ℤ)) V (crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ)) y) =
        crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ))
          (Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F₂ · V) (b : ℤ) (Φ.φ V y)) := fun y hy => by
    have h2 := crdL_hom_projF b (fun j => D.c j V.unop.left) (Φ.mem V).1 j (n + -(b : ℤ)) y
    have h3 : crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ))
        (Φ.φ V (Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F₁ · V) (b : ℤ) y)) =
        crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ)) (Φ.φ V y) :=
      congrArg (fun t => crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ)) (Φ.φ V t)) hy
    have h4 : crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ))
        (Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F₂ · V) (b : ℤ) (Φ.φ V y)) =
        crdL b (fun j => D.c j V.unop.left) j (n + -(b : ℤ)) (Φ.φ V y) :=
      crdL_projF b (fun j => D.c j V.unop.left) j _ _
    exact (h2.symm.trans (h3.trans h4.symm))
  exact key x.1.1 h1

private theorem Sc_rC (Φ : ConnHom θ₁ θ₂) {b : ℕ} (D : DualData P b) (j : Fin D.m) :
    Sc Φ b ≫ rC θ₂ D j = rC θ₁ D j ≫ GrMap Φ b := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  show (resρ P U).map (Φ.T0n (n + -(b : ℤ))) ≫ rMor D F₂ j n = rMor D F₁ j n ≫ GrMapN Φ b n
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun z => ?_
  refine Subtype.ext (Subtype.ext ?_)
  exact (projF_hom_recL b (fun j => D.s j V.unop.left) (Φ.mem V).1 j (n + -(b : ℤ)) z).symm

/-- `gr^b Φ` is a quasi-isomorphism if `T0Map` is: it is a retract of `m` copies of
`Res T0Map⟦-b⟧`. -/
private theorem quasiIso_GrMap (Φ : ConnHom θ₁ θ₂) (h : QuasiIso Φ.T0Map) (b : ℕ) :
    QuasiIso (GrMap Φ b) := by
  obtain ⟨D⟩ := exists_dualData P b
  haveI : Limits.HasFiniteBiproducts (CochainComplex (Mod (P.R.over U)) ℤ) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  have hS : QuasiIso (Sc Φ b) :=
    (CochainComplex.quasiIso_shift_iff _ _).2
      (quasiIso_restrictScalars
        (((Opens.grothendieckTopology X).overPullback RingCat U).map (ρS P)) Φ.T0Map)
  haveI : ∀ _ : Fin D.m, QuasiIso (Sc Φ b) := fun _ => hS
  haveI : QuasiIso (Limits.biproduct.map (fun _ : Fin D.m => Sc Φ b)) :=
    quasiIso_biproduct_map' _
  refine quasiIso_of_retractArrow (f := GrMap Φ b)
    (f' := Limits.biproduct.map (fun _ : Fin D.m => Sc Φ b)) ?_
  refine
    { i := Arrow.homMk (Limits.biproduct.lift fun j => iC θ₁ D j)
        (Limits.biproduct.lift fun j => iC θ₂ D j) ?_
      r := Arrow.homMk (Limits.biproduct.desc fun j => rC θ₁ D j)
        (Limits.biproduct.desc fun j => rC θ₂ D j) ?_
      retract := ?_ }
  · apply Limits.biproduct.hom_ext
    intro j
    simp only [Arrow.mk_hom, Category.assoc, Limits.biproduct.lift_π, Limits.biproduct.map_π]
    rw [← Category.assoc, Limits.biproduct.lift_π]
    exact iC_Sc Φ D j
  · apply Limits.biproduct.hom_ext'
    intro j
    simp only [Arrow.mk_hom, Limits.biproduct.ι_map_assoc, Limits.biproduct.ι_desc,
      Limits.biproduct.ι_desc_assoc]
    exact (Sc_rC Φ D j).symm
  · refine Arrow.hom_ext _ _ ?_ ?_
    · simp only [Arrow.comp_left, Arrow.id_left, Arrow.homMk_left, Limits.biproduct.lift_desc]
      exact iC_rC_sum θ₁ D
    · simp only [Arrow.comp_right, Arrow.id_right, Arrow.homMk_right, Limits.biproduct.lift_desc]
      exact iC_rC_sum θ₂ D

end GrQuasi

/-- **C7.f. Quasi-isomorphism criterion.** If the `(0,0)`-component `T0Map : F₁ → F₂` is a
quasi-isomorphism, then `TMap : T(θ₁) → T(θ₂)` is one. See the module doc for the proof plan
(form-degree filtration, A7, `gr^b` a retract of a finite power of `T0Map`). -/
theorem quasiIso_TMap [CompactSpace X] (h : QuasiIso Φ.T0Map) : QuasiIso Φ.TMap :=
  quasiIso_TMap_of_gr Φ fun b => quasiIso_GrMap Φ h b

end ConnHom

end PreResolvingData

end Cohesive
