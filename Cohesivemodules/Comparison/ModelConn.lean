import Cohesivemodules.Comparison.ModelConnNab

set_option linter.style.header false

/-!
# C7.b: the connection on `𝒜⁰ ⊗_R K` (part 2 of 2)

Split from `Comparison/ModelConn.lean` for size;
continues `Comparison/ModelConnNab.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace DirectSum
open scoped ChangeOfRings TensorProduct
variable {X : Type} [TopologicalSpace X]
namespace PreResolvingData
variable (P : PreResolvingData X) (U : Opens X) (K : CochainComplex (Mod (P.R.over U)) ℤ)

/-- `T^n` is separated: two sections of total degree `n` that agree locally agree. -/
private theorem tTot_ext_local [CompactSpace X] (n : ℤ) {V : (Over U)ᵒᵖ} (S : Sieve V.unop)
    (hS : S ∈ ((Opens.grothendieckTopology X).over U) V.unop)
    {x y : P.TTot U (P.FK U K) V} (hx : x ∈ P.tDeg U (P.FK U K) n V)
    (hy : y ∈ P.tDeg U (P.FK U K) n V)
    (h : ∀ ⦃W : Over U⦄ (g : W ⟶ V.unop), S g →
      P.tRes U (P.FK U K) g.op x = P.tRes U (P.FK U K) g.op y) : x = y := by
  have hsh := P.isSheaf_TPre U (P.FK U K) n
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type] at hsh
  have := ((hsh S hS).isSeparatedFor).ext (t₁ := (⟨x, hx⟩ : P.TSec U (P.FK U K) n V))
    (t₂ := ⟨y, hy⟩) (fun W g hg => Subtype.ext (h g hg))
  exact congrArg Subtype.val this

/-- `∇` with values in the total module. -/
private def nabT [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ) (f : P.FSec U (P.FK U K) p V) :
    P.TTot U (P.FK U K) V :=
  (nab P U K p V f).1

/-- `∇ f` has total degree `p + 1`. -/
private theorem nabT_mem [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ)
    (f : P.FSec U (P.FK U K) p V) : nabT P U K p V f ∈ P.tDeg U (P.FK U K) (p + 1) V :=
  (nab P U K p V f).2

/-- `∇` is additive. -/
private theorem nabT_add [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ)
    (f g : P.FSec U (P.FK U K) p V) :
    nabT P U K p V (f + g) = nabT P U K p V f + nabT P U K p V g := by
  unfold nabT
  rw [map_add]
  rfl

/-- `tRes` commutes with `∇`. -/
private theorem tRes_nabT [CompactSpace X] (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (x : P.FSec U (P.FK U K) p V) :
    P.tRes U (P.FK U K) f (nabT P U K p V x) = nabT P U K p W (P.fRes U (P.FK U K) p f x) :=
  congrArg Subtype.val (nab_res P U K p f x)

/-- `tRes` of `a ⊗ e` for `e` a generator. -/
private theorem tRes_tmul_lof (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (p : ℤ)
    {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (a : P.D.A V.unop.left) (y : P.FSec U F p V) :
    P.tRes U F f (Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U F · V) a
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) p y)) =
    Tot.tmul (P.D.𝒜 W.unop.left) (P.FSec U F · W) (P.D.res (leOfHom f.unop.left) a)
      (lof ↥(P.D.𝒜 W.unop.left 0) ℤ (P.FSec U F · W) p (P.fRes U F p f y)) := by
  rw [tRes_apply, totMapAlong_tmul, DirectSum.lof_eq_of, DirectSum.lof_eq_of, famMap_of]

/-- The pure tensor `s ⊗ k` in the presheaf-level tensor product. -/
private def tm (p : ℤ) (V : (Over U)ᵒᵖ) (s : ↥(P.D.𝒜 V.unop.left 0))
    (k : (K.X p).val.obj V) : (P0 P U K p).presheaf.obj V :=
  ((s : (P.A0.over U).obj.obj V) ⊗ₜ[(P.O.over U).obj.obj V,
    ((overHom P.ρSheaf U).hom.app V).hom] (k : secC (R := P.O.over U) (K.X p).val V) :
    bcObj (overHom P.ρSheaf U) (K.X p).val V)

/-- `s ⊗ k = s • (1 ⊗ k)`. -/
private theorem tm_eq_smul (p : ℤ) (V : (Over U)ᵒᵖ) (s : ↥(P.D.𝒜 V.unop.left 0))
    (k : (K.X p).val.obj V) :
    tm P U K p V s k = (show ((P.A0.over U).obj ⋙ forget₂ CommRingCat RingCat).obj V from s) •
      (show (P0 P U K p).obj V from tm P U K p V 1 k) :=
  bc_tmul_eq_smul ((overHom P.ρSheaf U).hom.app V).hom
    (M := secC (R := P.O.over U) (K.X p).val V) (s : (P.A0.over U).obj.obj V) k

/-- `unit(s ⊗ k) = s • η k`. -/
private theorem tsf_tm (p : ℤ) (V : (Over U)ᵒᵖ) (s : ↥(P.D.𝒜 V.unop.left 0))
    (k : (K.X p).val.obj V) : tsf P U K p V (tm P U K p V s k) = s • P.bcη U K p V k := by
  rw [tm_eq_smul, tsf_smul]
  rfl

/-- `∇(s • η k) = ds ⊗ η k`. -/
private theorem nabT_tm [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ) (s : ↥(P.D.𝒜 V.unop.left 0))
    (k : (K.X p).val.obj V) :
    nabT P U K p V (tsf P U K p V (tm P U K p V s k)) = nbTot P U K p V s k := by
  unfold nabT
  rw [nab_tsf]
  rfl

/-- The generator `a ⊗ e` with `e ∈ F^p(V)`. -/
private abbrev gT (p : ℤ) (V : (Over U)ᵒᵖ) (a : P.D.A V.unop.left)
    (f : P.FSec U (P.FK U K) p V) : P.TTot U (P.FK U K) V :=
  Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) a
    (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p f)

/-- Leibniz for `∇` on `α · (s • η k)`. -/
private theorem nabT_smul_tm [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ)
    (α s : ↥(P.D.𝒜 V.unop.left 0)) (k : (K.X p).val.obj V) :
    nabT P U K p V (α • tsf P U K p V (tm P U K p V s k)) =
      gT P U K p V (GCDga.d (𝒜 := P.D.𝒜 V.unop.left) (α : P.D.A V.unop.left))
        (tsf P U K p V (tm P U K p V s k)) +
      (α : P.D.A V.unop.left) • nabT P U K p V (tsf P U K p V (tm P U K p V s k)) := by
  have h1 : α • tsf P U K p V (tm P U K p V s k) = tsf P U K p V (tm P U K p V (α * s) k) := by
    rw [tsf_tm, tsf_tm, smul_smul]
  rw [h1, nabT_tm, nabT_tm, tsf_tm]
  unfold nbTot gT
  rw [map_smul, Tot.tmul_smul0, Tot.smul_tmul]
  have e : ((α * s : ↥(P.D.𝒜 V.unop.left 0)) : P.D.A V.unop.left) =
      (α : P.D.A V.unop.left) * (s : P.D.A V.unop.left) := rfl
  rw [e, GCDga.leibniz_zero _ α.2, Tot.add_tmul]

/-- `gT` is additive in the section. -/
private theorem gT_add (p : ℤ) (V : (Over U)ᵒᵖ) (a : P.D.A V.unop.left)
    (f g : P.FSec U (P.FK U K) p V) :
    gT P U K p V a (f + g) = gT P U K p V a f + gT P U K p V a g := by
  unfold gT
  rw [map_add, Tot.tmul_add]

/-- `dα ⊗ f` has total degree `p + 1`. -/
private theorem gT_mem (p : ℤ) (V : (Over U)ᵒᵖ) (a : ↥(P.D.𝒜 V.unop.left 0))
    (f : P.FSec U (P.FK U K) p V) :
    gT P U K p V (GCDga.d (𝒜 := P.D.𝒜 V.unop.left) (a : P.D.A V.unop.left)) f ∈
      P.tDeg U (P.FK U K) (p + 1) V := by
  have := tmul_mem_totDeg (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U (P.FK U K) · V))
    (GCDga.d_mem_one (𝒜 := P.D.𝒜 V.unop.left) a.2) f
  rwa [add_comm] at this

/-- **Leibniz rule for `∇`.** -/
private theorem nabT_smul [CompactSpace X] (p : ℤ) :
    ∀ (V : (Over U)ᵒᵖ) (f : P.FSec U (P.FK U K) p V) (α : ↥(P.D.𝒜 V.unop.left 0)),
      nabT P U K p V (α • f) =
        gT P U K p V (GCDga.d (𝒜 := P.D.𝒜 V.unop.left) (α : P.D.A V.unop.left)) f +
          (α : P.D.A V.unop.left) • nabT P U K p V f := by
  refine fsec_induction P U K p (fun V f => ∀ α : ↥(P.D.𝒜 V.unop.left 0),
    nabT P U K p V (α • f) =
        gT P U K p V (GCDga.d (𝒜 := P.D.𝒜 V.unop.left) (α : P.D.A V.unop.left)) f +
          (α : P.D.A V.unop.left) • nabT P U K p V f) ?_ ?_
  · intro V f S hS h α
    refine tTot_ext_local P U K (p + 1) S hS (nabT_mem P U K p V _) ?_ (fun W g hg => ?_)
    · refine add_mem (gT_mem P U K p V α f) ?_
      have := smul_mem_totDeg (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U (P.FK U K) · V))
        α.2 (nabT_mem P U K p V f)
      rwa [zero_add] at this
    · rw [tRes_nabT, P.fRes_smul U (P.FK U K) g.op p α f, h g hg, map_add, tRes_smul,
        tRes_nabT]
      unfold gT
      rw [tRes_tmul_lof]
      rw [DgaHom.map_d]
      rfl
  · intro V z α
    induction z using bc_induction with
    | ht s m => exact nabT_smul_tm P U K p V α s m
    | hadd x y hx hy =>
      erw [map_add]
      rw [smul_add, nabT_add, hx, hy, nabT_add, gT_add, smul_add]
      abel

/-- The differential of `F` is `𝒜⁰(V)`-linear. -/
private theorem fD_smul (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (p : ℤ)
    (V : (Over U)ᵒᵖ) (α : ↥(P.D.𝒜 V.unop.left 0)) (x : P.FSec U F p V) :
    P.fD U F p V (α • x) = α • P.fD U F p V x :=
  ((F.d p (p + 1)).val.app V).hom.map_smul α x

/-- The differential of `F` commutes with restriction. -/
private theorem fD_res (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (p : ℤ)
    {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.FSec U F p V) :
    P.fRes U F (p + 1) f (P.fD U F p V x) = P.fD U F p W (P.fRes U F p f x) :=
  (PresheafOfModules.naturality_apply (F.d p (p + 1)).val f x).symm

/-- `d² = 0` on sections of `F`. -/
private theorem fD_fD (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (p : ℤ)
    (V : (Over U)ᵒᵖ) (x : P.FSec U F p V) : P.fD U F (p + 1) V (P.fD U F p V x) = 0 := by
  have h := congrArg (fun φ => (φ.val.app V).hom x) (F.d_comp_d p (p + 1) (p + 1 + 1))
  exact h

/-- `d_F η k = η d_K k`. -/
private theorem fD_bcη (p : ℤ) (V : (Over U)ᵒᵖ) (k : (K.X p).val.obj V) :
    P.fD U (P.FK U K) p V (P.bcη U K p V k) = P.bcη U K (p + 1) V (P.kD U K p V k) := by
  have h := congrArg (fun φ => (φ.val.app V).hom k)
    ((sheafBCAdj (overHom P.ρSheaf U)).unit.naturality (K.d p (p + 1)))
  exact h.symm

/-- Sections of a sheaf `F^q` that agree locally agree. -/
private theorem fsec_ext_local (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (q : ℤ)
    {V : (Over U)ᵒᵖ} (S : Sieve V.unop)
    (hS : S ∈ ((Opens.grothendieckTopology X).over U) V.unop) {x y : P.FSec U F q V}
    (h : ∀ ⦃W : Over U⦄ (g : W ⟶ V.unop), S g → P.fRes U F q g.op x = P.fRes U F q g.op y) :
    x = y := by
  have hsh := (F.X q).isSheaf
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type] at hsh
  exact ((hsh S hS).isSeparatedFor).ext (fun W g hg => h g hg)

/-- Elements of `⨁ F^p(V)` that vanish locally vanish. -/
private theorem dsum_zero_local (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    {V : (Over U)ᵒᵖ} (S : Sieve V.unop)
    (hS : S ∈ ((Opens.grothendieckTopology X).over U) V.unop) (e : ⨁ p, P.FSec U F p V)
    (h : ∀ ⦃W : Over U⦄ (g : W ⟶ V.unop), S g →
      famMap (fun p => P.fRes U F p g.op) e = 0) : e = 0 := by
  refine DFinsupp.ext fun q => ?_
  refine fsec_ext_local P U F q S hS (fun W g hg => ?_)
  have := congrArg (fun z => z q) (h g hg)
  simp only [DirectSum.zero_apply] at this
  rw [famMap_apply_mdl] at this
  rw [this, DirectSum.zero_apply, map_zero]

/-- `ε` commutes with `tRes`. -/
private theorem eps_tRes (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
    {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.TTot U F V) :
    Tot.eps (P.D.𝒜 W.unop.left) (P.FSec U F · W) (P.tRes U F f x) =
      famMap (fun p => P.fRes U F p f) (Tot.eps (P.D.𝒜 V.unop.left) (P.FSec U F · V) x) :=
  eps_totMapAlong (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
    (fun p => P.fRes_smul U F f p) x

/-- The form-degree-`0` part of `∇ f` vanishes. -/
private theorem eps_nabT [CompactSpace X] (p : ℤ) :
    ∀ (V : (Over U)ᵒᵖ) (f : P.FSec U (P.FK U K) p V),
      Tot.eps (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) (nabT P U K p V f) = 0 := by
  refine fsec_induction P U K p (fun V f => Tot.eps (P.D.𝒜 V.unop.left)
    (P.FSec U (P.FK U K) · V) (nabT P U K p V f) = 0) ?_ ?_
  · intro V f S hS h
    refine dsum_zero_local P U (P.FK U K) S hS _ (fun W g hg => ?_)
    rw [← eps_tRes, tRes_nabT]
    exact h g hg
  · intro V z
    induction z using bc_induction with
    | ht s m =>
      have e : nabT P U K p V (tsf P U K p V (tm P U K p V s m)) = nbTot P U K p V s m :=
        nabT_tm P U K p V s m
      refine (congrArg _ e).trans ?_
      unfold nbTot
      rw [Tot.eps_tmul, Tot.proj0_of_mem_ne (GCDga.d_mem_one (𝒜 := P.D.𝒜 V.unop.left) s.2)
        one_ne_zero, zero_smul]
    | hadd x y hx hy =>
      erw [map_add]
      rw [nabT_add, map_add, hx, hy, add_zero]

/-- `1 ⊗ (f • z) = f • (1 ⊗ z)`. -/
private theorem gT_one_smul (p : ℤ) (V : (Over U)ᵒᵖ) (f : ↥(P.D.𝒜 V.unop.left 0))
    (z : P.FSec U (P.FK U K) p V) :
    gT P U K p V 1 (f • z) = (f : P.D.A V.unop.left) • gT P U K p V 1 z := by
  unfold gT
  rw [map_smul, Tot.tmul_smul0, Tot.smul_tmul, one_mul, mul_one]

/-- `θ_V` on the component `F^p(V)`: `f ↦ ∇f + 1 ⊗ d_F f`. -/
private def thAdd [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ) :
    P.FSec U (P.FK U K) p V →+ P.TTot U (P.FK U K) V :=
  AddMonoidHom.mk' (fun f => nabT P U K p V f +
    gT P U K (p + 1) V 1 (P.fD U (P.FK U K) p V f))
    (fun f g => by
      rw [nabT_add, map_add, gT_add]
      abel)

/-- `θ_V` on `⨁_p F^p(V)`. -/
private def thetaAdd [CompactSpace X] (V : (Over U)ᵒᵖ) :
    (⨁ p, P.FSec U (P.FK U K) p V) →+ P.TTot U (P.FK U K) V :=
  DirectSum.toAddMonoid (fun p => thAdd P U K p V)

/-- `θ_V` on a generator `lof p y`. -/
private theorem thetaAdd_of [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ)
    (y : P.FSec U (P.FK U K) p V) :
    thetaAdd P U K V (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p y) =
      nabT P U K p V y + gT P U K (p + 1) V 1 (P.fD U (P.FK U K) p V y) := by
  rw [DirectSum.lof_eq_of, thetaAdd, DirectSum.toAddMonoid_of]
  rfl

/-- The Leibniz rule for `θ_V`. -/
private theorem thetaAdd_leibniz [CompactSpace X] (V : (Over U)ᵒᵖ)
    (f : ↥(P.D.𝒜 V.unop.left 0)) (e : ⨁ p, P.FSec U (P.FK U K) p V) :
    thetaAdd P U K V (f • e) =
      Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V)
        (GCDga.d (𝒜 := P.D.𝒜 V.unop.left) f) e +
        (f : P.D.A V.unop.left) • thetaAdd P U K V e := by
  induction e using DirectSum.induction_on with
  | zero => rw [smul_zero, map_zero, Tot.tmul_zero, smul_zero, add_zero]
  | of p y =>
    have h : f • (DirectSum.of (P.FSec U (P.FK U K) · V) p y) =
        lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (f • y) :=
      (map_smul (DirectSum.lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p) f y).symm
    rw [h, thetaAdd_of, nabT_smul, P.fD_smul U (P.FK U K), gT_one_smul]
    have h2 : thetaAdd P U K V (DirectSum.of (P.FSec U (P.FK U K) · V) p y) =
        nabT P U K p V y + gT P U K (p + 1) V 1 (P.fD U (P.FK U K) p V y) :=
      thetaAdd_of P U K p V y
    rw [h2, smul_add]
    show gT P U K p V _ y + _ + _ = gT P U K p V _ y + _
    abel
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add, Tot.tmul_add, smul_add]
    abel

/-- The generator data `θ_V = ∇ + 1 ⊗ d_F` on `F^•(V)`. -/
private def theta [CompactSpace X] (V : (Over U)ᵒᵖ) :
    GenData (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) where
  θ := thetaAdd P U K V
  leibniz := thetaAdd_leibniz P U K V

/-- `∇ (η k) = 0`. -/
private theorem nabT_bcη [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ) (k : (K.X p).val.obj V) :
    nabT P U K p V (P.bcη U K p V k) = 0 := by
  have e : nabT P U K p V (tsf P U K p V (tm P U K p V 1 k)) = nbTot P U K p V 1 k :=
    nabT_tm P U K p V 1 k
  have e2 : P.bcη U K p V k = tsf P U K p V (tm P U K p V 1 k) := rfl
  rw [e2, e]
  unfold nbTot
  have h1 : ((1 : ↥(P.D.𝒜 V.unop.left 0)) : P.D.A V.unop.left) = 1 := rfl
  rw [h1, GCDga.d_one, Tot.zero_tmul]

/-- `θ(η k) = 1 ⊗ η(d k)`. -/
private theorem theta_bcη [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ) (k : (K.X p).val.obj V) :
    (theta P U K V).θ (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p
      (P.bcη U K p V k)) =
    Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) (p + 1)
        (P.bcη U K (p + 1) V (P.kD U K p V k))) := by
  show thetaAdd P U K V _ = _
  rw [thetaAdd_of, nabT_bcη, zero_add, fD_bcη]

/-- `1 ⊗ y` has total degree `p`. -/
private theorem gT_one_mem (p : ℤ) (V : (Over U)ᵒᵖ) (y : P.FSec U (P.FK U K) p V) :
    gT P U K p V 1 y ∈ totDeg (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) p := by
  have := tmul_mem_totDeg (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U (P.FK U K) · V))
    (SetLike.GradedOne.one_mem (A := P.D.𝒜 V.unop.left)) y
  rwa [zero_add] at this

/-- `θ_V` has total degree `1`. -/
private theorem theta_mem [CompactSpace X] (V : (Over U)ᵒᵖ) (p : ℤ)
    (e : P.FSec U (P.FK U K) p V) :
    (theta P U K V).θ (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p e) ∈
      totDeg (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) (p + 1) := by
  show thetaAdd P U K V _ ∈ _
  rw [thetaAdd_of]
  exact add_mem (nabT_mem P U K p V e) (gT_one_mem P U K (p + 1) V _)

/-- The form-degree-`0` part of `θ_V` is `d_F`. -/
private theorem theta_eps [CompactSpace X] (V : (Over U)ᵒᵖ) (p : ℤ)
    (e : P.FSec U (P.FK U K) p V) :
    Tot.eps (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V)
        ((theta P U K V).θ (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p e)) =
      lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) (p + 1)
        (P.fD U (P.FK U K) p V e) := by
  show Tot.eps _ _ (thetaAdd P U K V _) = _
  rw [thetaAdd_of, map_add, eps_nabT, zero_add]
  have := Tot.eps_oneTmul (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U (P.FK U K) · V))
    (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) (p + 1) (P.fD U (P.FK U K) p V e))
  rwa [Tot.oneTmul_apply] at this

/-- `θ` commutes with restriction. -/
private theorem theta_natural [CompactSpace X] {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (e : ⨁ p, P.FSec U (P.FK U K) p V) :
    P.tRes U (P.FK U K) f ((theta P U K V).θ e) =
      (theta P U K W).θ (famMap (fun p => P.fRes U (P.FK U K) p f) e) := by
  induction e using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | of p y =>
    have h2 : (theta P U K V).θ (DirectSum.of (P.FSec U (P.FK U K) · V) p y) =
        nabT P U K p V y + gT P U K (p + 1) V 1 (P.fD U (P.FK U K) p V y) :=
      thetaAdd_of P U K p V y
    rw [h2, famMap_of]
    have h3 : (theta P U K W).θ (DirectSum.of (P.FSec U (P.FK U K) · W) p
        (P.fRes U (P.FK U K) p f y)) =
        nabT P U K p W (P.fRes U (P.FK U K) p f y) +
          gT P U K (p + 1) W 1 (P.fD U (P.FK U K) p W (P.fRes U (P.FK U K) p f y)) :=
      thetaAdd_of P U K p W _
    rw [h3, map_add, tRes_nabT]
    unfold gT
    rw [tRes_tmul_lof, fD_res]
    exact congrArg (fun a => _ + Tot.tmul _ _ a _) (DgaHom.map_one' _)
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]
    exact (map_add (theta P U K W).θ _ _).symm

/-- `𝕏 ∇ + ∇ d_F = 0` on the image of the unit. -/
private theorem extNab_tm [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ)
    (s : ↥(P.D.𝒜 V.unop.left 0)) (k : (K.X p).val.obj V) :
    (theta P U K V).extend (nabT P U K p V (tsf P U K p V (tm P U K p V s k))) +
      nabT P U K (p + 1) V (P.fD U (P.FK U K) p V (tsf P U K p V (tm P U K p V s k))) = 0 := by
  have h1 : P.fD U (P.FK U K) p V (tsf P U K p V (tm P U K p V s k)) =
      tsf P U K (p + 1) V (tm P U K (p + 1) V s (P.kD U K p V k)) := by
    rw [tsf_tm, tsf_tm, P.fD_smul U (P.FK U K), fD_bcη]
  have e1 : nabT P U K p V (tsf P U K p V (tm P U K p V s k)) = nbTot P U K p V s k :=
    nabT_tm P U K p V s k
  have e2 : nabT P U K (p + 1) V
      (tsf P U K (p + 1) V (tm P U K (p + 1) V s (P.kD U K p V k))) =
      nbTot P U K (p + 1) V s (P.kD U K p V k) := nabT_tm P U K (p + 1) V s _
  rw [h1, e1, e2]
  unfold nbTot
  rw [GenData.extend_tmul, GCDga.d_d, Tot.zero_tmul, zero_add,
    GCDga.sigma_of_mem _ (GCDga.d_mem_one (𝒜 := P.D.𝒜 V.unop.left) s.2), theta_bcη,
    Int.negOnePow_one, Units.neg_smul, one_smul, neg_smul, Tot.smul_tmul, mul_one,
    neg_add_cancel]

/-- `tRes` commutes with the Leibniz extension of `θ`. -/
private theorem extend_tRes [CompactSpace X] {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (x : P.TTot U (P.FK U K) V) :
    P.tRes U (P.FK U K) f ((theta P U K V).extend x) =
      (theta P U K W).extend (P.tRes U (P.FK U K) f x) :=
  totMapAlong_extend (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U (P.FK U K) p f)
    (fun p => P.fRes_smul U (P.FK U K) f p) (theta P U K V) (theta P U K W)
    (fun e => theta_natural P U K f e) x

/-- `𝕏 ∇ + ∇ d_F = 0` everywhere. -/
private theorem extNab [CompactSpace X] (p : ℤ) :
    ∀ (V : (Over U)ᵒᵖ) (f : P.FSec U (P.FK U K) p V),
      (theta P U K V).extend (nabT P U K p V f) +
        nabT P U K (p + 1) V (P.fD U (P.FK U K) p V f) = 0 := by
  refine fsec_induction P U K p (fun V f => (theta P U K V).extend (nabT P U K p V f) +
        nabT P U K (p + 1) V (P.fD U (P.FK U K) p V f) = 0) ?_ ?_
  · intro V f S hS h
    refine tTot_ext_local P U K (p + 1 + 1) S hS ?_ (zero_mem _) (fun W g hg => ?_)
    · exact add_mem ((theta P U K V).extend_mem (theta_mem P U K V) (nabT_mem P U K p V f))
        (nabT_mem P U K (p + 1) V _)
    · have h0 := h g hg
      have h3 : P.tRes U (P.FK U K) g.op 0 = 0 := map_zero _
      rw [h3, ← h0, map_add, extend_tRes, tRes_nabT, tRes_nabT, fD_res]
  · intro V z
    induction z using bc_induction with
    | ht s m => exact extNab_tm P U K p V s m
    | hadd x y hx hy =>
      erw [map_add]
      rw [nabT_add, map_add, map_add (P.fD U (P.FK U K) p V), nabT_add, add_add_add_comm,
        hx, hy, add_zero]

/-- `θ_V` is flat (`𝕏² = c = 0`). -/
private theorem theta_flat [CompactSpace X] (V : (Over U)ᵒᵖ)
    (e : ⨁ p, P.FSec U (P.FK U K) p V) :
    (theta P U K V).extend ((theta P U K V).θ e) =
      GCDga.c (𝒜 := P.D.𝒜 V.unop.left) •
        Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1 e := by
  rw [P.c_eq_zero, zero_smul]
  induction e using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of p y =>
    have h2 : (theta P U K V).θ (DirectSum.of (P.FSec U (P.FK U K) · V) p y) =
        nabT P U K p V y + gT P U K (p + 1) V 1 (P.fD U (P.FK U K) p V y) :=
      thetaAdd_of P U K p V y
    rw [h2, map_add]
    have h3 : (theta P U K V).extend (gT P U K (p + 1) V 1 (P.fD U (P.FK U K) p V y)) =
        nabT P U K (p + 1) V (P.fD U (P.FK U K) p V y) +
          gT P U K (p + 1 + 1) V 1 (P.fD U (P.FK U K) (p + 1) V (P.fD U (P.FK U K) p V y)) :=
      (GenData.extend_tmul_one _ _).trans (thetaAdd_of P U K (p + 1) V _)
    rw [h3, fD_fD]
    have h4 : gT P U K (p + 1 + 1) V 1 0 = 0 := by
      unfold gT
      rw [map_zero, Tot.tmul_zero]
    rw [h4, add_zero]
    exact extNab P U K p V y
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- **C7.b. The connection on `𝒜⁰ ⊗_R K`.** There is a flat connection `θ` on `F_K` with
`∇(η k) = 0`: `∇` is the sheafification of `α ⊗ k ↦ dα ⊗ η(1 ⊗ k)` (well defined since
`d ∘ ρ = 0`; its target `𝒜¹ ⊗_{𝒜⁰} F_K` is a sheaf by C7.a), and `θ_V f = ∇f + 1 ⊗ d_F f`.
Leibniz, `∇ d_F = d_F ∇` and `∇² = 0` hold where `f` comes from the presheaf tensor product,
hence everywhere (the unit of sheafification is locally surjective; sections are separated).
Needs `X` compact (C7.a). -/
theorem exists_conn [CompactSpace X] : ∃ θ : P.Conn U (P.FK U K), P.IsBCConn U K θ :=
  ⟨⟨theta P U K, theta_mem P U K, theta_flat P U K, theta_eps P U K,
    fun f e => theta_natural P U K f e⟩, fun V p k => theta_bcη P U K p V k⟩

end PreResolvingData

end Cohesive
