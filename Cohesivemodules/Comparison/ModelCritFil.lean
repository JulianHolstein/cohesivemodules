import Cohesivemodules.Comparison.ModelCritCoord

set_option linter.style.header false

/-!
# C7.f: the quasi-isomorphism criterion for maps of `T`-complexes (part 3 of 4)

Split from `Comparison/ModelCrit.lean` for size;
continues `Comparison/ModelCritCoord.lean`.
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

section Proj

variable (F :CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)

/-- The form-degree projection `π_q` on `T^n(V)`. -/
private def PqV (q n : ℤ) (V : (Over U)ᵒᵖ) :
    P.TSec U F n V →ₗ[P.O.obj.obj (op V.unop.left)] P.TSec U F n V where
  toFun x := ⟨Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) q x.1, projF_mem_totDeg q x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' r x := Subtype.ext (by
    have := (Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) q).map_smul (P.ρ V.unop.left r) x.1
    rwa [Tot.smul0_eq, Tot.smul0_eq] at this)

/-- `π_q` commutes with restriction. -/
private theorem projF_tRes (q : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.TTot U F V) :
    P.tRes U F f (Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) q x) =
      Tot.projF (P.D.𝒜 W.unop.left) (P.FSec U F · W) q (P.tRes U F f x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.projF_tmul, tRes_apply, tRes_apply, totMapAlong_tmul, totMapAlong_tmul,
      Tot.projF_tmul, DgaHom.map_proj]
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- `π_q` as a morphism of sheaves `T^n ⟶ T^n`. -/
private def Pmor [CompactSpace X] (q n : ℤ) : P.TSh U F n ⟶ P.TSh U F n :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (PqV F q n V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact (projF_tRes F q f x.1).symm }⟩

/-- `Pmor` on sections. -/
private theorem Pmor_app [CompactSpace X] (q n : ℤ) (V : (Over U)ᵒᵖ) (x : P.TSec U F n V) :
    ((Pmor F q n).val.app V x).1 =
      Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) q x.1 := rfl

/-- `F^b ⊆ T^n`: the sections of form degree `≥ b`. -/
private def FilSub [CompactSpace X] (b : ℕ) (n : ℤ) : (P.TSh U F n).Submodule :=
  kerSub (fun q : {q : ℤ // q < (b : ℤ)} => Pmor F q.1 n)

/-- `gr^b ⊆ T^n`: the sections of pure form degree `b`. -/
def GrSub [CompactSpace X] (b : ℕ) (n : ℤ) : (P.TSh U F n).Submodule :=
  kerSub (fun _ : Unit => Pmor F (b : ℤ) n - 𝟙 _)

private theorem mem_FilSub [CompactSpace X] (b : ℕ) (n : ℤ) (V : (Over U)ᵒᵖ)
    (x : (P.TSh U F n).val.obj V) :
    x ∈ (FilSub F b n).obj V ↔
      x.1 ∈ filTot (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) := by
  rw [FilSub, mem_kerSub]
  constructor
  · intro h
    refine mem_filTot_of_projF fun q hq => ?_
    exact congrArg Subtype.val (h ⟨q, hq⟩)
  · intro h q
    exact Subtype.ext (projF_eq_zero_of_lt q.2 h)

theorem mem_GrSub [CompactSpace X] (b : ℕ) (n : ℤ) (V : (Over U)ᵒᵖ)
    (x : (P.TSh U F n).val.obj V) :
    x ∈ (GrSub F b n).obj V ↔
      Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) x.1 = x.1 := by
  rw [GrSub, mem_kerSub]
  constructor
  · intro h
    have := congrArg Subtype.val (h ())
    exact sub_eq_zero.1 this
  · intro h _
    exact Subtype.ext (sub_eq_zero.2 h)

end Proj

section FilComplex

variable [CompactSpace X] {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} (θ : P.Conn U F)

/-- The differential of `F^b` (`𝕏` preserves the form-degree filtration). -/
private def FilD (b : ℕ) (n : ℤ) :
    (FilSub F b n).toSheafOfModules ⟶ (FilSub F b (n + 1)).toSheafOfModules :=
  subLift (FilSub F b (n + 1)) ((FilSub F b n).ι ≫ θ.TD n) fun V a =>
    (mem_FilSub F b (n + 1) V _).2
      (X_mem_filTot (θ.N V) ((mem_FilSub F b n V a.1).1 a.2))

private theorem FilD_ι (b : ℕ) (n : ℤ) :
    FilD θ b n ≫ (FilSub F b (n + 1)).ι = (FilSub F b n).ι ≫ θ.TD n :=
  subLift_ι _ _ _

private theorem FilD_FilD (b : ℕ) (n : ℤ) : FilD θ b n ≫ FilD θ b (n + 1) = 0 := by
  rw [← cancel_mono (FilSub F b (n + 1 + 1)).ι, Category.assoc, FilD_ι, ← Category.assoc,
    FilD_ι, Category.assoc, θ.TD_TD, Limits.comp_zero, Limits.zero_comp]

/-- The subcomplex `F^b T(θ)` of `T(θ)`. -/
private def FilC (b : ℕ) : CochainComplex (Mod (P.R.over U)) ℤ :=
  CochainComplex.of (fun n => (FilSub F b n).toSheafOfModules) (FilD θ b) (FilD_FilD θ b)

private theorem N_XX (V : (Over U)ᵒᵖ) (x : (θ.N V).T) : (θ.N V).X ((θ.N V).X x) = 0 := by
  have h := (θ.N V).flat x
  erw [P.c_eq_zero, zero_smul] at h
  exact h

/-- The differential of `gr^b`: `x ↦ π_b 𝕏 x`. -/
private def GrD (b : ℕ) (n : ℤ) :
    (GrSub F b n).toSheafOfModules ⟶ (GrSub F b (n + 1)).toSheafOfModules :=
  subLift (GrSub F b (n + 1)) ((GrSub F b n).ι ≫ θ.TD n ≫ Pmor F b (n + 1)) fun V _ =>
    (mem_GrSub F b (n + 1) V _).2 (projF_projF _ _)

private theorem GrD_ι (b : ℕ) (n : ℤ) :
    GrD θ b n ≫ (GrSub F b (n + 1)).ι = (GrSub F b n).ι ≫ θ.TD n ≫ Pmor F b (n + 1) :=
  subLift_ι _ _ _

private theorem GrD_GrD (b : ℕ) (n : ℤ) : GrD θ b n ≫ GrD θ b (n + 1) = 0 := by
  rw [← cancel_mono (GrSub F b (n + 1 + 1)).ι, Category.assoc, GrD_ι, ← Category.assoc,
    GrD_ι]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact projF_X_projF_X (θ.N V) (N_XX θ V) b ((mem_GrSub F b n V _).1 x.2)

/-- The graded piece `gr^b T(θ)`. -/
def GrC (b : ℕ) : CochainComplex (Mod (P.R.over U)) ℤ :=
  CochainComplex.of (fun n => (GrSub F b n).toSheafOfModules) (GrD θ b) (GrD_GrD θ b)

/-- `F^{b+1} → F^b` in degree `n`. -/
private def FilInclN (b : ℕ) (n : ℤ) :
    (FilSub F (b + 1) n).toSheafOfModules ⟶ (FilSub F b n).toSheafOfModules :=
  subLift (FilSub F b n) (FilSub F (b + 1) n).ι fun V a =>
    (mem_FilSub F b n V _).2 (filTot_anti (by omega) ((mem_FilSub F (b + 1) n V a.1).1 a.2))

private theorem FilInclN_ι (b : ℕ) (n : ℤ) :
    FilInclN (F := F) b n ≫ (FilSub F b n).ι = (FilSub F (b + 1) n).ι :=
  subLift_ι _ _ _

/-- The inclusion of complexes `F^{b+1} T(θ) → F^b T(θ)`. -/
private def FilIncl (b : ℕ) : FilC θ (b + 1) ⟶ FilC θ b :=
  CochainComplex.ofHom (fun n => FilInclN b n) (fun n => by
    simp only [FilC, CochainComplex.of_d]
    rw [← cancel_mono (FilSub F b (n + 1)).ι]
    simp only [Category.assoc, FilD_ι, FilInclN_ι]
    rw [← Category.assoc, FilInclN_ι])

/-- `F^b → gr^b` in degree `n`. -/
private def GrProjN (b : ℕ) (n : ℤ) :
    (FilSub F b n).toSheafOfModules ⟶ (GrSub F b n).toSheafOfModules :=
  subLift (GrSub F b n) ((FilSub F b n).ι ≫ Pmor F b n) fun V _ =>
    (mem_GrSub F b n V _).2 (projF_projF _ _)

private theorem GrProjN_ι (b : ℕ) (n : ℤ) :
    GrProjN (F := F) b n ≫ (GrSub F b n).ι = (FilSub F b n).ι ≫ Pmor F b n :=
  subLift_ι _ _ _

/-- The projection of complexes `F^b T(θ) → gr^b T(θ)`. -/
private def GrProj (b : ℕ) : FilC θ b ⟶ GrC θ b :=
  CochainComplex.ofHom (fun n => GrProjN b n) (fun n => by
    simp only [FilC, GrC, CochainComplex.of_d]
    rw [← cancel_mono (GrSub F b (n + 1)).ι]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact projF_X_projF (θ.N V) b ((mem_FilSub F b n V _).1 x.2))

private theorem FilIncl_GrProj_N (b : ℕ) (n : ℤ) :
    FilInclN (F := F) b n ≫ GrProjN b n = 0 := by
  rw [← cancel_mono (GrSub F b n).ι]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact projF_eq_zero_of_mem (filTot_anti (by omega) ((mem_FilSub F (b + 1) n V _).1 x.2))

private theorem SK_shortExact_N (b : ℕ) (n : ℤ) :
    (ShortComplex.mk (FilInclN (F := F) b n) (GrProjN b n)
      (FilIncl_GrProj_N b n)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine exact_of_sections_exact _ fun V => ?_
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    have hz : Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) x.1.1 = 0 :=
      congrArg (fun z => z.1.1) hx
    have h1 := sub_projF_mem_filTot ((mem_FilSub F b n V _).1 x.2)
    rw [hz, sub_zero, ← Nat.cast_succ] at h1
    exact ⟨⟨x.1, (mem_FilSub F (b + 1) n V _).2 h1⟩, rfl⟩
  · refine mono_of_sections_injective _ fun V a c h => ?_
    have h' := Subtype.ext_iff.1 h
    exact Subtype.ext h'
  · refine epi_of_sections_surjective' _ fun V t => ?_
    have h1 := (mem_GrSub F b n V _).1 t.2
    have h2 : t.1.1 ∈ filTot (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) := by
      have h3 : Tot.projF (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) t.1.1 ∈
          filTot (P.D.𝒜 V.unop.left) (P.FSec U F · V) (b : ℤ) := projF_mem_filTot _ _
      rwa [h1] at h3
    exact ⟨⟨t.1, (mem_FilSub F b n V _).2 h2⟩, Subtype.ext (Subtype.ext h1)⟩

/-- The short complex `F^{b+1} → F^b → gr^b`. -/
private def SK (b : ℕ) : ShortComplex (CochainComplex (Mod (P.R.over U)) ℤ) :=
  ShortComplex.mk (FilIncl θ b) (GrProj θ b) (by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    exact FilIncl_GrProj_N b n)

private theorem SK_shortExact (b : ℕ) : (SK θ b).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => SK_shortExact_N b n

end FilComplex

section FilMap

variable [CompactSpace X]

/-- `π_b φ = π_b φ π_b` on `F^b`. -/
private theorem proj_phi_aux {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {M₁ M₂ : QuasiCohesive 𝒜}
    {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Z0 M₁ M₂) (b : ℤ) {n : ℤ} {x : M₁.T}
    (hx : x ∈ filTot 𝒜 M₁.Q b) (hxd : x ∈ totDeg 𝒜 M₁.Q n) :
    Tot.projF 𝒜 M₂.Q b (φ (Tot.projF 𝒜 M₁.Q b x)) = Tot.projF 𝒜 M₂.Q b (φ x) := by
  have h2 : x - Tot.projF 𝒜 M₁.Q b x ∈ M₁.filDeg (b + 1) n :=
    ⟨sub_mem hxd (projF_mem_totDeg b hxd), sub_projF_mem_filTot hx⟩
  have h3 := projF_eq_zero_of_mem (filMapD_mem hφ.1 h2).2
  rw [map_sub, map_sub, sub_eq_zero] at h3
  exact h3.symm

/-- `φ` maps `F^b` to `F^b` and `π_b φ π_b 𝕏 = π_b φ 𝕏` etc.: the compatibility of `gr^b φ`
with the differentials, at the level of `Tot`. -/
private theorem gr_comm_aux {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {M₁ M₂ : QuasiCohesive 𝒜}
    {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Z0 M₁ M₂) (b : ℤ) {n : ℤ} {x : M₁.T}
    (hxd : x ∈ totDeg 𝒜 M₁.Q n) (hx : Tot.projF 𝒜 M₁.Q b x = x) :
    Tot.projF 𝒜 M₂.Q b (M₂.X (Tot.projF 𝒜 M₂.Q b (φ x))) =
      Tot.projF 𝒜 M₂.Q b (φ (Tot.projF 𝒜 M₁.Q b (M₁.X x))) := by
  have hF : x ∈ M₁.filDeg b n := ⟨hxd, hx ▸ projF_mem_filTot b x⟩
  have hX := M₁.X_mem_filDeg hF
  have h1 : φ x ∈ filTot 𝒜 M₂.Q b := (filMapD_mem hφ.1 hF).2
  have h2 : M₁.X x - Tot.projF 𝒜 M₁.Q b (M₁.X x) ∈ M₁.filDeg (b + 1) (n + 1) :=
    ⟨sub_mem hX.1 (projF_mem_totDeg b hX.1), sub_projF_mem_filTot hX.2⟩
  have h3 := projF_eq_zero_of_mem (filMapD_mem hφ.1 h2).2
  rw [map_sub, map_sub, sub_eq_zero] at h3
  rw [projF_X_projF M₂ b h1, closed0_X (LinearMap.mem_ker.1 hφ.2) x, h3]

/-- `φ` preserves the form-degree filtration. -/
private def FilMapN (b : ℕ) (n : ℤ) :
    (FilSub F₁ b n).toSheafOfModules ⟶ (FilSub F₂ b n).toSheafOfModules :=
  subLift (FilSub F₂ b n) ((FilSub F₁ b n).ι ≫ Φ.TMapn n) fun V x =>
    (mem_FilSub F₂ b n V _).2
      (filMapD_mem (Φ.mem V).1 (b := (b : ℤ)) (m := n)
        ⟨x.1.2, (mem_FilSub F₁ b n V _).1 x.2⟩).2

private theorem FilMapN_ι (b : ℕ) (n : ℤ) :
    FilMapN Φ b n ≫ (FilSub F₂ b n).ι = (FilSub F₁ b n).ι ≫ Φ.TMapn n :=
  subLift_ι _ _ _

/-- The map `F^b T(θ₁) → F^b T(θ₂)`. -/
private def FilMap (b : ℕ) : FilC θ₁ b ⟶ FilC θ₂ b :=
  CochainComplex.ofHom (fun n => FilMapN Φ b n) (fun n => by
    simp only [FilC, CochainComplex.of_d]
    rw [← cancel_mono (FilSub F₂ b (n + 1)).ι]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact closed0_X (LinearMap.mem_ker.1 (Φ.mem V).2) x.1.1)

/-- The map `gr^b T(θ₁) → gr^b T(θ₂)`: `x ↦ π_b (φ x)`. -/
def GrMapN (b : ℕ) (n : ℤ) :
    (GrSub F₁ b n).toSheafOfModules ⟶ (GrSub F₂ b n).toSheafOfModules :=
  subLift (GrSub F₂ b n) ((GrSub F₁ b n).ι ≫ Φ.TMapn n ≫ Pmor F₂ b n) fun V _ =>
    (mem_GrSub F₂ b n V _).2 (projF_projF _ _)

private theorem GrMapN_ι (b : ℕ) (n : ℤ) :
    GrMapN Φ b n ≫ (GrSub F₂ b n).ι = (GrSub F₁ b n).ι ≫ Φ.TMapn n ≫ Pmor F₂ b n :=
  subLift_ι _ _ _

/-- The map of complexes `gr^b T(θ₁) → gr^b T(θ₂)`. -/
def GrMap (b : ℕ) : GrC θ₁ b ⟶ GrC θ₂ b :=
  CochainComplex.ofHom (fun n => GrMapN Φ b n) (fun n => by
    simp only [GrC, CochainComplex.of_d]
    rw [← cancel_mono (GrSub F₂ b (n + 1)).ι]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact gr_comm_aux (Φ.mem V) (b : ℤ) x.1.2 ((mem_GrSub F₁ b n V _).1 x.2))

/-- The morphism of short complexes `SK θ₁ b ⟶ SK θ₂ b` induced by `Φ`. -/
private def SKMap (b : ℕ) : SK θ₁ b ⟶ SK θ₂ b :=
  ShortComplex.homMk (FilMap Φ (b + 1)) (FilMap Φ b) (GrMap Φ b)
    (by
      refine HomologicalComplex.hom_ext _ _ fun n => ?_
      show FilInclN b n ≫ FilMapN Φ b n = FilMapN Φ (b + 1) n ≫ FilInclN b n
      rw [← cancel_mono (FilSub F₂ b n).ι]
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
      apply ModuleCat.hom_ext
      refine DFunLike.ext _ _ fun x => ?_
      exact Subtype.ext rfl)
    (by
      refine HomologicalComplex.hom_ext _ _ fun n => ?_
      show FilMapN Φ b n ≫ GrProjN b n = GrProjN b n ≫ GrMapN Φ b n
      rw [← cancel_mono (GrSub F₂ b n).ι]
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
      apply ModuleCat.hom_ext
      refine DFunLike.ext _ _ fun x => ?_
      exact Subtype.ext (proj_phi_aux (Φ.mem V) (b : ℤ)
        ((mem_FilSub F₁ b n V _).1 x.2) x.1.2).symm)

/-- `F^{N+1} T(θ) = 0`. -/
private theorem isZero_FilSh_top (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ) (n : ℤ) :
    Limits.IsZero (FilSub F (GCDga.N (P.D.𝒜 ⊤) + 1) n).toSheafOfModules :=
  isZero_of_sections_subsingleton fun V => ⟨fun a c => by
    have key : ∀ y : ↥((FilSub F (GCDga.N (P.D.𝒜 ⊤) + 1) n).obj V), y.1.1 = 0 := fun y => by
      have h1 := (mem_FilSub F _ n V _).1 y.2
      have hb : filTot (P.D.𝒜 V.unop.left) (P.FSec U F · V)
          (((GCDga.N (P.D.𝒜 ⊤) + 1 : ℕ)) : ℤ) = ⊥ :=
        filTot_eq_bot_of_zero (fun q hq a ha =>
          P.zero_above (by push_cast at hq; omega) V.unop.left ha)
      rw [hb] at h1
      exact (Submodule.mem_bot _).1 h1
    exact Subtype.ext (Subtype.ext ((key a).trans (key c).symm))⟩

/-- `F^{N+1}Φ` is a quasi-isomorphism (both sides are zero). -/
private theorem quasiIso_FilMap_top :
    QuasiIso (FilMap Φ (GCDga.N (P.D.𝒜 ⊤) + 1)) := by
  have h : ∀ n, IsIso ((FilMap Φ (GCDga.N (P.D.𝒜 ⊤) + 1)).f n) := fun n =>
    Limits.IsZero.isIso (isZero_FilSh_top F₁ n) (isZero_FilSh_top F₂ n) _
  have : IsIso (FilMap Φ (GCDga.N (P.D.𝒜 ⊤) + 1)) :=
    HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-- The inclusion `F^0 T(θ) → T(θ)`, a chain map. -/
private def FilToT {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} (θ : P.Conn U F) :
    FilC θ 0 ⟶ θ.TC :=
  CochainComplex.ofHom (fun n => (FilSub F 0 n).ι) (fun n => by
    simp only [FilC, Conn.TC, CochainComplex.of_d]
    exact (FilD_ι θ 0 n).symm)

private theorem isIso_FilToT {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ}
    (θ : P.Conn U F) : IsIso (FilToT θ) := by
  have h : ∀ n, IsIso ((FilToT θ).f n) := fun n => by
    have h1 : Mono (FilSub F 0 n).ι := inferInstance
    have h2 : Epi (FilSub F 0 n).ι := by
      refine epi_of_sections_surjective' _ fun V t => ?_
      refine ⟨⟨t, (mem_FilSub F 0 n V _).2 ?_⟩, rfl⟩
      exact filTot_zero _
    exact isIso_of_mono_of_epi (FilSub F 0 n).ι
  exact HomologicalComplex.Hom.isIso_of_components _

/-- If every `gr^b Φ` is a quasi-isomorphism, so is `Φ`: A7 with the form-degree filtration. -/
theorem quasiIso_TMap_of_gr (hgr : ∀ b : ℕ, QuasiIso (GrMap Φ b)) :
    QuasiIso Φ.TMap := by
  have key : QuasiIso (FilMap Φ 0) :=
    quasiIso_of_finite_filtration (GCDga.N (P.D.𝒜 ⊤) + 1) (fun b => SK θ₁ b)
      (fun b => SK θ₂ b) (fun b => SK_shortExact θ₁ b) (fun b => SK_shortExact θ₂ b)
      (fun b => SKMap Φ b) (fun b => ⟨FilC θ₁ b, FilC θ₂ b, FilMap Φ b⟩)
      (fun b => rfl) (fun b => rfl) (fun b _ => hgr b) (quasiIso_FilMap_top Φ)
  have := isIso_FilToT θ₁
  have := isIso_FilToT θ₂
  have e : Arrow.mk (FilMap Φ 0) ≅ Arrow.mk Φ.TMap :=
    Arrow.isoMk (asIso (FilToT θ₁)) (asIso (FilToT θ₂)) (by
      refine HomologicalComplex.hom_ext _ _ fun n => ?_
      show FilMapN Φ 0 n ≫ (FilSub F₂ 0 n).ι = (FilSub F₁ 0 n).ι ≫ Φ.TMapn n
      exact FilMapN_ι Φ 0 n)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ e).1 key

end FilMap

end ConnHom
end PreResolvingData
end Cohesive
end
