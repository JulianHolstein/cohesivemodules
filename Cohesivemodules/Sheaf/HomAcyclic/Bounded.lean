import Cohesivemodules.Sheaf.HomAcyclic.HomGood

set_option linter.style.header false

/-!
# S7.b (part 2): `HomGood` for bounded complexes of summands of finite free modules

Blueprint item S7.b (§3). Split from `Sheaf/HomAcyclic.lean` for size only (CLAUDE.md: "New work
goes in small new files"); no mathematical change.

* `𝓗om(R, N) ≅ N`, and `HomGood` for a single summand of a finite free module in one degree.
* Stupid truncation `0 → σ_{>a}P → P → Pᵃ[-a] → 0` and the induction on the length of `P`.
-/

universe v u

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

open TopologicalSpace CochainComplex.HomComplex
open scoped ZeroObject

/-- The evaluation of a morphism `R|V ⟶ N|V` at the unit section. -/
private def epsFun (N : Mod R) (V : Opens X) (φ : (SheafOfModules.unit R).over V ⟶ N.over V) :
    N.val.obj (op V) :=
  (φ.val.app (op (Over.mk (𝟙 V)))).hom (1 : R.obj.obj (op V))

/-- Naturality of `epsFun` in the open set. -/
private lemma epsFun_restr (N : Mod R) {V W : Opens X} (g : W ⟶ V)
    (φ : (SheafOfModules.unit R).over V ⟶ N.over V) :
    epsFun N W (homRestr g φ) = (N.val.map g.op).hom (epsFun N V φ) := by
  let u : (Over.map g).obj (Over.mk (𝟙 W)) ⟶ Over.mk (𝟙 V) := Over.homMk g (by simp)
  have h := PresheafOfModules.sections_property
    ((N.over V).unitHomEquiv (show SheafOfModules.unit (R.over V) ⟶ N.over V from φ)) u.op
  exact h.symm

/-- Evaluation at the unit section as a morphism `𝓗om(R, N) ⟶ N`. -/
private def epsHom (hR : IsCommSheaf R) (N : Mod R) :
    homSheaf hR (SheafOfModules.unit R) N ⟶ N where
  val :=
    { app := fun V ↦ ModuleCat.ofHom (X := (homSheaf hR (SheafOfModules.unit R) N).val.obj V)
        (Y := N.val.obj V)
        { toFun := epsFun N V.unop
          map_add' := fun φ ψ ↦ rfl
          map_smul' := fun r φ ↦ by
            have h : (overRes r (op (Over.mk (𝟙 V.unop))) : R.obj.obj V) = r := by
              show (R.obj.map (𝟙 V)).hom r = r
              rw [CategoryTheory.Functor.map_id]
              rfl
            exact congrArg (fun a : R.obj.obj V ↦ a • epsFun N V.unop φ) h }
      naturality := fun {V W} f ↦ by
        ext φ
        exact epsFun_restr N f.unop φ }

/-- A morphism of sheaves of modules that is bijective on sections is an isomorphism. -/
private lemma isIso_of_bijective_app {M N : Mod R} (f : M ⟶ N)
    (h : ∀ V : (Opens X)ᵒᵖ, Function.Bijective (f.val.app V)) : IsIso f := by
  have h1 : IsIso ((SheafOfModules.toSheaf.{0} R).map f) := by
    have : IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf.{0} R).map f)) := by
      have : ∀ V, IsIso
          (((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf.{0} R).map f)).app V) :=
        fun V ↦ (ConcreteCategory.isIso_iff_bijective _).2 (h V)
      exact NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf.{0} R)

/-- A section of a sheaf on the over-site is determined by its value at the terminal object. -/
private lemma sections_eq_of_terminal {V : Opens X} {M : Mod (R.over V)} (s t : M.sections)
    (h : s.1 (op (Over.mk (𝟙 V))) = t.1 (op (Over.mk (𝟙 V)))) : s = t := by
  apply PresheafOfModules.sections_ext
  intro Z
  obtain ⟨Z⟩ := Z
  let u : Z ⟶ Over.mk (𝟙 V) := Over.homMk Z.hom (by simp)
  have h1 := PresheafOfModules.sections_property s u.op
  have h2 := PresheafOfModules.sections_property t u.op
  rw [← h1, ← h2, h]

/-- `epsFun` is bijective. -/
private lemma epsFun_bijective (N : Mod R) (V : Opens X) : Function.Bijective (epsFun N V) := by
  constructor
  · intro φ ψ hφψ
    have := sections_eq_of_terminal (M := N.over V)
      ((N.over V).unitHomEquiv (show SheafOfModules.unit (R.over V) ⟶ N.over V from φ))
      ((N.over V).unitHomEquiv (show SheafOfModules.unit (R.over V) ⟶ N.over V from ψ)) hφψ
    exact (N.over V).unitHomEquiv.injective this
  · intro s0
    let sec : (N.over V).sections := PresheafOfModules.sectionsMk
      (fun Z ↦ N.val.map Z.unop.hom.op s0) (by
        intro Z Z' g
        have hw : g.unop.left ≫ Z.unop.hom = Z'.unop.hom := Over.w g.unop
        show (N.val.map g.unop.left.op).hom (N.val.map Z.unop.hom.op s0) = _
        rw [← PresheafOfModules.map_comp_apply]
        rw [← hw]
        rfl)
    refine ⟨(N.over V).unitHomEquiv.symm sec, ?_⟩
    show ((N.over V).unitHomEquiv ((N.over V).unitHomEquiv.symm sec)).val
      (op (Over.mk (𝟙 V))) = s0
    rw [Equiv.apply_symm_apply]
    show (N.val.map (𝟙 (op V))).hom s0 = s0
    simp only [PresheafOfModules.map_id]
    rfl

/-- `epsHom` is an isomorphism. -/
private instance isIso_epsHom (hR : IsCommSheaf R) (N : Mod R) : IsIso (epsHom hR N) :=
  isIso_of_bijective_app _ fun V ↦ epsFun_bijective N V.unop

/-- `epsHom` is natural in the target. -/
private lemma homPost_epsHom (hR : IsCommSheaf R) {N N' : Mod R} (g : N ⟶ N') :
    homPost hR (SheafOfModules.unit R) g ≫ epsHom hR N' = epsHom hR N ≫ g := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ rfl)

/-- The complex `n ↦ L^{a+n}`, differential `d^{a+n}` (no signs). -/
private def shiftIdx (a : ℤ) (L : CochainComplex (Mod R) ℤ) : CochainComplex (Mod R) ℤ where
  X n := L.X (a + n)
  d i j := L.d (a + i) (a + j)
  shape i j hij := L.shape _ _ (by
    simp only [ComplexShape.up_Rel] at hij ⊢
    lia)
  d_comp_d' i j k _ _ := L.d_comp_d _ _ _

/-- The map `n ↦ g^{a+n}`. -/
private def shiftIdxMap (a : ℤ) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') :
    shiftIdx a L ⟶ shiftIdx a L' where
  f n := g.f (a + n)
  comm' _ _ _ := g.comm _ _

/-- `shiftIdxMap` preserves quasi-isomorphisms. -/
private lemma quasiIso_shiftIdxMap (a : ℤ) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L')
    [QuasiIso g] : QuasiIso (shiftIdxMap a g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' (shiftIdxMap a g) (n - 1) n (n + 1) (by simp) (by simp)]
  have := (quasiIsoAt_iff' g (a + (n - 1)) (a + n) (a + (n + 1))
    (by rw [CochainComplex.prev]; lia) (by rw [CochainComplex.next]; lia)).1
    ((inferInstance : QuasiIso g).quasiIsoAt (a + n))
  exact this

/-- A product projection is an isomorphism when all other factors are zero. -/
private lemma isIso_pi_π_of_isZero {ι : Type} {A : Type*} [Category A] [HasZeroMorphisms A]
    (f : ι → A) [HasProduct f] (j : ι) (h : ∀ i, i ≠ j → IsZero (f i)) :
    IsIso (Pi.π f j) := by
  classical
  let s : f j ⟶ ∏ᶜ f := Pi.lift fun i ↦ if hi : i = j then eqToHom (by rw [hi]) else 0
  refine ⟨s, ?_, ?_⟩
  · apply Pi.hom_ext
    intro i
    by_cases hi : i = j
    · subst hi
      simp [s]
    · exact (h i hi).eq_of_tgt _ _
  · simp [s]

/-- `𝓗om(0, N)` is zero. -/
private lemma isZero_homSheaf_left (hR : IsCommSheaf R) {M : Mod R} (N : Mod R)
    (hM : IsZero M) : IsZero (homSheaf hR M N) := by
  rw [IsZero.iff_id_eq_zero]
  rw [← homPre_id', hM.eq_of_src (𝟙 M) 0, homPre_zero]

section Single

variable (hR : IsCommSheaf R) (M : Mod R) (a : ℤ)

/-- The complex with `M` in degree `a`. -/
private abbrev sing : CochainComplex (Mod R) ℤ :=
  (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).obj M

/-- The distinguished triplet `(a, a + n)`. -/
private abbrev trip (n : ℤ) : Triplet n := ⟨a, a + n, rfl⟩

/-- `𝓗om^n(M[-a], L) ⟶ 𝓗om(M, L^{a+n})`: projection to the only nonzero factor. -/
private def eS (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexX hR (sing M a) L n ⟶ homSheaf hR M (L.X (a + n)) :=
  Pi.π (fun T : Triplet n ↦ homSheaf hR ((sing M a).X T.p) (L.X T.q)) (trip a n) ≫
    homPre hR (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).inv (L.X (a + n))

/-- `eS` is an isomorphism. -/
private lemma isIso_eS (L : CochainComplex (Mod R) ℤ) (n : ℤ) : IsIso (eS hR M a L n) := by
  have h1 : IsIso (Pi.π (fun T : Triplet n ↦ homSheaf hR ((sing M a).X T.p) (L.X T.q))
      (trip a n)) := by
    refine isIso_pi_π_of_isZero _ _ fun T hT ↦ ?_
    refine isZero_homSheaf_left hR _ ?_
    refine HomologicalComplex.isZero_single_obj_X _ _ _ _ fun hp ↦ hT ?_
    obtain ⟨p, q, hpq⟩ := T
    subst hpq
    obtain rfl : p = a := hp
    rfl
  have h2 : IsIso (homPre hR (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).inv
      (L.X (a + n))) := by
    refine ⟨homPre hR
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).hom _, ?_, ?_⟩
    · rw [homPre_comp', Iso.hom_inv_id, homPre_id']
    · rw [homPre_comp', Iso.inv_hom_id, homPre_id']
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- `eS` commutes with the differentials. -/
private lemma eS_comm (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexD hR (sing M a) L n ≫ eS hR M a L (n + 1) =
      eS hR M a L n ≫ homPost hR M (L.d (a + n) (a + (n + 1))) := by
  unfold eS
  rw [← Category.assoc, homComplexD_π hR (sing M a) L n (trip a (n + 1))]
  have h0 : (sing M a).d a (a + 1) = 0 := HomologicalComplex.single_obj_d _ _ _ _ _
  simp only [trip, h0, homPre_zero, Limits.comp_zero, smul_zero, add_zero, Category.assoc]
  rw [← homPre_homPost']

/-- `eS` is natural in the target complex. -/
private lemma eS_nat (L L' : CochainComplex (Mod R) ℤ) (g : L ⟶ L') (n : ℤ) :
    eS hR M a L n ≫ homPost hR M (g.f (a + n)) = postX hR (sing M a) g n ≫ eS hR M a L' n := by
  unfold eS postX
  rw [← Category.assoc (Limits.Pi.map _), Limits.Pi.map_π, Category.assoc, Category.assoc,
    homPre_homPost']

/-- `𝓗om^n(R[-a], L) ≅ L^{a+n}`. -/
private def eU (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexX hR (sing (SheafOfModules.unit R) a) L n ≅ L.X (a + n) :=
  haveI := isIso_eS hR (SheafOfModules.unit R) a L n
  asIso (eS hR (SheafOfModules.unit R) a L n) ≪≫ asIso (epsHom hR (L.X (a + n)))

/-- `eU` commutes with the differentials. -/
private lemma eU_comm (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexD hR (sing (SheafOfModules.unit R) a) L n ≫ (eU hR a L (n + 1)).hom =
      (eU hR a L n).hom ≫ L.d (a + n) (a + (n + 1)) := by
  simp only [eU, Iso.trans_hom, asIso_hom, ← Category.assoc, eS_comm]
  simp only [Category.assoc, homPost_epsHom]

/-- `eU` is natural in the target complex. -/
private lemma eU_nat (L L' : CochainComplex (Mod R) ℤ) (g : L ⟶ L') (n : ℤ) :
    (eU hR a L n).hom ≫ g.f (a + n) =
      postX hR (sing (SheafOfModules.unit R) a) g n ≫ (eU hR a L' n).hom := by
  simp only [eU, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← homPost_epsHom, ← Category.assoc, ← Category.assoc, eS_nat]

/-- `𝓗om(R[-a], L) ≅ L` reindexed. -/
private def singIso (L : CochainComplex (Mod R) ℤ) :
    homSheafComplex hR (sing (SheafOfModules.unit R) a) L ≅ shiftIdx a L :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ eU hR a L n) (fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    have h : (homSheafComplex hR (sing (SheafOfModules.unit R) a) L).d i (i + 1) =
        homComplexD hR (sing (SheafOfModules.unit R) a) L i :=
      CochainComplex.of_d _ _ i
    rw [h]
    exact (eU_comm hR a L i).symm)

/-- `HomGood` for the complex `R[-a]`. -/
private lemma HomGood.single_unit : HomGood hR (sing (SheafOfModules.unit R) a) := by
  intro L L' g _
  have := quasiIso_shiftIdxMap a g
  refine (quasiIso_iff_of_arrow_mk_iso (homComplexMap₂ hR _ g) (shiftIdxMap a g)
    (Arrow.isoMk (singIso hR a L) (singIso hR a L') ?_)).2 this
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  exact eU_nat hR a L L' g n

/-- `HomGood` transfers along isomorphisms of the single term. -/
private lemma HomGood.sing_of_iso {M M' : Mod R} (e : M ≅ M') (h : HomGood hR (sing M' a)) :
    HomGood hR (sing M a) :=
  HomGood.of_retract hR h ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).map e.hom)
    ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).map e.inv) (by
      rw [← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id])

/-- `HomGood` for a single term which is a biproduct. -/
private lemma HomGood.sing_biprod {M M' : Mod R} (h : HomGood hR (sing M a))
    (h' : HomGood hR (sing M' a)) : HomGood hR (sing (M ⊞ M') a) := by
  let S0 : ShortComplex (Mod R) :=
    ShortComplex.mk (biprod.inl : M ⟶ M ⊞ M') biprod.snd (by simp)
  let sp : S0.Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct M M'
  have key : HomGood hR (S0.map (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a)).X₂ :=
    HomGood.of_ses hR (S0.map (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a))
      (fun n ↦ (sp.map (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a)).map
        (HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n)) h h'
  exact key

end Single

/-- `HomGood` for a complex whose terms are all zero. -/
private lemma HomGood.of_isZero (hR : IsCommSheaf R) {P : CochainComplex (Mod R) ℤ}
    (hP : ∀ p, IsZero (P.X p)) : HomGood hR P := by
  intro L L' g _
  have hz : ∀ M : CochainComplex (Mod R) ℤ, IsZero (homSheafComplex hR P M) := fun M ↦ by
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    apply Pi.hom_ext
    intro T
    exact (isZero_homSheaf_left hR _ (hP T.p)).eq_of_tgt _ _
  have h0 : homComplexMap₂ hR P g = 0 := (hz L).eq_of_src _ _
  have : IsIso (homComplexMap₂ hR P g) := by
    rw [h0]
    exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hz L, hz L'⟩
  infer_instance

/-- `R^{m+1} ≅ R^m ⊞ R`. -/
private def freeSuccIso (m : ℕ) :
    (SheafOfModules.free (R := R) (Fin (m + 1))) ≅
      SheafOfModules.free (R := R) (Fin m) ⊞ SheafOfModules.unit R :=
  ((SheafOfModules.freeFunctor (R := R)).mapIso
      (finSumFinEquiv (m := m) (n := 1)).toIso).symm ≪≫
    (SheafOfModules.freeSumIso (R := R) (Fin m) (Fin 1)).symm ≪≫
    (biprod.isoCoprod _ _).symm ≪≫
    biprod.mapIso (Iso.refl _) (coproductUniqueIso (fun _ : Fin 1 ↦ SheafOfModules.unit R))

/-- `HomGood` for a single zero term. -/
private lemma HomGood.sing_of_isZero (hR : IsCommSheaf R) {M : Mod R} (a : ℤ) (hM : IsZero M) :
    HomGood hR (sing M a) := by
  refine HomGood.of_isZero hR fun p ↦ ?_
  by_cases hp : p = a
  · subst hp
    exact hM.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p M)
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hp

/-- `HomGood` for a single finite free term. -/
private lemma HomGood.sing_free (hR : IsCommSheaf R) (a : ℤ) (m : ℕ) :
    HomGood hR (sing (SheafOfModules.free (R := R) (Fin m)) a) := by
  induction m with
  | zero =>
    refine HomGood.sing_of_isZero hR a ?_
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro i
    exact i.elim0
  | succ m ih =>
    exact HomGood.sing_of_iso hR a (freeSuccIso m)
      (HomGood.sing_biprod hR a ih (HomGood.single_unit hR a))

/-- `HomGood` for a single term which is a direct summand of a finite free module. -/
private lemma HomGood.sing_of_isFinFreeSummand (hR : IsCommSheaf R) (a : ℤ) {M : Mod R}
    (hM : IsFinFreeSummand M) : HomGood hR (sing M a) := by
  obtain ⟨m, i, p, hip⟩ := hM
  exact HomGood.of_retract hR (HomGood.sing_free hR a m)
    ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).map i)
    ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).map p) (by
      rw [← Functor.map_comp, hip, CategoryTheory.Functor.map_id])

section Trunc

/-- Short complexes of complexes of sheaves of modules have homology (instance search does not
find the instance of an abelian category directly). -/
private instance categoryWithHomology_complex : CategoryWithHomology (CochainComplex (Mod R) ℤ) :=
  @categoryWithHomology_of_abelian (CochainComplex (Mod R) ℤ) _ _

variable (P : CochainComplex (Mod R) ℤ) (a : ℤ) [hGE : P.IsStrictlyGE a]

/-- The projection `P ⟶ Pᵃ[-a]` onto the lowest term of a complex in degrees `≥ a`. -/
private def truncπ : P ⟶ sing (P.X a) a :=
  HomologicalComplex.mkHomToSingle (𝟙 (P.X a)) fun i _ ↦ by
    by_cases hi : i < a
    · exact (CochainComplex.isZero_of_isStrictlyGE P a i hi).eq_of_src _ _
    · exfalso
      rename_i hr
      simp only [ComplexShape.up_Rel] at hr
      lia

/-- `truncπ` is an isomorphism in degree `a`. -/
private lemma isIso_truncπ_f_self : IsIso ((truncπ P a).f a) := by
  unfold truncπ
  rw [HomologicalComplex.mkHomToSingle_f]
  infer_instance

/-- The complex `M[-a]` is zero outside degree `a`. -/
private lemma isZero_sing_X {M : Mod R} (n : ℤ) (hn : n ≠ a) : IsZero ((sing M a).X n) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hn

/-- `truncπ` is degreewise epi. -/
private lemma epi_truncπ_f (n : ℤ) : Epi ((truncπ P a).f n) := by
  by_cases hn : n = a
  · subst hn
    have := isIso_truncπ_f_self P n
    infer_instance
  · exact (isZero_sing_X (M := P.X a) a n hn).epi _

/-- The short complex `ker π ⟶ P ⟶ Pᵃ[-a]`. -/
private def truncSES : ShortComplex (CochainComplex (Mod R) ℤ) :=
  ShortComplex.mk (kernel.ι (truncπ P a)) (truncπ P a) (kernel.condition _)

/-- The truncation sequence is short exact. -/
private lemma truncSES_shortExact : (truncSES P a).ShortExact where
  exact := by
    have : (truncSES P a).HasHomology := inferInstance
    exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := inferInstanceAs (Mono (kernel.ι (truncπ P a)))
  epi_g := HomologicalComplex.epi_of_epi_f _ fun n ↦ epi_truncπ_f P a n

/-- The degreewise splitting of `truncSES`. -/
private def truncSplit (n : ℤ) :
    ((truncSES P a).map (HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n)).Splitting := by
  have hS := ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (truncSES_shortExact P a)) n
  by_cases hn : n = a
  · subst hn
    have h := isIso_truncπ_f_self P n
    exact ShortComplex.Splitting.ofExactOfSection _ hS.exact (@inv _ _ _ _ _ h)
      (@IsIso.inv_hom_id _ _ _ _ _ h) hS.mono_f
  · exact ShortComplex.Splitting.ofExactOfSection _ hS.exact 0
      ((isZero_sing_X a n hn).eq_of_src _ _) hS.mono_f

/-- The inclusion of the kernel of `truncπ` is degreewise mono. -/
private lemma mono_truncS_f (n : ℤ) : Mono ((kernel.ι (truncπ P a)).f n) :=
  ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (truncSES_shortExact P a) n).mono_f

/-- The kernel of `truncπ` is zero where `P` is. -/
private lemma isZero_truncS_X (n : ℤ) (h : IsZero (P.X n)) :
    IsZero ((kernel (truncπ P a)).X n) :=
  haveI := mono_truncS_f P a n
  IsZero.of_mono ((kernel.ι (truncπ P a)).f n) h

/-- The kernel of `truncπ` is zero in degree `a`. -/
private lemma isZero_truncS_X_self : IsZero ((kernel (truncπ P a)).X a) := by
  have := mono_truncS_f P a a
  have := isIso_truncπ_f_self P a
  refine IsZero.of_mono_eq_zero ((kernel.ι (truncπ P a)).f a) ?_
  have h : (kernel.ι (truncπ P a)).f a ≫ (truncπ P a).f a = 0 := by
    rw [← HomologicalComplex.comp_f, kernel.condition]
    rfl
  exact (cancel_mono ((truncπ P a).f a)).1 (by rw [h, zero_comp])

end Trunc

/-- Direct summands of finite free modules: closed under retracts. -/
private lemma IsFinFreeSummand.of_retract' {M N : Mod R} (ι : M ⟶ N) (π : N ⟶ M)
    (h : ι ≫ π = 𝟙 M) (hN : IsFinFreeSummand N) : IsFinFreeSummand M := by
  obtain ⟨m, i, p, hip⟩ := hN
  exact ⟨m, ι ≫ i, p ≫ π, by
    rw [Category.assoc, ← Category.assoc i, hip, Category.id_comp, h]⟩

/-- The projection of a complex concentrated in the single degree `a` onto its term is an
isomorphism. -/
private lemma isIso_truncπ_of_le (P : CochainComplex (Mod R) ℤ) (a : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE a] : IsIso (truncπ P a) := by
  have : ∀ i, IsIso ((truncπ P a).f i) := fun i ↦ by
    by_cases hi : i = a
    · subst hi
      exact isIso_truncπ_f_self P i
    · have hz : IsZero (P.X i) := by
        rcases lt_or_gt_of_ne hi with h | h
        · exact CochainComplex.isZero_of_isStrictlyGE P a i h
        · exact CochainComplex.isZero_of_isStrictlyLE P a i h
      have h0 : (truncπ P a).f i = 0 := hz.eq_of_src _ _
      rw [h0]
      exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hz, isZero_sing_X a i hi⟩
  exact HomologicalComplex.Hom.isIso_of_components _

/-- `HomGood` for bounded complexes with terms direct summands of finite free modules, by induction
on the length (stupid truncation `0 → σ_{>a}P → P → Pᵃ[-a] → 0`). -/
lemma HomGood.of_bounded (hR : IsCommSheaf R) (n : ℕ) :
    ∀ (a : ℤ) (P : CochainComplex (Mod R) ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE (a + n)],
      (∀ i, IsFinFreeSummand (P.X i)) → HomGood hR P := by
  induction n with
  | zero =>
    intro a P _ hLE hP
    have : P.IsStrictlyLE a := by simpa using hLE
    have := isIso_truncπ_of_le P a
    exact HomGood.of_retract hR (HomGood.sing_of_isFinFreeSummand hR a (hP a)) (truncπ P a)
      (inv (truncπ P a)) (IsIso.hom_inv_id _)
  | succ n ih =>
    intro a P _ hLE hP
    have hGE' : (kernel (truncπ P a)).IsStrictlyGE (a + 1) := by
      refine (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦ ?_
      by_cases hia : i = a
      · subst hia
        exact isZero_truncS_X_self P i
      · exact isZero_truncS_X P a i (CochainComplex.isZero_of_isStrictlyGE P a i (by lia))
    have hLE' : (kernel (truncπ P a)).IsStrictlyLE (a + 1 + n) := by
      refine (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦ ?_
      exact isZero_truncS_X P a i (CochainComplex.isZero_of_isStrictlyLE P (a + ↑(n + 1)) i
        (by push_cast; lia))
    have hS : ∀ i, IsFinFreeSummand ((kernel (truncπ P a)).X i) := fun i ↦
      IsFinFreeSummand.of_retract' ((kernel.ι (truncπ P a)).f i) (truncSplit P a i).r
        (truncSplit P a i).f_r (hP i)
    have h1 : HomGood hR (kernel (truncπ P a)) := ih (a + 1) _ hS
    have h3 : HomGood hR (sing (P.X a) a) := HomGood.sing_of_isFinFreeSummand hR a (hP a)
    exact HomGood.of_ses hR (truncSES P a) (truncSplit P a) h1 h3

end Cohesive
