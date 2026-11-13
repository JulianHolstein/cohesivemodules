import Cohesivemodules.Sheaf.Flat.Tensor

set_option linter.style.header false

/-!
# S8 (part 5): flat coproducts and K-flat complexes

Blueprint item S8 (§3), S8.b (`isFlat_sigma`), S8.d (`isKFlat_of_isFlat`) and S8.e
(`quasiIso_tensorCMap₂`). Split from `Sheaf/Flat.lean` for size only (CLAUDE.md: "New work goes
in small new files"); no mathematical change. See the module doc of `Sheaf/Flat.lean` for
deviations.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]

variable (R : Sheaf J CommRingCat.{0})

section ColimGen

variable {K : Type} [SmallCategory K]

/-- The comparison `colim (D ⋙ forget) ⟶ forget (colim D)`. -/
private noncomputable def piCompK (D : K ⥤ Mod (ringOf R)) :
    colimit (D ⋙ SheafOfModules.forget (ringOf R)) ⟶
      (SheafOfModules.forget (ringOf R)).obj (colimit D) :=
  colimit.post D (SheafOfModules.forget (ringOf R))

/-- The adjoint transpose of `piCompK`. -/
private noncomputable def phiPiK (D : K ⥤ Mod (ringOf R)) :
    (sheafifyF R).obj (colimit (D ⋙ SheafOfModules.forget (ringOf R))) ⟶ colimit D :=
  (sheafifyF R).map (piCompK R D) ≫
    (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit.app (colimit D)

/-- The counit of the sheafification adjunction as a natural transformation
`forget ⋙ sheafifyF ⟶ 𝟭`. -/
private noncomputable def cnat : SheafOfModules.forget (ringOf R) ⋙ sheafifyF R ⟶
    𝟭 (Mod (ringOf R)) where
  app M := (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit.app M
  naturality _ _ f :=
    (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit.naturality f

/-- The counit of sheafification is an isomorphism. -/
private instance isIso_cnat_app (M : Mod (ringOf R)) : IsIso ((cnat R).app M) :=
  NatIso.isIso_app_of_isIso
    (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit M

/-- The adjoint transpose of `piCompK` is an isomorphism. -/
private lemma isIso_phiPiK (D : K ⥤ Mod (ringOf R)) : IsIso (phiPiK R D) := by
  have hs : IsIso (colimit.post (D ⋙ SheafOfModules.forget (ringOf R)) (sheafifyF R)) :=
    inferInstance
  have : IsIso (cnat R) := NatIso.isIso_of_isIso_app _
  have hc : IsIso (colimMap (Functor.whiskerLeft D (cnat R))) := inferInstance
  have key : colimit.post (D ⋙ SheafOfModules.forget (ringOf R)) (sheafifyF R) ≫ phiPiK R D =
      colimMap (Functor.whiskerLeft D (cnat R)) := by
    refine colimit.hom_ext (fun j => ?_)
    unfold phiPiK
    have e : (sheafifyF R).map (colimit.ι (D ⋙ SheafOfModules.forget (ringOf R)) j) ≫
        (sheafifyF R).map (piCompK R D) =
        (sheafifyF R).map ((SheafOfModules.forget (ringOf R)).map (colimit.ι D j)) := by
      rw [← Functor.map_comp]
      unfold piCompK
      rw [colimit.ι_post]
    rw [colimit.ι_post_assoc]
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans ?_)
    refine ((cnat R).naturality (colimit.ι D j)).trans ?_
    exact (ι_colimMap (Functor.whiskerLeft D (cnat R)) j).symm
  have : IsIso (colimit.post (D ⋙ SheafOfModules.forget (ringOf R)) (sheafifyF R) ≫
      phiPiK R D) := by rw [key]; exact hc
  exact IsIso.of_isIso_comp_left (colimit.post (D ⋙ SheafOfModules.forget (ringOf R))
    (sheafifyF R)) _

/-- `piCompK` factors through the unit of sheafification. -/
private lemma piCompK_eq (D : K ⥤ Mod (ringOf R)) :
    (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app _ ≫
      (SheafOfModules.forget (ringOf R)).map (phiPiK R D) = piCompK R D := by
  set adj := PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj) with hadj
  unfold phiPiK
  have h1 := adj.right_triangle_components (colimit D)
  have h2 := adj.unit.naturality (piCompK R D)
  have h3 : adj.unit.app (colimit (D ⋙ SheafOfModules.forget (ringOf R))) ≫
      (SheafOfModules.forget (ringOf R)).map ((sheafifyF R).map (piCompK R D)) =
      piCompK R D ≫ adj.unit.app ((SheafOfModules.forget (ringOf R)).obj (colimit D)) := h2.symm
  exact (congrArg (adj.unit.app _ ≫ ·) (Functor.map_comp (SheafOfModules.forget (ringOf R))
    ((sheafifyF R).map (piCompK R D)) (adj.counit.app (colimit D)))).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h3).trans
    ((Category.assoc _ _ _).trans ((congrArg (piCompK R D ≫ ·) h1).trans (Category.comp_id _)))))

/-- Sectionwise tensoring with `N` followed by sheafification inverts `piCompK`. -/
private lemma isIso_PsiF_map_piCompK (D : K ⥤ Mod (ringOf R))
    (N : PresheafOfModules.{0} (ringOf R).obj) : IsIso ((PsiF R N).map (piCompK R D)) := by
  have := isIso_phiPiK R D
  have h1 : IsIso ((PsiF R N).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app
        (colimit (D ⋙ SheafOfModules.forget (ringOf R))))) :=
    isIso_sheafifyF_map_whiskerRight R
      (colimit (D ⋙ SheafOfModules.forget (ringOf R))) N
  have h2 : IsIso ((PsiF R N).map ((SheafOfModules.forget (ringOf R)).map (phiPiK R D))) :=
    Functor.map_isIso _ _
  rw [← piCompK_eq R D]
  erw [Functor.map_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- `forget ⋙ PsiF (forget M)` is the tensor product `- ⊗ M`. -/
private lemma flip_obj_eq (M : Mod (ringOf R)) :
    (tensorBifunctor R).flip.obj M =
      SheafOfModules.forget (ringOf R) ⋙ PsiF R ((SheafOfModules.forget (ringOf R)).obj M) :=
  rfl

/-- Tensoring on the right, `- ⊗ M`, preserves all colimits of shape `K`. -/
private noncomputable instance preservesColimit_flip (M : Mod (ringOf R))
    (D : K ⥤ Mod (ringOf R)) : PreservesColimit D ((tensorBifunctor R).flip.obj M) := by
  rw [flip_obj_eq]
  refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D) ?_
  have hc : IsColimit ((PsiF R ((SheafOfModules.forget (ringOf R)).obj M)).mapCocone
      (colimit.cocone (D ⋙ SheafOfModules.forget (ringOf R)))) :=
    isColimitOfPreserves _ (colimit.isColimit _)
  have := isIso_PsiF_map_piCompK R D ((SheafOfModules.forget (ringOf R)).obj M)
  refine IsColimit.ofIsoColimit hc (Cocone.ext
    (asIso ((PsiF R ((SheafOfModules.forget (ringOf R)).obj M)).map (piCompK R D))) ?_)
  intro j
  show (PsiF R ((SheafOfModules.forget (ringOf R)).obj M)).map
      (colimit.ι (D ⋙ SheafOfModules.forget (ringOf R)) j) ≫
      (PsiF R ((SheafOfModules.forget (ringOf R)).obj M)).map (piCompK R D) =
      (PsiF R ((SheafOfModules.forget (ringOf R)).obj M)).map
        ((SheafOfModules.forget (ringOf R)).map (colimit.ι D j))
  rw [← Functor.map_comp]
  unfold piCompK
  rw [colimit.ι_post]

end ColimGen

/-- **S8.b.** Coproducts of flat modules are flat. -/
theorem isFlat_sigma {ι : Type} (M : ι → Mod (ringOf R)) (hM : ∀ i, IsFlat R (M i)) :
    IsFlat R (∐ M) where
  preserves {A B} f hf := by
    have : ∀ i, Mono (((tensorBifunctor R).obj (M i)).map f) := fun i =>
      (hM i).preserves f
    have : Mono (Limits.Sigma.map (fun i => ((tensorBifunctor R).obj (M i)).map f)) :=
      inferInstance
    have h : ((tensorBifunctor R).obj (∐ M)).map f = inv (cSigma R M A) ≫
        Limits.Sigma.map (fun i => ((tensorBifunctor R).obj (M i)).map f) ≫ cSigma R M B :=
      (IsIso.eq_inv_comp _).2 (cSigma_naturality R M f).symm
    rw [h]
    infer_instance

/-- `M ⊗ -` preserves colimits (it is isomorphic to `- ⊗ M`). -/
private noncomputable instance preservesColimitsOfShape_tensorObj (M : Mod (ringOf R))
    (K : Type) [SmallCategory K] : PreservesColimitsOfShape K ((tensorBifunctor R).obj M) :=
  haveI : PreservesColimitsOfShape K ((tensorBifunctor R).flip.obj M) :=
    ⟨inferInstance⟩
  preservesColimitsOfShape_of_natIso ((tensorBifunctorFlipIso R).app M)

/-- A flat module `M` gives an exact functor `M ⊗ -`: it preserves homology. -/
private lemma IsFlat.preservesHomology {M : Mod (ringOf R)} (hM : IsFlat R M) :
    ((tensorBifunctor R).obj M).PreservesHomology := by
  have : ((tensorBifunctor R).obj M).PreservesMonomorphisms := hM
  have : ((tensorBifunctor R).obj M).PreservesZeroMorphisms := inferInstance
  have : ∀ {X Y : Mod (ringOf R)} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) ((tensorBifunctor R).obj M) := fun f => inferInstance
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- A functor preserving homology maps acyclic complexes to acyclic complexes. -/
private lemma acyclic_mapHomologicalComplex {F : Mod (ringOf R) ⥤ Mod (ringOf R)}
    [F.PreservesZeroMorphisms] [F.PreservesHomology] {L : CochainComplex (Mod (ringOf R)) ℤ}
    (hL : L.Acyclic) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic := fun j => by
  rw [HomologicalComplex.exactAt_iff' _ (j - 1) j (j + 1) (by simp) (by simp)]
  exact ((HomologicalComplex.exactAt_iff' L (j - 1) j (j + 1) (by simp) (by simp)).1 (hL j)).map F

/-- A flat module placed in degree `0` is K-flat. -/
private lemma isKFlat_single {G : Mod (ringOf R)} (hG : IsFlat R G) :
    IsKFlat R ((HomologicalComplex.single (Mod (ringOf R)) (ComplexShape.up ℤ) 0).obj G) := by
  intro L hL
  haveI := IsFlat.preservesHomology R hG
  exact fun j => (acyclic_mapHomologicalComplex R hL j).of_iso (tensorCSingleIso R G L).symm

/-- K-flatness is invariant under isomorphism. -/
private lemma IsKFlat.of_iso {K K' : CochainComplex (Mod (ringOf R)) ℤ} (e : K ≅ K')
    (h : IsKFlat R K) : IsKFlat R K' := fun L hL i =>
  (h L hL i).of_iso (((tensorBifunctor R).map₂CochainComplex.mapIso e).app L)

/-- The shift of an acyclic complex is acyclic. -/
private lemma acyclic_shift {K : CochainComplex (Mod (ringOf R)) ℤ} (hK : K.Acyclic) (x : ℤ) :
    (K⟦x⟧).Acyclic := fun i => by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have h := hK (x + i)
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h
  exact h.of_iso ((CochainComplex.ShiftSequence.shiftIso (Mod (ringOf R)) x i (x + i) rfl).app K)

/-- Shifts of K-flat complexes are K-flat. -/
private lemma IsKFlat.shift {K : CochainComplex (Mod (ringOf R)) ℤ} (hK : IsKFlat R K) (x : ℤ) :
    IsKFlat R (K⟦x⟧) := fun L hL i =>
  (acyclic_shift R (hK L hL) x i).of_iso
    (mapBifunctorShift₁IsoAux K L (tensorBifunctor R) x).symm

/-- A flat module placed in an arbitrary degree is K-flat. -/
private lemma isKFlat_single_degree {G : Mod (ringOf R)} (hG : IsFlat R G) (s : ℤ) :
    IsKFlat R ((HomologicalComplex.single (Mod (ringOf R)) (ComplexShape.up ℤ) s).obj G) :=
  IsKFlat.of_iso R (((CochainComplex.singleFunctors (Mod (ringOf R))).shiftIso (-s) s 0
    (by omega)).app G) ((isKFlat_single R hG).shift R (-s))

section PhiL

variable (L : CochainComplex (Mod (ringOf R)) ℤ)

/-- The functor `K ↦ K ⊗ L` on complexes. -/
private noncomputable abbrev PhiL :
    CochainComplex (Mod (ringOf R)) ℤ ⥤ CochainComplex (Mod (ringOf R)) ℤ :=
  (tensorBifunctor R).map₂CochainComplex.flip.obj L

/-- The index set of the degree `n` part of a total complex. -/
private abbrev TotIdx (n : ℤ) : Type :=
  ↥((ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⁻¹' {n})

/-- The family of summands `X^p ⊗ L^q` (`p + q = n`) of `(X ⊗ L)^n`, functorial in `X`. -/
private noncomputable def XiPhi (n : ℤ) :
    CochainComplex (Mod (ringOf R)) ℤ ⥤ (Discrete (TotIdx n) ⥤ Mod (ringOf R)) where
  obj X := Discrete.functor fun i => ((tensorBifunctor R).obj (X.X i.1.1)).obj (L.X i.1.2)
  map f := Discrete.natTrans fun i =>
    ((tensorBifunctor R).map (f.f i.as.1.1)).app (L.X i.as.1.2)

/-- `(X ⊗ L)^n` is the coproduct of the summands. -/
private noncomputable def thetaPhi (n : ℤ) :
    PhiL R L ⋙ HomologicalComplex.eval _ _ n ≅ XiPhi R L n ⋙ colim :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    refine HomologicalComplex.mapBifunctor.hom_ext (fun p q h => ?_)
    have e1 : HomologicalComplex.ιMapBifunctor X L (tensorBifunctor R) (ComplexShape.up ℤ)
        p q n h ≫ (HomologicalComplex.mapBifunctorMap f (𝟙 L) (tensorBifunctor R)
          (ComplexShape.up ℤ)).f n = ((tensorBifunctor R).map (f.f p)).app (L.X q) ≫
          HomologicalComplex.ιMapBifunctor Y L (tensorBifunctor R) (ComplexShape.up ℤ)
            p q n h := by
      rw [HomologicalComplex.ι_mapBifunctorMap]
      simp
    have e2 := ι_colimMap ((XiPhi R L n).map f) ⟨⟨(p, q), h⟩⟩
    exact (Category.comp_id _).trans (e1.trans ((Category.comp_id _).symm.trans
      (e2.symm.trans (congrArg _ (Category.id_comp _).symm)))))

/-- `X ↦ (X^p ⊗ L^q)_{p+q=n}` preserves colimits (they are computed pointwise). -/
private noncomputable instance XiPhi_pres (n : ℤ) (K : Type) [SmallCategory K] :
    PreservesColimitsOfShape K (XiPhi R L n) :=
  preservesColimitsOfShape_of_evaluation _ _ (fun i => by
    have h1 : PreservesColimitsOfShape K ((tensorBifunctor R).flip.obj (L.X i.as.1.2)) :=
      ⟨inferInstance⟩
    exact (inferInstance : PreservesColimitsOfShape K
      (HomologicalComplex.eval (Mod (ringOf R)) (ComplexShape.up ℤ) i.as.1.1 ⋙
        (tensorBifunctor R).flip.obj (L.X i.as.1.2))))

/-- `K ↦ K ⊗ L` preserves colimits. -/
private noncomputable instance PhiL_pres (K : Type) [SmallCategory K] :
    PreservesColimitsOfShape K (PhiL R L) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n =>
    preservesColimitsOfShape_of_natIso (thetaPhi R L n).symm)

/-- `K ↦ K ⊗ L` preserves zero morphisms. -/
private instance PhiL_zero : (PhiL R L).PreservesZeroMorphisms := inferInstance

/-- The degree `n` component of `f ⊗ L` is the coproduct of the maps `f^p ⊗ L^q`. -/
private lemma PhiL_map_f_eq {X Y : CochainComplex (Mod (ringOf R)) ℤ} (f : X ⟶ Y) (n : ℤ) :
    ((PhiL R L).map f).f n = colimMap ((XiPhi R L n).map f) := by
  have := (thetaPhi R L n).hom.naturality f
  exact (Category.comp_id _).symm.trans (this.trans (Category.id_comp _))

/-- `f ⊗ L` is a degreewise monomorphism if all maps `f^p ⊗ L^q` are monomorphisms. -/
private lemma mono_PhiL_map {X Y : CochainComplex (Mod (ringOf R)) ℤ} (f : X ⟶ Y)
    (hf : ∀ p q : ℤ, Mono (((tensorBifunctor R).map (f.f p)).app (L.X q))) :
    Mono ((PhiL R L).map f) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n => ?_
  rw [PhiL_map_f_eq]
  have : ∀ i : TotIdx n, Mono (((tensorBifunctor R).map (f.f i.1.1)).app (L.X i.1.2)) :=
    fun i => hf _ _
  exact (inferInstance : Mono (Limits.Sigma.map fun i : TotIdx n =>
    ((tensorBifunctor R).map (f.f i.1.1)).app (L.X i.1.2)))

end PhiL

/-- `X ⊗ Y` is zero when `X` is zero. -/
private lemma isZero_tensorObj_obj {Z : Mod (ringOf R)} (hZ : IsZero Z) (Y : Mod (ringOf R)) :
    IsZero (((tensorBifunctor R).obj Z).obj Y) := by
  haveI : ∀ X, ((tensorBifunctor R).flip.obj X).Additive := fun X => { }
  exact Functor.map_isZero ((tensorBifunctor R).flip.obj Y) hZ

/-- The inclusion `σ_{≥m+1} F ⟶ σ_{≥m} F` stays a monomorphism after `- ⊗ L`. -/
private lemma mono_PhiL_brutalTr (F L : CochainComplex (Mod (ringOf R)) ℤ) (m : ℤ) :
    Mono ((PhiL R L).map (brutalTr F (show m ≤ m + 1 by omega))) := by
  refine mono_PhiL_map R L _ (fun p q => ?_)
  by_cases hp : m + 1 ≤ p
  · have h1 : IsIso ((brutalTr F (show m ≤ m + 1 by omega)).f p) := by
      rw [brutalTr_f_pos F _ hp]
      infer_instance
    have h2 : IsIso ((tensorBifunctor R).map ((brutalTr F (show m ≤ m + 1 by omega)).f p)) :=
      inferInstance
    infer_instance
  · exact (isZero_tensorObj_obj R (isZero_brutal_X F (by omega)) _).mono _

/-- The inductive step: if `σ_{≥m+1} F ⊗ L` is acyclic and `F^m` is flat, so is
`σ_{≥m} F ⊗ L` (for `L` acyclic). -/
private lemma acyclic_PhiL_brutal_step (F : CochainComplex (Mod (ringOf R)) ℤ) (m : ℤ)
    (hG : IsFlat R (F.X m)) {L : CochainComplex (Mod (ringOf R)) ℤ} (hL : L.Acyclic)
    (h : ((PhiL R L).obj (brutal F (m + 1))).Acyclic) :
    ((PhiL R L).obj (brutal F m)).Acyclic := by
  have hS0 := brutalSES_shortExact F m
  let S1 := (brutalSES F m).map (PhiL R L)
  have hmono : Mono S1.f := mono_PhiL_brutalTr R F L m
  have hcok : IsColimit (CokernelCofork.ofπ S1.g S1.zero) :=
    isColimitCoforkMapOfIsColimit' (PhiL R L) (brutalSES F m).zero hS0.gIsCokernel
  have hex : S1.Exact := by
    refine HomologicalComplex.exact_of_degreewise_exact S1 (fun n => ?_)
    refine ShortComplex.exact_of_g_is_cokernel _ ?_
    exact isColimitCoforkMapOfIsColimit' (PhiL R L ⋙ HomologicalComplex.eval _ _ n)
      (brutalSES F m).zero hS0.gIsCokernel
  have hS1 : S1.ShortExact := ShortComplex.ShortExact.mk' hex hmono
    (epi_of_isColimit_cofork hcok)
  have h3 : S1.X₃.Acyclic := isKFlat_single_degree R hG m L hL
  exact hS1.acyclic_X₂ h h3

/-- **S8.d.** Bounded-above complexes of flat modules are K-flat. -/
theorem isKFlat_of_isFlat (F : CochainComplex (Mod (ringOf R)) ℤ) (b : ℤ) [F.IsStrictlyLE b]
    (hF : ∀ n, IsFlat R (F.X n)) : IsKFlat R F := by
  intro L hL
  have hbase : ∀ m, b < m → ((PhiL R L).obj (brutal F m)).Acyclic := by
    intro m hm
    have hz : IsZero (brutal F m) := by
      rw [IsZero.iff_id_eq_zero]
      refine HomologicalComplex.hom_ext _ _ fun p => ?_
      by_cases hp : p < m
      · exact (isZero_brutal_X F hp).eq_of_src _ _
      · exact ((CochainComplex.isZero_of_isStrictlyLE F b p (by omega)).of_iso
          (brutalXIso F (by omega))).eq_of_src _ _
    exact HomologicalComplex.acyclic_of_isZero _ (Functor.map_isZero (PhiL R L) hz)
  have key : ∀ (k : ℕ) (m : ℤ), b + 1 ≤ m + k → ((PhiL R L).obj (brutal F m)).Acyclic := by
    intro k
    induction k with
    | zero => intro m hm; exact hbase m (by omega)
    | succ k ih =>
      intro m hm
      exact acyclic_PhiL_brutal_step R F m (hF m) hL (ih (m + 1) (by omega))
  have hall : ∀ m, ((PhiL R L).obj (brutal F m)).Acyclic := fun m =>
    key (b + 1 - m).toNat m (by omega)
  have hc : IsColimit ((PhiL R L).mapCocone (brutalCocone F)) :=
    isColimitOfPreserves (PhiL R L) (isColimit_brutalCocone F)
  exact acyclic_of_isColimit (D := brutalFunctor F ⋙ PhiL R L) (fun j => hall j.unop) hc

/-- **S8.e.** For `K` K-flat, `K ⊗ -` maps quasi-isomorphisms to quasi-isomorphisms (the cone
of `K ⊗ g` is `K ⊗ cone g`). -/
theorem quasiIso_tensorCMap₂ {K : CochainComplex (Mod (ringOf R)) ℤ} (hK : IsKFlat R K)
    {L L' : CochainComplex (Mod (ringOf R)) ℤ} (g : L ⟶ L') [QuasiIso g] :
    QuasiIso (tensorCMap₂ R K g) := by
  have h1 := (quasiIso_iff_acyclic_mappingCone g).1 inferInstance
  have h2 := hK _ h1
  refine (quasiIso_iff_acyclic_mappingCone (tensorCMap₂ R K g)).2 ?_
  exact fun i => (h2 i).of_iso (tensorCConeIso₂ R K g)

end Site

end Cohesive
