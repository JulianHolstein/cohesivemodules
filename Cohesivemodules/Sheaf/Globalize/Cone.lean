import Cohesivemodules.Sheaf.Perfect
import Cohesivemodules.Sheaf.Projective
import Cohesivemodules.Sheaf.Hom
import Cohesivemodules.Sheaf.Derived

set_option linter.style.header false

/-!
# S10 (part 1): homology of mapping cones

Blueprint item S10 (§3). Split from `Sheaf/Globalize.lean` for size only (CLAUDE.md: "New work
goes in small new files"); no mathematical change.

Lemmas on the homology of mapping cones in an abelian category: exactness of a cone from
epi/mono conditions on homology, the step construction (adding a single object to kill homology,
via an octahedron) and the invariance of cone homology under homotopy and
quasi-isomorphisms.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

section ConeLemmas

variable {C : Type*} [Category C] [Abelian C]

/-- Arrow iso between homology of the quotient image and the complex-level homology map. -/
private noncomputable def Q_homology_arrow_iso {F K : CochainComplex C ℤ} (φ : F ⟶ K) (i : ℤ) :
    Arrow.mk ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ)) ≅
      Arrow.mk (HomologicalComplex.homologyMap φ i) :=
  Arrow.isoMk ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app F)
    ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app K)
    (((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).hom.naturality φ).symm)

/-- Exactness of the cone gives epi on homology. -/
lemma cone_homology_epi {F K : CochainComplex C ℤ} (φ : F ⟶ K) (i : ℤ)
    (h : (CochainComplex.mappingCone φ).ExactAt i) : Epi (HomologicalComplex.homologyMap φ i) := by
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished φ
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  have h1 := (H.homologySequence_epi_shift_map_mor₁_iff _ hT i)
  have hz : IsZero ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone φ))) :=
    IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
      ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app _)
  have h3 : Epi ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ)) :=
    h1.2 (hz.eq_of_tgt _ _)
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.epimorphisms C)
    (Q_homology_arrow_iso φ i)).1 h3

/-- Exactness of the cone gives mono on homology. -/
lemma cone_homology_mono {F K : CochainComplex C ℤ} (φ : F ⟶ K) (i : ℤ)
    (h : (CochainComplex.mappingCone φ).ExactAt (i - 1)) :
    Mono (HomologicalComplex.homologyMap φ i) := by
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished φ
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  have h1 := (H.homologySequence_mono_shift_map_mor₁_iff _ hT (i - 1) i (by omega))
  have hz : IsZero ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) (i - 1)).obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone φ))) :=
    IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
      ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) (i - 1)).app _)
  have h3 : Mono ((HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) i).map
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ)) :=
    h1.2 (hz.eq_of_src _ _)
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.monomorphisms C)
    (Q_homology_arrow_iso φ i)).1 h3

/-- Epi and mono on homology give exactness of the cone. -/
lemma cone_exactAt_of {F K : CochainComplex C ℤ} (φ : F ⟶ K) (i : ℤ)
    (he : Epi (HomologicalComplex.homologyMap φ i))
    (hm : Mono (HomologicalComplex.homologyMap φ (i + 1))) :
    (CochainComplex.mappingCone φ).ExactAt i := by
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished φ
  let H := HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) 0
  have h1 := (H.homologySequence_epi_shift_map_mor₁_iff _ hT i).1
    ((MorphismProperty.arrow_mk_iso_iff (MorphismProperty.epimorphisms C)
      (Q_homology_arrow_iso φ i)).2 he)
  have h2 := (H.homologySequence_mono_shift_map_mor₁_iff _ hT i (i + 1) rfl).1
    ((MorphismProperty.arrow_mk_iso_iff (MorphismProperty.monomorphisms C)
      (Q_homology_arrow_iso φ (i + 1))).2 hm)
  have hex := H.homologySequence_exact₃ _ hT i (i + 1) rfl
  have hz := (hex.isZero_X₂_iff).2 ⟨h1, h2⟩
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact IsZero.of_iso hz
    (((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) i).app _).symm)

end ConeLemmas

section StepLemmas

open Pretriangulated

variable {A : Type*} [Category A] [Abelian A]

/-- chain map from a single complex given by a cycle -/
private noncomputable def singleToComplex (K : CochainComplex A ℤ) (j : ℤ) (G : A) (z : G ⟶ K.X j)
    (hz : z ≫ K.d j (j + 1) = 0) :
    (HomologicalComplex.single A (ComplexShape.up ℤ) j).obj G ⟶ K where
  f i := if h : i = j then
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) j G i h).hom ≫ z ≫
        eqToHom (by rw [h])
    else 0
  comm' i i' hii' := by
    by_cases h : i = j
    · subst h
      have hi' : i' = i + 1 := by simpa using hii'.symm
      subst hi'
      simp [hz]
    · simp [h]

/-- The `j`-component of `singleToComplex`. -/
private lemma singleToComplex_f_self (K : CochainComplex A ℤ) (j : ℤ) (G : A) (z : G ⟶ K.X j)
    (hz : z ≫ K.d j (j + 1) = 0) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j G).inv ≫
      (singleToComplex K j G z hz).f j = z := by
  simp [singleToComplex, HomologicalComplex.singleObjXSelf]

/-- `singleToComplex` of a cycle that is epi onto homology is epi on `H^j`. -/
private lemma epi_homologyMap_singleToComplex (K : CochainComplex A ℤ) (j : ℤ) (G : A)
    (ρ : G ⟶ K.cycles j) (hρ : Epi (ρ ≫ K.homologyπ j))
    (hz : (ρ ≫ K.iCycles j) ≫ K.d j (j + 1) = 0) :
    Epi (HomologicalComplex.homologyMap (singleToComplex K j G (ρ ≫ K.iCycles j) hz) j) := by
  set ζ := singleToComplex K j G (ρ ≫ K.iCycles j) hz
  let σ := HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) j G
  have h1 : σ.inv ≫ HomologicalComplex.cyclesMap ζ j = ρ := by
    rw [← cancel_mono (K.iCycles j), Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc]
    exact singleToComplex_f_self K j G _ hz
  have h2 : Epi (HomologicalComplex.cyclesMap ζ j ≫ K.homologyπ j) := by
    have : Epi (σ.inv ≫ HomologicalComplex.cyclesMap ζ j ≫ K.homologyπ j) := by
      rw [← Category.assoc, h1]; exact hρ
    exact (epi_comp_iff_of_epi σ.inv _).1 this
  rw [← HomologicalComplex.homologyπ_naturality] at h2
  exact epi_of_epi (((HomologicalComplex.single A (ComplexShape.up ℤ) j).obj G).homologyπ j) _

/-- The cone of `singleToComplex` is exact in degrees `≥ j`. -/
private lemma exactAt_cone_singleToComplex (K : CochainComplex A ℤ) (j : ℤ) (G : A)
    (ρ : G ⟶ K.cycles j) (hρ : Epi (ρ ≫ K.homologyπ j))
    (hz : (ρ ≫ K.iCycles j) ≫ K.d j (j + 1) = 0) (hK : ∀ i, j + 1 ≤ i → K.ExactAt i)
    (i : ℤ) (hi : j ≤ i) :
    (CochainComplex.mappingCone (singleToComplex K j G (ρ ≫ K.iCycles j) hz)).ExactAt i := by
  apply cone_exactAt_of
  · rcases eq_or_lt_of_le hi with rfl | hlt
    · exact epi_homologyMap_singleToComplex K _ G ρ hρ hz
    · have := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hK i (by omega))
      exact this.epi _
  · have := HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) j G (i + 1)
      (by omega)
    exact this.mono _

section Octa

variable {𝓣 : Type*} [Category 𝓣] [Preadditive 𝓣] [HasZeroObject 𝓣] [HasShift 𝓣 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝓣 n).Additive] [Pretriangulated 𝓣] [IsTriangulated 𝓣]

/-- Octahedron step: attaching a cell to the cone. -/
private lemma oct_aux (T : Triangle 𝓣) (hT : T ∈ distTriang 𝓣) {G Z : 𝓣} (ζ : G ⟶ T.obj₃)
    (j : T.obj₃ ⟶ Z) (y : Z ⟶ G⟦(1 : ℤ)⟧)
    (hζ : Triangle.mk ζ j y ∈ distTriang 𝓣) :
    ∃ (F' : 𝓣) (φ' : F' ⟶ T.obj₂) (w : Z ⟶ F'⟦(1 : ℤ)⟧) (m₁ : T.obj₁ ⟶ F') (m₃ : F' ⟶ G),
      Triangle.mk φ' (T.mor₂ ≫ j) w ∈ distTriang 𝓣 ∧
      Triangle.mk m₁ m₃ (ζ ≫ T.mor₃) ∈ distTriang 𝓣 := by
  obtain ⟨F', φ', w, h₁₃⟩ := distinguished_cocone_triangle₁ (T.mor₂ ≫ j)
  have hT' : Triangle.mk T.mor₁ T.mor₂ T.mor₃ ∈ distTriang 𝓣 := hT
  let o := Triangulated.someOctahedron' (u₁₂ := T.mor₂) (u₂₃ := j) rfl hT' hζ h₁₃
  exact ⟨F', φ', w, o.m₁, o.m₃, h₁₃, o.mem⟩

end Octa

/-- **S10, step 1 (algebraic core).** Attach a free term in degree `k - 1` killing `H^{k-1}` of
the cone. -/
lemma step_construct {F K : CochainComplex A ℤ} (φ : F ⟶ K) (k : ℤ)
    (hex : ∀ i, k ≤ i → (CochainComplex.mappingCone φ).ExactAt i) (G : A)
    (ρ : G ⟶ (CochainComplex.mappingCone φ).cycles (k - 1))
    (hρ : Epi (ρ ≫ (CochainComplex.mappingCone φ).homologyπ (k - 1))) :
    ∃ (F' : CochainComplex A ℤ) (φ' : F' ⟶ K),
      (∀ i, k - 1 ≤ i → (CochainComplex.mappingCone φ').ExactAt i) ∧
      ∀ n, ∃ G₀ : A, (IsZero G₀ ∨ Nonempty (G₀ ≅ G)) ∧ (n ≠ k - 1 → IsZero G₀) ∧
        Nonempty (F'.X n ≅ G₀ ⊞ F.X n) := by
  have hz : (ρ ≫ (CochainComplex.mappingCone φ).iCycles (k - 1)) ≫
      (CochainComplex.mappingCone φ).d (k - 1) (k - 1 + 1) = 0 := by simp
  obtain ⟨ζ, hζ⟩ : ∃ ζ, ζ = singleToComplex (CochainComplex.mappingCone φ) (k - 1) G
      (ρ ≫ (CochainComplex.mappingCone φ).iCycles (k - 1)) hz := ⟨_, rfl⟩
  have hexζ : ∀ i, k - 1 ≤ i → (CochainComplex.mappingCone ζ).ExactAt i := fun i hi => by
    rw [hζ]
    exact exactAt_cone_singleToComplex (CochainComplex.mappingCone φ) (k - 1) G ρ hρ hz
      (fun i hi => hex i (by omega)) i hi
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished φ
  have hTζ := HomotopyCategory.mappingCone_triangleh_distinguished ζ
  obtain ⟨F₀, φ₀, w, m₁, m₃, hA, hB⟩ := oct_aux (CochainComplex.mappingCone.triangleh φ) hT
    (Q.map ζ) (CochainComplex.mappingCone.triangleh ζ).mor₂
    (CochainComplex.mappingCone.triangleh ζ).mor₃ hTζ
  have hinv := inv_rot_of_distTriang _ hB
  let eG : Q.obj ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).obj
      ((HomologicalComplex.single A (ComplexShape.up ℤ) (k - 1)).obj G)) ≅
      (CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (-1 : ℤ)).obj
      (Q.obj ((HomologicalComplex.single A (ComplexShape.up ℤ) (k - 1)).obj G)) :=
    (Q.commShiftIso (-1 : ℤ)).app _
  obtain ⟨θ, hθ⟩ := Q.map_surjective (eG.hom ≫
    (Triangle.mk m₁ m₃ (Q.map ζ ≫ (CochainComplex.mappingCone.triangleh φ).mor₃)).invRotate.mor₁)
  have hθd := HomotopyCategory.mappingCone_triangleh_distinguished θ
  let ε : Q.obj (CochainComplex.mappingCone θ) ≅ F₀ :=
    Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _ hθd hinv eG (Iso.refl _) (by
      exact (Category.comp_id _).trans hθ))
  obtain ⟨φ', hφ'⟩ := Q.map_surjective (ε.hom ≫ φ₀)
  have hT13 : Triangle.mk (ε.hom ≫ φ₀) ((CochainComplex.mappingCone.triangleh φ).mor₂ ≫
      (CochainComplex.mappingCone.triangleh ζ).mor₂)
      (w ≫ (CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) (1 : ℤ)).map
        ε.inv) ∈ distTriang (HomotopyCategory A (ComplexShape.up ℤ)) := by
    refine isomorphic_distinguished _ hA _ (Triangle.isoMk _ _ ε (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [← Functor.map_comp]))
  have hφd := HomotopyCategory.mappingCone_triangleh_distinguished φ'
  let ε₃ : Q.obj (CochainComplex.mappingCone φ') ≅ Q.obj (CochainComplex.mappingCone ζ) :=
    Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ _ hφd hT13 (Iso.refl _) (Iso.refl _) (by
      exact (Category.comp_id _).trans (hφ'.trans (Category.id_comp _).symm)))
  refine ⟨CochainComplex.mappingCone θ, φ', ?_, fun n => ?_⟩
  · intro i hi
    have h0 : IsZero ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i).obj
        (Q.obj (CochainComplex.mappingCone ζ))) :=
      IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hexζ i hi))
        ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app _)
    have h1 : IsZero ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i).obj
        (Q.obj (CochainComplex.mappingCone φ'))) :=
      IsZero.of_iso h0 ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i).mapIso ε₃)
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (IsZero.of_iso h1
        ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app _).symm)
  · let G' := (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).obj
      ((HomologicalComplex.single A (ComplexShape.up ℤ) (k - 1)).obj G)
    let eX : G'.X (n + 1) ≅ ((HomologicalComplex.single A (ComplexShape.up ℤ) (k - 1)).obj G).X
        (n + 1 + -1) := CochainComplex.shiftFunctorObjXIso _ (-1) (n + 1) (n + 1 + -1) rfl
    refine ⟨G'.X (n + 1), ?_, ?_, ⟨HomologicalComplex.homotopyCofiber.XIsoBiprod θ n (n + 1) rfl⟩⟩
    · by_cases h : n = k - 1
      · right
        exact ⟨eX ≪≫ HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) (k - 1) G _
          (by omega)⟩
      · left
        exact IsZero.of_iso (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (k - 1) G
          _ (by omega)) eX
    · intro h
      exact IsZero.of_iso (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (k - 1) G
        _ (by omega)) eX

/-- Homology of the cones of homotopic maps agree. -/
private lemma cone_homology_iso_of_homotopy {F K : CochainComplex A ℤ} {v w : F ⟶ K}
    (h : Homotopy v w) (i : ℤ) :
    Nonempty ((CochainComplex.mappingCone v).homology i ≅
      (CochainComplex.mappingCone w).homology i) := by
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have hv := HomotopyCategory.mappingCone_triangleh_distinguished v
  have hw := HomotopyCategory.mappingCone_triangleh_distinguished w
  have hvw : Q.map v = Q.map w := HomotopyCategory.eq_of_homotopy v w h
  obtain ⟨e, -, -⟩ := exists_iso_of_arrow_iso _ _ hv hw
    (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      exact ((Category.comp_id _).trans (hvw.trans (Category.id_comp _).symm)).symm))
  refine ⟨?_⟩
  exact ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app _).symm ≪≫
    (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) i).mapIso (Triangle.π₃.mapIso e) ≪≫
    ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app _)

/-- Homology of the cone of `u` and of `u ≫ s` agree if `s` is a quasi-isomorphism. -/
private lemma cone_homology_iso_of_qiso {F L M : CochainComplex A ℤ} (u : F ⟶ L) (s : L ⟶ M)
    [QuasiIso s] (i : ℤ) :
    Nonempty ((CochainComplex.mappingCone u).homology i ≅
      (CochainComplex.mappingCone (u ≫ s)).homology i) := by
  let Q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  have h1 := HomotopyCategory.mappingCone_triangleh_distinguished u
  have h3 := HomotopyCategory.mappingCone_triangleh_distinguished (u ≫ s)
  have hW : (HomotopyCategory.subcategoryAcyclic A).trW (Q.map s) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2
      ((HomologicalComplex.mem_quasiIso_iff s).2 inferInstance)
  obtain ⟨c, hc, -, -⟩ :=
    MorphismProperty.IsCompatibleWithTriangulation.compatible_with_triangulation
    (W := (HomotopyCategory.subcategoryAcyclic A).trW)
    (CochainComplex.mappingCone.triangleh u) (CochainComplex.mappingCone.triangleh (u ≫ s)) h1 h3
    (𝟙 _) (Q.map s) (MorphismProperty.id_mem _ _) hW
    (show (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u ≫
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s =
      𝟙 _ ≫ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (u ≫ s) from by
      rw [Category.id_comp, ← CategoryTheory.Functor.map_comp])
  have hc' := ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0
    ).mem_homologicalKernel_trW_iff c).1 hc i
  refine ⟨?_⟩
  exact ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app _).symm ≪≫
    (@asIso _ _ _ _ _ hc') ≪≫
    ((HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i).app _)

/-- Homology of the cone of `v` agrees with that of `u ≫ g` if `u ≫ f ≃ v` and `f`, `g` are
quasi-isomorphisms out of the same complex. -/
lemma cone_homology_iso_four {F L K P : CochainComplex A ℤ} (u : F ⟶ L) (v : F ⟶ K)
    (f : L ⟶ K) (g : L ⟶ P) [QuasiIso f] [QuasiIso g] (hv : Homotopy (u ≫ f) v) (i : ℤ) :
    Nonempty ((CochainComplex.mappingCone v).homology i ≅
      (CochainComplex.mappingCone (u ≫ g)).homology i) := by
  obtain ⟨e₁⟩ := cone_homology_iso_of_homotopy hv.symm i
  obtain ⟨e₂⟩ := cone_homology_iso_of_qiso u f i
  obtain ⟨e₃⟩ := cone_homology_iso_of_qiso u g i
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ e₃⟩


end StepLemmas

end Cohesive
