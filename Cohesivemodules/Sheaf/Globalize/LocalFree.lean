import Cohesivemodules.Sheaf.Globalize.LocalFreeBasic

set_option linter.style.header false

/-!
# S10 (part 2): local images, local lifting through free modules, local summands (part 2 of 2)

Split from `Sheaf/Globalize/LocalFree.lean` for size;
continues `Sheaf/Globalize/LocalFreeBasic.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace Limits
section Site
variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}}

/-- `N` is, over `Y`, a retract of a finite free module. -/
def FS (N : Mod R) (Y : C) : Prop :=
  ∃ (m : ℕ) (i : N.over Y ⟶ (Fr R m).over Y) (p : (Fr R m).over Y ⟶ N.over Y),
    i ≫ p = 𝟙 _

/-- `FS` is stable under restriction. -/
lemma FS.restrict {N : Mod R} {Y : C} (hN : FS N Y) {V : C} (h : V ⟶ Y) : FS N V := by
  obtain ⟨m, i, p, hip⟩ := hN
  exact ⟨m, homRestr h i, homRestr h p, by rw [← homRestr_mor_comp, hip, homRestr_mor_id]⟩

/-- A global summand of a free module is one over every object. -/
lemma FS.of_global {N : Mod R} (hN : IsFinFreeSummand N) (Y : C) : FS N Y := by
  obtain ⟨m, i, p, hip⟩ := hN
  exact ⟨m, i.over Y, p.over Y, by
    rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]⟩

/-- Retracts of `FS` objects are `FS`. -/
private lemma FS.of_retract {K A : Mod R} {Y : C} (ι : K.over Y ⟶ A.over Y)
    (r : A.over Y ⟶ K.over Y)
    (hι : ι ≫ r = 𝟙 _) (hA : FS A Y) : FS K Y := by
  obtain ⟨m, i, p, hip⟩ := hA
  exact ⟨m, ι ≫ i, p ≫ r, by
    rw [Category.assoc, ← Category.assoc i, hip, Category.id_comp, hι]⟩

/-- `FS` gives `IsFinFreeSummand` of the restriction. -/
lemma FS.isFinFreeSummand {N : Mod R} {Y : C} (hN : FS N Y) :
    IsFinFreeSummand (N.over Y) := by
  obtain ⟨m, i, p, hip⟩ := hN
  exact ⟨m, i ≫ (frIso Y m).hom, (frIso Y m).inv ≫ p, by
    rw [Category.assoc, ← Category.assoc (frIso Y m).hom, Iso.hom_inv_id, Category.id_comp,
      hip]⟩

/-- `IsFinFreeSummand` of the restriction gives `FS`. -/
private lemma FS.of_isFinFreeSummand {N : Mod R} {Y : C} (hN : IsFinFreeSummand (N.over Y)) :
    FS N Y := by
  obtain ⟨m, i, p, hip⟩ := hN
  exact ⟨m, i ≫ (frIso Y m).inv, (frIso Y m).hom ≫ p, by
    rw [Category.assoc, ← Category.assoc (frIso Y m).inv, Iso.inv_hom_id, Category.id_comp,
      hip]⟩

/-- The sieve of arrows `V ⟶ X` over which `N` is a retract of a finite free module. -/
private def fsSieve (N : Mod R) (X : C) : Sieve X where
  arrows V _ := FS N V
  downward_closed := fun hf g => hf.restrict g

/-- Local splitting of an epimorphism onto an `FS` object. -/
lemma split_FS {M N : Mod R} (π : M ⟶ N) [Epi π] (Y : C) (hN : FS N Y) :
    ∃ S ∈ J Y, ∀ ⦃V : C⦄ (h : V ⟶ Y), S h →
      ∃ σ : N.over V ⟶ M.over V, σ ≫ π.over V = 𝟙 _ := by
  obtain ⟨m, i, p, hip⟩ := hN
  obtain ⟨S, hS, hq⟩ := lift_free π Y m p
  refine ⟨S, hS, fun V h hh => ?_⟩
  obtain ⟨q, hq⟩ := hq h hh
  exact ⟨homRestr h i ≫ q, by
    rw [Category.assoc, hq, ← homRestr_mor_comp, hip, homRestr_mor_id]⟩

/-- Direct summands of finite free modules are closed under retracts. -/
lemma isFinFreeSummand_of_retract {A B : Mod R} (i : A ⟶ B) (p : B ⟶ A) (h : i ≫ p = 𝟙 A)
    (hB : IsFinFreeSummand B) : IsFinFreeSummand A := by
  obtain ⟨m, i', p', h'⟩ := hB
  exact ⟨m, i ≫ i', p' ≫ p, by
    rw [Category.assoc, ← Category.assoc i', h', Category.id_comp, h]⟩

/-- Finite free modules are closed under binary sums. -/
private def freeBiprodIso (a b : ℕ) :
    SheafOfModules.free (R := R) (Fin a) ⊞ SheafOfModules.free (R := R) (Fin b) ≅
      SheafOfModules.free (R := R) (Fin (a + b)) :=
  biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso (Fin a) (Fin b) ≪≫
    (SheafOfModules.freeFunctor (R := R)).mapIso (Equiv.toIso finSumFinEquiv)

/-- Finite free summands are closed under binary sums. -/
lemma isFinFreeSummand_biprod {A B : Mod R} (hA : IsFinFreeSummand A)
    (hB : IsFinFreeSummand B) : IsFinFreeSummand (A ⊞ B) := by
  obtain ⟨a, iA, pA, hA⟩ := hA
  obtain ⟨b, iB, pB, hB⟩ := hB
  refine ⟨a + b, biprod.map iA iB ≫ (freeBiprodIso a b).hom,
    (freeBiprodIso a b).inv ≫ biprod.map pA pB, ?_⟩
  rw [Category.assoc, ← Category.assoc (freeBiprodIso a b).hom, Iso.hom_inv_id,
    Category.id_comp]
  apply biprod.hom_ext <;> simp [hA, hB]

/-- Restriction to an over-site is a right adjoint (so preserves finite limits). -/
private instance ovR (Y : C) : (SheafOfModules.overFunctor.{0} R Y).IsRightAdjoint :=
  @SheafOfModules.instIsRightAdjointPushforward _ _ _ _ _ _ _ _ _ _ (𝟙 (R.over Y))
    (PresheafOfModules.instIsRightAdjointPushforward (F := Over.forget Y)
      (R := R.obj) (S := (R.over Y).obj) (𝟙 _)) _ _

/-- Local splitting of `A → ker g` for an exact `A → B → B'`: over covering arrows, `A|V` is
the sum of `ker f|V` and `ker g|V`. -/
private lemma local_decomp {A B B' : Mod R} (f : A ⟶ B) (g : B ⟶ B') (hfg : f ≫ g = 0)
    (hex : (ShortComplex.mk f g hfg).Exact) (Y : C) (hZ : FS (kernel g) Y) :
    ∃ S ∈ J Y, ∀ ⦃V : C⦄ (h : V ⟶ Y), S h →
      ∃ (r : A.over V ⟶ (kernel f).over V) (σ : (kernel g).over V ⟶ A.over V),
        (kernel.ι f).over V ≫ r = 𝟙 _ ∧
        r ≫ (kernel.ι f).over V + (kernel.lift g f hfg).over V ≫ σ = 𝟙 _ := by
  have hepi : Epi (kernel.lift g f hfg) :=
    (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk f g hfg)).1 hex
  obtain ⟨S, hS, hσ⟩ := split_FS (kernel.lift g f hfg) Y hZ
  refine ⟨S, hS, fun V h hh => ?_⟩
  obtain ⟨σ, hσ⟩ := hσ h hh
  let F := SheafOfModules.overFunctor.{0} R V
  have hf : f.over V = (kernel.lift g f hfg).over V ≫ (kernel.ι g).over V := by
    rw [← CategoryTheory.Functor.map_comp, kernel.lift_ι]
  have h1 : (𝟙 (A.over V) - (kernel.lift g f hfg).over V ≫ σ) ≫ f.over V = 0 := by
    rw [hf, Preadditive.sub_comp, Category.id_comp, Category.assoc,
      ← Category.assoc σ, hσ, Category.id_comp, sub_self]
  let r : A.over V ⟶ (kernel f).over V :=
    kernel.lift (f.over V) (𝟙 (A.over V) - (kernel.lift g f hfg).over V ≫ σ) h1 ≫
      inv (kernelComparison f F)
  have hr : r ≫ (kernel.ι f).over V = 𝟙 (A.over V) - (kernel.lift g f hfg).over V ≫ σ := by
    have := kernelComparison_comp_ι f F
    change r ≫ F.map (kernel.ι f) = _
    rw [← this]
    simp only [r, Category.assoc, IsIso.inv_hom_id_assoc]
    exact kernel.lift_ι _ _ _
  have hιd : (kernel.ι f) ≫ kernel.lift g f hfg = 0 := by
    rw [← cancel_mono (kernel.ι g), Category.assoc, kernel.lift_ι, kernel.condition, zero_comp]
  refine ⟨r, σ, ?_, by rw [hr, sub_add_cancel]⟩
  have : Mono ((kernel.ι f).over V) := inferInstance
  rw [← cancel_mono ((kernel.ι f).over V), Category.assoc, hr, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    hιd, CategoryTheory.Functor.map_zero, zero_comp, sub_zero]

/-- Zero objects are `FS`. -/
private lemma FS.of_isZero {N : Mod R} (hN : IsZero N) (Y : C) : FS N Y := by
  have hz : IsZero (N.over Y) := Functor.map_isZero _ hN
  exact ⟨0, 0, 0, hz.eq_of_src _ _⟩

/-- Exactness at `i + 1` as exactness of a short complex. -/
private lemma exact_sc {C' : CochainComplex (Mod R) ℤ} (i : ℤ) (hC : C'.ExactAt (i + 1)) :
    (ShortComplex.mk (C'.d i (i + 1)) (C'.d (i + 1) (i + 1 + 1)) (C'.d_comp_d _ _ _)).Exact :=
  (C'.exactAt_iff' i (i + 1) (i + 1 + 1) (by simp) (by simp)).1 hC

/-- Descending step for the cycle sheaves being locally summands of free modules. -/
private lemma fsZ_step {C' : CochainComplex (Mod R) ℤ} (i : ℤ) (hC : C'.ExactAt (i + 1))
    (hi : IsFinFreeSummand (C'.X i)) (X : C)
    (h : fsSieve (kernel (C'.d (i + 1) (i + 1 + 1))) X ∈ J X) :
    fsSieve (kernel (C'.d i (i + 1))) X ∈ J X := by
  refine J.transitive h _ (fun Y f hf => ?_)
  obtain ⟨S, hS, hd⟩ := local_decomp (C'.d i (i + 1)) (C'.d (i + 1) (i + 1 + 1))
    (C'.d_comp_d _ _ _) (exact_sc i hC) Y hf
  refine J.superset_covering (fun V g hg => ?_) hS
  obtain ⟨r, σ, hr, -⟩ := hd g hg
  exact FS.of_retract _ r hr (FS.of_global hi V)

/-- The cycle sheaves above an exact range of a bounded complex are locally `FS`. -/
private lemma fsZ_down {C' : CochainComplex (Mod R) ℤ} (n lo : ℤ) [C'.IsStrictlyLE n]
    (hex : ∀ i, lo ≤ i → C'.ExactAt (i + 1))
    (hfree : ∀ i, lo ≤ i → IsFinFreeSummand (C'.X i))
    (X : C) : ∀ i, lo ≤ i → fsSieve (kernel (C'.d i (i + 1))) X ∈ J X := by
  have key : ∀ k : ℕ, ∀ i, lo ≤ i → n < i + k →
      fsSieve (kernel (C'.d i (i + 1))) X ∈ J X := by
    intro k
    induction k with
    | zero =>
      intro i _ hi
      have hz : IsZero (kernel (C'.d i (i + 1))) :=
        IsZero.of_mono (kernel.ι _) (C'.isZero_of_isStrictlyLE n i (by simpa using hi))
      have : fsSieve (kernel (C'.d i (i + 1))) X = ⊤ := by
        ext V g
        exact ⟨fun _ => trivial, fun _ => FS.of_isZero hz V⟩
      rw [this]
      exact J.top_mem X
    | succ k ih =>
      intro i hlo hi
      exact fsZ_step i (hex i hlo) (hfree i hlo) X
        (ih (i + 1) (by omega) (by push_cast at hi; omega))
  intro i hi
  exact key (n + 1 - i).toNat i hi (by omega)

/-- At the bottom of a bounded acyclic complex, `C^m` is the cycles `Z^{m+1}`. -/
private lemma isIso_bottom {C' : CochainComplex (Mod R) ℤ} (m : ℤ) [C'.IsStrictlyGE m]
    (hC : C'.Acyclic) :
    IsIso (kernel.lift (C'.d (m + 1) (m + 1 + 1)) (C'.d m (m + 1)) (C'.d_comp_d _ _ _)) := by
  have hepi : Epi (kernel.lift (C'.d (m + 1) (m + 1 + 1)) (C'.d m (m + 1))
      (C'.d_comp_d _ _ _)) :=
    (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk (C'.d m (m + 1))
      (C'.d (m + 1) (m + 1 + 1)) (C'.d_comp_d _ _ _))).1 (exact_sc m (hC (m + 1)))
  have hex : (ShortComplex.mk (C'.d (m - 1) m) (C'.d m (m + 1)) (C'.d_comp_d _ _ _)).Exact :=
    (C'.exactAt_iff' (m - 1) m (m + 1) (by simp) (by simp)).1 (hC m)
  have hmono : Mono (C'.d m (m + 1)) :=
    hex.mono_g ((C'.isZero_of_isStrictlyGE m (m - 1) (by omega)).eq_of_src _ _)
  have : Mono (kernel.lift (C'.d (m + 1) (m + 1 + 1)) (C'.d m (m + 1)) (C'.d_comp_d _ _ _)) :=
    mono_of_mono_fac (kernel.lift_ι (C'.d (m + 1) (m + 1 + 1)) (C'.d m (m + 1))
      (C'.d_comp_d _ _ _))
  exact isIso_of_mono_of_epi _

/-- Proof of `isFinFreeSummand_locally_of_acyclic`. -/
theorem isFin_acyc {C' : CochainComplex (Mod R) ℤ} (m n : ℤ)
    [C'.IsStrictlyGE m] [C'.IsStrictlyLE n] (hC : C'.Acyclic)
    (hfree : ∀ i, i ≠ m + 1 → IsFinFreeSummand (C'.X i)) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ IsFinFreeSummand ((C'.X (m + 1)).over Y)) ∈ J X := by
  have hP := fsZ_down (J := J) n (m + 2) (fun i _ => hC (i + 1))
    (fun i hi => hfree i (by omega)) X (m + 1 + 1) (by omega)
  refine J.superset_covering (fun V g hg => Sieve.le_generate _ V g (FS.isFinFreeSummand hg))
    (J.transitive hP (fsSieve (C'.X (m + 1)) X) (fun Y f hf => ?_))
  obtain ⟨S, hS, hd⟩ := local_decomp (C'.d (m + 1) (m + 1 + 1))
    (C'.d (m + 1 + 1) (m + 1 + 1 + 1))
    (C'.d_comp_d _ _ _) (exact_sc (m + 1) (hC _)) Y hf
  refine J.superset_covering (fun V g hg => ?_) hS
  obtain ⟨r, σ, hr, hsum⟩ := hd g hg
  have hiso := isIso_bottom (C' := C') m hC
  have hK : FS (kernel (C'.d (m + 1) (m + 1 + 1))) V := by
    refine FS.of_retract
      ((SheafOfModules.overFunctor.{0} R V).map (inv (kernel.lift (C'.d (m + 1) (m + 1 + 1))
        (C'.d m (m + 1)) (C'.d_comp_d _ _ _)))) ((kernel.lift (C'.d (m + 1) (m + 1 + 1))
        (C'.d m (m + 1)) (C'.d_comp_d _ _ _)).over V) ?_ (FS.of_global (hfree m (by omega)) V)
    rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  have hN : FS (kernel (C'.d (m + 1 + 1) (m + 1 + 1 + 1))) V := hf.restrict g
  have hfs := isFinFreeSummand_biprod hK.isFinFreeSummand hN.isFinFreeSummand
  refine FS.of_isFinFreeSummand (isFinFreeSummand_of_retract
    (biprod.lift r ((kernel.lift (C'.d (m + 1 + 1) (m + 1 + 1 + 1)) (C'.d (m + 1) (m + 1 + 1))
      (C'.d_comp_d _ _ _)).over V))
    (biprod.desc ((kernel.ι (C'.d (m + 1) (m + 1 + 1))).over V) σ) ?_ hfs)
  rw [biprod.lift_desc]
  exact hsum

/-- Restriction to an over-site preserves epimorphisms. -/
private lemma epi_over {M N : Mod R} (f : M ⟶ N) [Epi f] (Y : C) : Epi (f.over Y) := by
  have h1 : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map f.val) :=
    ⟨fun s => imSieve_mem_of_epi f s⟩
  have h2 := Presheaf.isLocallySurjective_whisker (J.over Y) J (Over.forget Y)
    ((PresheafOfModules.toPresheaf R.obj).map f.val)
  have h3 : Epi ((SheafOfModules.toSheaf (R.over Y)).map (f.over Y)) :=
    (by
      have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over Y)).map (f.over Y)) := h2
      infer_instance)
  exact (SheafOfModules.toSheaf (R.over Y)).epi_of_epi_map h3

/-- The cycles `ker d^{k-1}` surject onto `H^{k-1}`. -/
private lemma exists_epi_kernel_homology (P : CochainComplex (Mod R) ℤ) (k : ℤ) :
    ∃ ρ : kernel (P.d (k - 1) (k - 1 + 1)) ⟶ P.homology (k - 1), Epi ρ := by
  let S := P.sc' (k - 1 - 1) (k - 1) (k - 1 + 1)
  refine ⟨S.cyclesIsoKernel.inv ≫ S.homologyπ ≫
    (P.homologyIsoSc' (k - 1 - 1) (k - 1) (k - 1 + 1) (by simp) (by simp)).inv, ?_⟩
  infer_instance

/-- Proof of `homology_finGen_locally`. -/
theorem homology_fg {P : CochainComplex (Mod R) ℤ} (hP : IsStrictlyPerfect P)
    (k : ℤ) (hk : ∀ i, k ≤ i → P.ExactAt i) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ ∃ (m : ℕ)
      (π : SheafOfModules.free (R := R.over Y) (Fin m) ⟶ (P.homology (k - 1)).over Y),
      Epi π) ∈ J X := by
  obtain ⟨⟨a, b, -, hb⟩, hfree⟩ := hP
  have hZ := fsZ_down (J := J) (C' := P) b (k - 1) (fun i hi => hk (i + 1) (by omega))
    (fun i _ => hfree i) X (k - 1) le_rfl
  obtain ⟨ρ, hρ⟩ := exists_epi_kernel_homology P k
  refine J.superset_covering (fun V g hg => Sieve.le_generate _ V g ?_) hZ
  obtain ⟨m, i, p, hip⟩ := hg
  have : Epi p := epi_of_epi_fac hip
  have := epi_over ρ V
  exact ⟨m, (frIso V m).inv ≫ p ≫ ρ.over V, inferInstance⟩

end Site

end Cohesive
