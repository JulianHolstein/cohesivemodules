import Cohesivemodules.Sheaf.ProjectiveBasic

set_option linter.style.header false

/-!
# S4: projective modules over a fine sheaf (part 2 of 2)

Split from `Sheaf/Projective.lean` for size; continues `Sheaf/ProjectiveBasic.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace Limits
variable {X : Type} [TopologicalSpace X]

/-- Auxiliary: the biproduct of `m` copies of `A` in `ModuleCat A` is the product module
`A^m`. -/
private theorem nonempty_biproduct_iso_pi (A : Type) [Ring A] (m : ℕ)
    [HasBiproduct (fun _ : Fin m => ModuleCat.of A A)] :
    Nonempty ((⨁ (fun _ : Fin m => ModuleCat.of A A)) ≅ ModuleCat.of A (Fin m → A)) := by
  refine ⟨{
    hom := biproduct.desc (fun i => ModuleCat.ofHom (LinearMap.single A (fun _ : Fin m => A) i))
    inv := biproduct.lift (fun i => ModuleCat.ofHom
      (LinearMap.proj (R := A) (φ := fun _ : Fin m => A) i))
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩
  · apply biproduct.hom_ext'
    intro j
    apply biproduct.hom_ext
    intro k
    simp only [biproduct.ι_desc_assoc, Category.comp_id, biproduct.ι_π]
    rw [Category.assoc, biproduct.lift_π, ← ModuleCat.ofHom_comp]
    split_ifs with h
    · subst h
      ext
      simp
    · ext
      simp [h]
  · rw [biproduct.lift_desc]
    ext
    simp [Pi.single_apply, Finset.sum_apply]

/-- Auxiliary: `Γ(R^m) ≅ R(X)^m` as `R(X)`-modules (`Γ` is additive, so preserves the finite
biproduct `R^m`). -/
private theorem nonempty_globalSections_free_iso (R : RingSheaf X) (m : ℕ) :
    Nonempty ((globalSections R).obj (SheafOfModules.free (R := R) (Fin m)) ≅
      ModuleCat.of (R.obj.obj (op ⊤)) (Fin m → R.obj.obj (op ⊤))) := by
  have : HasFiniteBiproducts (ModuleCat.{0} (R.obj.obj (op ⊤))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteBiproducts (Mod R) := HasFiniteBiproducts.of_hasFiniteProducts
  obtain ⟨e⟩ := nonempty_biproduct_iso_pi (R.obj.obj (op ⊤)) m
  exact ⟨(globalSections R).mapIso
    (biproduct.isoCoproduct (fun _ : Fin m => SheafOfModules.unit R)).symm
    ≪≫ (globalSections R).mapBiproduct (fun _ : Fin m => SheafOfModules.unit R) ≪≫ e⟩

/-- Auxiliary: `Γ p ∘ Γ i = id` for a retraction `i ≫ p = 𝟙`. -/
private theorem gs_retract {R : RingSheaf X} {M : Mod R} {m : ℕ}
    (i : M ⟶ SheafOfModules.free (Fin m))
    (p : SheafOfModules.free (Fin m) ⟶ M) (hip : i ≫ p = 𝟙 M) (y : (globalSections R).obj M) :
    ((globalSections R).map p).hom (((globalSections R).map i).hom y) = y := by
  have hc : (globalSections R).map i ≫ (globalSections R).map p = 𝟙 _ := by
    rw [← (globalSections R).map_comp, hip, (globalSections R).map_id]
  exact congrArg (fun k => k.hom y) hc

/-- **S4.c (1).** Global sections of a direct summand of a finite free module are a finitely
generated `R(X)`-module. -/
theorem finite_globalSections {R : RingSheaf X} {M : Mod R} (hM : IsFinFreeSummand M) :
    Module.Finite (R.obj.obj (op ⊤)) ((globalSections R).obj M) := by
  obtain ⟨m, i, p, hip⟩ := hM
  obtain ⟨e⟩ := nonempty_globalSections_free_iso R m
  have h1 : Module.Finite (R.obj.obj (op ⊤))
      ((globalSections R).obj (SheafOfModules.free (Fin m))) :=
    Module.Finite.equiv (Iso.toLinearEquiv e).symm
  exact Module.Finite.of_surjective ((globalSections R).map p).hom
    (fun y => ⟨((globalSections R).map i).hom y, gs_retract i p hip y⟩)

/-- **S4.c (2).** Global sections of a direct summand of a finite free module are a projective
`R(X)`-module. -/
theorem projective_globalSections {R : RingSheaf X} {M : Mod R} (hM : IsFinFreeSummand M) :
    Module.Projective (R.obj.obj (op ⊤)) ((globalSections R).obj M) := by
  obtain ⟨m, i, p, hip⟩ := hM
  obtain ⟨e⟩ := nonempty_globalSections_free_iso R m
  have h1 : Module.Projective (R.obj.obj (op ⊤))
      ((globalSections R).obj (SheafOfModules.free (Fin m))) :=
    Module.Projective.of_equiv (Iso.toLinearEquiv e).symm
  exact Module.Projective.of_split ((globalSections R).map i).hom
    ((globalSections R).map p).hom (LinearMap.ext (gs_retract i p hip))

/-- Auxiliary: a functor preserving a coproduct is bijective on `Hom(∐ Mᵢ, N)` if it is
bijective on each `Hom(Mᵢ, N)`. -/
private theorem bij_sigma {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {ι : Type}
    (M : ι → C) [HasCoproduct M] [PreservesColimit (Discrete.functor M) F]
    (h : ∀ i (N : C), Function.Bijective (fun f : M i ⟶ N => F.map f)) (N : C) :
    Function.Bijective (fun f : ∐ M ⟶ N => F.map f) := by
  constructor
  · intro f g hfg
    apply Sigma.hom_ext
    intro i
    apply (h i N).1
    simp only [Functor.map_comp, hfg]
  · intro k
    have := fun i => (h i N).2 (F.map (Sigma.ι M i) ≫ k)
    choose g hg using this
    refine ⟨Sigma.desc g, ?_⟩
    apply (isColimitOfPreserves F (coproductIsCoproduct M)).hom_ext
    intro j
    simp only [Functor.mapCocone_ι_app]
    rw [← F.map_comp]
    show F.map (Sigma.ι M j.as ≫ Sigma.desc g) = F.map (Sigma.ι M j.as) ≫ k
    rw [Sigma.ι_comp_desc]
    exact hg j.as

/-- Auxiliary: bijectivity on `Hom(-, N)` passes to retracts. -/
private theorem bij_retract {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {M P : C}
    (i : M ⟶ P) (p : P ⟶ M) (hip : i ≫ p = 𝟙 M)
    (h : ∀ N : C, Function.Bijective (fun f : P ⟶ N => F.map f)) (N : C) :
    Function.Bijective (fun f : M ⟶ N => F.map f) := by
  constructor
  · intro f g hfg
    have := (h N).1 (a₁ := p ≫ f) (a₂ := p ≫ g) (by simp only [Functor.map_comp, hfg])
    simpa [← Category.assoc, hip] using congrArg (i ≫ ·) this
  · intro k
    obtain ⟨g, hg⟩ := (h N).2 (F.map p ≫ k)
    refine ⟨i ≫ g, ?_⟩
    simp only [Functor.map_comp] at hg ⊢
    rw [hg, ← Category.assoc, ← F.map_comp, hip, F.map_id, Category.id_comp]

/-- Auxiliary: `Γ` is bijective on `Hom(R, N)`, since both sides are `Γ(N)`. -/
private theorem bij_unit (R : RingSheaf X) (N : Mod R) :
    Function.Bijective (fun f : SheafOfModules.unit R ⟶ N => (globalSections R).map f) := by
  constructor
  · intro f g hfg
    apply N.unitHomEquiv.injective
    apply sections_eq_of_top
    have := congrArg (fun k => k.hom ((1 : R.obj.obj (op ⊤)) :
      (globalSections R).obj (SheafOfModules.unit R))) hfg
    exact this
  · intro h
    let s0 : N.val.obj (op ⊤) := h.hom ((1 : R.obj.obj (op ⊤)) :
      (globalSections R).obj (SheafOfModules.unit R))
    let x : N.sections := PresheafOfModules.sectionsMk
      (fun U => N.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s0) (by
        intro U V g
        rw [← PresheafOfModules.map_comp_apply]
        rw [show (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ g = (homOfLE (le_top : V.unop ≤ ⊤)).op from
          Subsingleton.elim _ _])
    refine ⟨N.unitHomEquiv.symm x, ?_⟩
    ext
    show (N.unitHomEquiv.symm x).val.app (op ⊤) (1 : R.obj.obj (op ⊤)) = _
    have e : (N.unitHomEquiv (N.unitHomEquiv.symm x)).val (op ⊤) = x.val (op ⊤) := by
      rw [Equiv.apply_symm_apply]
    refine Eq.trans e ?_
    show ConcreteCategory.hom (N.val.map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op) s0 = s0
    rw [show (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _]
    simp only [PresheafOfModules.map_id]
    rfl

/-- Auxiliary: `Γ` is bijective on `Hom(Rᵐ, N)`. -/
private theorem bij_free (R : RingSheaf X) (m : ℕ) (N : Mod R) :
    Function.Bijective
      (fun f : SheafOfModules.free (R := R) (Fin m) ⟶ N => (globalSections R).map f) :=
  bij_sigma (globalSections R) (fun _ : Fin m => SheafOfModules.unit R)
    (fun _ N => bij_unit R N) N

/-- **S4.c (3). Hom property.** For `M` a direct summand of a finite free module and any
`R`-module `N`, `Γ : Hom_R(M, N) → Hom_{R(X)}(Γ M, Γ N)` is bijective. For `M = Rᵐ` both sides
are `Γ(N)ᵐ`. [A, remark after Def 7.2.5, proof of Lemma 7.2.7] -/
theorem bijective_globalSections_map {R : RingSheaf X} {M : Mod R} (hM : IsFinFreeSummand M)
    (N : Mod R) : Function.Bijective (fun f : M ⟶ N ↦ (globalSections R).map f) := by
  obtain ⟨m, i, p, hip⟩ := hM
  exact bij_retract (globalSections R) i p hip (bij_free R m) N

/-- Auxiliary: idempotents split in a preadditive category with kernels. -/
private theorem split_idem {C : Type*} [Category C] [Preadditive C] [HasKernels C] {F : C}
    (E : F ⟶ F) (hE : E ≫ E = E) :
    ∃ (K : C) (i : K ⟶ F) (e : F ⟶ K), i ≫ e = 𝟙 K ∧ e ≫ i = E := by
  have h0 : E ≫ (𝟙 F - E) = 0 := by
    rw [Preadditive.comp_sub, Category.comp_id, hE, sub_self]
  refine ⟨kernel (𝟙 F - E), kernel.ι (𝟙 F - E), kernel.lift (𝟙 F - E) E h0, ?_, ?_⟩
  · have hi : kernel.ι (𝟙 F - E) ≫ E = kernel.ι (𝟙 F - E) := by
      have := kernel.condition (𝟙 F - E)
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
      exact this.symm
    rw [← cancel_mono (kernel.ι (𝟙 F - E)), Category.assoc, kernel.lift_ι, hi, Category.id_comp]
  · exact kernel.lift_ι _ _ _

/-- Auxiliary: a f.g. projective `R(X)`-module `P` is a retract of `Γ(Rᵐ)` for some `m`
(`σ ≫ π = 𝟙`). -/
private theorem exists_retract_globalSections_free {R : RingSheaf X}
    (P : ModuleCat.{0} (R.obj.obj (op ⊤)))
    [Module.Finite (R.obj.obj (op ⊤)) P] [Module.Projective (R.obj.obj (op ⊤)) P] :
    ∃ (m : ℕ) (π : (globalSections R).obj (SheafOfModules.free (R := R) (Fin m)) ⟶ P)
      (σ : P ⟶ (globalSections R).obj (SheafOfModules.free (R := R) (Fin m))), σ ≫ π = 𝟙 P := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (R.obj.obj (op ⊤)) P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  obtain ⟨e⟩ := nonempty_globalSections_free_iso R m
  refine ⟨m, e.hom ≫ ModuleCat.ofHom f, ModuleCat.ofHom s ≫ e.inv, ?_⟩
  rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp,
    ← ModuleCat.ofHom_comp, hs]
  rfl

/-- **S4.c (4). Essential surjectivity.** Every finitely generated projective `R(X)`-module is
isomorphic to `Γ M` for a direct summand `M` of a finite free `R`-module (the image of the
idempotent endomorphism of `Rᵐ` given by a presentation `P ⊕ P' ≅ R(X)ᵐ`; this is `P̃`). -/
theorem exists_globalSections_iso {R : RingSheaf X} (P : ModuleCat.{0} (R.obj.obj (op ⊤)))
    [Module.Finite (R.obj.obj (op ⊤)) P] [Module.Projective (R.obj.obj (op ⊤)) P] :
    ∃ M : Mod R, IsFinFreeSummand M ∧ Nonempty ((globalSections R).obj M ≅ P) := by
  obtain ⟨m, π, σ, hσπ⟩ := exists_retract_globalSections_free (R := R) P
  obtain ⟨E, hE⟩ := (bij_free R m (SheafOfModules.free (Fin m))).2 (π ≫ σ)
  have hEE : E ≫ E = E := by
    apply (bij_free R m (SheafOfModules.free (Fin m))).1
    show (globalSections R).map (E ≫ E) = (globalSections R).map E
    rw [(globalSections R).map_comp]
    have hE' : (globalSections R).map E = π ≫ σ := hE
    rw [hE', Category.assoc, ← Category.assoc σ, hσπ, Category.id_comp]
  obtain ⟨K, i, e, hie, hei⟩ := split_idem E hEE
  refine ⟨K, ⟨m, i, e, hie⟩, ⟨⟨(globalSections R).map i ≫ π, σ ≫ (globalSections R).map e, ?_, ?_⟩⟩⟩
  · have hE' : (globalSections R).map E = π ≫ σ := hE
    have h1 : ((globalSections R).map i ≫ π) ≫ σ ≫ (globalSections R).map e =
        (globalSections R).map (i ≫ (e ≫ i) ≫ e) := by
      rw [hei, (globalSections R).map_comp, (globalSections R).map_comp, hE']
      simp only [Category.assoc]
    have h2 : i ≫ (e ≫ i) ≫ e = 𝟙 K := by
      rw [← Category.assoc, ← Category.assoc, hie, Category.id_comp, hie]
    rw [h1, h2, (globalSections R).map_id]
  · have hE' : (globalSections R).map E = π ≫ σ := hE
    have h1 : (σ ≫ (globalSections R).map e) ≫ (globalSections R).map i ≫ π =
        σ ≫ (globalSections R).map (e ≫ i) ≫ π := by
      rw [(globalSections R).map_comp]
      simp only [Category.assoc]
    rw [h1, hei, hE']
    simp only [Category.assoc]
    rw [← Category.assoc σ π, hσπ, Category.id_comp]

end Cohesive
