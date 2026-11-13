import Cohesivemodules.Sheaf.Basic
import Cohesivemodules.Sheaf.Restriction
import Cohesivemodules.Sheaf.PerfectDef
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

set_option linter.style.header false

/-!
# C2 auxiliary: `S4.c` on a site with a terminal object

The parts of S4.c (`Sheaf/Projective.lean`) that need neither fineness nor compactness, restated
for a sheaf of rings `R` on any small site with a terminal object `T` (in particular the over-site
`Over U`, with `T = Over.mk (𝟙 U)`): the Hom bijection `Γ : Hom(M, N) ≃ Hom(Γ M, Γ N)` for a
direct summand `M` of a finite free module, and essential surjectivity onto finitely generated
projective modules. `Γ` is evaluation at `T`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}} {T : C}

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- Auxiliary: a section of a sheaf of modules is determined by its value at a terminal
object. -/
private theorem sections_eq_of_terminal (hT : IsTerminal T) {N : Mod R} (s t : N.sections)
    (h : s.1 (op T) = t.1 (op T)) : s = t := by
  apply PresheafOfModules.sections_ext
  intro U
  have h1 := PresheafOfModules.sections_property s (X := op T) (Y := U) (hT.from U.unop).op
  have h2 := PresheafOfModules.sections_property t (X := op T) (Y := U) (hT.from U.unop).op
  rw [← h1, ← h2, h]

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- Auxiliary: every element of `N(T)` is the value at `T` of a section of `N`. -/
private theorem exists_section_of_terminal (hT : IsTerminal T) {N : Mod R}
    (s0 : N.val.obj (op T)) : ∃ x : N.sections, x.1 (op T) = s0 := by
  refine ⟨PresheafOfModules.sectionsMk
    (fun U => N.val.map (hT.from U.unop).op s0) (by
      intro U V g
      rw [← PresheafOfModules.map_comp_apply]
      rw [show (hT.from U.unop).op ≫ g = (hT.from V.unop).op from
        Quiver.Hom.unop_inj (hT.hom_ext _ _)]), ?_⟩
  show ConcreteCategory.hom (N.val.map (hT.from T).op) s0 = s0
  rw [show (hT.from T).op = 𝟙 (op T) from Quiver.Hom.unop_inj (hT.hom_ext _ _)]
  simp only [PresheafOfModules.map_id]
  rfl

/-- Auxiliary: a functor preserving a coproduct is bijective on `Hom(∐ Mᵢ, N)` if it is
bijective on each `Hom(Mᵢ, N)`. -/
private theorem bij_sigma' {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {ι : Type}
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
private theorem bij_retract' {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {M P : C}
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

/-- Evaluation at the terminal object `T`, as `Γ`. -/
abbrev gammaT (R : Sheaf J RingCat.{0}) (T : C) : Mod R ⥤ ModuleCat.{0} (R.obj.obj (op T)) :=
  SheafOfModules.evaluation.{0} R (op T)

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- Auxiliary: `Γ` is bijective on `Hom(R, N)`, since both sides are `Γ(N)`. -/
private theorem bij_unit' (hT : IsTerminal T) (N : Mod R) :
    Function.Bijective (fun f : SheafOfModules.unit R ⟶ N => (gammaT R T).map f) := by
  constructor
  · intro f g hfg
    apply N.unitHomEquiv.injective
    apply sections_eq_of_terminal hT
    have := congrArg (fun k => k.hom ((1 : R.obj.obj (op T)) :
      (gammaT R T).obj (SheafOfModules.unit R))) hfg
    exact this
  · intro h
    let s0 : N.val.obj (op T) := h.hom ((1 : R.obj.obj (op T)) :
      (gammaT R T).obj (SheafOfModules.unit R))
    obtain ⟨x, hx⟩ := exists_section_of_terminal hT (N := N) s0
    refine ⟨N.unitHomEquiv.symm x, ?_⟩
    ext
    show (N.unitHomEquiv.symm x).val.app (op T) (1 : R.obj.obj (op T)) = _
    have e : (N.unitHomEquiv (N.unitHomEquiv.symm x)).val (op T) = x.val (op T) := by
      rw [Equiv.apply_symm_apply]
    exact e.trans hx

/-- Auxiliary: `Γ` is bijective on `Hom(Rᵐ, N)`. -/
private theorem bij_free' (hT : IsTerminal T) (m : ℕ) (N : Mod R) :
    Function.Bijective
      (fun f : SheafOfModules.free (R := R) (Fin m) ⟶ N => (gammaT R T).map f) :=
  bij_sigma' (gammaT R T) (fun _ : Fin m => SheafOfModules.unit R)
    (fun _ N => bij_unit' hT N) N

/-- **S4.c (3), any site with a terminal object.** For `M` a direct summand of a finite free
module and any `N`, `Γ : Hom_R(M, N) → Hom_{R(T)}(Γ M, Γ N)` is bijective. -/
theorem bijective_gammaT_map (hT : IsTerminal T) {M : Mod R} (hM : IsFinFreeSummand M)
    (N : Mod R) : Function.Bijective (fun f : M ⟶ N ↦ (gammaT R T).map f) := by
  obtain ⟨m, i, p, hip⟩ := hM
  exact bij_retract' (gammaT R T) i p hip (bij_free' hT m) N

/-- Auxiliary: the biproduct of `m` copies of `A` in `ModuleCat A` is the product module
`A^m`. -/
private theorem nonempty_biproduct_iso_pi' (A : Type) [Ring A] (m : ℕ)
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

/-- Auxiliary: `Γ(R^m) ≅ R(T)^m` as `R(T)`-modules. -/
private theorem nonempty_gammaT_free_iso (R : Sheaf J RingCat.{0}) (T : C) (m : ℕ) :
    Nonempty ((gammaT R T).obj (SheafOfModules.free (R := R) (Fin m)) ≅
      ModuleCat.of (R.obj.obj (op T)) (Fin m → R.obj.obj (op T))) := by
  have : HasFiniteBiproducts (ModuleCat.{0} (R.obj.obj (op T))) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteBiproducts (Mod R) := HasFiniteBiproducts.of_hasFiniteProducts
  obtain ⟨e⟩ := nonempty_biproduct_iso_pi' (R.obj.obj (op T)) m
  exact ⟨(gammaT R T).mapIso
    (biproduct.isoCoproduct (fun _ : Fin m => SheafOfModules.unit R)).symm
    ≪≫ (gammaT R T).mapBiproduct (fun _ : Fin m => SheafOfModules.unit R) ≪≫ e⟩

/-- Auxiliary: idempotents split in a preadditive category with kernels. -/
private theorem split_idem' {C : Type*} [Category C] [Preadditive C] [HasKernels C] {F : C}
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

/-- Auxiliary: a f.g. projective `R(T)`-module `P` is a retract of `Γ(Rᵐ)` for some `m`. -/
private theorem exists_retract_gammaT_free (R : Sheaf J RingCat.{0}) (T : C)
    (P : ModuleCat.{0} (R.obj.obj (op T)))
    [Module.Finite (R.obj.obj (op T)) P] [Module.Projective (R.obj.obj (op T)) P] :
    ∃ (m : ℕ) (π : (gammaT R T).obj (SheafOfModules.free (R := R) (Fin m)) ⟶ P)
      (σ : P ⟶ (gammaT R T).obj (SheafOfModules.free (R := R) (Fin m))), σ ≫ π = 𝟙 P := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (R.obj.obj (op T)) P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  obtain ⟨e⟩ := nonempty_gammaT_free_iso R T m
  refine ⟨m, e.hom ≫ ModuleCat.ofHom f, ModuleCat.ofHom s ≫ e.inv, ?_⟩
  rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp,
    ← ModuleCat.ofHom_comp, hs]
  rfl

/-- **S4.c (4), any site with a terminal object.** Every finitely generated projective
`R(T)`-module is isomorphic to `Γ M` for a direct summand `M` of a finite free module. -/
theorem exists_gammaT_iso (hT : IsTerminal T) (P : ModuleCat.{0} (R.obj.obj (op T)))
    [Module.Finite (R.obj.obj (op T)) P] [Module.Projective (R.obj.obj (op T)) P] :
    ∃ M : Mod R, IsFinFreeSummand M ∧ Nonempty ((gammaT R T).obj M ≅ P) := by
  obtain ⟨m, π, σ, hσπ⟩ := exists_retract_gammaT_free R T P
  obtain ⟨E, hE⟩ := (bij_free' hT m (SheafOfModules.free (Fin m))).2 (π ≫ σ)
  have hEE : E ≫ E = E := by
    apply (bij_free' hT m (SheafOfModules.free (Fin m))).1
    show (gammaT R T).map (E ≫ E) = (gammaT R T).map E
    rw [(gammaT R T).map_comp]
    have hE' : (gammaT R T).map E = π ≫ σ := hE
    rw [hE', Category.assoc, ← Category.assoc σ, hσπ, Category.id_comp]
  obtain ⟨K, i, e, hie, hei⟩ := split_idem' E hEE
  refine ⟨K, ⟨m, i, e, hie⟩, ⟨⟨(gammaT R T).map i ≫ π, σ ≫ (gammaT R T).map e, ?_, ?_⟩⟩⟩
  · have hE' : (gammaT R T).map E = π ≫ σ := hE
    have h1 : ((gammaT R T).map i ≫ π) ≫ σ ≫ (gammaT R T).map e =
        (gammaT R T).map (i ≫ (e ≫ i) ≫ e) := by
      rw [hei, (gammaT R T).map_comp, (gammaT R T).map_comp, hE']
      simp only [Category.assoc]
    have h2 : i ≫ (e ≫ i) ≫ e = 𝟙 K := by
      rw [← Category.assoc, ← Category.assoc, hie, Category.id_comp, hie]
    rw [h1, h2, (gammaT R T).map_id]
  · have hE' : (gammaT R T).map E = π ≫ σ := hE
    have h1 : (σ ≫ (gammaT R T).map e) ≫ (gammaT R T).map i ≫ π =
        σ ≫ (gammaT R T).map (e ≫ i) ≫ π := by
      rw [(gammaT R T).map_comp]
      simp only [Category.assoc]
    rw [h1, hei, hE']
    simp only [Category.assoc]
    rw [← Category.assoc σ π, hσπ, Category.id_comp]

/-- A direct summand of a finite free module whose `Γ` is a zero module is zero. -/
theorem isZero_of_gammaT_isZero (hT : IsTerminal T) {M : Mod R} (hM : IsFinFreeSummand M)
    (h : IsZero ((gammaT R T).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply (bijective_gammaT_map hT hM M).1
  simp only [Functor.map_zero]
  exact h.eq_of_src _ _

/-- **S4.c (5), any site with a terminal object.** A complex `W` of finitely generated projective
`R(T)`-modules, zero outside `[a, b]`, lifts (through `Γ`, uniquely up to iso) to a strictly
perfect complex `L`: the differentials lift by the Hom bijection. -/
theorem exists_lift_complex (hT : IsTerminal T)
    (W : CochainComplex (ModuleCat.{0} (R.obj.obj (op T))) ℤ)
    (hfin : ∀ n, Module.Finite (R.obj.obj (op T)) (W.X n))
    (hproj : ∀ n, Module.Projective (R.obj.obj (op T)) (W.X n)) (a b : ℤ)
    (hab : ∀ p, (p < a ∨ b < p) → Subsingleton (W.X p)) :
    ∃ L : CochainComplex (Mod R) ℤ, IsStrictlyPerfect L ∧
      Nonempty (((gammaT R T).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ W) := by
  have key : ∀ n, ∃ M : Mod R, IsFinFreeSummand M ∧ Nonempty ((gammaT R T).obj M ≅ W.X n) :=
    fun n => exists_gammaT_iso hT (W.X n)
  choose M hM e using key
  let e' : ∀ n, (gammaT R T).obj (M n) ≅ W.X n := fun n => (e n).some
  have hd : ∀ n, ∃ f : M n ⟶ M (n + 1), (gammaT R T).map f =
      (e' n).hom ≫ W.d n (n + 1) ≫ (e' (n + 1)).inv := fun n =>
    (bijective_gammaT_map hT (hM n) (M (n + 1))).2 _
  choose d hd using hd
  have hdd : ∀ n, d n ≫ d (n + 1) = 0 := by
    intro n
    apply (bijective_gammaT_map hT (hM n) (M (n + 1 + 1))).1
    simp only [Functor.map_comp, hd, Functor.map_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, HomologicalComplex.d_comp_d_assoc,
      zero_comp, comp_zero]
  let L : CochainComplex (Mod R) ℤ := CochainComplex.of M d hdd
  have hz : ∀ i, (i < a ∨ b < i) → IsZero (L.X i) := by
    intro i hi
    refine isZero_of_gammaT_isZero hT (hM i) ?_
    have := hab i hi
    exact (e' i).isZero_iff.2 (ModuleCat.isZero_of_subsingleton _)
  have : L.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff L a).2
    (fun i hi => hz i (Or.inl hi))
  have : L.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff L b).2
    (fun i hi => hz i (Or.inr hi))
  refine ⟨L, ⟨⟨a, b, inferInstance, inferInstance⟩, fun n => hM n⟩, ⟨?_⟩⟩
  · refine HomologicalComplex.Hom.isoOfComponents (fun n => e' n) ?_
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have h1 : (((gammaT R T).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).d i (i + 1) =
        (gammaT R T).map (d i) := by
      change (gammaT R T).map (L.d i (i + 1)) = _
      exact congrArg _ (CochainComplex.of_d M d i)
    rw [h1, hd]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **S4.c (6), any site with a terminal object.** A chain map `Γ L → Γ N` out of the global
sections of a complex of finite free summands lifts (uniquely) to a chain map `L → N`. -/
theorem exists_lift_hom (hT : IsTerminal T) {L N : CochainComplex (Mod R) ℤ}
    (hL : ∀ n, IsFinFreeSummand (L.X n))
    (φ : ((gammaT R T).mapHomologicalComplex (ComplexShape.up ℤ)).obj L ⟶
      ((gammaT R T).mapHomologicalComplex (ComplexShape.up ℤ)).obj N) :
    ∃ u : L ⟶ N, ((gammaT R T).mapHomologicalComplex (ComplexShape.up ℤ)).map u = φ := by
  have key : ∀ n, ∃ f : L.X n ⟶ N.X n, (gammaT R T).map f = φ.f n := fun n =>
    (bijective_gammaT_map hT (hL n) (N.X n)).2 _
  choose f hf using key
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j hij
    apply (bijective_gammaT_map hT (hL i) (N.X j)).1
    simp only [Functor.map_comp, hf]
    exact φ.comm i j
  · refine HomologicalComplex.hom_ext _ _ fun n => ?_
    exact hf n

end Site

end Cohesive
