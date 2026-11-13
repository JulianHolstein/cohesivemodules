import Cohesivemodules.Sheaf.Fine
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

set_option linter.style.header false

/-!
# S3: acyclic complexes of modules over a fine sheaf

Blueprint item S3 (§3): for `R` fine on compact `X`, `Γ(X, -)` maps acyclic complexes of
`R`-modules to acyclic complexes, hence quasi-isomorphisms to quasi-isomorphisms. Proof from S2
by splitting into cycles; no sheaf cohomology. Replaces [A, Lemma 7.2.8] in all uses.
Split of blueprint §7's `Fine.lean` (size only).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

variable {X : Type} [TopologicalSpace X]

/-! ## S3 Acyclic complexes -/

/-- `Γ` maps exact short complexes of `R`-modules to exact ones, for `R` fine on compact `X`. -/
private lemma exact_map_globalSections [CompactSpace X] {R : RingSheaf X} (hR : IsFine R)
    (S : ShortComplex (Mod R)) (hS : S.Exact) : (S.map (globalSections R)).Exact := by
  have h1 : Epi S.toCycles := hS.epi_toCycles
  have h2 : Epi ((globalSections R).map S.toCycles) :=
    (ModuleCat.epi_iff_surjective _).2 (surjective_globalSections_of_epi hR _)
  rw [ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  let F := globalSections R
  have hlim := KernelFork.mapIsLimit _ S.cyclesIsKernel F
  let k : ModuleCat.of _ (R.obj.obj (op ⊤)) ⟶ F.obj S.X₂ :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x₂)
  have hk : k ≫ F.map S.g = 0 := by
    ext
    have : (F.map S.g).hom ((1 : R.obj.obj (op ⊤)) • x₂) = 0 := by
      rw [one_smul]
      exact hx₂
    exact this
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hlim k hk
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).1 h2 (l (1 : R.obj.obj (op ⊤)))
  refine ⟨y, ?_⟩
  have h4 : F.map S.f = F.map S.toCycles ≫ F.map S.iCycles := by
    rw [← F.map_comp, ShortComplex.toCycles_i]
  have h5 := congrArg (fun m => m.hom (1 : R.obj.obj (op ⊤))) hl
  have h6 : (F.map S.f).hom y = (F.map S.iCycles).hom ((F.map S.toCycles).hom y) := by
    rw [h4]
    rfl
  have h7 : (F.map S.iCycles).hom (l.hom 1) = (1 : R.obj.obj (op ⊤)) • x₂ := h5
  change (F.map S.f).hom y = x₂
  rw [h6, hy, h7, one_smul]

/-- **S3. Acyclic complexes.** For `R` fine on compact `X`, the complex of global sections of
an acyclic complex of `R`-modules is acyclic. Proof: a cycle `z ∈ Γ(Kⁿ)` is a global section of
the kernel `Zⁿ`, and `Kⁿ⁻¹ ⟶ Zⁿ` is an epimorphism; apply S2. No sheaf cohomology. Replaces
[A, Lemma 7.2.8]. -/
theorem acyclic_globalSections [CompactSpace X] {R : RingSheaf X} (hR : IsFine R)
    {K : CochainComplex (Mod R) ℤ} (hK : K.Acyclic) :
    (((globalSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro i
  exact exact_map_globalSections hR _ (hK i)

/-- **S3, degreewise.** For `R` fine on compact `X`, if a complex of `R`-modules is exact at
`i`, so is its complex of global sections (the proof of S3 is degreewise). Used for S10. -/
theorem exactAt_globalSections [CompactSpace X] {R : RingSheaf X} (hR : IsFine R)
    {K : CochainComplex (Mod R) ℤ} {i : ℤ} (hK : K.ExactAt i) :
    (((globalSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt i :=
  exact_map_globalSections hR _ hK

/-- A morphism of complexes in an abelian category is a quasi-isomorphism iff its mapping cone
is acyclic. -/
private lemma quasiIso_iff_acyclic_mappingCone {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  have := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
  exact this.trans (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/-- **S3, for quasi-isomorphisms.** For `R` fine on compact `X`, `Γ` maps quasi-isomorphisms of
complexes of `R`-modules to quasi-isomorphisms (S3 applied to the mapping cone, which `Γ`
preserves as an additive functor). Used in C4 step 4. -/
theorem quasiIso_globalSections [CompactSpace X] {R : RingSheaf X} (hR : IsFine R)
    {K L : CochainComplex (Mod R) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((globalSections R).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  rw [quasiIso_iff_acyclic_mappingCone] at *
  have h := acyclic_globalSections hR ‹(CochainComplex.mappingCone f).Acyclic›
  intro i
  exact (h i).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso f (globalSections R))

end Cohesive
