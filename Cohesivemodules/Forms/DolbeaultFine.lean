import Cohesivemodules.Forms.Holomorphic
import Cohesivemodules.Forms.Realify
import Cohesivemodules.Sheaf.Fine
import Cohesivemodules.Sheaf.Flat.Tensor
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option linter.style.header false

/-!
# F10–F12: gluing, fineness, local freeness, and `0 → O → 𝒜⁰ → 𝒜¹`

Blueprint items F10 (sheaf conditions), F11, F12 (§5), about the definitions of
`Forms/SheafDef.lean` and `Forms/Holomorphic.lean`. These are the facts F14 feeds into the
fields of C0.a.

* F10 `dolbeault_glue`, `isOfDegree_of_locally`: Dolbeault forms on a cover glue uniquely, and
  having degree `q` is local (the sheaf conditions of `𝒜` and of each `𝒜^{0,q}`).
* F11 `isFine_dolbeault0`: `𝒜⁰` is fine (`X` compact Hausdorff; smooth partitions of unity).
* F11 `dolbeault_locallyFree`: each `𝒜^{0,q}` is locally free over `𝒜⁰` of rank `C(n, q)`,
  sectionwise: near each point there are forms `e_I` (`|I| = q`), e.g. `dz̄_I` in a chart, such
  that on every smaller open every form of degree `q` is uniquely `Σ f_I e_I`, `f_I ∈ 𝒜⁰`.
* F12 `dolbeaultRhoU_injective`, `dbar_dolbeaultRhoU`, `exists_dolbeaultRhoU_of_dbar_eq_zero`:
  `0 → O_X(U) → 𝒜⁰(U) → 𝒜¹(U)` is exact on every open `U` (F8).

## Deviations
* Local freeness is stated sectionwise (a local frame), not as `SheafOfModules.IsLocallyFree`:
  the module sheaves `𝒜^{0,q}` over `𝒜⁰` are derived in C0 (v1.9) from the presheaf of dgas,
  and F14 converts. ⚠ F11 needs `X` Hausdorff and compact (hence σ-compact) for partitions of
  unity; the sources assume `X` compact.

Part 1 of 3 of the original `Forms/Dolbeault.lean`, split for size; continued in
`Forms/DolbeaultFree.lean`.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-! ## F10: sheaf conditions -/

/-- **F10** (sheaf condition for `𝒜`). Dolbeault forms `α i` on the opens `U i` that agree on
overlaps glue to a unique Dolbeault form on `⨆ i, U i` (forms are functions and `IsDolbeault`
is local, F9). -/
theorem dolbeault_glue {ι : Type} (U : ι → Opens X) (α : ∀ i, DolbeaultAlg E (U i))
    (hα : ∀ i j, restrictForm E (inf_le_left : U i ⊓ U j ≤ U i) (α i) =
      restrictForm E (inf_le_right : U i ⊓ U j ≤ U j) (α j)) :
    ∃! β : DolbeaultAlg E (⨆ i, U i),
      ∀ i, restrictForm E (le_iSup U i) β = (α i : U i → TotFibre E) := by
  classical
  have hmem : ∀ y : (⨆ i, U i : Opens X), ∃ i, (y : X) ∈ U i := fun y ↦ Opens.mem_iSup.1 y.2
  let β0 : (⨆ i, U i : Opens X) → TotFibre E := fun y ↦
    (α (Classical.choose (hmem y)) : U (Classical.choose (hmem y)) → TotFibre E)
      ⟨y, Classical.choose_spec (hmem y)⟩
  have key : ∀ (i : ι) (y : (⨆ i, U i : Opens X)) (hy : (y : X) ∈ U i),
      β0 y = (α i : U i → TotFibre E) ⟨y, hy⟩ := fun i y hy ↦ by
    have h := congrFun (hα (Classical.choose (hmem y)) i)
      ⟨y, Opens.mem_inf.2 ⟨Classical.choose_spec (hmem y), hy⟩⟩
    exact h
  have hβ : ∀ i, restrictForm E (le_iSup U i) β0 = (α i : U i → TotFibre E) := fun i ↦
    funext fun y ↦ key i ⟨y, le_iSup U i y.2⟩ y.2
  have hd : IsDolbeault E β0 := isDolbeault_of_locally fun x ↦
    ⟨U (Classical.choose (hmem x)), le_iSup U _, Classical.choose_spec (hmem x), by
      rw [hβ]; exact (α _).2⟩
  refine ⟨⟨β0, hd⟩, hβ, fun γ hγ ↦ Subtype.ext (funext fun y ↦ ?_)⟩
  have := congrFun (hγ (Classical.choose (hmem y))) ⟨y, Classical.choose_spec (hmem y)⟩
  exact this.trans (key _ y _).symm

/-- **F10** (sheaf condition for `𝒜^{0,q}`). Having degree `q` is local. -/
theorem isOfDegree_of_locally {U : Opens X} {q : ℤ} {α : U → TotFibre E}
    (hα : ∀ x : U, ∃ (V : Opens X) (h : V ≤ U), (x : X) ∈ V ∧
      IsOfDegree E q (restrictForm E h α)) :
    IsOfDegree E q α := by
  intro y i hi
  obtain ⟨V, h, hy, hV⟩ := hα y
  exact hV ⟨y, hy⟩ i hi

/-! ## F11: fineness and local freeness -/

/-- A constant `0`-form is the scalar multiple of `1` in the total fibre. -/
theorem ofDeg0_eq_smul_one (c : ℂ) :
    TotFibre.ofDeg 0 (form0Equiv E ℂ c) = c • (1 : TotFibre E) := by
  have h : form0Equiv E ℂ c = c • form0Equiv E ℂ 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h, map_smul, ← TotFibre.one_eq]

open Classical in
/-- The chart expression of a function viewed as a `0`-form is `c • 1`. -/
theorem chartExpr_funForm {U : Opens X} (f : U → ℂ) (e : OpenPartialHomeomorph X E)
    (z : E) : chartExpr E (funForm E f) e z =
      (if h : e.symm z ∈ U then f ⟨e.symm z, h⟩ else 0) • (1 : TotFibre E) := by
  unfold chartExpr
  by_cases h : e.symm z ∈ U
  · simp only [h, ↓reduceDIte, funForm, ofDeg0_eq_smul_one, map_smul, TotFibre.pull_one]
  · simp only [h, ↓reduceDIte, zero_smul]

attribute [local instance] isManifold_real contMDiffRing_real_complex

/-- A real-smooth function `X → ℂ` is a Dolbeault form of degree `0` on `⊤`. -/
private theorem isDolbeault_funForm_real (g : X → ℂ) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ g) :
    IsDolbeault E (funForm E fun y : (⊤ : Opens X) ↦ g y) := by
  intro x
  set e := chartAt E (x : X) with he
  have hxs : (x : X) ∈ e.source := mem_chart_source E (x : X)
  have hex : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm (e x) :=
    (contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
      (StructureGroupoid.subset_maximalAtlas _ (chart_mem_atlas E (x : X)))).contMDiffAt
      (e.open_target.mem_nhds (e.map_source hxs))
  have h1 : ContDiffAt ℝ ∞ (g ∘ e.symm) (e x) :=
    (hg.contMDiffAt.comp (e x) hex).contDiffAt
  have h2 : chartExpr E (funForm E fun y : (⊤ : Opens X) ↦ g y) e =
      fun z ↦ (g ∘ e.symm) z • (1 : TotFibre E) := by
    funext z
    rw [chartExpr_funForm]
    simp only [Opens.mem_top, ↓reduceDIte, Function.comp_apply]
  rw [h2]
  exact h1.smul contDiffAt_const

/-- **F11.** [B, §4], [A, §7.1]. On a compact Hausdorff complex manifold, `𝒜⁰` is fine (S1):
take a smooth partition of unity `ρ_i` subordinate to a finite open cover
(`SmoothPartitionOfUnity.exists_isSubordinate` for `𝓘(ℝ, E)`); `ρ_i` becomes a section of `𝒜⁰`
through `ℝ → ℂ`, supported in `U i` with `V := (tsupport ρ_i)ᶜ`. -/
theorem isFine_dolbeault0 [T2Space X] [CompactSpace X] :
    IsFine (ringOf (dolbeault0 E X)) := by
  intro ι _ U hU
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) (M := X)
    isClosed_univ (fun i ↦ (U i : Set X)) (fun i ↦ (U i).isOpen) (by
      intro x _
      have : x ∈ (⨆ i, U i : Opens X) := by rw [hU]; trivial
      exact Opens.mem_iSup.1 this |>.elim fun i hi ↦ Set.mem_iUnion.2 ⟨i, hi⟩)
  let ρ : ι → ↥(dolbeaultGrade E (⊤ : Opens X) 0) := fun i ↦
    ⟨⟨funForm E fun y : (⊤ : Opens X) ↦ (((f i y : ℝ)) : ℂ),
      isDolbeault_funForm_real E _ (Complex.ofRealCLM.contDiff.contMDiff.comp (f i).contMDiff)⟩,
      isOfDegree_funForm E _⟩
  refine ⟨ρ, ?_, fun i ↦ ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun y ↦ ?_))
    have h1 : ((∑ i, ρ i : ↥(dolbeaultGrade E (⊤ : Opens X) 0)) : DolbeaultAlg E (⊤ : Opens X)) =
        ∑ i, (ρ i : DolbeaultAlg E (⊤ : Opens X)) := AddSubmonoidClass.coe_finsetSum _ _
    have h2 : ((∑ i, (ρ i : DolbeaultAlg E (⊤ : Opens X)) : DolbeaultAlg E (⊤ : Opens X)) :
        (⊤ : Opens X) → TotFibre E) =
        ∑ i, ((ρ i : DolbeaultAlg E (⊤ : Opens X)) : (⊤ : Opens X) → TotFibre E) :=
      AddSubmonoidClass.coe_finsetSum _ _
    show (((∑ i, ρ i : ↥(dolbeaultGrade E (⊤ : Opens X) 0)) : DolbeaultAlg E (⊤ : Opens X)) :
        (⊤ : Opens X) → TotFibre E) y = 1
    rw [h1, h2, Finset.sum_apply]
    have h3 : ∀ i, ((ρ i : DolbeaultAlg E (⊤ : Opens X)) : (⊤ : Opens X) → TotFibre E) y =
        ((f i y : ℝ) : ℂ) • (1 : TotFibre E) := fun i ↦ ofDeg0_eq_smul_one E _
    simp only [h3]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype,
      f.sum_eq_one (Set.mem_univ _)]
    simp only [Complex.ofReal_one, one_smul]
  · refine ⟨⟨(tsupport (f i))ᶜ, (isClosed_tsupport _).isOpen_compl⟩, ?_, ?_⟩
    · refine top_unique fun x _ ↦ ?_
      by_cases hx : x ∈ tsupport (f i)
      · exact Or.inl (hf i hx)
      · exact Or.inr hx
    · refine Subtype.ext (Subtype.ext (funext fun y ↦ ?_))
      have hy : (f i y : ℝ) = 0 := image_eq_zero_of_notMem_tsupport y.2
      show ((ρ i : DolbeaultAlg E (⊤ : Opens X)) : (⊤ : Opens X) → TotFibre E) ⟨y, trivial⟩ = 0
      rw [show ((ρ i : DolbeaultAlg E (⊤ : Opens X)) : (⊤ : Opens X) → TotFibre E)
        ⟨y, trivial⟩ = ((f i y : ℝ) : ℂ) • (1 : TotFibre E) from ofDeg0_eq_smul_one E _, hy]
      simp only [Complex.ofReal_zero, zero_smul]

end Cohesive
end
