import Cohesivemodules.Forms.LocalFree

set_option linter.style.header false

/-!
# Z3.e: local freeness over an open

Blueprint item Z3.e (`blueprint/blueprint-tw.md` §3 E.1, §4; blueprint §11 v1.19, decision D7).
`exists_free_baseChange` (Z5.g) with the base `X` replaced by an open `U₀`: for a cohesive module
over `𝒜_X(U₀)` and `x ∈ U₀`, the generators become free over `𝒜⁰(U′)` on a small `U′ ≤ U₀`.
Same proof (localization at the kernel of evaluation at `x`).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

variable (E) in
/-- **Z3.e (Z5.g over an open).** [B, proof of Lemma 4.1.5], blueprint-ll A. For a cohesive module
`M` over `𝒜_X(U₀)` and `x ∈ U₀`, there is an open `U′ ≤ U₀` containing `x`, inside the source of
the chart at `x`, such that every base-changed generator module `𝒜⁰(U′) ⊗_{𝒜⁰(U₀)} Q^p` is free.
For `U₀ = ⊤` this is `exists_free_baseChange`. -/
theorem exists_free_baseChange_open {U₀ : Opens X} (M : CohesiveModule (dolbeaultGrade E U₀))
    {x : X} (hx : x ∈ U₀) :
    ∃ (U' : Opens X) (h : U' ≤ U₀), x ∈ U' ∧ (U' : Set X) ⊆ (chartAt E x).source ∧
      ∀ p, Module.Free ↥(dolbeaultGrade E U' 0) (BCGen (dolbeaultRes E h) M.Q p) := by
  have hfree : ∀ p, ∃ r ∉ RingHom.ker (evalForm0 E (⟨x, hx⟩ : U₀)),
      Module.Free (Localization.Away r) (LocalizedModule.Away r (M.Q p)) := by
    intro p
    have := M.finite p
    have := M.projective p
    have : (RingHom.ker (evalForm0 E (⟨x, hx⟩ : U₀))).IsPrime := RingHom.ker_isPrime _
    exact exists_free_away (R := ↥(dolbeaultGrade E U₀ 0)) (Q := M.Q p) _
  choose r hr hrfree using hfree
  obtain ⟨a, b, hab⟩ := M.bounded
  set e := chartAt E x
  let V : Set X := e.source ∩ U₀ ∩ ⋂ p ∈ Finset.Icc a b,
    {y | ∃ hy : y ∈ U₀, evalForm0 E ⟨y, hy⟩ (r p) ≠ 0}
  have hV : IsOpen V := by
    refine (e.open_source.inter U₀.isOpen).inter (isOpen_biInter_finset fun p _ ↦ ?_)
    have hc := (continuous_evalForm0 E (r p)).isOpen_preimage {0}ᶜ isOpen_compl_singleton
    have : {y : X | ∃ hy : y ∈ U₀, evalForm0 E ⟨y, hy⟩ (r p) ≠ 0} =
        Subtype.val '' ((fun y : U₀ ↦ evalForm0 E y (r p)) ⁻¹' {0}ᶜ) := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      exact ⟨fun ⟨hy, h⟩ ↦ ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨y', h, hy'⟩ ↦ hy' ▸ ⟨y'.2, h⟩⟩
    rw [this]
    exact U₀.isOpen.isOpenMap_subtype_val _ hc
  have hxV : x ∈ V := by
    refine ⟨⟨mem_chart_source E x, hx⟩, Set.mem_iInter₂.2 fun p _ ↦ ⟨hx, ?_⟩⟩
    exact fun h0 ↦ hr p (RingHom.mem_ker.2 h0)
  have hVe : V ⊆ e.source := fun y hy ↦ hy.1.1
  have hVU : (⟨V, hV⟩ : Opens X) ≤ U₀ := fun y hy ↦ hy.1.2
  refine ⟨⟨V, hV⟩, hVU, hxV, hVe, fun p ↦ ?_⟩
  by_cases hp : p < a ∨ b < p
  · have := hab p hp
    exact free_bcGen_of_subsingleton _ M.Q p
  · have hpI : p ∈ Finset.Icc a b := Finset.mem_Icc.2 (by omega)
    have := hrfree p
    refine free_bcGen_of_isUnit _ M.Q p (r p) ?_
    refine isUnit_of_evalForm0_ne_zero E _ fun y ↦ ?_
    obtain ⟨hy, h⟩ := Set.mem_iInter₂.1 (y.2 : (y : X) ∈ V).2 p hpI
    exact h

end Cohesive
