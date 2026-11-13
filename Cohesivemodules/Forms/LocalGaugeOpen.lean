import Cohesivemodules.Forms.LocalFreeOpen
import Cohesivemodules.Forms.LocalGauge

set_option linter.style.header false

/-!
# Z3.e: the local gauge lemma over an open

Blueprint item Z3.e (`blueprint/blueprint-tw.md` §3 E.1; blueprint §11 v1.19, decision D7). H2
(Z5.i, `localGaugeLemma`) with the base `X` replaced by an open `U₀`: a cohesive module over
`𝒜_X(U₀)` is, near each `x ∈ U₀`, isomorphic in `Ho(P)` to `𝒜 ⊗_O W` for a bounded complex `W`
of finitely generated projective `O(U′)`-modules. The proof is that of `localGaugeLemma` with
`exists_free_baseChange_open` in place of `exists_free_baseChange` (the frame model and the gauge
induction, `exists_local_iso`, are already local).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- Helper: a graded frame of the base change of `N` to a small neighbourhood `U' ≤ U₀` of `x`. -/
private theorem exists_frame_open {U₀ : Opens X} (N : CohesiveModule (dolbeaultGrade E U₀))
    {x : X} (hx : x ∈ U₀) :
    ∃ (U' : Opens X) (h : U' ≤ U₀) (_ : x ∈ U') (r : ℕ), Nonempty (GradedFrame
      (dolbeaultGrade E U') (N.baseChange (dolbeaultRes E h)).Q r) := by
  obtain ⟨U', h, hxU', -, hfree⟩ := exists_free_baseChange_open E N hx
  obtain ⟨r, ⟨F⟩⟩ := exists_gradedFrame_bcGen (dolbeaultRes E h) N hfree
  exact ⟨U', h, hxU', r, ⟨F⟩⟩

/-- Helper: `(N|U′)|U″ ≅ N|U″` in `Ho(P)` (`dolbeaultRes_comp`, `bcCompIso`). -/
private theorem iso_open_comp {U₀ U' U'' : Opens X} (N : CohesiveModule (dolbeaultGrade E U₀))
    (h : U' ≤ U₀) (hle : U'' ≤ U') :
    Nonempty (HoP.mk (N.baseChange (dolbeaultRes E (hle.trans h))) ≅
      HoP.mk ((N.baseChange (dolbeaultRes E h)).baseChange (dolbeaultRes E hle))) := by
  have e : dolbeaultRes E (hle.trans h) = (dolbeaultRes E hle).comp (dolbeaultRes E h) :=
    (dolbeaultRes_comp E h hle).symm
  rw [e]
  exact ⟨bcCompIso (dolbeaultRes E h) (dolbeaultRes E hle) (HoP.mk N)⟩

variable (E) in
/-- **Z3.e (H2 over an open).** [B, Lemma 4.1.5], blueprint-ll. For an open `U₀`, a cohesive
module `N` over `𝒜_X(U₀)` and `x ∈ U₀`, there are an open `U′ ≤ U₀` containing `x`, a bounded
complex `W` of finitely generated projective `O_X(U′)`-modules and an isomorphism in
`Ho(P_{𝒜_X(U′)})` between `N|U′` (A9) and `𝒜_X(U′) ⊗_{O(U′)} W` (A10). For `U₀ = ⊤` this is the
statement of `localGaugeLemma` (H2). -/
theorem localGaugeLemmaOpen {U₀ : Opens X} (N : CohesiveModule (dolbeaultGrade E U₀)) {x : X}
    (hx : x ∈ U₀) :
    ∃ (U' : Opens X) (hU' : U' ≤ U₀), x ∈ U' ∧
      ∃ (W : CochainComplex (ModuleCat.{0} ((holSheaf E X).obj.obj (op U'))) ℤ)
        (hW : IsBoundedFGProj ((holSheaf E X).obj.obj (op U')) W),
        Nonempty (HoP.mk (N.baseChange (dolbeaultRes E hU')) ≅
          HoP.mk (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E U') W
            (dbar_dolbeaultRhoU E U') rfl hW)) := by
  obtain ⟨U', h, hxU', r, ⟨F⟩⟩ := exists_frame_open N hx
  obtain ⟨U'', hle, hxU'', W, hW, ⟨hiso⟩⟩ := exists_local_iso hxU'
    (N.baseChange (dolbeaultRes E h)) F
  obtain ⟨e⟩ := iso_open_comp N h hle
  exact ⟨U'', hle.trans h, hxU'', W, hW, ⟨e ≪≫ hiso⟩⟩

end Cohesive
