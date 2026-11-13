-- FROZEN (gate 3, 26 Oct 2026; H1, H2, in the main statement). Do not edit without approval.
import Cohesivemodules.Forms.Dolbeault
import Cohesivemodules.Algebra.DegreeZero

set_option linter.style.header false

/-!
# H1, H2: the analytic hypotheses of the main theorem

Blueprint items H1, H2 (§5; H2 in its v1.9 Lean form, audit F9). Part of the statement: frozen
at gate 3. Both are `Prop`-valued definitions about the complex manifold `X` (modelled on `E`),
used as hypotheses of the main theorem, never as axioms (CLAUDE.md). Both are true on every
complex manifold; their proofs are LATER (Z4, Z5).

* `DolbeaultGrothendieck E X` (H1): `∂̄`-closed forms of positive degree are locally `∂̄`-exact.
  With F12 this says `ρ : O_X → 𝒜^•_X` is a resolution.
* `LocalGaugeLemma E X` (H2, weak form): every cohesive module over `A = 𝒜_X(X)` is, near each
  point, homotopy equivalent to `𝒜_X(U′) ⊗_{O_X(U′)} W` for a bounded complex `W` of finitely
  generated projective `O_X(U′)`-modules. This is field LL of C0, verbatim.
* Trivial cases: `dolbeaultGrothendieck_of_lt` (`q + 1 > n`),
  `dolbeaultGrothendieck_of_finrank_eq_zero` (`n = 0`),
  `localGaugeLemma_of_finrank_eq_zero` (`n = 0`; the algebra is in `Algebra/DegreeZero.lean`).

## Deviations
* ⚠ H1 is stated on `X`, not on open subsets of `E` (keeps chart transport F13 off the critical
  path; the standard sheaf-theoretic form of the lemma).
* ⚠ H2 is the weak, sectionwise form: only for restrictions of global cohesive modules, and a
  homotopy equivalence (an isomorphism in `Ho(P_{𝒜_X(U′)})`), as in the proof of
  [B, Lemma 4.1.5] and [A, Assumption 6] at the level of sections.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **H1. Dolbeault–Grothendieck lemma** (HYP). [B, §4.1], [A, §7.1]. For every open `U`,
`q : ℕ`, `x ∈ U` and form `α` of degree `q + 1` on `U` with `∂̄α = 0`, there are an open
`U′ ∋ x` inside `U` and a form `η` of degree `q` on `U′` with `∂̄η = α|U′`. -/
def DolbeaultGrothendieck : Prop :=
  ∀ (U : Opens X) (q : ℕ) (x : X), x ∈ U →
    ∀ α ∈ dolbeaultGrade E U ((q : ℤ) + 1), GCDga.d (𝒜 := dolbeaultGrade E U) α = 0 →
      ∃ (U' : Opens X) (h : U' ≤ U), x ∈ U' ∧
        ∃ η ∈ dolbeaultGrade E U' (q : ℤ),
          GCDga.d (𝒜 := dolbeaultGrade E U') η = (dolbeaultRes E h).toAlgHom α

/-- **H2. Local gauge lemma, weak form** (HYP). [B, Lemma 4.1.5 (its proof)],
[A, Assumption 6]. For every cohesive module `M` over the Dolbeault algebra `A = 𝒜_X(X)` and
every `x : X`, there are an open `U′ ∋ x`, a bounded complex `W` of finitely generated
projective `O_X(U′)`-modules, and an isomorphism in `Ho(P_{𝒜_X(U′)})` between the restriction
`M|U′` (A9, base change along `dolbeaultRes`) and `𝒜_X(U′) ⊗_{O_X(U′)} W` (A10, along
`ρ_{U′} = dolbeaultRhoU`; `c = 0` and `∂̄ ∘ ρ_{U′} = 0`, F12). -/
def LocalGaugeLemma : Prop :=
  ∀ (M : CohesiveModule (dolbeault E X)) (x : X),
    ∃ (U' : Opens X) (_ : x ∈ U')
      (W : CochainComplex (ModuleCat.{0} ((holSheaf E X).obj.obj (op U'))) ℤ)
      (hW : IsBoundedFGProj ((holSheaf E X).obj.obj (op U')) W),
      Nonempty (HoP.mk (M.baseChange (dolbeaultRes E (le_top : U' ≤ ⊤))) ≅
        HoP.mk (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E U') W
          (dbar_dolbeaultRhoU E U') rfl hW))

/-! ## Trivial cases (blueprint H1, H2; K1) -/

/-- H1, trivial case: for `q + 1 > n` there are no nonzero forms of degree `q + 1`. -/
theorem dolbeaultGrothendieck_of_lt (U : Opens X) (q : ℕ) (hq : Module.finrank ℂ E < q + 1)
    (x : X) (hx : x ∈ U) (α : DolbeaultAlg E U) (hα : α ∈ dolbeaultGrade E U ((q : ℤ) + 1))
    (hd : GCDga.d (𝒜 := dolbeaultGrade E U) α = 0) :
    ∃ (U' : Opens X) (h : U' ≤ U), x ∈ U' ∧
      ∃ η ∈ dolbeaultGrade E U' (q : ℤ),
        GCDga.d (𝒜 := dolbeaultGrade E U') η = (dolbeaultRes E h).toAlgHom α := by
  have hα0 : α = 0 := by
    apply Subtype.ext
    exact IsOfDegree.eq_zero (Or.inr (by exact_mod_cast hq)) hα
  refine ⟨U, le_rfl, hx, 0, zero_mem _, ?_⟩
  rw [hα0, map_zero, map_zero]

/-- **H1 in dimension 0** (K1). If `dim_ℂ E = 0`, H1 holds. -/
theorem dolbeaultGrothendieck_of_finrank_eq_zero (h : Module.finrank ℂ E = 0) :
    DolbeaultGrothendieck E X := by
  intro U q x hx α hα hd
  exact dolbeaultGrothendieck_of_lt E X U q (by omega) x hx α hα hd

/-- **H2 in dimension 0** (K1). If `dim_ℂ E = 0`, H2 holds, with `U′ = X`: then `𝒜_X(X)` is
concentrated in degree `0` and `ρ_X : O_X(X) → 𝒜⁰_X(X)` is bijective (F12: a form of degree `0`
with `∂̄α = 0`, here automatic, is holomorphic), so `M` is `𝒜_X(X) ⊗ W` with `W` its complex of
generators (`exists_iso_fromComplex_of_degree_zero`). -/
theorem localGaugeLemma_of_finrank_eq_zero (h : Module.finrank ℂ E = 0) :
    LocalGaugeLemma E X := by
  intro M x
  have hdeg : ∀ q : ℤ, q ≠ 0 → dolbeaultGrade E (⊤ : Opens X) q = ⊥ := by
    intro q hq
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · exact GCDga.zero_of_neg q hlt
    · exact GCDga.zero_of_gt q (by show (Module.finrank ℂ E : ℤ) < q; omega)
  have hb : Function.Bijective (dolbeaultRhoU E (⊤ : Opens X)) := by
    refine ⟨dolbeaultRhoU_injective E ⊤, fun α => ?_⟩
    refine exists_dolbeaultRhoU_of_dbar_eq_zero E α ?_
    exact GCDga.eq_zero_of_gt (dolbeaultGrade E (⊤ : Opens X)) (q := 1)
      (by show (Module.finrank ℂ E : ℤ) < 1; omega) (GCDga.d_mem_one _ α.2)
  obtain ⟨W, hW, e⟩ := exists_iso_fromComplex_of_degree_zero hdeg
    (dolbeaultRhoU E (⊤ : Opens X)) hb (dbar_dolbeaultRhoU E ⊤) rfl
    (M.baseChange (dolbeaultRes E (le_top : (⊤ : Opens X) ≤ ⊤)))
  exact ⟨⊤, trivial, W, hW, e⟩

end Cohesive
