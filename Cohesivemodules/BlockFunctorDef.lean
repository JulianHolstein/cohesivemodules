-- FROZEN (gate 5, 1 Nov 2026; F14 C0.a, F15 blockFunctor, in the main statement). Do not edit.
import Cohesivemodules.Comparison.FunctorDef
import Cohesivemodules.Hypotheses

set_option linter.style.header false

/-!
# F14 (C0.a part) and F15: the functor of the main theorem

Blueprint items F14 and F15 (§5), [B, Thm 4.1.3], [A, Def 7.2.3 and Thm 7.4.3 at h = 0].
* `dolbeaultPresheaf E X`: the presheaf of dgas `U ↦ 𝒜_X(U)` (F10) as a `DgaPresheaf` (C0).
* `dolbeaultPreData E X`: the Dolbeault data as pre-resolving data (C0.a): the dgas 𝒜_X(U),
  `O = holSheaf E X` (F12), `ρ_U : O(U) → 𝒜⁰(U)`, fineness of 𝒜⁰ (F11) and local frames (F11).
  No analytic hypothesis: H1 and H2 enter only in `Main.lean` (C0.b).
* `blockFunctor E X : HoP (dolbeault E X) ⥤ DerivedCategory (Mod (ringOf (holSheaf E X)))`, the
  functor `J` of C1 for these data (`M ↦ α(M)`).
These definitions enter `MainStatement` (`Statements.lean`), so this file is frozen at gate 5.

## Deviations
* As in §1: `blockFunctor` lands in the whole derived category (a functor into D_perf would need
  C2, hence H2); the `HasDerivedCategory` instance is an argument, fixed to
  `HasDerivedCategory.standard` once in `Statements.lean`.
* Blueprint §7 puts F14–F15 in `Main.lean`; the hypothesis-free definitions are here instead,
  because `Statements.lean` may import only frozen files (v1.13 draft, §11).
* `X` compact Hausdorff is required already here (fineness of 𝒜⁰, a field of C0.a).
-/

noncomputable section

universe w

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- **F14.** [B, §4], [A, §7.1]. The Dolbeault presheaf of dgas `U ↦ 𝒜_X(U)` (F10), with the
restriction of forms, as a `DgaPresheaf` (C0). -/
def dolbeaultPresheaf : DgaPresheaf X where
  A U := DolbeaultAlg E U
  𝒜 U := dolbeaultGrade E U
  res h := dolbeaultRes E h
  res_id _ _ := rfl
  res_comp _ _ _ := rfl

/-- F14: one carrier, the derived `𝒜⁰` presheaf of the Dolbeault data is `dolbeault0` (rfl). -/
theorem dolbeaultPresheaf_pre0 : (dolbeaultPresheaf E X).pre0 = (dolbeault0 E X).obj := rfl

variable [T2Space X] [CompactSpace X]

/-- **F14 (C0.a).** [A, Assumptions 7.2 at h = 0], [B, §4.1]. The Dolbeault data of a compact
Hausdorff complex manifold `X` as pre-resolving data: dgas `𝒜_X(U)` (F10), `O = O_X` (F12),
`ρ_U : O_X(U) → 𝒜⁰(U)` the inclusion of holomorphic functions with `∂̄ ∘ ρ = 0` (F12), `𝒜⁰`
fine (F11) and each `𝒜^q` locally free over `𝒜⁰` (F11). Every field is a phase-3 theorem; no
analytic hypothesis. -/
def dolbeaultPreData : PreResolvingData X where
  D := dolbeaultPresheaf E X
  glue U a h := by
    obtain ⟨b, hb, hu⟩ := dolbeault_glue E U a (fun i j ↦ congrArg Subtype.val (h i j))
    exact ⟨b, fun i ↦ Subtype.ext (hb i), fun b' hb' ↦ hu b' fun i ↦ congrArg Subtype.val (hb' i)⟩
  degree_local q a h := isOfDegree_of_locally E fun x ↦ by
    obtain ⟨V, hV, hx, hm⟩ := h x x.2
    exact ⟨V, hV, hx, hm⟩
  isSheaf0 := (dolbeault0 E X).property
  c_eq_zero _ := rfl
  O := holSheaf E X
  ρ U := dolbeaultRhoU E U
  ρ_natural _ _ := rfl
  d_ρ U := dbar_dolbeaultRhoU E U
  isFine0 := isFine_dolbeault0 E (X := X)
  locFrame q x := by
    obtain ⟨U, hx, e, he⟩ := dolbeault_locallyFree E (X := X) q x
    exact ⟨U, hx, _, inferInstance, e, he⟩

/-- F14: the global dga of the Dolbeault data is the Dolbeault algebra `dolbeault E X` (rfl). -/
theorem dolbeaultPreData_𝒜X : (dolbeaultPreData E X).𝒜X = dolbeault E X := rfl

/-- F14: the ring sheaf of the Dolbeault data is `O_X`, as a `RingSheaf` (rfl). -/
theorem dolbeaultPreData_R : (dolbeaultPreData E X).R = ringOf (holSheaf E X) := rfl

/-- **F15. The functor of the main theorem.** [B, Thm 4.1.3], [A, Def 7.2.3 at h = 0].
`blockFunctor E X : Ho(P_A) ⥤ D(O_X)` for `A = 𝒜_X(X)` the Dolbeault algebra: the functor `J`
of C1 (`M ↦ α(M)`, the complex of sheaves `V ↦ (𝒜_X(V) ⊗_A M)^n`) for the Dolbeault
pre-resolving data. Defined without H1, H2; lands in the whole derived category (§1 ⚠).
Lean note: the instance `h` is passed explicitly (`@PreResolvingData.J … h`) because instance
search does not unfold `(dolbeaultPreData E X).R` to `ringOf (holSheaf E X)`; the two are equal
by `rfl` (`dolbeaultPreData_R`), so this is the same functor `J`. -/
def blockFunctor [h : HasDerivedCategory.{w} (Mod (ringOf (holSheaf E X)))] :
    HoP (dolbeault E X) ⥤ DerivedCategory (Mod (ringOf (holSheaf E X))) :=
  @PreResolvingData.J X _ (dolbeaultPreData E X) h

/-- F15: `blockFunctor` is `J` of the Dolbeault pre-resolving data (rfl). -/
theorem blockFunctor_eq [h : HasDerivedCategory.{w} (Mod (ringOf (holSheaf E X)))] :
    blockFunctor E X = @PreResolvingData.J _ _ (dolbeaultPreData E X) h := rfl

end Cohesive
