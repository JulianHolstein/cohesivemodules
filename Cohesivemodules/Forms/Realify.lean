import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# F1: realification of complex manifolds

Blueprint item F1 (conventions §6–§7). A complex manifold (`IsManifold 𝓘(ℂ, E) ∞ M`) is a real
smooth manifold with the same charts (`IsManifold 𝓘(ℝ, E) ∞ M`), where `E` carries its real
structure `NormedSpace.complexToReal`. Also: multiplication on `ℂ` is real-smooth
(`ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ`, absent from Mathlib), needed for the sheaf of real-smooth
`ℂ`-valued functions `smoothSheafCommRing 𝓘(ℝ, E) 𝓘(ℝ, ℂ) M ℂ` (conventions §7).

Both are theorems, to be used as **local** instances (`attribute [local instance] …`), never
global ones: a global instance `IsManifold 𝓘(ℝ, E) ∞ M ← IsManifold 𝓘(ℂ, E) ∞ M` could loop or
create diamonds (CLAUDE.md, conventions §7).

The sources use the underlying real manifold of a complex manifold implicitly ([B, §4], [A, §7]).
-/

namespace Cohesive

open Manifold
open scoped ContDiff

/-- **F1.** A complex manifold modelled on `E` is a real `C^∞` manifold with the same charts:
`IsManifold 𝓘(ℂ, E) ∞ M → IsManifold 𝓘(ℝ, E) ∞ M`. The transition maps are `ContDiffOn ℂ ∞`,
hence `ContDiffOn ℝ ∞` (`ContDiffOn.restrict_scalars`). `E` is a real normed space through
`NormedSpace.complexToReal`. Implicit in [B, §4], [A, §7].

Deviation: none (the sources take the underlying real manifold for granted). A theorem, used
as a local instance only (conventions §7). -/
theorem isManifold_real {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] :
    IsManifold 𝓘(ℝ, E) ∞ M := by
  refine isManifold_of_contDiffOn 𝓘(ℝ, E) ∞ M fun e e' he he' => ?_
  have h := (StructureGroupoid.compatible (contDiffGroupoid ∞ 𝓘(ℂ, E)) he he')
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  exact h.1.restrict_scalars ℝ

/-- **F1.** `ℂ` is a real-smooth ring: `ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ` (absent from Mathlib, which
has it only over the field itself; it gives `ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ` by instance). Needed for
the sheaf of real-smooth `ℂ`-valued functions `smoothSheafCommRing 𝓘(ℝ, E) 𝓘(ℝ, ℂ) M ℂ`
(conventions §7). A theorem, used as a local instance only. -/
theorem contMDiffRing_real_complex : ContMDiffRing 𝓘(ℝ, ℂ) ∞ ℂ where
  toContMDiffAdd := inferInstance
  contMDiff_mul := by
    have hg : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ × ℂ) ∞ (fun p : ℂ × ℂ => (p.1, p.2)) :=
      contMDiff_fst.prodMk_space contMDiff_snd
    exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).comp_contMDiff hg

end Cohesive
