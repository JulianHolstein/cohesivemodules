import Cohesivemodules.Comparison.FullyFaithfulLocal
import Cohesivemodules.Comparison.EssSurj

set_option linter.style.header false

/-!
# C6: the comparison theorem

Blueprint item C6 (§4), [A, Thm 7.2.20 at h = 0], [CHL, Thm 7.10, Cor 7.13] (Thm 7.10 is stated
for twisted modules, Cor 7.13 for cohesive modules). For resolving data `D` (C0.b)
on a compact Hausdorff space, `J : Ho(P_{𝒜(X)}) ⥤ D(O)` is full and faithful (C4) with essential
image exactly `D_perf(X, O)` (C2, C5). F15 applies it to the Dolbeault data (H1, H2).
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace ResolvingData

variable (D : ResolvingData X)

/-- **C6. Comparison theorem.** `J` is full, faithful, and its essential image is `D_perf(X, O)`.
[A, Thm 7.2.20 at h = 0]. -/
theorem comparison [CompactSpace X] [T2Space X] [HasDerivedCategory.{w} (Mod D.R)] :
    D.J.Full ∧ D.J.Faithful ∧ D.J.essImage = Perf D.R := by
  refine ⟨D.full_J, D.faithful_J, ?_⟩
  ext K
  constructor
  · rintro ⟨M, ⟨e⟩⟩
    obtain ⟨L, hL, ⟨e'⟩⟩ := D.perf_J_obj M
    exact ⟨L, hL, ⟨e.symm ≪≫ e'⟩⟩
  · intro hK
    obtain ⟨M, ⟨e⟩⟩ := D.exists_J_obj_iso K hK
    exact ⟨M, ⟨e⟩⟩

end ResolvingData

end Cohesive
