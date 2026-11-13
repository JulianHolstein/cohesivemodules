-- FROZEN (gate 3, 26 Oct 2026; F7 definitions, in the main statement). Do not edit without approval.
import Cohesivemodules.Forms.ProductDef

set_option linter.style.header false

/-!
# F7: holomorphic pullback (definitions)

Blueprint item F7 (conventions §6). This file holds the definitions of F7 that the main
statement depends on, with their basic API; it will be frozen at gate 3. The holomorphic
pullback of forms and its properties (F7.a–c) are in `Cohesivemodules/Forms/Pullback.lean`.

Definitions: `DolbeaultFibre.pull` (pullback of a single form at a point along a `ℂ`-linear
map, through `Conj.map`) and `TotFibre.pull` (its componentwise extension to the total fibre).
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap Conj

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {q : ℕ}

/-- **F7.** Pullback of a single form at a point along a `ℂ`-linear map `T` of `E`:
`α ↦ α ∘ T` (slots in `Ē`, through `Conj.map T`). -/
def DolbeaultFibre.pull (T : E →L[ℂ] E) (α : DolbeaultFibre E q F) : DolbeaultFibre E q F :=
  α.compContinuousLinearMap (Conj.map T)

/-- F7: formula for `DolbeaultFibre.pull`. -/
@[simp] theorem DolbeaultFibre.pull_apply (T : E →L[ℂ] E) (α : DolbeaultFibre E q F)
    (v : Fin q → Conj E) :
    DolbeaultFibre.pull T α v = α (fun i => Conj.map T (v i)) := rfl

/-! ## F7.b: on fibres, pullback is an algebra map -/

variable [FiniteDimensional ℂ E]

namespace TotFibre

/-- **F7.b.** Pullback along a `ℂ`-linear `T` on the total fibre, componentwise
`DolbeaultFibre.pull`. -/
def pull (T : E →L[ℂ] E) : TotFibre E →ₗ[ℂ] TotFibre E where
  toFun x i := DolbeaultFibre.pull T (x i)
  map_add' x y := by
    funext i
    ext v
    rfl
  map_smul' c x := by
    funext i
    ext v
    rfl

end TotFibre

end Cohesive
