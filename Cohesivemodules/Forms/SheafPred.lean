-- FROZEN (gate 3, 26 Oct 2026; F9 forms and ∂̄, in the main statement). Do not edit.
import Cohesivemodules.Forms.PullbackDef
import Cohesivemodules.Forms.DbarDef
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Sheaves.LocalPredicate

set_option linter.style.header false

/-!
# F9: the Dolbeault forms on a complex manifold (predicate and ∂̄)

Blueprint item F9 (§5), conventions §6 ("Charts"). The definitions here enter the main
statement through the Dolbeault algebra (F10); they are frozen at gate 3.

A form on an open `U` of the complex manifold `X` (modelled on `E`) is a function
`α : U → Λ^{0,•}(E)` (the total fibre `TotFibre E`, F5), with `α y` written in the chart
`chartAt E y`. Its expression in the chart `φ = chartAt E x` is
`z ↦ α(y) ∘ D(chartAt y ∘ φ⁻¹)(z)` at `y = φ⁻¹ z` (`chartExpr`, through `TotFibre.pull` of F7),
and `α` is a Dolbeault form (`IsDolbeault`) if, for every `x ∈ U`, this expression is real
`C^∞` near `φ x`. `∂̄` is computed in `chartAt E x` and evaluated at `φ x` (`dbarSec`).

* `chartTrans e y z`: the derivative at `z` of the transition map from the chart `e` to
  `chartAt y` (complex `fderiv`).
* `chartExpr α e`: the expression of `α` in the chart `e`; `0` where `e⁻¹ z ∉ U` (junk, never
  seen by `ContDiffAt` or `∂̄` at `e x`, which only use a neighbourhood of `e x`).
* `IsDolbeault α`: the local predicate (its `TopCat.LocalPredicate` form, as Mathlib builds
  `smoothSheaf`, is in `Forms/Sheaf.lean`).
* `dbarTot f z`: `∂̄` on the total fibre for `f : E → Λ^{0,•}(E)`, degree by degree (F3).
* `dbarSec α`: `∂̄` of a form on `U`.
* `IsOfDegree q α`: `α` has values in degree `q` (`q : ℤ`; nothing has negative degree).
  `projDeg q α`: the degree-`q` part. `restrictForm h α`: restriction to `V ≤ U`.

## Deviations
* Forms take values in the total fibre `Π_{q ≤ n} Λ^{0,q}(E; ℂ)`; the sheaf `𝒜^{0,q}` is the
  degree-`q` part (`IsOfDegree`, F10, v1.9). [B, §4] and [A, §7.1] use the direct sum of the
  sheaves `𝒜^{0,q}`; the two agree since the sum is finite.
* Only `ℂ`-valued forms (F = ℂ); `F`-valued forms are LATER (Z3, Z8).
* Forms are called `α`, `β`: under `open scoped ContDiff`, `ω` is the analytic exponent.
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]

/-- **F9** (conventions §6, "Charts"). The derivative at `z` of the transition map
`chartAt y ∘ e⁻¹` from the chart `e` to the chart at `y` (complex `fderiv`; junk where the
transition map is not complex-differentiable, i.e. off `e(e.source ∩ (chartAt y).source)`). -/
def chartTrans (e : OpenPartialHomeomorph X E) (y : X) (z : E) : E →L[ℂ] E :=
  fderiv ℂ (chartAt E y ∘ e.symm) z

open Classical in
/-- **F9.** The expression in the chart `e` of `α : U → Λ^{0,•}(E)`, whose value at `y` is
written in `chartAt E y`: `z ↦ α(y) ∘ D(chartAt y ∘ e⁻¹)(z)` with `y = e⁻¹ z` (conventions §6).
Junk value `0` where `e⁻¹ z ∉ U`. Used with `e = chartAt E x` in `IsDolbeault` and `dbarSec`,
and with any atlas chart in F9.a. -/
def chartExpr {U : Opens X} (α : U → TotFibre E) (e : OpenPartialHomeomorph X E) (z : E) :
    TotFibre E :=
  if h : e.symm z ∈ U then TotFibre.pull (chartTrans E e (e.symm z) z) (α ⟨_, h⟩) else 0

/-- **F9. Dolbeault forms on `U`.** [B, §4], [A, §7.1]. `α : U → Λ^{0,•}(E)` is a (smooth)
form: for every `x ∈ U`, its expression in `chartAt E x` is real `C^∞` at `chartAt E x x`.
(Smoothness `∞`, not the analytic `ω`.) By F9.a the expression in every atlas chart is then
smooth. -/
def IsDolbeault {U : Opens X} (α : U → TotFibre E) : Prop :=
  ∀ x : U, ContDiffAt ℝ ∞ (chartExpr E α (chartAt E (x : X))) (chartAt E (x : X) x)

/-- **F3 on the total fibre.** For `f : E → Λ^{0,•}(E)`, `∂̄f(z)` degree by degree: the
component of degree `q + 1` is `∂̄` of the component of degree `q` (`dbar`, F3); components of
degree `> n` are `0` (`ofDeg`). Junk where `f` is not differentiable. -/
def dbarTot (f : E → TotFibre E) (z : E) : TotFibre E :=
  ∑ q : Fin (Module.finrank ℂ E + 1), TotFibre.ofDeg ((q : ℕ) + 1) (dbar (fun w ↦ f w q) z)

/-- **F9.b. `∂̄` of a form on `U`.** [B, §4], [A, §7.1]. `(∂̄α)(x)` is `∂̄` of the expression of
`α` in `φ = chartAt E x`, evaluated at `φ x` (conventions §6); it is written in `chartAt E x`,
as forms are. -/
def dbarSec {U : Opens X} (α : U → TotFibre E) (x : U) : TotFibre E :=
  dbarTot E (chartExpr E α (chartAt E (x : X))) (chartAt E (x : X) x)

/-- **F10.** `α` has values in degree `q`: every component of degree `≠ q` vanishes. For
`q < 0` or `q > n` only `α = 0` qualifies. -/
def IsOfDegree {U : Opens X} (q : ℤ) (α : U → TotFibre E) : Prop :=
  ∀ (y : U) (i : Fin (Module.finrank ℂ E + 1)), ((i : ℕ) : ℤ) ≠ q → α y i = 0

open Classical in
/-- **F10.** The degree-`q` part of `α`: keep the component of degree `q`, zero the others. -/
def projDeg {U : Opens X} (q : ℤ) (α : U → TotFibre E) : U → TotFibre E :=
  fun y i ↦ if ((i : ℕ) : ℤ) = q then α y i else 0

/-- **F9.** Restriction of a form on `U` to an open `V ≤ U`. -/
def restrictForm {U V : Opens X} (h : V ≤ U) (α : U → TotFibre E) : V → TotFibre E :=
  fun y ↦ α ⟨y, h y.2⟩

end Cohesive
