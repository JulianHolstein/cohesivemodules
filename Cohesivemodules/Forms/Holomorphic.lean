-- FROZEN (gate 3, 26 Oct 2026; F12 O_X and ρ, in the main statement). Do not edit without approval.
import Cohesivemodules.Forms.SheafDef
import Cohesivemodules.Forms.CauchyRiemann
import Mathlib.Geometry.Manifold.Sheaf.Smooth

set_option linter.style.header false

/-!
# F12: holomorphic functions and `ρ : O_X → 𝒜⁰`

Blueprint item F12 (§5), conventions §6 ("Holomorphic functions"). These definitions enter the
main statement; they are frozen at gate 3.

* `holSheaf E X`: `O_X := smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ, ℂ) X ℂ`, the complex `C^∞` (that is,
  holomorphic) functions, a sheaf of commutative rings on `X`.
* `holSec E f`: a section of `O_X` as a complex-`C^∞` function.
* `funForm E f`: a function `f : U → ℂ` as a form of degree `0` (`Λ^{0,0}(E; ℂ) ≅ ℂ`, F2.a).
* `dolbeaultRho E X : holSheaf E X ⟶ dolbeault0 E X`: `f ↦ f` as a form of degree `0`, the map
  `ρ` of C0. `dolbeaultRhoU E U`: the same on sections over `U`, as the ring map
  `O_X(U) →+* ↥(𝒜_U 0)` that A10 (`CohesiveModule.fromComplex`) takes.

The lemmas `isDolbeault_funForm` (F1, F8: holomorphic functions are real-smooth) and the
naturality of `ρ` are proved here because the definitions need them; the exactness statements
of F12 are in `Forms/Dolbeault.lean`.

## Deviations
* Holomorphic means complex `C^∞` (`ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞`), which is Mathlib's notion; no
  several-variable Cauchy theory is used (F8).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

variable (X) in
/-- **F12. Holomorphic functions** `O_X`. [B, §4], [A, §7.1]. The sheaf of complex-`C^∞`
`ℂ`-valued functions on `X`, `smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ, ℂ) X ℂ`; complex `C^∞` is
holomorphic. A sheaf of commutative rings on `Opens X` (converted to a `RingSheaf` by
`ringOf`). -/
def holSheaf : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0} :=
  smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ, ℂ) X ℂ

/-- **F12.** A section of `O_X` over `U` is a complex-`C^∞` function `U → ℂ` (by definition of
`smoothSheafCommRing`, `smoothSheaf.obj_eq`). -/
def holSec {U : Opens X} (f : (holSheaf E X).obj.obj (op U)) : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, ℂ), ℂ⟯ := f

/-- **F12.** A function `f : U → ℂ` as a form of degree `0`: `y ↦ f y` in
`Λ^{0,0}(E; ℂ) ≅ ℂ` (`form0Equiv`, F2.a), placed in degree `0` of the total fibre. -/
def funForm {U : Opens X} (f : U → ℂ) : U → TotFibre E :=
  fun y ↦ TotFibre.ofDeg 0 (form0Equiv E ℂ (f y))

/-- A constant `0`-form is the scalar multiple of `1` in the total fibre. -/
private theorem ofDeg_form0Equiv_eq_smul (c : ℂ) :
    TotFibre.ofDeg 0 (form0Equiv E ℂ c) = c • (1 : TotFibre E) := by
  have h : form0Equiv E ℂ c = c • form0Equiv E ℂ 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h, map_smul, ← TotFibre.one_eq]

/-- `funForm` as a scalar multiple of `1` pointwise. -/
private theorem funForm_apply_eq {U : Opens X} (f : U → ℂ) (y : U) :
    funForm E f y = f y • (1 : TotFibre E) :=
  ofDeg_form0Equiv_eq_smul E (f y)

/-- F12 with F1: a holomorphic function is a Dolbeault form (complex-smooth functions are
real-smooth in the charts; degree-`0` forms are unchanged by pullbacks). -/
theorem isDolbeault_funForm {U : Opens X} (f : C^∞⟮𝓘(ℂ, E), U; 𝓘(ℂ, ℂ), ℂ⟯) :
    IsDolbeault E (funForm E f) := by
  intro x
  classical
  set e := chartAt E (x : X) with he
  let f' : X → ℂ := fun y ↦ if h : y ∈ U then f ⟨y, h⟩ else 0
  have hf' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ f' (x : X) := by
    have h1 : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (fun y : U ↦ f' y) x := by
      have : (fun y : U ↦ f' y) = f := by
        funext y
        simp only [f', y.2, ↓reduceDIte]
      rw [this]
      exact f.contMDiff x
    exact contMDiffAt_subtype_iff.1 h1
  have hex : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e.symm (e x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (x := (x : X))).contMDiffAt
      (e.open_target.mem_nhds (mem_chart_target E (x : X)))
  have hsymm : e.symm (e x) = x := e.left_inv (mem_chart_source E (x : X))
  have hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (f' ∘ e.symm) (e x) := by
    refine ContMDiffAt.comp (e x) ?_ hex
    rw [hsymm]
    exact hf'
  have hg' : ContDiffAt ℝ ∞ (f' ∘ e.symm) (e x) := hg.contDiffAt.restrict_scalars ℝ
  have hev : ∀ᶠ z in nhds (e x), e.symm z ∈ U := by
    have hc : ContinuousAt e.symm (e x) := e.continuousAt_symm (mem_chart_target E (x : X))
    exact hc.eventually_mem (U.isOpen.mem_nhds (by rw [hsymm]; exact x.2))
  refine (hg'.smul (contDiffAt_const (c := (1 : TotFibre E)))).congr_of_eventuallyEq ?_
  filter_upwards [hev] with z hz
  simp only [chartExpr, hz, ↓reduceDIte, funForm_apply_eq, map_smul, TotFibre.pull_one]
  show _ = (if h : e.symm z ∈ U then f ⟨e.symm z, h⟩ else 0) • (1 : TotFibre E)
  simp only [hz, ↓reduceDIte]

/-- F12: `funForm` has degree `0`. -/
theorem isOfDegree_funForm {U : Opens X} (f : U → ℂ) : IsOfDegree E 0 (funForm E f) := by
  intro y i hi
  have h0 : (0 : ℕ) ≠ (i : ℕ) := by
    intro h
    apply hi
    rw [← h]
    rfl
  show (if h : 0 = (i : ℕ) then DolbeaultFibre.cast h (form0Equiv E ℂ (f y)) else 0) = 0
  simp only [h0, ↓reduceDIte]

/-- **F12.** `ρ_U : O_X(U) →+* 𝒜⁰(U) = ↥(𝒜_U 0)`, a holomorphic function as a form of degree
`0`. The ring map of C0 and A10 (`CohesiveModule.fromComplex`). -/
def dolbeaultRhoU (U : Opens X) :
    (holSheaf E X).obj.obj (op U) →+* ↥(dolbeaultGrade E U 0) where
  toFun f := ⟨⟨funForm E (holSec E f), isDolbeault_funForm E (holSec E f)⟩,
    isOfDegree_funForm E (holSec E f)⟩
  map_one' := by
    refine Subtype.ext (Subtype.ext (funext fun y ↦ ?_))
    show funForm E (holSec E 1) y = (1 : TotFibre E)
    rw [funForm_apply_eq]
    exact one_smul ℂ _
  map_mul' f g := by
    refine Subtype.ext (Subtype.ext (funext fun y ↦ ?_))
    show funForm E (holSec E (f * g)) y = funForm E (holSec E f) y * funForm E (holSec E g) y
    rw [funForm_apply_eq, funForm_apply_eq, funForm_apply_eq, smul_mul_smul_comm, one_mul]
    rfl
  map_zero' := by
    refine Subtype.ext (Subtype.ext (funext fun y ↦ ?_))
    show funForm E (holSec E 0) y = (0 : TotFibre E)
    rw [funForm_apply_eq]
    exact zero_smul ℂ _
  map_add' f g := by
    refine Subtype.ext (Subtype.ext (funext fun y ↦ ?_))
    show funForm E (holSec E (f + g)) y = funForm E (holSec E f) y + funForm E (holSec E g) y
    rw [funForm_apply_eq, funForm_apply_eq, funForm_apply_eq, ← add_smul]
    rfl

/-- F12: `dolbeaultRhoU` on the underlying forms (rfl). -/
theorem coe_dolbeaultRhoU (U : Opens X) (f : (holSheaf E X).obj.obj (op U)) :
    (((dolbeaultRhoU E U f : ↥(dolbeaultGrade E U 0)) : DolbeaultAlg E U) : U → TotFibre E) =
      funForm E (holSec E f) :=
  rfl

variable (X) in
/-- **F12. `ρ : O_X → 𝒜⁰`.** [B, §4], [A, §7.1]. The map of sheaves of commutative rings
`dolbeaultRhoU` on each open (natural: restriction is restriction of functions). -/
def dolbeaultRho : holSheaf E X ⟶ dolbeault0 E X :=
  ObjectProperty.homMk
    { app := fun U ↦ CommRingCat.ofHom (dolbeaultRhoU E U.unop)
      naturality := fun U V i ↦ by
        refine CommRingCat.hom_ext (RingHom.ext fun f ↦ Subtype.ext (Subtype.ext ?_))
        rfl }

/-- F12: the components of `dolbeaultRho` are `dolbeaultRhoU` (rfl). -/
theorem dolbeaultRho_app (U : Opens X) :
    (dolbeaultRho E X).hom.app (op U) = CommRingCat.ofHom (dolbeaultRhoU E U) :=
  rfl

end Cohesive
