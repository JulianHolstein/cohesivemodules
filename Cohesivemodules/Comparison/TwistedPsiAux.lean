import Cohesivemodules.Comparison.CurvedHomSheaf
import Cohesivemodules.Comparison.TwistedFunctorAux
import Cohesivemodules.Algebra.BaseChangeExt
import Cohesivemodules.Comparison.FullyFaithfulAux

set_option linter.style.header false

/-!
# Z3.s: the section maps of C4's Ψ over DgaSheafData

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F′ (i)). C4's section maps
(`Comparison/FullyFaithful.lean`: `homAt`, `ΨW`, `ΨW_homδ`) word for word over
`S : DgaSheafData X`, so that they apply to the curved data `S.withCurvature h`; plus `ΨW_smul0L`
(degree-`0` scalars commute with `Ψ(χ)`) and `ΨW_homδ_gauge` (`Ψ` intertwines `δ` with the gauged
operators `𝕏 − β`, `β` of degree `1`: the `β`-terms cancel since `χ(β·y) = (-1)^n β·χ(y)`), used
by the twisted `Ψ^tw` (Z3.s).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X]

namespace DgaSheafData

variable (S : DgaSheafData X)

variable (M₁ M₂ : CohesiveModule S.𝒜X)

/-- Z3.s (copy of C4 `mem_homAlong_iff`): `ℋ^n(V)` membership is `HomAlong` membership along
`res_V` (the same condition). -/
theorem mem_homAlong_iff (n : ℤ) {V : Opens X} (h : V ≤ ⊤)
    (χ : M₁.T →ₗ[ℂ] S.TotSec M₂ h) :
    χ ∈ S.homAlong M₁ M₂ n h ↔
      χ ∈ HomAlong (S.D.res h) M₁.toQuasiCohesive M₂.toQuasiCohesive n :=
  Iff.rfl

/-- Z3.s (copy of C4 `homAt`): a section `χ ∈ ℋ^n(V)` restricted to `W ≤ V`, as a map along
`res_W`. -/
def homAt (n : ℤ) {V W : Opens X} (hW : W ≤ V)
    (χ : S.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) :
    HomAlong (S.D.res (le_top : W ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n :=
  ⟨(S.homRes M₁ M₂ n le_top hW χ).1,
    (S.mem_homAlong_iff M₁ M₂ n _ _).1 (S.homRes M₁ M₂ n le_top hW χ).2⟩

/-- Z3.s (copy of C4 `extAlong_mem_totDeg`): `extAlong` maps degree `p` to degree `q` for a
triplet `p + n = q`. -/
theorem extAlong_mem_totDeg (n : ℤ) (T : Triplet n) {W : Opens X}
    (χ : HomAlong (S.D.res (le_top : W ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n)
    {x : S.TotSec M₁ (le_top : W ≤ ⊤)}
    (hx : x ∈ totDeg (S.D.𝒜 W) (M₁.baseChange (S.D.res le_top)).Q T.p) :
    extAlong χ x ∈ totDeg (S.D.𝒜 W) (M₂.baseChange (S.D.res le_top)).Q T.q := by
  have := (extAlong_mem χ).1 hx
  rwa [T.hpq] at this

/-- Z3.s (copy of C4 `extAlong_smulO`): `extAlong` commutes with the `O(W)`-action (degree-`0`
scalars). -/
theorem extAlong_smulO (n : ℤ) {W : Opens X}
    (χ : HomAlong (S.D.res (le_top : W ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n)
    (f : S.O.obj.obj (op W)) (x : S.TotSec M₁ (le_top : W ≤ ⊤)) :
    extAlong χ ((S.ρ W f) • x) = (S.ρ W f) • extAlong χ x := by
  have h := (extAlong_mem χ).2 (S.ρ W f).2 x
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  exact h

/-- Z3.s (copy of C4 `ΨW`): the component of `Ψ(χ)` on `W ≤ V`, from degree `p` to degree
`q = p + n`. -/
def ΨW (n : ℤ) (T : Triplet n) {V W : Opens X} (hW : W ≤ V)
    (χ : S.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) :
    S.sheafOfSec M₁ T.p (le_top : W ≤ ⊤) →ₗ[S.O.obj.obj (op W)]
      S.sheafOfSec M₂ T.q (le_top : W ≤ ⊤) where
  toFun x := ⟨extAlong (S.homAt M₁ M₂ n hW χ) x.1,
    S.extAlong_mem_totDeg M₁ M₂ n T (S.homAt M₁ M₂ n hW χ) x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (S.extAlong_smulO M₁ M₂ n (S.homAt M₁ M₂ n hW χ) f x.1)

/-- Z3.s (copy of C4 `ΨW_homδ`): `ΨW` intertwines `δ`: for `T : Triplet (n + 1)`,
`Ψ(δχ)(x) = 𝕏(Ψ(χ)_{p,p+n}(x)) + (-1)^{n+1} Ψ(χ)_{p+1,q}(𝕏 x)`. -/
theorem ΨW_homδ (n : ℤ) (T : Triplet (n + 1)) {V W : Opens X} (hW : W ≤ V)
    (χ : S.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) (x : S.sheafOfSec M₁ T.p (le_top : W ≤ ⊤)) :
    (S.ΨW M₁ M₂ (n + 1) T hW (S.homδV M₁ M₂ n le_top χ) x).1 =
      (M₂.baseChange (S.D.res (le_top : W ≤ ⊤))).X
          (S.ΨW M₁ M₂ n ⟨T.p, T.p + n, rfl⟩ hW χ x).1 +
        (n + 1).negOnePow •
          (S.ΨW M₁ M₂ n ⟨T.p + 1, T.q, by have := T.hpq; lia⟩ hW χ
            (S.sheafOfDV M₁ T.p le_top x)).1 := by
  have hX : ∀ y : M₁.T, (S.homAt M₁ M₂ (n + 1) hW (S.homδV M₁ M₂ n le_top χ)).1 y =
      ((M₂.toQuasiCohesive.baseChange (S.D.res (le_top : W ≤ ⊤))).X ∘ₗ
          (S.homAt M₁ M₂ n hW χ).1 -
        n.negOnePow • ((S.homAt M₁ M₂ n hW χ).1 ∘ₗ M₁.X)) y := by
    intro y
    refine (map_sub (S.totRes M₂ (le_top : V ≤ ⊤) hW) _ _).trans
      (congrArg₂ (· - ·) (S.X_totRes M₂ le_top hW _).symm ?_)
    change S.totRes M₂ (le_top : V ≤ ⊤) hW (n.negOnePow • χ.1 (M₁.X y)) =
      n.negOnePow • S.totRes M₂ (le_top : V ≤ ⊤) hW (χ.1 (M₁.X y))
    rw [Units.smul_def, Units.smul_def, map_zsmul]
  have h := extAlong_δ (S.homAt M₁ M₂ n hW χ) (S.homAt M₁ M₂ (n + 1) hW (S.homδV M₁ M₂ n le_top χ))
    (fun y => hX y)
  change extAlong (S.homAt M₁ M₂ (n + 1) hW (S.homδV M₁ M₂ n le_top χ)) x.1 = _
  rw [h, δ_eq_mathlib]
  rfl

/-- Z3.s: `Ψ(χ)` commutes with multiplication by a degree-`0` element `u` (`smul0L`). -/
theorem ΨW_smul0L (n : ℤ) (T : Triplet n) {V W : Opens X} (hW : W ≤ V)
    (χ : S.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) (u : ↥(S.D.𝒜 W 0))
    (x : S.sheafOfSec M₁ T.p (le_top : W ≤ ⊤)) :
    S.ΨW M₁ M₂ n T hW χ (S.smul0L M₁ T.p le_top u x) =
      S.smul0L M₂ T.q le_top u (S.ΨW M₁ M₂ n T hW χ x) := by
  refine Subtype.ext ?_
  have h := (extAlong_mem (S.homAt M₁ M₂ n hW χ)).2 u.2 x.1
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  exact h

/-- Sign bookkeeping for `ΨW_homδ_gauge`: the `β`-terms cancel when `c = -d` for signs `c, d`. -/
private theorem gauge_aux {G : Type*} [AddCommGroup G] (a b z : G) (c d : ℤˣ) (hcd : c = -d) :
    a + c • b = (a - z) + c • (b - d • z) := by
  rcases Int.units_eq_one_or d with rfl | rfl <;> subst hcd <;>
    simp only [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul, smul_sub,
      neg_neg, sub_neg_eq_add] <;> abel

/-- Z3.s: `Ψ` intertwines `δ` with the gauged operators `𝕏 − β·` (`gaugeDV`), `β` of degree `1`:
for `T : Triplet (n + 1)`,
`Ψ(δχ)(x) = (𝕏 − β)(Ψ(χ)_{p,p+n}(x)) + (-1)^{n+1} Ψ(χ)_{p+1,q}((𝕏 − β) x)`
(the `β`-terms cancel: `χ(β·y) = (-1)ⁿ β·χ(y)`). -/
theorem ΨW_homδ_gauge (n : ℤ) (T : Triplet (n + 1)) {V W : Opens X} (hW : W ≤ V)
    (χ : S.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) (β : S.D.A W) (hβ : β ∈ S.D.𝒜 W 1)
    (x : S.sheafOfSec M₁ T.p (le_top : W ≤ ⊤)) :
    (S.ΨW M₁ M₂ (n + 1) T hW (S.homδV M₁ M₂ n le_top χ) x).1 =
      (S.gaugeDV M₂ (T.p + n) le_top β hβ (S.ΨW M₁ M₂ n ⟨T.p, T.p + n, rfl⟩ hW χ x)).1 +
        (n + 1).negOnePow • (S.ΨW M₁ M₂ n ⟨T.p + 1, T.q, by have := T.hpq; lia⟩ hW χ
          (S.gaugeDV M₁ T.p le_top β hβ x)).1 := by
  rw [S.ΨW_homδ M₁ M₂ n T hW χ x]
  have h := (extAlong_mem (S.homAt M₁ M₂ n hW χ)).2 hβ x.1
  have e2 : extAlong (S.homAt M₁ M₂ n hW χ) (S.gaugeDV M₁ T.p le_top β hβ x).1 =
      extAlong (S.homAt M₁ M₂ n hW χ) ((M₁.baseChange (S.D.res le_top)).X x.1) -
        (n * 1).negOnePow • β • extAlong (S.homAt M₁ M₂ n hW χ) x.1 := by
    change extAlong (S.homAt M₁ M₂ n hW χ) ((M₁.baseChange (S.D.res le_top)).X x.1 - β • x.1) = _
    exact (map_sub (extAlong (S.homAt M₁ M₂ n hW χ)) _ _).trans (congrArg _ h)
  have e1 := S.gaugeDV_val M₂ (T.p + n) le_top β hβ (S.ΨW M₁ M₂ n ⟨T.p, T.p + n, rfl⟩ hW χ x)
  refine Eq.trans ?_ (congrArg₂ (· + ·) e1.symm (congrArg ((n + 1).negOnePow • ·) e2.symm))
  exact gauge_aux (G := S.TotSec M₂ le_top) _
    (extAlong (S.homAt M₁ M₂ n hW χ) ((M₁.baseChange (S.D.res le_top)).X x.1))
    (β • extAlong (S.homAt M₁ M₂ n hW χ) x.1) _ _ (by rw [mul_one, Int.negOnePow_succ])
