-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Comparison.CurvedPresheaf
import Cohesivemodules.Algebra.BaseChangeResAPI
import Mathlib.Algebra.Category.ModuleCat.Presheaf

set_option linter.style.header false

/-!
# Z3.m: sections of `α(M)` over `DgaSheafData` (copy of C1, part 1)

Blueprint item Z3.m (`blueprint/blueprint-tw.md` §2.4, D11; blueprint §11 v1.19). The section-level
data of C1 (`Comparison/AlphaDef.lean`, frozen, and the helpers `A0`, `𝒜X`, `r`, `R` of
`Comparison/SetupDef.lean`), word for word, with pre-resolving data `P` replaced by sheaf data
`S : DgaSheafData X` (no `c_eq_zero`), so that they apply to the curved data
`S.withCurvature h` and to cohesive modules over a curved algebra. None of these definitions uses
the curvature. For `S = P.toSheafData` every definition here is the frozen one by `rfl`
(`Comparison/SheafDataMap.lean`, bridges).

* `S.TotSec M h`: `Tot(M|V)` for `M` over `𝒜(U₀)`, `h : V ≤ U₀` (A9 base change);
* `S.deg0 M n h`, `S.sheafOfSec M n h`: its elements of total degree `n`, an `O(V)`-module;
* `S.totRes`, `S.sheafOfRes`: restriction; `S.sheafOfDV`: the operator `𝕏` of `M|V`;
* `S.sheafOfPre M n`: the presheaf `V ↦ α(M)^n(V)` of `O`-modules on `X`.

## Deviations
* As in C1: `α(M)^n(V)` is spelled through A9's base change.
* `sheafOfDV` is the operator `𝕏`, not a differential: for curved data `𝕏² = c·` (the twisted
  functor uses `𝕏 − h⁰_α·` on `U_α`, Z3.n).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace DgaSheafData

section Setup

variable (S : DgaSheafData X)

/-- **Z3.m** (copy of C0 `A0`). The sheaf of commutative rings `𝒜⁰`, `𝒜⁰(U) = ↥(𝒜_U 0)`. -/
abbrev A0 : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0} := ⟨S.D.pre0, S.isSheaf0⟩

/-- **Z3.m** (copy of C0 `𝒜X`). The global algebra `A = 𝒜(X)`, graded by `𝒜X` (with the
curvature of `S`). -/
abbrev 𝒜X : ℤ → Submodule ℂ (S.D.A ⊤) := S.D.𝒜 ⊤

/-- **Z3.m** (copy of C0 `r`). Restriction from `X` to `V`. -/
abbrev r (V : Opens X) : DgaHom S.𝒜X (S.D.𝒜 V) := S.D.res le_top

/-- **Z3.m** (copy of C0 `R`). The sheaf of rings `R = O` (`ringOf`, conventions §7). -/
abbrev R : RingSheaf X := ringOf S.O

end Setup

variable (S : DgaSheafData X) {U₀ : Opens X} (M : CohesiveModule (S.D.𝒜 U₀))

/-- **Z3.m** (copy of C1 `TotSec`). `Tot(M|V)`: the total module of the base change of `M` to
`V ≤ U₀` (A9). -/
abbrev TotSec {V : Opens X} (h : V ≤ U₀) : Type := (M.baseChange (S.D.res h)).T

/-- Degree-`0` elements of `𝒜(V)` preserve the total degree of `Tot(M|V)`. -/
theorem smul0_mem_totDeg {n : ℤ} {V : Opens X} {h : V ≤ U₀} (a : S.D.𝒜 V 0) {x : S.TotSec M h}
    (hx : x ∈ totDeg (S.D.𝒜 V) (M.baseChange (S.D.res h)).Q n) :
    a • x ∈ totDeg (S.D.𝒜 V) (M.baseChange (S.D.res h)).Q n := by
  have := smul_mem_totDeg (𝒜 := S.D.𝒜 V) (Q := (M.baseChange (S.D.res h)).Q) a.2 hx
  rwa [zero_add] at this

/-- **Z3.m** (copy of C1 `deg0`). The elements of total degree `n` of `Tot(M|V)`, as an
`𝒜⁰(V)`-submodule. -/
def deg0 (n : ℤ) {V : Opens X} (h : V ≤ U₀) : Submodule ↥(S.D.𝒜 V 0) (S.TotSec M h) where
  carrier := (totDeg (S.D.𝒜 V) (M.baseChange (S.D.res h)).Q n : Set (S.TotSec M h))
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a _ hx := S.smul0_mem_totDeg M a hx

/-- **Z3.m** (copy of C1 `sheafOfSec`). `α(M)^n(V)` as a type: the elements of total degree `n`
of `Tot(M|V)`. -/
def sheafOfSec (n : ℤ) {V : Opens X} (h : V ≤ U₀) : Type := ↥(S.deg0 M n h)

instance (n : ℤ) {V : Opens X} (h : V ≤ U₀) : AddCommGroup (S.sheafOfSec M n h) :=
  inferInstanceAs (AddCommGroup ↥(S.deg0 M n h))

/-- **Z3.m** (copy of C1). `O(V)` acts on `α(M)^n(V)` through `ρ_V : O(V) → 𝒜⁰(V)`. -/
instance (n : ℤ) {V : Opens X} (h : V ≤ U₀) : Module (S.O.obj.obj (op V)) (S.sheafOfSec M n h) :=
  Module.compHom ↥(S.deg0 M n h) (S.ρ V)

/-- The `O(V)`-action is `ρ_V` followed by the `𝒜⁰(V)`-action (rfl). -/
theorem sheafOfSec_smul_val {n : ℤ} {V : Opens X} {h : V ≤ U₀} (f : S.O.obj.obj (op V))
    (x : S.sheafOfSec M n h) :
    (show ↥(S.deg0 M n h) from f • x).1 = (S.ρ V f) • (show ↥(S.deg0 M n h) from x).1 :=
  rfl

/-- **Z3.m** (copy of C1 `totRes`). Restriction `Tot(M|V) → Tot(M|W)` for `W ≤ V ≤ U₀`:
`bcTotRes` along `res : 𝒜(V) → 𝒜(W)`. -/
def totRes {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) :
    S.TotSec M hV →+ S.TotSec M (hW.trans hV) :=
  bcTotRes (S.D.res hW) (S.D.res hV) (S.D.res (hW.trans hV)) (S.D.res_comp hV hW) M.Q

/-- `totRes` preserves the total degree. -/
theorem totRes_mem {n : ℤ} {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) {x : S.TotSec M hV}
    (hx : x ∈ totDeg (S.D.𝒜 V) (M.baseChange (S.D.res hV)).Q n) :
    S.totRes M hV hW x ∈ totDeg (S.D.𝒜 W) (M.baseChange (S.D.res (hW.trans hV))).Q n := by
  exact bcTotRes_mem (S.D.res hW) (S.D.res hV) (S.D.res (hW.trans hV)) (S.D.res_comp hV hW)
    M.Q hx

/-- `totRes` is semilinear over `res : 𝒜⁰(V) → 𝒜⁰(W)`. -/
theorem totRes_smul0 {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (a : S.D.𝒜 V 0)
    (x : S.TotSec M hV) :
    S.totRes M hV hW (a • x) = (S.D.res hW).f0 a • S.totRes M hV hW x :=
  bcTotRes_smul (S.D.res hW) (S.D.res hV) (S.D.res (hW.trans hV)) (S.D.res_comp hV hW)
    M.Q (a : S.D.A V) x

/-- `totRes` along `le_refl` is the identity. -/
theorem totRes_id {V : Opens X} (hV : V ≤ U₀) (x : S.TotSec M hV) :
    S.totRes M hV (le_refl V) x = x :=
  bcTotRes_id (S.D.res hV) M.Q (S.D.res (le_refl V)) (S.D.res_id V) (S.D.res_comp hV (le_refl V))
    x

/-- `totRes` is functorial. -/
theorem totRes_comp {V W Y : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (hY : Y ≤ W)
    (x : S.TotSec M hV) :
    S.totRes M (hW.trans hV) hY (S.totRes M hV hW x) = S.totRes M hV (hY.trans hW) x :=
  bcTotRes_comp (S.D.res hW) (S.D.res hV) (S.D.res (hW.trans hV)) (S.D.res_comp hV hW) M.Q
    (S.D.res hY) (S.D.res (hY.trans (hW.trans hV))) (S.D.res_comp (hW.trans hV) hY)
    (S.D.res (hY.trans hW)) (S.D.res_comp hV (hY.trans hW)) (S.D.res_comp hW hY) x

/-- **Z3.m** (copy of C1 `sheafOfRes`). Restriction `α(M)^n(V) → α(M)^n(W)` for `W ≤ V ≤ U₀`,
semilinear over `O(V) → O(W)`. -/
def sheafOfRes (n : ℤ) {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) :
    S.sheafOfSec M n hV →ₛₗ[(S.O.obj.map (homOfLE hW).op).hom] S.sheafOfSec M n (hW.trans hV) where
  toFun x := ⟨S.totRes M hV hW x.1, S.totRes_mem M hV hW x.2⟩
  map_add' x y := Subtype.ext (map_add (S.totRes M hV hW) x.1 y.1)
  map_smul' f x := Subtype.ext <| by
    show S.totRes M hV hW ((S.ρ V f) • x.1) = (S.ρ W _) • S.totRes M hV hW x.1
    rw [S.totRes_smul0, S.ρ_natural]

/-- `sheafOfRes` on the underlying element (rfl). -/
theorem sheafOfRes_val (n : ℤ) {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V)
    (x : S.sheafOfSec M n hV) :
    (S.sheafOfRes M n hV hW x).1 = S.totRes M hV hW x.1 := rfl

/-- `𝕏` of `M|V` is `O(V)`-linear (`d ∘ ρ_V = 0` and the Leibniz rule in degree `0`). -/
theorem X_smulO {V : Opens X} (h : V ≤ U₀) (f : S.O.obj.obj (op V)) (x : S.TotSec M h) :
    (M.baseChange (S.D.res h)).X ((S.ρ V f) • x) =
      (S.ρ V f) • (M.baseChange (S.D.res h)).X x := by
  have := (M.baseChange (S.D.res h)).leibniz (S.ρ V f).2 x
  rw [S.d_ρ, zero_smul, zero_add, Int.negOnePow_zero, one_smul] at this
  exact this

/-- **Z3.m** (copy of C1 `sheafOfDV`). The operator `α(M)^n(V) → α(M)^{n+1}(V)`: `𝕏` of `M|V`
(A9). ⚠ Not a differential for curved data (`𝕏² = c·`). -/
def sheafOfDV (n : ℤ) {V : Opens X} (h : V ≤ U₀) :
    S.sheafOfSec M n h →ₗ[S.O.obj.obj (op V)] S.sheafOfSec M (n + 1) h where
  toFun x := ⟨(M.baseChange (S.D.res h)).X x.1, (M.baseChange (S.D.res h)).X_mem x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (S.X_smulO M h f x.1)

/-- `sheafOfDV` on the underlying element (rfl). -/
theorem sheafOfDV_val (n : ℤ) {V : Opens X} (h : V ≤ U₀) (x : S.sheafOfSec M n h) :
    (S.sheafOfDV M n h x).1 = (M.baseChange (S.D.res h)).X x.1 := rfl

/-- `𝕏` commutes with restriction. -/
theorem X_totRes {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (x : S.TotSec M hV) :
    (M.baseChange (S.D.res (hW.trans hV))).X (S.totRes M hV hW x) =
      S.totRes M hV hW ((M.baseChange (S.D.res hV)).X x) :=
  bcTotRes_extend (S.D.res hW) (S.D.res hV) (S.D.res (hW.trans hV)) (S.D.res_comp hV hW)
    M.toQuasiCohesive x

/-- **Z3.m** (copy of C1 `sheafOfPre`). For `M` over `𝒜(X)`: `α(M)^n` as a presheaf of
`O`-modules on `X`, `V ↦ α(M)^n(V)` with restrictions `sheafOfRes`. -/
def sheafOfPre (M : CohesiveModule S.𝒜X) (n : ℤ) : PresheafOfModules.{0} S.R.obj where
  obj V := ModuleCat.of (S.O.obj.obj (op V.unop)) (S.sheafOfSec M n (le_top : V.unop ≤ ⊤))
  map {U V} f := ModuleCat.semilinearMapAddEquiv (S.R.obj.map f).hom
      (ModuleCat.of (S.O.obj.obj (op U.unop)) (S.sheafOfSec M n (le_top : U.unop ≤ ⊤)))
      (ModuleCat.of (S.O.obj.obj (op V.unop)) (S.sheafOfSec M n (le_top : V.unop ≤ ⊤)))
      (S.sheafOfRes M n le_top (leOfHom f.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact S.totRes_id M _ x.1
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact (S.totRes_comp M _ _ _ x.1).symm

end DgaSheafData

end Cohesive
