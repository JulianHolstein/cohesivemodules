-- FROZEN (gate 4, 29 Oct 2026; C1 sections of α(M), in the main statement). Do not edit.
import Cohesivemodules.Comparison.SetupDef
import Cohesivemodules.Algebra.BaseChangeResAPI
import Mathlib.Algebra.Category.ModuleCat.Presheaf

set_option linter.style.header false

/-!
# C1 (part 1): sections of `α(M)`, restriction and differential

Blueprint item C1 (§4), [B, §4.1] (the sheaves `ℰ_X`), [A, Def 7.2.3 at h = 0]. These
definitions enter the main statement through J (`Comparison/FunctorDef.lean`); they are frozen at
gate 4. The sheaf condition (C1.a) is in `Comparison/AlphaSheaf.lean`, the functor in
`Comparison/FunctorDef.lean`.

The section-level data are stated for a cohesive module `M = (Q, 𝕏)` over `𝒜(U₀)` for any open
`U₀` and opens `V ≤ U₀`; J uses `U₀ = X` (`⊤`). The same data over `U₀ = U′` give `α` on the
over-site of `U′` (C1.c, C2, C4; `Comparison/AlphaOver.lean`).
* `P.TotSec M h` (`h : V ≤ U₀`): the total module `Tot(M|V)` of the base change `M|V` of `M` along
  the restriction `res h : 𝒜(U₀) → 𝒜(V)` (A9);
* `P.deg0 M n h`: its elements of total degree `n`, an `𝒜⁰(V)`-submodule;
* `P.sheafOfSec M n h`: the same as a type, an `O(V)`-module through `ρ_V` (`Module.compHom`);
* `P.totRes M hV hW`: restriction `Tot(M|V) → Tot(M|W)` for `W ≤ V ≤ U₀`, the map `bcTotRes`
  (A9), `b ⊗ (β ⊗ q) ↦ res(b) ⊗ (res(β) ⊗ q)`; `P.sheafOfRes` its degree-`n` part, semilinear over
  `O(V) → O(W)`;
* `P.sheafOfDV M n h`: the differential `α(M)^n(V) → α(M)^{n+1}(V)`, the operator `𝕏` of `M|V`;
* `P.sheafOfPre M n`: for `U₀ = ⊤`, the presheaf of `O`-modules `V ↦ α(M)^n(V)` on `X`.

## Deviations
* `α(M)^n(V)` is the degree-`n` part of `𝒜(V) ⊗_{𝒜⁰(V)} ⨁_p (𝒜⁰(V) ⊗_{𝒜⁰(U₀)} Q^p)` (A9's base
  change), not literally `⊕_{p+q=n} 𝒜^q(V) ⊗_{𝒜⁰(U₀)} Q^p` as in the blueprint; the two are
  canonically isomorphic (cancel `𝒜⁰(V)`). This spelling reuses A9's differential and its
  functoriality on Hom complexes (`bcHomL`), so J on morphisms and homotopies needs no new
  construction, and `α(M)|U′` compares directly with the base change `M|U′` used in LL (H2).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) {U₀ : Opens X} (M : CohesiveModule (P.D.𝒜 U₀))

/-- **C1.** `Tot(M|V)`: the total module of the base change of `M` to `V ≤ U₀` (A9). -/
abbrev TotSec {V : Opens X} (h : V ≤ U₀) : Type := (M.baseChange (P.D.res h)).T

/-- Degree-`0` elements of `𝒜(V)` preserve the total degree of `Tot(M|V)`. -/
theorem smul0_mem_totDeg {n : ℤ} {V : Opens X} {h : V ≤ U₀} (a : P.D.𝒜 V 0) {x : P.TotSec M h}
    (hx : x ∈ totDeg (P.D.𝒜 V) (M.baseChange (P.D.res h)).Q n) :
    a • x ∈ totDeg (P.D.𝒜 V) (M.baseChange (P.D.res h)).Q n := by
  have := smul_mem_totDeg (𝒜 := P.D.𝒜 V) (Q := (M.baseChange (P.D.res h)).Q) a.2 hx
  rwa [zero_add] at this

/-- **C1.** The elements of total degree `n` of `Tot(M|V)`, as an `𝒜⁰(V)`-submodule (the
carrier of `totDeg`, which is a `ℂ`-submodule). -/
def deg0 (n : ℤ) {V : Opens X} (h : V ≤ U₀) : Submodule ↥(P.D.𝒜 V 0) (P.TotSec M h) where
  carrier := (totDeg (P.D.𝒜 V) (M.baseChange (P.D.res h)).Q n : Set (P.TotSec M h))
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a _ hx := P.smul0_mem_totDeg M a hx

/-- **C1.** `α(M)^n(V)` as a type: the elements of total degree `n` of `Tot(M|V)`. -/
def sheafOfSec (n : ℤ) {V : Opens X} (h : V ≤ U₀) : Type := ↥(P.deg0 M n h)

instance (n : ℤ) {V : Opens X} (h : V ≤ U₀) : AddCommGroup (P.sheafOfSec M n h) :=
  inferInstanceAs (AddCommGroup ↥(P.deg0 M n h))

/-- **C1.** `O(V)` acts on `α(M)^n(V)` through `ρ_V : O(V) → 𝒜⁰(V)`. -/
instance (n : ℤ) {V : Opens X} (h : V ≤ U₀) : Module (P.O.obj.obj (op V)) (P.sheafOfSec M n h) :=
  Module.compHom ↥(P.deg0 M n h) (P.ρ V)

/-- The `O(V)`-action is `ρ_V` followed by the `𝒜⁰(V)`-action (rfl). -/
theorem sheafOfSec_smul_val {n : ℤ} {V : Opens X} {h : V ≤ U₀} (f : P.O.obj.obj (op V))
    (x : P.sheafOfSec M n h) :
    (show ↥(P.deg0 M n h) from f • x).1 = (P.ρ V f) • (show ↥(P.deg0 M n h) from x).1 :=
  rfl

/-- **C1.** Restriction `Tot(M|V) → Tot(M|W)` for `W ≤ V ≤ U₀`: `bcTotRes` along
`res : 𝒜(V) → 𝒜(W)`, `b ⊗ (β ⊗ q) ↦ res(b) ⊗ (res(β) ⊗ q)`. -/
def totRes {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) :
    P.TotSec M hV →+ P.TotSec M (hW.trans hV) :=
  bcTotRes (P.D.res hW) (P.D.res hV) (P.D.res (hW.trans hV)) (P.D.res_comp hV hW) M.Q

/-- `totRes` preserves the total degree. -/
theorem totRes_mem {n : ℤ} {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) {x : P.TotSec M hV}
    (hx : x ∈ totDeg (P.D.𝒜 V) (M.baseChange (P.D.res hV)).Q n) :
    P.totRes M hV hW x ∈ totDeg (P.D.𝒜 W) (M.baseChange (P.D.res (hW.trans hV))).Q n := by
  exact bcTotRes_mem (P.D.res hW) (P.D.res hV) (P.D.res (hW.trans hV)) (P.D.res_comp hV hW)
    M.Q hx

/-- `totRes` is semilinear over `res : 𝒜⁰(V) → 𝒜⁰(W)`. -/
theorem totRes_smul0 {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (a : P.D.𝒜 V 0)
    (x : P.TotSec M hV) :
    P.totRes M hV hW (a • x) = (P.D.res hW).f0 a • P.totRes M hV hW x :=
  bcTotRes_smul (P.D.res hW) (P.D.res hV) (P.D.res (hW.trans hV)) (P.D.res_comp hV hW)
    M.Q (a : P.D.A V) x

/-- `totRes` along `le_refl` is the identity. -/
theorem totRes_id {V : Opens X} (hV : V ≤ U₀) (x : P.TotSec M hV) :
    P.totRes M hV (le_refl V) x = x :=
  bcTotRes_id (P.D.res hV) M.Q (P.D.res (le_refl V)) (P.D.res_id V) (P.D.res_comp hV (le_refl V))
    x

/-- `totRes` is functorial. -/
theorem totRes_comp {V W Y : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (hY : Y ≤ W)
    (x : P.TotSec M hV) :
    P.totRes M (hW.trans hV) hY (P.totRes M hV hW x) = P.totRes M hV (hY.trans hW) x :=
  bcTotRes_comp (P.D.res hW) (P.D.res hV) (P.D.res (hW.trans hV)) (P.D.res_comp hV hW) M.Q
    (P.D.res hY) (P.D.res (hY.trans (hW.trans hV))) (P.D.res_comp (hW.trans hV) hY)
    (P.D.res (hY.trans hW)) (P.D.res_comp hV (hY.trans hW)) (P.D.res_comp hW hY) x

/-- **C1.** Restriction `α(M)^n(V) → α(M)^n(W)` for `W ≤ V ≤ U₀`, semilinear over
`O(V) → O(W)`. -/
def sheafOfRes (n : ℤ) {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) :
    P.sheafOfSec M n hV →ₛₗ[(P.O.obj.map (homOfLE hW).op).hom] P.sheafOfSec M n (hW.trans hV) where
  toFun x := ⟨P.totRes M hV hW x.1, P.totRes_mem M hV hW x.2⟩
  map_add' x y := Subtype.ext (map_add (P.totRes M hV hW) x.1 y.1)
  map_smul' f x := Subtype.ext <| by
    show P.totRes M hV hW ((P.ρ V f) • x.1) = (P.ρ W _) • P.totRes M hV hW x.1
    rw [P.totRes_smul0, P.ρ_natural]

/-- `sheafOfRes` on the underlying element (rfl). -/
theorem sheafOfRes_val (n : ℤ) {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V)
    (x : P.sheafOfSec M n hV) :
    (P.sheafOfRes M n hV hW x).1 = P.totRes M hV hW x.1 := rfl

/-- `𝕏` of `M|V` is `O(V)`-linear (`d ∘ ρ_V = 0` and the Leibniz rule in degree `0`). -/
theorem X_smulO {V : Opens X} (h : V ≤ U₀) (f : P.O.obj.obj (op V)) (x : P.TotSec M h) :
    (M.baseChange (P.D.res h)).X ((P.ρ V f) • x) =
      (P.ρ V f) • (M.baseChange (P.D.res h)).X x := by
  have := (M.baseChange (P.D.res h)).leibniz (P.ρ V f).2 x
  rw [P.d_ρ, zero_smul, zero_add, Int.negOnePow_zero, one_smul] at this
  exact this

/-- **C1.** The differential `α(M)^n(V) → α(M)^{n+1}(V)`: the operator `𝕏` of `M|V` (A9). -/
def sheafOfDV (n : ℤ) {V : Opens X} (h : V ≤ U₀) :
    P.sheafOfSec M n h →ₗ[P.O.obj.obj (op V)] P.sheafOfSec M (n + 1) h where
  toFun x := ⟨(M.baseChange (P.D.res h)).X x.1, (M.baseChange (P.D.res h)).X_mem x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (P.X_smulO M h f x.1)

/-- `sheafOfDV` on the underlying element (rfl). -/
theorem sheafOfDV_val (n : ℤ) {V : Opens X} (h : V ≤ U₀) (x : P.sheafOfSec M n h) :
    (P.sheafOfDV M n h x).1 = (M.baseChange (P.D.res h)).X x.1 := rfl

/-- The differential commutes with restriction. -/
theorem X_totRes {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (x : P.TotSec M hV) :
    (M.baseChange (P.D.res (hW.trans hV))).X (P.totRes M hV hW x) =
      P.totRes M hV hW ((M.baseChange (P.D.res hV)).X x) :=
  bcTotRes_extend (P.D.res hW) (P.D.res hV) (P.D.res (hW.trans hV)) (P.D.res_comp hV hW)
    M.toQuasiCohesive x

/-- **C1.** For `M` over `𝒜(X)`: `α(M)^n` as a presheaf of `O`-modules on `X`,
`V ↦ α(M)^n(V)` with restrictions `sheafOfRes`. -/
def sheafOfPre (M : CohesiveModule P.𝒜X) (n : ℤ) : PresheafOfModules.{0} P.R.obj where
  obj V := ModuleCat.of (P.O.obj.obj (op V.unop)) (P.sheafOfSec M n (le_top : V.unop ≤ ⊤))
  map {U V} f := ModuleCat.semilinearMapAddEquiv (P.R.obj.map f).hom
      (ModuleCat.of (P.O.obj.obj (op U.unop)) (P.sheafOfSec M n (le_top : U.unop ≤ ⊤)))
      (ModuleCat.of (P.O.obj.obj (op V.unop)) (P.sheafOfSec M n (le_top : V.unop ≤ ⊤)))
      (P.sheafOfRes M n le_top (leOfHom f.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact P.totRes_id M _ x.1
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact (P.totRes_comp M _ _ _ x.1).symm

end PreResolvingData

end Cohesive
