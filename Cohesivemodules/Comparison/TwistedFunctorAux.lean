-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Comparison.SheafDataMap

set_option linter.style.header false

/-!
# Z3.n (sections): multiplication by `𝒜⁰` and the gauged operator `𝕏 − β·` on `α(M)^n(V)`

Blueprint item Z3.n (`blueprint/blueprint-tw.md` §2.4, §3 D.2–D.4). For sheaf data
`S : DgaSheafData X` (possibly curved) and a cohesive module `M` over `𝒜(U₀)`, on the sections
`α(M)^n(V)` (`V ≤ U₀`, the copies of Z3.m):
* `S.smul0L M n hV u`: multiplication by `u ∈ 𝒜⁰(V)` (the gluing maps `u_αβ·` of `J_T`, D.3);
* `S.gaugeDV M n hV β hβ`: the operator `𝕏 − β·` for `β ∈ 𝒜¹(V)` (the differential `𝕏 − h⁰_α·`
  of `J_T` on `U_α`, D.2);
* `(𝕏 − β)² = 0` if `dβ = c` (Leibniz, `β² = 0`;
[A, Def 7.2.3]);
`𝕏 − β′` and `𝕏 − β` are intertwined by `u` if `du = (β′ − β)u` (D.3);
both commute with restriction,
with `α(φ)` for  closed `φ` of degree `0`,
and `α(h)` for `h ∈ Hom^{-1}` gives a homotopy for `𝕏 − β` (D.4).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace DgaSheafData

variable (S : DgaSheafData X) {U₀ : Opens X}

section Ops

variable (M : CohesiveModule (S.D.𝒜 U₀))

/-- **Z3.n.** Multiplication by `u ∈ 𝒜⁰(V)` on `α(M)^n(V)`, `O(V)`-linear (`𝒜⁰(V)` is
commutative). -/
def smul0L (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (u : ↥(S.D.𝒜 V 0)) :
    S.sheafOfSec M n hV →ₗ[S.O.obj.obj (op V)] S.sheafOfSec M n hV where
  toFun x := (show ↥(S.deg0 M n hV) from u • (show ↥(S.deg0 M n hV) from x))
  map_add' x y := by
    exact smul_add u (show ↥(S.deg0 M n hV) from x) (show ↥(S.deg0 M n hV) from y)
  map_smul' f x := by
    show u • (S.ρ V f • (show ↥(S.deg0 M n hV) from x)) =
      S.ρ V f • (u • (show ↥(S.deg0 M n hV) from x))
    rw [smul_comm]

theorem smul0L_val (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (u : ↥(S.D.𝒜 V 0))
    (x : S.sheafOfSec M n hV) :
    (S.smul0L M n hV u x).1 = u • (show ↥(S.deg0 M n hV) from x).1 :=
  rfl

/-- Degree-one elements square to zero (`2` invertible; copy of the private `Gauge.lean` lemma). -/
private theorem sq_eq_zero_of_deg_one' {V : Opens X} {β : S.D.A V}
    (hβ : β ∈ S.D.𝒜 V 1) (h2 : IsUnit (2 : ℂ)) : β * β = 0 := by
  have h := GCDga.gcomm (𝒜 := S.D.𝒜 V) hβ hβ
  rw [show ((1 : ℤ) * 1).negOnePow = -1 by decide, Units.neg_smul, one_smul] at h
  have h' : (2 : ℂ) • (β * β) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  obtain ⟨u, hu⟩ := h2
  have : (↑u⁻¹ * 2 : ℂ) • (β * β) = 0 := by rw [mul_smul, h', smul_zero]
  rwa [← hu, Units.inv_mul, one_smul] at this

/-- `β ∈ 𝒜¹(V)` commutes with `u ∈ 𝒜⁰(V)` acting on `Tot(M|V)`. -/
private theorem beta_smul_comm {V : Opens X} (hV : V ≤ U₀) {β : S.D.A V}
    (hβ : β ∈ S.D.𝒜 V 1) (u : ↥(S.D.𝒜 V 0)) (x : S.TotSec M hV) :
    β • (u • x) = u • (β • x) := by
  show β • ((u : S.D.A V) • x) = (u : S.D.A V) • (β • x)
  rw [← mul_smul, ← mul_smul, GCDga.gcomm hβ u.2, mul_zero, Int.negOnePow_zero, one_smul]

/-- **Z3.n.** The gauged operator `𝕏 − β·` on `α(M)^n(V)` for `β ∈ 𝒜¹(V)`, `O(V)`-linear. -/
def gaugeDV (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (β : S.D.A V) (hβ : β ∈ S.D.𝒜 V 1) :
    S.sheafOfSec M n hV →ₗ[S.O.obj.obj (op V)] S.sheafOfSec M (n + 1) hV where
  toFun x := ⟨(M.baseChange (S.D.res hV)).X x.1 - β • x.1, by
    have h1 := (M.baseChange (S.D.res hV)).X_mem x.2
    have h2 := smul_mem_totDeg (𝒜 := S.D.𝒜 V) (Q := (M.baseChange (S.D.res hV)).Q) hβ x.2
    rw [add_comm 1 n] at h2
    exact sub_mem h1 h2⟩
  map_add' x y := by
    refine Subtype.ext ?_
    show (M.baseChange (S.D.res hV)).X (x.1 + y.1) - β • (x.1 + y.1) = _
    rw [map_add, smul_add]
    exact add_sub_add_comm _ _ _ _
  map_smul' f x := by
    refine Subtype.ext ?_
    show (M.baseChange (S.D.res hV)).X (S.ρ V f • x.1) - β • (S.ρ V f • x.1) =
      S.ρ V f • ((M.baseChange (S.D.res hV)).X x.1 - β • x.1)
    rw [S.X_smulO, S.beta_smul_comm M hV hβ, smul_sub]

theorem gaugeDV_val (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (β : S.D.A V) (hβ : β ∈ S.D.𝒜 V 1)
    (x : S.sheafOfSec M n hV) :
    (S.gaugeDV M n hV β hβ x).1 = (M.baseChange (S.D.res hV)).X x.1 - β • x.1 :=
  rfl

/-- Z3.n: multiplication by `1` is the identity. -/
theorem smul0L_one (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (x : S.sheafOfSec M n hV) :
    S.smul0L M n hV 1 x = x := by
  exact Subtype.ext (one_smul _ (show ↥(S.deg0 M n hV) from x).1)

/-- Z3.n: multiplication by a product. -/
theorem smul0L_mul (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (u v : ↥(S.D.𝒜 V 0))
    (x : S.sheafOfSec M n hV) :
    S.smul0L M n hV (u * v) x = S.smul0L M n hV u (S.smul0L M n hV v x) := by
  exact Subtype.ext (mul_smul u v (show ↥(S.deg0 M n hV) from x).1)

/-- Z3.n: the `O(V)`-action is multiplication by `ρ_V f` (rfl up to `Subtype.ext`). -/
theorem smul_eq_smul0L (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (f : S.O.obj.obj (op V))
    (x : S.sheafOfSec M n hV) : f • x = S.smul0L M n hV (S.ρ V f) x := by
  exact Subtype.ext rfl

/-- **Z3.n.** Multiplication commutes with restriction (along the restricted element). -/
theorem sheafOfRes_smul0L (n : ℤ) {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V)
    (u : ↥(S.D.𝒜 V 0)) (x : S.sheafOfSec M n hV) :
    S.sheafOfRes M n hV hW (S.smul0L M n hV u x) =
      S.smul0L M n (hW.trans hV) ((S.D.res hW).f0 u) (S.sheafOfRes M n hV hW x) := by
  exact Subtype.ext (S.totRes_smul0 M hV hW u x.1)

/-- `totRes` is semilinear over `res` for every `b ∈ 𝒜(V)` (not only degree `0`). -/
private theorem totRes_smul {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (b : S.D.A V)
    (x : S.TotSec M hV) :
    S.totRes M hV hW (b • x) = S.D.res hW b • S.totRes M hV hW x :=
  bcTotRes_smul (S.D.res hW) (S.D.res hV) (S.D.res (hW.trans hV)) (S.D.res_comp hV hW)
    M.Q b x

/-- **Z3.n.** `𝕏 − β·` commutes with restriction (along the restricted `β`). -/
theorem sheafOfRes_gaugeDV (n : ℤ) {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (β : S.D.A V)
    (hβ : β ∈ S.D.𝒜 V 1) (x : S.sheafOfSec M n hV) :
    S.sheafOfRes M (n + 1) hV hW (S.gaugeDV M n hV β hβ x) =
      S.gaugeDV M n (hW.trans hV) (S.D.res hW β) ((S.D.res hW).map_mem hβ)
        (S.sheafOfRes M n hV hW x) := by
  refine Subtype.ext ?_
  show S.totRes M hV hW ((M.baseChange (S.D.res hV)).X x.1 - β • x.1) =
    (M.baseChange (S.D.res (hW.trans hV))).X (S.totRes M hV hW x.1) -
      S.D.res hW β • S.totRes M hV hW x.1
  rw [map_sub, S.X_totRes, S.totRes_smul]

/-- **Z3.n.** [A, Def 7.2.3], blueprint-tw D.2. `(𝕏 − β)² = 0` if `dβ` is the curvature over
`V` (`(𝕏 − β)² = c − dβ + β²`, `β² = 0` by graded commutativity, `2` invertible in `ℂ`). -/
theorem gaugeDV_gaugeDV (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (β : S.D.A V) (hβ : β ∈ S.D.𝒜 V 1)
    (hdβ : GCDga.d (𝒜 := S.D.𝒜 V) β = GCDga.c (𝒜 := S.D.𝒜 V)) (x : S.sheafOfSec M n hV) :
    S.gaugeDV M (n + 1) hV β hβ (S.gaugeDV M n hV β hβ x) = 0 := by
  refine Subtype.ext ?_
  have h2 : IsUnit (2 : ℂ) := isUnit_iff_ne_zero.2 two_ne_zero
  have hsq : β • β • x.1 = 0 := by
    rw [← mul_smul, S.sq_eq_zero_of_deg_one' hβ h2, zero_smul]
  have hL := (M.baseChange (S.D.res hV)).leibniz hβ x.1
  have hF := (M.baseChange (S.D.res hV)).flat x.1
  rw [hdβ] at hL
  show (M.baseChange (S.D.res hV)).X ((M.baseChange (S.D.res hV)).X x.1 - β • x.1) -
    β • ((M.baseChange (S.D.res hV)).X x.1 - β • x.1) = 0
  rw [map_sub, hL, hF, smul_sub, hsq, Int.negOnePow_one, Units.neg_smul, one_smul]
  abel

/-- **Z3.n.** Blueprint-tw D.3. If `du = (β′ − β)·u` then `(𝕏 − β′)(u·x) = u·(𝕏 − β)x`
(Leibniz in degree `0`, and `u` commutes with `β`). -/
theorem gaugeDV_smul0L (n : ℤ) {V : Opens X} (hV : V ≤ U₀) (u : ↥(S.D.𝒜 V 0)) (β β' : S.D.A V)
    (hβ : β ∈ S.D.𝒜 V 1) (hβ' : β' ∈ S.D.𝒜 V 1)
    (hdu : GCDga.d (𝒜 := S.D.𝒜 V) (u : S.D.A V) = (β' - β) * (u : S.D.A V))
    (x : S.sheafOfSec M n hV) :
    S.gaugeDV M n hV β' hβ' (S.smul0L M n hV u x) =
      S.smul0L M (n + 1) hV u (S.gaugeDV M n hV β hβ x) := by
  refine Subtype.ext ?_
  have hL := (M.baseChange (S.D.res hV)).leibniz u.2 x.1
  rw [hdu, Int.negOnePow_zero, one_smul, mul_smul, sub_smul] at hL
  have c1 : (u : S.D.A V) • β • x.1 = β • (u : S.D.A V) • x.1 :=
    (S.beta_smul_comm M hV hβ u x.1).symm
  show (M.baseChange (S.D.res hV)).X ((u : S.D.A V) • x.1) - β' • ((u : S.D.A V) • x.1) =
    (u : S.D.A V) • ((M.baseChange (S.D.res hV)).X x.1 - β • x.1)
  rw [hL, smul_sub, c1]
  abel

end Ops

section Maps

variable {M N : CohesiveModule (S.D.𝒜 U₀)}

/-- **Z3.n.** `α(φ)` commutes with multiplication by `𝒜⁰(V)` (`φ` is `𝒜`-linear of degree `0`). -/
theorem sheafOfMapV_smul0L (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) {V : Opens X}
    (hV : V ≤ U₀) (u : ↥(S.D.𝒜 V 0)) (x : S.sheafOfSec M n hV) :
    S.sheafOfMapV φ n hV (S.smul0L M n hV u x) = S.smul0L N n hV u (S.sheafOfMapV φ n hV x) := by
  refine Subtype.ext ?_
  have := (bcHomL_mem (S.D.res hV) 0 (S.toHom0 φ)).2 u.2 x.1
  rw [zero_mul, Int.negOnePow_zero, one_smul] at this
  exact this

/-- **Z3.n.** Blueprint-tw D.4. `α(φ)` commutes with `𝕏 − β·` for a closed `φ` of degree `0`. -/
theorem sheafOfMapV_gaugeDV (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) {V : Opens X}
    (hV : V ≤ U₀) (β : S.D.A V) (hβ : β ∈ S.D.𝒜 V 1) (x : S.sheafOfSec M n hV) :
    S.sheafOfMapV φ (n + 1) hV (S.gaugeDV M n hV β hβ x) =
      S.gaugeDV N n hV β hβ (S.sheafOfMapV φ n hV x) := by
  refine Subtype.ext ?_
  have h1 := (bcHomL_mem (S.D.res hV) 0 (S.toHom0 φ)).2 hβ x.1
  rw [zero_mul, Int.negOnePow_zero, one_smul] at h1
  rw [sheafOfMapV_val, gaugeDV_val, gaugeDV_val, sheafOfMapV_val]
  exact (map_sub (bcHomL (S.D.res hV) 0 (S.toHom0 φ)) _ _).trans
    (congrArg₂ (· - ·) (S.bcHomL_X φ hV x.1) h1)

/-- **Z3.n.** `α(h)` for `h ∈ Hom^{-1}` commutes with multiplication by `𝒜⁰(V)`. -/
theorem hMapV_smul0L (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ)
    (hij : i + -1 = j) {V : Opens X} (hV : V ≤ U₀) (u : ↥(S.D.𝒜 V 0))
    (x : S.sheafOfSec M i hV) :
    S.hMapV h i j hij hV (S.smul0L M i hV u x) = S.smul0L N j hV u (S.hMapV h i j hij hV x) := by
  refine Subtype.ext ?_
  have := (bcHomL_mem (S.D.res hV) (-1) h).2 u.2 x.1
  rw [mul_zero, Int.negOnePow_zero, one_smul] at this
  exact this

/-- **Z3.n.** Blueprint-tw D.4. Homotopy formula for the gauged operators: if `a − b = δh`
(`h ∈ Hom^{-1}`), then `α(a) − α(b) = α(h)(𝕏 − β) + (𝕏 − β)α(h)` on `Tot(M|V)` (the `β`-terms
cancel: `h(βx) = −βh(x)`). -/
theorem bcHomL_gauge_homotopy (a b : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (hab : δ _ _ (-1) h.1 = a.1 - b.1)
    {V : Opens X} (hV : V ≤ U₀) (β : S.D.A V) (hβ : β ∈ S.D.𝒜 V 1) (x : S.TotSec M hV) :
    id (α := S.TotSec N hV) (bcHomL (S.D.res hV) 0 (S.toHom0 a) x) -
        id (α := S.TotSec N hV) (bcHomL (S.D.res hV) 0 (S.toHom0 b) x) =
      id (α := S.TotSec N hV)
          (bcHomL (S.D.res hV) (-1) h ((M.baseChange (S.D.res hV)).X x - β • x)) +
        ((N.baseChange (S.D.res hV)).X (bcHomL (S.D.res hV) (-1) h x) -
          β • id (α := S.TotSec N hV) (bcHomL (S.D.res hV) (-1) h x)) := by
  have hf := hty_formula (M₁ := M.toQuasiCohesive.baseChange (S.D.res hV))
    (M₂ := N.toQuasiCohesive.baseChange (S.D.res hV)) (bcHomL (S.D.res hV) (-1) h) _ _
    (S.bcHomL_homotopy a b h hab hV) x
  have h1 := (bcHomL_mem (S.D.res hV) (-1) h).2 hβ x
  rw [show ((-1 : ℤ) * 1).negOnePow = -1 by decide, Units.neg_smul, one_smul] at h1
  have e1 : id (α := S.TotSec N hV) (bcHomL (S.D.res hV) (-1) h
      ((M.baseChange (S.D.res hV)).X x - β • x)) =
      id (α := S.TotSec N hV) (bcHomL (S.D.res hV) (-1) h ((M.baseChange (S.D.res hV)).X x)) +
        β • id (α := S.TotSec N hV) (bcHomL (S.D.res hV) (-1) h x) :=
    (map_sub (bcHomL (S.D.res hV) (-1) h) _ _).trans
      ((congrArg (fun y => bcHomL (S.D.res hV) (-1) h ((M.baseChange (S.D.res hV)).X x) - y)
        h1).trans (sub_neg_eq_add _ _))
  have hf' : id (α := S.TotSec N hV) (bcHomL (S.D.res hV) 0 (S.toHom0 a) x) =
      id (α := S.TotSec N hV) (bcHomL (S.D.res hV) (-1) h ((M.baseChange (S.D.res hV)).X x)) +
        (N.baseChange (S.D.res hV)).X (bcHomL (S.D.res hV) (-1) h x) +
        id (α := S.TotSec N hV) (bcHomL (S.D.res hV) 0 (S.toHom0 b) x) := hf
  rw [e1, hf']
  abel

end Maps

end DgaSheafData

end Cohesive
