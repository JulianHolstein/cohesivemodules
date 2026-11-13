-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Comparison.TwistedFunctorAux
import Cohesivemodules.Comparison.TwistDatumDef
import Cohesivemodules.Sheaf.Twisted.SecHom
import Cohesivemodules.Sheaf.Twisted.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic

set_option linter.style.header false

/-!
# Z3.n: the twisted functor `J_T : Ho(P_{(𝒜(X), h)}) ⥤ D(X, ȟ)`

Blueprint item Z3.n (`blueprint/blueprint-tw.md` §2.4, §3 D.1–D.4;
 [A, Def 7.2.3, Rem 7.2.4, Lemma 7.2.17]).
For sheaf data `S`, a closed `h ∈ 𝒜²(X)` and a twist datum `T` for `h`, let `S_h` be the curved
data (`S.withCurvature h`). For a cohesive module `M` over `(𝒜(X), h)`:
* `twTerm T hh hd M n : TwMod S.O T.U T.ch`: components `α(M)^n|U_α` (the Z3.m copy of C1 over
  `S_h`), gluing maps `u_αβ ·` on sections (cocycle by `ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹`);
* `twDiff T hh hd M n`: on `U_α` the operator `𝕏 − h⁰_α ·` (`(𝕏 − h⁰_α)² = h − dh⁰_α = 0`;
  compatible with the gluing since `du_αβ = (h⁰_β − h⁰_α)u_αβ`);
* `twistedSheafOf T hh hd M`: the complex of twisted sheaves `J_T(M)`;
* `twMap`: `α(φ)` componentwise for closed `φ` of degree `0`; homotopies from `Hom^{-1}`;
* `twistedJK`, `twistedJ`: `J_T` into the homotopy category and the derived category of `TwMod`.

## Deviations
* The gluing maps are `u_αβ ·` for the units `u_αβ` of the twist datum,
 where [A, Def 7.2.3]
 writes `exp(h¹_αβ)` (blueprint-tw B correction 2, left modules, D2).
 The differentials
  `𝕏 − h⁰_α` agree with [A]'s `d_α = d|_{U_α} − h⁰_α`
  (blueprint-tw audit a7); [A]'s `+ h⁰_α` belongs only
  to the inverse (untwisting) construction.
* As for `J` (C1): `J_T` lands in the whole derived category; that it lands in `TwPerf` is Z3.p.
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] {S : DgaSheafData X} {h : S.D.A ⊤}

namespace TwistDatum

variable (T : TwistDatum S h) (hh : h ∈ S.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0)

section Complex

variable (M : CohesiveModule (S.withCurvature h hh hd).𝒜X)

/-- Z3.n: composition of restrictions on degree `0` elements. -/
private theorem res_f0_comp {V W W' : Opens X} (h₁ : W ≤ V) (h₂ : W' ≤ W) (a : ↥(S.D.𝒜 V 0)) :
    (S.D.res h₂).f0 ((S.D.res h₁).f0 a) = (S.D.res (h₂.trans h₁)).f0 a :=
  Subtype.ext (S.D.res_comp _ _ _)

/-- Z3.n: the twisted cocycle condition, restricted to `W ≤ U_α ∩ U_β ∩ U_γ`, on `𝒜⁰(W)`. -/
private theorem res_u_cocycle (α β γ : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (hγ : W ≤ T.U γ) :
    (S.D.res (le_inf hβ hγ)).f0 (T.u β γ) * (S.D.res (le_inf hα hβ)).f0 (T.u α β) =
      S.ρ W (unitRes S.O (le_inf (le_inf hα hβ) hγ) (T.ch α β γ) :
        S.O.obj.obj (op W)) * (S.D.res (le_inf hα hγ)).f0 (T.u α γ) := by
  have h0 := congrArg (S.D.res (le_inf (le_inf hα hβ) hγ)).f0 (T.ρ_ch α β γ)
  rw [S.ρ_natural, map_mul, map_mul, res_f0_comp, res_f0_comp, res_f0_comp] at h0
  have h1 : (S.D.res (le_inf hα hγ)).f0
      (((T.u α γ)⁻¹ : (↥(S.D.𝒜 (T.U α ⊓ T.U γ) 0))ˣ) : ↥(S.D.𝒜 (T.U α ⊓ T.U γ) 0)) *
      (S.D.res (le_inf hα hγ)).f0 (T.u α γ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h3 : S.ρ W (unitRes S.O (le_inf (le_inf hα hβ) hγ) (T.ch α β γ) :
      S.O.obj.obj (op W)) = _ := h0
  rw [h3]
  simp only [mul_assoc, h1, mul_one]

/-- Z3.n: `d u_αβ = (h⁰_β − h⁰_α) u_αβ`, restricted to `W ≤ U_α ∩ U_β`. -/
private theorem d_res_u (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) :
    GCDga.d (𝒜 := S.D.𝒜 W) (((S.D.res (le_inf hα hβ)).f0 (T.u α β) : ↥(S.D.𝒜 W 0)) : S.D.A W) =
      (S.D.res hβ (T.h0 β) - S.D.res hα (T.h0 α)) *
        (((S.D.res (le_inf hα hβ)).f0 (T.u α β) : ↥(S.D.𝒜 W 0)) : S.D.A W) := by
  have h1 := (S.D.res (le_inf hα hβ)).map_d
    (((T.u α β : (↥(S.D.𝒜 (T.U α ⊓ T.U β) 0))ˣ) : ↥(S.D.𝒜 (T.U α ⊓ T.U β) 0)) :
      S.D.A (T.U α ⊓ T.U β))
  rw [T.d_u α β] at h1
  rw [DgaHom.map_mul', map_sub, S.D.res_comp, S.D.res_comp] at h1
  exact h1.symm

/-- Z3.n: `gaugeDV` depends only on the value of `β`. -/
private theorem gaugeDV_congr (S' : DgaSheafData X) {U₀ : Opens X}
    (M : CohesiveModule (S'.D.𝒜 U₀)) (n : ℤ) {V : Opens X} (hV : V ≤ U₀) {β β' : S'.D.A V}
    (e : β = β') (hβ : β ∈ S'.D.𝒜 V 1) (hβ' : β' ∈ S'.D.𝒜 V 1) (x : S'.sheafOfSec M n hV) :
    S'.gaugeDV M n hV β hβ x = S'.gaugeDV M n hV β' hβ' x := by
  subst e
  rfl

/-- **Z3.n.** The component `α(M)^n|U_α` of `J_T(M)^n`, on the over-site `Over U_α`. -/
abbrev twComp (n : ℤ) (α : T.ι) : Mod ((ringOf S.O).over (T.U α)) :=
  (restr (ringOf S.O) (T.U α)).obj ((S.withCurvature h hh hd).sheafOfSh M n)

/-- **Z3.n.** [A, Def 7.2.3], blueprint-tw D.1, D.3. The twisted sheaf `J_T(M)^n`: components
`α(M)^n|U_α`, gluing maps multiplication by `u_αβ|W` on sections over `W ≤ U_α ∩ U_β`. -/
def twTerm (n : ℤ) : TwMod S.O T.U T.ch where
  M α := T.twComp hh hd M n α
  φ α β {W} hα hβ := ((S.withCurvature h hh hd).smul0L M n (le_top : W ≤ ⊤)
    ((S.D.res (le_inf hα hβ)).f0 (T.u α β))).toAddMonoidHom
  φ_smul := by
    intro α β W hα hβ r x
    exact ((S.withCurvature h hh hd).smul0L M n (le_top : W ≤ ⊤)
      ((S.D.res (le_inf hα hβ)).f0 (T.u α β))).map_smul r x
  φ_res := by
    intro α β W W' hα hβ h' x
    have hc : (S.D.res h').f0 ((S.D.res (le_inf hα hβ)).f0 (T.u α β)) =
        (S.D.res (le_inf (h'.trans hα) (h'.trans hβ))).f0 (T.u α β) :=
      Subtype.ext (S.D.res_comp _ _ _)
    exact (((S.withCurvature h hh hd).sheafOfRes_smul0L M n (le_top : W ≤ ⊤) h'
      ((S.D.res (le_inf hα hβ)).f0 (T.u α β)) x).trans
      (congrArg (fun u => (S.withCurvature h hh hd).smul0L M n
        (le_top : W' ≤ ⊤) u ((S.withCurvature h hh hd).sheafOfRes M n le_top h' x)) hc)).symm
  φ_self := by
    intro α W hα x
    have h1 : (S.D.res (le_inf hα hα)).f0 ((T.u α α : (↥(S.D.𝒜 (T.U α ⊓ T.U α) 0))ˣ) :
        ↥(S.D.𝒜 (T.U α ⊓ T.U α) 0)) = 1 := by
      rw [T.u_self α]
      exact map_one _
    exact (congrArg (fun u => (S.withCurvature h hh hd).smul0L M n (le_top : W ≤ ⊤) u x) h1).trans
      ((S.withCurvature h hh hd).smul0L_one M n le_top x)
  cocycle := by
    intro α β γ W hα hβ hγ x
    have e := T.res_u_cocycle α β γ hα hβ hγ
    exact ((((S.withCurvature h hh hd).smul0L_mul M n (le_top : W ≤ ⊤) _ _ x).symm).trans
      (congrArg (fun u => (S.withCurvature h hh hd).smul0L M n (le_top : W ≤ ⊤) u x) e)).trans
      (((S.withCurvature h hh hd).smul0L_mul M n (le_top : W ≤ ⊤) _ _ x).trans
        ((S.withCurvature h hh hd).smul_eq_smul0L M n le_top _ _).symm)

/-- Z3.n: the gluing maps of `J_T(M)^n` (rfl). -/
theorem twTerm_φ (n : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (x : (S.withCurvature h hh hd).sheafOfSec M n (le_top : W ≤ ⊤)) :
    (T.twTerm hh hd M n).φ α β hα hβ x = (S.withCurvature h hh hd).smul0L M n le_top
      ((S.D.res (le_inf hα hβ)).f0 (T.u α β)) x :=
  rfl

/-- **Z3.n.** Blueprint-tw D.2. The differential of `J_T(M)` on `U_α`: `𝕏 − h⁰_α|W` on sections
over `W ≤ U_α`. -/
def twDiffComp (n : ℤ) (α : T.ι) : T.twComp hh hd M n α ⟶ T.twComp hh hd M (n + 1) α :=
  homOfSec₀ (fun {W} hW => ((S.withCurvature h hh hd).gaugeDV M n (le_top : W ≤ ⊤)
      (S.D.res hW (T.h0 α)) ((S.D.res hW).map_mem (T.h0_mem α))).toAddMonoidHom)
    (fun {W} hW r x => ((S.withCurvature h hh hd).gaugeDV M n (le_top : W ≤ ⊤)
      (S.D.res hW (T.h0 α)) ((S.D.res hW).map_mem (T.h0_mem α))).map_smul r x)
    (fun {W W'} hW h' x => by
      have hc : S.D.res h' (S.D.res hW (T.h0 α)) = S.D.res (h'.trans hW) (T.h0 α) :=
        S.D.res_comp _ _ _
      exact (gaugeDV_congr (S.withCurvature h hh hd) M n _ hc.symm
        ((S.D.res (h'.trans hW)).map_mem (T.h0_mem α)) _ _).trans
        ((S.withCurvature h hh hd).sheafOfRes_gaugeDV M n (le_top : W ≤ ⊤) h'
        (S.D.res hW (T.h0 α)) ((S.D.res hW).map_mem (T.h0_mem α)) x).symm)

/-- Z3.n: `twDiffComp` on sections (rfl). -/
theorem twDiffComp_app (n : ℤ) (α : T.ι) {W : Opens X} (hW : W ≤ T.U α)
    (x : (S.withCurvature h hh hd).sheafOfSec M n (le_top : W ≤ ⊤)) :
    ((T.twDiffComp hh hd M n α).val.app (ovr hW)).hom x =
      (S.withCurvature h hh hd).gaugeDV M n le_top (S.D.res hW (T.h0 α))
        ((S.D.res hW).map_mem (T.h0_mem α)) x :=
  rfl

/-- Z3.n: `twDiffComp` squares to zero on sections (`d h⁰_α = h`, `gaugeDV_gaugeDV`). -/
private theorem twDiffComp_sq (n : ℤ) (α : T.ι) {W : Opens X} (hW : W ≤ T.U α)
    (x : (S.withCurvature h hh hd).sheafOfSec M n (le_top : W ≤ ⊤)) :
    ((T.twDiffComp hh hd M (n + 1) α).val.app (ovr hW)).hom
      (((T.twDiffComp hh hd M n α).val.app (ovr hW)).hom x) = 0 := by
  have hdβ : GCDga.d (𝒜 := S.D.𝒜 W) (S.D.res hW (T.h0 α)) =
      GCDga.c (𝒜 := (S.withCurvature h hh hd).D.𝒜 W) := by
    rw [← (S.D.res hW).map_d, T.d_h0 α]
    exact S.D.res_comp _ _ _
  exact (S.withCurvature h hh hd).gaugeDV_gaugeDV M n (le_top : W ≤ ⊤) (S.D.res hW (T.h0 α))
    ((S.D.res hW).map_mem (T.h0_mem α)) hdβ x

/-- **Z3.n.** Blueprint-tw D.2–D.3. The differential `J_T(M)^n ⟶ J_T(M)^{n+1}`: `𝕏 − h⁰_α` on
the component `α`; it commutes with the gluing (`du_αβ = (h⁰_β − h⁰_α)u_αβ`). -/
def twDiff (n : ℤ) : T.twTerm hh hd M n ⟶ T.twTerm hh hd M (n + 1) where
  f α := T.twDiffComp hh hd M n α
  comm := by
    intro α β W hα hβ x
    exact ((S.withCurvature h hh hd).gaugeDV_smul0L M n (le_top : W ≤ ⊤)
      ((S.D.res (le_inf hα hβ)).f0 (T.u α β)) (S.D.res hα (T.h0 α)) (S.D.res hβ (T.h0 β))
      ((S.D.res hα).map_mem (T.h0_mem α)) ((S.D.res hβ).map_mem (T.h0_mem β))
      (T.d_res_u α β hα hβ) x).symm

/-- **Z3.n.** [A, Def 7.2.3]. `d² = 0`: `(𝕏 − h⁰_α)² = h − dh⁰_α = 0` on `U_α`. -/
theorem twDiff_twDiff (n : ℤ) : T.twDiff hh hd M n ≫ T.twDiff hh hd M (n + 1) = 0 := by
  refine TwMod.hom_ext fun α => ?_
  change T.twDiffComp hh hd M n α ≫ T.twDiffComp hh hd M (n + 1) α = 0
  ext Y x
  exact T.twDiffComp_sq hh hd M n α (leOfHom Y.unop.hom) x

/-- **Z3.n.** [A, Def 7.2.3]. The complex of twisted sheaves `J_T(M)`, `J_T(M)^n = α(M)^n|U_α`
with differential `𝕏 − h⁰_α` and gluing `u_αβ`. -/
def twistedSheafOf : CochainComplex (TwMod S.O T.U T.ch) ℤ :=
  CochainComplex.of (T.twTerm hh hd M) (T.twDiff hh hd M) (T.twDiff_twDiff hh hd M)

/-- The terms of `J_T(M)` (rfl). -/
theorem twistedSheafOf_X (n : ℤ) : (T.twistedSheafOf hh hd M).X n = T.twTerm hh hd M n := rfl

end Complex

section Morphisms

variable {M N : CohesiveModule (S.withCurvature h hh hd).𝒜X}

/-- **Z3.n.** Blueprint-tw D.4. `α(φ)` in degree `n` on every component, for a closed `φ` of
degree `0`; it commutes with the gluing (`φ` is `𝒜⁰`-linear). -/
def twMapN (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) :
    T.twTerm hh hd M n ⟶ T.twTerm hh hd N n where
  f α := (restr (ringOf S.O) (T.U α)).map ((S.withCurvature h hh hd).sheafOfMapN φ n)
  comm := by
    intro α β W hα hβ x
    exact ((S.withCurvature h hh hd).sheafOfMapV_smul0L φ n (le_top : W ≤ ⊤)
      ((S.D.res (le_inf hα hβ)).f0 (T.u α β)) x).symm

/-- **Z3.n.** `J_T(φ) : J_T(M) ⟶ J_T(N)` for a closed `φ` of degree `0` (it commutes with
`𝕏 − h⁰_α`). -/
def twMap (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) :
    T.twistedSheafOf hh hd M ⟶ T.twistedSheafOf hh hd N where
  f n := T.twMapN hh hd φ n
  comm' := by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have e1 : (T.twistedSheafOf hh hd N).d i (i + 1) = T.twDiff hh hd N i :=
      CochainComplex.of_d _ _ _
    have e2 : (T.twistedSheafOf hh hd M).d i (i + 1) = T.twDiff hh hd M i :=
      CochainComplex.of_d _ _ _
    rw [e1, e2]
    refine TwMod.hom_ext fun α => ?_
    change (T.twMapN hh hd φ i).f α ≫ T.twDiffComp hh hd N i α =
      T.twDiffComp hh hd M i α ≫ (T.twMapN hh hd φ (i + 1)).f α
    ext Y x
    exact ((S.withCurvature h hh hd).sheafOfMapV_gaugeDV φ i (le_top : Y.unop.left ≤ ⊤)
      (S.D.res (leOfHom Y.unop.hom) (T.h0 α))
      ((S.D.res (leOfHom Y.unop.hom)).map_mem (T.h0_mem α)) x).symm

/-- **Z3.n.** The homotopy component `J_T(M)^i ⟶ J_T(N)^j` (`i + -1 = j`) given by
`h ∈ Hom^{-1}`, componentwise. -/
def twHMapN (k : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) (hij : i + -1 = j) :
    T.twTerm hh hd M i ⟶ T.twTerm hh hd N j where
  f α := (restr (ringOf S.O) (T.U α)).map ((S.withCurvature h hh hd).hMapN k i j hij)
  comm := by
    intro α β W hα hβ x
    exact ((S.withCurvature h hh hd).hMapV_smul0L k i j hij (le_top : W ≤ ⊤)
      ((S.D.res (le_inf hα hβ)).f0 (T.u α β)) x).symm

/-- **Z3.n.** The homotopy `J_T(M) ⟶ J_T(N)` of degree `-1` given by `k ∈ Hom^{-1}`. -/
def twHHom (k : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) :
    (T.twistedSheafOf hh hd M).X i ⟶ (T.twistedSheafOf hh hd N).X j :=
  if hij : i + -1 = j then T.twHMapN hh hd k i j hij else 0

/-- Z3.n: the homotopy formula on sections of `α(M)^{i+1}(W)`
(`bcHomL_gauge_homotopy`, `β = h⁰_α|W`). -/
private theorem twHomotopy_sec (a b : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (k : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (hab : δ _ _ (-1) k.1 = a.1 - b.1)
    (i : ℤ) (h1 : i + 1 + -1 = i) (h2 : i + 1 + 1 + -1 = i + 1) {W : Opens X} (β : S.D.A W)
    (hβ : β ∈ S.D.𝒜 W 1) (x : (S.withCurvature h hh hd).sheafOfSec M (i + 1) (le_top : W ≤ ⊤)) :
    (S.withCurvature h hh hd).sheafOfMapV a (i + 1) le_top x =
      (S.withCurvature h hh hd).hMapV k (i + 1 + 1) (i + 1) h2 le_top
        ((S.withCurvature h hh hd).gaugeDV M (i + 1) le_top β hβ x) +
      (S.withCurvature h hh hd).gaugeDV N i le_top β hβ
        ((S.withCurvature h hh hd).hMapV k (i + 1) i h1 le_top x) +
      (S.withCurvature h hh hd).sheafOfMapV b (i + 1) le_top x := by
  apply Subtype.ext
  exact (sub_eq_iff_eq_add.1
    ((S.withCurvature h hh hd).bcHomL_gauge_homotopy a b k hab le_top β hβ x.1))

/-- **Z3.n.** Blueprint-tw D.4. If `a − b = δk` for `k ∈ Hom^{-1}`, then `J_T(a)` and `J_T(b)` are
homotopic (`bcHomL_gauge_homotopy`). -/
theorem twMap_homotopic (a b : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (k : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (hab : δ _ _ (-1) k.1 = a.1 - b.1) :
    Nonempty (Homotopy (T.twMap hh hd a) (T.twMap hh hd b)) := by
  refine ⟨{ hom := T.twHHom hh hd k, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    have : ¬ (i + -1 = j) := by
      intro h'
      apply hij
      change j + 1 = i
      omega
    simp only [twHHom, this, ↓reduceDIte]
  · intro i'
    obtain ⟨i, rfl⟩ : ∃ i, i' = i + 1 := ⟨i' - 1, by omega⟩
    have e1 : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    have e2 : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    rw [dNext_eq _ e1, prevD_eq _ e2]
    have h1 : i + 1 + -1 = i := by omega
    have h2 : i + 1 + 1 + -1 = i + 1 := by omega
    have d1 : (T.twistedSheafOf hh hd M).d (i + 1) (i + 1 + 1) = T.twDiff hh hd M (i + 1) :=
      CochainComplex.of_d _ _ _
    have d2 : (T.twistedSheafOf hh hd N).d i (i + 1) = T.twDiff hh hd N i :=
      CochainComplex.of_d _ _ _
    rw [d1, d2]
    have k1 : T.twHHom hh hd k (i + 1 + 1) (i + 1) = T.twHMapN hh hd k _ _ h2 := by
      simp only [twHHom, h2, ↓reduceDIte]
      rfl
    have k2 : T.twHHom hh hd k (i + 1) i = T.twHMapN hh hd k _ _ h1 := by
      simp only [twHHom, h1, ↓reduceDIte]
      rfl
    rw [k1, k2]
    refine TwMod.hom_ext fun α => ?_
    ext Y x
    exact twHomotopy_sec hh hd a b k hab i h1 h2 (S.D.res (leOfHom Y.unop.hom) (T.h0 α))
      ((S.D.res (leOfHom Y.unop.hom)).map_mem (T.h0_mem α)) x

/-- `J_T` preserves identities. -/
theorem twMap_id (M : CohesiveModule (S.withCurvature h hh hd).𝒜X) :
    T.twMap hh hd (idZ0 M.toQuasiCohesive) = 𝟙 (T.twistedSheafOf hh hd M) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine TwMod.hom_ext fun α => ?_
  change (restr (ringOf S.O) (T.U α)).map
    ((S.withCurvature h hh hd).sheafOfMapN (idZ0 M.toQuasiCohesive) i) = 𝟙 _
  rw [(S.withCurvature h hh hd).sheafOfMapN_id]
  exact (restr (ringOf S.O) (T.U α)).map_id _

/-- `J_T` preserves composition. -/
theorem twMap_comp {L : CohesiveModule (S.withCurvature h hh hd).𝒜X}
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (ψ : Z0 N.toQuasiCohesive L.toQuasiCohesive) :
    T.twMap hh hd (compZ0 _ _ _ ψ φ) = T.twMap hh hd φ ≫ T.twMap hh hd ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine TwMod.hom_ext fun α => ?_
  change (restr (ringOf S.O) (T.U α)).map
    ((S.withCurvature h hh hd).sheafOfMapN (compZ0 _ _ _ ψ φ) i) =
      (restr (ringOf S.O) (T.U α)).map ((S.withCurvature h hh hd).sheafOfMapN φ i) ≫
        (restr (ringOf S.O) (T.U α)).map ((S.withCurvature h hh hd).sheafOfMapN ψ i)
  rw [(S.withCurvature h hh hd).sheafOfMapN_comp]
  exact (restr (ringOf S.O) (T.U α)).map_comp _ _

end Morphisms

/-- **Z3.n.** [A, Lemma 7.2.17], blueprint-tw D.4. `J_T` into the homotopy category of twisted
sheaves: `M ↦ J_T(M)`, `[φ] ↦ [J_T(φ)]` (well defined: coboundaries go to null-homotopic maps). -/
def twistedJK :
    HoP (S.withCurvature h hh hd).𝒜X ⥤ HomotopyCategory (TwMod S.O T.U T.ch) (ComplexShape.up ℤ)
    where
  obj M := (HomotopyCategory.quotient _ _).obj (T.twistedSheafOf hh hd M.as)
  map {M N} f := Quotient.liftOn' f
    (fun φ ↦ (HomotopyCategory.quotient _ _).map (T.twMap hh hd φ)) (by
      intro a b hab
      rw [Submodule.quotientRel_def] at hab
      obtain ⟨k, hk, hδ⟩ := hab
      obtain ⟨H⟩ := T.twMap_homotopic hh hd a b ⟨k, hk⟩ (by
        change δ _ _ (-1) k = a.1 - b.1
        exact hδ)
      exact HomotopyCategory.eq_of_homotopy _ _ H)
  map_id M := by
    change (HomotopyCategory.quotient _ _).map (T.twMap hh hd (idZ0 M.as.toQuasiCohesive)) = _
    rw [T.twMap_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    induction f using Submodule.Quotient.induction_on with
    | H z =>
    induction g using Submodule.Quotient.induction_on with
    | H w =>
    exact (congrArg (HomotopyCategory.quotient _ _).map (T.twMap_comp hh hd z w)).trans
      (CategoryTheory.Functor.map_comp _ _ _)

/-- **Z3.n. The twisted functor `J_T : Ho(P_{(𝒜(X), h)}) ⥤ D(X, ȟ)`,** `M ↦ J_T(M)`.
[A, Def 7.2.3, Lemma 7.2.17], [B, Thm 4.2.1]. The `HasDerivedCategory` instance is an argument, as
for `J` and `TwPerf`. -/
def twistedJ [HasDerivedCategory.{w} (TwMod S.O T.U T.ch)] :
    HoP (S.withCurvature h hh hd).𝒜X ⥤ DerivedCategory (TwMod S.O T.U T.ch) :=
  T.twistedJK hh hd ⋙ DerivedCategory.Qh

/-- `J_T` on objects (rfl). -/
theorem twistedJ_obj [HasDerivedCategory.{w} (TwMod S.O T.U T.ch)]
    (M : HoP (S.withCurvature h hh hd).𝒜X) :
    (T.twistedJ hh hd).obj M = DerivedCategory.Q.obj (T.twistedSheafOf hh hd M.as) := rfl

end TwistDatum

end Cohesive
