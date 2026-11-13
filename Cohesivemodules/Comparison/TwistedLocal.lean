import Cohesivemodules.Comparison.TwistedFunctorDef
import Cohesivemodules.Comparison.AlphaOver
import Cohesivemodules.Comparison.AlphaOverAux
import Cohesivemodules.Algebra.Gauge

set_option linter.style.header false

/-!
# Z3.o: local identification of `J_T(M)` on `U_α` (blueprint-tw D.6)

Blueprint item Z3.o (`blueprint/blueprint-tw.md` §3 D.6; prototype P23). For pre-resolving data `P`
(flat), a closed `h ∈ 𝒜²(X)`, a twist datum `T` for `h` over `P` and a cohesive module `M` over
`(𝒜(X), h)`:
* `curvedResM`: the restriction `M|U_α` (A9 base change along the curved restriction), a cohesive
  module over `(𝒜(U_α), h|U_α)`;
* `gaugedRes`: the flat cohesive module `gauge_{h⁰_α}(M|U_α)` over `𝒜(U_α)` (Z3.b,
  `h|U_α = 0 + dh⁰_α`);
* `twCmp`: A9's comparison `Tot(M|V) → Tot((M|U_α)|V) = Tot(gauge_{h⁰_α}(M|U_α)|V)` (`cmpTot`; the
  gauge does not change the generators); it intertwines `𝕏 − h⁰_α|V` with the operator of the
  gauged module (`twCmp_X`);
* `twLocalIso`: the component complex `J_T(M)_α` on `Over U_α` is isomorphic to `α_{U_α}` (C1.c,
  `sheafOfOver`) of `gaugedRes`.
For the Dolbeault data, `gaugedRes` is `gaugedRestrict` (Z3.e), see
`Comparison/TwistedPerfect.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] (P : PreResolvingData X) {h : P.D.A ⊤}
  (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)

/-- Z3.o: `h|U_α = c + dh⁰_α` for the flat instance over `U_α` (`c = 0`, field `d_h0`). -/
theorem twistDatum_hcβ (α : T.ι) :
    P.D.res (le_top : T.U α ≤ ⊤) h =
      GCDga.c (𝒜 := P.D.𝒜 (T.U α)) + GCDga.d (𝒜 := P.D.𝒜 (T.U α)) (T.h0 α) := by
  rw [P.c_eq_zero (T.U α), zero_add]
  exact (T.d_h0 α).symm

variable (α : T.ι) (M : CohesiveModule (P.toSheafData.withCurvature h hh hd).𝒜X)

/-- **Z3.o.** The restriction `M|U_α` of `M` along the curved restriction
`(𝒜(X), h) → (𝒜(U_α), h|U_α)` (A9), a cohesive module over the curved instance on `𝒜(U_α)`. -/
abbrev curvedResM :
    @CohesiveModule ℂ _ (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _
      ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α)) :=
  @CohesiveModule.baseChange ℂ _ _ _ _ (P.toSheafData.withCurvature h hh hd).𝒜X _ _
    (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _ ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α))
    ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) M

/-- **Z3.o.** [A, §7.2 proofs of Lemma 7.2.17 and Prop 7.2.19], blueprint-tw D.6. The flat
cohesive module `gauge_{h⁰_α}(M|U_α)` over `𝒜(U_α)` (`CohesiveModule.gauge`, Z3.b). -/
def gaugedRes : CohesiveModule (P.D.𝒜 (T.U α)) :=
  CohesiveModule.gauge (i := P.D.dga (T.U α)) (c' := P.D.res le_top h)
    (hc := (P.D.res le_top).map_mem hh)
    (hd := by rw [← (P.D.res le_top).map_d, hd]; exact map_zero _)
    (T.h0 α) (T.h0_mem α) (twistDatum_hcβ P T α) (isUnit_of_invertible 2)
    (curvedResM P T hh hd α M)

/-- Z3.o: `res_V = res_{V ≤ U_α} ∘ res_{U_α}` for the curved data, as dga maps. -/
theorem curved_res_comp_eq {V : Opens X} (hV : V ≤ T.U α) :
    ((P.toSheafData.withCurvature h hh hd).D.res hV).comp
        ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)) =
      (P.toSheafData.withCurvature h hh hd).D.res (le_top : V ≤ ⊤) :=
  dgaHom_ext' fun a => DgaPresheaf.res_comp _ le_top hV a

/-- **Z3.o.** A9's comparison `Tot(M|V) → Tot(gauge_{h⁰_α}(M|U_α)|V)` for `V ≤ U_α` (`cmpTot`
along `res_V = res_{V ≤ U_α} ∘ res_{U_α}`). -/
def twCmp {V : Opens X} (hV : V ≤ T.U α) :
    (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤) →+
      P.TotSec (gaugedRes P T hh hd α M) hV :=
  cmpTot ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res hV) _ (curved_res_comp_eq P T hh hd α hV)
    M.toQuasiCohesive

/-- **Z3.o.** The inverse comparison (`cmpTotInv`). -/
def twCmpInv {V : Opens X} (hV : V ≤ T.U α) :
    P.TotSec (gaugedRes P T hh hd α M) hV →+
      (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤) :=
  cmpTotInv ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res hV) _ (curved_res_comp_eq P T hh hd α hV)
    M.toQuasiCohesive

theorem twCmpInv_twCmp {V : Opens X} (hV : V ≤ T.U α)
    (x : (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤)) :
    twCmpInv P T hh hd α M hV (twCmp P T hh hd α M hV x) = x :=
  cmpTotInv_cmpTot _ _ _ _ _ x

theorem twCmp_twCmpInv {V : Opens X} (hV : V ≤ T.U α) (y : P.TotSec (gaugedRes P T hh hd α M) hV) :
    twCmp P T hh hd α M hV (twCmpInv P T hh hd α M hV y) = y :=
  cmpTot_cmpTotInv _ _ _ (curved_res_comp_eq P T hh hd α hV) M.toQuasiCohesive y

/-- `twCmp` preserves the total degree. -/
theorem twCmp_mem {n : ℤ} {V : Opens X} (hV : V ≤ T.U α)
    {x : (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤)}
    (hx : x ∈ (P.toSheafData.withCurvature h hh hd).deg0 M n (le_top : V ≤ ⊤)) :
    twCmp P T hh hd α M hV x ∈ P.deg0 (gaugedRes P T hh hd α M) n hV :=
  by
  have := cmpTot_mem ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res hV) _ (curved_res_comp_eq P T hh hd α hV)
    M.toQuasiCohesive hx
  exact this

/-- `twCmpInv` preserves the total degree. -/
theorem twCmpInv_mem {n : ℤ} {V : Opens X} (hV : V ≤ T.U α)
    {y : P.TotSec (gaugedRes P T hh hd α M) hV} (hy : y ∈ P.deg0 (gaugedRes P T hh hd α M) n hV) :
    twCmpInv P T hh hd α M hV y ∈ (P.toSheafData.withCurvature h hh hd).deg0 M n
      (le_top : V ≤ ⊤) :=
  cmpTotInv_mem _ _ _ (curved_res_comp_eq P T hh hd α hV) M.toQuasiCohesive hy

/-- `twCmp` is `𝒜(V)`-linear. -/
theorem twCmp_smul {V : Opens X} (hV : V ≤ T.U α) (a : (P.toSheafData.withCurvature h hh hd).D.A V)
    (x : (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤)) :
    twCmp P T hh hd α M hV (a • x) = (show P.D.A V from a) • twCmp P T hh hd α M hV x :=
  cmpTot_smul _ _ _ _ _ _ x

/-- `σ(a)·β = β·a` for `β ∈ A¹`. -/
private theorem sigma_mul_deg_one {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {β : A} (hβ : β ∈ 𝒜 1) (a : A) :
    GCDga.sigma 𝒜 a * β = β * a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, add_mul, hx, hy, mul_add]
  | homogeneous x =>
    rw [GCDga.sigma_of_mem 𝒜 x.2, smul_mul_assoc, GCDga.gcomm x.2 hβ, smul_smul, mul_one,
      Int.units_mul_self, one_smul]

/-- Generator data differing by `θ' = θ − β·(1 ⊗ ·)` have extensions differing by `−β·`. -/
private theorem genData_extend_sub {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {Q : ℤ → Type}
    [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (D D' : GenData 𝒜 Q) {β : A}
    (hβ : β ∈ 𝒜 1) (hθ : ∀ e, D'.θ e = D.θ e - β • Tot.tmul 𝒜 Q 1 e) (x : Tot 𝒜 Q) :
    D'.extend x = D.extend x - β • x := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [GenData.extend_tmul, GenData.extend_tmul, hθ, smul_sub, Tot.tmul_eq_smul a e, smul_smul,
      smul_smul, sigma_mul_deg_one hβ]
    abel
  | hadd x y hx hy =>
    rw [map_add, map_add, hx, hy, smul_add]
    abel

/-- Key identity for the base change of a gauge on a generator `b ⊗ q`. -/
private theorem bcθp_gauge_aux {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
    {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
    (f : DgaHom 𝒜 ℬ) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (p : ℤ) (b : ↥(ℬ 0)) (q : Q p) (β : A) (y : Tot 𝒜 Q) :
    Tot.tmul ℬ _ (GCDga.d (𝒜 := ℬ) b)
        (DirectSum.lof (ℬ 0) ℤ (BCGen f Q) p (BCGen.tmul f Q 1 q)) +
        (b : B) • bcF f Q (y - β • Tot.tmul 𝒜 Q 1 (DirectSum.lof (𝒜 0) ℤ Q p q)) +
        f β • Tot.tmul ℬ _ 1 (DirectSum.of (BCGen f Q) p (BCGen.tmul f Q b q)) =
      Tot.tmul ℬ _ (GCDga.d (𝒜 := ℬ) b)
        (DirectSum.lof (ℬ 0) ℤ (BCGen f Q) p (BCGen.tmul f Q 1 q)) +
        (b : B) • bcF f Q y := by
  have hx : DirectSum.of (BCGen f Q) p (BCGen.tmul f Q b q) =
      (b : ℬ 0) • bcι f Q (DirectSum.lof (𝒜 0) ℤ Q p q) := by
    rw [bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul]; rfl
  rw [hx, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (b : B), map_sub, bcF_smul, bcF_tmul,
    f.map_one', smul_sub, smul_smul, smul_smul, GCDga.central ℬ b.2 (f β)]
  abel

/-- Z3.o: `θ` of the base change of the gauge is `θ` of the base change minus `g(β)·(1 ⊗ ·)`. -/
private theorem bcθ_gaugedRes {V : Opens X} (hV : V ≤ T.U α)
    (e : DirectSum ℤ fun p => BCGen (P.D.res hV) (gaugedRes P T hh hd α M).Q p) :
    bcθ (P.D.res hV) (gaugedRes P T hh hd α M).toQuasiCohesive e +
        (P.D.res hV (T.h0 α)) • Tot.tmul (P.D.𝒜 V) _ 1 e =
      bcθ ((P.toSheafData.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _
          ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α)) (curvedResM P T hh hd α M))
        e := by
  induction e using DirectSum.induction_on with
  | zero =>
    simp only [map_zero, Tot.tmul_zero, smul_zero, add_zero]
    exact (map_zero _).symm
  | of p x =>
    induction x using BCGen.induction_on with
    | ht b q =>
      rw [bcθ_of]
      refine Eq.trans ?_ (bcθ_of ((P.toSheafData.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _
          ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α)) (curvedResM P T hh hd α M)) p
        _).symm
      rw [bcθp_tmul]
      exact bcθp_gauge_aux (P.D.res hV) _ p b q (T.h0 α) _
    | hadd x y hx hy =>
      rw [(DirectSum.of _ p).map_add, map_add, Tot.tmul_add, smul_add]
      refine Eq.trans ?_ ((congrArg₂ (· + ·) hx hy).trans
        (map_add (bcθ ((P.toSheafData.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _
          ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α)) (curvedResM P T hh hd α M)))
        _ _).symm)
      abel
  | add x y hx hy =>
    rw [map_add, Tot.tmul_add, smul_add]
    refine Eq.trans ?_ ((congrArg₂ (· + ·) hx hy).trans
        (map_add (bcθ ((P.toSheafData.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _
          ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α)) (curvedResM P T hh hd α M)))
        _ _).symm)
    abel

/-- Z3.o: the operator of `gauge_{h⁰_α}(M|U_α)|V` is that of `(M|U_α)|V` minus `h⁰_α|V`. -/
private theorem gaugedRes_bcX {V : Opens X} (hV : V ≤ T.U α)
    (y : Tot (P.D.𝒜 V) (BCGen (P.D.res hV) (gaugedRes P T hh hd α M).Q)) :
    (show Tot (P.D.𝒜 V) (BCGen (P.D.res hV) (gaugedRes P T hh hd α M).Q) from
      ((gaugedRes P T hh hd α M).baseChange (P.D.res hV)).X y) + P.D.res hV (T.h0 α) • y =
      (show Tot (P.D.𝒜 V) (BCGen (P.D.res hV) (gaugedRes P T hh hd α M).Q) from
      ((curvedResM P T hh hd α M).baseChange
        ((P.toSheafData.withCurvature h hh hd).D.res hV)).X y) := by
  have hβ : P.D.res hV (T.h0 α) ∈ P.D.𝒜 V 1 := (P.D.res hV).map_mem (T.h0_mem α)
  induction y using Tot.induction_on with
  | ht a e =>
    show (bcGenData (P.D.res hV) (gaugedRes P T hh hd α M).toQuasiCohesive).extend
        (Tot.tmul (P.D.𝒜 V) _ a e) + _ = _
    rw [GenData.extend_tmul]
    refine Eq.trans ?_ (GenData.extend_tmul
      (bcGenData ((P.toSheafData.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _
          ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α)) (curvedResM P T hh hd α M)))
        a e).symm
    have hθ := bcθ_gaugedRes P T hh hd α M hV e
    have hs : GCDga.sigma (P.D.𝒜 V) a • (P.D.res hV (T.h0 α) • Tot.tmul (P.D.𝒜 V) _ 1 e) =
        P.D.res hV (T.h0 α) •
          Tot.tmul (P.D.𝒜 V) (BCGen (P.D.res hV) (gaugedRes P T hh hd α M).Q) a e := by
      rw [smul_smul, sigma_mul_deg_one hβ, ← smul_smul, ← Tot.tmul_eq_smul]
    refine Eq.trans (?_ : _ = Tot.tmul (P.D.𝒜 V) _ (GCDga.d (P.D.𝒜 V) a) e +
      GCDga.sigma (P.D.𝒜 V) a •
        ((bcGenData (P.D.res hV) (gaugedRes P T hh hd α M).toQuasiCohesive).θ e +
        P.D.res hV (T.h0 α) • Tot.tmul (P.D.𝒜 V) _ 1 e)) ?_
    · rw [smul_add, hs]
      abel
    · exact congrArg (fun w => Tot.tmul (P.D.𝒜 V) _ (GCDga.d (P.D.𝒜 V) a) e +
        GCDga.sigma (P.D.𝒜 V) a • w) hθ
  | hadd x y hx hy =>
    refine Eq.trans (congrArg₂ (· + ·)
      (map_add (bcGenData (P.D.res hV) (gaugedRes P T hh hd α M).toQuasiCohesive).extend x y)
      (smul_add (P.D.res hV (T.h0 α)) x y)) ?_
    refine Eq.trans (add_add_add_comm _ _ _ _) ?_
    exact (congrArg₂ (· + ·) hx hy).trans
      (map_add (bcGenData ((P.toSheafData.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (P.D.A (T.U α)) _ _ (P.D.𝒜 (T.U α)) _
          ((P.toSheafData.withCurvature h hh hd).D.dga (T.U α)) (curvedResM P T hh hd α M))).extend
        x y).symm

/-- Z3.o: `cmpTot_X` for `twCmp`, with the second base change written over the gauged module's
total module type. -/
private theorem twCmp_X_aux {V : Opens X} (hV : V ≤ T.U α)
    (x : (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤)) :
    (show Tot (P.D.𝒜 V) (BCGen (P.D.res hV) (gaugedRes P T hh hd α M).Q) from
      ((curvedResM P T hh hd α M).baseChange ((P.toSheafData.withCurvature h hh hd).D.res hV)).X
      (show Tot (P.D.𝒜 V) (BCGen (P.D.res hV) (gaugedRes P T hh hd α M).Q) from
        twCmp P T hh hd α M hV x)) =
      twCmp P T hh hd α M hV
      ((M.baseChange ((P.toSheafData.withCurvature h hh hd).D.res (le_top : V ≤ ⊤))).X x) :=
  cmpTot_X ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res hV) _ (curved_res_comp_eq P T hh hd α hV)
    M.toQuasiCohesive x

/-- **Z3.o.** `twCmp` intertwines `𝕏 − h⁰_α|V` (on `Tot(M|V)`) with the operator of
`gauge_{h⁰_α}(M|U_α)|V` (the gauge changes `𝕏` by `−h⁰_α`; base change extends `𝕏` by the
Leibniz rule, `b·res(h⁰_α) = ±res(h⁰_α)·b`; and `cmpTot_X`, `cmpTot_smul`). -/
theorem twCmp_X {V : Opens X} (hV : V ≤ T.U α)
    (x : (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤)) :
    ((gaugedRes P T hh hd α M).baseChange (P.D.res hV)).X (twCmp P T hh hd α M hV x) =
      twCmp P T hh hd α M hV
        ((M.baseChange ((P.toSheafData.withCurvature h hh hd).D.res (le_top : V ≤ ⊤))).X x -
          (P.toSheafData.withCurvature h hh hd).D.res hV (T.h0 α) • x) := by
  have h1 := twCmp_X_aux P T hh hd α M hV x
  have h2 := gaugedRes_bcX P T hh hd α M hV (twCmp P T hh hd α M hV x)
  have h3 : twCmp P T hh hd α M hV
      ((M.baseChange ((P.toSheafData.withCurvature h hh hd).D.res (le_top : V ≤ ⊤))).X x -
        (P.toSheafData.withCurvature h hh hd).D.res hV (T.h0 α) • x) =
      twCmp P T hh hd α M hV ((M.baseChange ((P.toSheafData.withCurvature h hh hd).D.res
        (le_top : V ≤ ⊤))).X x) -
        P.D.res hV (T.h0 α) • twCmp P T hh hd α M hV x :=
    (map_sub _ _ _).trans (congrArg _ (twCmp_smul P T hh hd α M hV _ x))
  exact (eq_sub_of_add_eq h2).trans
    ((congrArg (fun w => w - P.D.res hV (T.h0 α) • twCmp P T hh hd α M hV x) h1).trans h3.symm)

/-- `twCmp` commutes with restriction. -/
theorem twCmp_totRes {V W : Opens X} (hV : V ≤ T.U α) (hW : W ≤ V)
    (x : (P.toSheafData.withCurvature h hh hd).TotSec M (le_top : V ≤ ⊤)) :
    twCmp P T hh hd α M (hW.trans hV)
        ((P.toSheafData.withCurvature h hh hd).totRes M le_top hW x) =
      P.totRes (gaugedRes P T hh hd α M) hV hW (twCmp P T hh hd α M hV x) :=
  cmpTot_bcTotRes ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
    ((P.toSheafData.withCurvature h hh hd).D.res hV) _ (curved_res_comp_eq P T hh hd α hV)
    M.toQuasiCohesive ((P.toSheafData.withCurvature h hh hd).D.res hW)
    ((P.toSheafData.withCurvature h hh hd).D.res (hW.trans hV)) _
    (curved_res_comp_eq P T hh hd α (hW.trans hV))
    ((P.toSheafData.withCurvature h hh hd).D.res_comp _ _)
    ((P.toSheafData.withCurvature h hh hd).D.res_comp _ _) x

/-- **Z3.o.** Sectionwise comparison `J_T(M)^n_α(V) ≃ α_{U_α}(gauge_{h⁰_α}(M|U_α))^n(V)` for
`V ≤ U_α` (`twCmp`; `O(V)`-linear by `twCmp_smul`). -/
def twLocalEquiv (n : ℤ) {V : Opens X} (hV : V ≤ T.U α) :
    (P.toSheafData.withCurvature h hh hd).sheafOfSec M n (le_top : V ≤ ⊤) ≃+
      P.sheafOfSec (gaugedRes P T hh hd α M) n hV where
  toFun x := ⟨twCmp P T hh hd α M hV x.1, twCmp_mem P T hh hd α M hV x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  invFun y := ⟨twCmpInv P T hh hd α M hV y.1, twCmpInv_mem P T hh hd α M hV y.2⟩
  left_inv x := Subtype.ext (twCmpInv_twCmp P T hh hd α M hV x.1)
  right_inv y := Subtype.ext (twCmp_twCmpInv P T hh hd α M hV y.1)

/-- `twLocalEquiv` commutes with restriction. -/
private theorem twLocalEquiv_res (n : ℤ) {W W' : Opens X} (hW : W ≤ T.U α) (h' : W' ≤ W)
    (x : (P.toSheafData.withCurvature h hh hd).sheafOfSec M n (le_top : W ≤ ⊤)) :
    twLocalEquiv P T hh hd α M n (h'.trans hW)
        ((P.toSheafData.withCurvature h hh hd).sheafOfRes M n le_top h' x) =
      P.sheafOfRes (gaugedRes P T hh hd α M) n hW h' (twLocalEquiv P T hh hd α M n hW x) := by
  refine Subtype.ext ?_
  exact twCmp_totRes P T hh hd α M hW h' x.1

/-- **Z3.o.** The comparison `J_T(M)^n_α ≅ α_{U_α}(gauge_{h⁰_α}(M|U_α))^n` of sheaves on
`Over U_α`: `twLocalEquiv` on sections over `W ≤ U_α` (`homOfSec₀`; `O`-linear by `twCmp_smul`,
natural by `twCmp_totRes`). -/
def twLocalIsoSh (n : ℤ) :
    (TwMod.comp P.toSheafData.O T.U T.ch α).obj (T.twTerm hh hd M n) ≅
      P.sheafOfOverSh (T.U α) (gaugedRes P T hh hd α M) n where
  hom := homOfSec₀ (fun {W} hW => (twLocalEquiv P T hh hd α M n hW).toAddMonoidHom)
    (by
      intro W hW r x
      refine Subtype.ext ?_
      exact twCmp_smul P T hh hd α M hW (P.ρ W r : P.D.A W) x.1)
    (by
      intro W W' hW h' x
      exact twLocalEquiv_res P T hh hd α M n hW h' x)
  inv := homOfSec₀ (fun {W} hW => (twLocalEquiv P T hh hd α M n hW).symm.toAddMonoidHom)
    (by
      intro W hW r y
      refine Subtype.ext ?_
      exact cmpTotInv_smul ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤))
        ((P.toSheafData.withCurvature h hh hd).D.res hW) _ (curved_res_comp_eq P T hh hd α hW)
        M.toQuasiCohesive (P.ρ W r : P.D.A W) y.1)
    (by
      intro W W' hW h' y
      refine (Equiv.symm_apply_eq (twLocalEquiv P T hh hd α M n (h'.trans hW)).toEquiv).2 ?_
      refine Eq.trans ?_ (twLocalEquiv_res P T hh hd α M n hW h' _).symm
      exact congrArg _ ((twLocalEquiv P T hh hd α M n hW).apply_symm_apply y).symm)
  hom_inv_id := by
    ext Y x
    exact (twLocalEquiv P T hh hd α M n (leOfHom Y.unop.hom)).symm_apply_apply x
  inv_hom_id := by
    ext Y y
    exact (twLocalEquiv P T hh hd α M n (leOfHom Y.unop.hom)).apply_symm_apply y

/-- **Z3.o.** [A, proofs of Lemma 7.2.17 and Prop 7.2.19], blueprint-tw D.6. The component
complex `J_T(M)_α` on `Over U_α` is isomorphic to `α_{U_α}(gauge_{h⁰_α}(M|U_α))` (C1.c): termwise `twLocalIsoSh`,
compatible with the differentials `𝕏 − h⁰_α` and `𝕏` of the gauged module (`twCmp_X`). -/
def twLocalIso :
    ((TwMod.comp P.toSheafData.O T.U T.ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (T.twistedSheafOf hh hd M) ≅
      P.sheafOfOver (T.U α) (gaugedRes P T hh hd α M) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => twLocalIsoSh P T hh hd α M n) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have e1 : (P.sheafOfOver (T.U α) (gaugedRes P T hh hd α M)).d i (i + 1) =
        P.sheafOfOverD (T.U α) (gaugedRes P T hh hd α M) i := CochainComplex.of_d _ _ _
    have e2 : (T.twistedSheafOf hh hd M).d i (i + 1) = T.twDiff hh hd M i :=
      CochainComplex.of_d _ _ _
    have e3 : (((TwMod.comp P.toSheafData.O T.U T.ch α).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (T.twistedSheafOf hh hd M)).d i (i + 1) =
        T.twDiffComp hh hd M i α := by
      change (TwMod.comp P.toSheafData.O T.U T.ch α).map
        ((T.twistedSheafOf hh hd M).d i (i + 1)) = _
      rw [e2]
      rfl
    rw [e1, e3]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact twCmp_X P T hh hd α M (leOfHom V.unop.hom) x.1)

end Cohesive
