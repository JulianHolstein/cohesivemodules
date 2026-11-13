import Cohesivemodules.Comparison.TwistedFunctorDef
import Cohesivemodules.Algebra.Gauge

set_option linter.style.header false

/-!
# K14: `α` of a curved module and of its gauge, sectionwise

Blueprint check K14 (`blueprint/blueprint-tw.md` §5), auxiliary. For sheaf data `S`, a closed
`h ∈ 𝒜²(X)` with `h = 0 + dβ` (`β ∈ 𝒜¹(X)`; `hcβ`, with `h|⊤ = res h` the curvature of
`curvedInst ⊤`), and a cohesive module `M` over `(𝒜(X), h)`:
* `gaugeM M`: the flat cohesive module `gauge_β M` over `𝒜(X)` (Z3.b), operator `𝕏 − β`;
* `gaugeTot`: on sections over `V`, `Tot(M|V) = Tot((gauge_β M)|V)`: both are
  `𝒜(V) ⊗ ⨁(𝒜⁰(V) ⊗_{𝒜⁰(X)} Q)`, along the curved and the flat restriction (same algebra map);
* `gaugeSec`: the same on the degree-`n` parts `α(M)^n(V) = α(gauge_β M)^n(V)`;
* it commutes with restrictions (`gaugeSec_res`), sends `𝕏 − β|V` (`gaugeDV`, the differential
  of `J_{T_β}`) to `𝕏` of `(gauge_β M)|V` (gauge commutes with base change, `gaugeSec_gaugeDV`),
  and `α(φ)` to `α(gauge φ)` (`gaugeSec_sheafOfMapV`; `gauge φ = φ`, Z3.b).
Used for `nonempty_twistedJK_exact_iso` (`ChecksTwistedK8.lean`).

## Lean notes
Stated over abstract `S` (not the Dolbeault data), so that no concrete restriction maps are
unfolded. `gaugeTot` is the identity: the two `Tot` types agree up to the `GCDga` instances, which
`Tot` and `BCGen` do not use (as in `twCmp`, Z3.o).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] (S : DgaSheafData X) {h : S.D.A ⊤}
  (hh : h ∈ S.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) (β : S.D.A ⊤) (hβ : β ∈ S.D.𝒜 ⊤ 1)
  (hcβ : S.D.res le_top h = (S.D.dga ⊤).c + (S.D.dga ⊤).d β)

/-- **K14 (aux).** [B, §2.7]. The gauge `gauge_β M` of a cohesive module `M` over `(𝒜(X), h)`, a
flat cohesive module over `𝒜(X)` (`CohesiveModule.gauge`, Z3.b, with the curvature `h|⊤` of
`curvedInst ⊤`). -/
abbrev gaugeM (M : CohesiveModule (S.withCurvature h hh hd).𝒜X) : CohesiveModule S.𝒜X :=
  CohesiveModule.gauge (i := S.D.dga ⊤) (c' := S.D.res le_top h)
    (hc := (S.D.res le_top).map_mem hh) (hd := (S.D.curvedInst h hh hd ⊤).d_c) β hβ hcβ
    (isUnit_of_invertible 2) M

variable (M : CohesiveModule (S.withCurvature h hh hd).𝒜X)

/-- **K14 (aux).** `gauge φ = φ` on closed degree-`0` maps (Z3.b, `gauge_Z0`). -/
def gaugeZ0 {N : CohesiveModule (S.withCurvature h hh hd).𝒜X}
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) :
    Z0 (gaugeM S hh hd β hβ hcβ M).toQuasiCohesive (gaugeM S hh hd β hβ hcβ N).toQuasiCohesive :=
  ⟨φ.1, (SetLike.ext_iff.1 (gauge_Z0 (i := S.D.dga ⊤) (c' := S.D.res le_top h)
    (hc := (S.D.res le_top).map_mem hh) (hd := (S.D.curvedInst h hh hd ⊤).d_c) β hβ hcβ
    (isUnit_of_invertible 2) M.toQuasiCohesive N.toQuasiCohesive) φ.1).2 φ.2⟩

variable {V : Opens X} (hV : V ≤ ⊤)

/-- **K14 (aux).** `Tot(M|V) = Tot((gauge_β M)|V)` for `V ≤ X`: the identity (the curved and
flat restrictions `𝒜(X) → 𝒜(V)` have the same underlying algebra map, and the gauge does not
change the generators). Written as three identities through `Tot (BCGen res M.Q)`, curved then
flat: the direct `AddEquiv.refl` times out in `whnf`. -/
def gaugeTot :
    (S.withCurvature h hh hd).TotSec M hV ≃+ S.TotSec (gaugeM S hh hd β hβ hcβ M) hV :=
  ((AddEquiv.refl _ : (S.withCurvature h hh hd).TotSec M hV ≃+
      Tot ((S.withCurvature h hh hd).D.𝒜 V) (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q)).trans
    (AddEquiv.refl _ : Tot ((S.withCurvature h hh hd).D.𝒜 V)
        (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q) ≃+
      Tot (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q))).trans
    (AddEquiv.refl _ : Tot (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q) ≃+
      S.TotSec (gaugeM S hh hd β hβ hcβ M) hV)

/-- Helper: the middle identity of `gaugeTot` preserves membership in `totDeg`. -/
private theorem gaugeTot_mem_aux {n : ℤ}
    (y : Tot ((S.withCurvature h hh hd).D.𝒜 V)
      (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q)) :
    (AddEquiv.refl _ : Tot ((S.withCurvature h hh hd).D.𝒜 V)
        (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q) ≃+
      Tot (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q)) y ∈
        totDeg (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q) n ↔
      y ∈ totDeg ((S.withCurvature h hh hd).D.𝒜 V)
        (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q) n :=
  Iff.rfl

/-- K14 (aux): `gaugeTot` preserves the total degree. -/
theorem gaugeTot_mem {n : ℤ} (x : (S.withCurvature h hh hd).TotSec M hV) :
    gaugeTot S hh hd β hβ hcβ M hV x ∈
        totDeg (S.D.𝒜 V) ((gaugeM S hh hd β hβ hcβ M).baseChange (S.D.res hV)).Q n ↔
      x ∈ totDeg ((S.withCurvature h hh hd).D.𝒜 V)
        (M.baseChange ((S.withCurvature h hh hd).D.res hV)).Q n := by
  exact gaugeTot_mem_aux S hh hd β hβ hcβ M hV x

/-- Helper: the middle identity of `gaugeTot`, with its type. -/
private def gaugeMid :
    Tot ((S.withCurvature h hh hd).D.𝒜 V) (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q) ≃+
      Tot (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q) :=
  AddEquiv.refl _

/-- Helper: the middle identity of `gaugeTot` is `𝒜(V)`-linear. -/
private theorem gaugeTot_smul_aux (a : S.D.A V)
    (y : Tot ((S.withCurvature h hh hd).D.𝒜 V)
      (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q)) :
    gaugeMid S hh hd β hβ hcβ M hV ((show (S.withCurvature h hh hd).D.A V from a) • y) =
      a • gaugeMid S hh hd β hβ hcβ M hV y :=
  rfl

/-- K14 (aux): `gaugeTot` is `𝒜(V)`-linear. -/
theorem gaugeTot_smul (a : S.D.A V) (x : (S.withCurvature h hh hd).TotSec M hV) :
    gaugeTot S hh hd β hβ hcβ M hV ((show (S.withCurvature h hh hd).D.A V from a) • x) =
      a • gaugeTot S hh hd β hβ hcβ M hV x := by
  exact gaugeTot_smul_aux S hh hd β hβ hcβ M hV a x

/-- **K14 (aux).** `α(M)^n(V) ≅ α(gauge_β M)^n(V)` (`gaugeTot` on the elements of total degree
`n`; `O(V)`-linear by `gaugeTot_smul`, `sheafOfSec_smul_val`). An `AddEquiv`: the two
`O(V)`-module structures live on different spellings of `O`. -/
def gaugeSec (n : ℤ) :
    (S.withCurvature h hh hd).sheafOfSec M n hV ≃+
      S.sheafOfSec (gaugeM S hh hd β hβ hcβ M) n hV where
  toFun x := ⟨gaugeTot S hh hd β hβ hcβ M hV x.1, (gaugeTot_mem S hh hd β hβ hcβ M hV x.1).2 x.2⟩
  invFun y := ⟨(gaugeTot S hh hd β hβ hcβ M hV).symm y.1,
    (gaugeTot_mem S hh hd β hβ hcβ M hV _).1 (by rw [AddEquiv.apply_symm_apply]; exact y.2)⟩
  map_add' x y := Subtype.ext (map_add (gaugeTot S hh hd β hβ hcβ M hV) x.1 y.1)
  left_inv x := Subtype.ext ((gaugeTot S hh hd β hβ hcβ M hV).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((gaugeTot S hh hd β hβ hcβ M hV).apply_symm_apply y.1)

/-- `gaugeSec` on the underlying element (rfl). -/
theorem gaugeSec_val (n : ℤ) (x : (S.withCurvature h hh hd).sheafOfSec M n hV) :
    (gaugeSec S hh hd β hβ hcβ M hV n x).1 = gaugeTot S hh hd β hβ hcβ M hV x.1 :=
  rfl

/-- Helper: the middle identity of `gaugeTot` commutes with `bcTotRes` (curved vs flat). -/
private theorem gaugeMid_res {W : Opens X} (hW : W ≤ V)
    (y : Tot ((S.withCurvature h hh hd).D.𝒜 V)
      (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q)) :
    gaugeMid S hh hd β hβ hcβ M (hW.trans hV)
        (bcTotRes ((S.withCurvature h hh hd).D.res hW) ((S.withCurvature h hh hd).D.res hV)
          ((S.withCurvature h hh hd).D.res (hW.trans hV))
          ((S.withCurvature h hh hd).D.res_comp hV hW) M.Q y) =
      bcTotRes (S.D.res hW) (S.D.res hV) (S.D.res (hW.trans hV)) (S.D.res_comp hV hW)
        (gaugeM S hh hd β hβ hcβ M).Q (gaugeMid S hh hd β hβ hcβ M hV y) := by
  induction y using Tot.induction_on with
  | ht b e => exact rfl
  | hadd x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- **K14 (aux).** `gaugeSec` commutes with the restrictions `α(·)^n(V) → α(·)^n(W)`. -/
theorem gaugeSec_res (n : ℤ) {W : Opens X} (hW : W ≤ V)
    (x : (S.withCurvature h hh hd).sheafOfSec M n hV) :
    gaugeSec S hh hd β hβ hcβ M (hW.trans hV) n ((S.withCurvature h hh hd).sheafOfRes M n hV hW x) =
      S.sheafOfRes (gaugeM S hh hd β hβ hcβ M) n hV hW (gaugeSec S hh hd β hβ hcβ M hV n x) :=
  Subtype.ext (gaugeMid_res S hh hd β hβ hcβ M hV hW x.1)

/-- Helper: `σ(a)·β = β·a` for `β ∈ A¹` (copy of the private lemma of `TwistedLocal.lean`). -/
private theorem sigma_mul_deg_one' {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {β : A} (hβ : β ∈ 𝒜 1) (a : A) :
    GCDga.sigma 𝒜 a * β = β * a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, add_mul, hx, hy, mul_add]
  | homogeneous x =>
    rw [GCDga.sigma_of_mem 𝒜 x.2, smul_mul_assoc, GCDga.gcomm x.2 hβ, smul_smul, mul_one,
      Int.units_mul_self, one_smul]

/-- Helper: `θ' = θ − β·` on generators (copy of the private lemma of `TwistedLocal.lean`). -/
private theorem bcθp_gauge_aux' {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
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

/-- Helper: `θ'` of the base change of the gauge is `θ'` of the base change of `M` minus
`res(β)·(1 ⊗ ·)` (`β|V` times the generator inclusion), curved restriction versus flat. -/
private theorem gaugeM_bcθ
    (e : DirectSum ℤ fun p => BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q p) :
    bcθ (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).toQuasiCohesive e +
        (S.D.res hV β) • Tot.tmul (S.D.𝒜 V) _ 1 e =
      bcθ ((S.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (S.D.A ⊤) _ _ (S.D.𝒜 ⊤) _
          ((S.withCurvature h hh hd).D.dga ⊤) M) e := by
  induction e using DirectSum.induction_on with
  | zero =>
    simp only [map_zero, Tot.tmul_zero, smul_zero, add_zero]
    exact (map_zero _).symm
  | of p x =>
    induction x using BCGen.induction_on with
    | ht b q =>
      rw [bcθ_of]
      refine Eq.trans ?_ (bcθ_of ((S.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (S.D.A ⊤) _ _ (S.D.𝒜 ⊤) _
          ((S.withCurvature h hh hd).D.dga ⊤) M) p _).symm
      rw [bcθp_tmul]
      exact bcθp_gauge_aux' (S.D.res hV) _ p b q β _
    | hadd x y hx hy =>
      rw [(DirectSum.of _ p).map_add, map_add, Tot.tmul_add, smul_add]
      refine Eq.trans ?_ ((congrArg₂ (· + ·) hx hy).trans
        (map_add (bcθ ((S.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (S.D.A ⊤) _ _ (S.D.𝒜 ⊤) _
          ((S.withCurvature h hh hd).D.dga ⊤) M)) _ _).symm)
      abel
  | add x y hx hy =>
    rw [map_add, Tot.tmul_add, smul_add]
    refine Eq.trans ?_ ((congrArg₂ (· + ·) hx hy).trans
        (map_add (bcθ ((S.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (S.D.A ⊤) _ _ (S.D.𝒜 ⊤) _
          ((S.withCurvature h hh hd).D.dga ⊤) M)) _ _).symm)
    abel

/-- Helper: `𝕏` of `(gauge_β M)|V` plus `β|V` is `𝕏` of `M|V` (on the common total module). -/
private theorem gaugeM_bcX
    (y : Tot (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q)) :
    (show Tot (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q) from
      ((gaugeM S hh hd β hβ hcβ M).baseChange (S.D.res hV)).X y) + S.D.res hV β • y =
      (show Tot (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q) from
      (M.baseChange ((S.withCurvature h hh hd).D.res hV)).X y) := by
  have hβ' : S.D.res hV β ∈ S.D.𝒜 V 1 := (S.D.res hV).map_mem hβ
  induction y using Tot.induction_on with
  | ht a e =>
    show (bcGenData (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).toQuasiCohesive).extend
        (Tot.tmul (S.D.𝒜 V) _ a e) + _ = _
    rw [GenData.extend_tmul]
    refine Eq.trans ?_ (GenData.extend_tmul
      (bcGenData ((S.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (S.D.A ⊤) _ _ (S.D.𝒜 ⊤) _
          ((S.withCurvature h hh hd).D.dga ⊤) M))
        a e).symm
    have hθ := gaugeM_bcθ S hh hd β hβ hcβ M hV e
    have hs : GCDga.sigma (S.D.𝒜 V) a • (S.D.res hV β • Tot.tmul (S.D.𝒜 V) _ 1 e) =
        S.D.res hV β •
          Tot.tmul (S.D.𝒜 V) (BCGen (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).Q) a e := by
      rw [smul_smul, sigma_mul_deg_one' hβ', ← smul_smul, ← Tot.tmul_eq_smul]
    refine Eq.trans (?_ : _ = Tot.tmul (S.D.𝒜 V) _ (GCDga.d (S.D.𝒜 V) a) e +
      GCDga.sigma (S.D.𝒜 V) a •
        ((bcGenData (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).toQuasiCohesive).θ e +
        S.D.res hV β • Tot.tmul (S.D.𝒜 V) _ 1 e)) ?_
    · rw [smul_add, hs]
      abel
    · exact congrArg (fun w => Tot.tmul (S.D.𝒜 V) _ (GCDga.d (S.D.𝒜 V) a) e +
        GCDga.sigma (S.D.𝒜 V) a • w) hθ
  | hadd x y hx hy =>
    refine Eq.trans (congrArg₂ (· + ·)
      (map_add (bcGenData (S.D.res hV) (gaugeM S hh hd β hβ hcβ M).toQuasiCohesive).extend x y)
      (smul_add (S.D.res hV β) x y)) ?_
    refine Eq.trans (add_add_add_comm _ _ _ _) ?_
    exact (congrArg₂ (· + ·) hx hy).trans
      (map_add (bcGenData ((S.withCurvature h hh hd).D.res hV)
        (@CohesiveModule.toQuasiCohesive ℂ _ (S.D.A ⊤) _ _ (S.D.𝒜 ⊤) _
          ((S.withCurvature h hh hd).D.dga ⊤) M)).extend x y).symm

/-- **K14 (aux).** [B, §2.7]. Gauge commutes with base change: `gaugeSec` sends `𝕏 − β|V` on
`α(M)^n(V)` (`gaugeDV`, the differential of `J_{T_β}`) to `𝕏` of `(gauge_β M)|V`. -/
theorem gaugeSec_gaugeDV (n : ℤ) (x : (S.withCurvature h hh hd).sheafOfSec M n hV) :
    gaugeSec S hh hd β hβ hcβ M hV (n + 1) ((S.withCurvature h hh hd).gaugeDV M n hV
        (S.D.res hV β) ((S.D.res hV).map_mem hβ) x) =
      S.sheafOfDV (gaugeM S hh hd β hβ hcβ M) n hV (gaugeSec S hh hd β hβ hcβ M hV n x) := by
  refine Subtype.ext ?_
  have h3 := eq_sub_of_add_eq
    (gaugeM_bcX S hh hd β hβ hcβ M hV (gaugeMid S hh hd β hβ hcβ M hV x.1))
  exact (map_sub (gaugeMid S hh hd β hβ hcβ M hV) _ _).trans h3.symm

/-- Helper: `bcHomL` of a degree-`0` map on the pure tensor `b ⊗ (γ ⊗ q)` (generic). -/
private theorem bcHomL_tmul_tmul {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
    {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
    (f : DgaHom 𝒜 ℬ) {M₁ M₂ : QuasiCohesive 𝒜} (φ : Hom M₁ M₂ 0) (b : B) (p : ℤ) (γ : ℬ 0)
    (q : M₁.Q p) :
    bcHomL f 0 φ (Tot.tmul ℬ (BCGen f M₁.Q) b
        (DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q γ q))) =
      GCDga.twist ℬ 0 b • (γ : B) •
        bcF f M₂.Q ((restrictGen 0 φ).1 (DirectSum.lof (𝒜 0) ℤ M₁.Q p q)) := by
  rw [bcHomL_tmul, bcGen_of, bcGenP_tmul]

/-- Helper: the middle identity of `gaugeTot` commutes with `bcHomL` of a closed degree-`0`
map. -/
private theorem gaugeMid_map {N : CohesiveModule (S.withCurvature h hh hd).𝒜X}
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (y : Tot ((S.withCurvature h hh hd).D.𝒜 V)
      (BCGen ((S.withCurvature h hh hd).D.res hV) M.Q)) :
    gaugeMid S hh hd β hβ hcβ N hV
        (bcHomL ((S.withCurvature h hh hd).D.res hV) 0
          ((S.withCurvature h hh hd).toHom0 φ) y) =
      bcHomL (S.D.res hV) 0 (S.toHom0 (gaugeZ0 S hh hd β hβ hcβ M φ))
        (gaugeMid S hh hd β hβ hcβ M hV y) := by
  induction y using Tot.induction_on with
  | ht b e =>
    induction e using DirectSum.induction_on with
    | zero => simp only [Tot.tmul_zero, map_zero]
    | of p x =>
      induction x using BCGen.induction_on with
      | ht γ q =>
        exact (congrArg (gaugeMid S hh hd β hβ hcβ N hV)
          (bcHomL_tmul_tmul ((S.withCurvature h hh hd).D.res hV)
            ((S.withCurvature h hh hd).toHom0 φ) b p γ q)).trans
          (bcHomL_tmul_tmul (S.D.res hV) (S.toHom0 (gaugeZ0 S hh hd β hβ hcβ M φ)) b p γ q).symm
      | hadd x y hx hy =>
        rw [(DirectSum.of _ p).map_add, Tot.tmul_add, map_add, map_add, map_add, map_add, hx, hy]
    | add x y hx hy =>
      rw [Tot.tmul_add, map_add, map_add, map_add, map_add, hx, hy]
  | hadd x y hx hy =>
    rw [map_add, map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hx hy

/-- **K14 (aux).** `gaugeSec` sends `α(φ)` to `α(gauge φ)` (`gauge φ = φ`, `gaugeZ0`). -/
theorem gaugeSec_sheafOfMapV {N : CohesiveModule (S.withCurvature h hh hd).𝒜X}
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ)
    (x : (S.withCurvature h hh hd).sheafOfSec M n hV) :
    gaugeSec S hh hd β hβ hcβ N hV n ((S.withCurvature h hh hd).sheafOfMapV φ n hV x) =
      S.sheafOfMapV (gaugeZ0 S hh hd β hβ hcβ M φ) n hV (gaugeSec S hh hd β hβ hcβ M hV n x) :=
  Subtype.ext (gaugeMid_map S hh hd β hβ hcβ M hV φ x.1)

end Cohesive
