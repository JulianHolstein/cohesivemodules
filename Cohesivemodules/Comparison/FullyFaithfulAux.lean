import Cohesivemodules.Comparison.AlphaDef
import Cohesivemodules.Algebra.BaseChangeExt
import Cohesivemodules.Algebra.BaseChangeResAPI

set_option linter.style.header false

/-!
# C4 helpers: uniqueness of semilinear maps out of a base change

Algebra-level lemmas used by `Comparison/FullyFaithful.lean` (not part of the statement).
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]
  (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ) (f' : DgaHom 𝒜 𝒞) (hgf : ∀ a, g (f a) = f' a)
  (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

variable {N : Type} [AddCommGroup N] [Module C N]

/-- **Uniqueness.** Two additive maps out of `Tot(f^*Q)` that are `g`-semilinear of degree `n`
and agree on the image of `F` are equal. -/
theorem bc_ext_semilinear (n : ℤ) (ψ ψ' : Tot ℬ (BCGen f Q) →+ N)
    (hs : ∀ {p : ℤ} {b : B}, b ∈ ℬ p → ∀ y, ψ (b • y) = (n * p).negOnePow • g b • ψ y)
    (hs' : ∀ {p : ℤ} {b : B}, b ∈ ℬ p → ∀ y, ψ' (b • y) = (n * p).negOnePow • g b • ψ' y)
    (h : ∀ x, ψ (bcF f Q x) = ψ' (bcF f Q x)) : ψ = ψ' := by
  have hgen : ∀ e' : ⨁ p, BCGen f Q p,
      ψ (Tot.tmul ℬ _ 1 e') = ψ' (Tot.tmul ℬ _ 1 e') := by
    intro e'
    induction e' using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero, map_zero]
    | of p x =>
      induction x using BCGen.induction_on with
      | ht β q =>
        have hx : DirectSum.of (BCGen f Q) p (BCGen.tmul f Q β q) =
            (β : ℬ 0) • bcι f Q (lof (𝒜 0) ℤ Q p q) := by
          rw [bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul]; rfl
        have hF1 : Tot.tmul ℬ _ 1 (bcι f Q (lof (𝒜 0) ℤ Q p q)) =
            bcF f Q (Tot.tmul 𝒜 Q 1 (lof (𝒜 0) ℤ Q p q)) := by
          rw [bcF_tmul, f.map_one']
        rw [hx, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (β : B), hs β.2, hs' β.2,
          mul_zero, Int.negOnePow_zero, one_smul, one_smul, hF1, h]
      | hadd x y hx hy =>
        rw [(DirectSum.of (BCGen f Q) p).map_add, Tot.tmul_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [Tot.tmul_add, map_add, map_add, hx, hy]
  have ht : ∀ (b : B) (e' : ⨁ p, BCGen f Q p), ψ (Tot.tmul ℬ _ b e') = ψ' (Tot.tmul ℬ _ b e') := by
    intro b e'
    rw [Tot.tmul_eq_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Tot.tmul_eq_smul (GCDga.proj ℬ q b) e', hs (GCDga.proj_mem ℬ q b),
      hs' (GCDga.proj_mem ℬ q b), hgen]
  ext x
  induction x using Tot.induction_on with
  | ht b e' => exact ht b e'
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

section Bounded

variable {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- Elements of total degree `m < a` vanish when `Q^p = 0` for `p < a`. -/
theorem eq_zero_of_totDeg_lt (a : ℤ) (hQ : ∀ p, p < a → Subsingleton (Q p)) {m : ℤ} (hm : m < a)
    {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) : x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, b, e, hqp, hb, rfl⟩ := hx
    by_cases hp : p < a
    · have := hQ p hp
      rw [Subsingleton.elim e 0, map_zero, TensorProduct.tmul_zero]
      rfl
    · rw [GCDga.eq_zero_of_neg 𝒜 (by lia) hb, TensorProduct.zero_tmul]
      rfl
  | zero => rfl
  | add x y _ _ hx hy => rw [hx, hy, add_zero]
  | smul r x _ hx => rw [hx, smul_zero]

/-- A `k`-linear map out of `Tot(Q)` (`Q^p = 0` outside `[a, b]`) vanishing on the pieces of total
degree in `[a, b + N]` is zero. -/
theorem linearMap_eq_zero_of_totDeg {N' : Type} [AddCommGroup N'] [Module k N']
    (φ : Tot 𝒜 Q →ₗ[k] N') (a b : ℤ) (hQ : ∀ p, (p < a ∨ b < p) → Subsingleton (Q p))
    (h : ∀ m, a ≤ m → m ≤ b + GCDga.N 𝒜 → ∀ x ∈ totDeg 𝒜 Q m, φ x = 0) : φ = 0 := by
  ext x
  induction x using Tot.induction_on with
  | ht a' e =>
    rw [Tot.tmul_eq_sum, map_sum]
    refine Finset.sum_eq_zero fun q hq => ?_
    have hq' := Finset.mem_Icc.1 hq
    induction e using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero]
    | of p z =>
      by_cases hp : p < a ∨ b < p
      · have := hQ p hp
        rw [Subsingleton.elim z 0, map_zero, Tot.tmul_zero, map_zero]
      · have hp' := not_or.1 hp
        refine h (q + p) (by lia) (by lia) _ ?_
        exact tmul_mem_totDeg (GCDga.proj_mem 𝒜 q a') z
    | add x y hx hy => rw [Tot.tmul_add, map_add, hx, hy, add_zero]
  | hadd x y hx hy => simp only [map_add, hx, hy]

/-- `B⁰ ⊗_{A⁰} Q^p` is a subsingleton when `Q^p` is. -/
theorem bcGen_subsingleton (p : ℤ) (h : Subsingleton (Q p)) : Subsingleton (BCGen f Q p) := by
  have hz : ∀ z : BCGen f Q p, z = 0 := fun z => by
    induction z using BCGen.induction_on with
    | ht β q =>
      rw [Subsingleton.elim q 0]
      exact TensorProduct.tmul_zero _ _
    | hadd x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end Bounded

section ExtAdd

variable {f} {M₁ M₂ : QuasiCohesive 𝒜} {n : ℤ}

/-- `extAlong` is additive. -/
theorem extAlong_add (χ ψ : HomAlong f M₁ M₂ n) : extAlong (χ + ψ) = extAlong χ + extAlong ψ :=
  (eq_extAlong (χ + ψ) (add_mem (extAlong_mem χ) (extAlong_mem ψ)) fun x =>
    (LinearMap.add_apply _ _ _).trans
      (congrArg₂ (· + ·) (extAlong_bcF χ x) (extAlong_bcF ψ x))).symm

/-- `extAlong 0 = 0`. -/
theorem extAlong_zero : extAlong (0 : HomAlong f M₁ M₂ n) = 0 :=
  (eq_extAlong (0 : HomAlong f M₁ M₂ n) (zero_mem _) fun _ => rfl).symm

/-- `extAlong` commutes with left multiplication by a degree-`0` element `c`. -/
theorem extAlong_smul0 (c : ℬ 0) (χ χ' : HomAlong f M₁ M₂ n)
    (h : ∀ x, χ'.1 x = (c : B) • χ.1 x) (y : (M₁.baseChange f).T) :
    extAlong χ' y = (c : B) • extAlong χ y := by
  let φ : (M₁.baseChange f).T →ₗ[k] (M₂.baseChange f).T :=
    { toFun := fun y => (c : B) • extAlong χ y
      map_add' := fun y z => by rw [map_add, smul_add]
      map_smul' := fun r y => by
        rw [map_smul, smul_comm]
        rfl }
  have hφ : φ ∈ Hom (M₁.baseChange f) (M₂.baseChange f) n := by
    refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
    · have := smul_mem_totDeg (𝒜 := ℬ) (Q := (M₂.baseChange f).Q) c.2 ((extAlong_mem χ).1 hx)
      rwa [zero_add] at this
    · change (c : B) • extAlong χ (a • x) = _
      rw [(extAlong_mem χ).2 ha, smul_comm]
      change _ = (n * p).negOnePow • a • (c : B) • extAlong χ x
      rw [← mul_smul, ← mul_smul, GCDga.central ℬ c.2 a]
  have := eq_extAlong χ' hφ fun x => by
    change (c : B) • extAlong χ (bcF f M₁.Q x) = χ'.1 x
    rw [extAlong_bcF, h]
  exact (LinearMap.congr_fun this y).symm

/-- `extAlong` commutes with the differential `δ`. -/
theorem extAlong_δ (χ : HomAlong f M₁ M₂ n) (χ' : HomAlong f M₁ M₂ (n + 1))
    (h : ∀ x, χ'.1 x = (M₂.baseChange f).X (χ.1 x) - n.negOnePow • χ.1 (M₁.X x)) :
    extAlong χ' = δ (M₁.baseChange f) (M₂.baseChange f) n (extAlong χ) := by
  refine (eq_extAlong χ' (δ_mem _ _ (extAlong_mem χ)) fun x => ?_).symm
  change (M₂.baseChange f).X (extAlong χ (bcF f M₁.Q x)) -
      n.negOnePow • extAlong χ ((M₁.baseChange f).X (bcF f M₁.Q x)) = χ'.1 x
  rw [h, extAlong_bcF]
  have e : (M₁.baseChange f).X (bcF f M₁.Q x) = bcF f M₁.Q (M₁.X x) := bc_extend_bcF f M₁ x
  rw [e, extAlong_bcF]

end ExtAdd

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] (P : PreResolvingData X)
  (M₁ M₂ : CohesiveModule P.𝒜X)

/-- `extAlong` commutes with the restriction `totRes`, when the maps `χ`, `χ'` along `res_W`,
`res_{W'}` are related by `χ' = totRes ∘ χ`. -/
theorem totRes_extAlong (n : ℤ) {W W' : Opens X} (hW : W' ≤ W)
    (χ : HomAlong (P.D.res (le_top : W ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n)
    (χ' : HomAlong (P.D.res (le_top : W' ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n)
    (hχ : ∀ x, χ'.1 x = P.totRes M₂ le_top hW (χ.1 x)) (y : P.TotSec M₁ (le_top : W ≤ ⊤)) :
    P.totRes M₂ le_top hW (extAlong χ y) = extAlong χ' (P.totRes M₁ le_top hW y) := by
  have hsm₁ : ∀ (b : P.D.A W) (y : P.TotSec M₁ (le_top : W ≤ ⊤)),
      P.totRes M₁ le_top hW (b • y) = P.D.res hW b • P.totRes M₁ le_top hW y :=
    fun b y => bcTotRes_smul (P.D.res hW) (P.D.res le_top) (P.D.res le_top)
      (P.D.res_comp le_top hW) M₁.Q b y
  have hsm₂ : ∀ (b : P.D.A W) (y : P.TotSec M₂ (le_top : W ≤ ⊤)),
      P.totRes M₂ le_top hW (b • y) = P.D.res hW b • P.totRes M₂ le_top hW y :=
    fun b y => bcTotRes_smul (P.D.res hW) (P.D.res le_top) (P.D.res le_top)
      (P.D.res_comp le_top hW) M₂.Q b y
  have hz : ∀ (u : ℤˣ) (z : P.TotSec M₂ (le_top : W ≤ ⊤)),
      P.totRes M₂ le_top hW (u • z) = u • P.totRes M₂ le_top hW z := fun u z => by
    rw [Units.smul_def, Units.smul_def, map_zsmul]
  have hF : ∀ x : M₁.T, P.totRes M₁ le_top hW (bcF (P.D.res (le_top : W ≤ ⊤)) M₁.Q x) =
      bcF (P.D.res (le_top : W' ≤ ⊤)) M₁.Q x := fun x =>
    bcTotRes_bcF (P.D.res hW) (P.D.res le_top) (P.D.res le_top)
      (P.D.res_comp le_top hW) M₁.Q x
  have e1 : ∀ {p : ℤ} {b : P.D.A W}, b ∈ P.D.𝒜 W p → ∀ y : P.TotSec M₁ (le_top : W ≤ ⊤),
      extAlong χ (b • y) = (n * p).negOnePow • b • extAlong χ y :=
    fun hb y => (extAlong_mem χ).2 hb y
  have e2 : ∀ {p : ℤ} {b : P.D.A W'}, b ∈ P.D.𝒜 W' p → ∀ y : P.TotSec M₁ (le_top : W' ≤ ⊤),
      extAlong χ' (b • y) = (n * p).negOnePow • b • extAlong χ' y :=
    fun hb y => (extAlong_mem χ').2 hb y
  have e3 : ∀ x : M₁.T, extAlong χ (bcF (P.D.res (le_top : W ≤ ⊤)) M₁.Q x) = χ.1 x :=
    fun x => extAlong_bcF χ x
  have e4 : ∀ x : M₁.T, extAlong χ' (bcF (P.D.res (le_top : W' ≤ ⊤)) M₁.Q x) = χ'.1 x :=
    fun x => extAlong_bcF χ' x
  have key := bc_ext_semilinear (P.D.res hW) (P.D.res (le_top : W ≤ ⊤)) M₁.Q n
    (N := P.TotSec M₂ (le_top : W' ≤ ⊤))
    ((P.totRes M₂ le_top hW).comp (extAlong χ).toAddMonoidHom)
    ((extAlong χ').toAddMonoidHom.comp (P.totRes M₁ le_top hW))
    (fun {p b} hb (y : P.TotSec M₁ (le_top : W ≤ ⊤)) => by
      change P.totRes M₂ le_top hW (extAlong χ (b • y)) =
        (n * p).negOnePow • P.D.res hW b • P.totRes M₂ le_top hW (extAlong χ y)
      refine (congrArg (P.totRes M₂ le_top hW) (e1 hb y)).trans ((hz _ _).trans ?_)
      exact congrArg _ (hsm₂ b _))
    (fun {p b} hb (y : P.TotSec M₁ (le_top : W ≤ ⊤)) => by
      change extAlong χ' (P.totRes M₁ le_top hW (b • y)) =
        (n * p).negOnePow • P.D.res hW b • extAlong χ' (P.totRes M₁ le_top hW y)
      rw [hsm₁, e2 ((P.D.res hW).map_mem hb)])
    (fun x => by
      change P.totRes M₂ le_top hW (extAlong χ (bcF (P.D.res (le_top : W ≤ ⊤)) M₁.Q x)) =
        extAlong χ' (P.totRes M₁ le_top hW (bcF (P.D.res (le_top : W ≤ ⊤)) M₁.Q x))
      rw [e3, hF, e4, hχ])
  exact DFunLike.congr_fun key y

end Cohesive
