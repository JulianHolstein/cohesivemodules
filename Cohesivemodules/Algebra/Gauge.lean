import Cohesivemodules.Algebra.CurvedDga
import Cohesivemodules.Algebra.CohesiveDef
import Cohesivemodules.Algebra.GeneratorsDef

set_option linter.style.header false

/-!
# Z3.b: the gauge `𝕏 ↦ 𝕏 − β·`

Blueprint item Z3.b (`blueprint/blueprint-tw.md` §2.1, §3 A.2–A.3; blueprint §11 v1.19). For a gc
dga `i` (curvature `c`), `β ∈ A¹` and `c' = c + dβ`:
* `QuasiCohesive.gauge M β`: a quasi-cohesive module `M` over `(𝒜, c')` (instance `withC i c'`)
  with operator `𝕏 − β·`, a quasi-cohesive module over `(𝒜, c)`; `ungauge` (`𝕏 + β·`) is inverse;
* the Hom complexes agree: `Hom` by `rfl`, `δ` on `Hom^n`, hence `Z0`, `B0`;
* `gaugeHoP : Ho(P_{(𝒜, c')}) ≌ Ho(P_{(𝒜, c)})`, the identity on `H⁰` up to `Z0`/`B0` equality.
This is [B, §2.7] `(f, ω) = (id, β)` read through `c_here = −c_Block` (left modules).

## Deviations
* `IsUnit (2 : k)` is assumed (for `β² = 0`: graded commutativity gives `β² = −β²`); true for
  `k = ℂ`. Not in [B].

## Lean notes
Two instances (`withC i c' …` and `i`) live on the same term `𝒜` here; projections of modules
over the curved instance are written with `@` (dot notation re-synthesizes `i`; prototype P15).
-/

noncomputable section

namespace Cohesive

open CategoryTheory

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  (i : GCDga 𝒜) (c' : A) (hc : c' ∈ 𝒜 2) (hd : i.d c' = 0)

/-- Z3.b: quasi-cohesive modules over the curved instance `withC i c'`. -/
abbrev CQC := @QuasiCohesive k _ A _ _ 𝒜 _ (i.withC c' hc hd)

/-- Z3.b: cohesive modules over the curved instance `withC i c'`. -/
abbrev CCM := @CohesiveModule k _ A _ _ 𝒜 _ (i.withC c' hc hd)

variable {i c' hc hd}

/-- Graded commutativity and `2` invertible give `β² = 0` for `β ∈ A¹`. -/
private lemma sq_eq_zero_of_deg_one (j : GCDga 𝒜) {β : A} (hβ : β ∈ 𝒜 1) (h2 : IsUnit (2 : k)) :
    β * β = 0 := by
  have h := j.gcomm hβ hβ
  rw [show ((1 : ℤ) * 1).negOnePow = -1 by decide, Units.neg_smul, one_smul] at h
  have h' : (2 : k) • (β * β) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  obtain ⟨u, hu⟩ := h2
  have : (↑u⁻¹ * 2 : k) • (β * β) = 0 := by rw [mul_smul, h', smul_zero]
  rwa [← hu, Units.inv_mul, one_smul] at this

/-- Leibniz rule for `𝕏 − β·` from the one for `𝕏`. -/
private lemma gauge_leibniz_aux (j : GCDga 𝒜) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (X : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q)
    (hL : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 Q,
      X (a • x) = j.d a • x + p.negOnePow • a • X x)
    {β : A} (hβ : β ∈ 𝒜 1) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (x : Tot 𝒜 Q) :
    (X - DistribSMul.toLinearMap k (Tot 𝒜 Q) β) (a • x) =
      j.d a • x + p.negOnePow • a • (X - DistribSMul.toLinearMap k (Tot 𝒜 Q) β) x := by
  have h2 : β • a • x = p.negOnePow • a • β • x := by
    rw [← mul_smul, ← mul_smul, j.gcomm hβ ha, one_mul, smul_assoc, mul_smul]
  simp only [LinearMap.sub_apply, DistribSMul.toLinearMap_apply, hL ha, h2, smul_sub]
  abel

/-- Flatness of `𝕏 − β·` from Leibniz and flatness of `𝕏` (curvature `cc + dβ`). -/
private lemma gauge_flat_aux (j : GCDga 𝒜) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (X : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q) (c' cc : A)
    (hL : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 Q,
      X (a • x) = j.d a • x + p.negOnePow • a • X x)
    (hF : ∀ x : Tot 𝒜 Q, X (X x) = c' • x)
    {β : A} (hβ : β ∈ 𝒜 1) (hcβ : c' = cc + j.d β) (h2 : IsUnit (2 : k)) (x : Tot 𝒜 Q) :
    (X - DistribSMul.toLinearMap k (Tot 𝒜 Q) β)
      ((X - DistribSMul.toLinearMap k (Tot 𝒜 Q) β) x) = cc • x := by
  have hsq : β • β • x = 0 := by
    rw [← mul_smul, sq_eq_zero_of_deg_one j hβ h2, zero_smul]
  simp only [LinearMap.sub_apply, DistribSMul.toLinearMap_apply, map_sub, hL hβ, hF, hsq, hcβ,
    add_smul, Int.negOnePow_one, Units.neg_smul, one_smul]
  abel

/-- Leibniz rule for `𝕏 + β·` from the one for `𝕏`. -/
private lemma ungauge_leibniz_aux (j : GCDga 𝒜) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (X : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q)
    (hL : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 Q,
      X (a • x) = j.d a • x + p.negOnePow • a • X x)
    {β : A} (hβ : β ∈ 𝒜 1) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (x : Tot 𝒜 Q) :
    (X + DistribSMul.toLinearMap k (Tot 𝒜 Q) β) (a • x) =
      j.d a • x + p.negOnePow • a • (X + DistribSMul.toLinearMap k (Tot 𝒜 Q) β) x := by
  have h2 : β • a • x = p.negOnePow • a • β • x := by
    rw [← mul_smul, ← mul_smul, j.gcomm hβ ha, one_mul, smul_assoc, mul_smul]
  simp only [LinearMap.add_apply, DistribSMul.toLinearMap_apply, hL ha, h2, smul_add]
  abel

/-- Flatness of `𝕏 + β·` from Leibniz and flatness of `𝕏` (curvature `cc`, `c' = cc + dβ`). -/
private lemma ungauge_flat_aux (j : GCDga 𝒜) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (X : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q) (c' cc : A)
    (hL : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 Q,
      X (a • x) = j.d a • x + p.negOnePow • a • X x)
    (hF : ∀ x : Tot 𝒜 Q, X (X x) = cc • x)
    {β : A} (hβ : β ∈ 𝒜 1) (hcβ : c' = cc + j.d β) (h2 : IsUnit (2 : k)) (x : Tot 𝒜 Q) :
    (X + DistribSMul.toLinearMap k (Tot 𝒜 Q) β)
      ((X + DistribSMul.toLinearMap k (Tot 𝒜 Q) β) x) = c' • x := by
  have hsq : β • β • x = 0 := by
    rw [← mul_smul, sq_eq_zero_of_deg_one j hβ h2, zero_smul]
  simp only [LinearMap.add_apply, DistribSMul.toLinearMap_apply, map_add, hL hβ, hF, hsq, hcβ,
    add_smul, Int.negOnePow_one, Units.neg_smul, one_smul]
  abel

/-- **Z3.b.** [B, §2.7]. The gauge of a quasi-cohesive module `M` over `(𝒜, c')` by `β ∈ A¹`
with `c' = c + dβ`: the same generators, operator `𝕏 − β·`, a quasi-cohesive module over `(𝒜, c)`:
`(𝕏 − β)² = c' − dβ + β² = c` (Leibniz `𝕏(βx) = dβ·x − β𝕏x`, `β² = 0`). -/
def QuasiCohesive.gauge (M : CQC i c' hc hd) (β : A) (hβ : β ∈ 𝒜 1) (hcβ : c' = i.c + i.d β)
    (h2 : IsUnit (2 : k)) : @QuasiCohesive k _ A _ _ 𝒜 _ i :=
  let Q := @QuasiCohesive.Q k _ A _ _ 𝒜 _ (i.withC c' hc hd) M
  letI : ∀ p, AddCommGroup (Q p) := @QuasiCohesive.acg k _ A _ _ 𝒜 _ (i.withC c' hc hd) M
  letI : ∀ p, Module (𝒜 0) (Q p) := @QuasiCohesive.mod k _ A _ _ 𝒜 _ (i.withC c' hc hd) M
  { Q := Q
    X := (fun (f : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q) => f - DistribSMul.toLinearMap k (Tot 𝒜 Q) β)
      (@QuasiCohesive.X k _ A _ _ 𝒜 _ (i.withC c' hc hd) M)
    X_mem := fun {m x} hx => by
      have h1 := @QuasiCohesive.X_mem k _ A _ _ 𝒜 _ (i.withC c' hc hd) M m x hx
      have h2 := smul_mem_totDeg (𝒜 := 𝒜) (Q := Q) hβ hx
      rw [add_comm 1 m] at h2
      exact sub_mem h1 h2
    leibniz := fun {p a} ha x =>
      gauge_leibniz_aux i Q (@QuasiCohesive.X k _ A _ _ 𝒜 _ (i.withC c' hc hd) M)
        (fun {p a} ha x => @QuasiCohesive.leibniz k _ A _ _ 𝒜 _ (i.withC c' hc hd) M p a ha x)
        hβ ha x
    flat := fun x =>
      gauge_flat_aux i Q (@QuasiCohesive.X k _ A _ _ 𝒜 _ (i.withC c' hc hd) M) c' i.c
        (fun {p a} ha x => @QuasiCohesive.leibniz k _ A _ _ 𝒜 _ (i.withC c' hc hd) M p a ha x)
        (@QuasiCohesive.flat k _ A _ _ 𝒜 _ (i.withC c' hc hd) M) hβ hcβ h2 x }

/-- **Z3.b.** The inverse of the gauge: a quasi-cohesive module `M` over `(𝒜, c)` with operator
`𝕏 + β·`, over `(𝒜, c')` for `c' = c + dβ`. -/
def QuasiCohesive.ungauge (M : @QuasiCohesive k _ A _ _ 𝒜 _ i) (β : A) (hβ : β ∈ 𝒜 1)
    (hcβ : c' = i.c + i.d β) (h2 : IsUnit (2 : k)) : CQC i c' hc hd :=
  @QuasiCohesive.mk k _ A _ _ 𝒜 _ (i.withC c' hc hd) M.Q M.acg M.mod
    (show @Tot k _ A _ _ 𝒜 _ (i.withC c' hc hd) M.Q M.acg M.mod →ₗ[k]
        @Tot k _ A _ _ 𝒜 _ (i.withC c' hc hd) M.Q M.acg M.mod from
      M.X + DistribSMul.toLinearMap k _ β)
    (fun {m x} hx => by
      have h1 := M.X_mem hx
      have h2 := smul_mem_totDeg (𝒜 := 𝒜) (Q := M.Q) hβ hx
      rw [add_comm 1 m] at h2
      exact add_mem h1 h2)
    (fun {p a} ha x => ungauge_leibniz_aux i M.Q M.X (fun {p a} ha x => M.leibniz ha x) hβ ha x)
    (fun x => ungauge_flat_aux i M.Q M.X c' i.c (fun {p a} ha x => M.leibniz ha x) M.flat hβ
      hcβ h2 x)

variable (β : A) (hβ : β ∈ 𝒜 1) (hcβ : c' = i.c + i.d β) (h2 : IsUnit (2 : k))

/-- **Z3.b.** The gauge of a cohesive module (same generators, so still bounded, finite and
projective). -/
def CohesiveModule.gauge (M : CCM i c' hc hd) : @CohesiveModule k _ A _ _ 𝒜 _ i :=
  { (@CohesiveModule.toQuasiCohesive k _ A _ _ 𝒜 _ (i.withC c' hc hd) M).gauge β hβ hcβ h2 with
    bounded := @CohesiveModule.bounded k _ A _ _ 𝒜 _ (i.withC c' hc hd) M
    finite := @CohesiveModule.finite k _ A _ _ 𝒜 _ (i.withC c' hc hd) M
    projective := @CohesiveModule.projective k _ A _ _ 𝒜 _ (i.withC c' hc hd) M }

/-- **Z3.b.** The inverse gauge of a cohesive module. -/
def CohesiveModule.ungauge (M : @CohesiveModule k _ A _ _ 𝒜 _ i) : CCM i c' hc hd :=
  @CohesiveModule.mk k _ A _ _ 𝒜 _ (i.withC c' hc hd)
    (M.toQuasiCohesive.ungauge β hβ hcβ h2) M.bounded M.finite M.projective

/-- **Z3.b (A.3).** The gauge does not change `Hom^n` (same submodule, rfl). -/
theorem gauge_hom (M₁ M₂ : CQC i c' hc hd) (n : ℤ) :
    @Hom k _ A _ _ 𝒜 _ i (M₁.gauge β hβ hcβ h2) (M₂.gauge β hβ hcβ h2) n =
      @Hom k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ M₂ n := rfl

/-- The `δ`-formula is unchanged by `X ↦ X − β` when `φ(βx) = (−1)^n βφ(x)`. -/
private lemma gauge_δ_aux (Q₁ Q₂ : ℤ → Type) [∀ p, AddCommGroup (Q₁ p)] [∀ p, AddCommGroup (Q₂ p)]
    [∀ p, Module (𝒜 0) (Q₁ p)] [∀ p, Module (𝒜 0) (Q₂ p)]
    (X₁ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₁) (X₂ : Tot 𝒜 Q₂ →ₗ[k] Tot 𝒜 Q₂) (n : ℤ)
    (φ : Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂) (β : A)
    (hφ : ∀ x, φ (β • x) = (n * 1).negOnePow • β • φ x) :
    (X₂ - DistribSMul.toLinearMap k (Tot 𝒜 Q₂) β) ∘ₗ φ -
        n.negOnePow • (φ ∘ₗ (X₁ - DistribSMul.toLinearMap k (Tot 𝒜 Q₁) β)) =
      X₂ ∘ₗ φ - n.negOnePow • (φ ∘ₗ X₁) := by
  ext x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_sub,
    DistribSMul.toLinearMap_apply, hφ, Units.smul_def, mul_one, smul_sub, smul_smul]
  rw [← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  abel

/-- **Z3.b (A.3).** On `Hom^n` the gauge does not change `δ`:the terms `−βφ + (−1)^n φβ`
cancel since `φ(βx) = (−1)^n βφ(x)`. -/
theorem gauge_δ (M₁ M₂ : CQC i c' hc hd) (n : ℤ)
    {φ : @QuasiCohesive.T k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ →ₗ[k]
      @QuasiCohesive.T k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₂}
    (hφ : φ ∈ @Hom k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ M₂ n) :
    @δ k _ A _ _ 𝒜 _ i (M₁.gauge β hβ hcβ h2) (M₂.gauge β hβ hcβ h2) n φ =
      @δ k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ M₂ n φ :=
  letI : ∀ p, AddCommGroup (@QuasiCohesive.Q k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ p) :=
    @QuasiCohesive.acg k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁
  letI : ∀ p, AddCommGroup (@QuasiCohesive.Q k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₂ p) :=
    @QuasiCohesive.acg k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₂
  letI : ∀ p, Module (𝒜 0) (@QuasiCohesive.Q k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ p) :=
    @QuasiCohesive.mod k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁
  letI : ∀ p, Module (𝒜 0) (@QuasiCohesive.Q k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₂ p) :=
    @QuasiCohesive.mod k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₂
  gauge_δ_aux (@QuasiCohesive.Q k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁)
    (@QuasiCohesive.Q k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₂)
    (@QuasiCohesive.X k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁)
    (@QuasiCohesive.X k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₂) n φ β (hφ.2 hβ)

/-- **Z3.b.** The gauge does not change the closed degree-0 maps. -/
theorem gauge_Z0 (M₁ M₂ : CQC i c' hc hd) :
    @Z0 k _ A _ _ 𝒜 _ i (M₁.gauge β hβ hcβ h2) (M₂.gauge β hβ hcβ h2) =
      @Z0 k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ M₂ := by
  refine Submodule.ext fun φ => ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨h.1, ?_⟩
    have := gauge_δ β hβ hcβ h2 M₁ M₂ 0 h.1
    exact this.symm.trans (LinearMap.mem_ker.1 h.2)
  · refine ⟨h.1, ?_⟩
    have := gauge_δ β hβ hcβ h2 M₁ M₂ 0 h.1
    have h0 : @δ k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ M₂ 0 φ = 0 := h.2
    exact this.trans h0

/-- **Z3.b.** The gauge does not change the boundaries of degree 0. -/
theorem gauge_B0 (M₁ M₂ : CQC i c' hc hd) :
    @B0 k _ A _ _ 𝒜 _ i (M₁.gauge β hβ hcβ h2) (M₂.gauge β hβ hcβ h2) =
      @B0 k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ M₂ := by
  refine Submodule.ext fun φ => ⟨?_, ?_⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨ψ, hψ, (gauge_δ β hβ hcβ h2 M₁ M₂ (-1) hψ).symm⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨ψ, hψ, gauge_δ β hβ hcβ h2 M₁ M₂ (-1) hψ⟩

/-- Two quasi-cohesive structures with the same generators and equal operators are equal. -/
private lemma qc_congr {j : GCDga 𝒜} {Q : ℤ → Type} [acg : ∀ p, AddCommGroup (Q p)]
    [mod : ∀ p, Module (𝒜 0) (Q p)] {X Y : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q} (h : X = Y)
    {m₁ l₁ f₁ m₂ l₂ f₂} :
    (QuasiCohesive.mk Q X m₁ l₁ f₁ : @QuasiCohesive k _ A _ _ 𝒜 _ j) =
      QuasiCohesive.mk Q Y m₂ l₂ f₂ := by
  subst h; rfl

/-- Two cohesive modules with the same generators and equal operators are equal. -/
private lemma cm_congr {j : GCDga 𝒜} {Q : ℤ → Type} [acg : ∀ p, AddCommGroup (Q p)]
    [mod : ∀ p, Module (𝒜 0) (Q p)] {X Y : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q} (h : X = Y)
    {m₁ l₁ f₁ b₁ fi₁ p₁ m₂ l₂ f₂ b₂ fi₂ p₂} :
    (CohesiveModule.mk (QuasiCohesive.mk Q X m₁ l₁ f₁) b₁ fi₁ p₁ :
        @CohesiveModule k _ A _ _ 𝒜 _ j) =
      CohesiveModule.mk (QuasiCohesive.mk Q Y m₂ l₂ f₂) b₂ fi₂ p₂ := by
  subst h; rfl

/-- **Z3.b.** `ungauge ∘ gauge = id`. -/
theorem ungauge_gauge (M : CCM i c' hc hd) :
    (M.gauge β hβ hcβ h2).ungauge β hβ hcβ h2 = M := by
  obtain ⟨⟨Q, X, hXm, hL, hF⟩, hb, hf, hp⟩ := M
  unfold CohesiveModule.ungauge CohesiveModule.gauge QuasiCohesive.ungauge QuasiCohesive.gauge
  congr 1
  exact qc_congr (sub_add_cancel _ _)

/-- **Z3.b.** `gauge ∘ ungauge = id`. -/
theorem gauge_ungauge (M : @CohesiveModule k _ A _ _ 𝒜 _ i) :
    (M.ungauge (hc := hc) (hd := hd) β hβ hcβ h2).gauge β hβ hcβ h2 = M := by
  obtain ⟨⟨Q, X, hXm, hL, hF⟩, hb, hf, hp⟩ := M
  unfold CohesiveModule.ungauge CohesiveModule.gauge QuasiCohesive.ungauge QuasiCohesive.gauge
  refine cm_congr ?_
  exact add_sub_cancel_right _ _

/-- **Z3.b.** The gauge on `H⁰`: the identity on representatives, through `gauge_Z0`, `gauge_B0`. -/
def gaugeH0 (M₁ M₂ : CQC i c' hc hd) :
    @H0 k _ A _ _ 𝒜 _ (i.withC c' hc hd) M₁ M₂ ≃ₗ[k]
      @H0 k _ A _ _ 𝒜 _ i (M₁.gauge β hβ hcβ h2) (M₂.gauge β hβ hcβ h2) :=
  Submodule.Quotient.equiv _ _ (LinearEquiv.ofEq _ _ (gauge_Z0 β hβ hcβ h2 M₁ M₂).symm) (by
    have e := gauge_B0 β hβ hcβ h2 M₁ M₂
    refine SetLike.ext fun z => ⟨?_, fun hz => ?_⟩
    · rintro ⟨w, hw, rfl⟩
      exact (SetLike.ext_iff.1 e _).2 hw
    · exact ⟨⟨z.1, (SetLike.ext_iff.1 (gauge_Z0 β hβ hcβ h2 M₁ M₂) _).1 z.2⟩,
        (SetLike.ext_iff.1 e _).1 hz, Subtype.ext rfl⟩)

/-- **Z3.b.** The gauge functor `Ho(P_{(𝒜, c')}) ⥤ Ho(P_{(𝒜, c)})`: `M ↦ gauge M`, the identity on
morphisms (`gaugeH0`). -/
def gaugeFunctor : @HoP k _ A _ _ 𝒜 _ (i.withC c' hc hd) ⥤ @HoP k _ A _ _ 𝒜 _ i where
  obj M := ⟨(@HoP.as k _ A _ _ 𝒜 _ (i.withC c' hc hd) M).gauge β hβ hcβ h2⟩
  map {M N} f := gaugeH0 β hβ hcβ h2 _ _ f
  map_id M := rfl
  map_comp {M N P} f g := by
    induction f using Submodule.Quotient.induction_on
    induction g using Submodule.Quotient.induction_on
    rfl

instance : (gaugeFunctor (hc := hc) (hd := hd) β hβ hcβ h2).Faithful where
  map_injective h := (gaugeH0 β hβ hcβ h2 _ _).injective h

instance : (gaugeFunctor (hc := hc) (hd := hd) β hβ hcβ h2).Full where
  map_surjective g :=
    ⟨(gaugeH0 β hβ hcβ h2 _ _).symm g, (gaugeH0 β hβ hcβ h2 _ _).apply_symm_apply g⟩

instance : (gaugeFunctor (hc := hc) (hd := hd) β hβ hcβ h2).EssSurj where
  mem_essImage N :=
    ⟨@HoP.mk k _ A _ _ 𝒜 _ (i.withC c' hc hd)
        (CohesiveModule.ungauge (hc := hc) (hd := hd) β hβ hcβ h2 (@HoP.as k _ A _ _ 𝒜 _ i N)),
      ⟨eqToIso (congrArg (fun M => (⟨M⟩ : @HoP k _ A _ _ 𝒜 _ i))
        (gauge_ungauge β hβ hcβ h2 (@HoP.as k _ A _ _ 𝒜 _ i N)))⟩⟩

/-- **Z3.b.** [B, §2.7]. The gauge is an equivalence `Ho(P_{(𝒜, c + dβ)}) ≌ Ho(P_{(𝒜, c)})`. -/
def gaugeHoP : @HoP k _ A _ _ 𝒜 _ (i.withC c' hc hd) ≌ @HoP k _ A _ _ 𝒜 _ i :=
  letI : (gaugeFunctor (hc := hc) (hd := hd) β hβ hcβ h2).IsEquivalence := {}
  (gaugeFunctor β hβ hcβ h2).asEquivalence

end Cohesive
