import Cohesivemodules.Algebra.BaseChangeResDef
import Cohesivemodules.Algebra.BaseChangeFunctor

set_option linter.style.header false

/-!
# A9: basic API for the restriction between base changes

Blueprint item A9 (used by C1, C4, C7). For maps of (possibly curved) dgas
`f : 𝒜 → ℬ`, `f' : 𝒜 → 𝒞`, `g : ℬ → 𝒞`
with `g ∘ f = f'`, the restriction `bcTotRes : Tot(M_f) → Tot(M_{f'})` between base changes
(`Algebra/BaseChangeResDef.lean`):
* is semilinear over `g`, `k`-linear, preserves the total degree, and is functorial;
* maps `ι e` to `ι' e`, commutes with `F`, `θ` and the operators `𝕏`;
* commutes with the base change `bcHomL` of maps in `Hom^n`.
Also the pointwise forms of "`φ` is closed" and "`δψ = φ - χ`" in `Hom^•` (A5), used for C1.b.
Collected here (28 Oct 2026) from private copies in the C1 definition files `AlphaDef` and
`FunctorDef` and public copies in `AlphaOver`; not part of the statement.
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

/-- A9: `bcTotRes` is semilinear over `g`: `bcTotRes (b • x) = g b • bcTotRes x`. -/
theorem bcTotRes_smul (b : B) (x : Tot ℬ (BCGen f Q)) :
    bcTotRes g f f' hgf Q (b • x) = g b • bcTotRes g f f' hgf Q x := by
  induction x using Tot.induction_on with
  | ht a e => rw [Tot.smul_tmul, bcTotRes_tmul, bcTotRes_tmul, Tot.smul_tmul, g.map_mul']
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- A9: `bcTotRes` is `k`-linear. -/
theorem bcTotRes_smul_k (r : k) (x : Tot ℬ (BCGen f Q)) :
    bcTotRes g f f' hgf Q (r • x) = r • bcTotRes g f f' hgf Q x := by
  rw [← algebraMap_smul B r x, bcTotRes_smul, ← algebraMap_smul C r (bcTotRes g f f' hgf Q x),
    show g (algebraMap k B r) = algebraMap k C r from g.toAlgHom.commutes r]

/-- A9: `bcTotRes` preserves the total degree. -/
theorem bcTotRes_mem {m : ℤ} {x : Tot ℬ (BCGen f Q)} (hx : x ∈ totDeg ℬ (BCGen f Q) m) :
    bcTotRes g f f' hgf Q x ∈ totDeg 𝒞 (BCGen f' Q) m := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change bcTotRes g f f' hgf Q (Tot.tmul ℬ _ a (DirectSum.of _ p e)) ∈ _
    rw [bcTotRes_tmul, DirectSum.map_of]
    exact tmul_mem_totDeg (g.map_mem ha) _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [bcTotRes_smul_k]; exact Submodule.smul_mem _ r hx

/-- A9: `bcTotRes` along the identity is the identity. -/
theorem bcTotRes_id (e : DgaHom ℬ ℬ) (he : ∀ b, e b = b) (hef : ∀ a, e (f a) = f a)
    (x : Tot ℬ (BCGen f Q)) : bcTotRes e f f hef Q x = x := by
  induction x using Tot.induction_on with
  | ht a y =>
    rw [bcTotRes_tmul, he]
    congr 1
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of p z =>
      rw [DirectSum.map_of]
      congr 1
      induction z using BCGen.induction_on with
      | ht β q =>
        rw [bcGenRes_tmul]
        exact congrArg (BCGen.tmul f Q · q) (Subtype.ext (he β))
      | hadd x y hx hy => rw [map_add, hx, hy]
    | add x y hx hy => rw [map_add, hx, hy]
  | hadd x y hx hy => rw [map_add, hx, hy]

section Comp

variable {D : Type} [Ring D] [Algebra k D] {𝒟 : ℤ → Submodule k D} [GradedAlgebra 𝒟] [GCDga 𝒟]

/-- A9: `bcTotRes` is functorial. -/
theorem bcTotRes_comp (h : DgaHom 𝒞 𝒟) (f'' : DgaHom 𝒜 𝒟) (h2 : ∀ a, h (f' a) = f'' a)
    (g3 : DgaHom ℬ 𝒟) (h3 : ∀ a, g3 (f a) = f'' a) (hc : ∀ b, h (g b) = g3 b)
    (x : Tot ℬ (BCGen f Q)) :
    bcTotRes h f' f'' h2 Q (bcTotRes g f f' hgf Q x) = bcTotRes g3 f f'' h3 Q x := by
  induction x using Tot.induction_on with
  | ht a y =>
    rw [bcTotRes_tmul, bcTotRes_tmul, bcTotRes_tmul, hc]
    congr 1
    induction y using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of p z =>
      rw [DirectSum.map_of, DirectSum.map_of, DirectSum.map_of]
      congr 1
      induction z using BCGen.induction_on with
      | ht β q =>
        rw [bcGenRes_tmul, bcGenRes_tmul, bcGenRes_tmul]
        exact congrArg (BCGen.tmul f'' Q · q) (Subtype.ext (hc β))
      | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  | hadd x y hx hy => simp only [map_add, hx, hy]

end Comp

/-- A9: `⨁ bcGenRes` maps `ι e` to `ι' e`. -/
theorem map_bcGenRes_bcι (e : DirectSum ℤ fun p => Q p) :
    DirectSum.map (bcGenRes g f f' hgf Q) (bcι f Q e) = bcι f' Q e := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p q =>
    rw [show DirectSum.of Q p q = DirectSum.lof (𝒜 0) ℤ Q p q from rfl, bcι_lof, bcι_lof]
    change DirectSum.map _ (DirectSum.of _ p _) = DirectSum.of _ p _
    rw [DirectSum.map_of, bcGenRes_tmul]
    exact congrArg (fun β => DirectSum.of (BCGen f' Q) p (BCGen.tmul f' Q β q))
      (Subtype.ext (by exact g.map_one'))
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A9: `bcTotRes ∘ F = F'`. -/
theorem bcTotRes_bcF (y : Tot 𝒜 Q) :
    bcTotRes g f f' hgf Q (bcF f Q y) = bcF f' Q y := by
  induction y using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul, bcF_tmul, bcTotRes_tmul, hgf, map_bcGenRes_bcι g f f' hgf]
  | hadd x y hx hy => simp only [map_add, hx, hy]

/-- A9: `bcTotRes ∘ θ' = θ'' ∘ ⨁ bcGenRes`. -/
theorem bcTotRes_bcθ (M : QuasiCohesive 𝒜) (e : DirectSum ℤ fun p => BCGen f M.Q p) :
    bcTotRes g f f' hgf M.Q (bcθ f M e) =
      bcθ f' M (DirectSum.map (bcGenRes g f f' hgf M.Q) e) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p z =>
    induction z using BCGen.induction_on with
    | ht β q =>
      rw [bcθ_of, bcθp_tmul, map_add, bcTotRes_tmul, bcTotRes_smul, bcTotRes_bcF,
        DirectSum.map_of, bcGenRes_tmul, bcθ_of, bcθp_tmul, g.map_d]
      have hmap : DirectSum.map (bcGenRes g f f' hgf M.Q)
          (DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q)) =
          DirectSum.of (BCGen f' M.Q) p (BCGen.tmul f' M.Q 1 q) := by
        rw [DirectSum.map_of, bcGenRes_tmul]
        exact congrArg (fun β => DirectSum.of (BCGen f' M.Q) p (BCGen.tmul f' M.Q β q))
          (Subtype.ext (by exact g.map_one'))
      change Tot.tmul _ _ _ (DirectSum.map _ (DirectSum.of _ p _)) + _ = _
      rw [hmap]
      rfl
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f M.Q) p).map_add]
      simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A9: `bcTotRes` commutes with the operators `𝕏` of the base changes. -/
theorem bcTotRes_extend (M : QuasiCohesive 𝒜) (x : Tot ℬ (BCGen f M.Q)) :
    (bcGenData f' M).extend (bcTotRes g f f' hgf M.Q x) =
      bcTotRes g f f' hgf M.Q ((bcGenData f M).extend x) := by
  induction x using Tot.induction_on with
  | ht b e =>
    rw [bcTotRes_tmul, GenData.extend_tmul, GenData.extend_tmul, map_add, bcTotRes_tmul,
      bcTotRes_smul, bcGenData_θ, bcGenData_θ, bcTotRes_bcθ, g.map_d, g.map_sigma]
  | hadd x y hx hy => simp only [map_add, hx, hy]

variable {M₁ M₂ : QuasiCohesive 𝒜} (n : ℤ)

/-- A9: the base-changed generator map commutes with `⨁ bcGenRes` and `bcTotRes`. -/
theorem bcGen_bcTotRes (φ : Hom M₁ M₂ n) (e : ⨁ p, BCGen f M₁.Q p) :
    bcGen f' n (restrictGen n φ) (DirectSum.map (bcGenRes g f f' hgf M₁.Q) e) =
      bcTotRes g f f' hgf M₂.Q (bcGen f n (restrictGen n φ) e) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p z =>
    induction z using BCGen.induction_on with
    | ht β q =>
      rw [DirectSum.map_of, bcGenRes_tmul, bcGen_of, bcGen_of, bcGenP_tmul, bcGenP_tmul,
        bcTotRes_smul, bcTotRes_bcF]
      rfl
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f M₁.Q) p).map_add]
      simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A9 (used for C1.b): the base change of `φ ∈ Hom^n` commutes with the restriction
`bcTotRes`. -/
theorem bcHomL_bcTotRes (φ : Hom M₁ M₂ n) (x : Tot ℬ (BCGen f M₁.Q)) :
    bcHomL f' n φ (bcTotRes g f f' hgf M₁.Q x) =
      bcTotRes g f f' hgf M₂.Q (bcHomL f n φ x) := by
  induction x using Tot.induction_on with
  | ht b e =>
    rw [bcTotRes_tmul, bcHomL_tmul, bcHomL_tmul, bcTotRes_smul, ← g.map_twist,
      bcGen_bcTotRes]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

section Hty

variable {M₁ M₂ : QuasiCohesive ℬ}

/-- A5: a closed degree-`0` map commutes with the operators `𝕏`. -/
theorem closed_comm (φ : M₁.T →ₗ[k] M₂.T) (hφ : φ ∈ Z0 M₁ M₂) (x : M₁.T) :
    φ (M₁.X x) = M₂.X (φ x) := by
  have h1 := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hφ).2
  rw [δ_apply, Int.negOnePow_zero, one_smul] at h1
  have h2 := LinearMap.congr_fun h1 x
  exact (sub_eq_zero.1 h2).symm

/-- A5: pointwise form of `δψ = φ - χ` in degree `-1`: `φ x = ψ(𝕏x) + 𝕏(ψx) + χ x`. -/
theorem hty_formula (ψ φ χ : M₁.T →ₗ[k] M₂.T) (hδ : δ M₁ M₂ (-1) ψ = φ - χ) (x : M₁.T) :
    φ x = ψ (M₁.X x) + M₂.X (ψ x) + χ x := by
  rw [δ_eq_mathlib, show (-1 : ℤ) + 1 = 0 by norm_num, Int.negOnePow_zero, one_smul] at hδ
  have h2 := LinearMap.congr_fun hδ x
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] at h2
  rw [add_comm (ψ (M₁.X x)), h2]
  abel

end Hty

end Cohesive
