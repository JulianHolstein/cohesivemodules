import Cohesivemodules.Algebra.BaseChangeResDef

set_option linter.style.header false

/-!
# C3 helper: base change along an isomorphism of (possibly curved) dgas

For maps of (possibly curved) dgas `f : 𝒜 → ℬ` and `g : ℬ → 𝒜` with
 `g ∘ f = id` and `f ∘ g = id` (pointwise), the
comparison map `F = bcF f Q : Tot 𝒜 Q → Tot ℬ (BCGen f Q)` is bijective, with inverse
`invTot` (`b ⊗ (β ⊗ q) ↦ (g b · g β) ⊗ q`). Used for `homTop_bijective` (C3), where
`f = g = res : 𝒜(X) → 𝒜(X)`.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

variable (g : DgaHom ℬ 𝒜) (f : DgaHom 𝒜 ℬ) (hgf : ∀ a, g (f a) = a)
  (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- The bi-additive map `(β, q) ↦ g(β) ⊗ q` on degree `p`. -/
def invGenAux (p : ℤ) : f.B0 →+ Q p →+ Tot 𝒜 Q :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk'
      (fun q => Tot.tmul 𝒜 Q (g (toB f β)) (lof (𝒜 0) ℤ Q p q))
      (fun q q' => by rw [map_add, Tot.tmul_add]))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [toB_add, g.map_add', Tot.add_tmul])

include hgf in
/-- `invGenAux` is `A⁰`-balanced. -/
theorem invGenAux_balanced (p : ℤ) (r : 𝒜 0) (β : f.B0) (q : Q p) :
    invGenAux g f Q p (r • β) q = invGenAux g f Q p β (r • q) := by
  have h1 : toB f (r • β) = f r * toB f β := by
    rw [Algebra.smul_def, toB_mul, toB_algebraMap]
  show Tot.tmul 𝒜 Q (g (toB f (r • β))) (lof (𝒜 0) ℤ Q p q) =
    Tot.tmul 𝒜 Q (g (toB f β)) (lof (𝒜 0) ℤ Q p (r • q))
  rw [h1, map_smul, Tot.tmul_smul0, g.map_mul', hgf, GCDga.central 𝒜 r.2]

/-- Generator inverse `B⁰ ⊗_{A⁰} Q^p → Tot(Q)`, `β ⊗ q ↦ g(β) ⊗ q`. -/
def invGenP (p : ℤ) : BCGen f Q p →+ Tot 𝒜 Q :=
  TensorProduct.liftAddHom (R := 𝒜 0) (invGenAux g f Q p) (invGenAux_balanced g f hgf Q p)

/-- `invGenP` on pure tensors (rfl). -/
theorem invGenP_tmul (p : ℤ) (β : ℬ 0) (q : Q p) :
    invGenP g f hgf Q p (BCGen.tmul f Q β q) = Tot.tmul 𝒜 Q (g β) (lof (𝒜 0) ℤ Q p q) := rfl

/-- Generator inverse on `⨁ p, B⁰ ⊗ Q^p`. -/
def invGen : (⨁ p, BCGen f Q p) →+ Tot 𝒜 Q := DirectSum.toAddMonoid (invGenP g f hgf Q)

/-- `invGenP` is `g`-semilinear. -/
theorem invGenP_smul (p : ℤ) (γ : ℬ 0) (x : BCGen f Q p) :
    invGenP g f hgf Q p (γ • x) = (g (γ : B) : A) • invGenP g f hgf Q p x := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [BCGen.smul_tmul, invGenP_tmul, invGenP_tmul, Tot.smul_tmul]
    exact congrArg (Tot.tmul 𝒜 Q · _) (g.map_mul' (γ : B) (β : B))
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `invGen` is `g`-semilinear. -/
theorem invGen_smul (γ : ℬ 0) (e : ⨁ p, BCGen f Q p) :
    invGen g f hgf Q (γ • e) = (g (γ : B) : A) • invGen g f hgf Q e := by
  induction e using DirectSum.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | of p x =>
    rw [← DirectSum.of_smul]
    unfold invGen
    rw [DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, invGenP_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The bi-additive map `(b, e) ↦ g(b) · invGen(e)`. -/
def invTotAux : B →+ (⨁ p, BCGen f Q p) →+ Tot 𝒜 Q :=
  AddMonoidHom.mk'
    (fun b => AddMonoidHom.mk' (fun e => g b • invGen g f hgf Q e)
      (fun e e' => by rw [map_add, smul_add]))
    (fun b b' => AddMonoidHom.ext fun e => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, g.map_add', add_smul])

/-- `invTotAux` is `B⁰`-balanced. -/
theorem invTotAux_balanced (r : ℬ 0) (b : B) (e : ⨁ p, BCGen f Q p) :
    invTotAux g f hgf Q (r • b) e = invTotAux g f hgf Q b (r • e) := by
  show g (r • b) • invGen g f hgf Q e = g b • invGen g f hgf Q (r • e)
  rw [invGen_smul, GCDga.smul0_def, g.map_mul', GCDga.central 𝒜 (g.map_mem r.2) (g b),
    mul_smul]

/-- `invGen ∘ ι = 1 ⊗ -`. -/
theorem invGen_bcι (e : ⨁ p, Q p) :
    invGen g f hgf Q (bcι f Q e) = Tot.tmul 𝒜 Q 1 e := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero, Tot.tmul_zero]
  | of p q =>
    rw [show DirectSum.of Q p q = DirectSum.lof (𝒜 0) ℤ Q p q from rfl, bcι_lof]
    unfold invGen
    rw [show DirectSum.lof (ℬ 0) ℤ (BCGen f Q) p (BCGen.tmul f Q 1 q) =
      DirectSum.of (BCGen f Q) p (BCGen.tmul f Q 1 q) from rfl, DirectSum.toAddMonoid_of,
      invGenP_tmul]
    have : g.f0 (1 : ℬ 0) = 1 := map_one _
    exact congrArg (Tot.tmul 𝒜 Q · _) g.map_one'
  | add x y hx hy => rw [map_add, map_add, hx, hy, Tot.tmul_add]

/-- The inverse `Tot(f^*M) → Tot(M)` of `F`: `b ⊗ e ↦ g(b) · invGen(e)`. -/
def invTot : Tot ℬ (BCGen f Q) →+ Tot 𝒜 Q :=
  TensorProduct.liftAddHom (R := ℬ 0) (invTotAux g f hgf Q) (invTotAux_balanced g f hgf Q)

/-- `invTot` on pure tensors (rfl). -/
theorem invTot_tmul (b : B) (e : ⨁ p, BCGen f Q p) :
    invTot g f hgf Q (Tot.tmul ℬ _ b e) = g b • invGen g f hgf Q e := rfl

/-- `invTot` is semilinear along `g`. -/
theorem invTot_smul (b : B) (y : Tot ℬ (BCGen f Q)) :
    invTot g f hgf Q (b • y) = g b • invTot g f hgf Q y := by
  induction y using Tot.induction_on with
  | ht a e => rw [Tot.smul_tmul, invTot_tmul, invTot_tmul, g.map_mul', mul_smul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `invTot` is `k`-linear. -/
theorem invTot_smul_k (r : k) (y : Tot ℬ (BCGen f Q)) :
    invTot g f hgf Q (r • y) = r • invTot g f hgf Q y := by
  rw [← algebraMap_smul B r y, invTot_smul, ← algebraMap_smul A r (invTot g f hgf Q y),
    show g (algebraMap k B r) = algebraMap k A r from g.toAlgHom.commutes r]

/-- `invTot ∘ F = id`. -/
theorem invTot_bcF (x : Tot 𝒜 Q) : invTot g f hgf Q (bcF f Q x) = x := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul, invTot_tmul, hgf, invGen_bcι, Tot.smul_tmul, mul_one]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- `F(invGen e) = 1 ⊗ e`. -/
theorem bcF_invGen (hfg : ∀ b, f (g b) = b) (e : ⨁ p, BCGen f Q p) :
    bcF f Q (invGen g f hgf Q e) = Tot.tmul ℬ _ 1 e := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero, Tot.tmul_zero]
  | of p x =>
    induction x using BCGen.induction_on with
    | ht β q =>
      unfold invGen
      rw [DirectSum.toAddMonoid_of, invGenP_tmul, bcF_tmul, hfg, bcι_lof,
        BCGen.tmul_eq_smul β q, ← DirectSum.lof_eq_of (ℬ 0), map_smul, Tot.tmul_smul0, one_mul]
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f Q) p).map_add, map_add, map_add, hx, hy, Tot.tmul_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, Tot.tmul_add]

/-- `invGen` maps the generators of degree `p` to total degree `p`. -/
theorem invGen_mem (p : ℤ) (z : BCGen f Q p) :
    invGen g f hgf Q (DirectSum.of (BCGen f Q) p z) ∈ totDeg 𝒜 Q p := by
  induction z using BCGen.induction_on with
  | ht β q =>
    unfold invGen
    rw [DirectSum.toAddMonoid_of, invGenP_tmul]
    have := tmul_mem_totDeg (𝒜 := 𝒜) (g.map_mem β.2) q
    rwa [zero_add] at this
  | hadd x y hx hy =>
    rw [(DirectSum.of (BCGen f Q) p).map_add, map_add]
    exact add_mem hx hy

/-- `invTot` preserves the total degree. -/
theorem invTot_mem {m : ℤ} {y : Tot ℬ (BCGen f Q)} (hy : y ∈ totDeg ℬ (BCGen f Q) m) :
    invTot g f hgf Q y ∈ totDeg 𝒜 Q m := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change invTot g f hgf Q (Tot.tmul ℬ _ a (DirectSum.of _ p e)) ∈ _
    rw [invTot_tmul]
    exact smul_mem_totDeg (g.map_mem ha) (invGen_mem g f hgf Q p e)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [invTot_smul_k]; exact Submodule.smul_mem _ r hx

/-- `F ∘ invTot = id`. -/
theorem bcF_invTot (hfg : ∀ b, f (g b) = b) (y : Tot ℬ (BCGen f Q)) :
    bcF f Q (invTot g f hgf Q y) = y := by
  induction y using Tot.induction_on with
  | ht b e =>
    rw [invTot_tmul, bcF_smul, hfg, bcF_invGen g f hgf Q hfg, Tot.smul_tmul, mul_one]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

end Cohesive
