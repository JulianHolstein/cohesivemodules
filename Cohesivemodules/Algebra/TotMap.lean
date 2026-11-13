import Cohesivemodules.Algebra.BaseChange
import Cohesivemodules.Algebra.Filtration

set_option linter.style.header false

/-!
# C7 (algebra): total modules along a map of (possibly curved) dgas

Blueprint item C7 (§4, v1.11). For a map of (possibly curved) dgas `g : (A, 𝒜) → (B, ℬ)` and a
family of additive
maps `u_p : Q^p → Q'^p` that is semilinear along `g⁰ : A⁰ → B⁰`, the map of total modules
`totMapAlong g u : A ⊗_{A⁰} ⨁ Q → B ⊗_{B⁰} ⨁ Q'`, `a ⊗ e ↦ g(a) ⊗ (⨁ u) e`. It gives the
restriction maps of the explicit model `T(K)` (C7.a, C7.c). Defined in one step
(`TensorProduct.liftAddHom`), so `totMapAlong_tmul` is `rfl`, as for `bcF` and `bcTotRes`.

## Deviations
* None from the sources (the sources do not spell this map out). `bcTotRes` (A9) is the special
  case of base-changed generators; it is not rewritten in terms of `totMapAlong`.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]

section Along

variable (g : DgaHom 𝒜 ℬ) {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
  {Q' : ℤ → Type} [∀ p, AddCommGroup (Q' p)] [∀ p, Module (ℬ 0) (Q' p)]
  (u : ∀ p, Q p →+ Q' p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = g.f0 r • u p x)

include hu in
/-- `⨁ u` is semilinear along `g⁰`. -/
theorem famMap_smul_along (r : 𝒜 0) (e : ⨁ p, Q p) :
    famMap u (r • e) = g.f0 r • famMap u e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    rw [show r • DirectSum.of Q p x = DirectSum.of Q p (r • x) from
        (map_smul (DirectSum.lof (𝒜 0) ℤ Q p) r x).symm, famMap_of, famMap_of, hu]
    exact map_smul (DirectSum.lof (ℬ 0) ℤ Q' p) (g.f0 r) _
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The bi-additive map `(a, e) ↦ g(a) ⊗ (⨁ u) e`. -/
def totMapAlongAux : A →+ (⨁ p, Q p) →+ Tot ℬ Q' :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk' (fun e => Tot.tmul ℬ Q' (g a) (famMap u e))
      (fun e e' => by rw [map_add, Tot.tmul_add]))
    (fun a b => AddMonoidHom.ext fun e => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, g.map_add', Tot.add_tmul])

include hu in
/-- `totMapAlongAux` is `A⁰`-balanced (`g` is a ring map and `B⁰` is central). -/
theorem totMapAlongAux_balanced (r : 𝒜 0) (a : A) (e : ⨁ p, Q p) :
    totMapAlongAux g u (r • a) e = totMapAlongAux g u a (r • e) := by
  show Tot.tmul ℬ Q' (g (r • a)) (famMap u e) = Tot.tmul ℬ Q' (g a) (famMap u (r • e))
  rw [famMap_smul_along g u hu, Tot.tmul_smul0, GCDga.smul0_def, g.map_mul', DgaHom.coe_f0]
  exact congrArg (Tot.tmul ℬ Q' · _) (GCDga.central ℬ (g.map_mem r.2) _)

/-- **C7 (algebra).** The map of total modules along `g`: `a ⊗ e ↦ g(a) ⊗ (⨁ u) e`, for a
family `u` of additive maps semilinear along `g⁰`. -/
def totMapAlong : Tot 𝒜 Q →+ Tot ℬ Q' :=
  TensorProduct.liftAddHom (R := 𝒜 0) (totMapAlongAux g u) (totMapAlongAux_balanced g u hu)

/-- `totMapAlong` on pure tensors (rfl). -/
theorem totMapAlong_tmul (a : A) (e : ⨁ p, Q p) :
    totMapAlong g u hu (Tot.tmul 𝒜 Q a e) = Tot.tmul ℬ Q' (g a) (famMap u e) := rfl

/-- `totMapAlong` is semilinear along `g`. -/
theorem totMapAlong_smul (a : A) (x : Tot 𝒜 Q) :
    totMapAlong g u hu (a • x) = g a • totMapAlong g u hu x := by
  induction x using Tot.induction_on with
  | ht b e => rw [Tot.smul_tmul, totMapAlong_tmul, totMapAlong_tmul, Tot.smul_tmul, g.map_mul']
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `totMapAlong` is `k`-linear. -/
theorem totMapAlong_smul_k (r : k) (x : Tot 𝒜 Q) :
    totMapAlong g u hu (r • x) = r • totMapAlong g u hu x := by
  rw [← algebraMap_smul A r x, totMapAlong_smul, ← algebraMap_smul B r (totMapAlong g u hu x),
    show g (algebraMap k A r) = algebraMap k B r from g.toAlgHom.commutes r]

/-- `totMapAlong` preserves the total degree. -/
theorem totMapAlong_mem_totDeg {m : ℤ} {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) :
    totMapAlong g u hu x ∈ totDeg ℬ Q' m := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change totMapAlong g u hu (Tot.tmul 𝒜 Q a (DirectSum.of Q p e)) ∈ _
    rw [totMapAlong_tmul, famMap_of]
    exact tmul_mem_totDeg (g.map_mem ha) _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [totMapAlong_smul_k]; exact Submodule.smul_mem _ r hx

/-- `totMapAlong` preserves the form-degree filtration (A6). -/
theorem totMapAlong_mem_filTot {b : ℤ} {x : Tot 𝒜 Q} (hx : x ∈ filTot 𝒜 Q b) :
    totMapAlong g u hu x ∈ filTot ℬ Q' b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hbq, ha, rfl⟩ := hx
    rw [totMapAlong_tmul]
    exact tmul_mem_filTot hbq (g.map_mem ha) _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [totMapAlong_smul_k]; exact Submodule.smul_mem _ r hx

/-- `totMapAlong` commutes with the augmentation: `ε ∘ totMapAlong = (⨁ u) ∘ ε`. -/
theorem eps_totMapAlong (x : Tot 𝒜 Q) :
    Tot.eps ℬ Q' (totMapAlong g u hu x) = famMap u (Tot.eps 𝒜 Q x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [totMapAlong_tmul, Tot.eps_tmul, Tot.eps_tmul, famMap_smul_along g u hu,
      show Tot.proj0 ℬ (g a) = g.f0 (Tot.proj0 𝒜 a) from Subtype.ext (g.map_proj 0 a).symm]
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- `totMapAlong` intertwines the Leibniz extensions of generator data that it intertwines on
the generators. -/
theorem totMapAlong_extend (θ : GenData 𝒜 Q) (θ' : GenData ℬ Q')
    (h : ∀ e, totMapAlong g u hu (θ.θ e) = θ'.θ (famMap u e)) (x : Tot 𝒜 Q) :
    totMapAlong g u hu (θ.extend x) = θ'.extend (totMapAlong g u hu x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [totMapAlong_tmul, GenData.extend_tmul, GenData.extend_tmul, map_add,
      totMapAlong_tmul, totMapAlong_smul, h, g.map_d, g.map_sigma]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Along

section Functorial

variable {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
  {Q' : ℤ → Type} [∀ p, AddCommGroup (Q' p)] [∀ p, Module (ℬ 0) (Q' p)]
  {Q'' : ℤ → Type} [∀ p, AddCommGroup (Q'' p)] [∀ p, Module (𝒞 0) (Q'' p)]

/-- `totMapAlong` along the identity, with the identity on generators, is the identity. -/
theorem totMapAlong_id (e : DgaHom 𝒜 𝒜) (he : ∀ a, e a = a) (u : ∀ p, Q p →+ Q p)
    (hu' : ∀ p x, u p x = x) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = e.f0 r • u p x)
    (x : Tot 𝒜 Q) : totMapAlong e u hu x = x := by
  induction x using Tot.induction_on with
  | ht a y => rw [totMapAlong_tmul, he, famMap_id u hu']
  | hadd x y hx hy => rw [map_add, hx, hy]

/-- `totMapAlong` is functorial. -/
theorem totMapAlong_comp (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ) (f' : DgaHom 𝒜 𝒞)
    (hgf : ∀ a, g (f a) = f' a) (u : ∀ p, Q p →+ Q' p) (v : ∀ p, Q' p →+ Q'' p)
    (w : ∀ p, Q p →+ Q'' p) (hvu : ∀ p x, v p (u p x) = w p x)
    (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = f.f0 r • u p x)
    (hv : ∀ p (r : ℬ 0) x, v p (r • x) = g.f0 r • v p x)
    (hw : ∀ p (r : 𝒜 0) x, w p (r • x) = f'.f0 r • w p x) (x : Tot 𝒜 Q) :
    totMapAlong g v hv (totMapAlong f u hu x) = totMapAlong f' w hw x := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [totMapAlong_tmul, totMapAlong_tmul, totMapAlong_tmul, hgf, famMap_famMap u v w hvu]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add]

end Functorial

end Cohesive
