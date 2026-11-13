-- FROZEN (gate 4, 29 Oct 2026; A9 restriction of base changes, in the main statement). No edits.
import Cohesivemodules.Algebra.BaseChangeDef

set_option linter.style.header false

/-!
# A9: restriction between base changes (definitions)

Used by C1 (blueprint §4): the restriction maps of the sheaf `α(M)` are restrictions between
base changes of `M` to smaller opens. This file holds definitions the main statement depends on
(through J); it is to be frozen at gate 4. Theorems about them go in `Comparison/` files.

For maps of (possibly curved) dgas `f : A → B`, `f' : A → C`, `g : B → C` with `g ∘ f = f'`
pointwise (`hgf`), and a family `Q` of `A⁰`-modules:
* `bcGenRes g f f' hgf Q p : B⁰ ⊗_{A⁰} Q^p → C⁰ ⊗_{A⁰} Q^p`, `β ⊗ q ↦ g(β) ⊗ q`;
* `bcTotRes g f f' hgf Q : B ⊗_{B⁰} ⨁(B⁰ ⊗_{A⁰} Q) → C ⊗_{C⁰} ⨁(C⁰ ⊗_{A⁰} Q)`,
  `b ⊗ e ↦ g(b) ⊗ (⨁ bcGenRes) e`.
Both are defined in one step (`TensorProduct.liftAddHom`), so that their values on pure tensors
are `rfl` (`bcGenRes_tmul`, `bcTotRes_tmul`), as for `bcF`.

## Deviations
* `g ∘ f = f'` is a pointwise hypothesis, not an equality of `DgaHom`s: `BCGen f` depends on `f`
  through the `A⁰`-algebra structure of `f.B0`, so `f.comp g` and `f'` give different (equal up to
  `bcGenRes`) generator types (prototype P8, finding 5).
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]

variable (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ) (f' : DgaHom 𝒜 𝒞) (hgf : ∀ a, g (f a) = f' a)
  (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- The bi-additive map `(β, q) ↦ g(β) ⊗ q` on degree `p`. -/
def bcGenResAux (p : ℤ) : f.B0 →+ Q p →+ BCGen f' Q p :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk' (fun q => BCGen.tmul f' Q (g.f0 (show ℬ 0 from β)) q)
      (fun q q' => BCGen.tmul_add _ q q'))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      exact (congrArg (BCGen.tmul f' Q · q) (map_add g.f0 _ _)).trans (BCGen.add_tmul _ _ q))

include hgf in
/-- `bcGenResAux` is `A⁰`-balanced (uses `g ∘ f = f'` in degree `0`). -/
theorem bcGenResAux_balanced (p : ℤ) (r : 𝒜 0) (β : f.B0) (q : Q p) :
    bcGenResAux g f f' Q p (r • β) q = bcGenResAux g f f' Q p β (r • q) := by
  have h0 : g.f0 (f.f0 r) = f'.f0 r := Subtype.ext (hgf r)
  have h1 : (show ℬ 0 from (r • β : f.B0)) = f.f0 r * (show ℬ 0 from β) := rfl
  show BCGen.tmul f' Q (g.f0 (show ℬ 0 from (r • β : f.B0))) q =
    BCGen.tmul f' Q (g.f0 (show ℬ 0 from β)) (r • q)
  rw [h1, map_mul, h0, BCGen.tmul_eq_smul (g.f0 (show ℬ 0 from β)) (r • q), BCGen.tmul_smul0,
    smul_smul, BCGen.smul_tmul, mul_one, mul_comm]

/-- **A9 (restriction of generators).** `B⁰ ⊗_{A⁰} Q^p → C⁰ ⊗_{A⁰} Q^p`, `β ⊗ q ↦ g(β) ⊗ q`,
for `g ∘ f = f'`. -/
def bcGenRes (p : ℤ) : BCGen f Q p →+ BCGen f' Q p :=
  TensorProduct.liftAddHom (R := 𝒜 0) (bcGenResAux g f f' Q p)
    (bcGenResAux_balanced g f f' hgf Q p)

/-- `bcGenRes` on pure tensors (rfl). -/
theorem bcGenRes_tmul (p : ℤ) (β : ℬ 0) (q : Q p) :
    bcGenRes g f f' hgf Q p (BCGen.tmul f Q β q) = BCGen.tmul f' Q (g.f0 β) q := rfl

/-- The bi-additive map `(b, e) ↦ g(b) ⊗ (⨁ bcGenRes) e`. -/
def bcTotResAux : B →+ (⨁ p, BCGen f Q p) →+ Tot 𝒞 (BCGen f' Q) :=
  AddMonoidHom.mk'
    (fun b => AddMonoidHom.mk'
      (fun e => Tot.tmul 𝒞 _ (g b) (DirectSum.map (bcGenRes g f f' hgf Q) e))
      (fun e e' => by rw [map_add, Tot.tmul_add]))
    (fun b b' => AddMonoidHom.ext fun e => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, g.map_add', Tot.add_tmul])

/-- `bcGenRes` is `g₀`-semilinear. -/
theorem bcGenRes_smul (p : ℤ) (γ : ℬ 0) (x : BCGen f Q p) :
    bcGenRes g f f' hgf Q p (γ • x) = g.f0 γ • bcGenRes g f f' hgf Q p x := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [BCGen.smul_tmul, bcGenRes_tmul, bcGenRes_tmul, BCGen.smul_tmul, map_mul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `DirectSum.map bcGenRes` is `g₀`-semilinear. -/
theorem map_bcGenRes_smul (γ : ℬ 0) (e : ⨁ p, BCGen f Q p) :
    DirectSum.map (bcGenRes g f f' hgf Q) (γ • e) =
      g.f0 γ • DirectSum.map (bcGenRes g f f' hgf Q) e := by
  ext i
  simp only [DirectSum.map_apply, DirectSum.smul_apply]
  exact bcGenRes_smul g f f' hgf Q i γ (e i)

/-- `bcTotResAux` is `B⁰`-balanced (`g` is a ring map and `B⁰` is central). -/
theorem bcTotResAux_balanced (r : ℬ 0) (b : B) (e : ⨁ p, BCGen f Q p) :
    bcTotResAux g f f' hgf Q (r • b) e = bcTotResAux g f f' hgf Q b (r • e) := by
  show Tot.tmul 𝒞 _ (g (r • b)) (DirectSum.map (bcGenRes g f f' hgf Q) e) =
    Tot.tmul 𝒞 _ (g b) (DirectSum.map (bcGenRes g f f' hgf Q) (r • e))
  rw [map_bcGenRes_smul, Tot.tmul_smul0, GCDga.smul0_def, g.map_mul', DgaHom.coe_f0]
  exact congrArg (Tot.tmul 𝒞 _ · _) (GCDga.central 𝒞 (g.map_mem r.2) _)

/-- **A9 (restriction of total modules).** `B ⊗_{B⁰} ⨁(B⁰ ⊗_{A⁰} Q) → C ⊗_{C⁰} ⨁(C⁰ ⊗_{A⁰} Q)`,
`b ⊗ e ↦ g(b) ⊗ (⨁ bcGenRes) e`, for `g ∘ f = f'`. For `Q = M.Q`, a map
`Tot(f^*M) → Tot(f'^*M)` (used for the restriction maps of `α(M)`, C1). -/
def bcTotRes : Tot ℬ (BCGen f Q) →+ Tot 𝒞 (BCGen f' Q) :=
  TensorProduct.liftAddHom (R := ℬ 0) (bcTotResAux g f f' hgf Q)
    (bcTotResAux_balanced g f f' hgf Q)

/-- `bcTotRes` on pure tensors (rfl). -/
theorem bcTotRes_tmul (b : B) (e : ⨁ p, BCGen f Q p) :
    bcTotRes g f f' hgf Q (Tot.tmul ℬ _ b e) =
      Tot.tmul 𝒞 _ (g b) (DirectSum.map (bcGenRes g f f' hgf Q) e) := rfl

end Cohesive
