-- FROZEN (gate 3, 26 Oct 2026; A10 definitions, in the main statement). Do not edit without approval.
import Cohesivemodules.Algebra.GeneratorsDef
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option linter.style.header false

/-!
# A10: cohesive modules from complexes (definitions)

Blueprint item A10. This file holds definitions the main statement depends on; it is to be
frozen at gate 3. Theorems about them (A10.a, the adjunction) stay in `Algebra/BaseChange.lean`.

For a ring map `ρ : R → A⁰` with `d ∘ ρ = 0` and a complex `W` of `R`-modules (a Mathlib
`CochainComplex (ModuleCat R) ℤ`), `A ⊗_R W` with `𝕏 = d ⊗ 1 + 1 ⊗ d_W` on the generators
`A⁰ ⊗_R W^p` (`QuasiCohesive.fromComplex`); cohesive if `W` is bounded with finitely generated
projective terms (`CohesiveModule.fromComplex`). [A, Assumption 6 (§7.2)].

Definitions: `RA0` with its instances, `RA0.of`, `RA0.un`, `FCGen` with its instances,
`FCGen.tmul`, `dW`, `fcι`, `fcθAux`, `fcθp`, `fcθ`, `fcGenData`, `QuasiCohesive.fromComplex`,
`IsBoundedFGProj`, `CohesiveModule.fromComplex`; together with the lemmas their constructions
need (balancedness, Leibniz rule, degree and flatness lemmas of `θ`) and their basic API.

## Deviations from the sources
* Left modules (conventions §3).
* A10 assumes `c = 0` (needed for `𝕏² = c`; the blueprint uses A10 only at `c = 0`).
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

/-! ## A10: cohesive modules from complexes

For a ring map `ρ : R → A⁰` with `d ∘ ρ = 0` and a complex `(W, d_W)` of `R`-modules, the module
`A ⊗_R W` with `𝕏 = d ⊗ 1 + 1 ⊗ d_W`, built on the generators `A⁰ ⊗_R W^p`: on generators,
`θ(α ⊗ w) = dα ⊗ (1 ⊗ w) + α·(1 ⊗ (1 ⊗ d_W w))`. -/

section FromComplex

open CategoryTheory

variable {R : Type} [CommRing R] (ρ : R →+* 𝒜 0)

/-- **A10** `A⁰` viewed as an `R`-algebra through `ρ` (a type synonym carrying the instance). -/
def RA0 (_ρ : R →+* 𝒜 0) : Type := 𝒜 0

/-- A10: the ring structure of `RA0 ρ` (that of `A⁰`). -/
instance : CommRing (RA0 ρ) := inferInstanceAs (CommRing (𝒜 0))

/-- A10: `A⁰` is an `R`-algebra through `ρ`. -/
instance : Algebra R (RA0 ρ) := RingHom.toAlgebra (ρ : R →+* 𝒜 0)

/-- A10: the identity `A⁰ → RA0 ρ`. -/
def RA0.of (α : 𝒜 0) : RA0 ρ := α

/-- A10: the identity `RA0 ρ → A⁰`. -/
def RA0.un (α : RA0 ρ) : 𝒜 0 := α

/-- A10: `r • α = ρ(r) α` in `RA0 ρ`. -/
theorem RA0.un_smul (r : R) (α : RA0 ρ) : RA0.un ρ (r • α) = ρ r * RA0.un ρ α := rfl

variable (W : CochainComplex (ModuleCat.{0} R) ℤ)

/-- **A10** The generators `A⁰ ⊗_R W^p` of `A ⊗_R W`. -/
def FCGen (p : ℤ) : Type := RA0 ρ ⊗[R] W.X p

/-- A10: the additive group of the generators. -/
instance (p : ℤ) : AddCommGroup (FCGen ρ W p) :=
  inferInstanceAs (AddCommGroup (RA0 ρ ⊗[R] W.X p))

/-- A10: the `A⁰`-module structure of the generators. -/
instance (p : ℤ) : Module (𝒜 0) (FCGen ρ W p) :=
  inferInstanceAs (Module (RA0 ρ) (RA0 ρ ⊗[R] W.X p))

/-- A10: `α ⊗ w` in the generators. -/
def FCGen.tmul {p : ℤ} (α : 𝒜 0) (w : W.X p) : FCGen ρ W p := RA0.of ρ α ⊗ₜ[R] w

/-- A10: the differential `d_W : W^p → W^{p+1}`. -/
def dW (p : ℤ) : W.X p →ₗ[R] W.X (p + 1) := (W.d p (p + 1)).hom

/-- A10: `d_W ∘ d_W = 0`. -/
theorem dW_dW (p : ℤ) (w : W.X p) : dW W (p + 1) (dW W p w) = 0 := by
  rw [dW, dW, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
  rfl

namespace FCGen

variable {ρ W}

/-- A10: `α ⊗ w` is additive in `w`. -/
theorem tmul_add {p : ℤ} (α : 𝒜 0) (w w' : W.X p) :
    FCGen.tmul ρ W α (w + w') = FCGen.tmul ρ W α w + FCGen.tmul ρ W α w' :=
  TensorProduct.tmul_add (RA0.of ρ α) w w'

/-- A10: `α ⊗ w` is additive in `α`. -/
theorem add_tmul {p : ℤ} (α α' : 𝒜 0) (w : W.X p) :
    FCGen.tmul ρ W (α + α') w = FCGen.tmul ρ W α w + FCGen.tmul ρ W α' w :=
  TensorProduct.add_tmul (RA0.of ρ α) (RA0.of ρ α') w

/-- A10: `γ • (α ⊗ w) = (γα) ⊗ w`. -/
theorem smul_tmul {p : ℤ} (γ α : 𝒜 0) (w : W.X p) :
    γ • FCGen.tmul ρ W α w = FCGen.tmul ρ W (γ * α) w :=
  TensorProduct.smul_tmul' (R := R) (RA0.of ρ γ) (RA0.of ρ α) w

/-- A10: `α ⊗ w = α • (1 ⊗ w)`. -/
theorem tmul_eq_smul {p : ℤ} (α : 𝒜 0) (w : W.X p) :
    FCGen.tmul ρ W α w = α • FCGen.tmul ρ W 1 w := by
  rw [smul_tmul, mul_one]

/-- A10: `α ⊗ (r w) = ρ(r)α ⊗ w`. -/
theorem tmul_smulR {p : ℤ} (α : 𝒜 0) (r : R) (w : W.X p) :
    FCGen.tmul ρ W α (r • w) = FCGen.tmul ρ W (ρ r * α) w :=
  (TensorProduct.smul_tmul (R := R) r (RA0.of ρ α) w).symm

/-- A10: induction on the generators. -/
theorem induction_on {p : ℤ} {C : FCGen ρ W p → Prop} (x : FCGen ρ W p)
    (ht : ∀ α w, C (FCGen.tmul ρ W α w)) (hadd : ∀ x y, C x → C y → C (x + y)) : C x :=
  TensorProduct.inductionOn (R := R) (M := RA0 ρ) (N := W.X p) x ht hadd

end FCGen

/-- A10: the generator `1 ⊗ (1 ⊗ w)` of degree `p` in `A ⊗_{A⁰} ⨁ (A⁰ ⊗_R W)`. -/
def fcι {p : ℤ} (w : W.X p) : Tot 𝒜 (FCGen ρ W) :=
  Tot.tmul 𝒜 (FCGen ρ W) 1 (lof (𝒜 0) ℤ (FCGen ρ W) p (FCGen.tmul ρ W 1 w))

/-- A10: `1 ⊗ (1 ⊗ r w) = ρ(r)·(1 ⊗ (1 ⊗ w))`. -/
theorem fcι_smulR {p : ℤ} (r : R) (w : W.X p) :
    fcι ρ W (r • w) = ((ρ r : 𝒜 0) : A) • fcι ρ W w := by
  rw [fcι, fcι, FCGen.tmul_smulR, ← FCGen.smul_tmul, map_smul, Tot.tmul_smul0, one_mul,
    Tot.tmul_eq_smul]

/-- A10: `1 ⊗ (1 ⊗ 0) = 0`. -/
theorem fcι_zero {p : ℤ} : fcι ρ W (0 : W.X p) = 0 := by
  rw [fcι, show FCGen.tmul ρ W 1 (0 : W.X p) = 0 from TensorProduct.tmul_zero _ _, map_zero,
    Tot.tmul_zero]

/-- A10: `1 ⊗ (1 ⊗ w)` is additive in `w`. -/
theorem fcι_add {p : ℤ} (w w' : W.X p) : fcι ρ W (w + w') = fcι ρ W w + fcι ρ W w' := by
  rw [fcι, fcι, fcι, FCGen.tmul_add, map_add, Tot.tmul_add]

/-- A10: `1 ⊗ (1 ⊗ w)` lies in total degree `p`. -/
theorem fcι_mem {p : ℤ} (w : W.X p) : fcι ρ W w ∈ totDeg 𝒜 (FCGen ρ W) p := by
  have := tmul_mem_totDeg (Q := FCGen ρ W) (SetLike.GradedOne.one_mem (A := 𝒜))
    (FCGen.tmul ρ W 1 w)
  rwa [zero_add] at this

/-- The bi-additive map `(α, w) ↦ dα ⊗ (1 ⊗ w) + α·(1 ⊗ (1 ⊗ d_W w))` on degree `p`. -/
def fcθAux (p : ℤ) : RA0 ρ →+ W.X p →+ Tot 𝒜 (FCGen ρ W) :=
  AddMonoidHom.mk'
    (fun α => AddMonoidHom.mk'
      (fun w => Tot.tmul 𝒜 (FCGen ρ W) (GCDga.d (𝒜 := 𝒜) (RA0.un ρ α : A))
          (lof (𝒜 0) ℤ (FCGen ρ W) p (FCGen.tmul ρ W 1 w)) +
        (RA0.un ρ α : A) • fcι ρ W (dW W p w))
      (fun w w' => by
        rw [FCGen.tmul_add, map_add, Tot.tmul_add, map_add, fcι, fcι, fcι, FCGen.tmul_add,
          map_add, Tot.tmul_add, smul_add]
        abel))
    (fun α α' => AddMonoidHom.ext fun w => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [show RA0.un ρ (α + α') = RA0.un ρ α + RA0.un ρ α' from rfl, Submodule.coe_add,
        map_add, Tot.add_tmul, add_smul]
      abel)

/-- The bi-additive map is `R`-balanced (uses `d ∘ ρ = 0`). -/
theorem fcθAux_balanced (hρ : ∀ r, GCDga.d (𝒜 := 𝒜) (ρ r : A) = 0) (p : ℤ) (r : R)
    (α : RA0 ρ) (w : W.X p) : fcθAux ρ W p (r • α) w = fcθAux ρ W p α (r • w) := by
  simp only [fcθAux, AddMonoidHom.mk'_apply]
  rw [RA0.un_smul, show ((ρ r * RA0.un ρ α : 𝒜 0) : A) = (ρ r : A) * (RA0.un ρ α : A) from rfl,
    GCDga.leibniz_zero 𝒜 (ρ r).2, hρ, zero_mul, zero_add, map_smul, fcι_smulR,
    FCGen.tmul_smulR, ← FCGen.smul_tmul, map_smul, Tot.tmul_smul0, smul_smul,
    GCDga.central 𝒜 (ρ r).2, GCDga.central 𝒜 (ρ r).2 (RA0.un ρ α : A)]

variable {ρ} (hρ : ∀ r, GCDga.d (𝒜 := 𝒜) (ρ r : A) = 0)

/-- **A10** `θ` on the degree-`p` generators `A⁰ ⊗_R W^p`. -/
def fcθp (p : ℤ) : FCGen ρ W p →+ Tot 𝒜 (FCGen ρ W) :=
  TensorProduct.liftAddHom (R := R) (fcθAux ρ W p) (fcθAux_balanced ρ W hρ p)

/-- A10: `θ(α ⊗ w) = dα ⊗ (1 ⊗ w) + α·(1 ⊗ (1 ⊗ d_W w))`. -/
theorem fcθp_tmul (p : ℤ) (α : 𝒜 0) (w : W.X p) :
    fcθp W hρ p (FCGen.tmul ρ W α w) =
      Tot.tmul 𝒜 (FCGen ρ W) (GCDga.d (𝒜 := 𝒜) (α : A))
          (lof (𝒜 0) ℤ (FCGen ρ W) p (FCGen.tmul ρ W 1 w)) +
        (α : A) • fcι ρ W (dW W p w) := rfl

/-- **A10** The generator data `θ` of `A ⊗_R W`. -/
def fcθ : (⨁ p, FCGen ρ W p) →+ Tot 𝒜 (FCGen ρ W) := DirectSum.toAddMonoid (fcθp W hρ)

/-- A10: `θ` on a homogeneous generator. -/
theorem fcθ_of (p : ℤ) (x : FCGen ρ W p) :
    fcθ W hρ (DirectSum.of (FCGen ρ W) p x) = fcθp W hρ p x :=
  DirectSum.toAddMonoid_of _ p x

/-- A10: `α ⊗ w = α • (1 ⊗ w)` in the direct sum of the generators. -/
theorem fc_of_tmul (p : ℤ) (α : 𝒜 0) (w : W.X p) :
    DirectSum.of (FCGen ρ W) p (FCGen.tmul ρ W α w) =
      α • lof (𝒜 0) ℤ (FCGen ρ W) p (FCGen.tmul ρ W 1 w) := by
  rw [← map_smul, FCGen.smul_tmul, mul_one]
  rfl

/-- A10: `θ(1 ⊗ w) = 1 ⊗ d_W w`. -/
theorem fcθ_one (p : ℤ) (w : W.X p) :
    fcθ W hρ (lof (𝒜 0) ℤ (FCGen ρ W) p (FCGen.tmul ρ W 1 w)) = fcι ρ W (dW W p w) := by
  change fcθ W hρ (DirectSum.of _ p _) = _
  rw [fcθ_of, fcθp_tmul, show ((1 : 𝒜 0) : A) = 1 from rfl, GCDga.d_one, Tot.zero_tmul,
    zero_add, one_smul]

/-- A10: the Leibniz rule of `θ` over `A⁰`. -/
theorem fcθ_leibniz (γ : 𝒜 0) (e : ⨁ p, FCGen ρ W p) :
    fcθ W hρ (γ • e) = Tot.tmul 𝒜 _ (GCDga.d (𝒜 := 𝒜) γ) e + (γ : A) • fcθ W hρ e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    induction x using FCGen.induction_on with
    | ht α w =>
      change fcθ W hρ (γ • DirectSum.of _ p (FCGen.tmul ρ W (RA0.un ρ α) w)) = _
      rw [show γ • DirectSum.of (FCGen ρ W) p (FCGen.tmul ρ W (RA0.un ρ α) w) =
          DirectSum.of (FCGen ρ W) p (γ • FCGen.tmul ρ W (RA0.un ρ α) w) from
          (map_smul (DirectSum.lof (𝒜 0) ℤ (FCGen ρ W) p) γ _).symm,
        FCGen.smul_tmul, fcθ_of, fcθ_of, fcθp_tmul, fcθp_tmul,
        show ((γ * RA0.un ρ α : 𝒜 0) : A) = (γ : A) * (RA0.un ρ α : A) from rfl,
        GCDga.leibniz_zero 𝒜 γ.2, Tot.add_tmul, smul_add, Tot.smul_tmul, mul_smul,
        fc_of_tmul, Tot.tmul_smul0]
      abel
    | hadd x y hx hy =>
      rw [(DirectSum.of (FCGen ρ W) p).map_add, smul_add, map_add, hx, hy, map_add,
        Tot.tmul_add, smul_add]
      abel
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add, Tot.tmul_add, smul_add]
    abel

/-- **A10** The generator data of `A ⊗_R W`. -/
def fcGenData : GenData 𝒜 (FCGen ρ W) where
  θ := fcθ W hρ
  leibniz := fcθ_leibniz W hρ

/-- A10: `θ` has total degree `1`. -/
theorem fcθ_mem (p : ℤ) (x : FCGen ρ W p) :
    fcθ W hρ (lof (𝒜 0) ℤ (FCGen ρ W) p x) ∈ totDeg 𝒜 (FCGen ρ W) (p + 1) := by
  induction x using FCGen.induction_on with
  | ht α w =>
    change fcθ W hρ (DirectSum.of _ p _) ∈ _
    rw [fcθ_of, fcθp_tmul]
    refine add_mem ?_ ?_
    · have := tmul_mem_totDeg (Q := FCGen ρ W) (GCDga.d_mem_one 𝒜 (RA0.un ρ α).2)
        (FCGen.tmul ρ W 1 w)
      rwa [add_comm] at this
    · have := smul_mem_totDeg (RA0.un ρ α).2 (fcι_mem ρ W (dW W p w))
      rwa [zero_add] at this
  | hadd x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/-- A10: `𝕏(1 ⊗ (1 ⊗ w)) = 1 ⊗ (1 ⊗ d_W w)`. -/
theorem fc_extend_fcι {p : ℤ} (w : W.X p) :
    (fcGenData W hρ).extend (fcι ρ W w) = fcι ρ W (dW W p w) := by
  rw [fcι, GenData.extend_tmul_one]
  exact fcθ_one W hρ p w

/-- A10: `A ⊗_R W` is flat on its generators (`c = 0` is needed: `𝕏² = 0`). -/
theorem fc_flat (hc : GCDga.c (𝒜 := 𝒜) = 0) (e : ⨁ p, FCGen ρ W p) :
    (fcGenData W hρ).extend ((fcGenData W hρ).θ e) =
      GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 _ 1 e := by
  rw [hc, zero_smul]
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    induction x using FCGen.induction_on with
    | ht α w =>
      change (fcGenData W hρ).extend (fcθ W hρ (DirectSum.of _ p
        (FCGen.tmul ρ W (RA0.un ρ α) w))) = 0
      have hα1 := GCDga.d_mem_one 𝒜 (RA0.un ρ α).2
      rw [fc_of_tmul, fcθ_leibniz, fcθ_one, map_add, Tot.tmul_eq_smul,
        (fcGenData W hρ).extend_leibniz hα1, (fcGenData W hρ).extend_leibniz (RA0.un ρ α).2,
        GenData.extend_tmul_one, fc_extend_fcι, dW_dW, GCDga.d_d, zero_smul, zero_add,
        show (fcGenData W hρ).θ = fcθ W hρ from rfl, fcθ_one, Int.negOnePow_one,
        Int.negOnePow_zero, Units.neg_smul, one_smul, one_smul, fcι_zero, smul_zero, add_zero,
        neg_add_cancel]
    | hadd x y hx hy =>
      rw [(DirectSum.of (FCGen ρ W) p).map_add, map_add, map_add, hx, hy, add_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- **A10** The quasi-cohesive module `A ⊗_R W` with `𝕏 = d ⊗ 1 + 1 ⊗ d_W`, for a ring map
`ρ : R → A⁰` with `d ∘ ρ = 0` and a complex `W` of `R`-modules, over a dga with `c = 0`.
Generators `A⁰ ⊗_R W^p`; on them `𝕏(α ⊗ w) = dα ⊗ w + α·(1 ⊗ d_W w)`. [A, Assumption 6
(§7.2): the module `(𝒜 ⊗_R W, d ⊗ 1 + 1 ⊗ d)`], [B, proof of Lemma 4.1.5] (the modules of the
local lifting condition LL / H2). ⚠ Requires `c = 0` (for `c ≠ 0`,
`𝕏² = 0 ≠ c`); the blueprint uses A10 only at `c = 0`. -/
def QuasiCohesive.fromComplex (hc : GCDga.c (𝒜 := 𝒜) = 0) : QuasiCohesive 𝒜 :=
  QuasiCohesive.ofGenerators (FCGen ρ W) (fcGenData W hρ) (fcθ_mem W hρ) (fc_flat W hρ hc)

/-- A10: the operator of `A ⊗_R W` is the extension of `θ`. -/
theorem fromComplex_X_apply (hc : GCDga.c (𝒜 := 𝒜) = 0) (x : Tot 𝒜 (FCGen ρ W)) :
    (QuasiCohesive.fromComplex W hρ hc).X x = (fcGenData W hρ).extend x := rfl

variable (R) in
/-- **A10** `W` is a bounded complex of finitely generated projective `R`-modules: `W^p = 0`
outside a bounded range of degrees, each `W^p` finitely generated and projective. -/
structure IsBoundedFGProj (W : CochainComplex (ModuleCat.{0} R) ℤ) : Prop where
  /-- `W^p = 0` outside a bounded range of degrees. -/
  bounded : ∃ a b : ℤ, ∀ p, (p < a ∨ b < p) → Subsingleton (W.X p)
  /-- Each `W^p` is finitely generated. -/
  finite : ∀ p, Module.Finite R (W.X p)
  /-- Each `W^p` is projective. -/
  projective : ∀ p, Module.Projective R (W.X p)

/-- **A10** For a bounded complex `W` of finitely generated projective `R`-modules, `A ⊗_R W`
is cohesive: `A⁰ ⊗_R W^p` is finitely generated projective over `A⁰` and vanishes where `W^p`
does. [A, Assumption 6 (§7.2)]. ⚠ Requires `c = 0`. -/
def CohesiveModule.fromComplex (hc : GCDga.c (𝒜 := 𝒜) = 0) (hW : IsBoundedFGProj R W) :
    CohesiveModule 𝒜 where
  toQuasiCohesive := QuasiCohesive.fromComplex W hρ hc
  bounded := by
    obtain ⟨a, b, h⟩ := hW.bounded
    refine ⟨a, b, fun p hp => ?_⟩
    have := h p hp
    exact inferInstanceAs (Subsingleton (RA0 ρ ⊗[R] W.X p))
  finite p := by
    have := hW.finite p
    exact inferInstanceAs (Module.Finite (RA0 ρ) (RA0 ρ ⊗[R] W.X p))
  projective p := by
    have := hW.projective p
    exact inferInstanceAs (Module.Projective (RA0 ρ) (RA0 ρ ⊗[R] W.X p))

end FromComplex

end Cohesive

end
