-- FROZEN (gate 4, 29 Oct 2026; A9 base change of maps, in the main statement). Do not edit.
import Cohesivemodules.Algebra.GenHomDef
import Cohesivemodules.Algebra.BaseChangeDef

set_option linter.style.header false

/-!
# A9: base change of morphisms (definitions)

Blueprint item A9 (definitions only). These definitions enter the main statement through the
functor J (C1), which acts on morphisms by base change along the restriction maps; this file is
to be frozen at gate 4. Theorems about them (`bcHomL_bcF`, `bcHomL_δ`, `bcHomL_comp`, …) stay in
`Algebra/BaseChange.lean`.

* `bcGenAux`, `bcGenP`, `bcGen`: the base change `ψ'(β ⊗ q) = β·F(ψ(q))` of a generator map,
  with `bcGen_mem`.
* `bcGenHom`, `bcHomL`: the base change `f^*φ` of `φ ∈ Hom^n(M₁, M₂)`, with `bcHomL_mem` and
  `bcHomL_tmul`.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

variable (f : DgaHom 𝒜 ℬ)

/-! ## A9: functoriality on Hom complexes -/

section Functoriality

variable {M₁ M₂ : QuasiCohesive 𝒜} (n : ℤ)

/-- The bi-additive map `(β, q) ↦ β·F(ψ(q))` on degree `p`, for a generator map `ψ`. -/
def bcGenAux (ψ : GenHom M₁ M₂ n) (p : ℤ) : f.B0 →+ M₁.Q p →+ Tot ℬ (BCGen f M₂.Q) :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk' (fun q => toB f β • bcF f M₂.Q (ψ.1 (lof (𝒜 0) ℤ M₁.Q p q)))
      (fun q q' => by rw [map_add, map_add, map_add, smul_add]))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, toB_add, add_smul])

/-- **A9** The base change of a generator map on degree `p`. -/
def bcGenP (ψ : GenHom M₁ M₂ n) (p : ℤ) : BCGen f M₁.Q p →+ Tot ℬ (BCGen f M₂.Q) :=
  TensorProduct.liftAddHom (R := 𝒜 0) (bcGenAux f n ψ p) fun r β q => by
    show toB f (r • β) • bcF f M₂.Q (ψ.1 _) =
      toB f β • bcF f M₂.Q (ψ.1 (lof (𝒜 0) ℤ M₁.Q p (r • q)))
    rw [Algebra.smul_def, toB_mul, toB_algebraMap, map_smul, ψ.2.1 r, bcF_smul, ← mul_smul,
      GCDga.central ℬ (f.map_mem r.2)]

/-- A9: `ψ'(β ⊗ q) = β·F(ψ(q))`. -/
theorem bcGenP_tmul (ψ : GenHom M₁ M₂ n) (p : ℤ) (β : ℬ 0) (q : M₁.Q p) :
    bcGenP f n ψ p (BCGen.tmul f M₁.Q β q) =
      (β : B) • bcF f M₂.Q (ψ.1 (lof (𝒜 0) ℤ M₁.Q p q)) := rfl

/-- **A9** The base change `ψ'` of a generator map. -/
def bcGen (ψ : GenHom M₁ M₂ n) : (⨁ p, BCGen f M₁.Q p) →+ Tot ℬ (BCGen f M₂.Q) :=
  DirectSum.toAddMonoid (bcGenP f n ψ)

/-- A9: `ψ'` on a homogeneous generator. -/
theorem bcGen_of (ψ : GenHom M₁ M₂ n) (p : ℤ) (x : BCGen f M₁.Q p) :
    bcGen f n ψ (DirectSum.of (BCGen f M₁.Q) p x) = bcGenP f n ψ p x :=
  DirectSum.toAddMonoid_of _ p x

/-- A9: `ψ'(ι e) = F(ψ(e))`. -/
theorem bcGen_bcι (ψ : GenHom M₁ M₂ n) (e : ⨁ p, M₁.Q p) :
    bcGen f n ψ (bcι f M₁.Q e) = bcF f M₂.Q (ψ.1 e) := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p q =>
    rw [show DirectSum.of M₁.Q p q = lof (𝒜 0) ℤ M₁.Q p q from rfl, bcι_lof,
      show lof (ℬ 0) ℤ (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q 1 q) =
        DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q 1 q) from rfl, bcGen_of, bcGenP_tmul,
      show ((1 : ℬ 0) : B) = 1 from rfl, one_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- A9: `ψ'` is `B⁰`-linear. -/
theorem bcGen_smul (ψ : GenHom M₁ M₂ n) (γ : ℬ 0) (e : ⨁ p, BCGen f M₁.Q p) :
    bcGen f n ψ (γ • e) = (γ : B) • bcGen f n ψ e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    induction x using BCGen.induction_on with
    | ht β q =>
      rw [show γ • DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q β q) =
          DirectSum.of (BCGen f M₁.Q) p (γ • BCGen.tmul f M₁.Q β q) from
          (map_smul (DirectSum.lof (ℬ 0) ℤ (BCGen f M₁.Q) p) γ _).symm, BCGen.smul_tmul,
        bcGen_of, bcGen_of, bcGenP_tmul, bcGenP_tmul,
        show ((γ * β : ℬ 0) : B) = (γ : B) * β from rfl, mul_smul]
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f M₁.Q) p).map_add, smul_add, map_add, hx, hy, map_add,
        smul_add]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- A9: `ψ'` has degree `n`. -/
theorem bcGen_deg (ψ : GenHom M₁ M₂ n) (p : ℤ) (x : BCGen f M₁.Q p) :
    bcGen f n ψ (lof (ℬ 0) ℤ (BCGen f M₁.Q) p x) ∈ totDeg ℬ (BCGen f M₂.Q) (p + n) := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [show lof (ℬ 0) ℤ (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q β q) =
      DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q β q) from rfl, bcGen_of, bcGenP_tmul]
    have := smul_mem_totDeg β.2 (bcF_mem_totDeg f M₂.Q (ψ.2.2 p q))
    rwa [zero_add] at this
  | hadd x y hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

/-- A9: `ψ'` is a generator map of degree `n` for the base changes. -/
theorem bcGen_mem (ψ : GenHom M₁ M₂ n) :
    bcGen f n ψ ∈ GenHom (M₁.baseChange f) (M₂.baseChange f) n :=
  ⟨bcGen_smul f n ψ, bcGen_deg f n ψ⟩

/-- The base-changed generator map as an element of `GenHom` of the base changes. -/
def bcGenHom (φ : Hom M₁ M₂ n) : GenHom (M₁.baseChange f) (M₂.baseChange f) n :=
  ⟨bcGen f n (restrictGen n φ), bcGen_mem f n _⟩

/-- **A9** Base change of morphisms: `φ ∈ Hom^n(M₁, M₂)` gives
`f^*φ : B ⊗ ⨁(B⁰ ⊗ Q₁) → B ⊗ ⨁(B⁰ ⊗ Q₂)`, `(f^*φ)(b ⊗ m) = (-1)^{n|b|} b·φ(m)`. -/
def bcHomL (φ : Hom M₁ M₂ n) : Tot ℬ (BCGen f M₁.Q) →ₗ[k] Tot ℬ (BCGen f M₂.Q) :=
  extGen n (bcGenHom f n φ)

/-- A9: `f^*φ ∈ Hom^n(f^*M₁, f^*M₂)`. -/
theorem bcHomL_mem (φ : Hom M₁ M₂ n) :
    bcHomL f n φ ∈ Hom (M₁.baseChange f) (M₂.baseChange f) n :=
  extGen_mem n (bcGenHom f n φ)

/-- A9: `f^*φ` on pure tensors. -/
theorem bcHomL_tmul (φ : Hom M₁ M₂ n) (b : B) (e' : ⨁ p, BCGen f M₁.Q p) :
    bcHomL f n φ (Tot.tmul ℬ (BCGen f M₁.Q) b e') =
      GCDga.twist ℬ n b • bcGen f n (restrictGen n φ) e' := rfl

end Functoriality

end Cohesive
