import Cohesivemodules.Algebra.BaseChangeHomDef
import Cohesivemodules.Algebra.BaseChange

set_option linter.style.header false

/-!
# A9: extension along a base change (the base-change adjunction on Hom)

Used by C4 (blueprint §4, the map `Ψ`). For a map of (possibly curved) dgas `f : A → B` and
quasi-cohesive modules
`M₁`, `M₂` over `A`, a `k`-linear map `χ : Tot(M₁) → Tot(f^*M₂)` of degree `n` that is
semilinear along `f` (`χ(a·x) = (-1)^{n|a|} f(a)·χ(x)`; `HomAlong f n`) extends uniquely to a
degree-`n` map `extAlong χ : Tot(f^*M₁) → Tot(f^*M₂)` with `extAlong χ ∘ F = χ`
(`F = bcF`): on generators `β ⊗ q ↦ β·χ(1 ⊗ q)`, extended by A4.c (`extGen`). This is the
base-change adjunction `Hom^n_B(f^*M₁, f^*M₂) ≅ Hom^n_{A, along f}(M₁, f^*M₂)`.

Not part of the main statement; not frozen.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

variable (f : DgaHom 𝒜 ℬ) (M₁ M₂ : QuasiCohesive 𝒜)

/-- Degree-`n` `k`-linear maps `Tot(M₁) → Tot(f^*M₂)` semilinear along `f`:
`χ(a·x) = (-1)^{n|a|} f(a)·χ(x)` for homogeneous `a`. -/
def HomAlong (n : ℤ) : Submodule k (M₁.T →ₗ[k] (M₂.baseChange f).T) where
  carrier := {χ | (∀ {m : ℤ} {x : M₁.T}, x ∈ totDeg 𝒜 M₁.Q m →
      χ x ∈ totDeg ℬ (M₂.baseChange f).Q (m + n)) ∧
    ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : M₁.T, χ (a • x) = (n * p).negOnePow • f a • χ x}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun hx => add_mem (hφ.1 hx) (hψ.1 hx), fun ha x => by
      simp only [LinearMap.add_apply, hφ.2 ha, hψ.2 ha, smul_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => by simp⟩
  smul_mem' := fun r φ hφ =>
    ⟨fun hx => Submodule.smul_mem _ r (hφ.1 hx), fun ha x => by
      simp only [LinearMap.smul_apply, hφ.2 ha]
      rw [smul_comm r, smul_comm r]⟩

variable {f M₁ M₂}

/-- The bi-additive map `(β, q) ↦ β·χ(1 ⊗ q)` on degree `p`. -/
def extAlongAux {n : ℤ} (χ : HomAlong f M₁ M₂ n) (p : ℤ) :
    f.B0 →+ M₁.Q p →+ (M₂.baseChange f).T :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk'
      (fun q => toB f β • χ.1 (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p q)))
      (fun q q' => by rw [map_add, Tot.tmul_add, map_add, smul_add]))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, toB_add, add_smul])

/-- `extAlongAux` is `A⁰`-balanced. -/
theorem extAlongAux_balanced {n : ℤ} (χ : HomAlong f M₁ M₂ n) (p : ℤ) (r : 𝒜 0) (β : f.B0)
    (q : M₁.Q p) : extAlongAux χ p (r • β) q = extAlongAux χ p β (r • q) := by
  show toB f (r • β) • χ.1 (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p q)) =
    toB f β • χ.1 (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p (r • q)))
  have h1 : Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p (r • q)) =
      (r : A) • Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p q) := by
    rw [← Tot.smul0_eq, map_smul (lof (𝒜 0) ℤ M₁.Q p) r q]
    exact map_smul (Tot.oneTmul 𝒜 M₁.Q) r _
  rw [h1, χ.2.2 r.2, mul_zero, Algebra.smul_def, toB_mul, toB_algebraMap, Int.negOnePow_zero,
    one_smul, ← mul_smul, GCDga.central ℬ (f.map_mem r.2)]

/-- The generator map of `extAlong χ` on degree `p`: `β ⊗ q ↦ β·χ(1 ⊗ q)`. -/
def extAlongP {n : ℤ} (χ : HomAlong f M₁ M₂ n) (p : ℤ) :
    BCGen f M₁.Q p →+ (M₂.baseChange f).T :=
  TensorProduct.liftAddHom (R := 𝒜 0) (extAlongAux χ p) (extAlongAux_balanced χ p)

/-- The generator map of `extAlong χ`. -/
def extAlongGen {n : ℤ} (χ : HomAlong f M₁ M₂ n) :
    (⨁ p, BCGen f M₁.Q p) →+ (M₂.baseChange f).T :=
  DirectSum.toAddMonoid (extAlongP χ)

/-- `extAlongGen χ` on a homogeneous pure tensor `β ⊗ q`. -/
private theorem extAlongGen_of {n : ℤ} (χ : HomAlong f M₁ M₂ n) (p : ℤ) (β : ℬ 0)
    (q : M₁.Q p) :
    extAlongGen χ (DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q β q)) =
      (β : B) • χ.1 (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p q)) :=
  DirectSum.toAddMonoid_of _ p _

/-- `extAlongGen χ` is `B⁰`-linear. -/
private theorem extAlongGen_smul {n : ℤ} (χ : HomAlong f M₁ M₂ n) (γ : ℬ 0)
    (e : ⨁ p, BCGen f M₁.Q p) : extAlongGen χ (γ • e) = (γ : B) • extAlongGen χ e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    induction x using BCGen.induction_on with
    | ht β q =>
      rw [show γ • DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q β q) =
          DirectSum.of (BCGen f M₁.Q) p (γ • BCGen.tmul f M₁.Q β q) from
          (map_smul (DirectSum.lof (ℬ 0) ℤ (BCGen f M₁.Q) p) γ _).symm, BCGen.smul_tmul,
        extAlongGen_of, extAlongGen_of, show ((γ * β : ℬ 0) : B) = (γ : B) * β from rfl,
        mul_smul]
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f M₁.Q) p).map_add, smul_add, map_add, hx, hy, map_add,
        smul_add]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `extAlongGen χ` has degree `n`. -/
private theorem extAlongGen_deg {n : ℤ} (χ : HomAlong f M₁ M₂ n) (p : ℤ)
    (x : BCGen f M₁.Q p) :
    extAlongGen χ (lof (ℬ 0) ℤ (BCGen f M₁.Q) p x) ∈ totDeg ℬ (BCGen f M₂.Q) (p + n) := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [show lof (ℬ 0) ℤ (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q β q) =
      DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q β q) from rfl, extAlongGen_of]
    have h1 := tmul_mem_totDeg (Q := M₁.Q) (SetLike.GradedOne.one_mem (A := 𝒜)) q
    have := smul_mem_totDeg β.2 (χ.2.1 h1)
    rwa [show (0 : ℤ) + (0 + p + n) = p + n by omega] at this
  | hadd x y hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

/-- `extAlongGen χ` is a generator map of degree `n` for the base changes. -/
theorem extAlongGen_mem {n : ℤ} (χ : HomAlong f M₁ M₂ n) :
    extAlongGen χ ∈ GenHom (M₁.baseChange f) (M₂.baseChange f) n :=
  ⟨extAlongGen_smul χ, extAlongGen_deg χ⟩

/-- **A9 (adjunction).** The extension `Tot(f^*M₁) → Tot(f^*M₂)` of `χ` (A4.c, `extGen`). -/
def extAlong {n : ℤ} (χ : HomAlong f M₁ M₂ n) :
    (M₁.baseChange f).T →ₗ[k] (M₂.baseChange f).T :=
  extGen n ⟨extAlongGen χ, extAlongGen_mem χ⟩

/-- `extAlong χ ∈ Hom^n(f^*M₁, f^*M₂)`. -/
theorem extAlong_mem {n : ℤ} (χ : HomAlong f M₁ M₂ n) :
    extAlong χ ∈ Hom (M₁.baseChange f) (M₂.baseChange f) n :=
  extGen_mem n _

/-- `extAlongGen χ ∘ ι = (e ↦ χ(1 ⊗ e))`. -/
private theorem extAlongGen_bcι {n : ℤ} (χ : HomAlong f M₁ M₂ n) (e : ⨁ p, M₁.Q p) :
    extAlongGen χ (bcι f M₁.Q e) = χ.1 (Tot.tmul 𝒜 M₁.Q 1 e) := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p q =>
    rw [show DirectSum.of M₁.Q p q = lof (𝒜 0) ℤ M₁.Q p q from rfl, bcι_lof,
      show lof (ℬ 0) ℤ (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q 1 q) =
        DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q 1 q) from rfl, extAlongGen_of,
      show ((1 : ℬ 0) : B) = 1 from rfl, one_smul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, Tot.tmul_add, map_add]

/-- **A9 (adjunction).** `extAlong χ ∘ F = χ`. -/
theorem extAlong_bcF {n : ℤ} (χ : HomAlong f M₁ M₂ n) (x : M₁.T) :
    extAlong χ (bcF f M₁.Q x) = χ.1 x := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul]
    change GCDga.twist ℬ n (f a) • extAlongGen χ (bcι f M₁.Q e) = _
    rw [extAlongGen_bcι]
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, add_smul, hx, hy, Tot.add_tmul, map_add]
    | @homogeneous q y =>
      rw [GCDga.twist_of_mem ℬ n (f.map_mem y.2), Tot.tmul_eq_smul (y : A) e, χ.2.2 y.2,
        smul_assoc]
  | hadd x y hx hy =>
    rw [map_add, map_add]
    exact ((extAlong χ).map_add _ _).trans (congrArg₂ _ hx hy)

/-- **A9 (adjunction), uniqueness.** A degree-`n` map `φ : Tot(f^*M₁) → Tot(f^*M₂)` with
`φ ∘ F = χ` is `extAlong χ`. -/
theorem eq_extAlong {n : ℤ} (χ : HomAlong f M₁ M₂ n)
    {φ : (M₁.baseChange f).T →ₗ[k] (M₂.baseChange f).T}
    (hφ : φ ∈ Hom (M₁.baseChange f) (M₂.baseChange f) n)
    (h : ∀ x : M₁.T, φ (bcF f M₁.Q x) = χ.1 x) : φ = extAlong χ :=
  hom_eq_of_bcF' f n hφ (extAlong_mem χ) fun x => (h x).trans (extAlong_bcF χ x).symm

end Cohesive
