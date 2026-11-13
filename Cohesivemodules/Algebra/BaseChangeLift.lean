import Cohesivemodules.Algebra.BaseChange

set_option linter.style.header false

/-!
# C7 (algebra): maps out of a base change into any quasi-cohesive module

Blueprint item C7.e (§4, v1.11). For a map of (possibly curved) dgas
`f : (A, 𝒜) → (B, ℬ)`, a quasi-cohesive
`A`-module `M` and a quasi-cohesive `B`-module `N`, a degree-`0` map `χ : Tot(M) → Tot(N)` that
is semilinear along `f` extends uniquely to a `B`-linear degree-`0` map
`bcLift χ : Tot(f^*M) → Tot(N)` with `bcLift χ ∘ F = χ` (the base-change adjunction). If `χ`
commutes with the operators `𝕏`, then `bcLift χ` is closed. This is `extAlong`
(`Algebra/BaseChangeExt.lean`) in degree `0` with an arbitrary target instead of a base change;
it gives the comparison map `Ξ_e : α_U(M) → T(K)` of C7.e on each open.

## Deviations
* Degree `0` only (all that C7 needs); semilinearity `χ(a·x) = f(a)·χ(x)` for all `a` (no sign
  in degree `0`).
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

variable (f : DgaHom 𝒜 ℬ) (M : QuasiCohesive 𝒜) (N : QuasiCohesive ℬ)

/-- **C7.e (algebra).** Degree-`0` `k`-linear maps `Tot(M) → Tot(N)` semilinear along `f`:
`χ(a·x) = f(a)·χ(x)`. -/
def LinAlong : Submodule k (M.T →ₗ[k] N.T) where
  carrier := {χ | (∀ {m : ℤ} {x : M.T}, x ∈ totDeg 𝒜 M.Q m → χ x ∈ totDeg ℬ N.Q m) ∧
    ∀ (a : A) (x : M.T), χ (a • x) = f a • χ x}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun hx => add_mem (hφ.1 hx) (hψ.1 hx), fun a x => by
      simp only [LinearMap.add_apply, hφ.2 a x, hψ.2 a x, smul_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => by simp⟩
  smul_mem' := fun r φ hφ =>
    ⟨fun hx => Submodule.smul_mem _ r (hφ.1 hx), fun a x => by
      simp only [LinearMap.smul_apply, hφ.2 a x]
      exact smul_comm r (f a) (φ x)⟩

variable {f M N}

/-- The bi-additive map `(β, q) ↦ β·χ(1 ⊗ q)` on degree `p`. -/
def bcLiftAux (χ : LinAlong f M N) (p : ℤ) : f.B0 →+ M.Q p →+ N.T :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk'
      (fun q => toB f β • χ.1 (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q)))
      (fun q q' => by rw [map_add, Tot.tmul_add, map_add, smul_add]))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, toB_add, add_smul])

/-- `bcLiftAux` is `A⁰`-balanced. -/
theorem bcLiftAux_balanced (χ : LinAlong f M N) (p : ℤ) (r : 𝒜 0) (β : f.B0) (q : M.Q p) :
    bcLiftAux χ p (r • β) q = bcLiftAux χ p β (r • q) := by
  show toB f (r • β) • χ.1 (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q)) =
    toB f β • χ.1 (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p (r • q)))
  have h1 : Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p (r • q)) =
      (r : A) • Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q) := by
    rw [← Tot.smul0_eq, map_smul (lof (𝒜 0) ℤ M.Q p) r q]
    exact map_smul (Tot.oneTmul 𝒜 M.Q) r _
  rw [h1, χ.2.2 r, Algebra.smul_def, toB_mul, toB_algebraMap, ← mul_smul,
    GCDga.central ℬ (f.map_mem r.2)]

/-- The generator map of `bcLift χ` on degree `p`: `β ⊗ q ↦ β·χ(1 ⊗ q)`. -/
def bcLiftP (χ : LinAlong f M N) (p : ℤ) : BCGen f M.Q p →+ N.T :=
  TensorProduct.liftAddHom (R := 𝒜 0) (bcLiftAux χ p) (bcLiftAux_balanced χ p)

/-- The generator map of `bcLift χ`. -/
def bcLiftGen (χ : LinAlong f M N) : (⨁ p, BCGen f M.Q p) →+ N.T :=
  DirectSum.toAddMonoid (bcLiftP χ)

/-- `bcLiftGen χ` on a homogeneous pure tensor `β ⊗ q`. -/
private theorem bcLiftGen_of (χ : LinAlong f M N) (p : ℤ) (β : ℬ 0) (q : M.Q p) :
    bcLiftGen χ (DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q β q)) =
      (β : B) • χ.1 (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q)) :=
  DirectSum.toAddMonoid_of _ p _

/-- `bcLiftGen χ` is `B⁰`-linear. -/
private theorem bcLiftGen_smul (χ : LinAlong f M N) (γ : ℬ 0)
    (e : ⨁ p, BCGen f M.Q p) : bcLiftGen χ (γ • e) = (γ : B) • bcLiftGen χ e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    induction x using BCGen.induction_on with
    | ht β q =>
      rw [show γ • DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q β q) =
          DirectSum.of (BCGen f M.Q) p (γ • BCGen.tmul f M.Q β q) from
          (map_smul (DirectSum.lof (ℬ 0) ℤ (BCGen f M.Q) p) γ _).symm, BCGen.smul_tmul,
        bcLiftGen_of, bcLiftGen_of, show ((γ * β : ℬ 0) : B) = (γ : B) * β from rfl,
        mul_smul]
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f M.Q) p).map_add, smul_add, map_add, hx, hy, map_add,
        smul_add]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `bcLiftGen χ` has degree `0`. -/
private theorem bcLiftGen_deg (χ : LinAlong f M N) (p : ℤ) (x : BCGen f M.Q p) :
    bcLiftGen χ (lof (ℬ 0) ℤ (BCGen f M.Q) p x) ∈ totDeg ℬ N.Q (p + 0) := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [show lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q β q) =
      DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q β q) from rfl, bcLiftGen_of]
    have h1 := tmul_mem_totDeg (Q := M.Q) (SetLike.GradedOne.one_mem (A := 𝒜)) q
    have := smul_mem_totDeg β.2 (χ.2.1 h1)
    rwa [show (0 : ℤ) + (0 + p) = p + 0 by omega] at this
  | hadd x y hx hy =>
    rw [map_add, map_add]
    exact add_mem hx hy

/-- `bcLiftGen χ` is a generator map of degree `0` (A4.c). -/
theorem bcLiftGen_mem (χ : LinAlong f M N) : bcLiftGen χ ∈ GenHom (M.baseChange f) N 0 :=
  ⟨bcLiftGen_smul χ, bcLiftGen_deg χ⟩

/-- `bcLiftGen χ ∘ ι = (e ↦ χ(1 ⊗ e))`. -/
private theorem bcLiftGen_bcι (χ : LinAlong f M N) (e : ⨁ p, M.Q p) :
    bcLiftGen χ (bcι f M.Q e) = χ.1 (Tot.tmul 𝒜 M.Q 1 e) := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p q =>
    rw [show DirectSum.of M.Q p q = lof (𝒜 0) ℤ M.Q p q from rfl, bcι_lof,
      show lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q) =
        DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q) from rfl, bcLiftGen_of,
      show ((1 : ℬ 0) : B) = 1 from rfl, one_smul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, Tot.tmul_add, map_add]

/-- **C7.e (algebra).** The extension `Tot(f^*M) → Tot(N)` of `χ` (A4.c, `extGen`). -/
def bcLift (χ : LinAlong f M N) : (M.baseChange f).T →ₗ[k] N.T :=
  extGen 0 ⟨bcLiftGen χ, bcLiftGen_mem χ⟩

/-- `bcLift χ ∈ Hom^0(f^*M, N)`. -/
theorem bcLift_mem (χ : LinAlong f M N) : bcLift χ ∈ Hom (M.baseChange f) N 0 :=
  extGen_mem 0 _

/-- **C7.e (algebra), adjunction.** `bcLift χ ∘ F = χ`. -/
theorem bcLift_bcF (χ : LinAlong f M N) (x : M.T) : bcLift χ (bcF f M.Q x) = χ.1 x := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul]
    change GCDga.twist ℬ 0 (f a) • bcLiftGen χ (bcι f M.Q e) = _
    rw [bcLiftGen_bcι]
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, add_smul, hx, hy, Tot.add_tmul, map_add]
    | @homogeneous q y =>
      rw [GCDga.twist_of_mem ℬ 0 (f.map_mem y.2), Tot.tmul_eq_smul (y : A) e, χ.2.2,
        zero_mul, Int.negOnePow_zero, one_smul]
  | hadd x y hx hy =>
    rw [map_add, map_add]
    exact ((bcLift χ).map_add _ _).trans (congrArg₂ _ hx hy)

/-- **C7.e (algebra), uniqueness.** A degree-`0` map `φ : Tot(f^*M) → Tot(N)` with `φ ∘ F = χ`
is `bcLift χ`. -/
theorem eq_bcLift (χ : LinAlong f M N) {φ : (M.baseChange f).T →ₗ[k] N.T}
    (hφ : φ ∈ Hom (M.baseChange f) N 0) (h : ∀ x : M.T, φ (bcF f M.Q x) = χ.1 x) :
    φ = bcLift χ :=
  hom_eq_of_bcF' f 0 hφ (bcLift_mem χ) fun x => (h x).trans (bcLift_bcF χ x).symm

/-- **C7.e (algebra).** If `χ` commutes with the operators, `𝕏_N ∘ χ = χ ∘ 𝕏_M`, then
`bcLift χ` is closed. -/
theorem bcLift_mem_Z0 (χ : LinAlong f M N) (hX : ∀ x : M.T, N.X (χ.1 x) = χ.1 (M.X x)) :
    bcLift χ ∈ Z0 (M.baseChange f) N := by
  refine ⟨bcLift_mem χ, LinearMap.mem_ker.2 ?_⟩
  have h1 : δ (M.baseChange f) N 0 (bcLift χ) ∈ Hom (M.baseChange f) N (0 + 1) :=
    δ_mem _ _ (bcLift_mem χ)
  rw [zero_add] at h1
  refine hom_eq_of_bcF' f 1 h1 (zero_mem _) fun x => ?_
  have e1 : (M.baseChange f).X (bcF f M.Q x) = bcF f M.Q (M.X x) := bc_extend_bcF f M x
  have e2 : bcLift χ (bcF f M.Q x) = χ.1 x := bcLift_bcF χ x
  have e3 : bcLift χ (bcF f M.Q (M.X x)) = χ.1 (M.X x) := bcLift_bcF χ (M.X x)
  change N.X (bcLift χ (bcF f M.Q x)) -
    (0 : ℤ).negOnePow • bcLift χ ((M.baseChange f).X (bcF f M.Q x)) = 0
  rw [e1, e2, e3, hX, Int.negOnePow_zero, one_smul, sub_self]

end Cohesive
