import Cohesivemodules.Algebra.CohesiveDef

set_option linter.style.header false

/-!
# A13: cohesive modules in Block's convention (right modules)

Blueprint item A13 (sanity; not on the critical path, does not enter the main statements). This
file transcribes Block's definitions [B, Def 2.3.1, Def 2.3.2] verbatim, in his right-module
convention, so that `Algebra/BlockBridge.lean` can prove that they agree with the left-module
definitions of `Algebra/CohesiveDef.lean` (conventions §3).

Block [B, §2.3]: `E•` a `ℤ`-graded module over `A⁰`, the total module `E• ⊗_{A⁰} A` a right
`A`-module, `𝔼` a `k`-linear operator of total degree `1` with
`𝔼(e ω) = 𝔼(e ⊗ 1) ω + (-1)^{|e|} e dω` for `e ∈ E•`, and relative curvature
`F_𝔼(x) = 𝔼(𝔼 x) + x·c = 0`. Morphisms of degree `n` are degree-`n` maps with `φ(x a) = φ(x) a`
(no sign), and `dφ = 𝔼₂ ∘ φ - (-1)^n φ ∘ 𝔼₁`.

## Encoding
* `TotR 𝒜 Q = (⨁_p Q^p) ⊗_{A⁰} A`, a `def` with its instances (as `Tot`). `k` acts through
  `k → A⁰` (`Module.compHom`): Mathlib has no instance for an action on the right factor.
* The right action of `a ∈ A` is the named `k`-linear map `rAct a` (`x ↦ x·a`), not an
  `Aᵐᵒᵖ`-module instance, so no instance diamonds arise.
* The curvature `cB` of Block's curved dga is an explicit parameter; the bridge relates it to
  the curvature of `GCDga` by `c = -cB` (conventions §3).

## Deviations from the source
* `E•` is a family of (left) modules over the commutative ring `A⁰`; for commutative `A⁰` left
  and right modules are the same.
* Integrability is required for all `x` in the total module; Block states it for `e ∈ E•`.
  The two agree because `F_𝔼` is right `A`-linear [B, §2.3].
* Universe: `Q p : Type` (conventions §7).
-/

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- **A13.** Block's total module `E• ⊗_{A⁰} A = (⨁_p Q^p) ⊗_{A⁰} A` [B, Def 2.3.1], a right
`A`-module. A `def` with its instances below, as `Tot`. -/
def TotR (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] : Type :=
  (⨁ p, Q p) ⊗[𝒜 0] A

section TotRInstances

variable (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- A13: the additive group structure of Block's total module. -/
instance : AddCommGroup (TotR 𝒜 Q) := inferInstanceAs (AddCommGroup ((⨁ p, Q p) ⊗[𝒜 0] A))
/-- A13: the `A⁰`-module structure of Block's total module. -/
instance : Module (𝒜 0) (TotR 𝒜 Q) := inferInstanceAs (Module (𝒜 0) ((⨁ p, Q p) ⊗[𝒜 0] A))
/-- A13: the `k`-module structure of Block's total module, through `k → A⁰`. -/
instance : Module k (TotR 𝒜 Q) := Module.compHom (TotR 𝒜 Q) (algebraMap k (𝒜 0))
/-- A13: the `k`- and `A⁰`-actions on Block's total module are compatible. -/
instance : IsScalarTower k (𝒜 0) (TotR 𝒜 Q) :=
  ⟨fun r f x => by
    change (r • f) • x = algebraMap k (𝒜 0) r • (f • x)
    rw [Algebra.smul_def, mul_smul]⟩

end TotRInstances

namespace TotR

variable {𝒜} {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

variable (𝒜 Q) in
/-- A13: the pure tensor `e ⊗ a` in Block's total module. -/
def tmul (e : ⨁ p, Q p) (a : A) : TotR 𝒜 Q := e ⊗ₜ[𝒜 0] a

variable (𝒜 Q) in
/-- A13: the right action `x ↦ x·a` as an `A⁰`-linear map (`1 ⊗ (· * a)`). -/
def rAct0 (a : A) : TotR 𝒜 Q →ₗ[𝒜 0] TotR 𝒜 Q :=
  LinearMap.lTensor (⨁ p, Q p) (LinearMap.mulRight (𝒜 0) a)

variable (𝒜 Q) in
/-- **A13.** Block's right action `x ↦ x·a` of `a ∈ A` on `E• ⊗_{A⁰} A`, as a named `k`-linear map
(`A` acting on the right factor by right multiplication). -/
def rAct (a : A) : TotR 𝒜 Q →ₗ[k] TotR 𝒜 Q := (rAct0 𝒜 Q a).restrictScalars k

/-- A13: `(e ⊗ b)·a = e ⊗ (b a)`. -/
@[simp] theorem rAct_tmul (a : A) (e : ⨁ p, Q p) (b : A) :
    rAct 𝒜 Q a (tmul 𝒜 Q e b) = tmul 𝒜 Q e (b * a) := rfl

end TotR

/-- **A13.** The elements of total degree `m` of `E• ⊗_{A⁰} A`: spanned by `e ⊗ a` with
`e ∈ Q^p`, `a ∈ A^q`, `p + q = m`. -/
def totDegR (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (m : ℤ) :
    Submodule k (TotR 𝒜 Q) :=
  Submodule.span k {x | ∃ (p q : ℤ) (e : Q p) (a : A), p + q = m ∧ a ∈ 𝒜 q ∧
    x = TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) a}

/-- **A13.** A quasi-cohesive module in Block's convention over the curved dga `(A, d, cB)`
[B, Def 2.3.1, Def 2.3.2(1)]: a `ℤ`-graded `A⁰`-module `E• = Q` with a `k`-linear `ℤ`-connection
`𝔼` of total degree `1` on the right `A`-module `E• ⊗_{A⁰} A`, satisfying Block's Leibniz rule
`𝔼(e ω) = 𝔼(e ⊗ 1) ω + (-1)^{|e|} e dω` for `e ∈ Q^p`, and integrability: the relative
curvature `F_𝔼(x) = 𝔼(𝔼 x) + x·cB` vanishes.

Deviations: integrability for all `x` (Block: for `e ∈ E•`; equivalent since `F_𝔼` is right
`A`-linear). The curvature `cB` is a parameter; it is the curvature of `GCDga` only up to the
sign `c = -cB` (⚠ conventions §3). -/
structure BlockQuasiCohesive (cB : A) where
  /-- The generators `E^p`. -/
  Q : ℤ → Type
  [acg : ∀ p, AddCommGroup (Q p)]
  [mod : ∀ p, Module (𝒜 0) (Q p)]
  /-- The `ℤ`-connection `𝔼` on `E• ⊗_{A⁰} A`. -/
  E : TotR 𝒜 Q →ₗ[k] TotR 𝒜 Q
  /-- `𝔼` has total degree `1`. -/
  E_mem : ∀ {m : ℤ} {x : TotR 𝒜 Q}, x ∈ totDegR 𝒜 Q m → E x ∈ totDegR 𝒜 Q (m + 1)
  /-- Block's Leibniz rule: `𝔼(e ω) = 𝔼(e ⊗ 1) ω + (-1)^{|e|} e dω` for `e ∈ E^p`. -/
  leibniz : ∀ {p : ℤ} (e : Q p) (ω : A),
    E (TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) ω) =
      TotR.rAct 𝒜 Q ω (E (TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) 1)) +
        p.negOnePow • TotR.tmul 𝒜 Q (lof (𝒜 0) ℤ Q p e) (GCDga.d (𝒜 := 𝒜) ω)
  /-- Integrability: the relative curvature `𝔼 ∘ 𝔼 + (-)·cB` vanishes. -/
  integrable : ∀ x : TotR 𝒜 Q, E (E x) + TotR.rAct 𝒜 Q cB x = 0

attribute [instance] BlockQuasiCohesive.acg BlockQuasiCohesive.mod

/-- **A13.** A cohesive module in Block's convention [B, Def 2.3.2(1)]: `E•` bounded in both
directions, each `E^p` finitely generated projective over `A⁰`. -/
structure BlockCohesive (cB : A) extends BlockQuasiCohesive 𝒜 cB where
  /-- `E^p = 0` outside a bounded range of degrees. -/
  bounded : ∃ a b : ℤ, ∀ p, (p < a ∨ b < p) → Subsingleton (Q p)
  /-- Each `E^p` is finitely generated. -/
  finite : ∀ p, Module.Finite (𝒜 0) (Q p)
  /-- Each `E^p` is projective. -/
  projective : ∀ p, Module.Projective (𝒜 0) (Q p)

variable {𝒜} {cB : A}

/-- The total module `E• ⊗_{A⁰} A` of a module in Block's convention. -/
abbrev BlockQuasiCohesive.T (E : BlockQuasiCohesive 𝒜 cB) : Type := TotR 𝒜 E.Q

variable (E₁ E₂ : BlockQuasiCohesive 𝒜 cB)

/-- **A13.** Block's morphisms of degree `n` [B, Def 2.3.2(2)]: `k`-linear maps
`φ : E₁ ⊗_{A⁰} A → E₂ ⊗_{A⁰} A` of degree `n` with `φ(x a) = φ(x) a` for all `a ∈ A` (right
`A`-linear, no sign). -/
def BlockHom (n : ℤ) : Submodule k (E₁.T →ₗ[k] E₂.T) where
  carrier := {φ | (∀ {m : ℤ} {x : E₁.T}, x ∈ totDegR 𝒜 E₁.Q m → φ x ∈ totDegR 𝒜 E₂.Q (m + n)) ∧
    ∀ (a : A) (x : E₁.T), φ (TotR.rAct 𝒜 E₁.Q a x) = TotR.rAct 𝒜 E₂.Q a (φ x)}
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => by simp⟩
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun hx => add_mem (hφ.1 hx) (hψ.1 hx), fun a x => by simp [hφ.2 a, hψ.2 a]⟩
  smul_mem' := fun r φ hφ =>
    ⟨fun hx => Submodule.smul_mem _ r (hφ.1 hx), fun a x => by simp [hφ.2 a]⟩

/-- **A13.** Block's differential `dφ = 𝔼₂ ∘ φ - (-1)^n φ ∘ 𝔼₁` on maps of degree `n`
[B, Def 2.3.2(2)]. -/
def blockδ (n : ℤ) : (E₁.T →ₗ[k] E₂.T) →ₗ[k] (E₁.T →ₗ[k] E₂.T) where
  toFun φ := E₂.E ∘ₗ φ - n.negOnePow • (φ ∘ₗ E₁.E)
  map_add' φ ψ := by
    simp only [LinearMap.comp_add, LinearMap.add_comp, smul_add]
    abel
  map_smul' r φ := by
    simp only [LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply]
    rw [smul_sub, smul_comm r]

/-- A13: formula for `blockδ`. -/
theorem blockδ_apply (n : ℤ) (φ : E₁.T →ₗ[k] E₂.T) :
    blockδ E₁ E₂ n φ = E₂.E ∘ₗ φ - n.negOnePow • (φ ∘ₗ E₁.E) := rfl

end Cohesive
