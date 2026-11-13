-- FROZEN (gate 1a, 22 Oct 2026; A3–A5, approved by the human). Do not edit without approval.
import Cohesivemodules.Algebra.Dga
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.CategoryTheory.Linear.Basic

set_option linter.style.header false

/-!
# A3–A5: cohesive modules, Hom complexes, the homotopy category `Ho(P_A)`

Blueprint items A3, A4, A5 (conventions §2–§4, encoding 1). This file holds the definitions
that enter the main statement, with only the API needed to define them. It is frozen at the
gate after phase 1a (CLAUDE.md, conventions §9); theorems about these objects go in
`Algebra/Cohesive.lean`.

## Encoding (conventions §4, encoding 1)
A quasi-cohesive module is given by its generators `Q : ℤ → Type` (graded `A⁰`-modules) and an
operator `𝕏` on the total module `T = A ⊗_{A⁰} ⨁_p Q^p`, which is built from `Q`, not given as
data. `Hom^n` consists of the `k`-linear maps `T₁ → T₂` of degree `n` with
`φ(a·x) = (-1)^{n|a|} a·φ(x)`, exactly as in blueprint A4.

## Deviations from the sources
* ⚠ Left modules `A ⊗_{A⁰} Q` (as [A]); Block uses right modules `Q ⊗_A A` (conventions §3,
  blueprint §9 deviation 1). Curvature: `𝕏 ∘ 𝕏 = c·(-)`, `c_here = -c_Block`.
* `Hom^n(M₁, M₂)` and its differential are defined for any two quasi-cohesive modules; the
  sources take `M₁` cohesive. The category `Ho(P_A)` only uses cohesive modules.
* Universe: `Q p : Type` (conventions §7).
-/

namespace Cohesive

open TensorProduct DirectSum CategoryTheory

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-! ## A3: quasi-cohesive and cohesive modules -/

/-- A3: the total module `A ⊗_{A⁰} ⨁_p Q^p` of a family of `A⁰`-modules `Q`.

A `def` with its instances declared once below, not an `abbrev`: with an `abbrev`, instance
search fails on submodules of `Tot →ₗ[k] Tot` (it cannot solve
`AddCommGroup.toAddCommMonoid ?g =?= (the tensor product's own AddCommMonoid)`), so `H⁰` would
have no quotient instance. -/
def Tot (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] : Type :=
  A ⊗[𝒜 0] (⨁ p, Q p)

section TotInstances

variable (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- A3: the additive group structure of the total module. -/
instance : AddCommGroup (Tot 𝒜 Q) := inferInstanceAs (AddCommGroup (A ⊗[𝒜 0] (⨁ p, Q p)))
/-- A3: the left `A`-module structure of the total module (`A` acting on the left factor). -/
instance : Module A (Tot 𝒜 Q) := inferInstanceAs (Module A (A ⊗[𝒜 0] (⨁ p, Q p)))
/-- A3: the `k`-module structure of the total module. -/
instance : Module k (Tot 𝒜 Q) := inferInstanceAs (Module k (A ⊗[𝒜 0] (⨁ p, Q p)))
/-- A3: the `A⁰`-module structure of the total module. -/
instance : Module (𝒜 0) (Tot 𝒜 Q) := inferInstanceAs (Module (𝒜 0) (A ⊗[𝒜 0] (⨁ p, Q p)))
/-- A3: the `k`- and `A`-actions on the total module are compatible. -/
instance : IsScalarTower k A (Tot 𝒜 Q) :=
  inferInstanceAs (IsScalarTower k A (A ⊗[𝒜 0] (⨁ p, Q p)))

end TotInstances

/-- A3: the elements of total degree `m` of `A ⊗_{A⁰} ⨁_p Q^p`: spanned by `a ⊗ e` with
`a ∈ A^q`, `e ∈ Q^p`, `q + p = m` (conventions §1). -/
def totDeg (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (m : ℤ) :
    Submodule k (Tot 𝒜 Q) :=
  Submodule.span k {x | ∃ (q p : ℤ) (a : A) (e : Q p), q + p = m ∧ a ∈ 𝒜 q ∧
    x = (a ⊗ₜ[𝒜 0] lof (𝒜 0) ℤ Q p e : A ⊗[𝒜 0] (⨁ p, Q p))}

/-- **A3.** A quasi-cohesive module over `(A, 𝒜)`: a `ℤ`-graded `A⁰`-module `Q` (as a family of
`A⁰`-modules `Q p : Type`) with a `k`-linear operator `𝕏` of total degree `1` on
`A ⊗_{A⁰} ⨁_p Q^p` satisfying the Leibniz rule `𝕏(a·x) = da·x + (-1)^{|a|} a·𝕏x` (for
homogeneous `a`) and flatness `𝕏 ∘ 𝕏 = c·(-)`. [B, Def 2.3.2], [A, Rem 4.0.4].

⚠ Left modules (conventions §3); curvature sign `c_here = -c_Block`. -/
structure QuasiCohesive where
  /-- The generators: the graded pieces `Q^p`. -/
  Q : ℤ → Type
  [acg : ∀ p, AddCommGroup (Q p)]
  [mod : ∀ p, Module (𝒜 0) (Q p)]
  /-- The operator `𝕏` on the total module. -/
  X : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q
  /-- `𝕏` has total degree `1`. -/
  X_mem : ∀ {m : ℤ} {x : Tot 𝒜 Q}, x ∈ totDeg 𝒜 Q m → X x ∈ totDeg 𝒜 Q (m + 1)
  /-- Leibniz: `𝕏(a·x) = da·x + (-1)^{|a|} a·𝕏x` for `a ∈ A^p`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : Tot 𝒜 Q,
    X (a • x) = GCDga.d (𝒜 := 𝒜) a • x + p.negOnePow • a • X x
  /-- Flatness: `𝕏 ∘ 𝕏 = c·(-)`. -/
  flat : ∀ x : Tot 𝒜 Q, X (X x) = GCDga.c (𝒜 := 𝒜) • x

attribute [instance] QuasiCohesive.acg QuasiCohesive.mod

/-- **A3.** A cohesive module: a quasi-cohesive module whose generators `Q^p` vanish for all but
finitely many `p` and are finitely generated projective `A⁰`-modules. [B, Def 2.3.2]. -/
structure CohesiveModule extends QuasiCohesive 𝒜 where
  /-- `Q^p = 0` outside a bounded range of degrees. -/
  bounded : ∃ a b : ℤ, ∀ p, (p < a ∨ b < p) → Subsingleton (Q p)
  /-- Each `Q^p` is finitely generated. -/
  finite : ∀ p, Module.Finite (𝒜 0) (Q p)
  /-- Each `Q^p` is projective. -/
  projective : ∀ p, Module.Projective (𝒜 0) (Q p)

/-! ## A4: Hom complexes -/

variable {𝒜}

/-- The total module of a quasi-cohesive module. -/
abbrev QuasiCohesive.T (M : QuasiCohesive 𝒜) : Type := Tot 𝒜 M.Q

variable (M₁ M₂ M₃ : QuasiCohesive 𝒜)

/-- **A4.** `Hom^n(M₁, M₂)`: the `k`-linear maps `φ : T₁ → T₂` of degree `n` with
`φ(a·x) = (-1)^{n|a|} a·φ(x)` for homogeneous `a`, as a `k`-submodule of `T₁ →ₗ[k] T₂`.
[B, §2.3], [A, Rem 4.0.4]; conventions §2. Defined for any quasi-cohesive `M₁` (the sources
take `M₁` cohesive). -/
def Hom (n : ℤ) : Submodule k (M₁.T →ₗ[k] M₂.T) where
  carrier := {φ | (∀ {m : ℤ} {x : M₁.T}, x ∈ totDeg 𝒜 M₁.Q m → φ x ∈ totDeg 𝒜 M₂.Q (m + n)) ∧
    ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : M₁.T, φ (a • x) = (n * p).negOnePow • a • φ x}
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => by simp⟩
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun hx => add_mem (hφ.1 hx) (hψ.1 hx), fun ha x => by simp [hφ.2 ha, hψ.2 ha, smul_add]⟩
  smul_mem' := fun r φ hφ =>
    ⟨fun hx => Submodule.smul_mem _ r (hφ.1 hx), fun ha x => by
      simp only [LinearMap.smul_apply, hφ.2 ha]
      rw [smul_comm r, smul_comm r]⟩

/-- **A4.** The differential `δφ = 𝕏₂ ∘ φ - (-1)^n φ ∘ 𝕏₁` (conventions §2; this is Mathlib's
`CochainComplex.HomComplex.δ`, see `δ_eq_mathlib`). -/
def δ (n : ℤ) : (M₁.T →ₗ[k] M₂.T) →ₗ[k] (M₁.T →ₗ[k] M₂.T) where
  toFun φ := M₂.X ∘ₗ φ - n.negOnePow • (φ ∘ₗ M₁.X)
  map_add' φ ψ := by
    simp only [LinearMap.comp_add, LinearMap.add_comp, smul_add]
    abel
  map_smul' r φ := by
    simp only [LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply]
    rw [smul_sub, smul_comm r]

/-- A4: formula for `δ`. -/
theorem δ_apply (n : ℤ) (φ : M₁.T →ₗ[k] M₂.T) :
    δ M₁ M₂ n φ = M₂.X ∘ₗ φ - n.negOnePow • (φ ∘ₗ M₁.X) := rfl

/-- A4.d: `δ` in Mathlib's form `z ≫ d + (-1)^{n+1} d ≫ z` (applicative order). -/
theorem δ_eq_mathlib (n : ℤ) (φ : M₁.T →ₗ[k] M₂.T) :
    δ M₁ M₂ n φ = M₂.X ∘ₗ φ + (n + 1).negOnePow • (φ ∘ₗ M₁.X) := by
  rw [δ_apply, Int.negOnePow_succ, Units.neg_smul]
  exact sub_eq_add_neg _ _

/-- Rewriting `(-1)^x` by parity. -/
theorem negOnePow_parity (x : ℤ) : x.negOnePow = if Even x then 1 else -1 := by
  split_ifs with h
  · exact Int.negOnePow_even x h
  · exact Int.negOnePow_odd x (Int.not_even_iff_odd.1 h)

/-- A4: `δ` maps `Hom^n` to `Hom^{n+1}`. -/
theorem δ_mem {n : ℤ} {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Hom M₁ M₂ n) :
    δ M₁ M₂ n φ ∈ Hom M₁ M₂ (n + 1) := by
  obtain ⟨h₁, h₂⟩ := hφ
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · have e1 : M₂.X (φ x) ∈ totDeg 𝒜 M₂.Q (m + (n + 1)) := by
      have := M₂.X_mem (h₁ hx); rwa [add_assoc] at this
    have e2 : φ (M₁.X x) ∈ totDeg 𝒜 M₂.Q (m + (n + 1)) := by
      have := h₁ (M₁.X_mem hx); rwa [add_assoc, add_comm 1 n] at this
    simp only [δ_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      Units.smul_def]
    exact sub_mem e1 (Submodule.smul_of_tower_mem _ _ e2)
  · have hda := GCDga.d_mem (𝒜 := 𝒜) ha
    simp only [δ_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      M₁.leibniz ha, map_add, h₂ ha, h₂ hda, M₂.leibniz ha, Units.smul_def, map_zsmul]
    simp only [negOnePow_parity, parity_simps]
    by_cases hn : Even n <;> by_cases hp : Even p <;> simp [hn, hp, smul_sub, smul_neg]

/-- A4.a: `δ ∘ δ = 0` on `Hom^n`, including curvature (`c` has even degree). [B, Lemma 2.3.4]. -/
theorem δ_δ {n : ℤ} {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Hom M₁ M₂ n) :
    δ M₁ M₂ (n + 1) (δ M₁ M₂ n φ) = 0 := by
  ext x
  have hc : φ (GCDga.c (𝒜 := 𝒜) • x) = GCDga.c (𝒜 := 𝒜) • φ x := by
    rw [hφ.2 (GCDga.c_mem (𝒜 := 𝒜)), show n * 2 = 2 * n by ring, Int.negOnePow_two_mul,
      one_smul]
  simp only [δ_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_sub,
    Units.smul_def, map_zsmul, M₁.flat, M₂.flat, hc, LinearMap.zero_apply]
  simp only [negOnePow_parity, parity_simps]
  by_cases hn : Even n
  · simp [hn]; abel
  · simp [hn]

/-- A4.b: composition `Hom^m(M₂, M₃) × Hom^n(M₁, M₂) → Hom^{m+n}(M₁, M₃)`. -/
theorem comp_mem {m n : ℤ} {ψ : M₂.T →ₗ[k] M₃.T} {φ : M₁.T →ₗ[k] M₂.T}
    (hψ : ψ ∈ Hom M₂ M₃ m) (hφ : φ ∈ Hom M₁ M₂ n) : ψ ∘ₗ φ ∈ Hom M₁ M₃ (m + n) := by
  refine ⟨fun {q x} hx => ?_, fun {p a} ha x => ?_⟩
  · have := hψ.1 (hφ.1 hx)
    rwa [add_assoc, add_comm n m] at this
  · simp only [LinearMap.comp_apply, hφ.2 ha, Units.smul_def, map_zsmul, hψ.2 ha, smul_smul]
    rw [← Units.val_mul, ← Int.negOnePow_add, add_mul, add_comm (m * p)]

/-- A4.b: the Leibniz rule `δ(ψ ∘ φ) = δψ ∘ φ + (-1)^m ψ ∘ δφ`. -/
theorem δ_comp (m n : ℤ) (ψ : M₂.T →ₗ[k] M₃.T) (φ : M₁.T →ₗ[k] M₂.T) :
    δ M₁ M₃ (m + n) (ψ ∘ₗ φ) = δ M₂ M₃ m ψ ∘ₗ φ + m.negOnePow • (ψ ∘ₗ δ M₁ M₂ n φ) := by
  ext x
  simp only [δ_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_sub, Units.smul_def, map_zsmul, smul_sub, smul_smul,
    Int.negOnePow_add]
  abel

/-- A4.b: the identity lies in `Hom^0` and is closed. -/
theorem id_mem : (LinearMap.id : M₁.T →ₗ[k] M₁.T) ∈ Hom M₁ M₁ 0 :=
  ⟨fun hx => by simpa using hx, fun _ x => by simp⟩

/-- A4.b: the identity is closed. -/
theorem δ_id : δ M₁ M₁ 0 LinearMap.id = 0 := by
  ext x
  simp [δ_apply]

/-! ## A5: the homotopy category -/

/-- A5: closed maps of degree 0, `Z⁰ = Hom^0 ∩ ker δ`. -/
def Z0 : Submodule k (M₁.T →ₗ[k] M₂.T) := Hom M₁ M₂ 0 ⊓ LinearMap.ker (δ M₁ M₂ 0)

/-- A5: exact maps of degree 0, `B⁰ = δ(Hom^{-1})`. -/
def B0 : Submodule k (M₁.T →ₗ[k] M₂.T) := (Hom M₁ M₂ (-1)).map (δ M₁ M₂ (-1))

/-- A5: boundaries are cycles (from `δ_mem` and `δ_δ`). -/
theorem B0_le_Z0 : B0 M₁ M₂ ≤ Z0 M₁ M₂ := by
  rintro _ ⟨ψ, hψ, rfl⟩
  have h1 := δ_mem M₁ M₂ hψ
  have h2 := δ_δ M₁ M₂ hψ
  norm_num at h1 h2
  exact ⟨h1, h2⟩

/-- A5: `H⁰ Hom(M₁, M₂) = Z⁰ / B⁰`, the morphisms of `Ho(P_A)`. -/
abbrev H0 : Type := Z0 M₁ M₂ ⧸ (B0 M₁ M₂).comap (Z0 M₁ M₂).subtype

variable {M₁ M₂ M₃}

/-- A5: the composite of closed degree-0 maps is closed of degree 0. -/
theorem comp_mem_Z0 {ψ : M₂.T →ₗ[k] M₃.T} {φ : M₁.T →ₗ[k] M₂.T} (hψ : ψ ∈ Z0 M₂ M₃)
    (hφ : φ ∈ Z0 M₁ M₂) : ψ ∘ₗ φ ∈ Z0 M₁ M₃ := by
  obtain ⟨hψ₁, hψ₂⟩ := Submodule.mem_inf.1 hψ
  obtain ⟨hφ₁, hφ₂⟩ := Submodule.mem_inf.1 hφ
  refine Submodule.mem_inf.2 ⟨by simpa using comp_mem M₁ M₂ M₃ hψ₁ hφ₁, ?_⟩
  have h := δ_comp M₁ M₂ M₃ 0 0 ψ φ
  rw [add_zero] at h
  rw [LinearMap.mem_ker, h, LinearMap.mem_ker.1 hψ₂, LinearMap.mem_ker.1 hφ₂]
  simp

/-- A5: a boundary composed with a cycle is a boundary. -/
theorem comp_mem_B0_left {ψ : M₂.T →ₗ[k] M₃.T} {φ : M₁.T →ₗ[k] M₂.T} (hψ : ψ ∈ B0 M₂ M₃)
    (hφ : φ ∈ Z0 M₁ M₂) : ψ ∘ₗ φ ∈ B0 M₁ M₃ := by
  obtain ⟨χ, hχ, rfl⟩ := hψ
  obtain ⟨hφ₁, hφ₂⟩ := Submodule.mem_inf.1 hφ
  refine ⟨χ ∘ₗ φ, by simpa using comp_mem M₁ M₂ M₃ hχ hφ₁, ?_⟩
  have h := δ_comp M₁ M₂ M₃ (-1) 0 χ φ
  rw [add_zero] at h
  rw [h, LinearMap.mem_ker.1 hφ₂]
  simp

/-- A5: a cycle composed with a boundary is a boundary. -/
theorem comp_mem_B0_right {ψ : M₂.T →ₗ[k] M₃.T} {φ : M₁.T →ₗ[k] M₂.T} (hψ : ψ ∈ Z0 M₂ M₃)
    (hφ : φ ∈ B0 M₁ M₂) : ψ ∘ₗ φ ∈ B0 M₁ M₃ := by
  obtain ⟨χ, hχ, rfl⟩ := hφ
  obtain ⟨hψ₁, hψ₂⟩ := Submodule.mem_inf.1 hψ
  refine ⟨ψ ∘ₗ χ, by simpa using comp_mem M₁ M₂ M₃ hψ₁ hχ, ?_⟩
  have h := δ_comp M₁ M₂ M₃ 0 (-1) ψ χ
  rw [zero_add] at h
  rw [h, LinearMap.mem_ker.1 hψ₂]
  simp

variable (M₁ M₂ M₃) in
/-- A5: composition of closed degree-0 maps, as a `k`-bilinear map. -/
def compZ0 : Z0 M₂ M₃ →ₗ[k] Z0 M₁ M₂ →ₗ[k] Z0 M₁ M₃ :=
  LinearMap.mk₂ k (fun ψ φ => ⟨ψ.1 ∘ₗ φ.1, comp_mem_Z0 ψ.2 φ.2⟩)
    (fun _ _ _ => Subtype.ext (by simp [LinearMap.add_comp]))
    (fun _ _ _ => Subtype.ext (by simp [LinearMap.smul_comp]))
    (fun _ _ _ => Subtype.ext (by simp [LinearMap.comp_add]))
    (fun _ _ _ => Subtype.ext (by simp [LinearMap.comp_smul]))

/-- A5: formula for `compZ0`. -/
@[simp] theorem compZ0_apply (ψ : Z0 M₂ M₃) (φ : Z0 M₁ M₂) :
    ((compZ0 M₁ M₂ M₃ ψ φ : Z0 M₁ M₃) : M₁.T →ₗ[k] M₃.T) = ψ.1 ∘ₗ φ.1 := rfl

variable (M₁ M₂ M₃) in
/-- **A5.** Composition on `H⁰`, the composition of `Ho(P_A)`; well defined because
boundaries absorb composition with cycles (`comp_mem_B0_left`, `comp_mem_B0_right`). -/
def compH0 : H0 M₂ M₃ →ₗ[k] H0 M₁ M₂ →ₗ[k] H0 M₁ M₃ :=
  LinearMap.liftQ₂ _ _ ((compZ0 M₁ M₂ M₃).compr₂ (Submodule.mkQ _))
    (fun _ hψ => LinearMap.mem_ker.2 <| LinearMap.ext fun φ =>
      (Submodule.Quotient.mk_eq_zero _).2 (comp_mem_B0_left hψ φ.2))
    (fun _ hφ => LinearMap.mem_ker.2 <| LinearMap.ext fun ψ =>
      (Submodule.Quotient.mk_eq_zero _).2 (comp_mem_B0_right ψ.2 hφ))

/-- A5: `compH0` on representatives. -/
theorem compH0_mk (ψ : Z0 M₂ M₃) (φ : Z0 M₁ M₂) :
    compH0 M₁ M₂ M₃ (Submodule.Quotient.mk ψ) (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk (compZ0 M₁ M₂ M₃ ψ φ) := rfl

variable (M₁) in
/-- A5: the identity as a closed degree-0 map. -/
def idZ0 : Z0 M₁ M₁ := ⟨LinearMap.id, Submodule.mem_inf.2 ⟨id_mem M₁, δ_id M₁⟩⟩

variable (𝒜) in
/-- **A5.** The homotopy category `Ho(P_A)`: objects are cohesive modules (wrapped, so that the
category structure is not an instance on `CohesiveModule` itself), morphisms are `H⁰` of the Hom
complex. [B, §2.4]. -/
structure HoP : Type 1 where
  /-- The underlying cohesive module. -/
  as : CohesiveModule 𝒜

/-- **A5.** `Ho(P_A)` is a category: `H⁰` with composition `compH0` (A4.b). -/
instance : Category (HoP 𝒜) where
  Hom M N := H0 M.as.toQuasiCohesive N.as.toQuasiCohesive
  id M := Submodule.Quotient.mk (idZ0 _)
  comp f g := compH0 _ _ _ g f
  id_comp f := by
    induction f using Submodule.Quotient.induction_on
    exact congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.comp_id _))
  comp_id f := by
    induction f using Submodule.Quotient.induction_on
    exact congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.id_comp _))
  assoc f g h := by
    induction f using Submodule.Quotient.induction_on
    induction g using Submodule.Quotient.induction_on
    induction h using Submodule.Quotient.induction_on
    exact congrArg Submodule.Quotient.mk (Subtype.ext (LinearMap.comp_assoc _ _ _).symm)

/-- A5: `f ≫ g` in `Ho(P_A)` is `compH0 g f`. -/
theorem HoP.comp_def {M N P : HoP 𝒜} (f : M ⟶ N) (g : N ⟶ P) :
    f ≫ g = compH0 _ _ _ g f := rfl

/-- **A5.** `Ho(P_A)` is preadditive: composition is bilinear. -/
instance : Preadditive (HoP 𝒜) where
  homGroup M N := inferInstanceAs (AddCommGroup (H0 _ _))
  add_comp _ _ _ f f' g := by simp only [HoP.comp_def, map_add]
  comp_add _ _ _ f g g' := by simp only [HoP.comp_def, map_add, LinearMap.add_apply]

/-- **A5.** `Ho(P_A)` is `k`-linear. -/
instance : Linear k (HoP 𝒜) where
  homModule M N := inferInstanceAs (Module k (H0 _ _))
  smul_comp _ _ _ r f g := by simp only [HoP.comp_def, map_smul]
  comp_smul _ _ _ f r g := by simp only [HoP.comp_def, map_smul, LinearMap.smul_apply]

end Cohesive
