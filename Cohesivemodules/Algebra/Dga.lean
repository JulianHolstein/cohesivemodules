-- FROZEN (23 Oct 2026; A1, in the main statement). Do not edit without approval.
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.Ring.NegOnePow

set_option linter.style.header false

/-!
# A1: bounded graded-commutative curved dgas

Blueprint item A1 (conventions §1, §2, §5). Sources: [B, Def 2.2.1] (curved dga; arXiv v2
numbering) and [A, Rem 4.0.4] (the cdga `(A^*, h)`: a non-negatively graded,
graded-commutative dga with closed `h ∈ A²`).

A total `k`-algebra `A` with an internal `ℤ`-grading `𝒜 : ℤ → Submodule k A`
(`[GradedAlgebra 𝒜]`), zero in negative degrees and above a top degree `N`, graded-commutative,
with a degree-one differential satisfying the graded Leibniz rule, and a closed curvature
element of degree 2.

From graded commutativity we build the commutative ring `A⁰ = 𝒜 0` and the `A⁰`-algebra
structure on `A`. Mathlib's `SetLike.GradeZero.instCommRing` cannot be used, because it needs
`A` itself to be commutative.

## Deviations from the sources
* [B, Def 2.2.1] allows non-graded-commutative `A` and asks `d²(a) = [c, a]`. We require graded
  commutativity, as [A, Rem 4.0.4] does; then `c` (even degree) is central, `[c, a] = 0`, and
  Block's condition is exactly `d² = 0`, which is what we state.
* [B] works over a field of characteristic 0, [A] over `𝕂 = ℝ, ℂ`; we allow any commutative ring
  `k` (only `k = ℂ` is used for the main theorem).
* Boundedness (`A^q = 0` for `q > N`) is not in the sources' definitions; it holds for the
  Dolbeault algebra and is used in A6 and A11 (blueprint §2 setting).
* ⚠ The grading is indexed by `ℤ` (with `A^q = 0` for `q < 0`), not by `ℕ`. The form degree,
  the internal degree of modules and the total degree then share one index type, and signs are
  `Int.negOnePow` as in Mathlib's `CochainComplex.HomComplex` (blueprint v1.2).
* Graded commutativity and boundedness are part of the structure (no Mathlib class exists).
* The curvature `c` is carried for generality; this project only uses `c = 0` outside layer A.
  Its sign relative to Block's curvature is fixed in A3 (conventions §3: `c_here = -c_Block`).
-/

namespace Cohesive

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]

/-- **A1.** A bounded graded-commutative curved dga structure on the internally `ℤ`-graded
`k`-algebra `(A, 𝒜)`. Sources: [B, Def 2.2.1], [A, Rem 4.0.4] (see the module docstring).

Informally: `A = ⨁_{0 ≤ q ≤ N} A^q` with `A^q = 𝒜 q`; `ab = (-1)^{pq} ba` for `a ∈ A^p`,
`b ∈ A^q`; `d : A → A` is `k`-linear of degree `+1` with `d(ab) = da·b + (-1)^p a·db` for
`a ∈ A^p` and `d ∘ d = 0`; `c ∈ A^2` with `dc = 0`.

Deviations (details in the module docstring): graded commutativity required, so Block's
`d² = [c, -]` becomes `d² = 0`; any commutative ring `k`; boundedness; ⚠ `ℤ`-indexed grading,
zero in negative degrees. -/
class GCDga (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] where
  /-- The top degree: `A^q = 0` for `q > N`. -/
  N : ℕ
  /-- `A^q = 0` for `q < 0`. -/
  zero_of_neg : ∀ q < 0, 𝒜 q = ⊥
  /-- `A^q = 0` for `q > N`. -/
  zero_of_gt : ∀ q, (N : ℤ) < q → 𝒜 q = ⊥
  /-- Graded commutativity: `ab = (-1)^{pq} ba` for `a ∈ A^p`, `b ∈ A^q`. -/
  gcomm : ∀ {p q : ℤ} {a b : A}, a ∈ 𝒜 p → b ∈ 𝒜 q → a * b = (p * q).negOnePow • (b * a)
  /-- The differential. -/
  d : A →ₗ[k] A
  /-- `d` has degree `+1`. -/
  d_mem : ∀ {q : ℤ} {a : A}, a ∈ 𝒜 q → d a ∈ 𝒜 (q + 1)
  /-- Graded Leibniz rule: `d(ab) = da·b + (-1)^p a·db` for `a ∈ A^p` and any `b`. -/
  leibniz : ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ b, d (a * b) = d a * b + p.negOnePow • (a * d b)
  /-- `d ∘ d = 0`. -/
  d_d : ∀ a, d (d a) = 0
  /-- The curvature. -/
  c : A
  /-- The curvature has degree 2. -/
  c_mem : c ∈ 𝒜 2
  /-- The curvature is closed. -/
  d_c : d c = 0

namespace GCDga

variable (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- A1: elements of negative degree vanish. -/
theorem eq_zero_of_neg {q : ℤ} (hq : q < 0) {a : A} (ha : a ∈ 𝒜 q) : a = 0 := by
  rwa [zero_of_neg (𝒜 := 𝒜) q hq, Submodule.mem_bot] at ha

/-- A1: elements of degree above the top degree `N` vanish. -/
theorem eq_zero_of_gt {q : ℤ} (hq : (N 𝒜 : ℤ) < q) {a : A} (ha : a ∈ 𝒜 q) : a = 0 := by
  rwa [zero_of_gt q hq, Submodule.mem_bot] at ha

/-- A1: elements of degree 0 are central (graded commutativity with `p = 0`). -/
theorem central {a : A} (ha : a ∈ 𝒜 0) (b : A) : a * b = b * a := by
  induction b using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m => simpa using gcomm ha m.2
  | add m m' h h' => rw [mul_add, add_mul, h, h']

/-- A1: `A⁰ = 𝒜 0` is a commutative ring. The ring structure is Mathlib's
`SetLike.GradeZero.instRing`; commutativity comes from graded commutativity (`A` itself is not
commutative). For commutative `A` this agrees with `SetLike.GradeZero.instCommRing`. -/
instance commRing0 : CommRing (𝒜 0) :=
  { SetLike.GradeZero.instRing 𝒜 with
    mul_comm := fun a b => Subtype.ext (central 𝒜 a.2 b) }

/-- A1: the inclusion `A⁰ → A` as a ring homomorphism. -/
def incl0 : 𝒜 0 →+* A where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- A1: `A` is an `A⁰`-algebra, because `A⁰` is central. This is the structure used for
tensor products `A ⊗_{A⁰} Q` (conventions §5). -/
instance algebra0 : Algebra (𝒜 0) A :=
  RingHom.toAlgebra' (incl0 𝒜) fun a b => central 𝒜 a.2 b

/-- A1: `algebraMap A⁰ A` is the inclusion. -/
@[simp] theorem algebraMap0_apply (f : 𝒜 0) : algebraMap (𝒜 0) A f = f := rfl

/-- A1: the action of `A⁰` on `A` is left multiplication. -/
theorem smul0_def (f : 𝒜 0) (a : A) : f • a = (f : A) * a := rfl

/-- A1: the degree-`q` part `A^q` as an `A⁰`-submodule of `A` (same carrier as `𝒜 q`; `A⁰` acts
by left multiplication). Used for tensor products `A^q ⊗_{A⁰} P`. -/
def piece (q : ℤ) : Submodule (𝒜 0) A where
  carrier := 𝒜 q
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' f a ha := by
    rw [smul0_def]
    simpa using SetLike.GradedMul.mul_mem f.2 ha

/-- A1: membership in `piece 𝒜 q` is membership in `𝒜 q`. -/
@[simp] theorem mem_piece {q : ℤ} {a : A} : a ∈ piece 𝒜 q ↔ a ∈ 𝒜 q := Iff.rfl

/-- A1: the action of `A⁰` on `A^q` is left multiplication. -/
@[simp] theorem coe_smul_piece {q : ℤ} (f : 𝒜 0) (a : piece 𝒜 q) :
    ((f • a : piece 𝒜 q) : A) = (f : A) * a := rfl

/-- A1 (sanity): `d 1 = 0`, from the Leibniz rule with `a = b = 1`. -/
@[simp] theorem d_one : d (𝒜 := 𝒜) 1 = 0 := by
  have h := leibniz (𝒜 := 𝒜) (SetLike.GradedOne.one_mem (A := 𝒜)) (1 : A)
  simpa using h

/-- A1 (sanity): `d` kills the scalars `k`. -/
@[simp] theorem d_algebraMap (r : k) : d (𝒜 := 𝒜) (algebraMap k A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, d_one, smul_zero]

/-- A1: on degree 0 the Leibniz rule has no sign: `d(fb) = df·b + f·db` for `f ∈ A⁰`. -/
theorem leibniz_zero {f : A} (hf : f ∈ 𝒜 0) (b : A) :
    d (𝒜 := 𝒜) (f * b) = d (𝒜 := 𝒜) f * b + f * d (𝒜 := 𝒜) b := by
  simpa using leibniz (𝒜 := 𝒜) hf b

/-- A1: `d` maps `A⁰` to `A¹`. -/
theorem d_mem_one {f : A} (hf : f ∈ 𝒜 0) : d (𝒜 := 𝒜) f ∈ 𝒜 1 := by
  simpa using d_mem (𝒜 := 𝒜) hf

end GCDga

end Cohesive
