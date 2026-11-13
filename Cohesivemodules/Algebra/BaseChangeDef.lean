-- FROZEN (gate 3, 26 Oct 2026; A9 definitions, in the main statement). Do not edit without approval.
import Cohesivemodules.Algebra.GeneratorsDef
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.TensorProduct.Finite

set_option linter.style.header false

/-!
# A9: base change along maps of (possibly curved) dgas (definitions)

Blueprint item A9. This file holds definitions the main statement depends on; it is to be
frozen at gate 3. Theorems about them (functoriality, A9.a) stay in `Algebra/BaseChange.lean`.

For a map of (possibly curved) dgas `f : A → B` (A1 structures over the same `k`), a
quasi-cohesive module `M = (Q, 𝕏)` over `A` gives a quasi-cohesive module over `B` with generators
`B⁰ ⊗_{A⁰} Q^p` and `𝕏_B(b ⊗ m) = db ⊗ m + (-1)^{|b|} b·𝕏m`. [B, §2.7 with ω = 0].
The construction uses the A3.a constructor: on generators,
`θ'(β ⊗ e) = dβ ⊗ e + β·F(𝕏(1 ⊗ e))` with `F : A ⊗_{A⁰} ⨁Q → B ⊗_{B⁰} ⨁(B⁰ ⊗_{A⁰} Q)`,
`F(a ⊗ e) = f(a) ⊗ (1 ⊗ e)`.

Definitions: `DgaHom`, `DgaHom.toAlgHom`, its `CoeFun` instance, `DgaHom.f0`, `DgaHom.B0`
with its `CommRing` instance, `DgaHom.ofB0`, `toB`, the `Algebra` instance on `f.B0`, `BCGen`
with its instances, `BCGen.tmul`, `bcι`, `bcFAux`, `bcF`, `bcθAux`, `bcθp`, `bcθ`, `bcGenData`,
`QuasiCohesive.baseChange`, `CohesiveModule.baseChange`; together with the lemmas their
constructions need (e.g. `DgaHom.map_sigma`, `QuasiCohesive.X_tmul`, the Leibniz rule,
degree and flatness lemmas of `θ'`) and their basic API.

## Deviations from the sources
* Left modules (conventions §3); `ω = 0`.
* `B⁰` is an `A⁰`-module through `f` by the type synonym `BCGen f Q p`, which carries the
  instances (the module structure depends on the term `f`).
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

variable (𝒜 ℬ) in
/-- **A9** A map of bounded graded-commutative curved dgas: a `k`-algebra map preserving the
grading, the differential and the curvature. -/
structure DgaHom where
  /-- The underlying algebra map. -/
  toAlgHom : A →ₐ[k] B
  /-- `f` preserves degrees. -/
  map_mem : ∀ {q : ℤ} {a : A}, a ∈ 𝒜 q → toAlgHom a ∈ ℬ q
  /-- `f ∘ d = d ∘ f`. -/
  map_d : ∀ a, toAlgHom (GCDga.d (𝒜 := 𝒜) a) = GCDga.d (𝒜 := ℬ) (toAlgHom a)
  /-- `f(c) = c`. -/
  map_c : toAlgHom (GCDga.c (𝒜 := 𝒜)) = GCDga.c (𝒜 := ℬ)

namespace DgaHom

variable (f : DgaHom 𝒜 ℬ)

/-- A9: a map of (possibly curved) dgas as a function. -/
instance : CoeFun (DgaHom 𝒜 ℬ) (fun _ => A → B) := ⟨fun f => f.toAlgHom⟩

/-- A9: `f` is additive. -/
@[simp] theorem map_add' (a b : A) : f (a + b) = f a + f b := map_add f.toAlgHom a b
/-- A9: `f` is multiplicative. -/
@[simp] theorem map_mul' (a b : A) : f (a * b) = f a * f b := map_mul f.toAlgHom a b
/-- A9: `f(1) = 1`. -/
@[simp] theorem map_one' : f 1 = 1 := map_one f.toAlgHom
/-- A9: `f(0) = 0`. -/
@[simp] theorem map_zero' : f 0 = 0 := map_zero f.toAlgHom

/-- A9: `f` on degree `0`, as a ring map `A⁰ → B⁰`. -/
def f0 : 𝒜 0 →+* ℬ 0 where
  toFun r := ⟨f r, f.map_mem r.2⟩
  map_one' := Subtype.ext f.map_one'
  map_mul' r s := Subtype.ext (f.map_mul' r s)
  map_zero' := Subtype.ext f.map_zero'
  map_add' r s := Subtype.ext (f.map_add' r s)

/-- A9: formula for `f0`. -/
@[simp] theorem coe_f0 (r : 𝒜 0) : (f.f0 r : B) = f r := rfl

/-- A9: `f` commutes with the parity involution. -/
theorem map_sigma (a : A) : f (GCDga.sigma 𝒜 a) = GCDga.sigma ℬ (f a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, f.map_add', hx, hy, f.map_add', map_add]
  | @homogeneous i x =>
    rw [GCDga.sigma_of_mem 𝒜 x.2, GCDga.sigma_of_mem ℬ (f.map_mem x.2), Units.smul_def,
      Units.smul_def, map_zsmul]

end DgaHom

/-! ## Generators of the base change -/

variable (f : DgaHom 𝒜 ℬ) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- **A9** `B⁰` viewed as an `A⁰`-algebra through `f` (a type synonym carrying the instance,
which depends on the term `f`). -/
def DgaHom.B0 (_f : DgaHom 𝒜 ℬ) : Type := ℬ 0

/-- A9: the ring structure of `f.B0` (that of `B⁰`). -/
instance : CommRing (f.B0) := inferInstanceAs (CommRing (ℬ 0))

/-- A9: the identity `B⁰ → f.B0`. -/
def DgaHom.ofB0 (β : ℬ 0) : f.B0 := β

/-- A9: the identity `f.B0 → B⁰ ⊆ B`. -/
def toB (β : f.B0) : B := ((show ℬ 0 from β) : B)

/-- A9: `toB` is additive. -/
theorem toB_add (β β' : f.B0) : toB f (β + β') = toB f β + toB f β' := rfl

/-- A9: `toB` is multiplicative. -/
theorem toB_mul (β β' : f.B0) : toB f (β * β') = toB f β * toB f β' := rfl

/-- A9: `toB ∘ ofB0` is the inclusion. -/
@[simp] theorem toB_ofB0 (β : ℬ 0) : toB f (f.ofB0 β) = β := rfl

/-- A9: `B⁰` is an `A⁰`-algebra through `f`. -/
instance : Algebra (𝒜 0) (f.B0) := RingHom.toAlgebra (f.f0 : 𝒜 0 →+* f.B0)

/-- **A9** The generators `B⁰ ⊗_{A⁰} Q^p` of the base change. -/
def BCGen (p : ℤ) : Type := f.B0 ⊗[𝒜 0] Q p

section BCGenInstances

variable (p : ℤ)

/-- A9: the additive group of the generators. -/
instance : AddCommGroup (BCGen f Q p) := inferInstanceAs (AddCommGroup (f.B0 ⊗[𝒜 0] Q p))

/-- A9: the `B⁰`-module structure of the generators. -/
instance : Module (ℬ 0) (BCGen f Q p) := inferInstanceAs (Module (f.B0) (f.B0 ⊗[𝒜 0] Q p))

end BCGenInstances

/-- A9: `β ⊗ q` in the base-changed generators. -/
def BCGen.tmul {p : ℤ} (β : ℬ 0) (q : Q p) : BCGen f Q p := f.ofB0 β ⊗ₜ[𝒜 0] q

variable {f Q} in
/-- A9: formula for `BCGen.tmul` (definitional). -/
theorem BCGen.tmul_def {p : ℤ} (β : ℬ 0) (q : Q p) :
    BCGen.tmul f Q β q = (f.ofB0 β ⊗ₜ[𝒜 0] q : f.B0 ⊗[𝒜 0] Q p) := rfl

/-- A9: the `A⁰`-module structure of the generators. -/
instance (p : ℤ) : Module (𝒜 0) (BCGen f Q p) :=
  inferInstanceAs (Module (𝒜 0) (f.B0 ⊗[𝒜 0] Q p))

/-- A9: on `B⁰ ⊗_{A⁰} Q^p`, the `A⁰`-action is the `B⁰`-action through `f`. -/
theorem tensor_smul0_eq {p : ℤ} (r : 𝒜 0) (x : f.B0 ⊗[𝒜 0] Q p) :
    r • x = algebraMap (𝒜 0) f.B0 r • x := by
  induction x using TensorProduct.inductionOn with
  | tmul β q =>
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def]
    rfl
  | add x y hx hy => rw [smul_add, hx, hy, smul_add]

/-- A9: the `A⁰`-action on the generators is the `B⁰`-action through `f`. -/
theorem BCGen.smul0_eq {p : ℤ} (r : 𝒜 0) (x : BCGen f Q p) : r • x = f.f0 r • x :=
  tensor_smul0_eq f Q r (x : f.B0 ⊗[𝒜 0] Q p)

/-- **A9** The generator embedding `ι(q) = 1 ⊗ q`, as an `A⁰`-linear map. -/
def bcι : (⨁ p, Q p) →ₗ[𝒜 0] (⨁ p, BCGen f Q p) :=
  DirectSum.lmap fun p => TensorProduct.mk (𝒜 0) f.B0 (Q p) 1

/-- A9: `ι` on a homogeneous generator. -/
theorem bcι_lof (p : ℤ) (q : Q p) :
    bcι f Q (lof (𝒜 0) ℤ Q p q) = lof (ℬ 0) ℤ (BCGen f Q) p (BCGen.tmul f Q 1 q) :=
  DirectSum.lmap_lof _ p q

/-- A9: `ι(r e) = f(r) ι(e)`. -/
theorem bcι_smul (r : 𝒜 0) (e : ⨁ p, Q p) : bcι f Q (r • e) = f.f0 r • bcι f Q e := by
  rw [map_smul]
  ext p
  rw [DirectSum.smul_apply, DirectSum.smul_apply, BCGen.smul0_eq]

/-- The bi-additive map `(a, e) ↦ f(a) ⊗ ι(e)`. -/
def bcFAux : A →+ (⨁ p, Q p) →+ Tot ℬ (BCGen f Q) :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk' (fun e => Tot.tmul ℬ _ (f a) (bcι f Q e))
      (fun e e' => by rw [map_add, Tot.tmul_add]))
    (fun a b => AddMonoidHom.ext fun e => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, f.map_add', Tot.add_tmul])

/-- **A9** The comparison map `F : A ⊗_{A⁰} ⨁Q → B ⊗_{B⁰} ⨁(B⁰ ⊗_{A⁰} Q)`,
`F(a ⊗ e) = f(a) ⊗ ι(e)`. -/
def bcF : Tot 𝒜 Q →+ Tot ℬ (BCGen f Q) :=
  TensorProduct.liftAddHom (R := 𝒜 0) (bcFAux f Q) fun r a e => by
    show Tot.tmul ℬ _ (f (r • a)) (bcι f Q e) = Tot.tmul ℬ _ (f a) (bcι f Q (r • e))
    rw [bcι_smul, Tot.tmul_smul0, GCDga.smul0_def, f.map_mul', DgaHom.coe_f0,
      GCDga.central ℬ (f.map_mem r.2)]

/-- A9: `F` on pure tensors. -/
theorem bcF_tmul (a : A) (e : ⨁ p, Q p) :
    bcF f Q (Tot.tmul 𝒜 Q a e) = Tot.tmul ℬ _ (f a) (bcι f Q e) := rfl

/-- A9: `F` is semilinear along `f`: `F(a·x) = f(a)·F(x)`. -/
theorem bcF_smul (a : A) (x : Tot 𝒜 Q) : bcF f Q (a • x) = f a • bcF f Q x := by
  induction x using Tot.induction_on with
  | ht b e => rw [Tot.smul_tmul, bcF_tmul, bcF_tmul, Tot.smul_tmul, f.map_mul']
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- A9: `F` is `k`-linear. -/
theorem bcF_smul_k (r : k) (x : Tot 𝒜 Q) : bcF f Q (r • x) = r • bcF f Q x := by
  rw [← algebraMap_smul A r x, bcF_smul, ← algebraMap_smul B r (bcF f Q x),
    show f (algebraMap k A r) = algebraMap k B r from f.toAlgHom.commutes r]

/-- A9: `F` preserves the total degree. -/
theorem bcF_mem_totDeg {m : ℤ} {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) :
    bcF f Q x ∈ totDeg ℬ (BCGen f Q) m := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change bcF f Q (Tot.tmul 𝒜 Q a _) ∈ _
    rw [bcF_tmul, bcι_lof]
    exact tmul_mem_totDeg (f.map_mem ha) _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [bcF_smul_k]; exact Submodule.smul_mem _ r hx

/-! ## Pure tensors in the generators -/

namespace BCGen

variable {f Q}

/-- A9: `β ⊗ q` is additive in `q`. -/
theorem tmul_add {p : ℤ} (β : ℬ 0) (q q' : Q p) :
    BCGen.tmul f Q β (q + q') = BCGen.tmul f Q β q + BCGen.tmul f Q β q' :=
  TensorProduct.tmul_add (f.ofB0 β) q q'

/-- A9: `β ⊗ q` is additive in `β`. -/
theorem add_tmul {p : ℤ} (β β' : ℬ 0) (q : Q p) :
    BCGen.tmul f Q (β + β') q = BCGen.tmul f Q β q + BCGen.tmul f Q β' q :=
  TensorProduct.add_tmul (f.ofB0 β) (f.ofB0 β') q

/-- A9: `γ • (β ⊗ q) = (γβ) ⊗ q`. -/
theorem smul_tmul {p : ℤ} (γ β : ℬ 0) (q : Q p) :
    γ • BCGen.tmul f Q β q = BCGen.tmul f Q (γ * β) q :=
  TensorProduct.smul_tmul' (R := 𝒜 0) (f.ofB0 γ) (f.ofB0 β) q

/-- A9: `β ⊗ q = β • (1 ⊗ q)`. -/
theorem tmul_eq_smul {p : ℤ} (β : ℬ 0) (q : Q p) :
    BCGen.tmul f Q β q = β • BCGen.tmul f Q 1 q := by
  rw [smul_tmul, mul_one]

/-- A9: `1 ⊗ (r q) = f(r) • (1 ⊗ q)`. -/
theorem tmul_smul0 {p : ℤ} (r : 𝒜 0) (q : Q p) :
    BCGen.tmul f Q 1 (r • q) = f.f0 r • BCGen.tmul f Q 1 q := by
  rw [← BCGen.smul0_eq]
  exact (TensorProduct.smul_tmul (R := 𝒜 0) r (1 : f.B0) q).symm.trans
    (TensorProduct.smul_tmul' (R := 𝒜 0) r (1 : f.B0) q).symm

/-- A9: induction on the generators. -/
theorem induction_on {p : ℤ} {C : BCGen f Q p → Prop} (x : BCGen f Q p)
    (ht : ∀ β q, C (BCGen.tmul f Q β q)) (hadd : ∀ x y, C x → C y → C (x + y)) : C x :=
  TensorProduct.inductionOn (R := 𝒜 0) (M := f.B0) (N := Q p) x ht hadd

end BCGen

/-- A3.a (general form): `𝕏(a ⊗ e) = da ⊗ e + σ(a)·𝕏(1 ⊗ e)` for any quasi-cohesive module. -/
theorem QuasiCohesive.X_tmul (M : QuasiCohesive 𝒜) (a : A) (e : ⨁ p, M.Q p) :
    M.X (Tot.tmul 𝒜 M.Q a e) =
      Tot.tmul 𝒜 M.Q (GCDga.d (𝒜 := 𝒜) a) e + GCDga.sigma 𝒜 a • M.X (Tot.tmul 𝒜 M.Q 1 e) := by
  conv_lhs => rw [Tot.tmul_eq_sum, map_sum]
  conv_rhs => rw [← GCDga.sum_proj 𝒜 a, map_sum, map_sum, ← Tot.tmulLeft_apply, map_sum,
    Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hq := GCDga.proj_mem 𝒜 q a
  rw [Tot.tmul_eq_smul (GCDga.proj 𝒜 q a), M.leibniz hq, Tot.tmulLeft_apply,
    Tot.tmul_eq_smul (GCDga.d (𝒜 := 𝒜) _), GCDga.sigma_of_mem 𝒜 hq, smul_assoc]

/-! ## The generator data of the base change -/

variable (M : QuasiCohesive 𝒜)

/-- The bi-additive map `(β, q) ↦ dβ ⊗ (1 ⊗ q) + β·F(𝕏(1 ⊗ q))` on degree `p`. -/
def bcθAux (p : ℤ) : f.B0 →+ M.Q p →+ Tot ℬ (BCGen f M.Q) :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk'
      (fun q => Tot.tmul ℬ _ (GCDga.d (𝒜 := ℬ) (toB f β))
          (lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q)) +
        toB f β • bcF f M.Q (M.X (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q))))
      (fun q q' => by
        rw [BCGen.tmul_add, map_add, Tot.tmul_add, map_add, Tot.tmul_add, map_add, map_add,
          smul_add]
        abel))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [toB_add, map_add, Tot.add_tmul, add_smul]
      abel)

/-- A9: `F(1 ⊗ e) = 1 ⊗ ι(e)`. -/
theorem bcF_tmul_one (e : ⨁ p, M.Q p) :
    bcF f M.Q (Tot.tmul 𝒜 M.Q 1 e) = Tot.tmul ℬ _ 1 (bcι f M.Q e) := by
  rw [bcF_tmul, f.map_one']

/-- A9: `toB (algebraMap r) = f r`. -/
theorem toB_algebraMap (r : 𝒜 0) : toB f (algebraMap (𝒜 0) f.B0 r) = f r := rfl

/-- The bi-additive map is `A⁰`-balanced. -/
theorem bcθAux_balanced (p : ℤ) (r : 𝒜 0) (β : f.B0) (q : M.Q p) :
    bcθAux f M p (r • β) q = bcθAux f M p β (r • q) := by
  simp only [bcθAux, AddMonoidHom.mk'_apply]
  rw [Algebra.smul_def, toB_mul, toB_algebraMap, BCGen.tmul_smul0, map_smul, Tot.tmul_smul0,
    DgaHom.coe_f0, map_smul, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (r : A),
    M.leibniz r.2, Int.negOnePow_zero, one_smul, (bcF f M.Q).map_add, bcF_smul, bcF_smul,
    bcF_tmul_one, bcι_lof, f.map_d, GCDga.leibniz_zero ℬ (f.map_mem r.2), Tot.add_tmul,
    smul_add, Tot.smul_tmul, Tot.smul_tmul, mul_one, ← mul_smul]
  rw [GCDga.central ℬ (f.map_mem r.2) (GCDga.d (𝒜 := ℬ) (toB f β)),
    GCDga.central ℬ (f.map_mem r.2) (toB f β),
    ← GCDga.central ℬ (show toB f β ∈ ℬ 0 from (show ℬ 0 from β).2)
      (GCDga.d (𝒜 := ℬ) (f r))]
  abel

/-- **A9** `θ'` on the degree-`p` generators `B⁰ ⊗_{A⁰} Q^p`. -/
def bcθp (p : ℤ) : BCGen f M.Q p →+ Tot ℬ (BCGen f M.Q) :=
  TensorProduct.liftAddHom (R := 𝒜 0) (bcθAux f M p) (bcθAux_balanced f M p)

/-- A9: `θ'(β ⊗ q) = dβ ⊗ (1 ⊗ q) + β·F(𝕏(1 ⊗ q))`. -/
theorem bcθp_tmul (p : ℤ) (β : ℬ 0) (q : M.Q p) :
    bcθp f M p (BCGen.tmul f M.Q β q) =
      Tot.tmul ℬ _ (GCDga.d (𝒜 := ℬ) β) (lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q)) +
        (β : B) • bcF f M.Q (M.X (Tot.tmul 𝒜 M.Q 1 (lof (𝒜 0) ℤ M.Q p q))) := rfl

/-- **A9** The generator data `θ'` of the base change. -/
def bcθ : (⨁ p, BCGen f M.Q p) →+ Tot ℬ (BCGen f M.Q) := DirectSum.toAddMonoid (bcθp f M)

/-- A9: `θ'` on a homogeneous generator. -/
theorem bcθ_of (p : ℤ) (x : BCGen f M.Q p) :
    bcθ f M (DirectSum.of (BCGen f M.Q) p x) = bcθp f M p x :=
  DirectSum.toAddMonoid_of _ p x

/-- A9: `θ'(ι e) = F(𝕏(1 ⊗ e))`. -/
theorem bcθ_bcι (e : ⨁ p, M.Q p) :
    bcθ f M (bcι f M.Q e) = bcF f M.Q (M.X (Tot.tmul 𝒜 M.Q 1 e)) := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p q =>
    rw [show DirectSum.of M.Q p q = lof (𝒜 0) ℤ M.Q p q from rfl, bcι_lof]
    rw [show lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q) =
      DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q) from rfl, bcθ_of, bcθp_tmul,
      show ((1 : ℬ 0) : B) = 1 from rfl, GCDga.d_one, Tot.zero_tmul, zero_add, one_smul]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, Tot.tmul_add, map_add, map_add]

/-- A9: the Leibniz rule of `θ'` over `B⁰`. -/
theorem bcθ_leibniz (γ : ℬ 0) (e : ⨁ p, BCGen f M.Q p) :
    bcθ f M (γ • e) = Tot.tmul ℬ _ (GCDga.d (𝒜 := ℬ) γ) e + (γ : B) • bcθ f M e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    induction x using BCGen.induction_on with
    | ht β q =>
      rw [show γ • DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q β q) =
          DirectSum.of (BCGen f M.Q) p (γ • BCGen.tmul f M.Q β q) from
          (map_smul (DirectSum.lof (ℬ 0) ℤ (BCGen f M.Q) p) γ _).symm,
        BCGen.smul_tmul, bcθ_of, bcθ_of, bcθp_tmul, bcθp_tmul,
        show ((γ * β : ℬ 0) : B) = (γ : B) * β from rfl,
        GCDga.leibniz_zero ℬ γ.2, Tot.add_tmul, smul_add, Tot.smul_tmul, mul_smul]
      rw [show DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q β q) =
          (β : ℬ 0) • lof (ℬ 0) ℤ (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q) by
          rw [← map_smul, ← BCGen.tmul_eq_smul]; rfl,
        Tot.tmul_smul0]
      abel
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f M.Q) p).map_add, smul_add, map_add, hx, hy, map_add,
        Tot.tmul_add, smul_add]
      abel
  | add x y hx hy =>
    rw [smul_add, map_add, hx, hy, map_add, Tot.tmul_add, smul_add]
    abel

/-- **A9** The generator data of the base change. -/
def bcGenData : GenData ℬ (BCGen f M.Q) where
  θ := bcθ f M
  leibniz := bcθ_leibniz f M

/-- A9: the generator data is `θ'`. -/
theorem bcGenData_θ : (bcGenData f M).θ = bcθ f M := rfl

/-- A9: `θ'` has total degree `1`. -/
theorem bcθ_mem (p : ℤ) (x : BCGen f M.Q p) :
    bcθ f M (lof (ℬ 0) ℤ (BCGen f M.Q) p x) ∈ totDeg ℬ (BCGen f M.Q) (p + 1) := by
  induction x using BCGen.induction_on with
  | ht β q =>
    change bcθ f M (DirectSum.of _ p _) ∈ _
    rw [bcθ_of, bcθp_tmul]
    refine add_mem ?_ ?_
    · have := tmul_mem_totDeg (Q := BCGen f M.Q) (GCDga.d_mem_one ℬ β.2) (BCGen.tmul f M.Q 1 q)
      rwa [add_comm] at this
    · have h1 := tmul_mem_totDeg (Q := M.Q) (SetLike.GradedOne.one_mem (A := 𝒜)) q
      have h2 := smul_mem_totDeg β.2 (bcF_mem_totDeg f M.Q (M.X_mem h1))
      rwa [zero_add, zero_add] at h2
  | hadd x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/-- A9: the extension of `θ'` intertwines `F`: `𝕏' ∘ F = F ∘ 𝕏`. -/
theorem bc_extend_bcF (x : Tot 𝒜 M.Q) :
    (bcGenData f M).extend (bcF f M.Q x) = bcF f M.Q (M.X x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul, GenData.extend_tmul, M.X_tmul, (bcF f M.Q).map_add, bcF_tmul, bcF_smul,
      ← f.map_d, ← f.map_sigma, bcGenData_θ, bcθ_bcι]
  | hadd x y hx hy => rw [(bcF f M.Q).map_add, map_add, hx, hy, map_add, (bcF f M.Q).map_add]

/-- A9: the base change is flat on its generators. -/
theorem bc_flat (e : ⨁ p, BCGen f M.Q p) :
    (bcGenData f M).extend ((bcGenData f M).θ e) =
      GCDga.c (𝒜 := ℬ) • Tot.tmul ℬ _ 1 e := by
  have hι : ∀ y, (bcGenData f M).extend (bcθ f M (bcι f M.Q y)) =
      GCDga.c (𝒜 := ℬ) • Tot.tmul ℬ _ 1 (bcι f M.Q y) := fun y => by
    rw [bcθ_bcι, bc_extend_bcF, M.flat, bcF_smul, f.map_c, bcF_tmul_one]
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    induction x using BCGen.induction_on with
    | ht β q =>
      have hx : DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q β q) =
          (β : ℬ 0) • bcι f M.Q (lof (𝒜 0) ℤ M.Q p q) := by
        rw [bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul]; rfl
      have hβ1 := GCDga.d_mem_one ℬ β.2
      rw [hx]
      change (bcGenData f M).extend (bcθ f M _) = _
      rw [bcθ_leibniz, map_add, Tot.tmul_eq_smul, (bcGenData f M).extend_leibniz hβ1,
        (bcGenData f M).extend_leibniz β.2, GenData.extend_tmul_one, GCDga.d_d, zero_smul,
        zero_add]
      rw [bcGenData_θ, hι, Int.negOnePow_one, Int.negOnePow_zero, Units.neg_smul, one_smul,
        one_smul, smul_smul (β : B) (GCDga.c (𝒜 := ℬ)), ← GCDga.c_central ℬ (β : B), mul_smul,
        Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (β : B)]
      abel
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f M.Q) p).map_add, map_add, map_add, hx, hy, Tot.tmul_add,
        smul_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, Tot.tmul_add, smul_add]

/-- **A9** Base change of a quasi-cohesive module along a map of (possibly curved) dgas
`f : A → B`: generators `B⁰ ⊗_{A⁰} Q^p`, `𝕏_B(b ⊗ m) = db ⊗ m + (-1)^{|b|} b·𝕏m`.
[B, §2.7 with ω = 0]. -/
def QuasiCohesive.baseChange : QuasiCohesive ℬ :=
  QuasiCohesive.ofGenerators (BCGen f M.Q) (bcGenData f M) (bcθ_mem f M) (bc_flat f M)

/-- **A9** Base change of a cohesive module is cohesive: `B⁰ ⊗_{A⁰} Q^p` is finitely generated
projective, and vanishes where `Q^p` does. [B, §2.7]. -/
def CohesiveModule.baseChange (M : CohesiveModule 𝒜) : CohesiveModule ℬ where
  toQuasiCohesive := M.toQuasiCohesive.baseChange f
  bounded := by
    obtain ⟨a, b, h⟩ := M.bounded
    refine ⟨a, b, fun p hp => ?_⟩
    have := h p hp
    exact inferInstanceAs (Subsingleton (f.B0 ⊗[𝒜 0] M.Q p))
  finite p := by
    have := M.finite p
    exact inferInstanceAs (Module.Finite f.B0 (f.B0 ⊗[𝒜 0] M.Q p))
  projective p := by
    have := M.projective p
    exact inferInstanceAs (Module.Projective f.B0 (f.B0 ⊗[𝒜 0] M.Q p))

end Cohesive

end
