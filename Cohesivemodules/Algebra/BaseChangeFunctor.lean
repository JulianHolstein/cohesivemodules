import Cohesivemodules.Algebra.Cohesive
import Cohesivemodules.Algebra.BaseChangeDef
import Cohesivemodules.Algebra.BaseChangeHomDef
import Cohesivemodules.Algebra.FromComplexDef
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option linter.style.header false

/-!
# A9: base change along maps of (possibly curved) dgas

Blueprint item A9. For a map of (possibly curved) dgas `f : A → B` (A1 structures over the same
`k`; `f` preserves the curvature), a quasi-cohesive
module `M = (Q, 𝕏)` over `A` gives a quasi-cohesive module over `B` with generators
`B⁰ ⊗_{A⁰} Q^p` and `𝕏_B(b ⊗ m) = db ⊗ m + (-1)^{|b|} b·𝕏m`. [B, §2.7 with ω = 0].

The construction uses the A3.a constructor: on generators,
`θ'(β ⊗ e) = dβ ⊗ e + β·F(𝕏(1 ⊗ e))` with `F : A ⊗_{A⁰} ⨁Q → B ⊗_{B⁰} ⨁(B⁰ ⊗_{A⁰} Q)`,
`F(a ⊗ e) = f(a) ⊗ (1 ⊗ e)`.

The definitions (`DgaHom`, `QuasiCohesive.baseChange`, …, and A10's `QuasiCohesive.fromComplex`,
`CohesiveModule.fromComplex`, …) are in `Algebra/BaseChangeDef.lean` and
`Algebra/FromComplexDef.lean`. The base change of morphisms (`bcGen`, `bcGenHom`, `bcHomL`,
with `bcHomL_mem`, `bcHomL_tmul`) is in `Algebra/BaseChangeHomDef.lean`.

## Relation to the sources
* The generators `B⁰ ⊗_{A⁰} Q^p` are exactly Block's `E^• ⊗_{𝒜₁} 𝒜₂` [B, §2.7] (left modules,
  `ω = 0`), and `θ'` is his `𝔼₂(e ⊗ b) = 𝔼(e)b + e ⊗ d₂b` on generators. The total module
  `B ⊗_{B⁰} ⨁_p (B⁰ ⊗_{A⁰} Q^p)` is `B ⊗_A M` up to the canonical isomorphism (not formalized).

A9.a (composite base change): for `f : A → B`, `g : B → C`, the comparison
`(g ∘ f)^*M → g^*(f^*M)`, `c ⊗ (γ ⊗ q) ↦ c ⊗ (γ ⊗ (1 ⊗ q))`, is a closed degree-`0` map with
closed inverse `c ⊗ (γ ⊗ (β ⊗ q)) ↦ c ⊗ (γ g(β) ⊗ q)`, natural on Hom complexes in every degree
(`bcCompTot_natural`); on `Ho(P)` it gives `bcCompNatIso`.

A10 (cohesive modules from complexes): for a ring map `ρ : R → A⁰` with `d ∘ ρ = 0` and a
complex `W` of `R`-modules (a Mathlib `CochainComplex (ModuleCat R) ℤ`), `A ⊗_R W` with
`𝕏 = d ⊗ 1 + 1 ⊗ d_W` on the generators `A⁰ ⊗_R W^p` (`QuasiCohesive.fromComplex`); cohesive if
`W` is bounded with finitely generated projective terms (`CohesiveModule.fromComplex`). [A,
Assumption 6 (§7.2)]. A10.a: `fcHomEquiv : Hom^n(A ⊗_R W, N) ≃+ Hom^n_R(W, N)` by restriction
along `w ↦ 1 ⊗ (1 ⊗ w)`, commuting with the differentials (`fcResP_δ`); `Hom^n_R(W, N)`
(`HomR`) is the group of families of `ρ`-semilinear maps `W^p → N` of total degree `p + n`, with
differential `homRδ` (conventions §2 signs).

## Deviations from the sources
* Left modules (conventions §3); `ω = 0`.
* A10 assumes `c = 0` (needed for `𝕏² = c`; the blueprint uses A10 only at `c = 0`). A10.a is
  an isomorphism of abelian groups in each degree commuting with the differentials (no
  `R`- or `k`-module structure on `Hom^n_R(W, N)` is introduced).
* `B⁰` is an `A⁰`-module through `f` by the type synonym `BCGen f Q p`, which carries the
  instances (the module structure depends on the term `f`).

Part 1 of 3 of the original `Algebra/BaseChange.lean`, split for size; continued in
`Algebra/BaseChangeComp.lean`.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

namespace DgaHom

variable (f : DgaHom 𝒜 ℬ)

/-- A9: `f` commutes with the homogeneous projections. -/
theorem map_proj (q : ℤ) (a : A) : f (GCDga.proj 𝒜 q a) = GCDga.proj ℬ q (f a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, f.map_add', hx, hy, f.map_add', map_add]
  | @homogeneous i x =>
    rw [GCDga.proj_of_mem 𝒜 x.2, GCDga.proj_of_mem ℬ (f.map_mem x.2)]
    split_ifs <;> simp

/-- A9: `f` commutes with the sign twists. -/
theorem map_twist (n : ℤ) (a : A) : f (GCDga.twist 𝒜 n a) = GCDga.twist ℬ n (f a) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add x y hx hy => rw [map_add, f.map_add', hx, hy, f.map_add', map_add]
  | @homogeneous i x =>
    rw [GCDga.twist_of_mem 𝒜 n x.2, GCDga.twist_of_mem ℬ n (f.map_mem x.2), Units.smul_def,
      Units.smul_def, map_zsmul]

variable (𝒜) in
/-- A9: the identity map of a (possibly curved) dga. -/
def id : DgaHom 𝒜 𝒜 where
  toAlgHom := AlgHom.id k A
  map_mem ha := ha
  map_d _ := rfl
  map_c := rfl

end DgaHom

/-! ## Base change (definitions in `Algebra/BaseChangeDef.lean`) -/

variable (f : DgaHom 𝒜 ℬ) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

variable (M : QuasiCohesive 𝒜)

/-! ## A9: functoriality on Hom complexes -/

section Functoriality

variable {M₁ M₂ : QuasiCohesive 𝒜} (n : ℤ)

/-- **A9** `f^*φ ∘ F = F ∘ φ`. -/
theorem bcHomL_bcF (φ : Hom M₁ M₂ n) (x : M₁.T) :
    bcHomL f n φ (bcF f M₁.Q x) = bcF f M₂.Q (φ.1 x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul, bcHomL_tmul, bcGen_bcι, hom_tmul φ.2 a e, bcF_smul, f.map_twist]
    rfl
  | hadd x y hx hy => rw [(bcF f M₁.Q).map_add, map_add, hx, hy, map_add, (bcF f M₂.Q).map_add]

/-- **A9** Maps of degree `n` out of a base change are determined on the image of `F` (the
target `N` is any quasi-cohesive `B`-module). -/
theorem hom_eq_of_bcF' {N : QuasiCohesive ℬ} {χ χ' : Tot ℬ (BCGen f M₁.Q) →ₗ[k] N.T}
    (hχ : χ ∈ Hom (M₁.baseChange f) N n)
    (hχ' : χ' ∈ Hom (M₁.baseChange f) N n)
    (h : ∀ x, χ (bcF f M₁.Q x) = χ' (bcF f M₁.Q x)) : χ = χ' := by
  have s₁ : ∀ {p : ℤ} {b : B}, b ∈ ℬ p → ∀ y : Tot ℬ (BCGen f M₁.Q),
      χ (b • y) = (n * p).negOnePow • b • χ y := fun hb y => hχ.2 hb y
  have s₂ : ∀ {p : ℤ} {b : B}, b ∈ ℬ p → ∀ y : Tot ℬ (BCGen f M₁.Q),
      χ' (b • y) = (n * p).negOnePow • b • χ' y := fun hb y => hχ'.2 hb y
  have t₁ : ∀ (b : B) (e' : ⨁ p, BCGen f M₁.Q p), χ (Tot.tmul ℬ _ b e') =
      GCDga.twist ℬ n b • χ (Tot.tmul ℬ _ 1 e') := fun b e' => hom_tmul hχ b e'
  have t₂ : ∀ (b : B) (e' : ⨁ p, BCGen f M₁.Q p), χ' (Tot.tmul ℬ _ b e') =
      GCDga.twist ℬ n b • χ' (Tot.tmul ℬ _ 1 e') := fun b e' => hom_tmul hχ' b e'
  have hgen : ∀ e' : ⨁ p, BCGen f M₁.Q p,
      χ (Tot.tmul ℬ _ 1 e') = χ' (Tot.tmul ℬ _ 1 e') := by
    intro e'
    induction e' using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero, map_zero]
    | of p x =>
      induction x using BCGen.induction_on with
      | ht β q =>
        have hx : DirectSum.of (BCGen f M₁.Q) p (BCGen.tmul f M₁.Q β q) =
            (β : ℬ 0) • bcι f M₁.Q (lof (𝒜 0) ℤ M₁.Q p q) := by
          rw [bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul]; rfl
        rw [hx, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (β : B), s₁ β.2, s₂ β.2,
          mul_zero, Int.negOnePow_zero, one_smul, one_smul, ← bcF_tmul_one, h]
      | hadd x y hx hy =>
        rw [(DirectSum.of (BCGen f M₁.Q) p).map_add, Tot.tmul_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [Tot.tmul_add, map_add, map_add, hx, hy]
  ext x
  induction x using Tot.induction_on with
  | ht b e' => rw [t₁, t₂, hgen]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- **A9** Maps of degree `n` between base changes are determined on the image of `F`. -/
theorem hom_eq_of_bcF {χ χ' : Tot ℬ (BCGen f M₁.Q) →ₗ[k] Tot ℬ (BCGen f M₂.Q)}
    (hχ : χ ∈ Hom (M₁.baseChange f) (M₂.baseChange f) n)
    (hχ' : χ' ∈ Hom (M₁.baseChange f) (M₂.baseChange f) n)
    (h : ∀ x, χ (bcF f M₁.Q x) = χ' (bcF f M₁.Q x)) : χ = χ' :=
  hom_eq_of_bcF' f n hχ hχ' h

/-- A9: the operator of the base change is the extension of `θ'`. -/
theorem baseChange_X_apply (M : QuasiCohesive 𝒜) (x : Tot ℬ (BCGen f M.Q)) :
    (M.baseChange f).X x = (bcGenData f M).extend x := rfl

/-- **A9** Base change commutes with `δ`: `f^*(δφ) = δ(f^*φ)`. -/
theorem bcHomL_δ (φ : Hom M₁ M₂ n) {m : ℤ} (h : n + 1 = m) :
    bcHomL f m ⟨δ M₁ M₂ n φ.1, h ▸ δ_mem M₁ M₂ φ.2⟩ =
      δ (M₁.baseChange f) (M₂.baseChange f) n (bcHomL f n φ) := by
  subst h
  apply hom_eq_of_bcF f (n + 1) (bcHomL_mem f _ _) (δ_mem _ _ (bcHomL_mem f n φ))
  intro x
  rw [bcHomL_bcF]
  show bcF f M₂.Q (M₂.X (φ.1 x) - n.negOnePow • φ.1 (M₁.X x)) =
    (bcGenData f M₂).extend (bcHomL f n φ (bcF f M₁.Q x)) -
      n.negOnePow • bcHomL f n φ ((bcGenData f M₁).extend (bcF f M₁.Q x))
  rw [bcHomL_bcF, bc_extend_bcF, bc_extend_bcF, bcHomL_bcF, map_sub, Units.smul_def,
    Units.smul_def, map_zsmul]

/-- **A9** Base change commutes with composition. -/
theorem bcHomL_comp {M₃ : QuasiCohesive 𝒜} (m : ℤ) (ψ : Hom M₂ M₃ m) (φ : Hom M₁ M₂ n) :
    bcHomL f (m + n) ⟨ψ.1 ∘ₗ φ.1, comp_mem M₁ M₂ M₃ ψ.2 φ.2⟩ =
      bcHomL f m ψ ∘ₗ bcHomL f n φ := by
  apply hom_eq_of_bcF f (m + n) (bcHomL_mem f _ _)
    (comp_mem (M₁.baseChange f) (M₂.baseChange f) (M₃.baseChange f)
      (bcHomL_mem f m ψ) (bcHomL_mem f n φ))
  intro x
  rw [bcHomL_bcF]
  show bcF f M₃.Q (ψ.1 (φ.1 x)) = bcHomL f m ψ (bcHomL f n φ (bcF f M₁.Q x))
  rw [bcHomL_bcF, bcHomL_bcF]

/-- **A9** Base change preserves identities. -/
theorem bcHomL_id (M : QuasiCohesive 𝒜) :
    bcHomL f 0 ⟨LinearMap.id, id_mem M⟩ = LinearMap.id := by
  apply hom_eq_of_bcF f 0 (bcHomL_mem f _ _) (id_mem (M.baseChange f))
  intro x
  rw [bcHomL_bcF]
  rfl

/-- **A9** Base change is additive in `φ`. -/
theorem bcHomL_add (φ ψ : Hom M₁ M₂ n) :
    bcHomL f n (φ + ψ) = bcHomL f n φ + bcHomL f n ψ := by
  apply hom_eq_of_bcF f n (bcHomL_mem f _ _)
    (add_mem (bcHomL_mem f n φ) (bcHomL_mem f n ψ))
  intro x
  rw [bcHomL_bcF]
  show bcF f M₂.Q (φ.1 x + ψ.1 x) = bcHomL f n φ (bcF f M₁.Q x) + bcHomL f n ψ (bcF f M₁.Q x)
  rw [bcHomL_bcF, bcHomL_bcF, (bcF f M₂.Q).map_add]

/-- **A9** Base change is `k`-linear in `φ`. -/
theorem bcHomL_smul (r : k) (φ : Hom M₁ M₂ n) :
    bcHomL f n (r • φ) = r • bcHomL f n φ := by
  apply hom_eq_of_bcF f n (bcHomL_mem f _ _) (Submodule.smul_mem _ r (bcHomL_mem f n φ))
  intro x
  rw [bcHomL_bcF]
  show bcF f M₂.Q (r • φ.1 x) = r • bcHomL f n φ (bcF f M₁.Q x)
  rw [bcHomL_bcF, bcF_smul_k]

/-- A9: base change of the zero map. -/
theorem bcHomL_zero : bcHomL f n (0 : Hom M₁ M₂ n) = 0 := by
  have := bcHomL_smul f n (0 : k) (0 : Hom M₁ M₂ n)
  rwa [zero_smul, zero_smul] at this

end Functoriality

/-! ## A9: the functor `Ho(P_A) ⥤ Ho(P_B)` -/

section HoFunctor

open CategoryTheory

variable {M₁ M₂ : QuasiCohesive 𝒜}

/-- A9: the image of a closed degree-0 map is closed. -/
theorem bcHomL_mem_Z0 (φ : Z0 M₁ M₂) :
    bcHomL f 0 ⟨φ.1, (Submodule.mem_inf.1 φ.2).1⟩ ∈ Z0 (M₁.baseChange f) (M₂.baseChange f) := by
  have h1 := bcHomL_δ f 0 ⟨φ.1, (Submodule.mem_inf.1 φ.2).1⟩ (zero_add 1)
  have h0 : (⟨δ M₁ M₂ 0 φ.1, (zero_add (1 : ℤ)) ▸
      δ_mem M₁ M₂ (Submodule.mem_inf.1 φ.2).1⟩ : Hom M₁ M₂ 1) = 0 :=
    Subtype.ext (LinearMap.mem_ker.1 (Submodule.mem_inf.1 φ.2).2)
  rw [h0, bcHomL_zero] at h1
  exact ⟨bcHomL_mem f 0 _, h1.symm⟩

/-- **A9** Base change on closed degree-0 maps. -/
def bcZ0 : Z0 M₁ M₂ →ₗ[k] Z0 (M₁.baseChange f) (M₂.baseChange f) where
  toFun φ := ⟨_, bcHomL_mem_Z0 f φ⟩
  map_add' φ ψ := Subtype.ext (bcHomL_add f 0 ⟨φ.1, _⟩ ⟨ψ.1, _⟩)
  map_smul' r φ := Subtype.ext (bcHomL_smul f 0 r ⟨φ.1, _⟩)

/-- A9: base change maps boundaries to boundaries. -/
theorem bcZ0_B0 : (B0 M₁ M₂).comap (Z0 M₁ M₂).subtype ≤
    ((B0 (M₁.baseChange f) (M₂.baseChange f)).comap
      (Z0 (M₁.baseChange f) (M₂.baseChange f)).subtype).comap (bcZ0 f) := by
  rintro φ ⟨χ, hχ, hφ⟩
  refine ⟨bcHomL f (-1) ⟨χ, hχ⟩, bcHomL_mem f (-1) _, ?_⟩
  rw [← bcHomL_δ f (-1) ⟨χ, hχ⟩ (show (-1 : ℤ) + 1 = 0 by norm_num)]
  change _ = bcHomL f 0 ⟨φ.1, _⟩
  congr 1
  exact Subtype.ext hφ

/-- **A9** Base change on `H⁰`. -/
def bcH0 : H0 M₁ M₂ →ₗ[k] H0 (M₁.baseChange f) (M₂.baseChange f) :=
  Submodule.mapQ _ _ (bcZ0 f) (bcZ0_B0 f)

/-- **A9** Base change along a map of (possibly curved) dgas `f : A → B` as a functor
 `Ho(P_A) ⥤ Ho(P_B)`; in
particular it preserves homotopy equivalences (isomorphisms in `Ho`). [B, §2.7]. -/
def bcHoFunctor : HoP 𝒜 ⥤ HoP ℬ where
  obj M := ⟨M.as.baseChange f⟩
  map {M N} φ := bcH0 f (M₁ := M.as.toQuasiCohesive) (M₂ := N.as.toQuasiCohesive) φ
  map_id M := by
    change Submodule.Quotient.mk (bcZ0 f (idZ0 _)) = Submodule.Quotient.mk (idZ0 _)
    congr 1
    exact Subtype.ext (bcHomL_id f M.as.toQuasiCohesive)
  map_comp {M N P} φ ψ := by
    induction φ using Submodule.Quotient.induction_on
    induction ψ using Submodule.Quotient.induction_on
    rename_i φ ψ
    change Submodule.Quotient.mk (bcZ0 f (compZ0 _ _ _ ψ φ)) =
      Submodule.Quotient.mk (compZ0 _ _ _ (bcZ0 f ψ) (bcZ0 f φ))
    congr 1
    exact Subtype.ext (bcHomL_comp f 0 0 ⟨ψ.1, _⟩ ⟨φ.1, _⟩)

end HoFunctor

/-! ## Degree-0 maps from maps of generators -/

section GenFamily

section Fam

variable {Q₁ Q₂ Q₃ : ℤ → Type} [∀ p, AddCommGroup (Q₁ p)] [∀ p, Module (𝒜 0) (Q₁ p)]
  [∀ p, AddCommGroup (Q₂ p)] [∀ p, Module (𝒜 0) (Q₂ p)]
  [∀ p, AddCommGroup (Q₃ p)] [∀ p, Module (𝒜 0) (Q₃ p)]

/-- The map `⨁ Q₁ → ⨁ Q₂` induced by a family `u_p : Q₁^p → Q₂^p`. -/
def famMap (u : ∀ p, Q₁ p →+ Q₂ p) : (⨁ p, Q₁ p) →+ (⨁ p, Q₂ p) :=
  DirectSum.toAddMonoid fun p => (DirectSum.of Q₂ p).comp (u p)

/-- `famMap u` on a homogeneous generator. -/
theorem famMap_of (u : ∀ p, Q₁ p →+ Q₂ p) (p : ℤ) (x : Q₁ p) :
    famMap u (DirectSum.of Q₁ p x) = DirectSum.of Q₂ p (u p x) :=
  DirectSum.toAddMonoid_of _ p x

/-- `famMap` of `A⁰`-linear maps is `A⁰`-linear. -/
theorem famMap_smul (u : ∀ p, Q₁ p →+ Q₂ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x)
    (r : 𝒜 0) (e : ⨁ p, Q₁ p) : famMap u (r • e) = r • famMap u e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    rw [show r • DirectSum.of Q₁ p x = DirectSum.of Q₁ p (r • x) from
        (map_smul (DirectSum.lof (𝒜 0) ℤ Q₁ p) r x).symm, famMap_of, famMap_of, hu]
    exact map_smul (DirectSum.lof (𝒜 0) ℤ Q₂ p) r _
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `famMap v ∘ famMap u = famMap w` if `v_p ∘ u_p = w_p` for all `p`. -/
theorem famMap_famMap (u : ∀ p, Q₁ p →+ Q₂ p) (v : ∀ p, Q₂ p →+ Q₃ p) (w : ∀ p, Q₁ p →+ Q₃ p)
    (h : ∀ p x, v p (u p x) = w p x) (e : ⨁ p, Q₁ p) :
    famMap v (famMap u e) = famMap w e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x => rw [famMap_of, famMap_of, famMap_of, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- `famMap` of the identity family is the identity. -/
theorem famMap_id (u : ∀ p, Q₁ p →+ Q₁ p) (h : ∀ p x, u p x = x) (e : ⨁ p, Q₁ p) :
    famMap u e = e := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x => rw [famMap_of, h]
  | add x y hx hy => rw [map_add, hx, hy]

/-- The bi-additive map `(a, e) ↦ a ⊗ famMap u e`. -/
def famTotAux (u : ∀ p, Q₁ p →+ Q₂ p) : A →+ (⨁ p, Q₁ p) →+ Tot 𝒜 Q₂ :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk' (fun e => Tot.tmul 𝒜 Q₂ a (famMap u e))
      (fun e e' => by rw [map_add, Tot.tmul_add]))
    (fun a b => AddMonoidHom.ext fun e => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Tot.add_tmul])

/-- The additive map `a ⊗ e ↦ a ⊗ famMap u e`. -/
def famTotAdd (u : ∀ p, Q₁ p →+ Q₂ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x) :
    Tot 𝒜 Q₁ →+ Tot 𝒜 Q₂ :=
  TensorProduct.liftAddHom (R := 𝒜 0) (famTotAux u) fun r a e => by
    show Tot.tmul 𝒜 Q₂ (r • a) (famMap u e) = Tot.tmul 𝒜 Q₂ a (famMap u (r • e))
    rw [famMap_smul u hu, Tot.tmul_smul0, GCDga.smul0_def, GCDga.central 𝒜 r.2]

/-- `famTotAdd u` on pure tensors. -/
theorem famTotAdd_tmul (u : ∀ p, Q₁ p →+ Q₂ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x)
    (a : A) (e : ⨁ p, Q₁ p) :
    famTotAdd u hu (Tot.tmul 𝒜 Q₁ a e) = Tot.tmul 𝒜 Q₂ a (famMap u e) := rfl

/-- `famTotAdd u` is `A`-linear. -/
theorem famTotAdd_smul (u : ∀ p, Q₁ p →+ Q₂ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x)
    (a : A) (x : Tot 𝒜 Q₁) : famTotAdd u hu (a • x) = a • famTotAdd u hu x := by
  induction x using Tot.induction_on with
  | ht b e => rw [Tot.smul_tmul, famTotAdd_tmul, famTotAdd_tmul, Tot.smul_tmul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **A9.a** The `A`-linear map `a ⊗ e ↦ a ⊗ famMap u e` of total modules induced by a family of
`A⁰`-linear maps of generators `u_p : Q₁^p → Q₂^p`. -/
def famTot (u : ∀ p, Q₁ p →+ Q₂ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x) :
    Tot 𝒜 Q₁ →ₗ[k] Tot 𝒜 Q₂ where
  toFun := famTotAdd u hu
  map_add' := (famTotAdd u hu).map_add
  map_smul' r x := by
    rw [RingHom.id_apply, ← algebraMap_smul A r x, famTotAdd_smul, algebraMap_smul]

/-- `famTot u` on pure tensors. -/
theorem famTot_tmul (u : ∀ p, Q₁ p →+ Q₂ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x)
    (a : A) (e : ⨁ p, Q₁ p) :
    famTot (k := k) u hu (Tot.tmul 𝒜 Q₁ a e) = Tot.tmul 𝒜 Q₂ a (famMap u e) := rfl

/-- `famTot u` is `A`-linear. -/
theorem famTot_smul (u : ∀ p, Q₁ p →+ Q₂ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x)
    (a : A) (x : Tot 𝒜 Q₁) : famTot (k := k) u hu (a • x) = a • famTot (k := k) u hu x :=
  famTotAdd_smul u hu a x

/-- `famTot u` preserves the total degree. -/
theorem famTot_mem_totDeg (u : ∀ p, Q₁ p →+ Q₂ p)
    (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x) {m : ℤ} {x : Tot 𝒜 Q₁}
    (hx : x ∈ totDeg 𝒜 Q₁ m) : famTot (k := k) u hu x ∈ totDeg 𝒜 Q₂ m := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change famTot u hu (Tot.tmul 𝒜 Q₁ a (DirectSum.of Q₁ p e)) ∈ _
    rw [famTot_tmul, famMap_of]
    exact tmul_mem_totDeg ha _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- `famTot v ∘ famTot u = famTot w` if `v_p ∘ u_p = w_p`. -/
theorem famTot_famTot (u : ∀ p, Q₁ p →+ Q₂ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x)
    (v : ∀ p, Q₂ p →+ Q₃ p) (hv : ∀ p (r : 𝒜 0) x, v p (r • x) = r • v p x)
    (w : ∀ p, Q₁ p →+ Q₃ p) (hw : ∀ p (r : 𝒜 0) x, w p (r • x) = r • w p x)
    (h : ∀ p x, v p (u p x) = w p x) (x : Tot 𝒜 Q₁) :
    famTot (k := k) v hv (famTot (k := k) u hu x) = famTot (k := k) w hw x := by
  induction x using Tot.induction_on with
  | ht a e => rw [famTot_tmul, famTot_tmul, famTot_tmul, famMap_famMap u v w h]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- `famTot` of the identity family is the identity. -/
theorem famTot_id (u : ∀ p, Q₁ p →+ Q₁ p) (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x)
    (h : ∀ p x, u p x = x) (x : Tot 𝒜 Q₁) : famTot (k := k) u hu x = x := by
  induction x using Tot.induction_on with
  | ht a e => rw [famTot_tmul, famMap_id u h]
  | hadd x y hx hy => rw [map_add, hx, hy]

end Fam

/-- **A9.a** `famTot u ∈ Hom^0(M₁, M₂)`, for quasi-cohesive modules with generators `Q₁`, `Q₂`
(stated for `M₁.Q`, `M₂.Q`). -/
theorem famTot_mem {M₁ M₂ : QuasiCohesive 𝒜} (u : ∀ p, M₁.Q p →+ M₂.Q p)
    (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = r • u p x) : famTot u hu ∈ Hom M₁ M₂ 0 := by
  refine ⟨fun hx => ?_, fun {p b} _ x => ?_⟩
  · rw [add_zero]
    exact famTot_mem_totDeg u hu hx
  · rw [zero_mul, Int.negOnePow_zero, one_smul]
    exact famTot_smul u hu b x

end GenFamily

end Cohesive
end
