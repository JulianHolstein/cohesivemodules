import Cohesivemodules.Algebra.LiftingConeGens

set_option linter.style.header false

/-!
# A11.a: the cone condition from flatness and a quasi-isomorphism (part 2 of 2)

Split from `Algebra/LiftingCone.lean` for size;
continues `Algebra/LiftingConeGens.lean`.
-/

noncomputable section
open CategoryTheory
namespace Cohesive
open TensorProduct DirectSum MonoidalCategory CochainComplex HomComplex
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

section Tco

/-- Sign bookkeeping: `u • u • y = y` for `u : ℤˣ`. -/
theorem units_smul_smul_self {M : Type*} [AddCommGroup M] (u : ℤˣ) (y : M) : u • u • y = y := by
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- Sign bookkeeping for `Tco_δ`. -/
theorem sign_aux {M : Type*} [AddCommGroup M] (s₁ u s w : ℤ) (D E : M) (e1 : s₁ * u = s) :
    s₁ • u • D - (-(w * s)) • E = s • D + (w * s) • E := by
  rw [smul_smul, e1, neg_smul, sub_neg_eq_add]

variable {Pc Xc Yc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ}

/-- A11.a: a map `φ ∈ HomT^n` on the generators of degree `p`, `x ↦ φ(1 ⊗ x)`. -/
def φgen {n : ℤ} (φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc))
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) (p : ℤ) : Pc.X p →ₗ[𝒜 0] Tot 𝒜 (Gens Xc) where
  toFun x := φ (Tot.tmul 𝒜 (Gens Pc) 1 (lof (𝒜 0) ℤ (Gens Pc) p x))
  map_add' x y := by rw [map_add, Tot.tmul_add, map_add]
  map_smul' r x := by
    rw [map_smul, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul, hφ.2 r.2, mul_zero,
      Int.negOnePow_zero, one_smul, RingHom.id_apply, Tot.smul0_eq]

/-- **A11.a** The cochain of degree `n - b` of a map `φ ∈ HomT^n`: on `P^p`,
`x ↦ (-1)^{bn} π_b(φ(1 ⊗ x))_q ∈ A^b ⊗ X^q`. For pure `φ` of form degree `b` this loses
nothing (`Tco_inj`). -/
def Tco (b n : ℤ) (φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc))
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) : Cochain Pc (tensC Xc b) (n - b) :=
  (b * n).negOnePow • Cochain.mk fun p q _ => ModuleCat.ofHom (extr Xc b q ∘ₗ φgen φ hφ p)

/-- A11.a: formula for `Tco`. -/
theorem Tco_apply (b n : ℤ) (φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc))
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) (p q : ℤ) (h : p + (n - b) = q) (x : Pc.X p) :
    ((Tco b n φ hφ).v p q h).hom x = (b * n).negOnePow •
      extr Xc b q (φ (Tot.tmul 𝒜 (Gens Pc) 1 (lof (𝒜 0) ℤ (Gens Pc) p x))) := by
  rw [Tco, Cochain.units_smul_v, Cochain.mk_v]
  rfl

/-- **A11.a** `Tco` intertwines `δ⁰` with Mathlib's differential. -/
theorem Tco_δ (b n m : ℤ) (hm : n + 1 = m) {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n)
    (h : δT (hatGen 1 (dGen Pc)) (hatGen 1 (dGen Xc)) n φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) m) :
    Tco b m _ h = HomComplex.δ (n - b) (m - b) (Tco b n φ hφ) := by
  subst hm
  refine Cochain.ext _ _ fun p q hpq => ?_
  obtain ⟨q₁, rfl⟩ : ∃ q₁, q = q₁ + 1 := ⟨q - 1, by ring⟩
  rw [HomComplex.δ_v (n - b) (n + 1 - b) (by ring) _ p (q₁ + 1) hpq q₁ (p + 1) (by ring) rfl]
  ext x
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rw [Tco_apply, Tco_apply, Tco_apply]
  simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_sub,
    hatGen_tmul_one, dGen_lof, extr_hatGen_d]
  -- signs: `(-1)^{b(n+1)} (-1)^b = (-1)^{bn}`, `(-1)^{b(n+1)} (-1)^n = -(-1)^{n+1-b} (-1)^{bn}`
  have hu : ((b.negOnePow : ℤˣ) : ℤ) * (b.negOnePow : ℤ) = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  have e1 : (((b * (n + 1)).negOnePow : ℤˣ) : ℤ) * (b.negOnePow : ℤ) = (b * n).negOnePow := by
    rw [mul_add, mul_one, Int.negOnePow_add, Units.val_mul, mul_assoc, hu, mul_one]
  have e2 : (((b * (n + 1)).negOnePow : ℤˣ) : ℤ) * (n.negOnePow : ℤ) =
      -(((n + 1 - b).negOnePow : ℤ) * ((b * n).negOnePow : ℤ)) := by
    rw [mul_add, mul_one, Int.negOnePow_add, Units.val_mul, sub_eq_add_neg, Int.negOnePow_add,
      Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one, Units.val_mul, Units.val_mul,
      Units.val_neg, Units.val_one]
    ring
  simp only [Units.smul_def, map_zsmul, smul_sub, smul_smul, e2]
  exact sign_aux _ _ _ _ _ _ e1

/-- A11.a: `Tco` of the zero map. -/
theorem Tco_zero (b n : ℤ) (h : (0 : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)) ∈
    HomT 𝒜 (Gens Pc) (Gens Xc) n) : Tco b n 0 h = 0 := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  ext x
  rw [Tco_apply, Cochain.zero_v, LinearMap.zero_apply, map_zero, smul_zero]
  rfl

/-- **A11.a** `Tco` intertwines composition with `ê₀` and with `1 ⊗ f`. -/
theorem Tco_comp (b n : ℤ) (f : Xc ⟶ Yc) {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n)
    (h : hatGen 0 (genMap f) ∘ₗ φ ∈ HomT 𝒜 (Gens Pc) (Gens Yc) n) :
    Tco b n _ h = (Tco b n φ hφ).comp (Cochain.ofHom (tensMap b f)) (add_zero _) := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  ext x
  simp only [Tco_apply, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ModuleCat.hom_comp,
    LinearMap.comp_apply, extr_hatGen_map, Units.smul_def, map_zsmul]

/-- A11.a: `Tco` is additive. -/
theorem Tco_add (b n : ℤ) {φ ψ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) (hψ : ψ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) :
    Tco b n (φ + ψ) (add_mem hφ hψ) = Tco b n φ hφ + Tco b n ψ hψ := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  ext x
  simp only [Tco_apply, Cochain.add_v, ModuleCat.hom_add, LinearMap.add_apply, map_add,
    smul_add]

/-- A11.a: `Tco` commutes with negation. -/
theorem Tco_neg (b n : ℤ) {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) :
    Tco b n (-φ) (neg_mem hφ) = -Tco b n φ hφ := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  ext x
  simp only [Tco_apply, Cochain.neg_v, ModuleCat.hom_neg, LinearMap.neg_apply, map_neg,
    smul_neg]

/-- A11.a: `Tco` only depends on the map. -/
theorem Tco_congr (b n : ℤ) {φ ψ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) (hψ : ψ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n)
    (h : φ = ψ) : Tco b n φ hφ = Tco b n ψ hψ := by
  subst h; rfl

/-- **A11.a** `Tco` is injective on pure maps of form degree `b`. -/
theorem Tco_inj (b n : ℤ) {φ ψ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) (hψ : ψ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n)
    (pφ : IsPure b φ) (pψ : IsPure b ψ) (h : Tco b n φ hφ = Tco b n ψ hψ) : φ = ψ := by
  -- a pure map is recovered from its cochain: `χ(1 ⊗ x) = pieceTot ((-1)^{bn} (Tco χ) x)`
  have key : ∀ {χ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
      (hχ : χ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n), IsPure b χ → ∀ (p : ℤ) (x : Pc.X p),
      χ (Tot.tmul 𝒜 (Gens Pc) 1 (lof (𝒜 0) ℤ (Gens Pc) p x)) =
        pieceTot Xc b (p + (n - b))
          ((b * n).negOnePow • ((Tco b n χ hχ).v p (p + (n - b)) rfl).hom x) := by
    intro χ hχ pχ p x
    have hdeg : χ (Tot.tmul 𝒜 (Gens Pc) 1 (lof (𝒜 0) ℤ (Gens Pc) p x)) ∈
        totDeg 𝒜 (Gens Xc) (p + n) := by
      have := hχ.1 (tmul_mem_totDeg (Q := Gens Pc) (SetLike.GradedOne.one_mem (A := 𝒜))
        (show Gens Pc p from x))
      rwa [zero_add] at this
    rw [Tco_apply, smul_smul, Int.units_mul_self, one_smul]
    conv_lhs => rw [← pχ]
    rw [← pieceTot_extr (j := p + (n - b)) (by ring) hdeg, pχ]
  refine homT_ext hφ hψ fun e => ?_
  induction e using DirectSum.induction_on with
  | zero => rw [Tot.tmul_zero, map_zero, map_zero]
  | of p x =>
    show φ (Tot.tmul 𝒜 (Gens Pc) 1 (lof (𝒜 0) ℤ (Gens Pc) p x)) =
      ψ (Tot.tmul 𝒜 (Gens Pc) 1 (lof (𝒜 0) ℤ (Gens Pc) p x))
    rw [key hφ pφ, key hψ pψ, h]
  | add x y hx hy => rw [Tot.tmul_add, map_add, map_add, hx, hy]

/-- **A11.a** Every cochain `P → A^b ⊗ X` of degree `n - b` comes from a pure map of form
degree `b`. -/
theorem Tco_surj (b n : ℤ) (z : Cochain Pc (tensC Xc b) (n - b)) :
    ∃ φ, ∃ hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n, IsPure b φ ∧ Tco (k := k) b n φ hφ = z := by
  -- the generator map `x ↦ pieceTot ((-1)^{bn} z(x))`
  obtain ⟨g, hgof⟩ : ∃ g : (⨁ p, Gens Pc p) →+ Tot 𝒜 (Gens Xc), ∀ p (x : Pc.X p),
      g (DirectSum.of (Gens Pc) p x) = pieceTot Xc b (p + (n - b))
        ((b * n).negOnePow • ((z.v p (p + (n - b)) rfl).hom x)) :=
    ⟨DirectSum.toAddMonoid fun p => (pieceTot Xc b (p + (n - b))).toAddMonoidHom.comp
      ((b * n).negOnePow • (z.v p (p + (n - b)) rfl).hom).toAddMonoidHom,
      fun p x => by rw [DirectSum.toAddMonoid_of]; rfl⟩
  have hg : ∀ (f : 𝒜 0) e, g (f • e) = (f : A) • g e := by
    intro f e
    induction e using DirectSum.induction_on with
    | zero => simp
    | of p x =>
      rw [show f • DirectSum.of (Gens Pc) p x = DirectSum.of (Gens Pc) p (f • x) from
          (map_smul (lof (𝒜 0) ℤ (Gens Pc) p) f x).symm, hgof, hgof,
        map_smul (ModuleCat.Hom.hom (z.v p (p + (n - b)) rfl)) f x,
        smul_comm ((b * n).negOnePow) f, map_smul (pieceTot Xc b (p + (n - b))) f,
        Tot.smul0_eq]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
  have hdeg : ∀ p (x : Gens Pc p), g (lof (𝒜 0) ℤ (Gens Pc) p x) ∈ totDeg 𝒜 (Gens Xc) (p + n) := by
    intro p x
    rw [show lof (𝒜 0) ℤ (Gens Pc) p x = DirectSum.of (Gens Pc) p x from rfl, hgof]
    have := pieceTot_mem (Xc := Xc) b (p + (n - b)) ((b * n).negOnePow •
      ((z.v p (p + (n - b)) rfl).hom x))
    rwa [show b + (p + (n - b)) = p + n by ring] at this
  refine ⟨extT n g hg, extT_mem n g hg hdeg, fun e => ?_, ?_⟩
  · rw [extT_tmul_one]
    induction e using DirectSum.induction_on with
    | zero => rw [map_zero, map_zero]
    | of p x => rw [hgof, projF_pieceTot]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · refine Cochain.ext _ _ fun p q hpq => ?_
    ext x
    subst hpq
    rw [Tco_apply, show (extT n g hg) (Tot.tmul 𝒜 (Gens Pc) 1 (lof (𝒜 0) ℤ (Gens Pc) p x)) =
      g (DirectSum.of (Gens Pc) p x) from extT_tmul_one n g hg _, hgof, extr_pieceTot]
    exact units_smul_smul_self _ _

/-- A11.a: sums of pure maps are pure. -/
theorem isPure_add {b : ℤ} {φ ψ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)} (hφ : IsPure b φ)
    (hψ : IsPure b ψ) : IsPure b (φ + ψ) := fun e => by
  rw [LinearMap.add_apply, map_add, hφ e, hψ e]

/-- A11.a: negatives of pure maps are pure. -/
theorem isPure_neg {b : ℤ} {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)} (hφ : IsPure b φ) :
    IsPure b (-φ) := fun e => by
  rw [LinearMap.neg_apply, map_neg, hφ e]

/-- A11.a: differences of pure maps are pure. -/
theorem isPure_sub {b : ℤ} {φ ψ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)} (hφ : IsPure b φ)
    (hψ : IsPure b ψ) : IsPure b (φ - ψ) := by
  rw [sub_eq_add_neg]; exact isPure_add hφ (isPure_neg hψ)

/-- A11.a: `Tco` commutes with differences. -/
theorem Tco_sub (b n : ℤ) {φ ψ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
    (hφ : φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) (hψ : ψ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n) :
    Tco b n (φ - ψ) (sub_mem hφ hψ) = Tco b n φ hφ - Tco b n ψ hψ := by
  rw [Tco_congr b n (sub_mem hφ hψ) (add_mem hφ (neg_mem hψ)) (sub_eq_add_neg φ ψ),
    Tco_add b n hφ (neg_mem hψ), Tco_neg b n hψ, ← sub_eq_add_neg]

/-- A11.a: `ĝ ∘ φ` is pure if `φ` is. -/
theorem isPure_hat_comp {b n : ℤ} {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)}
    (g : (⨁ j, Gens Xc j) →ₗ[𝒜 0] (⨁ j, Gens Yc j)) (hφ : IsPure b φ) :
    IsPure b (hatGen n g ∘ₗ φ) := fun e => by
  rw [LinearMap.comp_apply, projF_hatGen, hφ e]

/-- A11.a: `δ⁰φ` is pure if `φ` is. -/
theorem isPure_δT {b n : ℤ} {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)} (hφ : IsPure b φ) :
    IsPure b (δT (hatGen 1 (dGen Pc)) (hatGen 1 (dGen Xc)) n φ) := fun e => by
  simp only [δT, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    Units.smul_def, map_sub, map_zsmul, projF_hatGen, hφ e, hatGen_tmul_one, hφ (dGen Pc e)]

end Tco

/-! ## The cone condition -/

/-- **A11.a** The cone condition `ConeLift` in form degree `b` for Mathlib complexes: if `A^b` is
flat over `A⁰`, `P` is K-projective (e.g. a bounded-above complex of projectives) and
`f : P → X` is a quasi-isomorphism, then `ConeLift` holds. [A, proof of Prop 3.3.4, case 2]. -/
theorem coneLift_of_quasiIso (b : ℤ) [Module.Flat (𝒜 0) (GCDga.piece 𝒜 b)]
    {Pc Xc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ} [Pc.IsKProjective] (f : Pc ⟶ Xc)
    [QuasiIso f] :
    ConeLift (k := k) (Gens Pc) (Gens Xc) (dGen Pc) (dGen Xc) (genMap f) b := by
  intro K hK pK L hL pL hδK hδL
  have hP : hatGen 1 (dGen Pc) ∈ HomT 𝒜 (Gens Pc) (Gens Pc) 1 :=
    hatGen_mem fun p x => by rw [dGen_lof]; exact concAt_lof _ _
  have hX : hatGen 1 (dGen Xc) ∈ HomT 𝒜 (Gens Xc) (Gens Xc) 1 :=
    hatGen_mem fun p x => by rw [dGen_lof]; exact concAt_lof _ _
  have hf : hatGen 0 (genMap f) ∈ HomT 𝒜 (Gens Pc) (Gens Xc) 0 :=
    hatGen_mem fun p x => by rw [genMap_lof, add_zero]; exact concAt_lof _ _
  have mem2 : ∀ {n m : ℤ}, n + 1 = m → ∀ {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Xc)},
      φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n →
      δT (hatGen 1 (dGen Pc)) (hatGen 1 (dGen Xc)) n φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) m := by
    intro n m hm φ hφ
    subst hm
    exact δT_mem_of_hom hP hX hφ
  have mem1 : ∀ {n m : ℤ}, n + 1 = m → ∀ {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Pc)},
      φ ∈ HomT 𝒜 (Gens Pc) (Gens Pc) n →
      δT (hatGen 1 (dGen Pc)) (hatGen 1 (dGen Pc)) n φ ∈ HomT 𝒜 (Gens Pc) (Gens Pc) m := by
    intro n m hm φ hφ
    subst hm
    exact δT_mem_of_hom hP hP hφ
  have memc : ∀ {n : ℤ} {φ : Tot 𝒜 (Gens Pc) →ₗ[k] Tot 𝒜 (Gens Pc)},
      φ ∈ HomT 𝒜 (Gens Pc) (Gens Pc) n →
      hatGen 0 (genMap f) ∘ₗ φ ∈ HomT 𝒜 (Gens Pc) (Gens Xc) n := by
    intro n φ hφ
    have := comp_mem_homT hf hφ
    rwa [zero_add] at this
  -- the cycle conditions as cochains
  have hα : HomComplex.δ (2 - b) (3 - b) (Tco b 2 K hK) = 0 := by
    rw [← Tco_δ b 2 3 (by norm_num) hK (mem1 (by norm_num) hK),
      Tco_congr b 3 _ (zero_mem _) hδK, Tco_zero]
  have hβ : HomComplex.δ (1 - b) (2 - b) (Tco b 1 L hL) +
      (Tco b 2 K hK).comp (Cochain.ofHom (tensMap b f)) (add_zero _) = 0 := by
    rw [← Tco_δ b 1 2 (by norm_num) hL (mem2 (by norm_num) hL), ← Tco_comp b 2 f hK (memc hK),
      ← Tco_add, Tco_congr b 2 _ (zero_mem _) hδL, Tco_zero]
  obtain ⟨x, y, hx, hy⟩ := CochainComplex.cone_lift (tensMap b f) (n₀ := 0 - b) (n₁ := 1 - b)
    (n₂ := 2 - b) (n₃ := 3 - b) (by ring) (by ring) (by ring) _ _ hα hβ
  obtain ⟨φ, hφ, pφ, rfl⟩ := Tco_surj (k := k) b 1 x
  obtain ⟨ψ, hψ, pψ, rfl⟩ := Tco_surj (k := k) b 0 y
  refine ⟨φ, hφ, pφ, -ψ, neg_mem hψ, isPure_neg pψ, ?_, ?_⟩
  · refine Tco_inj b 2 (mem1 (by norm_num) hφ) (neg_mem hK) (isPure_δT pφ) (isPure_neg pK) ?_
    rw [Tco_δ b 1 2 (by norm_num) hφ, hx, Tco_neg]
  · have h1 := mem2 (by norm_num : (0 : ℤ) + 1 = 1) (neg_mem hψ)
    refine Tco_inj b 1 (sub_mem h1 (memc hφ)) (neg_mem hL)
      (isPure_sub (isPure_δT (isPure_neg pψ)) (isPure_hat_comp _ pφ)) (isPure_neg pL) ?_
    rw [Tco_sub b 1 h1 (memc hφ), Tco_δ b 0 1 (by norm_num) (neg_mem hψ) h1, Tco_neg b 0 hψ,
      Tco_comp b 1 f hφ (memc hφ), Tco_neg b 1 hL, HomComplex.δ_neg, ← hy]
    abel


/-! ## A11: the lifting theorem in blueprint form -/

section Final

omit [GCDga 𝒜] in
/-- A11: an element concentrated in degree `m` is its component in degree `m`. -/
theorem eq_lof_of_concAt {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    {m : ℤ} {e : ⨁ p, Q p} (h : Tot.ConcAt m e) : e = lof (𝒜 0) ℤ Q m (e m) := by
  ext i
  by_cases hi : i = m
  · subst hi
    rw [lof_apply]
  · rw [h i hi, show (lof (𝒜 0) ℤ Q m (e m)) i = 0 from DFinsupp.single_eq_of_ne hi]

namespace QuasiCohesive

variable (N : QuasiCohesive 𝒜)

/-- A11: the component `𝕏⁰ : Q^p → Q^{p+1}`. -/
def X0comp (p : ℤ) : N.Q p →ₗ[𝒜 0] N.Q (p + 1) :=
  DirectSum.component (𝒜 0) ℤ N.Q (p + 1) ∘ₗ N.X0 ∘ₗ lof (𝒜 0) ℤ N.Q p

/-- A11: `𝕏⁰(e in degree p) = 𝕏⁰ e in degree p + 1`. -/
theorem X0_lof (p : ℤ) (e : N.Q p) :
    N.X0 (lof (𝒜 0) ℤ N.Q p e) = lof (𝒜 0) ℤ N.Q (p + 1) (N.X0comp p e) :=
  eq_lof_of_concAt (N.X0_concAt e)

/-- **A11** The complex `(Q, 𝕏⁰)` of `A⁰`-modules underlying a quasi-cohesive module, as a
Mathlib cochain complex (A3.b in degree `0`: `𝕏⁰ ∘ 𝕏⁰ = 0`). -/
def complex0 : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ :=
  CochainComplex.of (fun p => ModuleCat.of (𝒜 0) (N.Q p))
    (fun p => ModuleCat.ofHom (N.X0comp p)) fun p => by
      ext e
      show N.X0comp (p + 1) (N.X0comp p e) = 0
      have h := N.X0_X0 (lof (𝒜 0) ℤ N.Q p e)
      rw [N.X0_lof, N.X0_lof] at h
      have := congrArg (fun y => y (p + 1 + 1)) h
      simpa only [lof_apply, DirectSum.zero_apply] using this

/-- A11: the differential of `complex0`. -/
theorem complex0_d (p : ℤ) (e : N.Q p) : (N.complex0.d p (p + 1)).hom e = N.X0comp p e := by
  simp only [complex0, CochainComplex.of_d, ModuleCat.hom_ofHom]
  rfl

/-- A11: `𝕏⁰`, typed on the generators of `complex0`. -/
def X0' : (⨁ p, Gens N.complex0 p) →ₗ[𝒜 0] (⨁ p, Gens N.complex0 p) := N.X0

/-- A11: `∂` of `complex0` on the direct sum is `𝕏⁰`. -/
theorem dGen_complex0 : dGen N.complex0 = N.X0' := by
  refine DirectSum.linearMap_ext _ fun p => LinearMap.ext fun e => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, dGen_lof]
  have h1 : (N.complex0.d p (p + 1)).hom e = N.X0comp p e := N.complex0_d p e
  rw [h1]
  exact (N.X0_lof p e).symm

end QuasiCohesive

variable {Pc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ}

/-- A11: `∂ ∘ ∂ = 0` on the direct sum of the terms of a complex. -/
theorem dGen_dGen (x : ⨁ p, Gens Pc p) : dGen Pc (dGen Pc x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    have h : (Pc.d (p + 1) (p + 1 + 1)).hom ((Pc.d p (p + 1)).hom x) = 0 := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
      rfl
    rw [show DirectSum.of (Gens Pc) p x = lof (𝒜 0) ℤ (Gens Pc) p x from rfl, dGen_lof,
      dGen_lof, h, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-- A11: a chain map `e₀ : P → (Q, 𝕏⁰)` on the direct sums, typed with the generators of `N`. -/
def e0N {N : QuasiCohesive 𝒜} (e₀ : Pc ⟶ N.complex0) : (⨁ p, Gens Pc p) →ₗ[𝒜 0] (⨁ p, N.Q p) :=
  genMap e₀

/-- A11: `e₀(x in degree p) = e₀ x in degree p`. -/
theorem e0N_lof {N : QuasiCohesive 𝒜} (e₀ : Pc ⟶ N.complex0) (p : ℤ) (x : Pc.X p) :
    e0N e₀ (lof (𝒜 0) ℤ (Gens Pc) p x) = lof (𝒜 0) ℤ N.Q p ((e₀.f p).hom x) :=
  genMap_lof e₀ p x

/-- A11: `e₀` is a chain map: `𝕏⁰ ∘ e₀ = e₀ ∘ ∂`. -/
theorem X0_e0N {N : QuasiCohesive 𝒜} (e₀ : Pc ⟶ N.complex0) (x : ⨁ p, Gens Pc p) :
    N.X0 (e0N e₀ x) = e0N e₀ (dGen Pc x) := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | of p x =>
    have hc : N.X0comp p ((e₀.f p).hom x) = (e₀.f (p + 1)).hom ((Pc.d p (p + 1)).hom x) := by
      have := congrArg (fun g => g.hom x) (e₀.comm p (p + 1))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [← this]
      exact (N.complex0_d p _).symm
    have h1 : N.X0 (e0N e₀ (lof (𝒜 0) ℤ (Gens Pc) p x)) =
        lof (𝒜 0) ℤ N.Q (p + 1) (N.X0comp p ((e₀.f p).hom x)) := by
      rw [e0N_lof]
      exact N.X0_lof p _
    have h2 : e0N e₀ (dGen Pc (lof (𝒜 0) ℤ (Gens Pc) p x)) =
        lof (𝒜 0) ℤ N.Q (p + 1) ((e₀.f (p + 1)).hom ((Pc.d p (p + 1)).hom x)) := by
      rw [dGen_lof, e0N_lof]
    rw [show DirectSum.of (Gens Pc) p x = lof (𝒜 0) ℤ (Gens Pc) p x from rfl, h1, h2, hc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (Pc) in
/-- **A11** The cohesive module on `A ⊗ P` defined by generator data `θ` on the terms of a
bounded complex `P` of finitely generated projective `A⁰`-modules (zero outside `[a, b]`). -/
def CohesiveModule.ofGenData (a b : ℤ) [Pc.IsStrictlyGE a] [Pc.IsStrictlyLE b]
    [∀ p, Module.Finite (𝒜 0) (Pc.X p)] [∀ p, Module.Projective (𝒜 0) (Pc.X p)]
    (θ : GenData 𝒜 (Gens Pc))
    (hθ : ∀ p (x : Gens Pc p), θ.θ (lof (𝒜 0) ℤ (Gens Pc) p x) ∈ totDeg 𝒜 (Gens Pc) (p + 1))
    (hflat : ∀ x, θ.extend (θ.θ x) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 (Gens Pc) 1 x) :
    CohesiveModule 𝒜 where
  toQuasiCohesive := QuasiCohesive.ofGenerators (Gens Pc) θ hθ hflat
  bounded := ⟨a, b, fun p hp => by
    rcases hp with hp | hp
    · exact ModuleCat.subsingleton_of_isZero (Pc.isZero_of_isStrictlyGE a p hp)
    · exact ModuleCat.subsingleton_of_isZero (Pc.isZero_of_isStrictlyLE b p hp)⟩
  finite p := inferInstanceAs (Module.Finite (𝒜 0) (Pc.X p))
  projective p := inferInstanceAs (Module.Projective (𝒜 0) (Pc.X p))

/-- **A11 (lifting theorem)** Assume each `A^b` is flat over `A⁰`. Let `N = (Q, 𝕏)` be
quasi-cohesive, `P` a bounded complex of finitely generated projective `A⁰`-modules (with
`P^p = 0` outside `[a, b]`), and `e₀ : (P, ∂) → (Q, 𝕏⁰)` a quasi-isomorphism. Then there are a
cohesive structure `𝔼` on `A ⊗ P` (generator data `θ`, the cohesive module
`CohesiveModule.ofGenData`) with `𝔼⁰ = ∂` (`ε ∘ θ = ∂` on the generators), and a closed
degree-`0` map `e : (A ⊗ P, 𝔼) → N` whose `(0,0)`-component is `e₀` (`ε(e(1 ⊗ x)) = e₀ x`).
[B, Thm 3.2.7(2) and Lemma 3.2.8], [A, Prop 3.3.4, case 2].

Deviations: the cohesive module is given through generator data on the terms of `P` (its
generators are the `P^p`); `𝔼⁰` and "`(0,0)`-component" are expressed with the augmentation `ε`
(form-degree-`0` part); flatness is assumed for every `b` (only `1 ≤ b ≤ N` is used). -/
theorem lifting [∀ b, Module.Flat (𝒜 0) (GCDga.piece 𝒜 b)] (N : QuasiCohesive 𝒜)
    (a b : ℤ) [Pc.IsStrictlyGE a] [Pc.IsStrictlyLE b]
    [∀ p, Module.Finite (𝒜 0) (Pc.X p)] [∀ p, Module.Projective (𝒜 0) (Pc.X p)]
    (e₀ : Pc ⟶ N.complex0) [QuasiIso e₀] :
    ∃ (θ : GenData 𝒜 (Gens Pc))
      (hθ : ∀ p (x : Gens Pc p), θ.θ (lof (𝒜 0) ℤ (Gens Pc) p x) ∈ totDeg 𝒜 (Gens Pc) (p + 1))
      (hflat : ∀ x, θ.extend (θ.θ x) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 (Gens Pc) 1 x),
      (∀ x, Tot.eps 𝒜 (Gens Pc) (θ.θ x) = dGen Pc x) ∧
      ∃ e ∈ Z0 (CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive N,
        ∀ x, Tot.eps 𝒜 N.Q (e (Tot.tmul 𝒜 (Gens Pc) 1 x)) = e0N e₀ x := by
  have : ∀ n, Projective (Pc.X n) := fun n =>
    (Pc.X n).projective_of_categoryTheory_projective
  have : Pc.IsKProjective := CochainComplex.isKProjective_of_projective Pc b
  have hlift : ∀ c : ℤ, 1 ≤ c → c ≤ GCDga.N 𝒜 →
      ConeLift (k := k) (Gens Pc) N.Q (dGen Pc) N.X0 (e0N e₀) c := by
    intro c _ _
    have := coneLift_of_quasiIso (k := k) c e₀
    rw [N.dGen_complex0] at this
    exact this
  exact lift_core (Gens Pc) N (dGen Pc) (e0N e₀)
    (fun p x => by rw [dGen_lof]; exact concAt_lof _ _) dGen_dGen
    (fun p x => by rw [e0N_lof]; exact concAt_lof _ _) (X0_e0N e₀) hlift

end Final

end Cohesive
