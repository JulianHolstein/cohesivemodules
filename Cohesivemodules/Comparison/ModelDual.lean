import Cohesivemodules.Comparison.Setup
import Cohesivemodules.Algebra.TotMap

set_option linter.style.header false

/-!
# C7: dual bases for `𝒜^q` and coordinates on `Tot`

Blueprint item C7 (§4, v1.11; C7.a and C7.d use it). Auxiliary declarations shared by
`ModelDef`, `ModelCrit`, `ModelTensor*` and `FullyFaithfulGlobal` (formerly copied between them):
* `hom0_smul`, `closed0_X`: degree-`0` maps of the Hom complex are `A`-linear, and closed ones
  commute with the operators `𝕏`;
* `Dfm`: uniform dual-basis data `a = ∑_j c_j(a) s_j` for the pieces `𝒜^q`, `q ≤ N0`, and the
  resulting coordinates `iTot : Tot(Q) → ∏_{qj} Q^{n-q}` with retraction `rTot` (on total
  degree `n`), natural for `totMapAlong`;
* `exists_dual`, `exists_dfm`: such data exist on all opens of a compact `X`, compatibly with
  restriction (from `isFinFreeSummand_pieceSheaf`, S4.b); `zero_above`: `𝒜_V^q = 0` for
  `q > N(𝒜_X)`.

Not part of the statement.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

section HomZero

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {M N : QuasiCohesive 𝒜}

/-- A5: a degree-`0` map of the Hom complex is `A`-linear (decompose `a` into homogeneous
parts). -/
theorem hom0_smul {φ : M.T →ₗ[k] N.T} (hφ : φ ∈ Hom M N 0) (a : A) (x : M.T) :
    φ (a • x) = a • φ x := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add y z hy hz => rw [add_smul, map_add, hy, hz, add_smul]
  | @homogeneous p y =>
    rw [hφ.2 y.2, zero_mul, Int.negOnePow_zero, one_smul]

/-- A5: a map with `δφ = 0` (degree `0`) commutes with the operators: `𝕏(φ x) = φ(𝕏 x)`. -/
theorem closed0_X {φ : M.T →ₗ[k] N.T} (hφ : δ M N 0 φ = 0) (x : M.T) :
    N.X (φ x) = φ (M.X x) := by
  have h2 := LinearMap.congr_fun hφ x
  rw [δ_apply] at h2
  simp only [Int.negOnePow_zero, one_smul, LinearMap.sub_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.zero_apply] at h2
  exact sub_eq_zero.1 h2

end HomZero

namespace PreResolvingData

variable (P : PreResolvingData X)

section TotRetract

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable {N0 : ℕ} {m : ℕ → ℕ}

variable (𝒜) in
/-- Uniform dual basis data for the pieces `𝒜^q`, `q ≤ N0`, with `m q` generators of `𝒜^q`:
`a = ∑_j c_j(a) s_j`; `𝒜^q = 0` for `q > N0`. -/
structure Dfm (N0 : ℕ) (m : ℕ → ℕ) where
  /-- The generators of `𝒜^q`. -/
  s : ∀ q : ℕ, Fin (m q) → ↥(GCDga.piece 𝒜 q)
  /-- The coefficient functionals. -/
  c : ∀ q : ℕ, Fin (m q) → ↥(GCDga.piece 𝒜 q) →ₗ[↥(𝒜 0)] ↥(𝒜 0)
  /-- Dual basis property. -/
  expand : ∀ (q : ℕ) (a : ↥(GCDga.piece 𝒜 q)),
    (a : A) = ∑ j, ((c q j a : ↥(𝒜 0)) : A) * (s q j : A)
  /-- Vanishing above `N0`. -/
  zero_of_gt : ∀ q : ℤ, (N0 : ℤ) < q → ∀ a ∈ 𝒜 q, a = 0

variable (N0 m) in
/-- The index type `(q, j)` of the generators of `𝒜^q`, `q ≤ N0`. -/
abbrev DIdx : Type := Σ q : Fin (N0 + 1), Fin (m q)

/-- The degree `q` of the index `(q, j)`. -/
abbrev DIdx.deg (qj : DIdx N0 m) : ℤ := ((qj.1 : ℕ) : ℤ)

/-- The coefficient of `a` along the generator `(q, j)`: `c_{qj}(a_q)`. -/
def Dfm.coef (D : Dfm 𝒜 N0 m) (qj : DIdx N0 m) : A →ₗ[↥(𝒜 0)] ↥(𝒜 0) :=
  (D.c qj.1 qj.2) ∘ₗ (LinearMap.codRestrict (GCDga.piece 𝒜 ((qj.1 : ℕ) : ℤ))
    (GCDga.proj 𝒜 ((qj.1 : ℕ) : ℤ)) (fun a => GCDga.proj_mem 𝒜 _ a))

variable {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- The bi-additive map `(a, e) ↦ (c_{qj}(a_q) · e_{n-q})_{qj}`. -/
def Dfm.iAux (D : Dfm 𝒜 N0 m) (n : ℤ) :
    A →+ (⨁ p, Q p) →+ (∀ qj : DIdx N0 m, Q (n - DIdx.deg qj)) :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun e qj => D.coef qj a • e (n - DIdx.deg qj))
      (fun e e' => by
        funext qj
        simp only [DirectSum.add_apply, smul_add, Pi.add_apply]))
    (fun a b => AddMonoidHom.ext fun e => by
      funext qj
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, add_smul, Pi.add_apply])

/-- `iAux` is `𝒜⁰`-balanced. -/
theorem Dfm.iAux_balanced (D : Dfm 𝒜 N0 m) (n : ℤ) (γ : ↥(𝒜 0)) (a : A)
    (e : ⨁ p, Q p) : D.iAux n (γ • a) e = D.iAux n a (γ • e) := by
  funext qj
  show D.coef qj (γ • a) • e (n - DIdx.deg qj) = D.coef qj a • (γ • e) (n - DIdx.deg qj)
  rw [map_smul, DirectSum.smul_apply, smul_smul, smul_eq_mul, mul_comm]

/-- The coordinates `Tot(Q) → ∏_{qj} Q^{n-q}`. -/
def Dfm.iTot (D : Dfm 𝒜 N0 m) (n : ℤ) :
    Tot 𝒜 Q →+ (∀ qj : DIdx N0 m, Q (n - DIdx.deg qj)) :=
  TensorProduct.liftAddHom (R := 𝒜 0) (D.iAux n) (D.iAux_balanced n)

/-- `iTot` on pure tensors (rfl). -/
theorem Dfm.iTot_tmul (D : Dfm 𝒜 N0 m) (n : ℤ) (a : A) (e : ⨁ p, Q p)
    (qj : DIdx N0 m) :
    D.iTot n (Tot.tmul 𝒜 Q a e) qj = D.coef qj a • e (n - DIdx.deg qj) := rfl

/-- The map `∏ Q^{n-q} → Tot(Q)`, `(z_{qj}) ↦ ∑ s_{qj} ⊗ z_{qj}`. -/
def Dfm.rTot (D : Dfm 𝒜 N0 m) (n : ℤ) :
    (∀ qj : DIdx N0 m, Q (n - DIdx.deg qj)) →+ Tot 𝒜 Q :=
  AddMonoidHom.mk'
    (fun z => ∑ q : Fin (N0 + 1), ∑ j : Fin (m q),
      Tot.tmul 𝒜 Q (D.s q j : A) (lof (𝒜 0) ℤ Q (n - ((q : ℕ) : ℤ)) (z ⟨q, j⟩)))
    (fun z z' => by
      simp only [Pi.add_apply, map_add, Tot.tmul_add, Finset.sum_add_distrib])

/-- `rTot` maps into elements of total degree `n`. -/
theorem Dfm.rTot_mem (D : Dfm 𝒜 N0 m) (n : ℤ)
    (z : ∀ qj : DIdx N0 m, Q (n - DIdx.deg qj)) : D.rTot n z ∈ totDeg 𝒜 Q n := by
  show (∑ q : Fin (N0 + 1), ∑ j : Fin (m q),
    Tot.tmul 𝒜 Q (D.s q j : A)
      (lof (𝒜 0) ℤ Q (n - ((q : ℕ) : ℤ)) (z ⟨q, j⟩))) ∈ totDeg 𝒜 Q n
  refine Submodule.sum_mem _ fun q _ => Submodule.sum_mem _ fun j _ => ?_
  have := tmul_mem_totDeg (𝒜 := 𝒜) (Q := Q) (q := ((q : ℕ) : ℤ)) (a := (D.s q j : A))
    (D.s q j).2 (z ⟨q, j⟩)
  rwa [show ((q : ℕ) : ℤ) + (n - ((q : ℕ) : ℤ)) = n by ring] at this

/-- The coefficient along a generator of another degree vanishes on a homogeneous element. -/
theorem Dfm.coef_of_ne (D : Dfm 𝒜 N0 m) {a : A} {q' : ℤ} (ha : a ∈ 𝒜 q')
    (qj : DIdx N0 m) (h : q' ≠ DIdx.deg qj) : D.coef qj a = 0 := by
  have h1 : GCDga.proj 𝒜 (DIdx.deg qj) a = 0 := by
    rw [GCDga.proj_of_mem 𝒜 ha]
    exact ite_eq_right_iff.2 (fun h' => absurd h' h)
  have h2 : (⟨GCDga.proj 𝒜 (DIdx.deg qj) a, GCDga.proj_mem 𝒜 _ a⟩ :
      ↥(GCDga.piece 𝒜 (DIdx.deg qj))) = 0 := Subtype.ext h1
  exact (congrArg (D.c qj.1 qj.2) h2).trans (map_zero _)

/-- The coefficient along a generator of the same degree. -/
theorem Dfm.coef_of_eq (D : Dfm 𝒜 N0 m) {a : A} (qq : Fin (N0 + 1))
    (ha : a ∈ 𝒜 ((qq : ℕ) : ℤ)) (j : Fin (m qq)) :
    D.coef ⟨qq, j⟩ a = D.c qq j ⟨a, ha⟩ := by
  have h2 : (⟨GCDga.proj 𝒜 ((qq : ℕ) : ℤ) a, GCDga.proj_mem 𝒜 _ a⟩ :
      ↥(GCDga.piece 𝒜 ((qq : ℕ) : ℤ))) = ⟨a, ha⟩ :=
    Subtype.ext (by
      show GCDga.proj 𝒜 ((qq : ℕ) : ℤ) a = a
      rw [GCDga.proj_of_mem 𝒜 ha]
      exact ite_eq_left_iff.2 (fun h' => absurd rfl h'))
  exact congrArg (D.c qq j) h2

/-- `rTot ∘ iTot = id` on a generator `a ⊗ e` of total degree `n`. -/
theorem Dfm.rTot_iTot_gen (D : Dfm 𝒜 N0 m) (n : ℤ) {q' : ℤ} {a : A}
    (ha : a ∈ 𝒜 q') (e : Q (n - q')) :
    D.rTot n (D.iTot n (Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q (n - q') e))) =
      Tot.tmul 𝒜 Q a (lof (𝒜 0) ℤ Q (n - q') e) := by
  by_cases hq : 0 ≤ q' ∧ q' ≤ N0
  · obtain ⟨hq0, hq1⟩ := hq
    obtain ⟨qq, rfl⟩ : ∃ qq : Fin (N0 + 1), ((qq : ℕ) : ℤ) = q' :=
      ⟨⟨q'.toNat, by omega⟩, by simp only; omega⟩
    change (∑ q : Fin (N0 + 1), ∑ j : Fin (m q), Tot.tmul 𝒜 Q (D.s q j : A)
      (lof (𝒜 0) ℤ Q (n - ((q : ℕ) : ℤ)) (D.coef ⟨q, j⟩ a •
        (lof (𝒜 0) ℤ Q (n - ((qq : ℕ) : ℤ)) e) (n - ((q : ℕ) : ℤ))))) = _
    rw [Finset.sum_eq_single qq]
    · have he : (lof (𝒜 0) ℤ Q (n - ((qq : ℕ) : ℤ)) e) (n - ((qq : ℕ) : ℤ)) = e := by
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
      have hj : ∀ j : Fin (m qq), Tot.tmul 𝒜 Q (D.s qq j : A)
          (lof (𝒜 0) ℤ Q (n - ((qq : ℕ) : ℤ)) (D.coef ⟨qq, j⟩ a •
            (lof (𝒜 0) ℤ Q (n - ((qq : ℕ) : ℤ)) e) (n - ((qq : ℕ) : ℤ)))) =
          Tot.tmul 𝒜 Q ((D.s qq j : A) * (D.c qq j ⟨a, ha⟩ : ↥(𝒜 0)))
            (lof (𝒜 0) ℤ Q (n - ((qq : ℕ) : ℤ)) e) := fun j => by
        rw [he, D.coef_of_eq qq ha j, map_smul, Tot.tmul_smul0]
      rw [Finset.sum_congr rfl fun j _ => hj j]
      have hs : (∑ j : Fin (m qq), (D.s qq j : A) * (D.c qq j ⟨a, ha⟩ : ↥(𝒜 0))) = a :=
        (Finset.sum_congr rfl fun j _ => (GCDga.central 𝒜 (D.c qq j ⟨a, ha⟩).2 _).symm).trans
          (D.expand qq ⟨a, ha⟩).symm
      exact (TensorProduct.sum_tmul _ _ _).symm.trans
        (congrArg (fun x => Tot.tmul 𝒜 Q x _) hs)
    · intro q _ hne
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [D.coef_of_ne ha ⟨q, j⟩ (fun h => hne (Fin.ext (by exact_mod_cast h.symm))), zero_smul,
        map_zero, Tot.tmul_zero]
    · intro h
      exact absurd (Finset.mem_univ qq) h
  · have h0 : a = 0 := by
      rcases not_and_or.1 hq with h | h
      · exact GCDga.eq_zero_of_neg 𝒜 (not_le.1 h) ha
      · exact D.zero_of_gt q' (not_le.1 h) a ha
    subst h0
    rw [Tot.zero_tmul, map_zero, map_zero]

/-- `iTot` is `𝒜⁰`-linear. -/
theorem Dfm.iTot_smul0 (D : Dfm 𝒜 N0 m) (n : ℤ) (γ : ↥(𝒜 0)) (x : Tot 𝒜 Q) :
    D.iTot n ((γ : A) • x) = γ • D.iTot n x := by
  induction x using Tot.induction_on with
  | ht a e =>
    funext qj
    rw [Tot.smul_tmul]
    show D.coef qj (γ • a) • e (n - DIdx.deg qj) = γ • (D.coef qj a • e (n - DIdx.deg qj))
    rw [map_smul, smul_smul, smul_eq_mul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `rTot` is `𝒜⁰`-linear. -/
theorem Dfm.rTot_smul0 (D : Dfm 𝒜 N0 m) (n : ℤ) (γ : ↥(𝒜 0))
    (z : ∀ qj : DIdx N0 m, Q (n - DIdx.deg qj)) :
    D.rTot n (γ • z) = (γ : A) • D.rTot n z := by
  show (∑ q : Fin (N0 + 1), ∑ j : Fin (m q),
    Tot.tmul 𝒜 Q (D.s q j : A)
      (lof (𝒜 0) ℤ Q (n - ((q : ℕ) : ℤ)) ((γ • z) ⟨q, j⟩))) =
    (γ : A) • ∑ q : Fin (N0 + 1), ∑ j : Fin (m q),
      Tot.tmul 𝒜 Q (D.s q j : A) (lof (𝒜 0) ℤ Q (n - ((q : ℕ) : ℤ)) (z ⟨q, j⟩))
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Tot.smul_tmul, Pi.smul_apply, map_smul, Tot.tmul_smul0]
  exact congrArg (Tot.tmul 𝒜 Q · _) (GCDga.central 𝒜 γ.2 _).symm

/-- `rTot ∘ iTot = id` on elements of total degree `n`. -/
theorem Dfm.rTot_iTot (D : Dfm 𝒜 N0 m) (n : ℤ) {x : Tot 𝒜 Q}
    (hx : x ∈ totDeg 𝒜 Q n) : D.rTot n (D.iTot n x) = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, hqp, ha, rfl⟩ := hx
    obtain rfl : p = n - q := by omega
    exact D.rTot_iTot_gen n ha e
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r x _ hx =>
    have h1 : algebraMap k A r ∈ 𝒜 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (SetLike.GradedOne.one_mem (A := 𝒜))
    rw [← algebraMap_smul A r x]
    have := D.iTot_smul0 n ⟨algebraMap k A r, h1⟩ x
    change D.iTot n (algebraMap k A r • x) = _ at this
    rw [this, D.rTot_smul0 n ⟨algebraMap k A r, h1⟩, hx]

section Natural

variable {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ]
  [GCDga ℬ]
  {Q' : ℤ → Type} [∀ p, AddCommGroup (Q' p)] [∀ p, Module (ℬ 0) (Q' p)]
  (g : DgaHom 𝒜 ℬ) (u : ∀ p, Q p →+ Q' p)
  (hu : ∀ p (r : 𝒜 0) x, u p (r • x) = g.f0 r • u p x)
  (D : Dfm 𝒜 N0 m) (D' : Dfm ℬ N0 m)
  (hc : ∀ (q : ℕ) j (a : ↥(GCDga.piece 𝒜 q)) (b : ↥(GCDga.piece ℬ q)),
    (b : B) = g a → D'.c q j b = g.f0 (D.c q j a))

/-- `famMap u` acts componentwise. -/
theorem famMap_apply_mdl (e : ⨁ p, Q p) (p : ℤ) : famMap u e p = u p (e p) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply]
  | of q y =>
    rw [famMap_of]
    by_cases h : q = p
    · subst h
      simp only [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h),
        map_zero]
  | add x y hx hy =>
    rw [map_add, DirectSum.add_apply, hx, hy, DirectSum.add_apply, map_add]

include hc in
/-- The coefficients are natural. -/
theorem Dfm.coef_map (qj : DIdx N0 m) (a : A) :
    D'.coef qj (g a) = g.f0 (D.coef qj a) :=
  hc qj.1 qj.2 _ _ (g.map_proj _ a).symm

include hu hc in
/-- `iTot` is natural for `totMapAlong`. -/
theorem Dfm.iTot_map (n : ℤ) (x : Tot 𝒜 Q) (qj : DIdx N0 m) :
    D'.iTot n (totMapAlong g u hu x) qj = u _ (D.iTot n x qj) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [totMapAlong_tmul]
    show D'.coef qj (g a) • famMap u e (n - DIdx.deg qj) =
      u _ (D.coef qj a • e (n - DIdx.deg qj))
    rw [D.coef_map g D' hc, famMap_apply_mdl, hu]
  | hadd x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add (D.iTot n), Pi.add_apply, map_add]

include hu in
/-- `rTot` is natural for `totMapAlong`. -/
theorem Dfm.map_rTot (hs : ∀ q j, g (D.s q j : A) = (D'.s q j : B)) (n : ℤ)
    (z : ∀ qj : DIdx N0 m, Q (n - DIdx.deg qj)) :
    totMapAlong g u hu (D.rTot n z) = D'.rTot n (fun qj => u _ (z qj)) := by
  show totMapAlong g u hu (∑ q : Fin (N0 + 1), ∑ j : Fin (m q),
    Tot.tmul 𝒜 Q (D.s q j : A) (lof (𝒜 0) ℤ Q (n - ((q : ℕ) : ℤ)) (z ⟨q, j⟩))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [totMapAlong_tmul, hs, DirectSum.lof_eq_of, famMap_of]
  rfl

end Natural

end TotRetract

/-- Dual basis for `𝒜^q` on compact `X`: sections `s_j` and coefficient functionals `c_j`,
compatible with restriction, with `a = ∑ c_j(a) s_j` (from `isFinFreeSummand_pieceSheaf`). -/
theorem exists_dual [CompactSpace X] (q : ℕ) : ∃ (m : ℕ)
    (s : Fin m → ∀ V : Opens X, ↥(GCDga.piece (P.D.𝒜 V) q))
    (c : Fin m → ∀ V : Opens X,
      ↥(GCDga.piece (P.D.𝒜 V) q) →ₗ[↥(P.D.𝒜 V 0)] ↥(P.D.𝒜 V 0)),
    (∀ j (V W : Opens X) (h : W ≤ V),
      P.D.res h (s j V : P.D.A V) = (s j W : P.D.A W)) ∧
    (∀ j (V W : Opens X) (h : W ≤ V) (a : ↥(GCDga.piece (P.D.𝒜 V) q)),
      c j W (P.resPiece q h a) = (P.D.res h).f0 (c j V a)) ∧
    ∀ (V : Opens X) (a : ↥(GCDga.piece (P.D.𝒜 V) q)),
      (a : P.D.A V) = ∑ j, ((c j V a : ↥(P.D.𝒜 V 0)) : P.D.A V) * (s j V : P.D.A V) := by
  obtain ⟨m, i, p, hip⟩ := P.isFinFreeSummand_pieceSheaf q
  have : Limits.HasFiniteBiproducts (Mod (ringOf P.A0)) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  let iso := Limits.biproduct.isoCoproduct
    (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0))
  let i' : P.pieceSheaf q ⟶ ∐ (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)) := i
  let p' : ∐ (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)) ⟶ P.pieceSheaf q := p
  have hip' : i' ≫ p' = 𝟙 _ := hip
  let cj : Fin m → (P.pieceSheaf q ⟶ SheafOfModules.unit (ringOf P.A0)) :=
    fun j => i' ≫ iso.inv ≫
      Limits.biproduct.π (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)) j
  let ej : Fin m → (SheafOfModules.unit (ringOf P.A0) ⟶ P.pieceSheaf q) :=
    fun j => Limits.biproduct.ι (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)) j ≫
      iso.hom ≫ p'
  have hsum : ∑ j, cj j ≫ ej j = 𝟙 _ := by
    have h1 : ∀ j, cj j ≫ ej j = (i' ≫ iso.inv) ≫ (
        Limits.biproduct.π (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)) j ≫
        Limits.biproduct.ι (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)) j) ≫
        (iso.hom ≫ p') := fun j => by simp only [cj, ej, Category.assoc]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Preadditive.comp_sum,
      ← Preadditive.sum_comp, Limits.biproduct.total, Category.id_comp,
      Category.assoc, iso.inv_hom_id_assoc, hip']
  refine ⟨m, fun j V => (((ej j).val.app (op V)).hom (1 : ↥(P.D.𝒜 V 0)) :
      ↥(GCDga.piece (P.D.𝒜 V) q)), fun j V => ((cj j).val.app (op V)).hom, ?_, ?_, ?_⟩
  · intro j V W h
    have h1 := PresheafOfModules.naturality_apply (ej j).val (homOfLE h).op
      (1 : (ringOf P.A0).obj.obj (op V))
    have h2 := PresheafOfModules.unit_map_one (R := (ringOf P.A0).obj) (homOfLE h).op
    exact congrArg Subtype.val
      ((congrArg (fun x => ((ej j).val.app (op W)).hom x) h2.symm).trans h1).symm
  · intro j V W h a
    exact PresheafOfModules.naturality_apply (cj j).val (homOfLE h).op a
  · intro V a
    have hs : (∑ j, cj j ≫ ej j).val.app (op V) = ∑ j, ((cj j ≫ ej j).val.app (op V)) :=
      Functor.map_sum (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op V)) _ _
    have h3 : ((∑ j, cj j ≫ ej j).val.app (op V)).hom a = a := by rw [hsum]; rfl
    rw [hs, ModuleCat.hom_sum] at h3
    erw [LinearMap.sum_apply] at h3
    let T : Fin m → ↥(GCDga.piece (P.D.𝒜 V) q) :=
      fun d => ((cj d ≫ ej d).val.app (op V)).hom a
    have h3' : ∑ d, T d = a := h3
    refine (congrArg Subtype.val h3'.symm).trans ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    let E : ↥(P.D.𝒜 V 0) →ₗ[↥(P.D.𝒜 V 0)] ↥(GCDga.piece (P.D.𝒜 V) q) :=
      ((ej j).val.app (op V)).hom
    have key : ∀ r : ↥(P.D.𝒜 V 0), E r = r • E 1 := fun r => by
      have := map_smul E r 1
      rwa [smul_eq_mul, mul_one] at this
    exact congrArg Subtype.val (key _)

/-- Uniform vanishing of `𝒜_V^q` above the top degree `N` of `𝒜_X` (compact `X`), from the
dual bases of `exists_dual`. -/
theorem zero_above [CompactSpace X] {q : ℤ} (hq : (GCDga.N (P.D.𝒜 ⊤) : ℤ) < q) (V : Opens X)
    {a : P.D.A V} (ha : a ∈ P.D.𝒜 V q) : a = 0 := by
  obtain ⟨q', rfl⟩ : ∃ q' : ℕ, (q' : ℤ) = q := ⟨q.toNat, by omega⟩
  obtain ⟨m, s, c, hs, hc, he⟩ := P.exists_dual q'
  have h0 : ∀ j, (s j V : P.D.A V) = 0 := fun j => by
    rw [← hs j ⊤ V le_top, GCDga.eq_zero_of_gt (P.D.𝒜 ⊤) hq (s j ⊤).2, map_zero]
  exact (he V ⟨a, ha⟩).trans (Finset.sum_eq_zero fun j _ => by rw [h0 j, mul_zero])

/-- Uniform dual basis data on all opens, compatible with restriction. -/
theorem exists_dfm [CompactSpace X] : ∃ (N0 : ℕ) (m : ℕ → ℕ)
    (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m),
    (∀ (V W : Opens X) (h : W ≤ V) q j,
      P.D.res h ((D V).s q j : P.D.A V) = ((D W).s q j : P.D.A W)) ∧
    (∀ (V W : Opens X) (h : W ≤ V) (q : ℕ) j (a : ↥(GCDga.piece (P.D.𝒜 V) q))
      (b : ↥(GCDga.piece (P.D.𝒜 W) q)), (b : P.D.A W) = P.D.res h a →
      (D W).c q j b = (P.D.res h).f0 ((D V).c q j a)) := by
  choose m s c hs hc he using fun q : ℕ => P.exists_dual q
  refine ⟨GCDga.N (P.D.𝒜 ⊤), m, fun V => ⟨fun q j => s q j V, fun q j => c q j V,
    fun q a => he q V a, fun q hq a ha => P.zero_above hq V ha⟩,
    fun V W h q j => hs q j V W h, ?_⟩
  intro V W h q j a b hab
  have : b = P.resPiece q h a := Subtype.ext hab
  subst this
  exact hc q j V W h a

end PreResolvingData

end Cohesive
