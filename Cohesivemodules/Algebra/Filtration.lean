import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.QuasiIso
import Cohesivemodules.Algebra.Cohesive
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.ModuleCat.Basic

set_option linter.style.header false

/-!
# A6–A7: the form-degree filtration; finite filtration comparison

Blueprint items A6, A7.

## A6
`filTot b ⊆ A ⊗_{A⁰} ⨁ Q` is spanned by `a ⊗ e` with `a` of form degree `≥ b`; `𝕏` preserves
it. `F^b Hom^n` consists of the `φ` that raise this filtration by `b`; equivalently
(`memFilHom_iff`) `φ(1 ⊗ e)` has no components of form degree `< b`, the definition of
[B, Prop 2.5.1], [A, Def 3.3.2]. `δ` preserves `F^b`, `F^0 = Hom^n`, `F^{N+1} = 0`. The Hom
complex is packaged as a Mathlib cochain complex `homComplex`.

## A7
 A morphism of finitely filtered complexes that induces quasi-isomorphisms on
all graded pieces is a quasi-isomorphism. Proof: downward induction on the filtration with the
homology long exact sequence. This replaces the spectral sequences of [B, Prop 2.5.1] and
[A, Def 3.3.2].

* `quasiIso_τ₂`: in a morphism of short exact sequences of cochain complexes, if the outer
  maps are quasi-isomorphisms, so is the middle one. (Mathlib has the version for the third map,
  `HomologicalComplex.HomologySequence.quasiIso_τ₃`; the others are a Mathlib TODO.)
* `quasiIso_of_finite_filtration`: A7.

## Deviations from the sources
* The filtration is given by its short exact sequences `F^{b+1} → F^b → gr^b`, `b < N`, with
  `F^N` acyclic; this is the form in which A12 and C5 use it.
-/

namespace Cohesive

open CategoryTheory Limits HomologicalComplex ComposableArrows Abelian

variable {C : Type*} [Category C] [Abelian C]

/-- In a morphism of short exact sequences of `ℤ`-indexed cochain complexes, if the outer maps
are quasi-isomorphisms, so is the middle one (four lemma, twice, on the homology long exact
sequences). -/
theorem quasiIso_τ₂ {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hmono : Mono (homologyMap φ.τ₂ i) := by
    apply mono_of_epi_of_mono_of_mono ((δ₀Functor ⋙ δ₀Functor).map
      (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ (i - 1) i (by simp)))
    · exact (HomologySequence.composableArrows₅_exact hS₁ (i - 1) i (by simp)).δ₀.δ₀
    · exact (HomologySequence.composableArrows₅_exact hS₂ (i - 1) i (by simp)).δ₀.δ₀
    · change Epi (homologyMap φ.τ₃ (i - 1)); infer_instance
    · change Mono (homologyMap φ.τ₁ i); infer_instance
    · change Mono (homologyMap φ.τ₃ i); infer_instance
  have hepi : Epi (homologyMap φ.τ₂ i) := by
    apply epi_of_epi_of_epi_of_mono ((δlastFunctor ⋙ δlastFunctor).map
      (HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i (i + 1) (by simp)))
    · exact (HomologySequence.composableArrows₅_exact hS₁ i (i + 1) (by simp)).δlast.δlast
    · exact (HomologySequence.composableArrows₅_exact hS₂ i (i + 1) (by simp)).δlast.δlast
    · change Epi (homologyMap φ.τ₁ i); infer_instance
    · change Epi (homologyMap φ.τ₃ i); infer_instance
    · change Mono (homologyMap φ.τ₁ (i + 1)); infer_instance
  exact isIso_of_mono_of_epi _

/-- **A7.** Finite filtration comparison. Let `f_b : F^b K → F^b L` (`b ≤ N`) be maps of cochain
complexes and `g_b : gr^b K → gr^b L` (`b < N`), compatible with short exact sequences
`F^{b+1} → F^b → gr^b` on both sides. If every `g_b` is a quasi-isomorphism and `f_N` is one
(e.g. `F^N = 0`), then `f_0` is a quasi-isomorphism. [B, Prop 2.5.1], [A, Def 3.3.2]; the proof
replaces the spectral sequence by the long exact sequence. -/
theorem quasiIso_of_finite_filtration (N : ℕ) (SK SL : ℕ → ShortComplex (CochainComplex C ℤ))
    (hSK : ∀ b, (SK b).ShortExact) (hSL : ∀ b, (SL b).ShortExact) (ψ : ∀ b, SK b ⟶ SL b)
    (f : ℕ → Σ (K L : CochainComplex C ℤ), K ⟶ L)
    (h₁ : ∀ b, Arrow.mk (ψ b).τ₁ = Arrow.mk (f (b + 1)).2.2)
    (h₂ : ∀ b, Arrow.mk (ψ b).τ₂ = Arrow.mk (f b).2.2)
    (hgr : ∀ b < N, QuasiIso (ψ b).τ₃) (hN : QuasiIso (f N).2.2) : QuasiIso (f 0).2.2 := by
  have key : ∀ m ≤ N, QuasiIso (f (N - m)).2.2 := by
    intro m
    induction m with
    | zero => intro _; simpa using hN
    | succ m ih =>
      intro hm
      have hb : N - (m + 1) < N := by omega
      have h1 : QuasiIso (ψ (N - (m + 1))).τ₁ := by
        have := ih (by omega)
        have e := h₁ (N - (m + 1))
        rw [show N - (m + 1) + 1 = N - m by omega] at e
        exact (quasiIso_iff_of_arrow_mk_iso _ _ (eqToIso e)).2 this
      have h2 := quasiIso_τ₂ (ψ (N - (m + 1))) (hSK _) (hSL _) h1 (hgr _ hb)
      exact (quasiIso_iff_of_arrow_mk_iso _ _ (eqToIso (h₂ (N - (m + 1))))).1 h2
  have := key N le_rfl
  rwa [Nat.sub_self] at this

/-! ## A6: the form-degree filtration -/

section A6

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable (𝒜) in
/-- **A6** The form-degree filtration of the total module: spanned by `a ⊗ e` with `a ∈ A^q`,
`q ≥ b`. -/
def filTot (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (b : ℤ) :
    Submodule k (Tot 𝒜 Q) :=
  Submodule.span k {x | ∃ (q : ℤ) (a : A) (e : ⨁ p, Q p), b ≤ q ∧ a ∈ 𝒜 q ∧
    x = Tot.tmul 𝒜 Q a e}

variable {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- A6: `a ⊗ e ∈ filTot b` for `a ∈ A^q`, `q ≥ b`. -/
theorem tmul_mem_filTot {b q : ℤ} (hbq : b ≤ q) {a : A} (ha : a ∈ 𝒜 q) (e : ⨁ p, Q p) :
    Tot.tmul 𝒜 Q a e ∈ filTot 𝒜 Q b :=
  Submodule.subset_span ⟨q, a, e, hbq, ha, rfl⟩

/-- A6: the filtration is decreasing. -/
theorem filTot_anti {b c : ℤ} (h : b ≤ c) : filTot 𝒜 Q c ≤ filTot 𝒜 Q b :=
  Submodule.span_mono fun _ ⟨q, a, e, hcq, ha, hx⟩ => ⟨q, a, e, h.trans hcq, ha, hx⟩

/-- A6: `filTot 0` is everything. -/
theorem filTot_zero (x : Tot 𝒜 Q) : x ∈ filTot 𝒜 Q 0 := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.tmul_eq_sum]
    exact Submodule.sum_mem _ fun q hq =>
      tmul_mem_filTot (Finset.mem_Icc.1 hq).1 (GCDga.proj_mem 𝒜 q a) e
  | hadd x y hx hy => exact add_mem hx hy

/-- A6: `filTot b = 0` for `b > N`. -/
theorem filTot_eq_bot {b : ℤ} (hb : (GCDga.N 𝒜 : ℤ) < b) : filTot 𝒜 Q b = ⊥ := by
  rw [eq_bot_iff, filTot, Submodule.span_le]
  rintro _ ⟨q, a, e, hbq, ha, rfl⟩
  rw [GCDga.eq_zero_of_gt 𝒜 (by omega) ha, Tot.zero_tmul]
  exact zero_mem _

/-- A6: multiplication by `a ∈ A^q` raises the filtration by `q`. -/
theorem smul_mem_filTot {q b : ℤ} {a : A} (ha : a ∈ 𝒜 q) {x : Tot 𝒜 Q}
    (hx : x ∈ filTot 𝒜 Q b) : a • x ∈ filTot 𝒜 Q (q + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q', c, e, hbq, hc, rfl⟩ := hx
    rw [Tot.smul_tmul]
    exact tmul_mem_filTot (by omega) (SetLike.GradedMul.mul_mem ha hc) e
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul r x _ hx => rw [smul_algebra_smul_comm]; exact Submodule.smul_mem _ r hx

/-- A6: `𝕏` preserves the form-degree filtration. -/
theorem X_mem_filTot (M : QuasiCohesive 𝒜) {b : ℤ} {x : M.T} (hx : x ∈ filTot 𝒜 M.Q b) :
    M.X x ∈ filTot 𝒜 M.Q b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hbq, ha, rfl⟩ := hx
    rw [Tot.tmul_eq_smul, M.leibniz ha]
    refine add_mem ?_ ?_
    · rw [← Tot.tmul_eq_smul]
      exact tmul_mem_filTot (by omega) (GCDga.d_mem (𝒜 := 𝒜) ha) e
    · rw [Units.smul_def]
      refine Submodule.smul_of_tower_mem _ _ ?_
      have := smul_mem_filTot ha (filTot_zero (M.X (Tot.tmul 𝒜 M.Q 1 e)))
      rw [add_zero] at this
      exact filTot_anti hbq this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

variable (M₁ M₂ : QuasiCohesive 𝒜)

/-- **A6** `F^b Hom^n(M₁, M₂)`: the `φ ∈ Hom^n` raising the form-degree filtration by `b`.
[B, Prop 2.5.1], [A, Def 3.3.2]; see `memFilHom_iff` for the definition by components. -/
def filHom (n b : ℤ) : Submodule k (M₁.T →ₗ[k] M₂.T) :=
  Hom M₁ M₂ n ⊓
    { carrier := {φ | ∀ (c : ℤ) (x : M₁.T), x ∈ filTot 𝒜 M₁.Q c → φ x ∈ filTot 𝒜 M₂.Q (c + b)}
      add_mem' := fun hφ hψ c x hx => add_mem (hφ c x hx) (hψ c x hx)
      zero_mem' := fun _ _ _ => zero_mem _
      smul_mem' := fun r _ hφ c x hx => Submodule.smul_mem _ r (hφ c x hx) }

variable {M₁ M₂}

/-- **A6** `φ ∈ F^b` iff `φ(1 ⊗ e)` has form degree `≥ b` for all generators `e`: the components
of `φ` into `A^{b'} ⊗ Q₂` vanish for `b' < b`. -/
theorem memFilHom_iff {n b : ℤ} {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Hom M₁ M₂ n) :
    φ ∈ filHom M₁ M₂ n b ↔ ∀ e, φ (Tot.tmul 𝒜 M₁.Q 1 e) ∈ filTot 𝒜 M₂.Q b := by
  constructor
  · intro h e
    have := (Submodule.mem_inf.1 h).2 0 (Tot.tmul 𝒜 M₁.Q 1 e) (filTot_zero _)
    rwa [zero_add] at this
  · intro h
    refine Submodule.mem_inf.2 ⟨hφ, fun c x hx => ?_⟩
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, a, e, hcq, ha, rfl⟩ := hx
      rw [Tot.tmul_eq_smul, hφ.2 ha, Units.smul_def]
      refine Submodule.smul_of_tower_mem _ _ ?_
      exact filTot_anti (by omega) (smul_mem_filTot ha (h e))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- **A6** `δ` preserves `F^b`. -/
theorem δ_mem_filHom {n b : ℤ} {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ filHom M₁ M₂ n b) :
    δ M₁ M₂ n φ ∈ filHom M₁ M₂ (n + 1) b := by
  obtain ⟨hφ₁, hφ₂⟩ := Submodule.mem_inf.1 hφ
  refine Submodule.mem_inf.2 ⟨δ_mem M₁ M₂ hφ₁, fun c x hx => ?_⟩
  simp only [δ_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    Units.smul_def]
  exact sub_mem (X_mem_filTot M₂ (hφ₂ c x hx))
    (Submodule.smul_of_tower_mem _ _ (hφ₂ c _ (X_mem_filTot M₁ hx)))

/-- **A6** The filtration is exhaustive: `F^0 = Hom^n`. -/
theorem filHom_zero {n : ℤ} {φ : M₁.T →ₗ[k] M₂.T} (hφ : φ ∈ Hom M₁ M₂ n) :
    φ ∈ filHom M₁ M₂ n 0 :=
  (memFilHom_iff hφ).2 fun _ => filTot_zero _

/-- **A6** The filtration is finite: `F^{N+1} = 0`. -/
theorem filHom_eq_zero {n b : ℤ} (hb : (GCDga.N 𝒜 : ℤ) < b) {φ : M₁.T →ₗ[k] M₂.T}
    (hφ : φ ∈ filHom M₁ M₂ n b) : φ = 0 := by
  obtain ⟨hφ₁, -⟩ := Submodule.mem_inf.1 hφ
  have h0 : ∀ e, φ (Tot.tmul 𝒜 M₁.Q 1 e) = 0 := fun e => by
    have := (memFilHom_iff hφ₁).1 hφ e
    rwa [filTot_eq_bot hb, Submodule.mem_bot] at this
  ext x
  induction x using Tot.induction_on with
  | ht a e =>
    rw [Tot.tmul_eq_sum, map_sum, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [Tot.tmul_eq_smul, hφ₁.2 (GCDga.proj_mem 𝒜 q a), h0, smul_zero, smul_zero]
  | hadd x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

variable (M₁ M₂) in
/-- **A4** The Hom complex `(Hom^•(M₁, M₂), δ)` as a Mathlib cochain complex of `k`-modules. -/
noncomputable def homComplex : CochainComplex (ModuleCat.{0} k) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of k (Hom M₁ M₂ n))
    (fun n => ModuleCat.ofHom
      { toFun φ := ⟨δ M₁ M₂ n φ.1, δ_mem M₁ M₂ φ.2⟩
        map_add' _ _ := Subtype.ext (map_add _ _ _)
        map_smul' _ _ := Subtype.ext (map_smul _ _ _) })
    (fun _ => ModuleCat.hom_ext (LinearMap.ext fun φ => Subtype.ext (δ_δ M₁ M₂ φ.2)))

end A6

end Cohesive
