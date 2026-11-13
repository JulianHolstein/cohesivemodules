import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Refinements

set_option linter.style.header false

/-!
# Resolutions of bounded-above complexes by a generating class

Generic homological algebra used for S8.d (flat resolutions, `FlatResolution.lean`): in an
abelian category in which every object is a quotient of an object with property `P`, every
complex strictly zero above degree `b` receives a quasi-isomorphism from a complex strictly zero
above degree `b` with all terms in `P`. [Stacks, chapter *Derived Categories*, the lemma on
resolving bounded-above complexes by a class of objects of which every object is a quotient]

Proof (by descending induction on degrees, starting at `b`): given `F^{n+1} → … → F^b` with a
map to `K` that is a quasi-isomorphism in degrees `> n + 1`, choose `F^n ∈ P` mapping onto the
pullback `K^n ×_{K^{n+1}} Z^{n+1}(F)`; this makes the map surjective on `H^{n+1}` and injective
on `H^{n+2}`.
-/

namespace Cohesive

open CategoryTheory Limits
open scoped ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

section Aux

variable {P : ObjectProperty C} (hP : ∀ M : C, ∃ (F : C) (f : F ⟶ M), P F ∧ Epi f)

/-- A chosen object with property `P` surjecting onto `M`. -/
private noncomputable def pickObj (M : C) : C := (hP M).choose

/-- The chosen epimorphism `pickObj hP M ⟶ M`. -/
private noncomputable def pickHom (M : C) : pickObj hP M ⟶ M := (hP M).choose_spec.choose

omit [Abelian C] in
/-- The chosen object satisfies `P`. -/
private lemma pickObj_prop (M : C) : P (pickObj hP M) := (hP M).choose_spec.choose_spec.1

/-- The chosen map is an epimorphism. -/
private instance pickHom_epi (M : C) : Epi (pickHom hP M) := (hP M).choose_spec.choose_spec.2

/-- One stage of the descending construction of a resolution of `L : ChainComplex C ℕ`:
an object `X` (to be `G_k`), its target `Y` (to be `G_{k-1}`), the differential and the map
`X ⟶ L_k`. -/
private structure ResStep (L : ChainComplex C ℕ) (k : ℕ) where
  /-- the object `G_k` -/
  X : C
  /-- the object `G_{k-1}` -/
  Y : C
  /-- the differential -/
  d : X ⟶ Y
  /-- the component of the comparison map -/
  g : X ⟶ L.X k

/-- The pullback `L_{k+1} ×_{L_k} Z_k(G)` used to build the next stage. -/
private noncomputable abbrev resPB {L : ChainComplex C ℕ} {k : ℕ} (s : ResStep L k) : C :=
  pullback (L.d (k + 1) k) (kernel.ι s.d ≫ s.g)

/-- The next stage: a `P`-object surjecting onto the pullback `resPB s`. -/
private noncomputable def ResStep.next {L : ChainComplex C ℕ} {k : ℕ} (s : ResStep L k) :
    ResStep L (k + 1) where
  X := pickObj hP (resPB s)
  Y := s.X
  d := pickHom hP (resPB s) ≫ pullback.snd _ _ ≫ kernel.ι s.d
  g := pickHom hP (resPB s) ≫ pullback.fst _ _

/-- The initial stage. -/
private noncomputable def ResStep.init (L : ChainComplex C ℕ) : ResStep L 0 where
  X := pickObj hP (L.X 0)
  Y := 0
  d := 0
  g := pickHom hP (L.X 0)

/-- The sequence of stages. -/
private noncomputable def resSeq (L : ChainComplex C ℕ) : ∀ k, ResStep L k
  | 0 => ResStep.init hP L
  | k + 1 => (resSeq L k).next hP

/-- The resolving chain complex. -/
private noncomputable def resComplex (L : ChainComplex C ℕ) : ChainComplex C ℕ :=
  ChainComplex.of (fun k => (resSeq hP L k).X) (fun k => (resSeq hP L (k + 1)).d)
    (fun k => by
      show (pickHom hP _ ≫ pullback.snd _ _ ≫ kernel.ι (resSeq hP L (k + 1)).d) ≫
        (resSeq hP L (k + 1)).d = 0
      simp only [Category.assoc, kernel.condition, comp_zero])

/-- Differentials of the resolving complex. -/
private lemma resComplex_d (L : ChainComplex C ℕ) (j : ℕ) :
    (resComplex hP L).d (j + 1) j = (resSeq hP L (j + 1)).d := by
  simp only [resComplex]
  exact ChainComplex.of_d _ _ j

/-- The comparison map from the resolving complex. -/
private noncomputable def resMap (L : ChainComplex C ℕ) : resComplex hP L ⟶ L where
  f k := (resSeq hP L k).g
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst hij
    rw [resComplex_d]
    show (pickHom hP (resPB (resSeq hP L j)) ≫ pullback.fst _ _) ≫ L.d (j + 1) j =
      (pickHom hP (resPB (resSeq hP L j)) ≫ pullback.snd _ _ ≫
        kernel.ι (resSeq hP L j).d) ≫ (resSeq hP L j).g
    simp only [Category.assoc]
    rw [pullback.condition]

/-- Injectivity step: a cycle of `G_j` mapping to a boundary in `L` is a boundary
(after a refinement). -/
private lemma res_mono_step (L : ChainComplex C ℕ) (j : ℕ) {A : C}
    (x₂ : A ⟶ (resSeq hP L j).X) (hx : x₂ ≫ (resSeq hP L j).d = 0)
    (y₁ : A ⟶ L.X (j + 1))
    (hy : x₂ ≫ (resSeq hP L j).g = y₁ ≫ L.d (j + 1) j) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ (resSeq hP L (j + 1)).X),
      π ≫ x₂ = x₁ ≫ (resSeq hP L (j + 1)).d := by
  let w : A ⟶ resPB (resSeq hP L j) :=
    pullback.lift y₁ (kernel.lift _ x₂ hx)
      (by rw [← Category.assoc, kernel.lift_ι]; exact hy.symm)
  obtain ⟨A', π, hπ, x₁, h⟩ :=
    (epi_iff_surjective_up_to_refinements (pickHom hP (resPB (resSeq hP L j)))).1 inferInstance w
  refine ⟨A', π, hπ, x₁, ?_⟩
  show π ≫ x₂ = x₁ ≫ (pickHom hP _ ≫ pullback.snd _ _ ≫ kernel.ι _)
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, w, pullback.lift_snd_assoc, kernel.lift_ι]

/-- Surjectivity step in positive degree: a cycle of `L_{j+1}` lifts to a cycle of `G_{j+1}`
(after a refinement). -/
private lemma res_epi_step (L : ChainComplex C ℕ) (j : ℕ) {A : C} (y₂ : A ⟶ L.X (j + 1))
    (hy : y₂ ≫ L.d (j + 1) j = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ (resSeq hP L (j + 1)).X),
      x₂ ≫ (resSeq hP L (j + 1)).d = 0 ∧ π ≫ y₂ = x₂ ≫ (resSeq hP L (j + 1)).g := by
  let w : A ⟶ resPB (resSeq hP L j) :=
    pullback.lift y₂ 0 (by rw [hy]; simp only [zero_comp])
  obtain ⟨A', π, hπ, x₂, h⟩ :=
    (epi_iff_surjective_up_to_refinements (pickHom hP (resPB (resSeq hP L j)))).1 inferInstance w
  refine ⟨A', π, hπ, x₂, ?_, ?_⟩
  · show x₂ ≫ (pickHom hP _ ≫ pullback.snd _ _ ≫ kernel.ι _) = 0
    rw [← Category.assoc, ← h]
    simp only [Category.assoc, w, pullback.lift_snd_assoc, zero_comp, comp_zero]
  · show π ≫ y₂ = x₂ ≫ (pickHom hP _ ≫ pullback.fst _ _)
    rw [← Category.assoc, ← h]
    simp only [Category.assoc, w, pullback.lift_fst]

/-- Surjectivity step in degree zero. -/
private lemma res_epi_zero (L : ChainComplex C ℕ) {A : C} (y₂ : A ⟶ L.X 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₂ : A' ⟶ (resSeq hP L 0).X),
      π ≫ y₂ = x₂ ≫ (resSeq hP L 0).g :=
  (epi_iff_surjective_up_to_refinements (pickHom hP (L.X 0))).1 inferInstance y₂

/-- The comparison map is a quasi-isomorphism in every degree. -/
private lemma resMap_quasiIsoAt (L : ChainComplex C ℕ) (j : ℕ) :
    QuasiIsoAt (resMap hP L) j := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  rcases j with _ | m
  · have hi : (ComplexShape.down ℕ).prev 0 = 1 := ChainComplex.prev ℕ 0
    have hk : (ComplexShape.down ℕ).next 0 = 0 := ChainComplex.next_nat_zero
    have hmono : Mono (HomologicalComplex.homologyMap (resMap hP L) 0) := by
      rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ 1 0 0 hi hk]
      intro A x₂ _ y₁ hy
      obtain ⟨A', π, hπ, x₁, h⟩ := res_mono_step hP L 0 x₂ (comp_zero) y₁ hy
      exact ⟨A', π, hπ, x₁,
        h.trans (congrArg (fun t => x₁ ≫ t) (resComplex_d hP L 0).symm)⟩
    have hepi : Epi (HomologicalComplex.homologyMap (resMap hP L) 0) := by
      rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ 1 0 0 hi hk]
      intro A y₂ _
      obtain ⟨A', π, hπ, x₂, h⟩ := res_epi_zero hP L y₂
      refine ⟨A', π, hπ, x₂, ?_, 0, ?_⟩
      · rw [HomologicalComplex.shape _ _ _ (by simp)]
        exact comp_zero
      · rw [zero_comp, add_zero]; exact h
    exact isIso_of_mono_of_epi _
  · have hi : (ComplexShape.down ℕ).prev (m + 1) = m + 2 := ChainComplex.prev ℕ (m + 1)
    have hk : (ComplexShape.down ℕ).next (m + 1) = m := ChainComplex.next_nat_succ m
    have hmono : Mono (HomologicalComplex.homologyMap (resMap hP L) (m + 1)) := by
      rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements _ (m + 2) (m + 1) m hi hk]
      intro A x₂ hx y₁ hy
      rw [resComplex_d] at hx
      obtain ⟨A', π, hπ, x₁, h⟩ := res_mono_step hP L (m + 1) x₂ hx y₁ hy
      exact ⟨A', π, hπ, x₁,
        h.trans (congrArg (fun t => x₁ ≫ t) (resComplex_d hP L (m + 1)).symm)⟩
    have hepi : Epi (HomologicalComplex.homologyMap (resMap hP L) (m + 1)) := by
      rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements _ (m + 2) (m + 1) m hi hk]
      intro A y₂ hy
      obtain ⟨A', π, hπ, x₂, hx, h⟩ := res_epi_step hP L m y₂ hy
      refine ⟨A', π, hπ, x₂, ?_, 0, ?_⟩
      · rw [resComplex_d]; exact hx
      · rw [zero_comp, add_zero]; exact h
    exact isIso_of_mono_of_epi _

include hP in
/-- The resolving complex has terms with property `P` and maps quasi-isomorphically to `L`. -/
private lemma exists_quasiIso_chain (L : ChainComplex C ℕ) :
    ∃ (G : ChainComplex C ℕ) (g : G ⟶ L), (∀ n, P (G.X n)) ∧ QuasiIso g := by
  refine ⟨resComplex hP L, resMap hP L, fun n => ?_, ⟨fun j => resMap_quasiIsoAt hP L j⟩⟩
  rcases n with _ | m
  · exact pickObj_prop hP _
  · exact pickObj_prop hP _

end Aux

/-- **S8.d (generic part).** If every object of the abelian category `C` is a quotient of an
object with property `P`, and zero objects have property `P`, then every cochain complex `K`
strictly zero above degree `b` receives a quasi-isomorphism `f : F ⟶ K` from a complex `F`
strictly zero above degree `b` whose terms all have property `P`.

Deviation: the hypothesis on zero objects is needed because `F.X n` must have property `P` in
every degree, including those above `b`. -/
theorem exists_quasiIso_of_enough (P : ObjectProperty C)
    (hP : ∀ M : C, ∃ (F : C) (f : F ⟶ M), P F ∧ Epi f) (hP₀ : ∀ Z : C, IsZero Z → P Z)
    (K : CochainComplex C ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (F : CochainComplex C ℤ) (f : F ⟶ K),
      F.IsStrictlyLE b ∧ (∀ n, P (F.X n)) ∧ QuasiIso f := by
  obtain ⟨G, g, hG, hq⟩ :=
    exists_quasiIso_chain hP (K.restriction (ComplexShape.embeddingUpIntLE b))
  have hlift : (ComplexShape.embeddingUpIntLE b).HasLift
      (𝟙 (K.restriction (ComplexShape.embeddingUpIntLE b))) := by
    intro j hj
    exfalso
    refine hj.2 (j + 1) ?_
    simp only [ComplexShape.embeddingUpIntLE_f, ComplexShape.up_Rel]
    push_cast
    lia
  let φ : K ⟶ (K.restriction (ComplexShape.embeddingUpIntLE b)).extend
      (ComplexShape.embeddingUpIntLE b) :=
    (ComplexShape.embeddingUpIntLE b).liftExtend _ hlift
  have hφ : IsIso φ := by
    suffices ∀ i', IsIso (φ.f i') from HomologicalComplex.Hom.isIso_of_components φ
    intro i'
    by_cases hi' : ∃ i, (ComplexShape.embeddingUpIntLE b).f i = i'
    · obtain ⟨i, hi⟩ := hi'
      rw [ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ hlift hi]
      infer_instance
    · have hi'' : ∀ i, (ComplexShape.embeddingUpIntLE b).f i ≠ i' :=
        fun i hi => hi' ⟨i, hi⟩
      exact IsZero.isIso
        (HomologicalComplex.isZero_X_of_isStrictlySupported K
          (ComplexShape.embeddingUpIntLE b) i' hi'')
        (HomologicalComplex.isZero_extend_X _ _ _ hi'') _
  refine ⟨G.extend (ComplexShape.embeddingUpIntLE b),
    HomologicalComplex.extendMap g (ComplexShape.embeddingUpIntLE b) ≫ inv φ, inferInstance,
    fun n => ?_, ?_⟩
  · show P (HomologicalComplex.extend.X G ((ComplexShape.embeddingUpIntLE b).r n))
    rcases h : (ComplexShape.embeddingUpIntLE b).r n with _ | i
    · exact hP₀ _ (HomologicalComplex.extend.isZero_X G rfl)
    · exact hG i
  · have : QuasiIso (HomologicalComplex.extendMap g (ComplexShape.embeddingUpIntLE b)) :=
      inferInstance
    infer_instance

end Cohesive
