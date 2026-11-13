import Cohesivemodules.Sheaf.PerfectDef
import Cohesivemodules.Sheaf.Restriction
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

set_option linter.style.header false

/-!
# S9: perfect complexes

Blueprint items S9.c (invariance) and S9.d (§3). The definitions (S9.a–c) are in
`Sheaf/PerfectDef.lean`; S10 is in `Sheaf/Globalize.lean`.

* S9.c perfectness is invariant under quasi-isomorphism, and `Q K ∈ Perf R ↔ K` perfect.
* S9.d on compact `X` a perfect complex has local strictly perfect models in one degree range
  `[a, b]` (`IsPerfectIn K a b`), and its homology vanishes outside `[a, b]`.

## Deviations
* S9.d records only the uniform degree range; a uniform bound on the number of generators
  ([A, Def 7.2.11 (3)]) is not needed: on compact `X` a finite subcover gives it anyway.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

/-! ## S9.c Invariance -/

/-- **S9.c.** The target of a quasi-isomorphism `f : K ⟶ K'` out of a perfect complex is
perfect (compose the local roofs with `f|U`). -/
theorem IsPerfect.of_quasiIso_left {K K' : CochainComplex (Mod R) ℤ} (f : K ⟶ K')
    [QuasiIso f] (hK : IsPerfect K) : IsPerfect K' := by
  intro x
  obtain ⟨U, hU, L, P, g, h, hg, hh, hP⟩ := hK x
  have : QuasiIso (((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    inferInstance
  exact ⟨U, hU, L, P, g ≫ ((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).map f, h,
    inferInstance, hh, hP⟩

universe w v u

/-- Pullback of quasi-isomorphisms (roofs), through the derived category. -/
private lemma exists_pullback_quasiIso {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {K K' L : CochainComplex C ℤ} (f : K ⟶ K') (s : L ⟶ K')
    [QuasiIso f] [QuasiIso s] :
    ∃ (M : CochainComplex C ℤ) (t : M ⟶ K) (u : M ⟶ L), QuasiIso t ∧ QuasiIso u := by
  have h1 : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 ‹_›
  have h2 : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 ‹_›
  obtain ⟨M, t, ht, u, hu⟩ := DerivedCategory.right_fac
    (DerivedCategory.Q.map f ≫ inv (DerivedCategory.Q.map s))
  have h3 : DerivedCategory.Q.map u = DerivedCategory.Q.map t ≫ DerivedCategory.Q.map f ≫
      inv (DerivedCategory.Q.map s) := by
    rw [hu, IsIso.hom_inv_id_assoc]
  have h4 : IsIso (DerivedCategory.Q.map u) := by
    rw [h3]
    infer_instance
  exact ⟨M, t, u, (DerivedCategory.isIso_Q_map_iff_quasiIso _ t).1 ht,
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ u).1 h4⟩

/-- An isomorphism in the derived category is a roof of quasi-isomorphisms. -/
private lemma exists_roof_of_iso {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {K K' : CochainComplex C ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj K') :
    ∃ (M : CochainComplex C ℤ) (s : M ⟶ K) (g : M ⟶ K'), QuasiIso s ∧ QuasiIso g := by
  obtain ⟨M, s, hs, g, hg⟩ := DerivedCategory.right_fac e.hom
  have h4 : IsIso (DerivedCategory.Q.map g) := by
    have : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ e.hom := by
      rw [hg, IsIso.hom_inv_id_assoc]
    rw [this]; infer_instance
  exact ⟨M, s, g, (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs,
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 h4⟩

/-- **S9.c.** The source of a quasi-isomorphism `f : K ⟶ K'` into a perfect complex is perfect
(a roof `K'|U ← L → P` is pulled back along `f|U` by a homotopy pullback). -/
theorem IsPerfect.of_quasiIso_right {K K' : CochainComplex (Mod R) ℤ} (f : K ⟶ K')
    [QuasiIso f] (hK' : IsPerfect K') : IsPerfect K := by
  intro x
  obtain ⟨U, hU, L, P, s, g, hs, hg, hP⟩ := hK' x
  let _ : HasDerivedCategory (Mod (R.over U)) := HasDerivedCategory.standard _
  have : QuasiIso (((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    inferInstance
  have := hs
  have := hg
  obtain ⟨M, t, u, ht, hu⟩ := exists_pullback_quasiIso
    (((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).map f) s
  have := hu
  exact ⟨U, hU, M, P, t, u ≫ g, ht, inferInstance, hP⟩

/-- **S9.c.** `Q K` lies in `D_perf(X, R)` iff `K` is perfect: an isomorphism `Q K ≅ Q K'` in
the derived category is a roof of quasi-isomorphisms of complexes. -/
theorem perf_Q_obj_iff [HasDerivedCategory.{0} (Mod R)] (K : CochainComplex (Mod R) ℤ) :
    Perf R (DerivedCategory.Q.obj K) ↔ IsPerfect K := by
  constructor
  · rintro ⟨K', hK', ⟨e⟩⟩
    obtain ⟨M, s, g, hs, hg⟩ := exists_roof_of_iso e
    have := hs
    have := hg
    exact IsPerfect.of_quasiIso_left s (IsPerfect.of_quasiIso_right g hK')
  · intro hK
    exact ⟨K, hK, ⟨Iso.refl _⟩⟩

/-! ## S9.d Global bounds -/

/-- **S9.d.** `K` is perfect with all local strictly perfect models concentrated in degrees
`[a, b]` ("globally bounded perfect" of [A, Def 7.2.11 (3)], without the bound on the number of
generators). -/
def IsPerfectIn (K : CochainComplex (Mod R) ℤ) (a b : ℤ) : Prop :=
  ∀ x : X, ∃ U : Opens X, x ∈ U ∧
    ∃ (L P : CochainComplex (Mod (R.over U)) ℤ)
      (f : L ⟶ ((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) (g : L ⟶ P),
      QuasiIso f ∧ QuasiIso g ∧ IsStrictlyPerfect P ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b

theorem IsPerfectIn.isPerfect {K : CochainComplex (Mod R) ℤ} {a b : ℤ}
    (hK : IsPerfectIn K a b) : IsPerfect K := by
  intro x
  obtain ⟨U, hU, L, P, f, g, hf, hg, hP, -, -⟩ := hK x
  exact ⟨U, hU, L, P, f, g, hf, hg, hP⟩

/-- **S9.d.** On compact `X` every perfect complex is globally bounded: one degree range for
all local models (finite subcover). -/
theorem IsPerfect.exists_isPerfectIn [CompactSpace X] {K : CochainComplex (Mod R) ℤ}
    (hK : IsPerfect K) : ∃ a b : ℤ, IsPerfectIn K a b := by
  have key : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ a b : ℤ,
      ∃ (L P : CochainComplex (Mod (R.over U)) ℤ)
      (f : L ⟶ ((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) (g : L ⟶ P),
      QuasiIso f ∧ QuasiIso g ∧ IsStrictlyPerfect P ∧ P.IsStrictlyGE a ∧
        P.IsStrictlyLE b := by
    intro x
    obtain ⟨U, hU, L, P, f, g, hf, hg, hP⟩ := hK x
    obtain ⟨⟨a, b, ha, hb⟩, -⟩ := id hP
    exact ⟨U, hU, a, b, L, P, f, g, hf, hg, hP, ha, hb⟩
  choose U hU a b L P f g hf hg hP ha hb using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩)
  refine ⟨-(∑ i ∈ t, |a i|), ∑ i ∈ t, |b i|, fun x => ?_⟩
  obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, x ∈ (U i : Set X) := by
    have := ht (Set.mem_univ x)
    simpa only [Set.mem_iUnion, exists_prop] using this
  have h1 : |a i| ≤ ∑ j ∈ t, |a j| :=
    Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) hi
  have h2 : |b i| ≤ ∑ j ∈ t, |b j| :=
    Finset.single_le_sum (f := fun j => |b j|) (fun j _ => abs_nonneg _) hi
  have := ha i
  have := hb i
  refine ⟨U i, hxi, L i, P i, f i, g i, hf i, hg i, hP i, ?_, ?_⟩
  · exact (P i).isStrictlyGE_of_ge _ (a i) (by linarith [neg_abs_le (a i)])
  · exact (P i).isStrictlyLE_of_le (b i) _ (by linarith [le_abs_self (b i)])

/-- Sections over `V ≤ U` of `M|U` are those of `M`; so they vanish if `M|U` is zero. -/
private lemma sections_subsingleton {M : Mod R} {U V : Opens X} (hV : V ≤ U)
    (h : IsZero ((restr R U).obj M)) : Subsingleton (M.val.obj (op V)) := by
  have := (SheafOfModules.evaluation.{0} (R.over U) (op (Over.mk (homOfLE hV)))).map_isZero h
  exact (ModuleCat.isZero_iff_subsingleton.1 this)

/-- A sheaf of modules whose restrictions to the members of an open cover are zero is zero. -/
private lemma isZero_of_locally {M : Mod R}
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsZero ((restr R U).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  choose U hU hZ using h
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  let F : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of X) := ⟨M.val.presheaf, M.isSheaf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' F (fun x : X => (U x ⊓ V.unop : Opens (TopCat.of X)))
    V.unop (fun x => homOfLE inf_le_right) ?_ _ _ ?_
  · intro x hx
    exact (Opens.mem_iSup).2 ⟨x, hU x, hx⟩
  · intro x
    have := sections_subsingleton (inf_le_left : U x ⊓ V.unop ≤ U x) (hZ x)
    exact Subsingleton.elim (α := M.val.obj (op (U x ⊓ V.unop))) _ _

/-- Exactness of a complex at `i` is local (homology commutes with the exact functor `restr`). -/
private lemma exactAt_of_locally {K : CochainComplex (Mod R) ℤ} (i : ℤ)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      (((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt i) :
    K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
  refine isZero_of_locally fun x => ?_
  obtain ⟨U, hU, hK⟩ := h x
  refine ⟨U, hU, ?_⟩
  have h1 : ((K.sc i).map (restr R U)).Exact := hK
  rw [ShortComplex.exact_iff_isZero_homology] at h1
  exact IsZero.of_iso h1 ((K.sc i).mapHomologyIso (restr R U)).symm

/-- **S9.d.** The homology sheaves of a perfect complex with local models in `[a, b]` vanish
outside `[a, b]` (locally they are those of the models; S6). -/
theorem IsPerfectIn.exactAt {K : CochainComplex (Mod R) ℤ} {a b : ℤ} (hK : IsPerfectIn K a b)
    (i : ℤ) (hi : i < a ∨ b < i) : K.ExactAt i := by
  refine exactAt_of_locally i fun x => ?_
  obtain ⟨U, hU, L, P, f, g, hf, hg, -, ha, hb⟩ := hK x
  refine ⟨U, hU, ?_⟩
  have hP : P.ExactAt i := by
    rcases hi with hi | hi
    · exact P.exactAt_of_isGE a i hi
    · exact P.exactAt_of_isLE b i hi
  have := (quasiIso_iff f).1 hf i
  have := (quasiIso_iff g).1 hg i
  rw [← exactAt_iff_of_quasiIsoAt f i, exactAt_iff_of_quasiIsoAt g i]
  exact hP

/-! S10 (globalization) is in `Sheaf/Globalize.lean`. -/

end Cohesive
