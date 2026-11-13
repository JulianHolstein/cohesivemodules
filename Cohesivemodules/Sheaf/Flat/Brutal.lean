import Cohesivemodules.Sheaf.Flat.TotAux

set_option linter.style.header false

/-!
# S8 (part 3): brutal truncations, filtered colimits of acyclic complexes

Blueprint item S8 (§3), input for S8.d. Split from `Sheaf/Flat.lean` for size only (CLAUDE.md:
"New work goes in small new files"); no mathematical change.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace

/-!
### Brutal truncations and exactness of filtered colimits of complexes

Generic homological algebra for `isKFlat_of_isFlat`: the brutal truncations `σ_{≥m} F` of a
complex (with their inclusions), `F` as the colimit over `m → -∞`, the short exact sequence
`0 → σ_{≥m+1} F → σ_{≥m} F → F^m[-m] → 0`, and the acyclicity of filtered colimits of acyclic
complexes (Grothendieck's axiom AB5).
-/

section Brutal

open ZeroObject

variable {M : Type*} [Category M] [Preadditive M] [HasZeroObject M]

/-- The brutal truncation `σ_{≥m} F`: keep the terms of degree `≥ m`. -/
noncomputable def brutal (F : CochainComplex M ℤ) (m : ℤ) : CochainComplex M ℤ where
  X p := if m ≤ p then F.X p else 0
  d p q := if h : m ≤ p ∧ m ≤ q then
    eqToHom (by simp [h.1]) ≫ F.d p q ≫ eqToHom (by simp [h.2]) else 0
  shape p q hpq := by
    by_cases h : m ≤ p ∧ m ≤ q
    · simp only [h, and_self, dite_true]
      rw [F.shape p q hpq]
      simp
    · simp only [h, dite_false]
  d_comp_d' p q r hpq hqr := by
    have hq : q = p + 1 := by simpa using hpq.symm
    have hr : r = q + 1 := by simpa using hqr.symm
    by_cases h1 : m ≤ p
    · have h2 : m ≤ q := by omega
      have h3 : m ≤ r := by omega
      simp [h1, h2, h3]
    · simp [h1]

variable (F : CochainComplex M ℤ) {m : ℤ}

/-- For `m ≤ p`, the degree `p` term of `σ_{≥m} F` is `F^p`. -/
noncomputable def brutalXIso {p : ℤ} (h : m ≤ p) : (brutal F m).X p ≅ F.X p :=
  eqToIso (by simp [brutal, h])

/-- For `p < m`, the degree `p` term of `σ_{≥m} F` is zero. -/
lemma isZero_brutal_X {p : ℤ} (h : p < m) : IsZero ((brutal F m).X p) := by
  have : ¬ m ≤ p := by omega
  have e : (brutal F m).X p = 0 := by simp [brutal, this]
  rw [e]
  exact isZero_zero M

/-- The differential of `σ_{≥m} F` in degrees `≥ m`. -/
private lemma brutal_d_pos {p q : ℤ} (h1 : m ≤ p) (h2 : m ≤ q) :
    (brutal F m).d p q = (brutalXIso F h1).hom ≫ F.d p q ≫ (brutalXIso F h2).inv := by
  simp [brutal, brutalXIso, h1, h2]
  rfl

/-- The differential of `σ_{≥m} F` out of degrees `< m` vanishes. -/
private lemma brutal_d_neg {p q : ℤ} (h : p < m) : (brutal F m).d p q = 0 := by
  have : ¬ (m ≤ p ∧ m ≤ q) := fun h' => by omega
  simp [brutal, this]
  rfl

variable (m)

/-- The inclusion `σ_{≥m} F ⟶ F`. -/
private noncomputable def brutalι : brutal F m ⟶ F where
  f p := if h : m ≤ p then (brutalXIso F h).hom else 0
  comm' p q hpq := by
    have hq : q = p + 1 := by simpa using hpq.symm
    by_cases h1 : m ≤ p
    · have h2 : m ≤ q := by omega
      simp [h1, h2, brutal_d_pos F h1 h2]
    · have h3 : p < m := by omega
      simp [h1, brutal_d_neg F h3 (q := q)]

variable {m}

/-- The inclusion is the canonical identification in degrees `≥ m`. -/
private lemma brutalι_f_pos {p : ℤ} (h : m ≤ p) :
    (brutalι F m).f p = (brutalXIso F h).hom := by
  simp [brutalι, h]

/-- The inclusion is an isomorphism in degrees `≥ m`. -/
private lemma isIso_brutalι_f {p : ℤ} (h : m ≤ p) : IsIso ((brutalι F m).f p) := by
  rw [brutalι_f_pos F h]
  infer_instance

/-- For `m ≤ m'`, the inclusion `σ_{≥m'} F ⟶ σ_{≥m} F`. -/
noncomputable def brutalTr {m m' : ℤ} (h : m ≤ m') : brutal F m' ⟶ brutal F m where
  f p := if hp : m' ≤ p then (brutalXIso F hp).hom ≫ (brutalXIso F (h.trans hp)).inv else 0
  comm' p q hpq := by
    have hq : q = p + 1 := by simpa using hpq.symm
    by_cases h1 : m' ≤ p
    · have h2 : m' ≤ q := by omega
      simp [h1, h2, brutal_d_pos F h1 h2, brutal_d_pos F (h.trans h1) (h.trans h2)]
    · have h3 : p < m' := by omega
      simp [h1, brutal_d_neg F h3 (q := q)]

/-- The transition map is the canonical identification in degrees `≥ m'`. -/
lemma brutalTr_f_pos {m m' : ℤ} (h : m ≤ m') {p : ℤ} (hp : m' ≤ p) :
    (brutalTr F h).f p = (brutalXIso F hp).hom ≫ (brutalXIso F (h.trans hp)).inv := by
  simp [brutalTr, hp]

/-- Compatibility of the transition maps with the inclusions. -/
private lemma brutalTr_ι {m m' : ℤ} (h : m ≤ m') :
    brutalTr F h ≫ brutalι F m = brutalι F m' := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  by_cases hp : m' ≤ p
  · have e1 := brutalι_f_pos F hp
    have e2 := brutalι_f_pos F (h.trans hp)
    simp [brutalTr_f_pos F h hp, e1, e2]
  · have hp' : p < m' := by omega
    exact (isZero_brutal_X F hp').eq_of_src _ _

/-- The inclusion `σ_{≥m} F ⟶ F` is a monomorphism. -/
private lemma mono_brutalι : Mono (brutalι F m) := by
  refine HomologicalComplex.mono_of_mono_f _ fun p => ?_
  by_cases hp : m ≤ p
  · have := isIso_brutalι_f F hp
    infer_instance
  · exact (isZero_brutal_X F (by omega)).mono _

/-- The diagram `m ↦ σ_{≥m} F` indexed by `ℤᵒᵖ` (the transition maps are the inclusions). -/
noncomputable def brutalFunctor : ℤᵒᵖ ⥤ CochainComplex M ℤ where
  obj m := brutal F m.unop
  map {m m'} f := brutalTr F (leOfHom f.unop)
  map_id m := by
    have := mono_brutalι F (m := m.unop)
    rw [← cancel_mono (brutalι F m.unop), brutalTr_ι, Category.id_comp]
  map_comp {m m' m''} f g := by
    have := mono_brutalι F (m := m''.unop)
    rw [← cancel_mono (brutalι F m''.unop), Category.assoc, brutalTr_ι, brutalTr_ι, brutalTr_ι]

/-- `F` is the cocone over its brutal truncations. -/
noncomputable def brutalCocone : Cocone (brutalFunctor F) where
  pt := F
  ι :=
    { app := fun m => brutalι F m.unop
      naturality := fun m m' f => by
        simp only [brutalFunctor, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact brutalTr_ι F (leOfHom f.unop) }

/-- `F` is the colimit of its brutal truncations (the diagram is degreewise eventually
constant). -/
noncomputable def isColimit_brutalCocone : IsColimit (brutalCocone F) :=
  HomologicalComplex.isColimitOfEval _ _ (fun p => by
    have h : ((brutalFunctor F) ⋙ HomologicalComplex.eval M (ComplexShape.up ℤ) p
        ).IsEventuallyConstantFrom (Opposite.op p) := by
      intro j f
      show IsIso ((brutalTr F (leOfHom f.unop)).f p)
      rw [brutalTr_f_pos F _ le_rfl]
      infer_instance
    have : IsIso (((HomologicalComplex.eval M (ComplexShape.up ℤ) p).mapCocone
        (brutalCocone F)).ι.app (Opposite.op p)) := by
      show IsIso ((brutalι F p).f p)
      exact isIso_brutalι_f F le_rfl
    exact h.isColimitOfIsIso _)

end Brutal

section BrutalSES

variable {M : Type*} [Category M] [Abelian M] (F : CochainComplex M ℤ) (m : ℤ)

/-- The projection `σ_{≥m} F ⟶ F^m` (placed in degree `m`). -/
private noncomputable def brutalProj :
    brutal F m ⟶ (HomologicalComplex.single M (ComplexShape.up ℤ) m).obj (F.X m) where
  f p := if h : p = m then (brutalXIso F (le_of_eq h.symm)).hom ≫ eqToHom (congrArg F.X h) ≫
    (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) m (F.X m) p h).inv else 0
  comm' p q hpq := by
    have hq : q = p + 1 := by simpa using hpq.symm
    by_cases hq' : q = m
    · have hp : p < m := by omega
      simp [brutal_d_neg F hp (q := q)]
    · simp [hq']

/-- The projection in degree `m`. -/
private lemma brutalProj_f_self : (brutalProj F m).f m = (brutalXIso F le_rfl).hom ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m (F.X m)).inv := by
  simp [brutalProj, HomologicalComplex.singleObjXSelf]

/-- The projection vanishes in the other degrees. -/
private lemma brutalProj_f_ne {p : ℤ} (h : p ≠ m) : (brutalProj F m).f p = 0 := by
  simp [brutalProj, h]

/-- The projection kills the image of `σ_{≥m+1} F`. -/
private lemma brutalTr_proj : brutalTr F (show m ≤ m + 1 by omega) ≫ brutalProj F m = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  by_cases hp : p = m
  · subst hp
    exact (isZero_brutal_X F (show p < p + 1 by omega)).eq_of_src _ _
  · simp [brutalProj_f_ne F m hp]

/-- The short complex `0 → σ_{≥m+1} F → σ_{≥m} F → F^m[-m] → 0`. -/
noncomputable def brutalSES : ShortComplex (CochainComplex M ℤ) :=
  ShortComplex.mk (brutalTr F (show m ≤ m + 1 by omega)) (brutalProj F m) (brutalTr_proj F m)

/-- The sequence `0 → σ_{≥m+1} F → σ_{≥m} F → F^m[-m] → 0` is short exact. -/
lemma brutalSES_shortExact : (brutalSES F m).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun p => ?_)
  by_cases h1 : p < m
  · have hz2 := isZero_brutal_X F h1
    have hz1 := isZero_brutal_X F (show p < m + 1 by omega)
    have hz3 := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) m (F.X m) p
      (by omega)
    exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hz2)
      (hz1.mono _) (hz3.epi _)
  by_cases h2 : p = m
  · subst h2
    have hz1 := isZero_brutal_X F (show p < p + 1 by omega)
    have hg : IsIso ((brutalProj F p).f p) := by
      rw [brutalProj_f_self]
      infer_instance
    refine ShortComplex.ShortExact.mk' ?_ (hz1.mono _) ?_
    · refine (ShortComplex.exact_iff_mono _ (hz1.eq_of_src _ _)).2 ?_
      exact (inferInstance : Mono ((brutalProj F p).f p))
    · exact (inferInstance : Epi ((brutalProj F p).f p))
  · have h3 : m + 1 ≤ p := by omega
    have hz3 := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) m (F.X m) p h2
    have hf : IsIso ((brutalTr F (show m ≤ m + 1 by omega)).f p) := by
      rw [brutalTr_f_pos F _ h3]
      infer_instance
    refine ShortComplex.ShortExact.mk' ?_ (inferInstance : Mono ((brutalTr F _).f p))
      (hz3.epi _)
    exact (ShortComplex.exact_iff_epi _ (hz3.eq_of_tgt _ _)).2
      (inferInstance : Epi ((brutalTr F _).f p))

end BrutalSES

section ColimAcyclic

variable {C : Type*} [Category C] [Abelian C] {J : Type*} [SmallCategory J]
  [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- Evaluation functors jointly reflect isomorphisms. -/
private lemma jointlyReflect_evaluation' {J C : Type*} [Category J] [Category C] :
    JointlyReflectIsomorphisms (fun j : J => (evaluation J C).obj j) :=
  ⟨fun f h => by
    have : ∀ j, IsIso (f.app j) := fun j => h j
    exact NatIso.isIso_of_isIso_app f⟩

/-- A colimit of acyclic complexes (over a shape with exact colimits) is acyclic. -/
lemma acyclic_of_isColimit {D : J ⥤ CochainComplex C ℤ} (hD : ∀ j, (D.obj j).Acyclic)
    {c : Cocone D} (hc : IsColimit c) : c.pt.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  let f : D ⋙ HomologicalComplex.eval C _ (n - 1) ⟶ D ⋙ HomologicalComplex.eval C _ n :=
    { app := fun j => (D.obj j).d (n - 1) n
      naturality := fun j j' φ => (D.map φ).comm (n - 1) n }
  let g : D ⋙ HomologicalComplex.eval C _ n ⟶ D ⋙ HomologicalComplex.eval C _ (n + 1) :=
    { app := fun j => (D.obj j).d n (n + 1)
      naturality := fun j j' φ => (D.map φ).comm n (n + 1) }
  let S : ShortComplex (J ⥤ C) :=
    ShortComplex.mk f g (NatTrans.ext (funext fun j => (D.obj j).d_comp_d (n - 1) n (n + 1)))
  have hS : S.Exact := by
    rw [(jointlyReflect_evaluation' (J := J) (C := C)).exact_iff S]
    intro j
    exact (HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)).1 (hD j n)
  have hS' := hS.map (colim : (J ⥤ C) ⥤ C)
  let e : ∀ k : ℤ, colimit (D ⋙ HomologicalComplex.eval C _ k) ≅ c.pt.X k := fun k =>
    (colimit.isColimit _).coconePointUniqueUpToIso
      (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) k) hc)
  have he : ∀ (k k' : ℤ) (j : J), colimit.ι (D ⋙ HomologicalComplex.eval C _ k) j ≫
      (e k).hom = (c.ι.app j).f k := fun k k' j =>
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ j
  have iso : S.map (colim : (J ⥤ C) ⥤ C) ≅ c.pt.sc' (n - 1) n (n + 1) :=
    ShortComplex.isoMk (e (n - 1)) (e n) (e (n + 1))
      (by
        refine colimit.hom_ext (fun j => ?_)
        show colimit.ι _ j ≫ (e (n - 1)).hom ≫ c.pt.d (n - 1) n =
          colimit.ι _ j ≫ colimMap f ≫ (e n).hom
        rw [← Category.assoc, he (n - 1) n j, ι_colimMap_assoc, he n (n + 1) j]
        exact (c.ι.app j).comm _ _)
      (by
        refine colimit.hom_ext (fun j => ?_)
        show colimit.ι _ j ≫ (e n).hom ≫ c.pt.d n (n + 1) =
          colimit.ι _ j ≫ colimMap g ≫ (e (n + 1)).hom
        rw [← Category.assoc, he n (n + 1) j, ι_colimMap_assoc, he (n + 1) (n + 2) j]
        exact (c.ι.app j).comm _ _)
  exact ShortComplex.exact_of_iso iso hS'

end ColimAcyclic

end Cohesive
