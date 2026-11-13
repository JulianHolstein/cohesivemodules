import Cohesivemodules.Sheaf.Globalize.LocalFree

set_option linter.style.header false

/-!
# S10 (part 3): S10.a–d, local null-homotopies and lifts

Blueprint item S10 (§3), sub-lemmas S10.a–d on a site. Split from `Sheaf/Globalize.lean` for
size only (CLAUDE.md: "New work goes in small new files"); no mathematical change.

* S10.a `nullHomotopic_locally`, S10.b `lift_locally`, S10.c `split_locally`,
  `isFinFreeSummand_locally_of_acyclic`, S10.d `homology_finGen_locally`.
* `overOverEquiv`: the nested over-site `Over Z` of `Over X` is `Over Z.left`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}}

/-- `homRestr` is compatible with subtraction. -/
private lemma homRestr_sub {X Y : C} (f : Y ⟶ X) {M N : Mod R} (φ ψ : M.over X ⟶ N.over X) :
    homRestr f (φ - ψ) = homRestr f φ - homRestr f ψ := by
  rw [eq_sub_iff_add_eq, ← homRestr_add, sub_add_cancel]

/-- `homRestr` of zero is zero. -/
private lemma homRestr_zero {X Y : C} (f : Y ⟶ X) {M N : Mod R} :
    homRestr f (0 : M.over X ⟶ N.over X) = 0 := rfl

/-- `homRestr` along a composite. -/
private lemma homRestr_homRestr {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) {M N : Mod R}
    (φ : M.over X ⟶ N.over X) : homRestr g (homRestr f φ) = homRestr (g ≫ f) φ :=
  (homRestr_comp f g φ).symm

/-- Morphisms into `A|V` killed by `f|V` factor through `(ker f)|V`. -/
private lemma factor_kernel {A B : Mod R} (f : A ⟶ B) (V : C) {T : Mod (R.over V)}
    (w : T ⟶ A.over V)
    (hw : w ≫ f.over V = 0) :
    ∃ w' : T ⟶ (kernel f).over V, w' ≫ (kernel.ι f).over V = w := by
  let F := SheafOfModules.overFunctor.{0} R V
  refine ⟨kernel.lift (f.over V) w hw ≫ inv (kernelComparison f F), ?_⟩
  have := kernelComparison_comp_ι f F
  change _ ≫ F.map (kernel.ι f) = _
  rw [← this]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  exact kernel.lift_ι _ _ _

/-- Local lifting of a map out of a summand of a finite free module along an epimorphism. -/
private lemma lift_summand {M N E : Mod R} (π : M ⟶ N) [Epi π] (hE : IsFinFreeSummand E) (V : C)
    (w : E.over V ⟶ N.over V) :
    ∃ S ∈ J V, ∀ ⦃W : C⦄ (g : W ⟶ V), S g →
      ∃ new : E.over W ⟶ M.over W, new ≫ π.over W = homRestr g w := by
  obtain ⟨m, i, p, hip⟩ := hE
  obtain ⟨S, hS, hq⟩ := lift_free π V m (p.over V ≫ w)
  refine ⟨S, hS, fun W g hg => ?_⟩
  obtain ⟨q, hq⟩ := hq g hg
  refine ⟨i.over W ≫ q, ?_⟩
  rw [Category.assoc, hq, homRestr_mor_comp, homRestr_over, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Exactness at `j` as exactness of a short complex, with free indices. -/
private lemma exact_sc' {C' : CochainComplex (Mod R) ℤ} (i j k : ℤ) (hij : i + 1 = j)
    (hjk : j + 1 = k)
    (hC : C'.ExactAt j) :
    (ShortComplex.mk (C'.d i j) (C'.d j k) (C'.d_comp_d _ _ _)).Exact :=
  (C'.exactAt_iff' i j k (by simp; omega) (by simp; omega)).1 hC

/-- A family of degree `-1` components over `V`. -/
private abbrev HFam (E A : CochainComplex (Mod R) ℤ) (V : C) :=
  ∀ p q : ℤ, p + (-1) = q → ((E.X p).over V ⟶ (A.X q).over V)

/-- The homotopy relation `u = d h + h d` in degrees `≥ i`. -/
private def PH {E A : CochainComplex (Mod R) ℤ} (u : E ⟶ A) (V : C) (H : HFam E A V) (i : ℤ) :
    Prop :=
  ∀ p q r : ℤ, i ≤ p → ∀ (hq : p + (-1) = q) (hr : p + 1 = r),
    (u.f p).over V = H p q hq ≫ (A.d q p).over V + (E.d p r).over V ≫ H r p (by omega)

/-- Restriction of a family of components along `g : W ⟶ V`. -/
private def HFam.restrict {E A : CochainComplex (Mod R) ℤ} {V W : C} (g : W ⟶ V) (H : HFam E A V) :
    HFam E A W := fun p q hpq => homRestr g (H p q hpq)

/-- `PH` is stable under restriction. -/
private lemma PH.restrict {E A : CochainComplex (Mod R) ℤ} {u : E ⟶ A} {V W : C} {H : HFam E A V}
    {i : ℤ} (h : PH u V H i) (g : W ⟶ V) : PH u W (H.restrict g) i := by
  intro p q r hp hq hr
  have := congrArg (homRestr g) (h p q r hp hq hr)
  rw [homRestr_add, homRestr_mor_comp, homRestr_mor_comp, homRestr_over, homRestr_over,
    homRestr_over] at this
  exact this

/-- The sieve of arrows over which a partial null-homotopy in degrees `≥ i` exists. -/
private def nhSieve {E A : CochainComplex (Mod R) ℤ} (u : E ⟶ A) (X : C) (i : ℤ) : Sieve X where
  arrows V _ := ∃ H : HFam E A V, PH u V H i
  downward_closed := fun ⟨H, hH⟩ g => ⟨H.restrict g, hH.restrict g⟩

/-- One step of the construction of the local null-homotopy. -/
private lemma nh_step {E A : CochainComplex (Mod R) ℤ} (u : E ⟶ A) (i : ℤ) (hA : A.ExactAt i)
    (hE : IsFinFreeSummand (E.X i)) (X : C) (h : nhSieve u X (i + 1) ∈ J X) :
    nhSieve u X i ∈ J X := by
  refine J.transitive h _ (fun V g hg => ?_)
  obtain ⟨H, hH⟩ := hg
  let w : (E.X i).over V ⟶ (A.X i).over V :=
    (u.f i).over V - (E.d i (i + 1)).over V ≫ H (i + 1) i (by omega)
  have hw : w ≫ (A.d i (i + 1)).over V = 0 := by
    have e1 : (u.f i).over V ≫ (A.d i (i + 1)).over V =
        (E.d i (i + 1)).over V ≫ (u.f (i + 1)).over V := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, u.comm]
    have e2 := hH (i + 1) i (i + 1 + 1) le_rfl (by omega) (by omega)
    have e3 : (E.d i (i + 1)).over V ≫ (E.d (i + 1) (i + 1 + 1)).over V = 0 := by
      rw [← CategoryTheory.Functor.map_comp, E.d_comp_d, CategoryTheory.Functor.map_zero]
    simp only [w, Preadditive.sub_comp, e1, e2, Preadditive.comp_add, ← Category.assoc, e3,
      zero_comp, add_zero, sub_self]
  obtain ⟨w', hw'⟩ := factor_kernel (A.d i (i + 1)) V w hw
  have hepi : Epi (kernel.lift (A.d i (i + 1)) (A.d (i + -1) i) (A.d_comp_d _ _ _)) :=
    (ShortComplex.exact_iff_epi_kernel_lift (ShortComplex.mk (A.d (i + -1) i) (A.d i (i + 1))
      (A.d_comp_d _ _ _))).1 (exact_sc' (i + -1) i (i + 1) (by omega) rfl hA)
  obtain ⟨S, hS, hnew⟩ := lift_summand
    (kernel.lift (A.d i (i + 1)) (A.d (i + -1) i) (A.d_comp_d _ _ _)) hE V w'
  refine J.superset_covering (fun W g' hg' => ?_) hS
  obtain ⟨new, hnew⟩ := hnew g' hg'
  let H' : HFam E A W := fun p q hpq =>
    if hp : p = i then eqToHom (by rw [hp]) ≫ new ≫ eqToHom (by rw [show q = i + -1 by omega])
    else homRestr g' (H p q hpq)
  have hH'1 : ∀ p q hpq, p ≠ i → H' p q hpq = homRestr g' (H p q hpq) :=
    fun p q hpq hne => dite_eq_right hne
  have hH'2 : H' i (i + -1) rfl = new := by
    change dite _ _ _ = _
    rw [dite_eq_left rfl]
    simp
  refine ⟨H', fun p q r hp hq hr => ?_⟩
  rcases eq_or_lt_of_le hp with rfl | hlt
  · subst hq hr
    rw [hH'2, hH'1 (i + 1) i _ (by omega)]
    have k1 : (A.d (i + -1) i).over W = (kernel.lift (A.d i (i + 1)) (A.d (i + -1) i)
        (A.d_comp_d _ _ _)).over W ≫ (kernel.ι (A.d i (i + 1))).over W := by
      rw [← CategoryTheory.Functor.map_comp, kernel.lift_ι]
    have k2 : new ≫ (A.d (i + -1) i).over W = homRestr g' w := by
      rw [k1, ← Category.assoc, hnew, ← hw', homRestr_mor_comp, homRestr_over]
    rw [k2]
    simp only [w, homRestr_sub, homRestr_mor_comp, homRestr_over]
    rw [sub_add_cancel]
  · have := (hH.restrict g') p q r (by omega) hq hr
    rw [hH'1 p q hq (by omega), hH'1 r p _ (by omega)]
    exact this

open CochainComplex.HomComplex in
/-- A partial homotopy in all degrees gives a null-homotopy. -/
private lemma homotopy_of_PH {E A : CochainComplex (Mod R) ℤ} (a : ℤ) [E.IsStrictlyGE a] (u : E ⟶ A)
    (V : C) (H : HFam E A V) (hH : PH u V H a) :
    Nonempty (Homotopy ((overC V).map u) 0) := by
  have hall : ∀ p q r : ℤ, ∀ (hq : p + (-1) = q) (hr : p + 1 = r),
      (u.f p).over V = H p q hq ≫ (A.d q p).over V + (E.d p r).over V ≫ H r p (by omega) := by
    intro p q r hq hr
    by_cases hp : a ≤ p
    · exact hH p q r hp hq hr
    · have hz : IsZero ((E.X p).over V) :=
        Functor.map_isZero _ (E.isZero_of_isStrictlyGE a p (by omega))
      exact hz.eq_of_src _ _
  let z : Cochain ((overC V).obj E) ((overC V).obj A) (-1) :=
    Cochain.mk (fun p q hpq => H p q hpq)
  refine ⟨(Cochain.equivHomotopy _ _).symm ⟨z, ?_⟩⟩
  refine Cochain.ext₀ _ _ fun p => ?_
  rw [Cochain.add_v, δ_v (-1) 0 (by omega) z p p (add_zero p) (p + -1) (p + 1) rfl rfl,
    Cochain.ofHom_v, Cochain.ofHom_zero, Cochain.zero_v]
  simp only [Int.negOnePow_zero, one_smul, add_zero]
  exact hall p (p + -1) (p + 1) rfl rfl

/-- Partial null-homotopies exist locally in every degree. -/
private lemma nh_down {E A : CochainComplex (Mod R) ℤ} (b : ℤ) [E.IsStrictlyLE b]
    (hfree : ∀ i, IsFinFreeSummand (E.X i)) (hA : A.Acyclic) (u : E ⟶ A) (X : C) :
    ∀ i, nhSieve u X i ∈ J X := by
  have key : ∀ k : ℕ, ∀ i, b < i + k → nhSieve u X i ∈ J X := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : nhSieve u X i = ⊤ := by
        ext V g
        refine ⟨fun _ => trivial, fun _ => ⟨fun _ _ _ => 0, fun p q r hp hq hr => ?_⟩⟩
        have hz : IsZero ((E.X p).over V) :=
          Functor.map_isZero _ (E.isZero_of_isStrictlyLE b p (by push_cast at hi; omega))
        exact hz.eq_of_src _ _
      rw [this]
      exact J.top_mem X
    | succ k ih =>
      intro i hi
      exact nh_step u i (hA i) (hfree i) X (ih (i + 1) (by push_cast at hi; omega))
  intro i
  exact key (b + 1 - i).toNat i (by omega)

/-- Proof of `nullHomotopic_locally`. -/
private theorem nullHomotopic_fill {E A : CochainComplex (Mod R) ℤ} (hE : IsStrictlyPerfect E)
    (hA : A.Acyclic) (u : E ⟶ A) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ Nonempty (Homotopy ((overC Y).map u) 0)) ∈ J X := by
  obtain ⟨⟨a, b, ha, hb⟩, hfree⟩ := hE
  refine J.superset_covering (fun V g hg => Sieve.le_generate _ V g ?_)
    (nh_down (J := J) b hfree hA u X a)
  obtain ⟨H, hH⟩ := hg
  exact homotopy_of_PH a u V H hH

/-- Proof of `lift_locally`. -/
lemma lift_fill {E K L : CochainComplex (Mod R) ℤ} (hE : IsStrictlyPerfect E)
    (s : L ⟶ K) [QuasiIso s] (g : E ⟶ K) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ ∃ g' : (overC Y).obj E ⟶ (overC Y).obj L,
      Nonempty (Homotopy (g' ≫ (overC Y).map s) ((overC Y).map g))) ∈ J X := by
  have hacyc := (quasiIso_iff_acyclic_mappingCone s).1 inferInstance
  refine J.superset_covering ((Sieve.generate_le_iff _ _).2 fun Y f hf => ?_)
    (nullHomotopic_fill hE hacyc (g ≫ CochainComplex.mappingCone.inr s) X)
  refine Sieve.le_generate _ Y f ?_
  obtain ⟨ho⟩ := hf
  let G := SheafOfModules.overFunctor.{0} R Y
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished ((overC Y).map s)
  have h0 : (HomotopyCategory.quotient _ _).map ((overC Y).map (g ≫
      CochainComplex.mappingCone.inr s)) = 0 := by
    rw [HomotopyCategory.eq_of_homotopy _ _ ho]
    simp
  have hf : (HomotopyCategory.quotient _ _).map ((overC Y).map g) ≫
      (CochainComplex.mappingCone.triangleh ((overC Y).map s)).mor₂ = 0 := by
    have e := CochainComplex.mappingCone.map_inr s G
    have e2 : (HomotopyCategory.quotient _ _).map ((overC Y).map g) ≫
        (CochainComplex.mappingCone.triangleh ((overC Y).map s)).mor₂ =
        (HomotopyCategory.quotient _ _).map ((overC Y).map (g ≫
          CochainComplex.mappingCone.inr s)) ≫
        (HomotopyCategory.quotient _ _).map
          (CochainComplex.mappingCone.mapHomologicalComplexIso s G).hom := by
      change (HomotopyCategory.quotient _ _).map ((overC Y).map g) ≫
        (HomotopyCategory.quotient _ _).map (CochainComplex.mappingCone.inr ((overC Y).map s)) = _
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp (overC Y), Category.assoc]
      exact congrArg _ (by rw [← e])
    rw [e2, h0]
    exact zero_comp
  obtain ⟨gh, hgh⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ hT _ hf
  obtain ⟨g', rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective gh
  refine ⟨g', ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  exact (CategoryTheory.Functor.map_comp _ _ _).trans hgh.symm


/-- Restriction along `V ⟶ U` of a morphism of over-modules preserves epimorphisms. -/
lemma epi_homRestr {M N : Mod R} {U V : C} (φ : M.over U ⟶ N.over U) [Epi φ] (h : V ⟶ U) :
    Epi (homRestr h φ) := by
  have h1 : Presheaf.IsLocallySurjective (J.over U)
      ((PresheafOfModules.toPresheaf (R.over U).obj).map φ.val) :=
    ⟨fun s => imSieve_mem_of_epi φ s⟩
  have h2 := Presheaf.isLocallySurjective_whisker (J.over V) (J.over U) (Over.map h)
    ((PresheafOfModules.toPresheaf (R.over U).obj).map φ.val)
  have h3 : Epi ((SheafOfModules.toSheaf (R.over V)).map (homRestr h φ)) := by
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over V)).map (homRestr h φ)) :=
      h2
    infer_instance
  exact (SheafOfModules.toSheaf (R.over V)).epi_of_epi_map h3

/-- **S10.a. Local null-homotopy.** A chain map `u : E ⟶ A` from a strictly perfect complex to
an acyclic complex is locally null-homotopic: for every object `X`, the objects `Y ⟶ X` over
which `u|Y` is null-homotopic generate a covering sieve. Proof: degree by degree from the top of
the bounded `E`, finitely many sections to lift each time (terms are summands of finite free
modules), by local surjectivity of epimorphisms. -/
theorem nullHomotopic_locally {E A : CochainComplex (Mod R) ℤ} (hE : IsStrictlyPerfect E)
    (hA : A.Acyclic) (u : E ⟶ A) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ Nonempty (Homotopy ((overC Y).map u) 0)) ∈ J X := by
  exact nullHomotopic_fill hE hA u X

/-- **S10.b. Local lifting.** For `E` strictly perfect and a quasi-isomorphism `s : L ⟶ K`,
every chain map `g : E ⟶ K` lifts locally through `s` up to homotopy (S10.a applied to the
composite `E ⟶ K ⟶ cone s`, with the cone acyclic; exactness of `Hom(E, -)` on the triangle of
`s` in the homotopy category). -/
theorem lift_locally {E K L : CochainComplex (Mod R) ℤ} (hE : IsStrictlyPerfect E)
    (s : L ⟶ K) [QuasiIso s] (g : E ⟶ K) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ ∃ g' : (overC Y).obj E ⟶ (overC Y).obj L,
      Nonempty (Homotopy (g' ≫ (overC Y).map s) ((overC Y).map g))) ∈ J X := by
  exact lift_fill hE s g X

/-- **S10.c. Local splitting.** An epimorphism `π : M ⟶ N` onto a direct summand of a finite
free module splits locally (lift the finitely many generators locally). -/
theorem split_locally {M N : Mod R} (π : M ⟶ N) [Epi π] (hN : IsFinFreeSummand N) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ ∃ σ : N.over Y ⟶ M.over Y,
      σ ≫ (SheafOfModules.overFunctor.{0} R Y).map π = 𝟙 _) ∈ J X := by
  obtain ⟨S, hS, hσ⟩ := split_FS π X (FS.of_global hN X)
  exact J.superset_covering (fun Y g hg => Sieve.le_generate _ Y g (hσ g hg)) hS

/-- **S10.c.** In a bounded acyclic complex `C'` concentrated in degrees `[m, n]` whose terms are
direct summands of finite free modules except possibly `C'^{m+1}`, that term is locally one too:
splitting from the top, the cycle sheaves above `m + 1` are locally such summands, and
`C'^{m+1} ≅ C'^m ⊞ Z^{m+2}` locally. -/
theorem isFinFreeSummand_locally_of_acyclic {C' : CochainComplex (Mod R) ℤ} (m n : ℤ)
    [C'.IsStrictlyGE m] [C'.IsStrictlyLE n] (hC : C'.Acyclic)
    (hfree : ∀ i, i ≠ m + 1 → IsFinFreeSummand (C'.X i)) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ IsFinFreeSummand ((C'.X (m + 1)).over Y)) ∈ J X := by
  exact isFin_acyc m n hC hfree X

/-- **S10.d.** For `P` strictly perfect and exact in all degrees `≥ k`, the homology sheaf
`H^{k-1}(P)` is locally a quotient of a finite free module (the cycles `Z^{k-1}` are locally
summands of finite free modules by S10.c, and `H^{k-1}` is their quotient). -/
theorem homology_finGen_locally {P : CochainComplex (Mod R) ℤ} (hP : IsStrictlyPerfect P)
    (k : ℤ) (hk : ∀ i, k ≤ i → P.ExactAt i) (X : C) :
    Sieve.generate (fun Y (_ : Y ⟶ X) ↦ ∃ (m : ℕ)
      (π : SheafOfModules.free (R := R.over Y) (Fin m) ⟶ (P.homology (k - 1)).over Y),
      Epi π) ∈ J X := by
  exact homology_fg hP k hk X

/-- **S10 (transfer).** Nested over-sites: modules on `(Over X).over Z` are modules on
`Over Z.left` (Mathlib's `Over.iteratedSliceEquiv`). -/
def overOverEquiv (X : C) (Z : Over X) :
    Mod ((R.over X).over Z) ≌ Mod (R.over Z.left) :=
  (SheafOfModules.pushforwardPushforwardEquivalence.{0} (Over.iteratedSliceEquiv Z)
    (S := (R.over X).over Z) (R := R.over Z.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)).symm

/-- **S10 (transfer).** Under `overOverEquiv`, restricting to `X` and then to `Z` is restricting
to `Z.left`. -/
def overOverEquivObjIso (X : C) (Z : Over X) (M : Mod R) :
    (overOverEquiv X Z).functor.obj ((M.over X).over Z) ≅ M.over Z.left :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl))

/-- `overOverEquiv` maps the unit to the unit. -/
def overOverUnit (X : C) (Z : Over X) :
    SheafOfModules.unit (R.over Z.left) ≅
      (overOverEquiv (R := R) X Z).functor.obj (SheafOfModules.unit ((R.over X).over Z)) :=
  Iso.refl _

/-- The inverse of `overOverEquiv` maps the unit to the unit. -/
private def overOverUnit' (X : C) (Z : Over X) :
    SheafOfModules.unit ((R.over X).over Z) ≅
      (overOverEquiv (R := R) X Z).inverse.obj (SheafOfModules.unit (R.over Z.left)) :=
  Iso.refl _

/-- **S10 (transfer).** `overOverEquiv` preserves and reflects direct summands of finite free
modules (it maps the unit to the unit). -/
theorem isFinFreeSummand_overOverEquiv_iff (X : C) (Z : Over X) (M : Mod ((R.over X).over Z)) :
    IsFinFreeSummand ((overOverEquiv X Z).functor.obj M) ↔ IsFinFreeSummand M := by
  constructor
  · rintro ⟨m, i, p, hip⟩
    let e := overOverEquiv (R := R) X Z
    let η := SheafOfModules.mapFreeIso e.inverse (Fin m) (overOverUnit' (R := R) X Z)
    refine ⟨m, e.unit.app M ≫ e.inverse.map i ≫ η.inv, η.hom ≫ e.inverse.map p ≫
      e.unitInv.app M, ?_⟩
    rw [Category.assoc, Category.assoc, ← Category.assoc η.inv, η.inv_hom_id, Category.id_comp,
      ← Category.assoc (e.inverse.map i), ← CategoryTheory.Functor.map_comp, hip,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    rfl
  · rintro ⟨m, i, p, hip⟩
    let e := overOverEquiv (R := R) X Z
    let η := SheafOfModules.mapFreeIso e.functor (Fin m) (overOverUnit (R := R) X Z)
    refine ⟨m, e.functor.map i ≫ η.inv, η.hom ≫ e.functor.map p, ?_⟩
    rw [Category.assoc, ← Category.assoc η.inv, η.inv_hom_id, Category.id_comp,
      ← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]

end Site

end Cohesive
