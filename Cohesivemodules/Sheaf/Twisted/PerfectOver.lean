import Cohesivemodules.Sheaf.Twisted.PerfectDef
import Cohesivemodules.Sheaf.RestrOver
import Cohesivemodules.Sheaf.RestrictionBasic
import Cohesivemodules.Sheaf.Perfect
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

set_option linter.style.header false

/-!
# Z3.j: perfect complexes on an over-site

Blueprint item Z3.j (`blueprint/blueprint-tw.md` §3 C.6 (a)–(d), (h)). For a sheaf of rings `R`
on `X` and an open `V`, the over-site versions of S9.c and S9.d for `IsPerfectOver`:
* restriction `restrOver` preserves summands of finite free modules and strictly perfect
  complexes (and quasi-isomorphisms, by instance search: it is exact);
* `IsPerfectOver` is invariant under quasi-isomorphism;
* `IsPerfectOverIn K a b` (local models in `[a, b]`): stable under restriction, local, and the
  homology of `K` vanishes outside `[a, b]`;
* sanity: `IsPerfectOver (K|⊤) ↔ IsPerfect K`.

Restrictions compose definitionally (`restrOver h' ∘ restrOver h = restrOver (h'.trans h)`,
`restrOver (le_refl V) = 𝟭`, also on complexes), which the proofs use freely.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

universe w v u

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

/-! ## (a) Restriction -/

/-- Z3.j (a): restriction between over-sites preserves quasi-isomorphisms (it is exact; found by
instance search, as for `restr`). -/
example {V W : Opens X} (h : W ≤ V) {K L : CochainComplex (Mod (R.over V)) ℤ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (((restrOver R h).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  inferInstance

/-- Restriction between over-sites of a free module is free on the same index type. -/
private def restrOverFreeIso {V W : Opens X} (h : W ≤ V) (I : Type) :
    (restrOver R h).obj (SheafOfModules.free I) ≅ SheafOfModules.free (R := R.over W) I :=
  (SheafOfModules.mapFreeIso (restrOver R h) I (Iso.refl _)).symm

/-- **Z3.j (a).** blueprint-tw C.6, as S5.a. The restriction to `W ≤ V` of a direct summand of a
finite free `R.over V`-module is a direct summand of a finite free `R.over W`-module. -/
theorem IsFinFreeSummand.restrOver {V W : Opens X} (h : W ≤ V) {M : Mod (R.over V)}
    (hM : IsFinFreeSummand M) : IsFinFreeSummand ((restrOver R h).obj M) := by
  obtain ⟨m, i, p, hip⟩ := hM
  refine ⟨m, (Cohesive.restrOver R h).map i ≫ (restrOverFreeIso h (Fin m)).hom,
    (restrOverFreeIso h (Fin m)).inv ≫ (Cohesive.restrOver R h).map p, ?_⟩
  rw [Category.assoc, ← Category.assoc (restrOverFreeIso h (Fin m)).hom,
    Iso.hom_inv_id, Category.id_comp, ← Functor.map_comp, hip,
    CategoryTheory.Functor.map_id]

/-- **Z3.j (a).** The restriction of a complex strictly zero below `a` is strictly zero below `a`.
-/
theorem isStrictlyGE_restrOver {V W : Opens X} (h : W ≤ V) (P : CochainComplex (Mod (R.over V)) ℤ)
    (a : ℤ) [P.IsStrictlyGE a] : CochainComplex.IsStrictlyGE
      (((restrOver R h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a :=
  (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
    (restrOver R h).map_isZero (CochainComplex.isZero_of_isStrictlyGE P a i hi)

/-- **Z3.j (a).** The restriction of a complex strictly zero above `b` is strictly zero above `b`.
-/
theorem isStrictlyLE_restrOver {V W : Opens X} (h : W ≤ V) (P : CochainComplex (Mod (R.over V)) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] : CochainComplex.IsStrictlyLE
      (((restrOver R h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) b :=
  (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
    (restrOver R h).map_isZero (CochainComplex.isZero_of_isStrictlyLE P b i hi)

/-- **Z3.j (a).** The restriction of a strictly perfect complex on `Over V` to `Over W` is strictly
perfect. -/
theorem IsStrictlyPerfect.restrOver {V W : Opens X} (h : W ≤ V)
    {P : CochainComplex (Mod (R.over V)) ℤ} (hP : IsStrictlyPerfect P) :
    IsStrictlyPerfect (((restrOver R h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  obtain ⟨⟨a, b, hGE, hLE⟩, hX⟩ := hP
  exact ⟨⟨a, b, isStrictlyGE_restrOver h P a, isStrictlyLE_restrOver h P b⟩,
    fun n => (hX n).restrOver h⟩

/-! ## (b) Invariance under quasi-isomorphism -/

/-- Pullback of quasi-isomorphisms (roofs), through the derived category. -/
private lemma exists_pullback_quasiIso' {C : Type u} [Category.{v} C] [Abelian C]
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

/-- **Z3.j (b).** As S9.c. The target of a quasi-isomorphism out of a perfect complex on `Over V`
is perfect (compose the local roofs with `f|W`). -/
theorem IsPerfectOver.of_quasiIso_left {V : Opens X} {K K' : CochainComplex (Mod (R.over V)) ℤ}
    (f : K ⟶ K') [QuasiIso f] (hK : IsPerfectOver K) : IsPerfectOver K' := by
  intro x hx
  obtain ⟨W, hW, hxW, L, P, g, h, hg, hh, hP⟩ := hK x hx
  have : QuasiIso (((restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    inferInstance
  exact ⟨W, hW, hxW, L, P, g ≫ ((restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).map f,
    h, inferInstance, hh, hP⟩

/-- **Z3.j (b).** As S9.c. The source of a quasi-isomorphism into a perfect complex on `Over V` is
perfect (pull the local roofs back along `f|W` through `D(R|W)`). -/
theorem IsPerfectOver.of_quasiIso_right {V : Opens X} {K K' : CochainComplex (Mod (R.over V)) ℤ}
    (f : K ⟶ K') [QuasiIso f] (hK' : IsPerfectOver K') : IsPerfectOver K := by
  intro x hx
  obtain ⟨W, hW, hxW, L, P, s, g, hs, hg, hP⟩ := hK' x hx
  let _ : HasDerivedCategory (Mod (R.over W)) := HasDerivedCategory.standard _
  have : QuasiIso (((restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    inferInstance
  have := hs
  have := hg
  obtain ⟨M, t, u, ht, hu⟩ := exists_pullback_quasiIso'
    (((restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).map f) s
  have := hu
  exact ⟨W, hW, hxW, M, P, t, u ≫ g, ht, inferInstance, hP⟩

/-! ## (c) Local models in a fixed degree range -/

/-- **Z3.j (c).** As S9.d (`IsPerfectIn`). `K` on `Over V` is perfect with all local strictly
perfect models concentrated in degrees `[a, b]`. -/
def IsPerfectOverIn {V : Opens X} (K : CochainComplex (Mod (R.over V)) ℤ) (a b : ℤ) : Prop :=
  ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧
    ∃ (L P : CochainComplex (Mod (R.over W)) ℤ)
      (f : L ⟶ ((restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) (g : L ⟶ P),
      QuasiIso f ∧ QuasiIso g ∧ IsStrictlyPerfect P ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b

/-- Z3.j (c): local models in `[a, b]` are local models. -/
theorem IsPerfectOverIn.isPerfectOver {V : Opens X} {K : CochainComplex (Mod (R.over V)) ℤ}
    {a b : ℤ} (hK : IsPerfectOverIn K a b) : IsPerfectOver K := by
  intro x hx
  obtain ⟨W, hW, hxW, L, P, f, g, hf, hg, hP, -, -⟩ := hK x hx
  exact ⟨W, hW, hxW, L, P, f, g, hf, hg, hP⟩

/-- **Z3.j (c).** A single roof `K ← L → P` on `V` itself, `P` strictly perfect in `[a, b]`, gives
local models in `[a, b]` (take `W = V`; `restrOver (le_refl V)` is the identity). -/
theorem isPerfectOverIn_of_roof {V : Opens X} {K L P : CochainComplex (Mod (R.over V)) ℤ}
    (f : L ⟶ K) (g : L ⟶ P) [QuasiIso f] [QuasiIso g] (hP : IsStrictlyPerfect P) {a b : ℤ}
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] : IsPerfectOverIn K a b := by
  intro x hx
  exact ⟨V, le_refl V, hx, L, P, f, g, ‹QuasiIso f›, ‹QuasiIso g›, hP, ‹P.IsStrictlyGE a›,
    ‹P.IsStrictlyLE b›⟩

/-- **Z3.j (c).** Local models in `[a, b]` are preserved by quasi-isomorphisms (as
`IsPerfectOver.of_quasiIso_left`). -/
theorem IsPerfectOverIn.of_quasiIso_left {V : Opens X}
    {K K' : CochainComplex (Mod (R.over V)) ℤ} (f : K ⟶ K') [QuasiIso f] {a b : ℤ}
    (hK : IsPerfectOverIn K a b) : IsPerfectOverIn K' a b := by
  intro x hx
  obtain ⟨W, hW, hxW, L, P, g, h, hg, hh, hP, ha, hb⟩ := hK x hx
  have : QuasiIso (((Cohesive.restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    inferInstance
  exact ⟨W, hW, hxW, L, P,
    g ≫ ((Cohesive.restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).map f,
    h, inferInstance, hh, hP, ha, hb⟩

/-- **Z3.j (c).** Local models in `[a, b]` restrict: a roof on `W ∋ x` restricts to `W ⊓ V'`. -/
theorem IsPerfectOverIn.restrOver {V V' : Opens X} (h : V' ≤ V)
    {K : CochainComplex (Mod (R.over V)) ℤ} {a b : ℤ} (hK : IsPerfectOverIn K a b) :
    IsPerfectOverIn (((restrOver R h).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a b := by
  intro x hx
  obtain ⟨W, hW, hxW, L, P, f, g, hf, hg, hP, ha, hb⟩ := hK x (h hx)
  have h1 : (W ⊓ V' : Opens X) ≤ W := inf_le_left
  have h2 : (W ⊓ V' : Opens X) ≤ V' := inf_le_right
  have hf' : QuasiIso (((Cohesive.restrOver R h1).mapHomologicalComplex
    (ComplexShape.up ℤ)).map f) := inferInstance
  have hg' : QuasiIso (((Cohesive.restrOver R h1).mapHomologicalComplex
    (ComplexShape.up ℤ)).map g) := inferInstance
  exact ⟨W ⊓ V', h2, ⟨hxW, hx⟩,
    ((Cohesive.restrOver R h1).mapHomologicalComplex (ComplexShape.up ℤ)).obj L,
    ((Cohesive.restrOver R h1).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    ((Cohesive.restrOver R h1).mapHomologicalComplex (ComplexShape.up ℤ)).map f,
    ((Cohesive.restrOver R h1).mapHomologicalComplex (ComplexShape.up ℤ)).map g,
    hf', hg', hP.restrOver h1, isStrictlyGE_restrOver h1 P a,
    isStrictlyLE_restrOver h1 P b⟩

/-- **Z3.j (c).** Local models in `[a, b]` are a local property: if every `x ∈ V` has an open
neighbourhood `V' ≤ V` on which `K|V'` has local models in `[a, b]`, so does `K`. -/
theorem IsPerfectOverIn.of_restrOver {V : Opens X} {K : CochainComplex (Mod (R.over V)) ℤ}
    {a b : ℤ} (hK : ∀ x ∈ V, ∃ (V' : Opens X) (h : V' ≤ V), x ∈ V' ∧ IsPerfectOverIn
      (((Cohesive.restrOver R h).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a b) :
    IsPerfectOverIn K a b := by
  intro x hx
  obtain ⟨V', h, hxV', hV'⟩ := hK x hx
  obtain ⟨W, hW, hxW, L, P, f, g, hf, hg, hP, ha, hb⟩ := hV' x hxV'
  let e : ((Cohesive.restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((Cohesive.restrOver R h).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((Cohesive.restrOver R (hW.trans h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
    Iso.refl _
  exact ⟨W, hW.trans h, hxW, L, P, f ≫ e.hom, g, inferInstance, hg, hP, ha, hb⟩

/-! ## (d) Homology -/

/-- Sections over `Z ≤ W ≤ V` of `M` vanish if `M|W` is zero. -/
private lemma sections_subsingleton_over {V W : Opens X} (hW : W ≤ V) {M : Mod (R.over V)}
    (h : IsZero ((restrOver R hW).obj M)) (Z : Over V) (hz : Z.left ≤ W) :
    Subsingleton (M.val.obj (op Z)) := by
  let Z' : Over W := Over.mk (homOfLE hz)
  have h1 := (SheafOfModules.evaluation.{0} (R.over W) (op Z')).map_isZero h
  have h2 : (Over.map (homOfLE hW)).obj Z' = Z := by
    rfl
  have h3 : IsZero (M.val.obj (op ((Over.map (homOfLE hW)).obj Z'))) := h1
  rw [h2] at h3
  exact ModuleCat.isZero_iff_subsingleton.1 h3

/-- **Z3.j (d).** A sheaf of modules on `Over V` whose restrictions to the members of an open
cover of `V` are zero is zero. -/
theorem isZero_of_locally_restrOver {V : Opens X} {M : Mod (R.over V)}
    (h : ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧ IsZero ((restrOver R hW).obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  choose W hW hxW hZ using h
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Y
  ext s
  have hsub : Subsingleton (M.val.obj Y) := by
    obtain ⟨Y'⟩ := Y
    let S₀ : Sieve Y'.left :=
      { arrows := fun Z _ => ∃ (x : X) (hx : x ∈ V), Z ≤ W x hx
        downward_closed := by
          rintro Z Z' f ⟨x, hx, hZ⟩ g
          exact ⟨x, hx, (leOfHom g).trans hZ⟩ }
    have hS₀ : S₀ ∈ Opens.grothendieckTopology X Y'.left := by
      intro y hy
      have hyV : y ∈ V := leOfHom Y'.hom hy
      exact ⟨Y'.left ⊓ W y hyV, homOfLE inf_le_left, ⟨y, hyV, inf_le_right⟩, hy, hxW y hyV⟩
    have hS : (Sieve.overEquiv Y').symm S₀ ∈ ((Opens.grothendieckTopology X).over V) Y' :=
      GrothendieckTopology.overEquiv_symm_mem_over _ Y' S₀ hS₀
    refine ⟨fun s t => ?_⟩
    refine Presheaf.IsSheaf.isSeparated M.isSheaf Y' _ hS s t ?_
    intro Z f hf
    obtain ⟨x, hx, hZx⟩ := (Sieve.overEquiv_symm_iff S₀ f).1 hf
    have := sections_subsingleton_over (hW x hx) (hZ x hx) Z hZx
    exact Subsingleton.elim (α := M.val.obj (op Z)) _ _
  exact Subsingleton.elim _ _

/-- **Z3.j (d).** As S9.d. The homology sheaves of a complex on `Over V` with local models in
`[a, b]` vanish outside `[a, b]`. -/
theorem IsPerfectOverIn.exactAt {V : Opens X} {K : CochainComplex (Mod (R.over V)) ℤ} {a b : ℤ}
    (hK : IsPerfectOverIn K a b) (i : ℤ) (hi : i < a ∨ b < i) : K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
  refine isZero_of_locally_restrOver fun x hx => ?_
  obtain ⟨W, hW, hxW, L, P, f, g, hf, hg, -, ha, hb⟩ := hK x hx
  refine ⟨W, hW, hxW, ?_⟩
  have hP : P.ExactAt i := by
    rcases hi with hi | hi
    · exact P.exactAt_of_isGE a i hi
    · exact P.exactAt_of_isLE b i hi
  have hKi : (((Cohesive.restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt
      i := by
    have := (quasiIso_iff f).1 hf i
    have := (quasiIso_iff g).1 hg i
    rw [← exactAt_iff_of_quasiIsoAt f i, exactAt_iff_of_quasiIsoAt g i]
    exact hP
  have h1 : ((K.sc i).map (Cohesive.restrOver R hW)).Exact := hKi
  rw [ShortComplex.exact_iff_isZero_homology] at h1
  exact IsZero.of_iso h1 ((K.sc i).mapHomologyIso (Cohesive.restrOver R hW)).symm

/-! ## (h) Sanity check against S9.b -/

/-- **Z3.j (h).** Faithfulness check of `IsPerfectOver` against the frozen `IsPerfect`: for a
complex `K` of sheaves of `R`-modules on `X`, its restriction to the over-site `Over ⊤` is perfect
iff `K` is (`restr_restrOver`: `K|⊤|W ≅ K|W`). -/
theorem isPerfectOver_restr_top_iff (K : CochainComplex (Mod R) ℤ) :
    IsPerfectOver (((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ↔
      IsPerfect K := by
  have e : ∀ W : Opens X, (hW : W ≤ ⊤) →
      ((restrOver R hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((restr R W).mapHomologicalComplex (ComplexShape.up ℤ)).obj K := fun W hW =>
    (NatIso.mapHomologicalComplex (restr_restrOver R hW) (ComplexShape.up ℤ)).app K
  constructor
  · intro hK x
    obtain ⟨W, hW, hxW, L, P, f, g, hf, hg, hP⟩ := hK x trivial
    exact ⟨W, hxW, L, P, f ≫ (e W hW).hom, g, inferInstance, hg, hP⟩
  · intro hK x _
    obtain ⟨W, hxW, L, P, f, g, hf, hg, hP⟩ := hK x
    exact ⟨W, le_top, hxW, L, P, f ≫ (e W le_top).inv, g, inferInstance, hg, hP⟩

end Cohesive
