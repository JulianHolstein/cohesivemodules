import Cohesivemodules.Sheaf.HomAcyclic
import Cohesivemodules.Sheaf.Restriction

set_option linter.style.header false

/-!
# S7.b′, S7.c′: Hom complexes and quasi-isomorphisms on any site

Blueprint items S7.b, S7.c (§3) in the generality needed by C4 step 3 (v1.11): the local
square lives on the over-site of an open `U`, where `Sheaf/HomAcyclic.lean` (stated on `Opens X`)
does not apply. Same statements on any small site; for S7.c′ the injectivity of the restrictions
`I^i|V` (automatic on a space, S5.c) is a hypothesis, and `injective_overFunctor_restr` supplies
it for complexes restricted from `X`. Also the naturality of `homComplexOverIso`.

## Deviations
* S7.c′ assumes the restrictions of the terms of `I` to every object are injective (on a space
  this follows from `I^i` injective, S5.c).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits TopologicalSpace

section SiteHelpers

namespace SiteHom

open CochainComplex.HomComplex
open scoped ZeroObject

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}}

/-- Restriction of a section. -/
private abbrev sres (N : Mod R) {U W : C} (h : W ⟶ U) (s : N.val.obj (op U)) :
    N.val.obj (op W) := (N.val.map h.op).hom s

/-- The sieve on `U` of arrows `g : V ⟶ U` over which `s ∈ N(U)` restricts into the image
of `f`. -/
private def imSieve {M N : Mod R} (f : M ⟶ N) {U : C} (s : N.val.obj (op U)) : Sieve U where
  arrows V g := ∃ t : M.val.obj (op V), f.val.app (op V) t = sres N g s
  downward_closed := by
    rintro V W g ⟨t, ht⟩ h
    refine ⟨(M.val.map h.op).hom t, ?_⟩
    have h1 := PresheafOfModules.naturality_apply f.val h.op t
    have h2 := N.val.map_comp_apply g.op h.op s
    change f.val.app (op W) (M.val.map h.op t) = N.val.map (h ≫ g).op s
    rw [h1, ht]
    exact h2.symm

/-- The sieve of a restricted section is the pullback sieve. -/
private lemma imSieve_map {M N : Mod R} (f : M ⟶ N) {U : C}
    (s : N.val.obj (op U)) {W : C} (h : W ⟶ U) :
    imSieve f (sres N h s) = (imSieve f s).pullback h := by
  ext V g
  simp only [imSieve, Sieve.pullback_apply]
  change (∃ t, _ = N.val.map g.op (N.val.map h.op s)) ↔
    ∃ t, _ = N.val.map (g ≫ h).op s
  rw [← N.val.map_comp_apply]
  rfl

/-- The submodule of sections of `N` that are locally in the image of `f`. -/
private def localImage {M N : Mod R} (f : M ⟶ N) : N.Submodule where
  obj U :=
    { carrier := {s | imSieve f s ∈ J U.unop}
      add_mem' := by
        intro s s' hs hs'
        refine J.superset_covering ?_ (J.intersection_covering hs hs')
        rintro V g ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
        refine ⟨t + t', ?_⟩
        simp only [map_add, ht, ht']
        rfl
      zero_mem' := by
        refine J.superset_covering ?_ (J.top_mem _)
        intro V g _
        exact ⟨0, by simp only [map_zero]; rfl⟩
      smul_mem' := by
        intro r s hs
        refine J.superset_covering ?_ hs
        rintro V g ⟨t, ht⟩
        refine ⟨(R.obj.map g.op).hom r • t, ?_⟩
        have h1 : f.val.app (op V) ((R.obj.map g.op).hom r • t) =
            (R.obj.map g.op).hom r • f.val.app (op V) t :=
          map_smul (f.val.app (op V)).hom _ _
        have h2 := N.val.map_smul g.op r s
        rw [h1, ht]
        exact h2.symm }
  map := by
    intro Xo Yo g s hs
    have h1 := J.pullback_stable g.unop hs
    have h2 := imSieve_map f s g.unop
    show imSieve f (sres N g.unop s) ∈ J Yo.unop
    rw [h2]
    exact h1
  isSheaf := by
    intro Xo s hs
    refine J.transitive hs _ (fun V g hg => ?_)
    have h2 := imSieve_map f s g
    exact h2 ▸ hg

/-- `f` factors through its local image. -/
private def toLocalImage {M N : Mod R} (f : M ⟶ N) :
    M ⟶ (localImage f).toSheafOfModules :=
  ⟨{ app := fun U => ModuleCat.ofHom ((f.val.app U).hom.codRestrict ((localImage f).obj U) (by
        intro t
        refine J.superset_covering ?_ (J.top_mem _)
        intro V g _
        refine ⟨(M.val.map g.op).hom t, ?_⟩
        exact PresheafOfModules.naturality_apply f.val g.op t))
     naturality := by
        intro U V g
        ext t
        exact Subtype.ext (PresheafOfModules.naturality_apply f.val g t) }⟩

/-- The factorization through the local image composes to `f`. -/
private lemma toLocalImage_ι {M N : Mod R} (f : M ⟶ N) :
    toLocalImage f ≫ (localImage f).ι = f := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext t
  rfl

/-- An epimorphism of sheaves of modules is locally surjective, on any site. -/
private lemma imSieve_mem_of_epi {M N : Mod R} (f : M ⟶ N) [Epi f] {U : C}
    (s : N.val.obj (op U)) : imSieve f s ∈ J U := by
  have hepi : Epi (localImage f).ι := epi_of_epi_fac (toLocalImage_ι f)
  have hiso : IsIso (localImage f).ι := isIso_of_mono_of_epi _
  have h : ((inv (localImage f).ι ≫ (localImage f).ι).val.app (op U)) s = s := by
    rw [IsIso.inv_hom_id]
    rfl
  have h' : ((inv (localImage f).ι).val.app (op U) s).1 = s := h
  exact h' ▸ ((inv (localImage f).ι).val.app (op U) s).2

/-- Restriction to an over-site is a right adjoint (so preserves finite limits). -/
private instance ovR (Y : C) : (SheafOfModules.overFunctor.{0} R Y).IsRightAdjoint :=
  @SheafOfModules.instIsRightAdjointPushforward _ _ _ _ _ _ _ _ _ _ (𝟙 (R.over Y))
    (PresheafOfModules.instIsRightAdjointPushforward (F := Over.forget Y)
      (R := R.obj) (S := (R.over Y).obj) (𝟙 _)) _ _

/-- Restriction to an over-site preserves epimorphisms (epis are locally surjective, and
`Over.forget` is cocontinuous). -/
private lemma overFunctor_epi (V : C) {M N : Mod R} (φ : M ⟶ N) [Epi φ] :
    Epi ((SheafOfModules.overFunctor.{0} R V).map φ) := by
  have h1 : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map φ.val) :=
    ⟨fun s => imSieve_mem_of_epi φ s⟩
  have h2 := Presheaf.isLocallySurjective_whisker (J.over V) J (Over.forget V)
    ((PresheafOfModules.toPresheaf R.obj).map φ.val)
  have h3 : Epi ((SheafOfModules.toSheaf (R.over V)).map
      ((SheafOfModules.overFunctor.{0} R V).map φ)) := by
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over V)).map
      ((SheafOfModules.overFunctor.{0} R V).map φ)) := h2
    infer_instance
  exact (SheafOfModules.toSheaf (R.over V)).epi_of_epi_map h3

/-- Restriction to an over-site preserves epimorphisms. -/
private instance overFunctor_preservesEpi (V : C) :
    (SheafOfModules.overFunctor.{0} R V).PreservesEpimorphisms where
  preserves f hf := overFunctor_epi V f

/-- Restriction to an over-site preserves homology (right adjoint, preserves epis). -/
private instance overFunctor_preservesHomology (V : C) :
    (SheafOfModules.overFunctor.{0} R V).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The complex of sections of `𝓗om(K, I)` over `V` (as abelian groups) is Mathlib's Hom complex
`HomComplex (K|V) (I|V)`. -/
private def secHomIso (hR : IsCommSheaf R) (K I : CochainComplex (Mod R) ℤ) (V : C) :
    ((forget₂ (ModuleCat ↑(R.obj.obj (op V))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((SheafOfModules.evaluation.{0} R (op V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (homSheafComplex hR K I)) ≅
      CochainComplex.HomComplex ((overC V).obj K) ((overC V).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (homComplexSectionsEquiv hR K I n V).toAddCommGrpIso) (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      ext z
      exact (homComplexSectionsEquiv_d hR K I i V z).symm)

/-! ### Helpers for S7.b -/

/-- Pointwise extensionality for morphisms of restricted sheaves of modules. -/
private lemma hom_ext_pt₀ {V : C} {M N : Mod R} {φ ψ : M.over V ⟶ N.over V}
    (h : ∀ (Z : (Over V)ᵒᵖ) (m : (M.over V).val.obj Z),
      (φ.val.app Z).hom m = (ψ.val.app Z).hom m) : φ = ψ := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext m
  exact h Z m

/-- `homPre` of the identity. -/
private lemma homPre_id' (hR : IsCommSheaf R) (M N : Mod R) :
    homPre hR (𝟙 M) N = 𝟙 _ := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt₀ fun Z m ↦ rfl)

/-- `homPre` is contravariantly functorial. -/
private lemma homPre_comp' (hR : IsCommSheaf R) {M M' M'' : Mod R} (f : M' ⟶ M) (g : M'' ⟶ M')
    (N : Mod R) : homPre hR f N ≫ homPre hR g N = homPre hR (g ≫ f) N := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt₀ fun Z m ↦ rfl)

/-- `homPre` is additive. -/
private lemma homPre_add (hR : IsCommSheaf R) {M M' : Mod R} (f f' : M' ⟶ M) (N : Mod R) :
    homPre hR (f + f') N = homPre hR f N + homPre hR f' N := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt₀ fun Z m ↦ by
    exact map_add (φ.val.app Z).hom _ _)

/-- `homPre` of the zero map. -/
private lemma homPre_zero (hR : IsCommSheaf R) {M M' : Mod R} (N : Mod R) :
    homPre hR (0 : M' ⟶ M) N = 0 := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt₀ fun Z m ↦ by
    exact map_zero (φ.val.app Z).hom)

/-- `homPre` and `homPost` commute. -/
private lemma homPre_homPost' (hR : IsCommSheaf R) {M M' N N' : Mod R} (f : M' ⟶ M)
    (g : N ⟶ N') : homPre hR f N ≫ homPost hR M' g = homPost hR M g ≫ homPre hR f N' := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt₀ fun Z m ↦ rfl)

/-- Degree `n` of `homComplexMap₁`, as a map between the products. -/
private def preX (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ} (f : K' ⟶ K)
    (L : CochainComplex (Mod R) ℤ) (n : ℤ) : homComplexX hR K L n ⟶ homComplexX hR K' L n :=
  Limits.Pi.map fun T : Triplet n ↦ homPre hR (f.f T.p) (L.X T.q)

/-- Degree `n` of `homComplexMap₂`, as a map between the products. -/
private def postX (hR : IsCommSheaf R) (K : CochainComplex (Mod R) ℤ)
    {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') (n : ℤ) :
    homComplexX hR K L n ⟶ homComplexX hR K L' n :=
  Limits.Pi.map fun T : Triplet n ↦ homPost hR (K.X T.p) (g.f T.q)

/-- `preX` is contravariantly functorial. -/
private lemma preX_comp (hR : IsCommSheaf R) {K K' K'' : CochainComplex (Mod R) ℤ}
    (f : K' ⟶ K) (f' : K'' ⟶ K') (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    preX hR f L n ≫ preX hR f' L n = preX hR (f' ≫ f) L n := by
  apply Pi.hom_ext
  intro T
  simp only [preX, Category.assoc, Limits.Pi.map_π]
  rw [← Category.assoc, Limits.Pi.map_π, Category.assoc, homPre_comp']
  rfl

/-- `preX` of the identity. -/
private lemma preX_id (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    preX hR (𝟙 K) L n = 𝟙 _ := by
  apply Pi.hom_ext
  intro T
  simp only [preX, Limits.Pi.map_π, HomologicalComplex.id_f, homPre_id', Category.id_comp,
    Category.comp_id]

/-- `preX` of the zero map. -/
private lemma preX_zero (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ}
    (L : CochainComplex (Mod R) ℤ) (n : ℤ) : preX hR (0 : K' ⟶ K) L n = 0 := by
  apply Pi.hom_ext
  intro T
  simp only [preX, Limits.Pi.map_π, HomologicalComplex.zero_f_apply, homPre_zero,
    Limits.comp_zero, Limits.zero_comp]

/-- `postX` and `preX` commute. -/
private lemma postX_preX (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ}
    (f : K' ⟶ K) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') (n : ℤ) :
    postX hR K g n ≫ preX hR f L' n = preX hR f L n ≫ postX hR K' g n := by
  apply Pi.hom_ext
  intro T
  simp only [preX, postX, Category.assoc, Limits.Pi.map_π]
  rw [← Category.assoc (Limits.Pi.map (fun T : Triplet n ↦ homPre hR (f.f T.p) (L.X T.q))),
    Limits.Pi.map_π, Category.assoc, homPre_homPost']
  rw [← Category.assoc (Limits.Pi.map (fun T : Triplet n ↦ homPost hR (K.X T.p) (g.f T.q))),
    Limits.Pi.map_π, Category.assoc]

/-- `homComplexMap₁` is contravariantly functorial. -/
private lemma homComplexMap₁_comp (hR : IsCommSheaf R) {K K' K'' : CochainComplex (Mod R) ℤ}
    (f : K' ⟶ K) (f' : K'' ⟶ K') (L : CochainComplex (Mod R) ℤ) :
    homComplexMap₁ hR f L ≫ homComplexMap₁ hR f' L = homComplexMap₁ hR (f' ≫ f) L := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  exact preX_comp hR f f' L n

/-- `homComplexMap₁` of the identity. -/
private lemma homComplexMap₁_id (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) :
    homComplexMap₁ hR (𝟙 K) L = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n ↦ preX_id hR K L n

/-- `homComplexMap₁` of the zero map. -/
private lemma homComplexMap₁_zero (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ}
    (L : CochainComplex (Mod R) ℤ) : homComplexMap₁ hR (0 : K' ⟶ K) L = 0 :=
  HomologicalComplex.hom_ext _ _ fun n ↦ preX_zero hR L n

/-- `homComplexMap₁` and `homComplexMap₂` commute. -/
private lemma homComplexMap₂_comm₁ (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ}
    (f : K' ⟶ K) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') :
    homComplexMap₂ hR K g ≫ homComplexMap₁ hR f L' =
      homComplexMap₁ hR f L ≫ homComplexMap₂ hR K' g :=
  HomologicalComplex.hom_ext _ _ fun n ↦ postX_preX hR f g n

/-- `𝓗om(P, -)` preserves quasi-isomorphisms. -/
private def HomGood (hR : IsCommSheaf R) (P : CochainComplex (Mod R) ℤ) : Prop :=
  ∀ (L L' : CochainComplex (Mod R) ℤ) (g : L ⟶ L') [QuasiIso g],
    QuasiIso (homComplexMap₂ hR P g)

/-- `HomGood` passes to retracts of complexes. -/
private lemma HomGood.of_retract (hR : IsCommSheaf R) {P F : CochainComplex (Mod R) ℤ}
    (hF : HomGood hR F) (ι : P ⟶ F) (π : F ⟶ P) (h : ι ≫ π = 𝟙 P) : HomGood hR P := by
  intro L L' g _
  have := hF L L' g
  have hret : RetractArrow (homComplexMap₂ hR P g) (homComplexMap₂ hR F g) :=
    { i := Arrow.homMk (homComplexMap₁ hR π L) (homComplexMap₁ hR π L')
        (homComplexMap₂_comm₁ hR π g).symm
      r := Arrow.homMk (homComplexMap₁ hR ι L) (homComplexMap₁ hR ι L')
        (homComplexMap₂_comm₁ hR ι g).symm
      retract := by
        refine Arrow.hom_ext _ _ ?_ ?_
        · exact (homComplexMap₁_comp hR π ι L).trans (by rw [h, homComplexMap₁_id]; rfl)
        · exact (homComplexMap₁_comp hR π ι L').trans (by rw [h, homComplexMap₁_id]; rfl) }
  exact quasiIso_of_retractArrow hret

/-- The short complex `𝓗om(S₃, L) ⟶ 𝓗om(S₂, L) ⟶ 𝓗om(S₁, L)`. -/
private def homSES (hR : IsCommSheaf R) (S : ShortComplex (CochainComplex (Mod R) ℤ))
    (L : CochainComplex (Mod R) ℤ) : ShortComplex (CochainComplex (Mod R) ℤ) :=
  ShortComplex.mk (homComplexMap₁ hR S.g L) (homComplexMap₁ hR S.f L)
    (by rw [homComplexMap₁_comp, S.zero, homComplexMap₁_zero])

/-- Precomposition by a graded family of maps, degree `n` of the Hom complex. -/
private def preG (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ}
    (φ : ∀ p, K'.X p ⟶ K.X p) (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexX hR K L n ⟶ homComplexX hR K' L n :=
  Limits.Pi.map fun T : Triplet n ↦ homPre hR (φ T.p) (L.X T.q)

/-- `preG` is contravariantly functorial. -/
private lemma preG_comp (hR : IsCommSheaf R) {K K' K'' : CochainComplex (Mod R) ℤ}
    (φ : ∀ p, K'.X p ⟶ K.X p) (ψ : ∀ p, K''.X p ⟶ K'.X p) (L : CochainComplex (Mod R) ℤ)
    (n : ℤ) : preG hR φ L n ≫ preG hR ψ L n = preG hR (fun p ↦ ψ p ≫ φ p) L n := by
  apply Pi.hom_ext
  intro T
  simp only [preG, Category.assoc, Limits.Pi.map_π]
  rw [← Category.assoc, Limits.Pi.map_π, Category.assoc, homPre_comp']

/-- `preG` is additive. -/
private lemma preG_add (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ}
    (φ ψ : ∀ p, K'.X p ⟶ K.X p) (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    preG hR φ L n + preG hR ψ L n = preG hR (fun p ↦ φ p + ψ p) L n := by
  apply Pi.hom_ext
  intro T
  simp only [preG, Limits.Pi.map_π, Preadditive.add_comp]
  rw [homPre_add, Preadditive.comp_add]

/-- `preG` of a family of identities. -/
private lemma preG_id (hR : IsCommSheaf R) {K : CochainComplex (Mod R) ℤ}
    (φ : ∀ p, K.X p ⟶ K.X p) (hφ : ∀ p, φ p = 𝟙 _) (L : CochainComplex (Mod R) ℤ)
    (n : ℤ) :
    preG hR φ L n = 𝟙 _ := by
  apply Pi.hom_ext
  intro T
  simp only [preG, Limits.Pi.map_π, hφ, homPre_id', Category.id_comp, Category.comp_id]

/-- Degreewise splitting of the Hom short complex. -/
private def homSESSplitting (hR : IsCommSheaf R) (S : ShortComplex (CochainComplex (Mod R) ℤ))
    (hsplit : ∀ n, (S.map (HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n)).Splitting)
    (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    ((homSES hR S L).map (HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n)).Splitting where
  r := preG hR (fun p ↦ (hsplit p).s) L n
  s := preG hR (fun p ↦ (hsplit p).r) L n
  f_r := by
    show preG hR (fun p ↦ S.g.f p) L n ≫ preG hR (fun p ↦ (hsplit p).s) L n = _
    rw [preG_comp]
    exact preG_id hR _ (fun p ↦ (hsplit p).s_g) L n
  s_g := by
    show preG hR (fun p ↦ (hsplit p).r) L n ≫ preG hR (fun p ↦ S.f.f p) L n = _
    rw [preG_comp]
    exact preG_id hR _ (fun p ↦ (hsplit p).f_r) L n
  id := by
    show preG hR (fun p ↦ (hsplit p).s) L n ≫ preG hR (fun p ↦ S.g.f p) L n +
      preG hR (fun p ↦ S.f.f p) L n ≫ preG hR (fun p ↦ (hsplit p).r) L n = _
    rw [preG_comp, preG_comp, preG_add]
    refine preG_id hR _ (fun p ↦ ?_) L n
    rw [add_comm]
    exact (hsplit p).id

/-- A degreewise split short exact sequence gives a short exact Hom sequence. -/
private lemma homSES_shortExact (hR : IsCommSheaf R) (S : ShortComplex (CochainComplex (Mod R) ℤ))
    (hsplit : ∀ n, (S.map (HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n)).Splitting)
    (L : CochainComplex (Mod R) ℤ) : (homSES hR S L).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (homSESSplitting hR S hsplit L n).shortExact

section FiveLemma

open ComposableArrows Abelian HomologicalComplex HomologySequence

variable {C : Type*} [Category* C] [Abelian C]
  {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂ in
/-- Five lemma for the middle term of a morphism of short exact sequences of complexes. -/
private lemma isIso_homologyMap_τ₂ (i : ℤ)
    (h₁ : ∀ j, IsIso (homologyMap φ.τ₁ j)) (h₃ : ∀ j, IsIso (homologyMap φ.τ₃ j)) :
    IsIso (homologyMap φ.τ₂ i) := by
  have hmono : Mono (homologyMap φ.τ₂ i) := by
    apply mono_of_epi_of_mono_of_mono
      ((δ₀Functor ⋙ δ₀Functor).map
        (mapComposableArrows₅ φ hS₁ hS₂ (i - 1) i (by simp)))
    · exact (composableArrows₅_exact hS₁ (i - 1) i (by simp)).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ (i - 1) i (by simp)).δ₀.δ₀
    · exact (h₃ _).epi_of_iso
    · exact (h₁ _).mono_of_iso
    · exact (h₃ _).mono_of_iso
  have hepi : Epi (homologyMap φ.τ₂ i) := by
    apply epi_of_epi_of_epi_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map
        (mapComposableArrows₅ φ hS₁ hS₂ i (i + 1) (by simp)))
    · exact (composableArrows₅_exact hS₁ i (i + 1) (by simp)).δlast.δlast
    · exact (composableArrows₅_exact hS₂ i (i + 1) (by simp)).δlast.δlast
    · exact (h₁ _).epi_of_iso
    · exact (h₃ _).epi_of_iso
    · exact (h₁ _).mono_of_iso
  exact isIso_of_mono_of_epi _

include hS₁ hS₂ in
/-- Two out of three for quasi-isomorphisms of short exact sequences: the middle one. -/
private lemma quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_τ₂ φ hS₁ hS₂ i
    (fun j ↦ (quasiIsoAt_iff_isIso_homologyMap _ _).1 (h₁.quasiIsoAt j))
    (fun j ↦ (quasiIsoAt_iff_isIso_homologyMap _ _).1 (h₃.quasiIsoAt j))

end FiveLemma

/-- `HomGood` for the middle term of a degreewise split short exact sequence of complexes. -/
private lemma HomGood.of_ses (hR : IsCommSheaf R) (S : ShortComplex (CochainComplex (Mod R) ℤ))
    (hsplit : ∀ n, (S.map (HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n)).Splitting)
    (h₁ : HomGood hR S.X₁) (h₃ : HomGood hR S.X₃) : HomGood hR S.X₂ := by
  intro L L' g _
  let φ : homSES hR S L ⟶ homSES hR S L' :=
    { τ₁ := homComplexMap₂ hR S.X₃ g
      τ₂ := homComplexMap₂ hR S.X₂ g
      τ₃ := homComplexMap₂ hR S.X₁ g
      comm₁₂ := homComplexMap₂_comm₁ hR S.g g
      comm₂₃ := homComplexMap₂_comm₁ hR S.f g }
  exact quasiIso_τ₂ φ (homSES_shortExact hR S hsplit L) (homSES_shortExact hR S hsplit L')
    (h₃ L L' g) (h₁ L L' g)

/-- The evaluation of a morphism `R|V ⟶ N|V` at the unit section. -/
private def epsFun (N : Mod R) (V : C) (φ : (SheafOfModules.unit R).over V ⟶ N.over V) :
    N.val.obj (op V) :=
  (φ.val.app (op (Over.mk (𝟙 V)))).hom (1 : R.obj.obj (op V))

/-- Naturality of `epsFun` in the open set. -/
private lemma epsFun_restr (N : Mod R) {V W : C} (g : W ⟶ V)
    (φ : (SheafOfModules.unit R).over V ⟶ N.over V) :
    epsFun N W (homRestr g φ) = (N.val.map g.op).hom (epsFun N V φ) := by
  let u : (Over.map g).obj (Over.mk (𝟙 W)) ⟶ Over.mk (𝟙 V) := Over.homMk g (by simp)
  have h := PresheafOfModules.sections_property
    ((N.over V).unitHomEquiv (show SheafOfModules.unit (R.over V) ⟶ N.over V from φ)) u.op
  exact h.symm

/-- Evaluation at the unit section as a morphism `𝓗om(R, N) ⟶ N`. -/
private def epsHom (hR : IsCommSheaf R) (N : Mod R) :
    homSheaf hR (SheafOfModules.unit R) N ⟶ N where
  val :=
    { app := fun V ↦ ModuleCat.ofHom (X := (homSheaf hR (SheafOfModules.unit R) N).val.obj V)
        (Y := N.val.obj V)
        { toFun := epsFun N V.unop
          map_add' := fun φ ψ ↦ rfl
          map_smul' := fun r φ ↦ by
            have h : (overRes r (op (Over.mk (𝟙 V.unop))) : R.obj.obj V) = r := by
              show (R.obj.map (𝟙 V)).hom r = r
              rw [CategoryTheory.Functor.map_id]
              rfl
            exact congrArg (fun a : R.obj.obj V ↦ a • epsFun N V.unop φ) h }
      naturality := fun {V W} f ↦ by
        ext φ
        exact epsFun_restr N f.unop φ }

/-- A morphism of sheaves of modules that is bijective on sections is an isomorphism. -/
private lemma isIso_of_bijective_app {M N : Mod R} (f : M ⟶ N)
    (h : ∀ V : Cᵒᵖ, Function.Bijective (f.val.app V)) : IsIso f := by
  have h1 : IsIso ((SheafOfModules.toSheaf.{0} R).map f) := by
    have : IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf.{0} R).map f)) := by
      have : ∀ V, IsIso
          (((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf.{0} R).map f)).app V) :=
        fun V ↦ (ConcreteCategory.isIso_iff_bijective _).2 (h V)
      exact NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso f (SheafOfModules.toSheaf.{0} R)

/-- A section of a sheaf on the over-site is determined by its value at the terminal object. -/
private lemma sections_eq_of_terminal {V : C} {M : Mod (R.over V)} (s t : M.sections)
    (h : s.1 (op (Over.mk (𝟙 V))) = t.1 (op (Over.mk (𝟙 V)))) : s = t := by
  apply PresheafOfModules.sections_ext
  intro Z
  obtain ⟨Z⟩ := Z
  let u : Z ⟶ Over.mk (𝟙 V) := Over.homMk Z.hom (by simp)
  have h1 := PresheafOfModules.sections_property s u.op
  have h2 := PresheafOfModules.sections_property t u.op
  rw [← h1, ← h2, h]

/-- `epsFun` is bijective. -/
private lemma epsFun_bijective (N : Mod R) (V : C) : Function.Bijective (epsFun N V) := by
  constructor
  · intro φ ψ hφψ
    have := sections_eq_of_terminal (M := N.over V)
      ((N.over V).unitHomEquiv (show SheafOfModules.unit (R.over V) ⟶ N.over V from φ))
      ((N.over V).unitHomEquiv (show SheafOfModules.unit (R.over V) ⟶ N.over V from ψ)) hφψ
    exact (N.over V).unitHomEquiv.injective this
  · intro s0
    let sec : (N.over V).sections := PresheafOfModules.sectionsMk
      (fun Z ↦ N.val.map Z.unop.hom.op s0) (by
        intro Z Z' g
        have hw : g.unop.left ≫ Z.unop.hom = Z'.unop.hom := Over.w g.unop
        show (N.val.map g.unop.left.op).hom (N.val.map Z.unop.hom.op s0) = _
        rw [← PresheafOfModules.map_comp_apply]
        rw [← hw]
        rfl)
    refine ⟨(N.over V).unitHomEquiv.symm sec, ?_⟩
    show ((N.over V).unitHomEquiv ((N.over V).unitHomEquiv.symm sec)).val
      (op (Over.mk (𝟙 V))) = s0
    rw [Equiv.apply_symm_apply]
    show (N.val.map (𝟙 (op V))).hom s0 = s0
    simp only [PresheafOfModules.map_id]
    rfl

/-- `epsHom` is an isomorphism. -/
private instance isIso_epsHom (hR : IsCommSheaf R) (N : Mod R) : IsIso (epsHom hR N) :=
  isIso_of_bijective_app _ fun V ↦ epsFun_bijective N V.unop

/-- `epsHom` is natural in the target. -/
private lemma homPost_epsHom (hR : IsCommSheaf R) {N N' : Mod R} (g : N ⟶ N') :
    homPost hR (SheafOfModules.unit R) g ≫ epsHom hR N' = epsHom hR N ≫ g := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ rfl)

/-- The complex `n ↦ L^{a+n}`, differential `d^{a+n}` (no signs). -/
private def shiftIdx (a : ℤ) (L : CochainComplex (Mod R) ℤ) : CochainComplex (Mod R) ℤ where
  X n := L.X (a + n)
  d i j := L.d (a + i) (a + j)
  shape i j hij := L.shape _ _ (by
    simp only [ComplexShape.up_Rel] at hij ⊢
    lia)
  d_comp_d' i j k _ _ := L.d_comp_d _ _ _

/-- The map `n ↦ g^{a+n}`. -/
private def shiftIdxMap (a : ℤ) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') :
    shiftIdx a L ⟶ shiftIdx a L' where
  f n := g.f (a + n)
  comm' _ _ _ := g.comm _ _

/-- `shiftIdxMap` preserves quasi-isomorphisms. -/
private lemma quasiIso_shiftIdxMap (a : ℤ) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L')
    [QuasiIso g] : QuasiIso (shiftIdxMap a g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' (shiftIdxMap a g) (n - 1) n (n + 1) (by simp) (by simp)]
  have := (quasiIsoAt_iff' g (a + (n - 1)) (a + n) (a + (n + 1))
    (by rw [CochainComplex.prev]; lia) (by rw [CochainComplex.next]; lia)).1
    ((inferInstance : QuasiIso g).quasiIsoAt (a + n))
  exact this

/-- A product projection is an isomorphism when all other factors are zero. -/
private lemma isIso_pi_π_of_isZero {ι : Type} {A : Type*} [Category A] [HasZeroMorphisms A]
    (f : ι → A) [HasProduct f] (j : ι) (h : ∀ i, i ≠ j → IsZero (f i)) :
    IsIso (Pi.π f j) := by
  classical
  let s : f j ⟶ ∏ᶜ f := Pi.lift fun i ↦ if hi : i = j then eqToHom (by rw [hi]) else 0
  refine ⟨s, ?_, ?_⟩
  · apply Pi.hom_ext
    intro i
    by_cases hi : i = j
    · subst hi
      simp [s]
    · exact (h i hi).eq_of_tgt _ _
  · simp [s]

/-- `𝓗om(0, N)` is zero. -/
private lemma isZero_homSheaf_left (hR : IsCommSheaf R) {M : Mod R} (N : Mod R)
    (hM : IsZero M) : IsZero (homSheaf hR M N) := by
  rw [IsZero.iff_id_eq_zero]
  rw [← homPre_id', hM.eq_of_src (𝟙 M) 0, homPre_zero]

section Single

variable (hR : IsCommSheaf R) (M : Mod R) (a : ℤ)

/-- The complex with `M` in degree `a`. -/
private abbrev sing : CochainComplex (Mod R) ℤ :=
  (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).obj M

/-- The distinguished triplet `(a, a + n)`. -/
private abbrev trip (n : ℤ) : Triplet n := ⟨a, a + n, rfl⟩

/-- `𝓗om^n(M[-a], L) ⟶ 𝓗om(M, L^{a+n})`: projection to the only nonzero factor. -/
private def eS (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexX hR (sing M a) L n ⟶ homSheaf hR M (L.X (a + n)) :=
  Pi.π (fun T : Triplet n ↦ homSheaf hR ((sing M a).X T.p) (L.X T.q)) (trip a n) ≫
    homPre hR (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).inv (L.X (a + n))

/-- `eS` is an isomorphism. -/
private lemma isIso_eS (L : CochainComplex (Mod R) ℤ) (n : ℤ) : IsIso (eS hR M a L n) := by
  have h1 : IsIso (Pi.π (fun T : Triplet n ↦ homSheaf hR ((sing M a).X T.p) (L.X T.q))
      (trip a n)) := by
    refine isIso_pi_π_of_isZero _ _ fun T hT ↦ ?_
    refine isZero_homSheaf_left hR _ ?_
    refine HomologicalComplex.isZero_single_obj_X _ _ _ _ fun hp ↦ hT ?_
    obtain ⟨p, q, hpq⟩ := T
    subst hpq
    obtain rfl : p = a := hp
    rfl
  have h2 : IsIso (homPre hR (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).inv
      (L.X (a + n))) := by
    refine ⟨homPre hR
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a M).hom _, ?_, ?_⟩
    · rw [homPre_comp', Iso.hom_inv_id, homPre_id']
    · rw [homPre_comp', Iso.inv_hom_id, homPre_id']
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- `eS` commutes with the differentials. -/
private lemma eS_comm (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexD hR (sing M a) L n ≫ eS hR M a L (n + 1) =
      eS hR M a L n ≫ homPost hR M (L.d (a + n) (a + (n + 1))) := by
  unfold eS
  rw [← Category.assoc, homComplexD_π hR (sing M a) L n (trip a (n + 1))]
  have h0 : (sing M a).d a (a + 1) = 0 := HomologicalComplex.single_obj_d _ _ _ _ _
  simp only [trip, h0, homPre_zero, Limits.comp_zero, smul_zero, add_zero, Category.assoc]
  rw [← homPre_homPost']

/-- `eS` is natural in the target complex. -/
private lemma eS_nat (L L' : CochainComplex (Mod R) ℤ) (g : L ⟶ L') (n : ℤ) :
    eS hR M a L n ≫ homPost hR M (g.f (a + n)) = postX hR (sing M a) g n ≫ eS hR M a L' n := by
  unfold eS postX
  rw [← Category.assoc (Limits.Pi.map _), Limits.Pi.map_π, Category.assoc, Category.assoc,
    homPre_homPost']

/-- `𝓗om^n(R[-a], L) ≅ L^{a+n}`. -/
private def eU (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexX hR (sing (SheafOfModules.unit R) a) L n ≅ L.X (a + n) :=
  haveI := isIso_eS hR (SheafOfModules.unit R) a L n
  asIso (eS hR (SheafOfModules.unit R) a L n) ≪≫ asIso (epsHom hR (L.X (a + n)))

/-- `eU` commutes with the differentials. -/
private lemma eU_comm (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexD hR (sing (SheafOfModules.unit R) a) L n ≫ (eU hR a L (n + 1)).hom =
      (eU hR a L n).hom ≫ L.d (a + n) (a + (n + 1)) := by
  simp only [eU, Iso.trans_hom, asIso_hom, ← Category.assoc, eS_comm]
  simp only [Category.assoc, homPost_epsHom]

/-- `eU` is natural in the target complex. -/
private lemma eU_nat (L L' : CochainComplex (Mod R) ℤ) (g : L ⟶ L') (n : ℤ) :
    (eU hR a L n).hom ≫ g.f (a + n) =
      postX hR (sing (SheafOfModules.unit R) a) g n ≫ (eU hR a L' n).hom := by
  simp only [eU, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [← homPost_epsHom, ← Category.assoc, ← Category.assoc, eS_nat]

/-- `𝓗om(R[-a], L) ≅ L` reindexed. -/
private def singIso (L : CochainComplex (Mod R) ℤ) :
    homSheafComplex hR (sing (SheafOfModules.unit R) a) L ≅ shiftIdx a L :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ eU hR a L n) (fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    have h : (homSheafComplex hR (sing (SheafOfModules.unit R) a) L).d i (i + 1) =
        homComplexD hR (sing (SheafOfModules.unit R) a) L i :=
      CochainComplex.of_d _ _ i
    rw [h]
    exact (eU_comm hR a L i).symm)

/-- `HomGood` for the complex `R[-a]`. -/
private lemma HomGood.single_unit : HomGood hR (sing (SheafOfModules.unit R) a) := by
  intro L L' g _
  have := quasiIso_shiftIdxMap a g
  refine (quasiIso_iff_of_arrow_mk_iso (homComplexMap₂ hR _ g) (shiftIdxMap a g)
    (Arrow.isoMk (singIso hR a L) (singIso hR a L') ?_)).2 this
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  exact eU_nat hR a L L' g n

/-- `HomGood` transfers along isomorphisms of the single term. -/
private lemma HomGood.sing_of_iso {M M' : Mod R} (e : M ≅ M') (h : HomGood hR (sing M' a)) :
    HomGood hR (sing M a) :=
  HomGood.of_retract hR h ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).map e.hom)
    ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).map e.inv) (by
      rw [← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id])

/-- `HomGood` for a single term which is a biproduct. -/
private lemma HomGood.sing_biprod {M M' : Mod R} (h : HomGood hR (sing M a))
    (h' : HomGood hR (sing M' a)) : HomGood hR (sing (M ⊞ M') a) := by
  let S0 : ShortComplex (Mod R) :=
    ShortComplex.mk (biprod.inl : M ⟶ M ⊞ M') biprod.snd (by simp)
  let sp : S0.Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct M M'
  have key : HomGood hR (S0.map (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a)).X₂ :=
    HomGood.of_ses hR (S0.map (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a))
      (fun n ↦ (sp.map (HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a)).map
        (HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n)) h h'
  exact key

end Single

/-- `HomGood` for a complex whose terms are all zero. -/
private lemma HomGood.of_isZero (hR : IsCommSheaf R) {P : CochainComplex (Mod R) ℤ}
    (hP : ∀ p, IsZero (P.X p)) : HomGood hR P := by
  intro L L' g _
  have hz : ∀ M : CochainComplex (Mod R) ℤ, IsZero (homSheafComplex hR P M) := fun M ↦ by
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    apply Pi.hom_ext
    intro T
    exact (isZero_homSheaf_left hR _ (hP T.p)).eq_of_tgt _ _
  have h0 : homComplexMap₂ hR P g = 0 := (hz L).eq_of_src _ _
  have : IsIso (homComplexMap₂ hR P g) := by
    rw [h0]
    exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hz L, hz L'⟩
  infer_instance

/-- `R^{m+1} ≅ R^m ⊞ R`. -/
private def freeSuccIso (m : ℕ) :
    (SheafOfModules.free (R := R) (Fin (m + 1))) ≅
      SheafOfModules.free (R := R) (Fin m) ⊞ SheafOfModules.unit R :=
  ((SheafOfModules.freeFunctor (R := R)).mapIso
      (finSumFinEquiv (m := m) (n := 1)).toIso).symm ≪≫
    (SheafOfModules.freeSumIso (R := R) (Fin m) (Fin 1)).symm ≪≫
    (biprod.isoCoprod _ _).symm ≪≫
    biprod.mapIso (Iso.refl _) (coproductUniqueIso (fun _ : Fin 1 ↦ SheafOfModules.unit R))

/-- `HomGood` for a single zero term. -/
private lemma HomGood.sing_of_isZero (hR : IsCommSheaf R) {M : Mod R} (a : ℤ) (hM : IsZero M) :
    HomGood hR (sing M a) := by
  refine HomGood.of_isZero hR fun p ↦ ?_
  by_cases hp : p = a
  · subst hp
    exact hM.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p M)
  · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hp

/-- `HomGood` for a single finite free term. -/
private lemma HomGood.sing_free (hR : IsCommSheaf R) (a : ℤ) (m : ℕ) :
    HomGood hR (sing (SheafOfModules.free (R := R) (Fin m)) a) := by
  induction m with
  | zero =>
    refine HomGood.sing_of_isZero hR a ?_
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro i
    exact i.elim0
  | succ m ih =>
    exact HomGood.sing_of_iso hR a (freeSuccIso m)
      (HomGood.sing_biprod hR a ih (HomGood.single_unit hR a))

/-- `HomGood` for a single term which is a direct summand of a finite free module. -/
private lemma HomGood.sing_of_isFinFreeSummand (hR : IsCommSheaf R) (a : ℤ) {M : Mod R}
    (hM : IsFinFreeSummand M) : HomGood hR (sing M a) := by
  obtain ⟨m, i, p, hip⟩ := hM
  exact HomGood.of_retract hR (HomGood.sing_free hR a m)
    ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).map i)
    ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) a).map p) (by
      rw [← Functor.map_comp, hip, CategoryTheory.Functor.map_id])

section Trunc

/-- Short complexes of complexes of sheaves of modules have homology (instance search does not
find the instance of an abelian category directly). -/
private instance categoryWithHomology_complex : CategoryWithHomology (CochainComplex (Mod R) ℤ) :=
  @categoryWithHomology_of_abelian (CochainComplex (Mod R) ℤ) _ _

variable (P : CochainComplex (Mod R) ℤ) (a : ℤ) [hGE : P.IsStrictlyGE a]

/-- The projection `P ⟶ Pᵃ[-a]` onto the lowest term of a complex in degrees `≥ a`. -/
private def truncπ : P ⟶ sing (P.X a) a :=
  HomologicalComplex.mkHomToSingle (𝟙 (P.X a)) fun i _ ↦ by
    by_cases hi : i < a
    · exact (CochainComplex.isZero_of_isStrictlyGE P a i hi).eq_of_src _ _
    · exfalso
      rename_i hr
      simp only [ComplexShape.up_Rel] at hr
      lia

/-- `truncπ` is an isomorphism in degree `a`. -/
private lemma isIso_truncπ_f_self : IsIso ((truncπ P a).f a) := by
  unfold truncπ
  rw [HomologicalComplex.mkHomToSingle_f]
  infer_instance

/-- The complex `M[-a]` is zero outside degree `a`. -/
private lemma isZero_sing_X {M : Mod R} (n : ℤ) (hn : n ≠ a) : IsZero ((sing M a).X n) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hn

/-- `truncπ` is degreewise epi. -/
private lemma epi_truncπ_f (n : ℤ) : Epi ((truncπ P a).f n) := by
  by_cases hn : n = a
  · subst hn
    have := isIso_truncπ_f_self P n
    infer_instance
  · exact (isZero_sing_X (M := P.X a) a n hn).epi _

/-- The short complex `ker π ⟶ P ⟶ Pᵃ[-a]`. -/
private def truncSES : ShortComplex (CochainComplex (Mod R) ℤ) :=
  ShortComplex.mk (kernel.ι (truncπ P a)) (truncπ P a) (kernel.condition _)

/-- The truncation sequence is short exact. -/
private lemma truncSES_shortExact : (truncSES P a).ShortExact where
  exact := by
    have : (truncSES P a).HasHomology := inferInstance
    exact ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := inferInstanceAs (Mono (kernel.ι (truncπ P a)))
  epi_g := HomologicalComplex.epi_of_epi_f _ fun n ↦ epi_truncπ_f P a n

/-- The degreewise splitting of `truncSES`. -/
private def truncSplit (n : ℤ) :
    ((truncSES P a).map (HomologicalComplex.eval (Mod R) (ComplexShape.up ℤ) n)).Splitting := by
  have hS := ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (truncSES_shortExact P a)) n
  by_cases hn : n = a
  · subst hn
    have h := isIso_truncπ_f_self P n
    exact ShortComplex.Splitting.ofExactOfSection _ hS.exact (@inv _ _ _ _ _ h)
      (@IsIso.inv_hom_id _ _ _ _ _ h) hS.mono_f
  · exact ShortComplex.Splitting.ofExactOfSection _ hS.exact 0
      ((isZero_sing_X a n hn).eq_of_src _ _) hS.mono_f

/-- The inclusion of the kernel of `truncπ` is degreewise mono. -/
private lemma mono_truncS_f (n : ℤ) : Mono ((kernel.ι (truncπ P a)).f n) :=
  ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (truncSES_shortExact P a) n).mono_f

/-- The kernel of `truncπ` is zero where `P` is. -/
private lemma isZero_truncS_X (n : ℤ) (h : IsZero (P.X n)) :
    IsZero ((kernel (truncπ P a)).X n) :=
  haveI := mono_truncS_f P a n
  IsZero.of_mono ((kernel.ι (truncπ P a)).f n) h

/-- The kernel of `truncπ` is zero in degree `a`. -/
private lemma isZero_truncS_X_self : IsZero ((kernel (truncπ P a)).X a) := by
  have := mono_truncS_f P a a
  have := isIso_truncπ_f_self P a
  refine IsZero.of_mono_eq_zero ((kernel.ι (truncπ P a)).f a) ?_
  have h : (kernel.ι (truncπ P a)).f a ≫ (truncπ P a).f a = 0 := by
    rw [← HomologicalComplex.comp_f, kernel.condition]
    rfl
  exact (cancel_mono ((truncπ P a).f a)).1 (by rw [h, zero_comp])

end Trunc

/-- Direct summands of finite free modules: closed under retracts. -/
private lemma IsFinFreeSummand.of_retract' {M N : Mod R} (ι : M ⟶ N) (π : N ⟶ M)
    (h : ι ≫ π = 𝟙 M) (hN : IsFinFreeSummand N) : IsFinFreeSummand M := by
  obtain ⟨m, i, p, hip⟩ := hN
  exact ⟨m, ι ≫ i, p ≫ π, by
    rw [Category.assoc, ← Category.assoc i, hip, Category.id_comp, h]⟩

/-- The projection of a complex concentrated in the single degree `a` onto its term is an
isomorphism. -/
private lemma isIso_truncπ_of_le (P : CochainComplex (Mod R) ℤ) (a : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE a] : IsIso (truncπ P a) := by
  have : ∀ i, IsIso ((truncπ P a).f i) := fun i ↦ by
    by_cases hi : i = a
    · subst hi
      exact isIso_truncπ_f_self P i
    · have hz : IsZero (P.X i) := by
        rcases lt_or_gt_of_ne hi with h | h
        · exact CochainComplex.isZero_of_isStrictlyGE P a i h
        · exact CochainComplex.isZero_of_isStrictlyLE P a i h
      have h0 : (truncπ P a).f i = 0 := hz.eq_of_src _ _
      rw [h0]
      exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨hz, isZero_sing_X a i hi⟩
  exact HomologicalComplex.Hom.isIso_of_components _

/-- `HomGood` for bounded complexes with terms direct summands of finite free modules, by induction
on the length (stupid truncation `0 → σ_{>a}P → P → Pᵃ[-a] → 0`). -/
private lemma HomGood.of_bounded (hR : IsCommSheaf R) (n : ℕ) :
    ∀ (a : ℤ) (P : CochainComplex (Mod R) ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE (a + n)],
      (∀ i, IsFinFreeSummand (P.X i)) → HomGood hR P := by
  induction n with
  | zero =>
    intro a P _ hLE hP
    have : P.IsStrictlyLE a := by simpa using hLE
    have := isIso_truncπ_of_le P a
    exact HomGood.of_retract hR (HomGood.sing_of_isFinFreeSummand hR a (hP a)) (truncπ P a)
      (inv (truncπ P a)) (IsIso.hom_inv_id _)
  | succ n ih =>
    intro a P _ hLE hP
    have hGE' : (kernel (truncπ P a)).IsStrictlyGE (a + 1) := by
      refine (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦ ?_
      by_cases hia : i = a
      · subst hia
        exact isZero_truncS_X_self P i
      · exact isZero_truncS_X P a i (CochainComplex.isZero_of_isStrictlyGE P a i (by lia))
    have hLE' : (kernel (truncπ P a)).IsStrictlyLE (a + 1 + n) := by
      refine (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦ ?_
      exact isZero_truncS_X P a i (CochainComplex.isZero_of_isStrictlyLE P (a + ↑(n + 1)) i
        (by push_cast; lia))
    have hS : ∀ i, IsFinFreeSummand ((kernel (truncπ P a)).X i) := fun i ↦
      IsFinFreeSummand.of_retract' ((kernel.ι (truncπ P a)).f i) (truncSplit P a i).r
        (truncSplit P a i).f_r (hP i)
    have h1 : HomGood hR (kernel (truncπ P a)) := ih (a + 1) _ hS
    have h3 : HomGood hR (sing (P.X a) a) := HomGood.sing_of_isFinFreeSummand hR a (hP a)
    exact HomGood.of_ses hR (truncSES P a) (truncSplit P a) h1 h3

end SiteHom

end SiteHelpers

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}} (hR : IsCommSheaf R)

open CochainComplex.HomComplex

/-- **S7.b′.** On any site, for `P` strictly perfect, `𝓗om(P, -)` preserves quasi-isomorphisms
(proof as `quasiIso_homComplexMap₂`: `𝓗om(Rᵐ, L) ≅ Lᵐ`, induction on the length of `P`). -/
theorem quasiIso_homComplexMap₂_site {P : CochainComplex (Mod R) ℤ} (hP : IsStrictlyPerfect P)
    {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') [QuasiIso g] :
    QuasiIso (homComplexMap₂ hR P g) := by
  obtain ⟨⟨a, b, hGE, hLE⟩, hfree⟩ := hP
  have : P.IsStrictlyLE (a + ((b - a).toNat : ℕ)) :=
    CochainComplex.isStrictlyLE_of_le P b _ (by lia)
  exact SiteHom.HomGood.of_bounded hR (b - a).toNat a P hfree L L' g

/-- **S7.c′.** On any site, for `I` bounded below whose terms restrict to injective objects over
every object `V`, `𝓗om(-, I)` maps quasi-isomorphisms to quasi-isomorphisms (proof as
`quasiIso_homComplexMap₁`: sectionwise, the sections over `V` are the Hom complex into the
K-injective `I|V`). -/
theorem quasiIso_homComplexMap₁_site {K K' : CochainComplex (Mod R) ℤ} (f : K' ⟶ K) [QuasiIso f]
    {I : CochainComplex (Mod R) ℤ} (n : ℤ) [I.IsStrictlyGE n]
    (hI : ∀ (V : C) (i : ℤ), Injective ((SheafOfModules.overFunctor.{0} R V).obj (I.X i))) :
    QuasiIso (homComplexMap₁ hR f I) := by
  refine quasiIso_of_sectionwise _ fun V => ?_
  obtain ⟨V⟩ := V
  have hq : QuasiIso ((overC V).map f) :=
    inferInstanceAs (QuasiIso (((SheafOfModules.overFunctor.{0} R V).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f))
  have : ∀ i, Injective (((overC V).obj I).X i) := fun i => hI V i
  have : ((overC V).obj I).IsStrictlyGE n :=
    (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi =>
      (SheafOfModules.overFunctor.{0} R V).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE I n i hi)
  have : ((overC V).obj I).IsKInjective :=
    CochainComplex.isKInjective_of_injective ((overC V).obj I) n
  have hpre := quasiIso_homComplexPrecomp' ((overC V).map f) ((overC V).obj I)
  have hsq : (SiteHom.secHomIso hR K I V).hom ≫
      homComplexPrecomp ((overC V).map f) ((overC V).obj I) =
      ((forget₂ (ModuleCat ↑(R.obj.obj (op V))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (((SheafOfModules.evaluation.{0} R (op V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (homComplexMap₁ hR f I)) ≫
        (SiteHom.secHomIso hR K' I V).hom := by
    refine HomologicalComplex.hom_ext _ _ fun m ↦ ?_
    ext z : 2
    funext T
    show (Cochain.ofHom ((overC V).map f)).comp (homComplexSectionsEquiv hR K I m V z)
      (zero_add m) T = homComplexSectionsEquiv hR K' I m V
        (((homComplexMap₁ hR f I).f m).val.app (op V) z) T
    rw [homComplexSectionsEquiv_apply]
    have h1 := congrArg (fun g ↦ ((g.val.app (op V)).hom z))
      (Limits.Pi.map_π (fun T : Triplet m ↦ homPre hR (f.f T.p) (I.X T.q)) T)
    have hl := Cochain.zero_cochain_comp_v (Cochain.ofHom ((overC V).map f))
      (homComplexSectionsEquiv hR K I m V z) T.p T.q T.hpq
    refine hl.trans (Eq.trans ?_ (congrArg (homSheafSectionsEquiv hR (K'.X T.p) (I.X T.q) V)
      h1.symm))
    rw [Cochain.ofHom_v]
    show (f.f T.p).over V ≫ homComplexSectionsEquiv hR K I m V z T = _
    erw [homComplexSectionsEquiv_apply]
    rfl
  refine (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat ↑(R.obj.obj (op V))) AddCommGrpCat)).1 ?_
  exact (quasiIso_iff_of_arrow_mk_iso _
    (homComplexPrecomp ((overC V).map f) ((overC V).obj I))
    (Arrow.isoMk (SiteHom.secHomIso hR K I V) (SiteHom.secHomIso hR K' I V) hsq)).2 hpre

/-- Restriction to an object `V` commutes with post-composition (`homSheafOverIso` is natural in
the target). -/
private lemma homSheafOverIso_post (M : Mod R) {N N' : Mod R} (g : N ⟶ N') (V : C) :
    (SheafOfModules.overFunctor.{0} R V).map (homPost hR M g) ≫
      (homSheafOverIso hR M N' V).hom =
    (homSheafOverIso hR M N V).hom ≫ homPost (hR.over V) (M.over V) (g.over V) := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext φ
  rfl

/-- `homComplexOverIso` is natural in the target. -/
theorem homComplexOverIso_naturality₂ (K : CochainComplex (Mod R) ℤ)
    {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') (V : C) :
    (overC V).map (homComplexMap₂ hR K g) ≫ (homComplexOverIso hR K L' V).hom =
      (homComplexOverIso hR K L V).hom ≫ homComplexMap₂ (hR.over V) ((overC V).obj K)
        ((overC V).map g) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  have hπ : ∀ (L : CochainComplex (Mod R) ℤ) (m : ℤ) (T' : Triplet m),
      (homComplexOverIso hR K L V).hom.f m ≫ Pi.π (fun T : Triplet m ↦
        homSheaf (hR.over V) (((overC V).obj K).X T.p) (((overC V).obj L).X T.q)) T' =
      (SheafOfModules.overFunctor.{0} R V).map (Pi.π (fun T : Triplet m ↦
        homSheaf hR (K.X T.p) (L.X T.q)) T') ≫
        (homSheafOverIso hR (K.X T'.p) (L.X T'.q) V).hom := by
    intro L m T'
    show (piComparison _ _ ≫ Limits.Pi.map
      (fun T : Triplet m ↦ (homSheafOverIso hR (K.X T.p) (L.X T.q) V).hom)) ≫ _ = _
    rw [Category.assoc]
    erw [Limits.Pi.map_π]
    rw [← Category.assoc, piComparison_comp_π]
  apply Pi.hom_ext
  intro T
  let F := SheafOfModules.overFunctor.{0} R V
  let I : ∀ L : CochainComplex (Mod R) ℤ, F.obj (homComplexX hR K L n) ⟶
      homComplexX (hR.over V) ((overC V).obj K) ((overC V).obj L) n :=
    fun L ↦ (homComplexOverIso hR K L V).hom.f n
  let Pm : homComplexX hR K L n ⟶ homComplexX hR K L' n := (homComplexMap₂ hR K g).f n
  let Pm' : homComplexX (hR.over V) ((overC V).obj K) ((overC V).obj L) n ⟶
      homComplexX (hR.over V) ((overC V).obj K) ((overC V).obj L') n :=
    (homComplexMap₂ (hR.over V) ((overC V).obj K) ((overC V).map g)).f n
  let πL' : homComplexX hR K L' n ⟶ homSheaf hR (K.X T.p) (L'.X T.q) :=
    Pi.π (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L'.X T.q)) T
  let πL : homComplexX hR K L n ⟶ homSheaf hR (K.X T.p) (L.X T.q) :=
    Pi.π (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)) T
  let π' : ∀ L : CochainComplex (Mod R) ℤ, homComplexX (hR.over V) ((overC V).obj K)
      ((overC V).obj L) n ⟶ homSheaf (hR.over V) (((overC V).obj K).X T.p)
      (((overC V).obj L).X T.q) := fun L ↦ Pi.π (fun T : Triplet n ↦
        homSheaf (hR.over V) (((overC V).obj K).X T.p) (((overC V).obj L).X T.q)) T
  have e1 : Pm ≫ πL' = πL ≫ homPost hR (K.X T.p) (g.f T.q) :=
    Limits.Pi.map_π (fun T : Triplet n ↦ homPost hR (K.X T.p) (g.f T.q)) T
  have e2 : Pm' ≫ π' L' = π' L ≫ homPost (hR.over V) (((overC V).obj K).X T.p)
      (((overC V).map g).f T.q) :=
    Limits.Pi.map_π (fun T : Triplet n ↦
      homPost (hR.over V) (((overC V).obj K).X T.p) (((overC V).map g).f T.q)) T
  have h1 : I L' ≫ π' L' = F.map πL' ≫ (homSheafOverIso hR (K.X T.p) (L'.X T.q) V).hom :=
    hπ L' n T
  have h2 : I L ≫ π' L = F.map πL ≫ (homSheafOverIso hR (K.X T.p) (L.X T.q) V).hom :=
    hπ L n T
  have h3 := homSheafOverIso_post hR (K.X T.p) (g.f T.q) V
  have m1 := F.map_comp Pm πL'
  have m2 := F.map_comp πL (homPost hR (K.X T.p) (g.f T.q))
  show (F.map Pm ≫ I L') ≫ π' L' = (I L ≫ Pm') ≫ π' L'
  rw [Category.assoc, Category.assoc, h1, e2, ← Category.assoc (I L), h2, ← Category.assoc,
    ← m1, e1, m2, Category.assoc, h3, Category.assoc]
  rfl

end Site

section Space

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X} (U : Opens X)

/-- Modules on the nested over-site `(Over U).over V` are modules on `Over V.left`
(as `overOverEquiv` in `Sheaf/Globalize/Locally.lean`, Mathlib's `Over.iteratedSliceEquiv`). -/
private def overOverEquiv' (V : Over U) :
    Mod ((R.over U).over V) ≌ Mod (R.over V.left) :=
  (SheafOfModules.pushforwardPushforwardEquivalence.{0} (Over.iteratedSliceEquiv V)
    (S := (R.over U).over V) (R := R.over V.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)).symm

/-- Restricting to `U` and then to `V` is restricting to `V.left`. -/
private def overOverEquivObjIso' (V : Over U) (M : Mod R) :
    (overOverEquiv' U V).functor.obj (((M.over U).over V)) ≅ M.over V.left :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl))

/-- Restrictions of injective sheaves on `X` to the over-site of `U` stay injective after
restricting further to any object `V` of the over-site (`(I|U)|V ≅ I|V.left`, S5.c). -/
theorem injective_overFunctor_restr (I : Mod R) [Injective I] (V : Over U) :
    Injective ((SheafOfModules.overFunctor.{0} (R.over U) V).obj ((restr R U).obj I)) := by
  have h1 : Injective ((restr R V.left).obj I) := inferInstance
  have h2 : Injective ((overOverEquiv' U V).functor.obj
      ((SheafOfModules.overFunctor.{0} (R.over U) V).obj ((restr R U).obj I))) :=
    Injective.of_iso (overOverEquivObjIso' U V I).symm h1
  have h3 := (overOverEquiv' U V).toAdjunction.map_injective _ h2
  exact Injective.of_iso ((overOverEquiv' U V).unitIso.app _).symm h3

end Space

end Cohesive
