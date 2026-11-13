import Cohesivemodules.Sheaf.Hom
import Cohesivemodules.Sheaf.Restriction
import Cohesivemodules.Sheaf.Derived
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

set_option linter.style.header false

/-!
# S7.b, S7.c (part 1): Hom complexes, precomposition, the predicate `HomGood`

Blueprint items S7.b and S7.c (§3). Split from `Sheaf/HomAcyclic.lean` for size only (CLAUDE.md:
"New work goes in small new files"); no mathematical change.

* Precomposition with a quasi-isomorphism on Mathlib's Hom complex into a K-injective complex,
  and the sections of `𝓗om(K, I)` as a Hom complex (used for S7.c).
* Functoriality of `𝓗om` in the first variable, the predicate `HomGood` (`𝓗om(P, -)` preserves
  quasi-isomorphisms) and its closure under retracts and degreewise split extensions (for S7.b).
-/

universe v u

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

open TopologicalSpace CochainComplex.HomComplex
open scoped ZeroObject

/-- Cocycles of the Hom complex from an acyclic complex to a K-injective one are coboundaries. -/
theorem coboundary_of_cocycle {A : Type u} [Category.{v} A] [Abelian A]
    (F G : CochainComplex A ℤ) (hF : F.Acyclic) [G.IsKInjective] (n m : ℤ) (hm : m + 1 = n)
    (z : Cochain F G n) (hz : δ n (n + 1) z = 0) : ∃ y : Cochain F G m, δ m n y = z := by
  let c : Cocycle F G n := ⟨z, (Cocycle.mem_iff n (n + 1) rfl z).2 hz⟩
  have h0 : CohomologyClass.toHom (CohomologyClass.mk c) = 0 := by
    rw [CohomologyClass.toHom_mk]
    rw [HomotopyCategory.eq_of_homotopy _ 0
      (CochainComplex.IsKInjective.homotopyZero (Cocycle.equivHomShift.symm c) hF),
      Functor.map_zero]
  obtain ⟨y, hy⟩ := ((mem_coboundaries_iff c m hm).1
    ((CohomologyClass.toHom_mk_eq_zero_iff c).1 h0))
  exact ⟨y, hy⟩

section
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- `Qh` of a quasi-isomorphism is invertible. -/
private lemma isIso_Qh_map {F' F : CochainComplex A ℤ} (f : F' ⟶ F) [QuasiIso f] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)) := by
  have hf := (DerivedCategory.quotientCompQhIso A).hom.naturality f
  simp only [Functor.comp_map] at hf
  have : IsIso (DerivedCategory.Q.map f) := inferInstance
  have h2 : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app F) := by
    rw [hf]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.quotientCompQhIso A).hom.app F)

/-- Precomposition with a quasi-isomorphism is bijective on maps in `Ho` into a K-injective. -/
private lemma bijective_precomp_ho {F' F L : CochainComplex A ℤ} (f : F' ⟶ F) [QuasiIso f]
    [L.IsKInjective] :
    Function.Bijective (fun x : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj F ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ↦
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f ≫ x) := by
  have h1 := CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj F) L
  have h2 := CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj F') L
  have := isIso_Qh_map f
  have h3 : Function.Bijective (fun y : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj F) ⟶ DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L) ↦
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) ≫ y) :=
    Function.bijective_iff_has_inverse.2 ⟨fun y ↦ inv (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)) ≫ y,
      fun y ↦ by simp, fun y ↦ by simp⟩
  have h4 : (DerivedCategory.Qh.map ∘
      (fun x : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj F ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ↦
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f ≫ x)) =
      (fun y ↦ DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f) ≫ y)
        ∘ DerivedCategory.Qh.map := by
    funext x; simp
  exact (Function.Bijective.of_comp_iff' h2 _).1 (by rw [h4]; exact h3.comp h1)

variable {F' F : CochainComplex A ℤ} (f : F' ⟶ F) (G : CochainComplex A ℤ) (n : ℤ)

/-- Precomposition of cocycles with `f`, additively. -/
private def precompHom : Cocycle F G n →+ Cocycle F' G n :=
  AddMonoidHom.mk' (fun z ↦ z.precomp f) (fun a b ↦ by
    ext1
    simp [Cochain.comp_add])

/-- Precomposition with `f` on cohomology classes. -/
private def cohMap : CohomologyClass F G n →+ CohomologyClass F' G n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom F' G n).comp (precompHom f G n)) (by
      rintro x ⟨m, hm, β, hβ⟩
      show CohomologyClass.mk (x.precomp f) = 0
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
      refine ⟨(Cochain.ofHom f).comp β (zero_add m), ?_⟩
      ext1
      simp [← hβ])

omit [HasDerivedCategory A] in
private lemma toHom_cohMap (c : CohomologyClass F G n) :
    CohomologyClass.toHom (cohMap f G n c) =
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f ≫ CohomologyClass.toHom c := by
  induction c with
  | mk x =>
    show CohomologyClass.toHom (CohomologyClass.mk (x.precomp f)) = _
    rw [CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_precomp,
      Functor.map_comp]

private lemma bijective_cohMap [QuasiIso f] [G.IsKInjective] :
    Function.Bijective (cohMap f G n) := by
  have h := bijective_precomp_ho (L := G⟦n⟧) f
  have e1 := CohomologyClass.toHom_bijective F G n
  have e2 := CohomologyClass.toHom_bijective F' G n
  have : (CohomologyClass.toHom ∘ cohMap f G n) = (fun x ↦ (HomotopyCategory.quotient A
      (ComplexShape.up ℤ)).map f ≫ x) ∘ CohomologyClass.toHom := by
    funext c; exact toHom_cohMap f G n c
  exact (Function.Bijective.of_comp_iff' e2 _).1 (by rw [this]; exact h.comp e1)

/-- Precomposition with `f` as a morphism of Hom complexes. -/
def homComplexPrecomp : CochainComplex.HomComplex F G ⟶ CochainComplex.HomComplex F' G where
  f i := AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun z : Cochain F G i ↦
    (Cochain.ofHom f).comp z (zero_add i)) (fun a b ↦ by simp [Cochain.comp_add]))
  comm' i j _ := by
    ext z
    exact δ_ofHom_comp f z j

private lemma quasiIso_homComplexPrecomp [QuasiIso f] [G.IsKInjective] :
    QuasiIso (homComplexPrecomp f G) := by
  refine ⟨fun i ↦ ?_⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let γ : ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ i).map (homComplexPrecomp f G))
      (leftHomologyData F G i) (leftHomologyData F' G i) :=
    { φK := AddCommGrpCat.ofHom (precompHom f G i)
      φH := AddCommGrpCat.ofHom (cohMap f G i)
      commi := by ext x; rfl
      commf' := by
        ext x
        apply Subtype.ext
        exact (δ_ofHom_comp f (K := G) (n := (ComplexShape.up ℤ).prev i) x i).symm
      commπ := by ext x; rfl }
  show IsIso (ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor _ _ i).map (homComplexPrecomp f G)))
  rw [γ.homologyMap_eq]
  have hb := bijective_cohMap f G i
  have : IsIso (AddCommGrpCat.ofHom (cohMap f G i)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance
end

/-- `homComplexPrecomp` is a quasi-isomorphism, without a chosen derived category. -/
lemma quasiIso_homComplexPrecomp' {A : Type u} [Category.{v} A] [Abelian A]
    {F' F : CochainComplex A ℤ} (f : F' ⟶ F) (G : CochainComplex A ℤ) [QuasiIso f]
    [G.IsKInjective] : QuasiIso (homComplexPrecomp f G) := by
  let _ := HasDerivedCategory.standard A
  exact quasiIso_homComplexPrecomp f G

/-- The complex of sections of `𝓗om(K, I)` over `V` (as abelian groups) is Mathlib's Hom complex
`HomComplex (K|V) (I|V)`. -/
def secHomIso (hR : IsCommSheaf R) (K I : CochainComplex (Mod R) ℤ) (V : Opens X) :
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
private lemma hom_ext_pt₀ {V : Opens X} {M N : Mod R} {φ ψ : M.over V ⟶ N.over V}
    (h : ∀ (Z : (Over V)ᵒᵖ) (m : (M.over V).val.obj Z),
      (φ.val.app Z).hom m = (ψ.val.app Z).hom m) : φ = ψ := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext m
  exact h Z m

/-- `homPre` of the identity. -/
lemma homPre_id' (hR : IsCommSheaf R) (M N : Mod R) :
    homPre hR (𝟙 M) N = 𝟙 _ := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt₀ fun Z m ↦ rfl)

/-- `homPre` is contravariantly functorial. -/
lemma homPre_comp' (hR : IsCommSheaf R) {M M' M'' : Mod R} (f : M' ⟶ M) (g : M'' ⟶ M')
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
lemma homPre_zero (hR : IsCommSheaf R) {M M' : Mod R} (N : Mod R) :
    homPre hR (0 : M' ⟶ M) N = 0 := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt₀ fun Z m ↦ by
    exact map_zero (φ.val.app Z).hom)

/-- `homPre` and `homPost` commute. -/
lemma homPre_homPost' (hR : IsCommSheaf R) {M M' N N' : Mod R} (f : M' ⟶ M)
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
def postX (hR : IsCommSheaf R) (K : CochainComplex (Mod R) ℤ)
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
def HomGood (hR : IsCommSheaf R) (P : CochainComplex (Mod R) ℤ) : Prop :=
  ∀ (L L' : CochainComplex (Mod R) ℤ) (g : L ⟶ L') [QuasiIso g],
    QuasiIso (homComplexMap₂ hR P g)

/-- `HomGood` passes to retracts of complexes. -/
lemma HomGood.of_retract (hR : IsCommSheaf R) {P F : CochainComplex (Mod R) ℤ}
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
lemma HomGood.of_ses (hR : IsCommSheaf R) (S : ShortComplex (CochainComplex (Mod R) ℤ))
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

end Cohesive
