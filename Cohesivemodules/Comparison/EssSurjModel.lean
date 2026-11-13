import Cohesivemodules.Comparison.ModelBC
import Cohesivemodules.Comparison.EssSurjAux
import Cohesivemodules.Algebra.LiftingCone
import Cohesivemodules.Sheaf.Flat
import Cohesivemodules.Sheaf.Acyclic

set_option linter.style.header false

/-!
# C5.a–c via the explicit model C7

Blueprint item C5 (§4, v1.11 "C5.a–c are proved via C7"). The model `T(K')` lives on the
over-site of `⊤`; the results are brought back to `X` by restriction to `⊤`, which is full on
complexes and detects quasi-isomorphisms.
* `exists_preimage_restrTop`, `quasiIso_of_restrTop`: restriction to `⊤`.
* `exists_restr_tensorC_iso`: restriction commutes with `tensorC` (S8.f, termwise
  `restrTensorIso`).
* `exists_restrTop_sheafOf_iso`: `α(M)|⊤ ≅ α_⊤(M)` (same sections).
* `exists_cohesive_gr0_quasiIso` (C5 steps 4–5 on `⊤`): with `N := N_{K'}(⊤)` (C7.c), `P = Γ(Pt)`
  and `e⁰ = Γ(f⁰)` (a quasi-isomorphism by S3, `𝒜⁰` fine), A11 gives `M` and a closed `e` whose
  `(0,0)`-component is `e⁰`; then `gr0Ξ e ≅ f⁰|⊤` (via `Γ`, S4.c), a quasi-isomorphism.

## Deviations
* None beyond those of C7 (blueprint v1.11).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

section Restr

variable {R : RingSheaf X}

/-- Components of a morphism `M|⊤ ⟶ N|⊤` at the objects `V ≤ ⊤` of the over-site. -/
private def topApp {M N : Mod R} (g : (restr R ⊤).obj M ⟶ (restr R ⊤).obj N)
    (V : (Opens X)ᵒᵖ) : M.val.presheaf.obj V ⟶ N.val.presheaf.obj V :=
  (PresheafOfModules.toPresheaf _ |>.map g.val).app (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤))))

/-- Naturality of `topApp`. -/
private theorem topApp_naturality {M N : Mod R} (g : (restr R ⊤).obj M ⟶ (restr R ⊤).obj N)
    {V W : (Opens X)ᵒᵖ} (f : V ⟶ W) :
    M.val.presheaf.map f ≫ topApp g W = topApp g V ≫ N.val.presheaf.map f :=
  (PresheafOfModules.toPresheaf _ |>.map g.val).naturality
    (Over.homMk f.unop : Over.mk (homOfLE (le_top : W.unop ≤ ⊤)) ⟶ Over.mk (homOfLE le_top)).op

/-- A morphism `M|⊤ ⟶ N|⊤` as a morphism `M ⟶ N` (`⊤` is terminal). -/
private def topHom {M N : Mod R} (g : (restr R ⊤).obj M ⟶ (restr R ⊤).obj N) : M ⟶ N :=
  ⟨PresheafOfModules.homMk (M₁ := M.val) (M₂ := N.val)
    { app := topApp g
      naturality := fun {_ _} f ↦ topApp_naturality g f }
    (fun V r m ↦ (g.val.app (op (Over.mk (homOfLE (le_top : V.unop ≤ ⊤))))).hom.map_smul r m)⟩

/-- `topHom` is a right inverse of restriction. -/
private theorem restr_topHom {M N : Mod R} (g : (restr R ⊤).obj M ⟶ (restr R ⊤).obj N) :
    (restr R ⊤).map (topHom g) = g := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun m ↦ ?_
  rfl

/-- `topHom` is a left inverse of restriction. -/
private theorem topHom_restr {M N : Mod R} (f : M ⟶ N) :
    topHom ((restr R ⊤).map f) = f := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V ↦ ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun m ↦ ?_
  rfl

/-- Restriction to `⊤` is full on complexes: a map of complexes of sheaves on the over-site of
`⊤` between restrictions comes from a map on `X` (sections over `V` are sections over
`V.left`). -/
theorem exists_preimage_restrTop {A B : CochainComplex (Mod R) ℤ}
    (g : ((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⟶
      ((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj B) :
    ∃ f : A ⟶ B, ((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map f = g := by
  refine ⟨{ f := fun n ↦ topHom (g.f n), comm' := ?_ }, ?_⟩
  · intro i j hij
    have h := g.comm i j
    have e1 : ∀ {M N : Mod R} (f : M ⟶ N), topHom ((restr R ⊤).map f) = f := fun f ↦
      topHom_restr f
    rw [← e1 (topHom (g.f i) ≫ B.d i j), ← e1 (A.d i j ≫ topHom (g.f j))]
    simp only [Functor.map_comp, restr_topHom]
    exact congrArg topHom h
  · refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    exact restr_topHom (g.f n)

/-- A map of complexes whose restriction to `⊤` is a quasi-isomorphism is one (S6). -/
theorem quasiIso_of_restrTop {A B : CochainComplex (Mod R) ℤ} (f : A ⟶ B)
    (h : QuasiIso (((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :
    QuasiIso f :=
  quasiIso_of_locally f fun _ => ⟨⊤, trivial, h⟩

end Restr

section TotMapIso

open Limits HomologicalComplex

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  (G : C ⥤ D) [G.Additive] (F : C ⥤ C ⥤ C) (F' : D ⥤ D ⥤ D)
  [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
  [F'.PreservesZeroMorphisms] [∀ X, (F'.obj X).PreservesZeroMorphisms]
  (e : ∀ M N, G.obj ((F.obj M).obj N) ≅ (F'.obj (G.obj M)).obj (G.obj N))
  (K L : CochainComplex C ℤ)
  [HasMapBifunctor K L F (ComplexShape.up ℤ)]
  [HasMapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
    (ComplexShape.up ℤ)]

/-- The comparison `K ⊗' L → G(K ⊗ L)` on total complexes, in degree `n`. -/
private def totMapψ (n : ℤ) :
    (mapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
      (ComplexShape.up ℤ)).X n ⟶ G.obj ((mapBifunctor K L F (ComplexShape.up ℤ)).X n) :=
  mapBifunctorDesc (fun p q h => (e (K.X p) (L.X q)).inv ≫
    G.map (ιMapBifunctor K L F (ComplexShape.up ℤ) p q n h))

/-- `ι` followed by `totMapψ`. -/
private lemma ι_totMapψ (p q n : ℤ) (h : p + q = n) :
    ιMapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
      (ComplexShape.up ℤ) p q n h ≫ totMapψ G F F' e K L n =
    (e (K.X p) (L.X q)).inv ≫ G.map (ιMapBifunctor K L F (ComplexShape.up ℤ) p q n h) :=
  ι_mapBifunctorDesc _ p q h

/-- `ιOrZero` followed by `totMapψ`. -/
private lemma ιOrZero_totMapψ (p q n : ℤ) :
    ιMapBifunctorOrZero ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
      (ComplexShape.up ℤ) p q n ≫ totMapψ G F F' e K L n =
    (e (K.X p) (L.X q)).inv ≫ G.map (ιMapBifunctorOrZero K L F (ComplexShape.up ℤ) p q n) := by
  by_cases h : p + q = n
  · rw [ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h, ιMapBifunctorOrZero_eq _ _ _ _ _ _ _ h]
    exact ι_totMapψ G F F' e K L p q n h
  · rw [ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h, ιMapBifunctorOrZero_eq_zero _ _ _ _ _ _ _ h]
    simp only [zero_comp, Functor.map_zero, comp_zero]

variable
  (he₁ : ∀ {M M' : C} (f : M ⟶ M') (N : C),
    G.map ((F.map f).app N) ≫ (e M' N).hom = (e M N).hom ≫ (F'.map (G.map f)).app (G.obj N))
  (he₂ : ∀ (M : C) {N N' : C} (g : N ⟶ N'),
    G.map ((F.obj M).map g) ≫ (e M N').hom = (e M N).hom ≫ (F'.obj (G.obj M)).map (G.map g))

include he₁ in
/-- `totMapψ` is compatible with the first differential. -/
private lemma d₁_totMapψ (p q n : ℤ) :
    mapBifunctor.d₁ ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
      (ComplexShape.up ℤ) p q (n + 1) ≫ totMapψ G F F' e K L (n + 1) =
    (e (K.X p) (L.X q)).inv ≫ G.map (mapBifunctor.d₁ K L F (ComplexShape.up ℤ) p q (n + 1)) := by
  have r1 : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
  rw [mapBifunctor.d₁_eq' _ _ _ _ r1, mapBifunctor.d₁_eq' _ _ _ _ r1]
  simp only [Linear.units_smul_comp, Category.assoc, ιOrZero_totMapψ,
    Functor.map_units_smul, Functor.map_comp, Linear.comp_units_smul]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, he₁ (K.d p (p + 1)) (L.X q), Iso.inv_hom_id_assoc]
  rfl

include he₂ in
/-- `totMapψ` is compatible with the second differential. -/
private lemma d₂_totMapψ (p q n : ℤ) :
    mapBifunctor.d₂ ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
      (ComplexShape.up ℤ) p q (n + 1) ≫ totMapψ G F F' e K L (n + 1) =
    (e (K.X p) (L.X q)).inv ≫ G.map (mapBifunctor.d₂ K L F (ComplexShape.up ℤ) p q (n + 1)) := by
  have r2 : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
  rw [mapBifunctor.d₂_eq' _ _ _ _ p r2, mapBifunctor.d₂_eq' _ _ _ _ p r2]
  simp only [Linear.units_smul_comp, Category.assoc, ιOrZero_totMapψ,
    Functor.map_units_smul, Linear.comp_units_smul, Functor.map_comp]
  congr 1
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, he₂ (K.X p) (L.d q (q + 1)), Iso.inv_hom_id_assoc]
  rfl

include he₁ he₂ in
/-- `totMapψ` is a chain map. -/
private lemma totMapψ_comm (n : ℤ) :
    (mapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
      (ComplexShape.up ℤ)).d n (n + 1) ≫ totMapψ G F F' e K L (n + 1) =
    totMapψ G F F' e K L n ≫ G.map ((mapBifunctor K L F (ComplexShape.up ℤ)).d n (n + 1)) := by
  refine mapBifunctor.hom_ext fun p q h => ?_
  rw [← Category.assoc, mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂, Preadditive.add_comp, d₁_totMapψ G F F' e K L he₁,
    d₂_totMapψ G F F' e K L he₂, ← Category.assoc, ι_totMapψ G F F' e K L p q n h,
    Category.assoc, ← G.map_comp, mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂, G.map_add, Preadditive.comp_add]

section Iso

variable [∀ ι : Type, PreservesColimitsOfShape (Discrete ι) G]

omit [Preadditive D] [G.Additive] in
/-- Extensionality for maps out of `G` of a total complex (`G` preserves coproducts). -/
private lemma totMap_hom_ext (n : ℤ) {Y : D}
    {f g : G.obj ((mapBifunctor K L F (ComplexShape.up ℤ)).X n) ⟶ Y}
    (h : ∀ (p q : ℤ) (hpq : p + q = n),
      G.map (ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq) ≫ f =
        G.map (ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq) ≫ g) : f = g :=
  IsColimit.hom_ext
    (isColimitOfPreserves G
      ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj
        L).toGradedObject.isColimitCofanMapObj
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n))
    (fun j => by
      obtain ⟨⟨⟨p, q⟩, hpq⟩⟩ := j
      exact h p q hpq)

/-- `G` applied to the coproduct cofan of the total complex is a colimit. -/
private def totColim (n : ℤ) :
    IsColimit (G.mapCocone
      ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj
        L).toGradedObject.cofanMapObj
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)) :=
  isColimitOfPreserves G
      ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj
        L).toGradedObject.isColimitCofanMapObj
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)

/-- The cocone used to define `totMapφ`. -/
private def totCocone (n : ℤ) :
    Cocone (Discrete.functor
      ((((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj
        L).toGradedObject.mapObjFun
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n) ⋙ G)
    where
  pt := (mapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
        (ComplexShape.up ℤ)).X n
  ι := Discrete.natTrans (fun ⟨⟨⟨p, q⟩, hpq⟩⟩ => (e (K.X p) (L.X q)).hom ≫
      ιMapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
        (ComplexShape.up ℤ) p q n hpq)

/-- The inverse of `totMapψ`, from the preserved coproduct. -/
private def totMapφ (n : ℤ) :
    G.obj ((mapBifunctor K L F (ComplexShape.up ℤ)).X n) ⟶
      (mapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
        (ComplexShape.up ℤ)).X n :=
  (totColim G F K L n).desc (totCocone G F F' e K L n)

/-- `G ι` followed by `totMapφ`. -/
private lemma ι_totMapφ (p q n : ℤ) (hpq : p + q = n) :
    G.map (ιMapBifunctor K L F (ComplexShape.up ℤ) p q n hpq) ≫ totMapφ G F F' e K L n =
    (e (K.X p) (L.X q)).hom ≫
      ιMapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
        (ComplexShape.up ℤ) p q n hpq :=
  (totColim G F K L n).fac (totCocone G F F' e K L n) ⟨⟨⟨p, q⟩, hpq⟩⟩

/-- `totMapψ ≫ totMapφ = 𝟙`. -/
private lemma totMapψ_φ (n : ℤ) : totMapψ G F F' e K L n ≫ totMapφ G F F' e K L n = 𝟙 _ := by
  refine mapBifunctor.hom_ext fun p q h => ?_
  rw [← Category.assoc, ι_totMapψ G F F' e K L p q n h, Category.assoc,
    ι_totMapφ G F F' e K L p q n h, Iso.inv_hom_id_assoc, Category.comp_id]

/-- `totMapφ ≫ totMapψ = 𝟙`. -/
private lemma totMapφ_ψ (n : ℤ) : totMapφ G F F' e K L n ≫ totMapψ G F F' e K L n = 𝟙 _ := by
  refine totMap_hom_ext G F K L n fun p q hpq => ?_
  rw [← Category.assoc, ι_totMapφ G F F' e K L p q n hpq, Category.assoc,
    ι_totMapψ G F F' e K L p q n hpq, Iso.hom_inv_id_assoc, Category.comp_id]

include he₁ he₂ in
/-- A natural isomorphism `G (F M N) ≅ F' (G M) (G N)`, for `G` preserving coproducts, induces
an isomorphism of total complexes `G (K ⊗ L) ≅ G K ⊗' G L`. -/
private def totMapIso :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (mapBifunctor K L F (ComplexShape.up ℤ)) ≅
      mapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L) F'
        (ComplexShape.up ℤ) :=
  let iso : mapBifunctor ((G.mapHomologicalComplex _).obj K) ((G.mapHomologicalComplex _).obj L)
        F' (ComplexShape.up ℤ) ≅
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (mapBifunctor K L F (ComplexShape.up ℤ)) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => ⟨totMapψ G F F' e K L n, totMapφ G F F' e K L n, totMapψ_φ G F F' e K L n,
        totMapφ_ψ G F F' e K L n⟩)
      (fun i j hij => by
        obtain rfl : i + 1 = j := hij
        exact (totMapψ_comm G F F' e K L he₁ he₂ i).symm)
  iso.symm

end Iso

end TotMapIso

/-- `restr` with the target spelled with the over-site ring sheaf `ringOf (R.over U)`. -/
private abbrev restrO (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}) (U : Opens X) :
    Mod (ringOf R) ⥤ Mod (ringOf (R.over U)) :=
  restr (ringOf R) U

private instance (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}) (U : Opens X) :
    (restrO R U).Additive where
  map_add := rfl

private instance (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}) (U : Opens X)
    (ι : Type) : Limits.PreservesColimitsOfShape (Discrete ι) (restrO R U) :=
  (inferInstance : Limits.PreservesColimitsOfShape (Discrete ι) (restr (ringOf R) U))

/-- Naturality of `restrTensorIso` in the first variable (S8.f; `restrTensorIso_naturality₁`,
restated with `restrO`). -/
private theorem restrTensorIso_nat₁ (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})
    (U : Opens X) {M M' : Mod (ringOf R)} (f : M ⟶ M') (N : Mod (ringOf R)) :
    (restrO R U).map (((tensorBifunctor R).map f).app N) ≫
        (restrTensorIso R U M' N).hom =
      (restrTensorIso R U M N).hom ≫
        ((tensorBifunctor (R.over U)).map ((restrO R U).map f)).app
          ((restrO R U).obj N) :=
  restrTensorIso_naturality₁ R U f N

/-- Naturality of `restrTensorIso` in the second variable (S8.f; `restrTensorIso_naturality`,
restated with `restrO`). -/
private theorem restrTensorIso_nat₂ (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})
    (U : Opens X) (M : Mod (ringOf R)) {N N' : Mod (ringOf R)} (g : N ⟶ N') :
    (restrO R U).map (((tensorBifunctor R).obj M).map g) ≫
        (restrTensorIso R U M N').hom =
      (restrTensorIso R U M N).hom ≫
        ((tensorBifunctor (R.over U)).obj ((restrO R U).obj M)).map
          ((restrO R U).map g) :=
  restrTensorIso_naturality R U M g

/-- **S8.f for complexes.** Restriction to an open commutes with `tensorC` (termwise
`restrTensorIso`, compatible with the differentials). -/
theorem exists_restr_tensorC_iso (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})
    (U : Opens X) (K L : CochainComplex (Mod (ringOf R)) ℤ) :
    Nonempty (((restr (ringOf R) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (tensorC R K L) ≅
      tensorC (R.over U) (((restr (ringOf R) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (((restr (ringOf R) U).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :=
  ⟨totMapIso (restrO R U) (tensorBifunctor R) (tensorBifunctor (R.over U))
    (restrTensorIso R U) K L (restrTensorIso_nat₁ R U) (restrTensorIso_nat₂ R U)⟩

namespace PreResolvingData

variable (P : PreResolvingData X)

/-- The termwise comparison `α(M)^n|⊤ ≅ α_⊤(M)^n` (same sections). -/
private def restrTopIsoSh (M : CohesiveModule P.𝒜X) (n : ℤ) :
    (restr P.R ⊤).obj (P.sheafOfSh M n) ≅ P.sheafOfOverSh ⊤ M n :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => Iso.refl _) (fun V W f => by rfl))

/-- `α(M)|⊤ ≅ α_⊤(M)`: over `V` both have sections `α(M)^n(V.left)` (the same type: `sheafOfSec`
with two proofs of `V.left ≤ ⊤`) and the same restrictions and differentials. -/
theorem exists_restrTop_sheafOf_iso (M : CohesiveModule P.𝒜X) :
    Nonempty (((restr P.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P.sheafOf M) ≅
      P.sheafOfOver ⊤ M) := by
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n => P.restrTopIsoSh M n) ?_⟩
  intro i j hij
  obtain rfl : i + 1 = j := hij
  have e1 : (P.sheafOfOver ⊤ M).d i (i + 1) = P.sheafOfOverD ⊤ M i := CochainComplex.of_d _ _ _
  have e2 : (P.sheafOf M).d i (i + 1) = P.sheafOfD M i := CochainComplex.of_d _ _ _
  have e3 : (((restr P.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P.sheafOf M)).d i
      (i + 1) = (restr P.R ⊤).map (P.sheafOfD M i) := by
    change (restr P.R ⊤).map ((P.sheafOf M).d i (i + 1)) = _
    rw [e2]
    rfl
  rw [e1, e3]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  rfl

end PreResolvingData

-- C5 steps 4–5 on `⊤` (`exists_cohesive_gr0_quasiIso`) are in `EssSurjCore.lean` (split for
-- size, v1.11).

end Cohesive
