import Cohesivemodules.Sheaf.Flat.KFlat

set_option linter.style.header false

/-!
# S8: tensor products and K-flat complexes

Blueprint item S8 (§3), tensor part (S8.a first half, S8.b–f). Base change along a map of
sheaves of rings (S8.a second half) and S8.g need a concrete model of extension of scalars and
are in a separate file (todo).

Rings: tensor products need commutative rings, so here the ring is a sheaf of commutative rings
`R : Sheaf J CommRingCat`, and modules are modules over its underlying sheaf of rings
`ringOf R` (conventions §7: convert with `forget₂`). Mathlib's monoidal structure on
presheaves of modules over a presheaf of commutative rings ✓ plus sheafification ✓; Mathlib has
no monoidal structure on `SheafOfModules` ✗, so only the tensor bifunctor is built.

* S8.a `tensorBifunctor R`: `M ⊗ N` = sheafification of the sectionwise tensor product;
  `tensorC R K L`: the total complex of `K ⊗ L` (Mathlib's `mapBifunctor`).
* `IsFlat R M`: `M ⊗ -` preserves monomorphisms; `IsKFlat R K`: `K ⊗ L` is acyclic for every
  acyclic `L` [Stacks, Def. of K-flat complexes].
* S8.b `R` and `j_! R|U` are flat; coproducts of flat modules are flat.
* S8.c every module is a quotient of a coproduct of modules `j_! R|U`.
* S8.d bounded-above complexes of flat modules are K-flat. The flat resolutions themselves are
  in `FlatResolution.lean`.
* S8.e for `K` K-flat, `K ⊗ -` preserves quasi-isomorphisms. The acyclicity of `K ⊗ L` for
  bounded-above `L` is in `FlatResolution.lean`.
* S8.f flatness restricts to opens; tensor products commute with restriction.

## Deviations
* S8.e is stated for bounded-above `L` (the resolution of S8.d is for bounded-above complexes);
  its uses (S8.g with `L = S`, C5 step 6) are bounded.
* S8.f is stated for flat modules (so for bounded-above complexes of flat modules, K-flat by
  S8.d), not for arbitrary K-flat complexes: C5 only applies it to the resolution of S8.d.

## Files
Split for size (CLAUDE.md: "New work goes in small new files"); this file holds the part on a
space (S8.c `exists_epi_sigma_extZero`, S8.f, `isFlat_extZero_unit`). The earlier parts are
* `Sheaf/Flat/TensorLoc.lean`: the `ℤ`-tensor product and local injectivity of `f ⊗ N`;
* `Sheaf/Flat/TotAux.lean`: total complexes of bifunctors;
* `Sheaf/Flat/Brutal.lean`: brutal truncations, filtered colimits of acyclic complexes;
* `Sheaf/Flat/Tensor.lean`: `tensorBifunctor`, `tensorC`, `IsFlat`, `IsKFlat`, `isFlat_unit`;
* `Sheaf/Flat/KFlat.lean`: `isFlat_sigma`, `isKFlat_of_isFlat`, `quasiIso_tensorCMap₂`.

Part 1 of 2 of the original `Sheaf/Flat.lean`, split for size; continued in
`Sheaf/Flat.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace

section SheafifyAux

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  (R : Sheaf J CommRingCat.{0})

/-- The unit `P ⟶ a P` of sheafification, with a clean type. -/
def unitR (P : PresheafOfModules.{0} (ringOf R).obj) :
    P ⟶ (SheafOfModules.forget (ringOf R)).obj ((sheafifyF R).obj P) :=
  (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.app P

/-- Naturality of `unitR`. -/
private lemma unitR_naturality {P P' : PresheafOfModules.{0} (ringOf R).obj} (φ : P ⟶ P') :
    φ ≫ unitR R P' = unitR R P ≫ (SheafOfModules.forget (ringOf R)).map ((sheafifyF R).map φ) :=
  (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).unit.naturality φ

/-- The counit `a M ⟶ M` of sheafification, with a clean type. -/
private def counitR (M : Mod (ringOf R)) :
    (sheafifyF R).obj ((SheafOfModules.forget (ringOf R)).obj M) ⟶ M :=
  (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit.app M

/-- Naturality of `counitR`. -/
private lemma counitR_naturality {M M' : Mod (ringOf R)} (f : M ⟶ M') :
    (sheafifyF R).map ((SheafOfModules.forget (ringOf R)).map f) ≫ counitR R M' =
      counitR R M ≫ f :=
  (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit.naturality f

/-- The counit of sheafification is an isomorphism. -/
private instance isIso_counitR (M : Mod (ringOf R)) : IsIso (counitR R M) :=
  NatIso.isIso_app_of_isIso
    (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).counit M

end SheafifyAux

section Space

variable {X : Type} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})

/-- The section of `M|V` (over the over-site) given by a section `s ∈ M(V)`. -/
private def secOver (S : RingSheaf X) (M : Mod S) (V : Opens X) (s : M.val.obj (op V)) :
    ((restr S V).obj M).sections :=
  PresheafOfModules.sectionsMk (M := ((restr S V).obj M).val)
    (fun W => mres M (leOfHom W.unop.hom) s) (by
      intro W W' f
      exact (M.val.map_comp_apply (homOfLE (leOfHom W.unop.hom)).op
        (homOfLE (leOfHom f.unop.left)).op s).symm)

/-- The map `j_! R|V ⟶ M` adjoint to `s : R|V ⟶ M|V`. -/
private def piOver (S : RingSheaf X) (M : Mod S) (V : Opens X) (s : M.val.obj (op V)) :
    (extZero S V).obj (SheafOfModules.unit (S.over V)) ⟶ M :=
  ((extZeroAdj S V).homEquiv _ _).symm
    ((SheafOfModules.unitHomEquiv _).symm (secOver S M V s))

/-- The section `s` is in the image of `piOver s` over `V`. -/
private lemma piOver_eval (S : RingSheaf X) (M : Mod S) (V : Opens X) (s : M.val.obj (op V)) :
    ∃ e : ((extZero S V).obj (SheafOfModules.unit (S.over V))).val.obj (op V),
      (piOver S M V s).val.app (op V) e = s := by
  have key : (extZeroAdj S V).unit.app (SheafOfModules.unit (S.over V)) ≫
      (restr S V).map (piOver S M V s) =
        (SheafOfModules.unitHomEquiv _).symm (secOver S M V s) := by
    have := ((extZeroAdj S V).homEquiv _ _).apply_symm_apply
      ((SheafOfModules.unitHomEquiv _).symm (secOver S M V s))
    rw [Adjunction.homEquiv_unit] at this
    exact this
  let one : ((SheafOfModules.unit (S.over V)).val.obj (op (Over.mk (𝟙 V)))) :=
    (1 : (S.over V).obj.obj (op (Over.mk (𝟙 V))))
  have h := congr(ModuleCat.Hom.hom ($(congrArg (fun m => m.val.app (op (Over.mk (𝟙 V)))) key))
    one)
  refine ⟨((extZeroAdj S V).unit.app (SheafOfModules.unit (S.over V))).val.app
    (op (Over.mk (𝟙 V))) one, ?_⟩
  refine h.trans ?_
  have h1 := congrArg (fun t => t.val (op (Over.mk (𝟙 V))))
    ((SheafOfModules.unitHomEquiv ((restr S V).obj M)).apply_symm_apply (secOver S M V s))
  refine (Eq.trans ?_ (h1.trans ?_))
  · rfl
  · show mres M (leOfHom (𝟙 V)) s = s
    exact congr($(M.val.presheaf.map_id (op V)) s)

/-- **S8.c.** Every module is a quotient of a coproduct of modules `j_! R|U`: one summand for
each open `U` and section `s ∈ M(U)`, mapped by the adjoint of `s : R|U ⟶ M|U`. -/
theorem exists_epi_sigma_extZero (M : Mod (ringOf R)) :
    ∃ (ι : Type) (U : ι → TopologicalSpace.Opens X)
      (π : (∐ fun i ↦ (extZero (ringOf R) (U i)).obj (SheafOfModules.unit _)) ⟶ M), Epi π := by
  refine ⟨Σ V : Opens X, M.val.obj (op V), fun i => i.1,
    Sigma.desc (fun i => piOver (ringOf R) M i.1 i.2), ⟨fun g k h => ?_⟩⟩
  have hi : ∀ i : (Σ V : Opens X, M.val.obj (op V)),
      piOver (ringOf R) M i.1 i.2 ≫ g = piOver (ringOf R) M i.1 i.2 ≫ k := fun i => by
    have := Sigma.ι (fun i : (Σ V : Opens X, M.val.obj (op V)) =>
      (extZero (ringOf R) i.1).obj (SheafOfModules.unit _)) i ≫= h
    simpa using this
  refine (SheafOfModules.fullyFaithfulForget _).map_injective ?_
  ext ⟨V⟩ s
  obtain ⟨e, he⟩ := piOver_eval (ringOf R) M V s
  have h2 := congr(ModuleCat.Hom.hom
    ($(congrArg (fun m => m.val.app (op V)) (hi ⟨V, s⟩))) e)
  show g.val.app (op V) s = k.val.app (op V) s
  rw [← he]
  exact h2

/-- Restriction of presheaves of modules to an open `U`. -/
private abbrev resPre (U : TopologicalSpace.Opens X) :
    PresheafOfModules.{0} (ringOf R).obj ⥤ PresheafOfModules.{0} (ringOf (R.over U)).obj :=
  PresheafOfModules.pushforward.{0} (𝟙 ((ringOf R).over U).obj)

/-- Restriction of sheaves of modules, with the target ring spelled `ringOf (R.over U)`. -/
private abbrev restrR (U : TopologicalSpace.Opens X) :
    Mod (ringOf R) ⥤ Mod (ringOf (R.over U)) :=
  restr (ringOf R) U

/-- The counit of sheafification over `U`, at a restricted sheaf. -/
private def counitRes (U : TopologicalSpace.Opens X)
    (P : PresheafOfModules.{0} (ringOf R).obj) :
    (sheafifyF (R.over U)).obj ((resPre R U).obj
      ((SheafOfModules.forget (ringOf R)).obj ((sheafifyF R).obj P))) ⟶
      (restrR R U).obj ((sheafifyF R).obj P) :=
  counitR (R.over U) ((restrR R U).obj ((sheafifyF R).obj P))

/-- Naturality of `counitRes`. -/
private lemma counitRes_naturality (U : TopologicalSpace.Opens X)
    {P P' : PresheafOfModules.{0} (ringOf R).obj} (φ : P ⟶ P') :
    (sheafifyF (R.over U)).map ((resPre R U).map
      ((SheafOfModules.forget (ringOf R)).map ((sheafifyF R).map φ))) ≫ counitRes R U P' =
      counitRes R U P ≫ (restrR R U).map ((sheafifyF R).map φ) :=
  counitR_naturality (R.over U) ((restrR R U).map ((sheafifyF R).map φ))

/-- The comparison `a_U (P|U) ⟶ (a P)|U`. -/
private def resSheafifyHom (U : TopologicalSpace.Opens X)
    (P : PresheafOfModules.{0} (ringOf R).obj) :
    (sheafifyF (R.over U)).obj ((resPre R U).obj P) ⟶
      (restrR R U).obj ((sheafifyF R).obj P) :=
  (sheafifyF (R.over U)).map ((resPre R U).map (unitR R P)) ≫ counitRes R U P

/-- Restriction commutes with sheafification: `a_U (P|U) ≅ (a P)|U`, because the unit
`P ⟶ a P` restricts to a locally bijective map. -/
private instance isIso_resSheafifyHom (U : TopologicalSpace.Opens X)
    (P : PresheafOfModules.{0} (ringOf R).obj) : IsIso (resSheafifyHom R U P) := by
  have hi : Presheaf.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf _).map ((resPre R U).map (unitR R P))) := by
    have h0 : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf _).map (unitR R P)) :=
      (inferInstance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
        (toSheafify _ P.presheaf))
    exact Presheaf.isLocallyInjective_whisker (H := Over.forget U)
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (unitR R P))
  have hs : Presheaf.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      ((PresheafOfModules.toPresheaf _).map ((resPre R U).map (unitR R P))) := by
    have h0 : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        ((PresheafOfModules.toPresheaf _).map (unitR R P)) :=
      (inferInstance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
        (toSheafify _ P.presheaf))
    exact Presheaf.isLocallySurjective_whisker (H := Over.forget U)
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (unitR R P))
  have := isIso_sheafifyF_map_of_locallyBijective (R.over U) ((resPre R U).map (unitR R P))
  have h2 : IsIso (counitRes R U P) := isIso_counitR (R.over U) _
  unfold resSheafifyHom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this h2

/-- Naturality of `resSheafifyHom`. -/
private lemma resSheafifyHom_naturality (U : TopologicalSpace.Opens X)
    {P P' : PresheafOfModules.{0} (ringOf R).obj} (φ : P ⟶ P') :
    (sheafifyF (R.over U)).map ((resPre R U).map φ) ≫ resSheafifyHom R U P' =
      resSheafifyHom R U P ≫ (restrR R U).map ((sheafifyF R).map φ) := by
  unfold resSheafifyHom
  have e1 : (sheafifyF (R.over U)).map ((resPre R U).map φ) ≫
      (sheafifyF (R.over U)).map ((resPre R U).map (unitR R P')) =
      (sheafifyF (R.over U)).map ((resPre R U).map (unitR R P)) ≫
      (sheafifyF (R.over U)).map ((resPre R U).map
        ((SheafOfModules.forget (ringOf R)).map ((sheafifyF R).map φ))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      unitR_naturality]
  rw [← Category.assoc, e1, Category.assoc, Category.assoc, counitRes_naturality]

/-- Restriction commutes with the sectionwise tensor product of presheaves of modules. -/
private def resTensorIso (U : TopologicalSpace.Opens X)
    (P N : PresheafOfModules.{0} (ringOf R).obj) :
    (resPre R U).obj (MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj) P N) ≅
      MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} (R.over U).obj)
        ((resPre R U).obj P) ((resPre R U).obj N) :=
  PresheafOfModules.isoMk (fun Y => Iso.refl _) (fun Y Z f => by rfl)

/-- Restriction commutes with sheafification, as an isomorphism. -/
private def resSheafifyIso (U : TopologicalSpace.Opens X)
    (P : PresheafOfModules.{0} (ringOf R).obj) :
    (sheafifyF (R.over U)).obj ((resPre R U).obj P) ≅ (restrR R U).obj ((sheafifyF R).obj P) :=
  @asIso _ _ _ _ (resSheafifyHom R U P) (isIso_resSheafifyHom R U P)

/-- Naturality of the inverse of `resSheafifyIso`. -/
private lemma resSheafifyIso_naturality_inv (U : TopologicalSpace.Opens X)
    {P P' : PresheafOfModules.{0} (ringOf R).obj} (φ : P ⟶ P') :
    (restrR R U).map ((sheafifyF R).map φ) ≫ (resSheafifyIso R U P').inv =
      (resSheafifyIso R U P).inv ≫ (sheafifyF (R.over U)).map ((resPre R U).map φ) := by
  rw [Iso.comp_inv_eq, Category.assoc]
  exact (Iso.eq_inv_comp _).2 (resSheafifyHom_naturality R U φ).symm

/-- A formal consequence of two commutative squares. -/
private lemma comp_eq_aux {𝒞 : Type*} [Category 𝒞] {x y s s' u u' : 𝒞} (A : x ⟶ y)
    (i : x ⟶ s) (i' : y ⟶ s') (F : s ⟶ s') (t : s ⟶ u) (t' : s' ⟶ u') (B : u ⟶ u')
    (h3 : A ≫ i' = i ≫ F) (h2 : F ≫ t' = t ≫ B) :
    A ≫ (i' ≫ t') = (i ≫ t) ≫ B := by
  rw [← Category.assoc, h3, Category.assoc, h2, Category.assoc]

/-- **S8.f.** Tensor products commute with restriction to an open: `(M ⊗ N)|U ≅ M|U ⊗ N|U`
(restriction commutes with sheafification and with the sectionwise tensor product). -/
def restrTensorIso (U : TopologicalSpace.Opens X) (M N : Mod (ringOf R)) :
    (restr (ringOf R) U).obj (((tensorBifunctor R).obj M).obj N) ≅
      ((tensorBifunctor (R.over U)).obj ((restr (ringOf R) U).obj M)).obj
        ((restr (ringOf R) U).obj N) :=
  (resSheafifyIso R U (MonoidalCategory.tensorObj
    (C := PresheafOfModulesOfCommRing.{0} R.obj) M.val N.val)).symm ≪≫
    (sheafifyF (R.over U)).mapIso (resTensorIso R U M.val N.val)

/-- Naturality of `resTensorIso` in the second variable. -/
private lemma resTensorIso_naturality (U : TopologicalSpace.Opens X)
    (P : PresheafOfModules.{0} (ringOf R).obj) {N N' : PresheafOfModules.{0} (ringOf R).obj}
    (g : N ⟶ N') :
    (resPre R U).map (MonoidalCategory.whiskerLeft
        (C := PresheafOfModulesOfCommRing.{0} R.obj) P g) ≫ (resTensorIso R U P N').hom =
      (resTensorIso R U P N).hom ≫ MonoidalCategory.whiskerLeft
        (C := PresheafOfModulesOfCommRing.{0} (R.over U).obj) ((resPre R U).obj P)
        ((resPre R U).map g) := by
  rfl

/-- Naturality of `resTensorIso` in the first variable. -/
private lemma resTensorIso_naturality₁ (U : TopologicalSpace.Opens X)
    {P P' : PresheafOfModules.{0} (ringOf R).obj} (g : P ⟶ P')
    (N : PresheafOfModules.{0} (ringOf R).obj) :
    (resPre R U).map (MonoidalCategory.whiskerRight
        (C := PresheafOfModulesOfCommRing.{0} R.obj) g N) ≫ (resTensorIso R U P' N).hom =
      (resTensorIso R U P N).hom ≫ MonoidalCategory.whiskerRight
        (C := PresheafOfModulesOfCommRing.{0} (R.over U).obj) ((resPre R U).map g)
        ((resPre R U).obj N) := by
  rfl

/-- **S8.f.** Naturality of `restrTensorIso` in the first variable (used in C5 via C7 for
`tensorC`). -/
theorem restrTensorIso_naturality₁ (U : TopologicalSpace.Opens X) {M M' : Mod (ringOf R)}
    (f : M ⟶ M') (N : Mod (ringOf R)) :
    (restr (ringOf R) U).map (((tensorBifunctor R).map f).app N) ≫
        (restrTensorIso R U M' N).hom =
      (restrTensorIso R U M N).hom ≫
        ((tensorBifunctor (R.over U)).map ((restr (ringOf R) U).map f)).app
          ((restr (ringOf R) U).obj N) := by
  have h1 := resSheafifyIso_naturality_inv R U
    (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} R.obj) f.val N.val)
  have h2 := resTensorIso_naturality₁ R U f.val N.val
  exact comp_eq_aux _ _ _ _ _ _ _ h1
    ((Functor.map_comp _ _ _).symm.trans ((congrArg _ h2).trans (Functor.map_comp _ _ _)))

/-- **S8.f.** Naturality of `restrTensorIso` in the second variable (public since v1.11; used in
C5 via C7). -/
theorem restrTensorIso_naturality (U : TopologicalSpace.Opens X) (M : Mod (ringOf R))
    {N N' : Mod (ringOf R)} (g : N ⟶ N') :
    (restr (ringOf R) U).map (((tensorBifunctor R).obj M).map g) ≫
        (restrTensorIso R U M N').hom =
      (restrTensorIso R U M N).hom ≫
        ((tensorBifunctor (R.over U)).obj ((restr (ringOf R) U).obj M)).map
          ((restr (ringOf R) U).map g) := by
  have h1 := resSheafifyIso_naturality_inv R U
    (MonoidalCategory.whiskerLeft (C := PresheafOfModulesOfCommRing.{0} R.obj) M.val g.val)
  have h2 := resTensorIso_naturality R U M.val g.val
  exact comp_eq_aux _ _ _ _ _ _ _ h1
    ((Functor.map_comp _ _ _).symm.trans ((congrArg _ h2).trans (Functor.map_comp _ _ _)))

end Space
end Cohesive
end
