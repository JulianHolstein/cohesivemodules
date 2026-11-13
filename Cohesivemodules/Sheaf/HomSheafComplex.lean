import Cohesivemodules.Sheaf.Hom.Basic

set_option linter.style.header false

/-!
# S7: Hom sheaves (Hom complexes)

Blueprint item S7 (§3). The first part (the Hom sheaf `homSheaf hR M N`, with sections over `X`
the morphisms `M|X ⟶ N|X`, `R(X)` acting through the target) is in `Sheaf/Hom/Basic.lean`; see
its module docstring for conventions and deviations. Split for size only (no statement changes).

This file: for complexes `K`, `L`, `homSheafComplex hR K L` with
`homSheafComplex(K, L)ⁿ = ∏_{p + n = q} homSheaf (Kᵖ) (L^q)` and Mathlib's sign convention
`δ z = z ≫ d + (-1)^{n+1} d ≫ z` (conventions §2, `CochainComplex.HomComplex.δ`); functoriality
`homComplexMap₁/₂`; sections `homComplexSectionsEquiv` (+ `_d`); restriction
`homSheafOverIso`, `homComplexOverIso`. S7.b and S7.c are in `Sheaf/HomAcyclic.lean`.

Part 1 of 2 of the original `Sheaf/Hom.lean`, split for size; continued in
`Sheaf/Hom.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}}

open CochainComplex.HomComplex in
/-- **S7.** Degree `n` of the Hom complex: `∏_{p + n = q} homSheaf (Kᵖ) (L^q)`, indexed by
Mathlib's `Triplet n` as for `Cochain K L n`. -/
abbrev homComplexX (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ) : Mod R :=
  ∏ᶜ fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)

open CochainComplex.HomComplex in
/-- **S7.** The differential of the Hom complex, with Mathlib's sign
(`CochainComplex.HomComplex.δ`, conventions §2): the component at `p + (n+1) = q` is
`φ_{p, p+n} ≫ d_L + (-1)^{n+1} d_K ≫ φ_{p+1, q}`. -/
def homComplexD (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexX hR K L n ⟶ homComplexX hR K L (n + 1) :=
  Pi.lift fun T : Triplet (n + 1) ↦
    Pi.π (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)) ⟨T.p, T.p + n, rfl⟩ ≫
        homPost hR (K.X T.p) (L.d (T.p + n) T.q) +
      (n + 1).negOnePow •
        (Pi.π (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q))
            ⟨T.p + 1, T.q, by have := T.hpq; lia⟩ ≫
          homPre hR (K.d T.p (T.p + 1)) (L.X T.q))

/-- Restriction to the over-site `Over X` is additive. -/
instance overFunctor_additive (X : C) : (SheafOfModules.overFunctor.{0} R X).Additive where
  map_add := rfl

open CochainComplex.HomComplex in
/-- Sections of the degree-`n` term of the Hom complex over `X` as cochains `K|X → L|X`
(private form of `homComplexSectionsEquiv`, available before `homSheafComplex`). -/
private def secEquiv (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ) (X : C) :
    (homComplexX hR K L n).val.obj (op X) ≃+
      Cochain (((SheafOfModules.overFunctor.{0} R X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) (((SheafOfModules.overFunctor.{0} R X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) n :=
  ((asIso (piComparison (SheafOfModules.evaluation.{0} R (op X))
      fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q))) ≪≫
    ModuleCat.piIsoPi _).toLinearEquiv.toAddEquiv

open CochainComplex.HomComplex in
/-- The component of `secEquiv` at a triplet is the projection to that factor. -/
private lemma secEquiv_apply (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ)
    (X : C) (s : (homComplexX hR K L n).val.obj (op X)) (T : Triplet n) :
    secEquiv hR K L n X s T =
      (homSheafSectionsEquiv hR (K.X T.p) (L.X T.q) X)
        (((Pi.π (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)) T).val.app (op X)).hom s) :=
  by
  have h1 := congrArg (fun f ↦ ModuleCat.Hom.hom f
    (ModuleCat.Hom.hom (piComparison (SheafOfModules.evaluation.{0} R (op X))
      fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)) s))
    (ModuleCat.piIsoPi_hom_ker_subtype
      (fun T : Triplet n ↦ (homSheaf hR (K.X T.p) (L.X T.q)).val.obj (op X)) T)
  have h2 := congrArg (fun f ↦ ModuleCat.Hom.hom f s)
    (piComparison_comp_π (SheafOfModules.evaluation.{0} R (op X))
      (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)) T)
  exact h1.trans h2

/-- Evaluation at an object is additive. -/
private instance evaluation_additive_aux (X : Cᵒᵖ) :
    (SheafOfModules.evaluation.{0} R X).Additive where
  map_add := rfl

/-- Sections of a sum of morphisms of sheaves of modules. -/
private lemma add_app_apply' {A B : Mod R} (f g : A ⟶ B) (X : C) (s : A.val.obj (op X)) :
    ((f + g).val.app (op X)).hom s = (f.val.app (op X)).hom s + (g.val.app (op X)).hom s :=
  rfl

/-- Sections of a `ℤˣ`-multiple of a morphism of sheaves of modules. -/
private lemma units_smul_app_apply {A B : Mod R} (z : ℤˣ) (f : A ⟶ B) (X : C)
    (s : A.val.obj (op X)) :
    ((z • f).val.app (op X)).hom s = z • (f.val.app (op X)).hom s := by
  have h : (SheafOfModules.evaluation.{0} R (op X)).map ((z : ℤ) • f) =
      (z : ℤ) • (SheafOfModules.evaluation.{0} R (op X)).map f := Functor.map_zsmul _
  rw [Units.smul_def, Units.smul_def]
  exact congrArg (fun g : A.val.obj (op X) ⟶ B.val.obj (op X) ↦ g.hom s) h

open CochainComplex.HomComplex in
/-- S7: the components of `homComplexD`: the `T`-component of `d φ` is
`d_L ∘ φ + (-1)^{n+1} φ ∘ d_K` (`CochainComplex.HomComplex.δ`). -/
lemma homComplexD_π (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ)
    (T : Triplet (n + 1)) :
    homComplexD hR K L n ≫ Pi.π (fun T : Triplet (n + 1) ↦ homSheaf hR (K.X T.p) (L.X T.q)) T =
      Pi.π (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)) ⟨T.p, T.p + n, rfl⟩ ≫
          homPost hR (K.X T.p) (L.d (T.p + n) T.q) +
        (n + 1).negOnePow •
          (Pi.π (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q))
              ⟨T.p + 1, T.q, by have := T.hpq; lia⟩ ≫
            homPre hR (K.d T.p (T.p + 1)) (L.X T.q)) :=
  Pi.lift_comp_π _ _

open CochainComplex.HomComplex in
/-- Under `secEquiv`, `homComplexD` on sections is Mathlib's `δ`. -/
private lemma secEquiv_D (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ)
    (X : C) (s : (homComplexX hR K L n).val.obj (op X)) :
    secEquiv hR K L (n + 1) X (((homComplexD hR K L n).val.app (op X)).hom s) =
      δ n (n + 1) (secEquiv hR K L n X s) := by
  funext T
  rw [secEquiv_apply]
  show homSheafSectionsEquiv hR (K.X T.p) (L.X T.q) X
    ((((homComplexD hR K L n) ≫ Pi.π (fun T : Triplet (n + 1) ↦
      homSheaf hR (K.X T.p) (L.X T.q)) T).val.app (op X)).hom s) = _
  rw [homComplexD_π]
  have hv := δ_v n (n + 1) rfl (secEquiv hR K L n X s) T.p T.q T.hpq (T.p + n) (T.p + 1)
    (by have := T.hpq; lia) rfl
  have hv' : δ n (n + 1) (secEquiv hR K L n X s) T =
      (show (K.X T.p).over X ⟶ (L.X T.q).over X from
        secEquiv hR K L n X s ⟨T.p, T.p + n, rfl⟩ ≫ (L.d (T.p + n) T.q).over X) +
        (n + 1).negOnePow • (show (K.X T.p).over X ⟶ (L.X T.q).over X from
          (K.d T.p (T.p + 1)).over X ≫
            secEquiv hR K L n X s ⟨T.p + 1, T.q, by have := T.hpq; lia⟩) := hv
  rw [hv', secEquiv_apply, secEquiv_apply, add_app_apply', units_smul_app_apply]
  rfl

lemma homComplexD_comp (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    homComplexD hR K L n ≫ homComplexD hR K L (n + 1) = 0 := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro X
  ext s
  obtain ⟨X⟩ := X
  apply (secEquiv hR K L (n + 1 + 1) X).injective
  have h := (secEquiv_D hR K L (n + 1) X (((homComplexD hR K L n).val.app (op X)).hom s)).trans
    (congrArg (CochainComplex.HomComplex.δ (n + 1) (n + 1 + 1)) (secEquiv_D hR K L n X s))
  refine h.trans ((CochainComplex.HomComplex.δ_δ _ _ _ _).trans ?_)
  exact (map_zero (secEquiv hR K L (n + 1 + 1) X)).symm

/-- **S7. The Hom complex** `𝓗om(K, L)` of two complexes of sheaves of `R`-modules, a complex of
sheaves of `R`-modules (`R` commutative): sections over `X` are the cochains `K|X → L|X`
(`homComplexSectionsEquiv`), with Mathlib's differential `δ`. -/
def homSheafComplex (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) :
    CochainComplex (Mod R) ℤ :=
  CochainComplex.of (homComplexX hR K L) (homComplexD hR K L) (homComplexD_comp hR K L)

/-- The differential of `homSheafComplex` in degree `n` is `homComplexD`. -/
lemma homComplex_d (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    (homSheafComplex hR K L).d n (n + 1) = homComplexD hR K L n :=
  CochainComplex.of_d (homComplexX hR K L) (homComplexD hR K L) n

/-- `homPost` is functorial in the target. -/
private lemma homPost_comp (hR : IsCommSheaf R) (M : Mod R) {N N' N'' : Mod R} (g : N ⟶ N')
    (g' : N' ⟶ N'') : homPost hR M (g ≫ g') = homPost hR M g ≫ homPost hR M g' := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro X
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

/-- `homPre` and `homPost` commute. -/
private lemma homPre_homPost (hR : IsCommSheaf R) {M M' N N' : Mod R} (f : M' ⟶ M)
    (g : N ⟶ N') : homPre hR f N ≫ homPost hR M' g = homPost hR M g ≫ homPre hR f N' := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro X
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

open CochainComplex.HomComplex in
/-- `homComplexMap₂` commutes with the differentials. -/
private lemma homComplexMap₂_comm (hR : IsCommSheaf R) (K : CochainComplex (Mod R) ℤ)
    {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') (n : ℤ) :
    Limits.Pi.map (fun T : Triplet n ↦ homPost hR (K.X T.p) (g.f T.q)) ≫
        homComplexD hR K L' n =
      homComplexD hR K L n ≫
        Limits.Pi.map (fun T : Triplet (n + 1) ↦ homPost hR (K.X T.p) (g.f T.q)) := by
  apply Pi.hom_ext
  intro T
  rw [Category.assoc, Category.assoc, homComplexD_π, Pi.map_π, ← Category.assoc, homComplexD_π]
  rw [Preadditive.comp_add, Preadditive.add_comp, Linear.comp_units_smul,
    Linear.units_smul_comp]
  congr 1
  · rw [← Category.assoc, Pi.map_π, Category.assoc, Category.assoc, ← homPost_comp,
      ← homPost_comp, ← g.comm]
  · congr 1
    rw [← Category.assoc, Pi.map_π, Category.assoc, Category.assoc, homPre_homPost]

/-- `homPre` is contravariantly functorial in the source. -/
private lemma homPre_comp (hR : IsCommSheaf R) {M M' M'' : Mod R} (f : M' ⟶ M) (g : M'' ⟶ M')
    (N : Mod R) : homPre hR f N ≫ homPre hR g N = homPre hR (g ≫ f) N := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro X
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

open CochainComplex.HomComplex in
/-- `homComplexMap₁` commutes with the differentials. -/
private lemma homComplexMap₁_comm (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ}
    (f : K' ⟶ K) (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    Limits.Pi.map (fun T : Triplet n ↦ homPre hR (f.f T.p) (L.X T.q)) ≫
        homComplexD hR K' L n =
      homComplexD hR K L n ≫
        Limits.Pi.map (fun T : Triplet (n + 1) ↦ homPre hR (f.f T.p) (L.X T.q)) := by
  apply Pi.hom_ext
  intro T
  rw [Category.assoc, Category.assoc, homComplexD_π, Pi.map_π, ← Category.assoc,
    homComplexD_π]
  rw [Preadditive.comp_add, Preadditive.add_comp, Linear.comp_units_smul,
    Linear.units_smul_comp]
  congr 1
  · rw [← Category.assoc, Pi.map_π, Category.assoc, Category.assoc, homPre_homPost]
  · congr 1
    rw [← Category.assoc, Pi.map_π, Category.assoc, Category.assoc, homPre_comp, homPre_comp,
      f.comm]

open CochainComplex.HomComplex in
/-- **S7.** Functoriality in the target: `g : L ⟶ L'` induces `𝓗om(K, L) ⟶ 𝓗om(K, L')`
(post-composition in each factor). -/
def homComplexMap₂ (hR : IsCommSheaf R) (K : CochainComplex (Mod R) ℤ)
    {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') :
    homSheafComplex hR K L ⟶ homSheafComplex hR K L' where
  f n := Limits.Pi.map fun T : Triplet n ↦ homPost hR (K.X T.p) (g.f T.q)
  comm' := fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    rw [homComplex_d, homComplex_d]
    exact homComplexMap₂_comm hR K g i

open CochainComplex.HomComplex in
/-- **S7.** Functoriality in the source: `f : K' ⟶ K` induces `𝓗om(K, L) ⟶ 𝓗om(K', L)`
(pre-composition in each factor). -/
def homComplexMap₁ (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ} (f : K' ⟶ K)
    (L : CochainComplex (Mod R) ℤ) : homSheafComplex hR K L ⟶ homSheafComplex hR K' L where
  f n := Limits.Pi.map fun T : Triplet n ↦ homPre hR (f.f T.p) (L.X T.q)
  comm' := fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    rw [homComplex_d, homComplex_d]
    exact homComplexMap₁_comm hR f L i

/-- Restriction of a complex of sheaves of modules to the over-site `Over X` (termwise
`M ↦ M.over X`; on `Opens` this is `restr` applied termwise). -/
abbrev overC (X : C) : CochainComplex (Mod R) ℤ ⥤ CochainComplex (Mod (R.over X)) ℤ :=
  (SheafOfModules.overFunctor.{0} R X).mapHomologicalComplex (ComplexShape.up ℤ)

open CochainComplex.HomComplex in
/-- **S7. Sections of the Hom complex.** Sections of `𝓗om(K, L)ⁿ` over `X` are the degree-`n`
cochains `K|X → L|X` (evaluation preserves products; `ModuleCat.piIsoPi`). -/
def homComplexSectionsEquiv (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ)
    (X : C) : ((homSheafComplex hR K L).X n).val.obj (op X) ≃+ Cochain ((overC X).obj K)
      ((overC X).obj L) n :=
  ((asIso (piComparison (SheafOfModules.evaluation.{0} R (op X))
      fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q))) ≪≫
    ModuleCat.piIsoPi _).toLinearEquiv.toAddEquiv

open CochainComplex.HomComplex in
/-- **S7.** The component of `homComplexSectionsEquiv` at `p + n = q` is the section of the
factor `homSheaf (Kᵖ) (L^q)`, i.e. a morphism `Kᵖ|X ⟶ L^q|X`. -/
lemma homComplexSectionsEquiv_apply (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ)
    (n : ℤ) (X : C) (s : ((homSheafComplex hR K L).X n).val.obj (op X)) (T : Triplet n) :
    homComplexSectionsEquiv hR K L n X s T =
      (homSheafSectionsEquiv hR (K.X T.p) (L.X T.q) X)
        (((Pi.π (fun T : Triplet n ↦ homSheaf hR (K.X T.p) (L.X T.q)) T).val.app (op X)).hom s) :=
  secEquiv_apply hR K L n X s T

open CochainComplex.HomComplex in
/-- **S7.** Under `homComplexSectionsEquiv`, the differential of `𝓗om(K, L)` is Mathlib's `δ`. -/
lemma homComplexSectionsEquiv_d (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ)
    (X : C) (s : ((homSheafComplex hR K L).X n).val.obj (op X)) :
    homComplexSectionsEquiv hR K L (n + 1) X
        (((homSheafComplex hR K L).d n (n + 1)).val.app (op X) s) =
      δ n (n + 1) (homComplexSectionsEquiv hR K L n X s) := by
  have h : (homSheafComplex hR K L).d n (n + 1) = homComplexD hR K L n :=
    CochainComplex.of_d (homComplexX hR K L) (homComplexD hR K L) n
  rw [h]
  exact secEquiv_D hR K L n X s

end Cohesive
end
