import Cohesivemodules.Sheaf.Hom
import Cohesivemodules.Sheaf.Soft

set_option linter.style.header false

/-!
# S7.a′: the termwise source action on Hom sheaves

Blueprint item S7.a′ (§3, v1.9; replaces S7.a, audit F3). Let a ring `T` act on each term `Kᵖ`
of a complex of sheaves of `R`-modules by `R`-linear sheaf endomorphisms, additively and
unitally, not necessarily commuting with the differential. Precomposition gives an action of `T`
on each term `𝓗om(K, L)ⁿ = ∏_{p + n = q} 𝓗om(Kᵖ, L^q)` by `R`-linear sheaf endomorphisms,
additive and unital, vanishing on an open `V` whenever the action on every `Kᵖ` vanishes on all
opens `W ≤ V`. It is not a chain map. With `T = S(X)` for a fine `S` this is the input of S3.b(i)
(`IsSoft.of_action`): the terms of `𝓗om(K, L)` are soft (`isSoft_homSheafComplex_X`), as C4
step 2 uses.

* `homSourceAction`, `homSourceAction_one`, `homSourceAction_app_eq_zero`: one sheaf.
* `homComplexSourceAction`, `homComplexSourceAction_one`, `homComplexSourceAction_app_eq_zero`:
  the terms of `homSheafComplex`.
* `isSoft_homSheafComplex_X`: softness of the terms.

## Deviations
* Stated on `Opens X` (where locality and softness live), not on a general site.
* The old S7.a ("a complex of `S`-modules via the source") is false as stated when the
  differentials of `K` are not `S`-linear, the case of C3/C4; it is not formalized.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X} {T : Type} [Ring T]

/-- `homPre` on sections over `V` is precomposition with `f|V`. -/
private lemma homPre_equiv (hR : IsCommSheaf R) {M M' : Mod R} (f : M' ⟶ M) (N : Mod R)
    (V : Opens X) (φ : (homSheaf hR M N).val.obj (op V)) :
    homSheafSectionsEquiv hR M' N V (((homPre hR f N).val.app (op V)).hom φ) =
      f.over V ≫ homSheafSectionsEquiv hR M N V φ :=
  Equiv.apply_symm_apply _ _

/-- Two sheaf morphisms into `homSheaf` agreeing on sections after the section equivalence. -/
private lemma homSheaf_hom_ext (hR : IsCommSheaf R) {M N P Q : Mod R} {f g : homSheaf hR M N ⟶
    homSheaf hR P Q}
    (h : ∀ (V : Opens X) (φ : (homSheaf hR M N).val.obj (op V)),
      homSheafSectionsEquiv hR P Q V ((f.val.app (op V)).hom φ) =
      homSheafSectionsEquiv hR P Q V ((g.val.app (op V)).hom φ)) : f = g := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦
    (homSheafSectionsEquiv hR P Q V.unop).injective (h V.unop φ))

/-- `homPre` of the zero morphism is zero. -/
private lemma homPre_zero' (hR : IsCommSheaf R) {M M' : Mod R} (N : Mod R) :
    homPre hR (0 : M' ⟶ M) N = 0 := by
  refine homSheaf_hom_ext hR fun V φ ↦ ?_
  rw [homPre_equiv]
  refine hom_ext_pt fun Z m ↦ ?_
  have h0 : (0 : M' ⟶ M).over V = 0 :=
    Functor.map_zero (SheafOfModules.overFunctor.{0} R V) M' M
  rw [h0, zero_comp]
  rfl

/-- `homPre` is additive in the morphism. -/
private lemma homPre_add' (hR : IsCommSheaf R) {M M' : Mod R} (f g : M' ⟶ M) (N : Mod R) :
    homPre hR (f + g) N = homPre hR f N + homPre hR g N := by
  refine homSheaf_hom_ext hR fun V φ ↦ ?_
  rw [homPre_equiv]
  have h0 : (f + g).over V = f.over V + g.over V :=
    Functor.map_add (F := SheafOfModules.overFunctor.{0} R V)
  rw [h0, Preadditive.add_comp]
  refine hom_ext_pt fun Z m ↦ ?_
  rfl

/-- `homPre` of the identity is the identity. -/
private lemma homPre_id' (hR : IsCommSheaf R) {M : Mod R} (N : Mod R) :
    homPre hR (𝟙 M) N = 𝟙 _ := by
  refine homSheaf_hom_ext hR fun V φ ↦ ?_
  rw [homPre_equiv]
  have h0 : (𝟙 M : M ⟶ M).over V = 𝟙 _ :=
    CategoryTheory.Functor.map_id (SheafOfModules.overFunctor.{0} R V) M
  rw [h0, Category.id_comp]
  rfl

/-- `homPre` of a morphism vanishing on all opens below `V` vanishes over `V`. -/
private lemma homPre_app_eq_zero (hR : IsCommSheaf R) {M M' : Mod R} (f : M' ⟶ M) (N : Mod R)
    (V : Opens X) (h : ∀ W : Opens X, W ≤ V → f.val.app (op W) = 0) :
    (homPre hR f N).val.app (op V) = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
  refine (homSheafSectionsEquiv hR M' N V).injective ?_
  rw [homPre_equiv]
  change _ = (0 : M'.over V ⟶ N.over V)
  generalize homSheafSectionsEquiv hR M N V φ = ψ
  refine hom_ext_pt fun Z m ↦ ?_
  have := h Z.unop.left (leOfHom Z.unop.hom)
  have h2 : ((f.val.app (op Z.unop.left)).hom m : M.val.obj (op Z.unop.left)) = 0 := by
    rw [this]; rfl
  show (ψ.val.app Z).hom ((f.val.app (op Z.unop.left)).hom m) = _
  rw [h2]
  exact map_zero _

/-- **S7.a′** (one sheaf). [B, §4], [A, Lemma 7.2.8]. An additive action `act` of `T` on `M` by
sheaf endomorphisms induces, by precomposition (`homPre`), an additive action of `T` on
`homSheaf hR M N`: `t` acts on a section `φ : M|V ⟶ N|V` by `φ ↦ (act t)|V ≫ φ`.
Deviation: `T` acts through the source, not through `R` (blueprint S7.a′). -/
def homSourceAction (hR : IsCommSheaf R) {M : Mod R} (act : T →+ (M ⟶ M)) (N : Mod R) :
    T →+ (homSheaf hR M N ⟶ homSheaf hR M N) where
  toFun t := homPre hR (act t) N
  map_zero' := by rw [map_zero]; exact homPre_zero' hR N
  map_add' t s := by rw [map_add]; exact homPre_add' hR _ _ N

/-- `homSourceAction` applied to `t` is `homPre` of `act t`. -/
@[simp] lemma homSourceAction_apply (hR : IsCommSheaf R) {M : Mod R} (act : T →+ (M ⟶ M))
    (N : Mod R) (t : T) : homSourceAction hR act N t = homPre hR (act t) N :=
  rfl

/-- **S7.a′** (one sheaf, unital). If `1` acts on `M` as the identity, it acts on
`homSheaf hR M N` as the identity. -/
theorem homSourceAction_one (hR : IsCommSheaf R) {M : Mod R} (act : T →+ (M ⟶ M))
    (h1 : act 1 = 𝟙 M) (N : Mod R) : homSourceAction hR act N 1 = 𝟙 _ := by
  rw [homSourceAction_apply, h1]
  exact homPre_id' hR N

/-- **S7.a′** (one sheaf, local). If `t` acts as `0` on the sections of `M` over every open
`W ≤ V`, it acts as `0` on the sections of `homSheaf hR M N` over `V` (`φ ↦ (act t)|V ≫ φ = 0`). -/
theorem homSourceAction_app_eq_zero (hR : IsCommSheaf R) {M : Mod R} (act : T →+ (M ⟶ M))
    (N : Mod R) (t : T) (V : Opens X)
    (h : ∀ W : Opens X, W ≤ V → (act t).val.app (op W) = 0) :
    (homSourceAction hR act N t).val.app (op V) = 0 :=
  homPre_app_eq_zero hR (act t) N V h

/-- A product of morphisms vanishing on sections over `V` vanishes on sections over `V`. -/
private lemma pi_map_app_eq_zero {ι : Type} (F G : ι → Mod R) (g : ∀ i, F i ⟶ G i)
    [HasProduct F] [HasProduct G] (V : Opens X) (h : ∀ i, (g i).val.app (op V) = 0) :
    (Limits.Pi.map g).val.app (op V) = 0 := by
  let E := SheafOfModules.evaluation.{0} R (op V)
  have key : E.map (Limits.Pi.map g) ≫ piComparison E G = 0 := by
    apply Limits.Pi.hom_ext
    intro i
    rw [Category.assoc, piComparison_comp_π, zero_comp, ← E.map_comp, Limits.Pi.map_π,
      E.map_comp]
    have : E.map (g i) = 0 := h i
    rw [this, comp_zero]
  have := (cancel_mono (piComparison E G)).1 (key.trans (zero_comp).symm)
  exact this

/-- The term of `homSheafComplex hR K L` in degree `n` is `homComplexX hR K L n`. -/
lemma homSheafComplex_X_eq (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    (homSheafComplex hR K L).X n = homComplexX hR K L n :=
  rfl

open CochainComplex.HomComplex in
/-- **S7.a′** (complexes).[B, §4], [A, Lemma 7.2.8]. Additive actions `act p` of `T` on the
terms `Kᵖ` (not required to commute with the differential of `K`) induce an additive action of
`T` on the term `𝓗om(K, L)ⁿ = ∏_{p + n = q} 𝓗om(Kᵖ, L^q)`, by `homSourceAction` on each factor.
It is not a chain map. Typed on `homComplexX hR K L n`, which is `(homSheafComplex hR K L).X n`
by definition (`homSheafComplex_X_eq`). -/
def homComplexSourceAction (hR : IsCommSheaf R) {K : CochainComplex (Mod R) ℤ}
    (act : ∀ p : ℤ, T →+ (K.X p ⟶ K.X p)) (L : CochainComplex (Mod R) ℤ) (n : ℤ) :
    T →+ (homComplexX hR K L n ⟶ homComplexX hR K L n) where
  toFun t := Limits.Pi.map fun τ : Triplet n ↦ homSourceAction hR (act τ.p) (L.X τ.q) t
  map_zero' := by
    apply Limits.Pi.hom_ext
    intro τ
    rw [Limits.Pi.map_π, zero_comp, map_zero, comp_zero]
  map_add' t s := by
    apply Limits.Pi.hom_ext
    intro τ
    rw [Preadditive.add_comp, Limits.Pi.map_π, Limits.Pi.map_π, Limits.Pi.map_π,
      ← Preadditive.comp_add, map_add]

open CochainComplex.HomComplex in
/-- `homComplexSourceAction` acts on the factor at `τ : Triplet n` by `homSourceAction`. -/
lemma homComplexSourceAction_π (hR : IsCommSheaf R) {K : CochainComplex (Mod R) ℤ}
    (act : ∀ p : ℤ, T →+ (K.X p ⟶ K.X p)) (L : CochainComplex (Mod R) ℤ) (n : ℤ) (t : T)
    (τ : Triplet n) :
    homComplexSourceAction hR act L n t ≫
        Pi.π (fun τ : Triplet n ↦ homSheaf hR (K.X τ.p) (L.X τ.q)) τ =
      Pi.π (fun τ : Triplet n ↦ homSheaf hR (K.X τ.p) (L.X τ.q)) τ ≫
        homSourceAction hR (act τ.p) (L.X τ.q) t :=
  Limits.Pi.map_π (fun τ : Triplet n ↦ homSourceAction hR (act τ.p) (L.X τ.q) t) τ

/-- **S7.a′** (complexes, unital). If `1` acts on every `Kᵖ` as the identity, it acts on every
term of `homSheafComplex hR K L` as the identity. -/
theorem homComplexSourceAction_one (hR : IsCommSheaf R) {K : CochainComplex (Mod R) ℤ}
    (act : ∀ p : ℤ, T →+ (K.X p ⟶ K.X p)) (h1 : ∀ p, act p 1 = 𝟙 (K.X p))
    (L : CochainComplex (Mod R) ℤ) (n : ℤ) : homComplexSourceAction hR act L n 1 = 𝟙 _ := by
  apply Limits.Pi.hom_ext
  intro τ
  rw [homComplexSourceAction_π, Category.id_comp, homSourceAction_one hR (act τ.p) (h1 τ.p),
    Category.comp_id]

/-- **S7.a′** (complexes, local). If `t` acts as `0` on the sections of every `Kᵖ` over every
open `W ≤ V`, it acts as `0` on the sections over `V` of every term of `homSheafComplex hR K L`. -/
theorem homComplexSourceAction_app_eq_zero (hR : IsCommSheaf R)
    {K : CochainComplex (Mod R) ℤ} (act : ∀ p : ℤ, T →+ (K.X p ⟶ K.X p))
    (L : CochainComplex (Mod R) ℤ) (n : ℤ) (t : T) (V : Opens X)
    (h : ∀ (p : ℤ) (W : Opens X), W ≤ V → (act p t).val.app (op W) = 0) :
    (homComplexSourceAction hR act L n t).val.app (op V) = 0 :=
  pi_map_app_eq_zero _ _ _ V fun τ ↦ homSourceAction_app_eq_zero hR (act τ.p) (L.X τ.q) t V
    (h τ.p)

/-- **S7.a′ with S3.b(i)** (input of C4 step 2). [A, Lemma 7.2.8]. Let `S` be a fine sheaf of
rings whose global sections act on every term `Kᵖ` by sheaf endomorphisms, additively, with `1`
acting as the identity, and with `ρ` acting as `0` over every open `V` on which `ρ|V = 0`. Then
every term of `𝓗om(K, L)` is soft. Deviation: the action need not commute with the differential
of `K` (it does not in C3/C4), so `𝓗om(K, L)` is not a complex of `S`-modules. -/
theorem isSoft_homSheafComplex_X {S : RingSheaf X} (hS : IsFine S) (hR : IsCommSheaf R)
    {K : CochainComplex (Mod R) ℤ} (act : ∀ p : ℤ, S.obj.obj (op ⊤) →+ (K.X p ⟶ K.X p))
    (h1 : ∀ p, act p 1 = 𝟙 (K.X p))
    (hloc : ∀ (p : ℤ) (ρ : S.obj.obj (op ⊤)) (V : Opens X), rres S (le_top : V ≤ ⊤) ρ = 0 →
      (act p ρ).val.app (op V) = 0)
    (L : CochainComplex (Mod R) ℤ) (n : ℤ) : IsSoft ((homSheafComplex hR K L).X n) := by
  refine IsSoft.of_action hS (homComplexX hR K L n) (homComplexSourceAction hR act L n)
    (homComplexSourceAction_one hR act h1 L n) fun ρ V hV ↦ ?_
  refine homComplexSourceAction_app_eq_zero hR act L n ρ V fun p W hW ↦ hloc p ρ W ?_
  have h2 : rres S (le_top : W ≤ ⊤) ρ = rres S hW (rres S (le_top : V ≤ ⊤) ρ) := by
    change _ = (S.obj.map (homOfLE hW).op).hom ((S.obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom ρ)
    rw [← RingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
    rfl
  rw [h2, hV, map_zero]

end Cohesive
