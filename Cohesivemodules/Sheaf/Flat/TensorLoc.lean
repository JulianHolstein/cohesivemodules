import Cohesivemodules.Sheaf.Restriction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.Algebra.Homology.TotalComplexShift
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.Abelian

set_option linter.style.header false

/-!
# S8 (part 1): the `ℤ`-tensor product and local injectivity of `f ⊗ N`

Blueprint item S8 (§3). Split from `Sheaf/Flat.lean` for size only (CLAUDE.md: "New work goes in
small new files"); no mathematical change. Auxiliary material for
`isIso_sheafifyF_map_whiskerRight`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace

/-! ### The `ℤ`-tensor product and local injectivity of `f ⊗ N`

Auxiliary material for `isIso_sheafifyF_map_whiskerRight` (tensor product and sheafification).
For a presheaf of commutative rings `R₀` and presheaves of modules `P`, `N`, the sectionwise
`R₀(U)`-tensor product `P(U) ⊗ N(U)` is a quotient of the `ℤ`-tensor product by the relations
`(r m) ⊗ n - m ⊗ (r n)`. A locally bijective `f : P ⟶ Q` stays locally injective after `- ⊗ N`:
over `ℤ` this is Mathlib's monoidality of the localization `J.W`
(`zTensor_locInj`), and the relations are lifted locally. -/

section TensorLoc

/-- Bijectivity of postcomposition is detected after a fully faithful functor. -/
private lemma bij_comp_map_iff {D D' : Type*} [Category D] [Category D'] (Φ : D ⥤ D')
    [Φ.Full] [Φ.Faithful] {X Y : D} (f : X ⟶ Y) (Z : D) :
    Function.Bijective (fun g : Y ⟶ Z => f ≫ g) ↔
      Function.Bijective (fun g : Φ.obj Y ⟶ Φ.obj Z => Φ.map f ≫ g) := by
  have hΦ : ∀ A B : D, Function.Bijective (fun g : A ⟶ B => Φ.map g) := fun A B =>
    ⟨fun _ _ h => Φ.map_injective h, Φ.map_surjective⟩
  have h : (fun g : Φ.obj Y ⟶ Φ.obj Z => Φ.map f ≫ g) ∘ (fun g : Y ⟶ Z => Φ.map g) =
      (fun g : X ⟶ Z => Φ.map g) ∘ (fun g : Y ⟶ Z => f ≫ g) := by
    funext g; simp
  rw [← Function.Bijective.of_comp_iff' (hΦ X Z) (fun g : Y ⟶ Z => f ≫ g), ← h]
  constructor
  · intro hb
    have := hb.comp (Equiv.ofBijective _ (hΦ Y Z)).symm.bijective
    have e2 : ∀ x, Φ.map ((Equiv.ofBijective _ (hΦ Y Z)).symm x) = x := fun x =>
      Equiv.apply_symm_apply (Equiv.ofBijective _ (hΦ Y Z)) x
    convert this using 1
    funext x
    simp only [Function.comp_apply, e2]
  · intro hb
    exact hb.comp (hΦ Y Z)

/-- Locality of a morphism with respect to an object property is invariant under a fully faithful
functor whose image detects the property up to isomorphism. -/
private lemma isLocal_map_iff {D D' : Type*} [Category D] [Category D'] (Φ : D ⥤ D')
    [Φ.Full] [Φ.Faithful] (P : ObjectProperty D) (P' : ObjectProperty D')
    (hP : ∀ Z, P Z ↔ P' (Φ.obj Z))
    (hess : ∀ Z', P' Z' → ∃ Z, P Z ∧ Nonempty (Φ.obj Z ≅ Z'))
    {X Y : D} (f : X ⟶ Y) : P.isLocal f ↔ P'.isLocal (Φ.map f) := by
  constructor
  · intro h Z' hZ'
    obtain ⟨Z, hZ, ⟨e⟩⟩ := hess Z' hZ'
    have h1 := (bij_comp_map_iff Φ f Z).1 (h Z hZ)
    have h2 : (fun g : Φ.obj Y ⟶ Z' => Φ.map f ≫ g) =
        (fun k : Φ.obj X ⟶ Φ.obj Z => k ≫ e.hom) ∘ (fun k : Φ.obj Y ⟶ Φ.obj Z => Φ.map f ≫ k) ∘
          (fun g : Φ.obj Y ⟶ Z' => g ≫ e.inv) := by
      funext g; simp
    rw [h2]
    refine Function.Bijective.comp ?_ (Function.Bijective.comp h1 ?_)
    · exact ⟨fun a b hab => by simpa using hab, fun k => ⟨k ≫ e.inv, by simp⟩⟩
    · exact ⟨fun a b hab => by simpa using hab, fun k => ⟨k ≫ e.hom, by simp⟩⟩
  · intro h Z hZ
    exact (bij_comp_map_iff Φ f Z).2 (h _ ((hP Z).1 hZ))

/-- `W` for `ℤ`-module presheaves can be tested after forgetting to abelian groups. -/
private lemma W_modInt_iff {C : Type} [SmallCategory C] (J : GrothendieckTopology C)
    {F G : Cᵒᵖ ⥤ ModuleCat.{0} ℤ} (g : F ⟶ G) :
    J.W g ↔ J.W (Functor.whiskerRight g (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0})) := by
  refine isLocal_map_iff
    ((Functor.whiskeringRight Cᵒᵖ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).obj
      (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0})) _ _ ?_ ?_ g
  · intro Z
    exact Presheaf.isSheaf_iff_isSheaf_comp J Z (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0})
  · intro Z' hZ'
    let E := forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}
    let e : (Z' ⋙ E.asEquivalence.inverse) ⋙ E ≅ Z' :=
      Functor.isoWhiskerLeft Z' E.asEquivalence.counitIso ≪≫ Z'.rightUnitor
    refine ⟨Z' ⋙ E.asEquivalence.inverse, ?_, ⟨e⟩⟩
    rw [Presheaf.isSheaf_iff_isSheaf_comp J _ E]
    exact (Presheaf.isSheaf_of_iso_iff e).2 hZ'

/-- Abelian groups as `ℤ`-modules (same carrier). -/
private def toInt : AddCommGrpCat.{0} ⥤ ModuleCat.{0} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap

/-- **Local injectivity of the `ℤ`-tensor product.** If `h` is locally bijective, then so is
`h ⊗ T` over `ℤ` (Mathlib's `GrothendieckTopology.W.whiskerRight`, which needs
`Mathlib.CategoryTheory.Sites.Monoidal`). -/
private lemma zTensor_locInj {C : Type} [SmallCategory C] (J : GrothendieckTopology C)
    [J.WEqualsLocallyBijective AddCommGrpCat.{0}] {A B T : Cᵒᵖ ⥤ AddCommGrpCat.{0}} (h : A ⟶ B)
    [Presheaf.IsLocallyInjective J h] [Presheaf.IsLocallySurjective J h] {U : C}
    (a : TensorProduct ℤ (A.obj (op U)) (T.obj (op U)))
    (ha : TensorProduct.map (h.app (op U)).hom.toIntLinearMap LinearMap.id a = 0) :
    ∃ S ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), S g →
      TensorProduct.map (A.map g.op).hom.toIntLinearMap (T.map g.op).hom.toIntLinearMap a = 0 := by
  have hW : J.W (Functor.whiskerRight h toInt) := by
    rw [W_modInt_iff]
    exact J.W_of_isLocallyBijective h
  have hW2 := hW.whiskerRight (T ⋙ toInt)
  have hW3 := (W_modInt_iff J _).1 hW2
  have hinj := hW3.isLocallyInjective
  have := hinj.equalizerSieve_mem (X := op U) (a : _) 0 (by rw [map_zero]; exact ha)
  refine ⟨_, this, fun V g hg => ?_⟩
  exact hg.trans (map_zero _)

section Kernel
open scoped TensorProduct

variable (R : Type*) [CommRing R] (M N : Type*) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The canonical surjection from the `ℤ`-tensor product onto the `R`-tensor product. -/
private def tensorInt : M ⊗[ℤ] N →+ M ⊗[R] N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => m ⊗ₜ[R] n) (fun n n' => by
      simp only [TensorProduct.tmul_add])) (fun m m' => by
        ext n; simp only [TensorProduct.add_tmul, AddMonoidHom.add_apply, AddMonoidHom.mk'_apply]))
    (fun k m n => by
      simp only [AddMonoidHom.mk'_apply]
      rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul])

/-- The relations killed by passing from `⊗[ℤ]` to `⊗[R]`. -/
private def tensorRel : Submodule ℤ (M ⊗[ℤ] N) :=
  Submodule.span ℤ {x | ∃ (r : R) (m : M) (n : N), x = (r • m) ⊗ₜ[ℤ] n - m ⊗ₜ[ℤ] (r • n)}

/-- `tensorInt` on pure tensors. -/
private lemma tensorInt_tmul (m : M) (n : N) :
    tensorInt R M N (m ⊗ₜ[ℤ] n) = m ⊗ₜ[R] n := rfl

/-- `tensorInt` is surjective. -/
private lemma tensorInt_surjective : Function.Surjective (tensorInt R M N) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul m n => exact ⟨m ⊗ₜ[ℤ] n, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- The kernel of `tensorInt` is generated by the relations `tensorRel`. -/
private lemma mem_tensorRel_of_tensorInt_eq_zero {z : M ⊗[ℤ] N} (hz : tensorInt R M N z = 0) :
    z ∈ tensorRel R M N := by
  let σ : M ⊗[R] N →+ (M ⊗[ℤ] N) ⧸ tensorRel R M N :=
    TensorProduct.liftAddHom
      (AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n =>
        Submodule.Quotient.mk (m ⊗ₜ[ℤ] n)) (fun n n' => by
          rw [TensorProduct.tmul_add, Submodule.Quotient.mk_add])) (fun m m' => by
        ext n
        simp only [TensorProduct.add_tmul, AddMonoidHom.add_apply, AddMonoidHom.mk'_apply,
          Submodule.Quotient.mk_add]))
      (fun r m n => by
        simp only [AddMonoidHom.mk'_apply]
        rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
        exact Submodule.subset_span ⟨r, m, n, rfl⟩)
  have h1 : ∀ w : M ⊗[ℤ] N, σ (tensorInt R M N w) = Submodule.Quotient.mk w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, Submodule.Quotient.mk_add]
  have h2 := h1 z
  rw [hz, map_zero] at h2
  exact (Submodule.Quotient.mk_eq_zero _).1 h2.symm

/-- The relations `tensorRel` are killed by `tensorInt`. -/
private lemma tensorInt_eq_zero_of_mem_tensorRel {w : M ⊗[ℤ] N} (hw : w ∈ tensorRel R M N) :
    tensorInt R M N w = 0 := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, m, n, rfl⟩ := hx
    rw [map_sub, tensorInt_tmul, tensorInt_tmul, sub_eq_zero]
    exact TensorProduct.smul_tmul r m n
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_zsmul, hx, smul_zero]
end Kernel

section Assembly
open scoped TensorProduct
variable {C : Type} [SmallCategory C] (J : GrothendieckTopology C) {R₀ : Cᵒᵖ ⥤ CommRingCat.{0}}

/-- The underlying presheaf of abelian groups of a presheaf of modules. -/
private abbrev ab (P : PresheafOfModulesOfCommRing.{0} R₀) : Cᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (PresheafOfModules.toPresheaf (R₀ ⋙ forget₂ CommRingCat RingCat)).obj P

/-- The restriction map of a presheaf of modules, as an additive map of carriers. -/
private abbrev resAdd (P : PresheafOfModulesOfCommRing.{0} R₀) {U V : Cᵒᵖ} (g : U ⟶ V) :
    P.obj U →+ P.obj V :=
  (P.map g).hom.toAddMonoidHom

/-- Restriction of the `ℤ`-tensor product of two presheaves of modules. -/
private abbrev zres (P N : PresheafOfModulesOfCommRing.{0} R₀) {U V : Cᵒᵖ} (g : U ⟶ V) :
    P.obj U ⊗[ℤ] N.obj U →ₗ[ℤ] P.obj V ⊗[ℤ] N.obj V :=
  TensorProduct.map (resAdd P g).toIntLinearMap (resAdd N g).toIntLinearMap

/-- The map `f ⊗ 1` on `ℤ`-tensor products of sections. -/
private abbrev zmap {P Q : PresheafOfModulesOfCommRing.{0} R₀}
    (N : PresheafOfModulesOfCommRing.{0} R₀) (f : P ⟶ Q) (U : Cᵒᵖ) :
    P.obj U ⊗[ℤ] N.obj U →ₗ[ℤ] Q.obj U ⊗[ℤ] N.obj U :=
  TensorProduct.map (f.app U).hom.toAddMonoidHom.toIntLinearMap LinearMap.id

/-- Restriction of the sectionwise tensor product, in terms of `tensorInt` and `zres`. -/
private lemma tensorObj_map_tensorInt (P N : PresheafOfModulesOfCommRing.{0} R₀) {U V : Cᵒᵖ}
    (g : U ⟶ V) (a : P.obj U ⊗[ℤ] N.obj U) :
    ((P ⊗ N).map g).hom (tensorInt (R₀.obj U) (P.obj U) (N.obj U) a) =
      tensorInt (R₀.obj V) (P.obj V) (N.obj V) (zres P N g a) := by
  induction a using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    exact (map_add ((P ⊗ N).map g).hom _ _).trans (congrArg₂ _ hx hy)

/-- The map `f ▷ N` on sections, in terms of `tensorInt` and `zmap`. -/
private lemma whiskerRight_app_tensorInt {P Q : PresheafOfModulesOfCommRing.{0} R₀}
    (N : PresheafOfModulesOfCommRing.{0} R₀) (f : P ⟶ Q) (U : Cᵒᵖ)
    (a : P.obj U ⊗[ℤ] N.obj U) :
    ((f ▷ N).app U).hom (tensorInt (R₀.obj U) (P.obj U) (N.obj U) a) =
      tensorInt (R₀.obj U) (Q.obj U) (N.obj U) (zmap N f U a) := by
  induction a using TensorProduct.inductionOn with
  | tmul m n => rfl
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    exact (map_add ((f ▷ N).app U).hom _ _).trans (congrArg₂ _ hx hy)

/-- `zres` commutes with `zmap`. -/
private lemma zres_zmap {P Q : PresheafOfModulesOfCommRing.{0} R₀}
    (N : PresheafOfModulesOfCommRing.{0} R₀) (f : P ⟶ Q) {U V : Cᵒᵖ} (g : U ⟶ V)
    (a : P.obj U ⊗[ℤ] N.obj U) :
    zres Q N g (zmap N f U a) = zmap N f V (zres P N g a) := by
  induction a using TensorProduct.inductionOn with
  | tmul m n =>
    show (Q.map g (f.app U m)) ⊗ₜ[ℤ] (N.map g n) = (f.app V (P.map g m)) ⊗ₜ[ℤ] (N.map g n)
    rw [PresheafOfModules.naturality_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- Over a locally surjective `f : P ⟶ Q`, the relations of `Q ⊗ N` are locally images of
relations of `P ⊗ N`. -/
private lemma exists_local_lift {P Q : PresheafOfModulesOfCommRing.{0} R₀}
    (N : PresheafOfModulesOfCommRing.{0} R₀) (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)]
    {U : C} (w : Q.obj (op U) ⊗[ℤ] N.obj (op U))
    (hw : w ∈ tensorRel (R₀.obj (op U)) (Q.obj (op U)) (N.obj (op U))) :
    ∃ S ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), S g → ∃ k ∈ tensorRel (R₀.obj (op V)) (P.obj (op V))
      (N.obj (op V)), zmap N f (op V) k = zres Q N g.op w := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, q, n, rfl⟩ := hx
    refine ⟨_, Presheaf.imageSieve_mem J ((PresheafOfModules.toPresheaf _).map f) q,
      fun V g ⟨p₀, hp₀⟩ => ?_⟩
    let p : P.obj (op V) := p₀
    have hp : f.app (op V) p = Q.map g.op q := hp₀
    let n' : N.obj (op V) := N.map g.op n
    let r' : R₀.obj (op V) := R₀.map g.op r
    refine ⟨(r' • p) ⊗ₜ[ℤ] n' - p ⊗ₜ[ℤ] (r' • n'),
      Submodule.subset_span ⟨r', p, n', rfl⟩, ?_⟩
    have e1 : f.app (op V) (r' • p) = r' • f.app (op V) p :=
      map_smul (f.app (op V)).hom _ _
    let q' : Q.obj (op V) := Q.map g.op q
    let qr : Q.obj (op V) := Q.map g.op (r • q)
    let nr : N.obj (op V) := N.map g.op (r • n)
    have e2 : qr = r' • q' := PresheafOfModules.map_smul Q g.op r q
    have e3 : nr = r' • n' := PresheafOfModules.map_smul N g.op r n
    rw [map_sub, map_sub]
    show f.app (op V) (r' • p) ⊗ₜ[ℤ] n' - f.app (op V) p ⊗ₜ[ℤ] (r' • n') =
      qr ⊗ₜ[ℤ] n' - q' ⊗ₜ[ℤ] nr
    rw [e1, e2, e3, hp]
  | zero => exact ⟨⊤, J.top_mem U, fun V g _ => ⟨0, Submodule.zero_mem _, by simp⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨S₁, h₁, hS₁⟩ := hx
    obtain ⟨S₂, h₂, hS₂⟩ := hy
    refine ⟨S₁ ⊓ S₂, J.intersection_covering h₁ h₂, fun V g hg => ?_⟩
    obtain ⟨k₁, hk₁, e₁⟩ := hS₁ g hg.1
    obtain ⟨k₂, hk₂, e₂⟩ := hS₂ g hg.2
    exact ⟨k₁ + k₂, Submodule.add_mem _ hk₁ hk₂, by rw [map_add, map_add, e₁, e₂]⟩
  | smul c x _ hx =>
    obtain ⟨S, h, hS⟩ := hx
    refine ⟨S, h, fun V g hg => ?_⟩
    obtain ⟨k, hk, e⟩ := hS g hg
    exact ⟨c • k, Submodule.smul_mem _ c hk, by rw [map_smul, map_smul, e]⟩

/-- A section of `P ⊗ N` whose image in `Q ⊗ N` vanishes is locally zero. -/
private lemma tensor_locInj_aux [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {P Q : PresheafOfModulesOfCommRing.{0} R₀} (N : PresheafOfModulesOfCommRing.{0} R₀)
    (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)] {U : C}
    (t : P.obj (op U) ⊗[ℤ] N.obj (op U))
    (ht : tensorInt (R₀.obj (op U)) (Q.obj (op U)) (N.obj (op U)) (zmap N f (op U) t) = 0) :
    Presheaf.equalizerSieve (F := ab (P ⊗ N)) (X := op U)
      (tensorInt (R₀.obj (op U)) (P.obj (op U)) (N.obj (op U)) t) 0 ∈ J U := by
  obtain ⟨S, hS, hSg⟩ := exists_local_lift J N f (U := U) _
    (mem_tensorRel_of_tensorInt_eq_zero _ _ _ ht)
  refine J.transitive hS _ (fun V g hg => ?_)
  obtain ⟨k, hk, e⟩ := hSg g hg
  have h0 : zmap N f (op V) (zres P N g.op t - k) = 0 := by
    rw [map_sub, e, zres_zmap, sub_self]
  obtain ⟨S', hS', hS'g⟩ := zTensor_locInj J (A := ab P) (B := ab Q) (T := ab N)
    ((PresheafOfModules.toPresheaf _).map f) (U := V) (zres P N g.op t - k) h0
  refine J.superset_covering (fun W g' hg' => ?_) hS'
  have h1 : zres P N g'.op (zres P N g.op t - k) = 0 := hS'g g' hg'
  rw [map_sub, sub_eq_zero] at h1
  have hπ : tensorInt (R₀.obj (op V)) (P.obj (op V)) (N.obj (op V)) k = 0 :=
    tensorInt_eq_zero_of_mem_tensorRel _ _ _ hk
  show ((P ⊗ N).map (g' ≫ g).op).hom
      (tensorInt (R₀.obj (op U)) (P.obj (op U)) (N.obj (op U)) t) =
    ((P ⊗ N).map (g' ≫ g).op).hom 0
  rw [map_zero, op_comp]
  let z : (P ⊗ N).obj (op U) := tensorInt (R₀.obj (op U)) (P.obj (op U)) (N.obj (op U)) t
  have a0 : ((P ⊗ N).map (g.op ≫ g'.op)).hom z =
      ((P ⊗ N).map g'.op).hom (((P ⊗ N).map g.op).hom z) :=
    PresheafOfModules.map_comp_apply (P ⊗ N) g.op g'.op z
  have a1 : ((P ⊗ N).map g.op).hom z =
      tensorInt (R₀.obj (op V)) (P.obj (op V)) (N.obj (op V)) (zres P N g.op t) :=
    tensorObj_map_tensorInt P N g.op t
  have a2 : ((P ⊗ N).map g'.op).hom
      (tensorInt (R₀.obj (op V)) (P.obj (op V)) (N.obj (op V)) (zres P N g.op t)) =
      tensorInt (R₀.obj (op W)) (P.obj (op W)) (N.obj (op W))
        (zres P N g'.op (zres P N g.op t)) :=
    tensorObj_map_tensorInt P N g'.op _
  have a3 : tensorInt (R₀.obj (op W)) (P.obj (op W)) (N.obj (op W)) (zres P N g'.op k) = 0 := by
    have := tensorObj_map_tensorInt P N g'.op k
    rw [hπ] at this
    exact this.symm.trans (map_zero _)
  rw [a0, a1, a2, h1, a3]
  rfl

/-- Tensoring a locally bijective map of presheaves of modules with `N` keeps it locally
injective. -/
theorem tensor_locInj [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {P Q : PresheafOfModulesOfCommRing.{0} R₀} (N : PresheafOfModulesOfCommRing.{0} R₀)
    (f : P ⟶ Q)
    [Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)] :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf _).map (f ▷ N)) := by
  constructor
  intro X x y hxy
  obtain ⟨U⟩ := X
  let x' : (P ⊗ N).obj (op U) := x
  let y' : (P ⊗ N).obj (op U) := y
  obtain ⟨t, ht⟩ := tensorInt_surjective (R₀.obj (op U)) (P.obj (op U)) (N.obj (op U)) (x' - y')
  have hxy' : ((f ▷ N).app (op U)).hom x' = ((f ▷ N).app (op U)).hom y' := hxy
  have h0 : tensorInt (R₀.obj (op U)) (Q.obj (op U)) (N.obj (op U)) (zmap N f (op U) t) = 0 := by
    rw [← whiskerRight_app_tensorInt, ht, map_sub, hxy', sub_self]
    rfl
  have := tensor_locInj_aux J N f t h0
  refine J.superset_covering (fun V g hg => ?_) this
  have e : x - y = tensorInt (R₀.obj (op U)) (P.obj (op U)) (N.obj (op U)) t := ht.symm
  have hg' : ((ab (P ⊗ N)).map g.op) (x - y) = 0 := by
    rw [e]
    exact hg.trans (map_zero _)
  rw [map_sub, sub_eq_zero] at hg'
  exact hg'

/-- Tensoring with `N` preserves locally surjective maps. -/
lemma tensor_locSurj {P Q : PresheafOfModulesOfCommRing.{0} R₀}
    (N : PresheafOfModulesOfCommRing.{0} R₀) (f : P ⟶ Q)
    [Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map f)] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map (f ▷ N)) := by
  constructor
  intro U y
  induction y using TensorProduct.inductionOn with
  | tmul q n =>
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J
      ((PresheafOfModules.toPresheaf _).map f) q)
    intro V g ⟨p, hp⟩
    refine ⟨p ⊗ₜ[R₀.obj (op V)] N.map g.op n, ?_⟩
    exact congrArg (· ⊗ₜ[R₀.obj (op V)] N.map g.op n) hp
  | add y y' hy hy' =>
    refine J.superset_covering ?_ (J.intersection_covering hy hy')
    rintro V g ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
    refine ⟨t + t', ?_⟩
    rw [map_add, ht, ht']
    exact (map_add _ y y').symm
end Assembly

end TensorLoc

end Cohesive
