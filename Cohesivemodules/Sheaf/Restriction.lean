import Cohesivemodules.Sheaf.RestrictionBasic

set_option linter.style.header false

/-!
# S5–S6: restriction, extension by zero, locality (part 2 of 2)

Split from `Sheaf/Restriction.lean` for size; continues `Sheaf/RestrictionBasic.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace Limits
variable {X : Type} [TopologicalSpace X] (R : RingSheaf X) (U : Opens X)
section Helpers
variable {R}

/-- A sheaf of modules that is locally zero is zero. -/
private lemma isZero_of_locally {c : Mod R}
    (hc : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsZero ((restr R U).obj c)) : IsZero c := by
  rw [IsZero.iff_id_eq_zero]
  refine eq_of_locally_eq _ _ fun V s x hx => ?_
  obtain ⟨U, hxU, hU⟩ := hc x
  refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
  have hz := (SheafOfModules.evaluation.{0} (R.over U)
    (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))).map_isZero hU
  have : Subsingleton (c.val.obj (op (V ⊓ U))) := (ModuleCat.isZero_iff_subsingleton).1 hz
  exact Subsingleton.elim _ _


/-- Sections of a kernel are computed sectionwise (any site). -/
private lemma kernel_sections {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {S : Sheaf J RingCat.{0}} {M N : Mod S} (g : M ⟶ N) (V : Cᵒᵖ) :
    Function.Injective ((kernel.ι g).val.app V) ∧
      ∀ s : M.val.obj V, g.val.app V s = 0 → ∃ u, (kernel.ι g).val.app V u = s := by
  have hex := ShortComplex.exact_kernel g
  have hex' := hex.map_of_mono_of_preservesKernel (SheafOfModules.evaluation.{0} S V)
    inferInstance inferInstance
  refine ⟨?_, (ShortComplex.moduleCat_exact_iff _).1 hex'⟩
  have : Mono ((SheafOfModules.evaluation.{0} S V).map (kernel.ι g)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

/-- A morphism of sheaves of modules that is surjective on sections over every object is epi. -/
private lemma epi_of_sections_surjective {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {S : Sheaf J RingCat.{0}} {M N : Mod S} (f : M ⟶ N)
    (hf : ∀ V : Cᵒᵖ, Function.Surjective (f.val.app V)) : Epi f := by
  refine ⟨fun g h hgh => ?_⟩
  ext V s
  obtain ⟨t, rfl⟩ := hf V s
  exact congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V) hgh)) t)

/-- Exactness of a short complex of sheaves of modules can be checked on sections over every
object (any site). -/
lemma exact_of_sections_exact {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {S : Sheaf J RingCat.{0}} (T : ShortComplex (Mod S))
    (h : ∀ V : Cᵒᵖ, (T.map (SheafOfModules.evaluation.{0} S V)).Exact) : T.Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  refine epi_of_sections_surjective _ fun V u => ?_
  obtain ⟨hinj, -⟩ := kernel_sections T.g V
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).1 (h V) ((kernel.ι T.g).val.app V u)
    (by
      have := congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V)
        (kernel.condition T.g))) u)
      exact this)
  refine ⟨t, hinj ?_⟩
  have := congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app V)
    (kernel.lift_ι T.g T.f T.zero))) t)
  exact this.trans ht

/-- A morphism of complexes in an abelian category is a quasi-isomorphism iff its mapping cone
is acyclic. -/
lemma quasiIso_iff_acyclic_mappingCone {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  have := (HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)
  exact this.trans (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/-- Naturality of a morphism of sheaves of modules with respect to restriction of sections. -/
private lemma mres_map {M N : Mod R} (φ : M ⟶ N) {U V : Opens X} (h : V ≤ U)
    (s : M.val.obj (op U)) :
    φ.val.app (op V) (mres M h s) = mres N h (φ.val.app (op U) s) :=
  congr(ModuleCat.Hom.hom $(φ.val.naturality (homOfLE h).op) s)

/-- A morphism of sheaves of modules that is locally surjective on sections is epi. -/
private lemma epi_of_locally_surjective {M N : Mod R} (f : M ⟶ N)
    (h : ∀ (V : Opens X) (u : N.val.obj (op V)), ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V),
      x ∈ W ∧ ∃ t : M.val.obj (op W), f.val.app (op W) t = mres N hW u) : Epi f := by
  refine ⟨fun g k hgk => eq_of_locally_eq g k fun V s x hx => ?_⟩
  obtain ⟨W, hW, hxW, t, ht⟩ := h V s x hx
  refine ⟨W, hW, hxW, ?_⟩
  rw [← ht]
  exact congr(ModuleCat.Hom.hom ($(congrArg (fun m => m.val.app (op W)) hgk)) t)

end Helpers

/-! ## S5.b Extension by zero -/

/-- **S5.b.** Extension by zero `j_!` for the inclusion of the open `U`: the left adjoint of
restriction. (Mathlib's `SheafOfModules.pullback (𝟙 _)` is defined in the same way.) -/
abbrev extZero : Mod (R.over U) ⥤ Mod R :=
  (restr R U).leftAdjoint

/-- **S5.b.** `j_! ⊣ (-)|U`. -/
def extZeroAdj : extZero R U ⊣ restr R U :=
  Adjunction.ofIsRightAdjoint _

/-- Reduction of left exactness of `j_!`: it follows from the unit being an isomorphism and the
local vanishing of sections of `j_! M` outside `U`. -/
private lemma extZero_preservesMonomorphisms_aux
    (hunit : ∀ M : Mod (R.over U), IsIso ((extZeroAdj R U).unit.app M))
    (hloc : ∀ (M : Mod (R.over U)) {V : Opens X}
      (s : ((extZero R U).obj M).val.obj (op V)) {x : X} (_ : x ∈ V) (_ : x ∉ U),
      ∃ (W : Opens X) (h : W ≤ V), x ∈ W ∧ mres ((extZero R U).obj M) h s = 0) :
    (extZero R U).PreservesMonomorphisms := by
  refine ⟨fun {M M'} f hf => ?_⟩
  set T := (extZero R U).obj M with hT
  set g := (extZero R U).map f with hg
  have := hunit M
  have hmono : Mono ((restr R U).map g) := by
    have h1 : (extZeroAdj R U).unit.app M ≫ (restr R U).map g =
        f ≫ (extZeroAdj R U).unit.app M' :=
      ((extZeroAdj R U).unit.naturality f).symm
    have h2 : Mono ((extZeroAdj R U).unit.app M ≫ (restr R U).map g) := by
      rw [h1]
      have := hunit M'
      infer_instance
    have h3 : (restr R U).map g =
        inv ((extZeroAdj R U).unit.app M) ≫
          ((extZeroAdj R U).unit.app M ≫ (restr R U).map g) := by
      rw [IsIso.inv_hom_id_assoc]
    rw [h3]
    infer_instance
  have hker : kernel.ι g = 0 := by
    refine eq_of_locally_eq _ _ fun V t x hx => ?_
    by_cases hxU : x ∈ U
    · refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
      have h0 : (restr R U).map (kernel.ι g) = 0 := by
        rw [← cancel_mono ((restr R U).map g), ← Functor.map_comp, kernel.condition,
          Functor.map_zero, zero_comp]
      have := congr(ModuleCat.Hom.hom ($(congrArg (fun m => m.val.app
        (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))) h0)) (mres _ inf_le_left t))
      exact this
    · obtain ⟨W, hW, hxW, hz⟩ := hloc M ((kernel.ι g).val.app (op V) t) hx hxU
      refine ⟨W, hW, hxW, ?_⟩
      rw [mres_map, hz]
      rfl
  exact Preadditive.mono_of_kernel_zero hker

/-- Reduction of left exactness of `j_!` to the two other properties of S5.b (unit iso and local
vanishing): `extZero_preservesFiniteLimits` follows from `isIso_extZeroAdj_unit` and
`extZero_locally_zero` by this lemma. -/
private lemma extZero_preservesFiniteLimits_aux
    (hunit : ∀ M : Mod (R.over U), IsIso ((extZeroAdj R U).unit.app M))
    (hloc : ∀ (M : Mod (R.over U)) {V : Opens X}
      (s : ((extZero R U).obj M).val.obj (op V)) {x : X} (_ : x ∈ V) (_ : x ∉ U),
      ∃ (W : Opens X) (h : W ≤ V), x ∈ W ∧ mres ((extZero R U).obj M) h s = 0) :
    PreservesFiniteLimits (extZero R U) := by
  have := extZero_preservesMonomorphisms_aux R U hunit hloc
  have : (extZero R U).PreservesZeroMorphisms := inferInstance
  have : (extZero R U).Additive := by
    have : PreservesBinaryBiproducts (extZero R U) :=
      Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (extZero R U).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels _
  exact Functor.preservesFiniteLimits_of_preservesHomology _

/-- The unit of `Over.forget U ⊣ Over.star U` is an isomorphism (the site is a poset). -/
private lemma isIso_forgetAdjStar_unit (Y : Over U) :
    IsIso ((Over.forgetAdjStar U).unit.app Y) := by
  have : IsIso (Over.forget U |>.map ((Over.forgetAdjStar U).unit.app Y)) := by
    show IsIso ((Over.forgetAdjStar U).unit.app Y).left
    rw [Over.forgetAdjStar_unit_app_left]
    exact ⟨prod.snd, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact isIso_of_reflects_iso _ (Over.forget U)

/-- The counit of `(-)|U ⊣ j_*` is an isomorphism (`j_*` is fully faithful). -/
private lemma isIso_overPushforwardOverAdj_counit (M : Mod (R.over U)) :
    IsIso ((SheafOfModules.overPushforwardOverAdj.{0} (R := R) U).counit.app M) := by
  have h2 : IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf _).map
      ((SheafOfModules.overPushforwardOverAdj.{0} (R := R) U).counit.app M))) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun Y => ?_
    have := isIso_forgetAdjStar_unit U Y.unop
    exact (inferInstance : IsIso (M.val.presheaf.map ((Over.forgetAdjStar U).unit.app Y.unop).op))
  have h3 : IsIso ((SheafOfModules.toSheaf _).map
      ((SheafOfModules.overPushforwardOverAdj.{0} (R := R) U).counit.app M)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- **S5.b.** `(j_! M)|U ≅ M`: the unit of `j_! ⊣ (-)|U` is an isomorphism (stalks of `j_! M`
at points of `U` are those of `M`). Proof: adjoint triple `j_! ⊣ (-)|U ⊣ j_*` with `j_*`
(pushforward along `Over.star U`) fully faithful. -/
theorem isIso_extZeroAdj_unit (M : Mod (R.over U)) : IsIso ((extZeroAdj R U).unit.app M) := by
  let t : Adjunction.Triple (extZero R U) (restr R U) _ :=
    ⟨extZeroAdj R U, SheafOfModules.overPushforwardOverAdj.{0} (R := R) U⟩
  have : IsIso t.adj₂.counit :=
    haveI : ∀ N, IsIso (t.adj₂.counit.app N) := isIso_overPushforwardOverAdj_counit R U
    NatIso.isIso_of_isIso_app _
  have := t.isIso_unit_iff_isIso_counit.2 this
  exact NatIso.isIso_app_of_isIso _ M

section ZeroOutside

variable {R}

/-- Restriction of sections is functorial. -/
private lemma mres_mres' (N : Mod R) {A B C : Opens X} (h1 : B ≤ A) (h2 : C ≤ B)
    (s : N.val.obj (op A)) : mres N h2 (mres N h1 s) = mres N (h2.trans h1) s :=
  (N.val.map_comp_apply (homOfLE h1).op (homOfLE h2).op s).symm

/-- Restriction of sections is linear over restriction of scalars. -/
private lemma mres_smul' (N : Mod R) {A B : Opens X} (h : B ≤ A) (r : R.obj.obj (op A))
    (s : N.val.obj (op A)) : mres N h (r • s) = rres R h r • mres N h s :=
  N.val.map_smul (homOfLE h).op r s

/-- Restriction of sections is additive. -/
private lemma mres_add' (N : Mod R) {A B : Opens X} (h : B ≤ A) (s s' : N.val.obj (op A)) :
    mres N h (s + s') = mres N h s + mres N h s' :=
  map_add (N.val.map (homOfLE h).op).hom s s'

/-- Restriction of the zero section is zero. -/
private lemma mres_zero' (N : Mod R) {A B : Opens X} (h : B ≤ A) :
    mres N h (0 : N.val.obj (op A)) = 0 :=
  map_zero (N.val.map (homOfLE h).op).hom

/-- The sheaf submodule of sections of `N` that vanish near every point outside `U`. -/
private def zeroOutside (N : Mod R) : N.Submodule where
  obj V :=
    { carrier := {s | ∀ x ∈ V.unop, x ∉ U →
        ∃ (W : Opens X) (h : W ≤ V.unop), x ∈ W ∧ mres N h s = 0}
      add_mem' := by
        intro s s' hs hs' x hx hxU
        obtain ⟨W, hW, hxW, h1⟩ := hs x hx hxU
        obtain ⟨W', hW', hxW', h2⟩ := hs' x hx hxU
        refine ⟨W ⊓ W', inf_le_left.trans hW, ⟨hxW, hxW'⟩, ?_⟩
        have e1 := mres_mres' N hW (inf_le_left : W ⊓ W' ≤ W) s
        have e2 := mres_mres' N hW' (inf_le_right : W ⊓ W' ≤ W') s'
        rw [mres_add', ← e1, ← e2, h1, h2]
        rw [mres_zero', mres_zero', add_zero]
      zero_mem' := by
        intro x hx hxU
        exact ⟨V.unop, le_rfl, hx, map_zero _⟩
      smul_mem' := by
        intro r s hs x hx hxU
        obtain ⟨W, hW, hxW, h1⟩ := hs x hx hxU
        refine ⟨W, hW, hxW, ?_⟩
        rw [mres_smul', h1, smul_zero] }
  map := by
    intro A B g s hs x hx hxU
    obtain ⟨W, hW, hxW, h1⟩ := hs x (leOfHom g.unop hx) hxU
    refine ⟨W ⊓ B.unop, inf_le_right, ⟨hxW, hx⟩, ?_⟩
    show mres N _ (mres N (leOfHom g.unop) s) = 0
    rw [mres_mres']
    have e1 := mres_mres' N hW (inf_le_left : W ⊓ B.unop ≤ W) s
    rw [show (inf_le_right.trans (leOfHom g.unop) : W ⊓ B.unop ≤ A.unop) =
      (inf_le_left.trans hW) from rfl, ← e1, h1, mres_zero']
  isSheaf := by
    intro A s hs x hx hxU
    obtain ⟨V, g, hg, hxV⟩ := hs x hx
    obtain ⟨W, hW, hxW, h1⟩ := hg x hxV hxU
    refine ⟨W, hW.trans g.le, hxW, ?_⟩
    have e1 := mres_mres' N g.le hW s
    rw [← e1]
    exact h1

/-- Restricting the inclusion of `zeroOutside` to `U` gives an isomorphism (no points outside
`U` in the over-site). -/
private lemma isIso_restr_zeroOutside (N : Mod R) :
    IsIso ((restr R U).map (zeroOutside U N).ι) := by
  have h2 : IsIso ((sheafToPresheaf _ _).map ((SheafOfModules.toSheaf _).map
      ((restr R U).map (zeroOutside U N).ι))) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun Y => ?_
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab => Subtype.ext hab, fun t => ?_⟩
    exact ⟨⟨t, fun x hx hxU => absurd (Y.unop.hom.le hx) hxU⟩, rfl⟩
  have h3 : IsIso ((SheafOfModules.toSheaf _).map ((restr R U).map (zeroOutside U N).ι)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

end ZeroOutside

/-- **S5.b.** Sections of `j_! M` vanish near every point outside `U` (the stalk of `j_! M` at
`x ∉ U` is zero). Proof: the submodule `B ⊆ j_! M` of sections vanishing near points outside `U`
receives the unit `M → (j_! M)|U` (as `(restr B) ≅ (restr j_! M)`), so by adjunction the
identity of `j_! M` factors through `B`. -/
theorem extZero_locally_zero (M : Mod (R.over U)) {V : Opens X}
    (s : ((extZero R U).obj M).val.obj (op V)) {x : X} (hxV : x ∈ V) (hxU : x ∉ U) :
    ∃ (W : Opens X) (h : W ≤ V), x ∈ W ∧ mres ((extZero R U).obj M) h s = 0 := by
  have hiso := isIso_restr_zeroOutside U ((extZero R U).obj M)
  let lam : M ⟶ (restr R U).obj (zeroOutside U ((extZero R U).obj M)).toSheafOfModules :=
    (extZeroAdj R U).unit.app M ≫ inv ((restr R U).map (zeroOutside U ((extZero R U).obj M)).ι)
  let σ : (extZero R U).obj M ⟶ (zeroOutside U ((extZero R U).obj M)).toSheafOfModules :=
    ((extZeroAdj R U).homEquiv _ _).symm lam
  have hσ : σ ≫ (zeroOutside U ((extZero R U).obj M)).ι = 𝟙 ((extZero R U).obj M) := by
    apply ((extZeroAdj R U).homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
      CategoryTheory.Functor.map_id,
      ← Category.assoc, ← Adjunction.homEquiv_unit]
    have : (extZeroAdj R U).homEquiv _ _ σ = lam := Equiv.apply_symm_apply _ _
    rw [this]
    simp only [lam, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (Category.comp_id _).symm
  have h1 : (σ ≫ (zeroOutside U ((extZero R U).obj M)).ι).val.app (op V) s = s := by
    rw [hσ]; rfl
  have h2 := (σ.val.app (op V) s).2 x hxV hxU
  rw [← h1]
  exact h2

/-- **S5.b.** `j_!` is exact (it is a left adjoint, so right exact; left exactness is the
stalk argument: `j_! M` is the sheafification of the presheaf extension by zero, which is
sectionwise exact). -/
theorem extZero_preservesFiniteLimits : PreservesFiniteLimits (extZero R U) :=
  extZero_preservesFiniteLimits_aux R U (isIso_extZeroAdj_unit R U)
    (fun M _ s _ hx hU => extZero_locally_zero R U M s hx hU)

instance : PreservesFiniteLimits (extZero R U) := extZero_preservesFiniteLimits R U


/-! ## S5.c Injectives -/

/-- **S5.c.** Restriction preserves injective objects: its left adjoint `j_!` is exact
(S5.b). -/
instance restr_injective (I : Mod R) [Injective I] : Injective ((restr R U).obj I) :=
  (extZeroAdj R U).map_injective I inferInstance

/-! ## S6 Locality -/

variable {R}

/-- **S6.** Exactness of a short complex of sheaves of modules is local on sections: `S` is
exact iff every section of `S.X₂` over `U` killed by `S.g` comes, near every point of `U`, from a
section of `S.X₁`. -/
theorem shortComplex_exact_iff (S : ShortComplex (Mod R)) :
    S.Exact ↔ ∀ (U : Opens X) (s : S.X₂.val.obj (op U)), S.g.val.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
        ∃ t : S.X₁.val.obj (op V), S.f.val.app (op V) t = mres S.X₂ h s := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have hκι : ∀ (V : Opens X) (t : S.X₁.val.obj (op V)),
      (kernel.ι S.g).val.app (op V) ((kernel.lift S.g S.f S.zero).val.app (op V) t) =
        S.f.val.app (op V) t := fun V t =>
    congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op V))
      (kernel.lift_ι S.g S.f S.zero))) t)
  constructor
  · intro hepi U s hs x hx
    obtain ⟨-, hsurj⟩ := kernel_sections S.g (op U)
    obtain ⟨u, hu⟩ := hsurj s hs
    obtain ⟨V, hVU, hxV, t, ht⟩ := exists_local_preimage_of_epi
      (kernel.lift S.g S.f S.zero) u hx
    refine ⟨V, hVU, hxV, t, ?_⟩
    rw [← hκι, ht, mres_map, hu]
  · intro h
    refine epi_of_locally_surjective _ fun V u x hx => ?_
    obtain ⟨hinj, -⟩ := kernel_sections S.g (op V)
    have hg : S.g.val.app (op V) ((kernel.ι S.g).val.app (op V) u) = 0 :=
      congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op V))
        (kernel.condition S.g))) u)
    obtain ⟨W, hW, hxW, t, ht⟩ := h V _ hg x hx
    refine ⟨W, hW, hxW, t, ?_⟩
    obtain ⟨hinjW, -⟩ := kernel_sections S.g (op W)
    apply hinjW
    rw [hκι, ht, mres_map]

/-- **S6.** A complex of `R`-modules whose restrictions to the members of an open cover are
acyclic is acyclic. -/
theorem acyclic_of_locally {K : CochainComplex (Mod R) ℤ}
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      (((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic) :
    K.Acyclic := by
  intro i
  show (K.sc i).Exact
  rw [ShortComplex.exact_iff_isZero_homology]
  refine isZero_of_locally fun x => ?_
  obtain ⟨U, hxU, hU⟩ := h x
  refine ⟨U, hxU, ?_⟩
  have h1 : ((K.sc i).map (restr R U)).Exact := hU i
  rw [ShortComplex.exact_iff_isZero_homology] at h1
  exact h1.of_iso ((K.sc i).mapHomologyIso (restr R U)).symm

/-- **S6.** A map of complexes of `R`-modules whose restrictions to the members of an open cover
are quasi-isomorphisms is a quasi-isomorphism. (The converse holds by S5.a.) -/
theorem quasiIso_of_locally {K L : CochainComplex (Mod R) ℤ} (f : K ⟶ L)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      QuasiIso (((restr R U).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :
    QuasiIso f := by
  rw [quasiIso_iff_acyclic_mappingCone]
  refine acyclic_of_locally fun x => ?_
  obtain ⟨U, hxU, hq⟩ := h x
  refine ⟨U, hxU, ?_⟩
  have hc := (quasiIso_iff_acyclic_mappingCone _).1 hq
  exact fun i => (hc i).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (restr R U)).symm

/-- **S6. Sectionwise quasi-isomorphisms.** On any site (in particular the over-sites `Over U`
of restrictions), a map of complexes of sheaves of modules that is a quasi-isomorphism on
sections over every object is a quasi-isomorphism (homology sheaves are sheafifications of the
presheaf homology). Covers sectionwise homotopy equivalences. -/
theorem quasiIso_of_sectionwise {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {S : Sheaf J RingCat.{0}} {K L : CochainComplex (Mod S) ℤ} (f : K ⟶ L)
    (h : ∀ V : Cᵒᵖ, QuasiIso
      (((SheafOfModules.evaluation.{0} S V).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :
    QuasiIso f := by
  rw [quasiIso_iff_acyclic_mappingCone]
  intro i
  refine exact_of_sections_exact _ fun V => ?_
  have hc := (quasiIso_iff_acyclic_mappingCone _).1 (h V)
  exact (hc i).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (SheafOfModules.evaluation.{0} S V)).symm

end Cohesive
