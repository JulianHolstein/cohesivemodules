import Cohesivemodules.Sheaf.Fine
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

set_option linter.style.header false

/-!
# S4: projective modules over a fine sheaf

Blueprint item S4 (§3). S4.a free modules over a fine sheaf on compact `X` are projective; S4.b
locally direct summands of finite free modules are direct summands of finite free modules;
S4.c `Γ` on direct summands of finite free modules. Split of blueprint §7's `Fine.lean` (size
only).

## Deviations
* S4.a is proved for free modules on any index type, not only finite ones.
* S4.b needs `R` commutative (`IsComm R`): `ρ • φ` is `R`-linear only for central `ρ`.
  Blueprint §3 assumes commutative rings throughout.
* S4.c is stated as: `Γ` of a direct summand of a finite free module is finitely generated
  projective, `Γ` is bijective on morphisms out of such a module (into any module), and every
  finitely generated projective `R(X)`-module is `Γ` of one. The explicit inverse
  `P̃(U) = R(U) ⊗_{R(X)} P` is not formalized here (it enters C1.a); S4.d needs the tensor
  product of sheaves of modules and is stated with S8. S4.c needs neither fineness nor
  compactness.

Part 1 of 2 of the original `Sheaf/Projective.lean`, split for size; continued in
`Sheaf/Projective.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

variable {X : Type} [TopologicalSpace X]

/-! ## S4 Projective modules over a fine sheaf -/

/-- Auxiliary: a section of a sheaf of modules is determined by its value at `⊤`. -/
theorem sections_eq_of_top {R : RingSheaf X} {N : Mod R} (s t : N.sections)
    (h : s.1 (op ⊤) = t.1 (op ⊤)) : s = t := by
  apply PresheafOfModules.sections_ext
  intro U
  have h1 := PresheafOfModules.sections_property s (X := op ⊤) (Y := U) (homOfLE le_top).op
  have h2 := PresheafOfModules.sections_property t (X := op ⊤) (Y := U) (homOfLE le_top).op
  rw [← h1, ← h2, h]

/-- Auxiliary: every element of `N(⊤)` is the value at `⊤` of a section of `N`. -/
private theorem exists_section_of_top {R : RingSheaf X} {N : Mod R} (s0 : N.val.obj (op ⊤)) :
    ∃ x : N.sections, x.1 (op ⊤) = s0 := by
  refine ⟨PresheafOfModules.sectionsMk
    (fun U => N.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s0) (by
      intro U V g
      rw [← PresheafOfModules.map_comp_apply]
      rw [show (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ g = (homOfLE (le_top : V.unop ≤ ⊤)).op from
        Subsingleton.elim _ _]), ?_⟩
  show ConcreteCategory.hom (N.val.map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op) s0 = s0
  rw [show (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _]
  simp only [PresheafOfModules.map_id]
  rfl

/-- **S4.a.** For `R` fine on compact `X`, free `R`-modules are projective:
`Hom(R^{(I)}, M) = Γ(M)^I` and S2. ⚠ Any index type `I`, not only finite ones. -/
theorem projective_free [CompactSpace X] {R : RingSheaf X} (hR : IsFine R) (I : Type) :
    Projective (SheafOfModules.free (R := R) I) := by
  refine ⟨fun {E N} f e _ => ?_⟩
  have key : ∀ i : I, ∃ x : E.sections,
      SheafOfModules.sectionsMap e x = SheafOfModules.freeHomEquiv N f i := by
    intro i
    obtain ⟨t0, ht0⟩ := surjective_globalSections_of_epi hR e
      ((SheafOfModules.freeHomEquiv N f i).1 (op ⊤))
    obtain ⟨x, hx⟩ := exists_section_of_top (N := E) t0
    refine ⟨x, sections_eq_of_top _ _ ?_⟩
    show (e.val.app (op ⊤)).hom (x.1 (op ⊤)) = _
    rw [hx]
    exact ht0
  choose x hx using key
  refine ⟨(SheafOfModules.freeHomEquiv E).symm x, ?_⟩
  rw [SheafOfModules.freeHomEquiv_symm_comp]
  apply (SheafOfModules.freeHomEquiv N).injective
  rw [Equiv.apply_symm_apply]
  funext i
  exact hx i

/-- **S4.a, summands.** For `R` fine on compact `X`, direct summands of finite free
`R`-modules are projective. -/
theorem projective_of_isFinFreeSummand [CompactSpace X] {R : RingSheaf X} (hR : IsFine R)
    {M : Mod R} (hM : IsFinFreeSummand M) : Projective M := by
  obtain ⟨m, i, p, hip⟩ := hM
  have := projective_free hR (Fin m)
  exact Retract.projective (X := M) (Y := SheafOfModules.free (Fin m)) ⟨i, p, hip⟩

/-- Auxiliary: sections of a sheaf of modules that agree locally are equal. -/
private theorem eq_of_locally_eq {R : RingSheaf X} {M : Mod R} (V : Opens X)
    (y z : M.val.obj (op V))
    (h : ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧ mres M hW y = mres M hW z) :
    y = z := by
  have hsep := Presheaf.IsSheaf.isSeparated M.isSheaf
  obtain ⟨y', hy'⟩ : ∃ y' : M.val.presheaf.obj (op V), y' = y := ⟨y, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : M.val.presheaf.obj (op V), z' = z := ⟨z, rfl⟩
  rw [← hy', ← hz'] at h ⊢
  refine hsep V ⟨fun {Y} f => M.val.presheaf.map f.op y' = M.val.presheaf.map f.op z', ?_⟩
    ?_ y' z' ?_
  · intro Y Z f hf g
    simp only at hf ⊢
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hf]
  · intro x hx
    obtain ⟨W, hW, hxW, hz⟩ := h x hx
    exact ⟨W, homOfLE hW, hz, hxW⟩
  · intro Y f hf
    exact hf

/-- Auxiliary: ring sections that agree locally are equal. -/
private theorem ring_eq_of_locally_eq {R : RingSheaf X} (V : Opens X) (y z : R.obj.obj (op V))
    (h : ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧ rres R hW y = rres R hW z) :
    y = z :=
  eq_of_locally_eq (M := SheafOfModules.unit R) V y z h

/-- Auxiliary: restriction of sections is semilinear over the restriction of the ring. -/
private theorem mres_smul {R : RingSheaf X} {M : Mod R} {V W : Opens X} (h : W ≤ V)
    (r : R.obj.obj (op V)) (m : M.val.obj (op V)) :
    mres M h (r • m) = rres R h r • mres M h m :=
  LinearMap.map_smul (ModuleCat.Hom.hom (M.val.map (homOfLE h).op)) r m

/-- Auxiliary: restrictions of ring sections compose. -/
private theorem rres_rres {R : RingSheaf X} {V W Y : Opens X} (h1 : W ≤ V) (h2 : Y ≤ W)
    (r : R.obj.obj (op V)) : rres R h2 (rres R h1 r) = rres R (h2.trans h1) r := by
  show (R.obj.map (homOfLE h2).op).hom ((R.obj.map (homOfLE h1).op).hom r) = _
  rw [← RingCat.comp_apply, ← R.obj.map_comp]
  rfl

/-- Auxiliary: morphisms of sheaves of modules commute with restriction of sections. -/
private theorem mres_hom {R : RingSheaf X} {M N : Mod R} (f : M ⟶ N) {V W : Opens X}
    (h : W ≤ V) (m : M.val.obj (op V)) :
    mres N h ((f.val.app (op V)).hom m) = (f.val.app (op W)).hom (mres M h m) := by
  have := congr(ModuleCat.Hom.hom $(f.val.naturality (homOfLE h).op) m)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  exact this.symm

/-- Auxiliary: `restrApp` is linear over the ring of sections. -/
private theorem restrApp_smul {R : RingSheaf X} {M N : Mod R} {U V : Opens X}
    (φ : (restr R U).obj M ⟶ (restr R U).obj N)
    (h : V ≤ U) (r : R.obj.obj (op V)) (m : M.val.obj (op V)) :
    restrApp φ h (r • m) = r • restrApp φ h m :=
  LinearMap.map_smul (ModuleCat.Hom.hom (φ.val.app (op (Over.mk (homOfLE h))))) r m

/-- Auxiliary: if `ρ` and `ψ` are supported in `U` with `ψρ = ρ` and `φ' ∘ φ = 1` on `U`, then
`φ`, `φ'` extend by zero to global maps `σ : M → N`, `π : N → M` with `π σ = ρ • 1`. -/
private theorem local_summand_split {R : RingSheaf X} (hc : IsComm R) {M N : Mod R}
    {U : Opens X} {ρ ψ : R.obj.obj (op ⊤)} (hρ : SupportedIn ρ U) (hψ : SupportedIn ψ U)
    (hψρ : ψ * ρ = ρ)
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) (φ' : (restr R U).obj N ⟶ (restr R U).obj M)
    (hφ : φ ≫ φ' = 𝟙 _) :
    ∃ (σ : M ⟶ N) (π : N ⟶ M), ∀ (V : Opens X) (m : M.val.obj (op V)),
      (π.val.app (op V)).hom ((σ.val.app (op V)).hom m) = rres R (le_top : V ≤ ⊤) ρ • m := by
  obtain ⟨σ, hσ1, hσ2⟩ := exists_hom_extend hc hρ φ
  obtain ⟨π, hπ1, hπ2⟩ := exists_hom_extend hc hψ φ'
  refine ⟨σ, π, fun V m => ?_⟩
  apply eq_of_locally_eq
  intro x hx
  obtain ⟨W, hUW, hW0⟩ := hρ
  have hxUW : x ∈ U ⊔ W := by rw [hUW]; trivial
  rcases (Opens.mem_sup.1 hxUW) with hxU | hxW
  · refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
    have hVU : V ⊓ U ≤ U := inf_le_right
    rw [mres_hom, mres_hom, mres_smul, hσ1 _ hVU, hπ1 _ hVU, restrApp_smul, smul_smul,
      rres_rres, ← map_mul, hψρ]
    have key : ∀ m' : M.val.obj (op (V ⊓ U)), restrApp φ' hVU (restrApp φ hVU m') = m' := by
      intro m'
      have : restrApp (φ ≫ φ') hVU m' = m' := by rw [hφ]; rfl
      exact this
    rw [key]
  · refine ⟨V ⊓ W, inf_le_left, ⟨hx, hxW⟩, ?_⟩
    have h0 : rres R (le_top : V ⊓ W ≤ ⊤) ρ = 0 := by
      have := rres_rres (R := R) (le_top : W ≤ ⊤) (inf_le_right : V ⊓ W ≤ W) ρ
      rw [hW0, map_zero] at this
      exact this.symm
    rw [mres_hom, mres_hom, mres_smul, hσ2 _ h0, rres_rres]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero, h0, zero_smul]

/-- Auxiliary: for `ρ` supported in `U` and `R` fine there is `ψ` supported in `U` with
`ψρ = ρ`. -/
private theorem exists_cutoff {R : RingSheaf X} (hR : IsFine R) {ρ : R.obj.obj (op ⊤)}
    {U : Opens X} (hρ : SupportedIn ρ U) :
    ∃ ψ : R.obj.obj (op ⊤), SupportedIn ψ U ∧ ψ * ρ = ρ := by
  obtain ⟨W, hUW, hW0⟩ := hρ
  obtain ⟨a, ha1, haS⟩ := hR Bool (fun b => if b then U else W) (by
    rw [iSup_bool_eq]; simpa using hUW)
  have hsum : a true + a false = 1 := by
    rw [Fintype.sum_bool] at ha1; exact ha1
  refine ⟨a true, haS true, ?_⟩
  obtain ⟨V', hV', hV'0⟩ := haS false
  have h0 : a false * ρ = 0 := by
    apply ring_eq_of_locally_eq
    intro x hx
    have hx' : x ∈ W ⊔ V' := by
      have hV'' : W ⊔ V' = ⊤ := by simpa using hV'
      rw [hV'']; trivial
    rcases Opens.mem_sup.1 hx' with hxW | hxV
    · refine ⟨W, le_top, hxW, ?_⟩
      rw [map_mul, hW0, mul_zero, map_zero]
    · refine ⟨V', le_top, hxV, ?_⟩
      rw [map_mul, hV'0, zero_mul, map_zero]
  rw [eq_sub_of_add_eq hsum, sub_mul, one_mul, h0, sub_zero]

/-- Auxiliary: the value of a finite sum of morphisms at a section is the sum of the values. -/
private theorem app_sum {R : RingSheaf X} {M N : Mod R} {ι : Type} (s : Finset ι)
    (g : ι → (M ⟶ N)) (V : Opens X) (m : M.val.obj (op V)) :
    ((∑ j ∈ s, g j).val.app (op V)).hom m = ∑ j ∈ s, ((g j).val.app (op V)).hom m := by
  have : (SheafOfModules.evaluation.{0} R (op V)).Additive := ⟨rfl⟩
  have := (SheafOfModules.evaluation.{0} R (op V)).map_sum g s
  have h2 := congrArg (fun k => k.hom (m : (SheafOfModules.evaluation.{0} R (op V)).obj M)) this
  simp only [ModuleCat.hom_sum] at h2
  exact h2.trans (LinearMap.sum_apply s (fun i => ModuleCat.Hom.hom
    ((SheafOfModules.evaluation.{0} R (op V)).map (g i))) m)

/-- Auxiliary: morphisms of sheaves of modules that agree on all sections are equal. -/
private theorem hom_eq_of_app {R : RingSheaf X} {M N : Mod R} (f g : M ⟶ N)
    (h : ∀ (V : Opens X) (m : M.val.obj (op V)),
      (f.val.app (op V)).hom m = (g.val.app (op V)).hom m) :
    f = g := by
  ext V m
  exact h V.unop m

/-- Auxiliary: `freeMap` is compatible with composition. -/
private theorem freeMap_comp_freeMap {R : RingSheaf X} {I J K : Type} (f : I → J) (g : J → K) :
    SheafOfModules.freeMap (R := R) f ≫ SheafOfModules.freeMap g =
      SheafOfModules.freeMap (g ∘ f) := by
  apply (SheafOfModules.freeHomEquiv _).injective
  funext i
  rw [SheafOfModules.freeHomEquiv_comp_apply, SheafOfModules.freeHomEquiv_freeMap,
    SheafOfModules.freeHomEquiv_freeMap]
  simp only [Function.comp_apply, SheafOfModules.sectionMap_freeMap_freeSection]

/-- Auxiliary: `freeMap id = 𝟙`. -/
private theorem freeMap_id {R : RingSheaf X} {I : Type} :
    SheafOfModules.freeMap (R := R) (id : I → I) = 𝟙 _ := by
  apply (SheafOfModules.freeHomEquiv _).injective
  funext i
  rw [SheafOfModules.freeHomEquiv_freeMap]
  rfl

/-- Auxiliary: if `∑ σⱼ πⱼ = 1` for maps through finite free modules, `M` is a summand of a
finite free module. -/
private theorem isFinFreeSummand_of_family {R : RingSheaf X} {M : Mod R} {ι : Type} [Fintype ι]
    (m : ι → ℕ) (σ : ∀ j, M ⟶ SheafOfModules.free (Fin (m j)))
    (π : ∀ j, SheafOfModules.free (Fin (m j)) ⟶ M) (h : ∑ j, σ j ≫ π j = 𝟙 M) :
    IsFinFreeSummand M := by
  let T := Σ j, Fin (m j)
  let πT : SheafOfModules.free (R := R) T ⟶ M := (SheafOfModules.freeHomEquiv M).symm
    (fun t => SheafOfModules.sectionsMap (π t.1) (SheafOfModules.freeSection t.2))
  have hπ : ∀ j, SheafOfModules.freeMap (R := R) (Sigma.mk (β := fun j => Fin (m j)) j :
      Fin (m j) → T) ≫ πT = π j := by
    intro j
    apply (SheafOfModules.freeHomEquiv M).injective
    funext k
    rw [SheafOfModules.freeHomEquiv_comp_apply, SheafOfModules.freeHomEquiv_freeMap,
      Function.comp_apply, ← SheafOfModules.freeHomEquiv_apply, Equiv.apply_symm_apply,
      SheafOfModules.freeHomEquiv_apply]
  let σT : M ⟶ SheafOfModules.free (R := R) T :=
    ∑ j, σ j ≫ SheafOfModules.freeMap (Sigma.mk (β := fun j => Fin (m j)) j : Fin (m j) → T)
  have hσπ : σT ≫ πT = 𝟙 M := by
    rw [← h, Preadditive.sum_comp]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Category.assoc, hπ]
  let e : T ≃ Fin (Fintype.card T) := Fintype.equivFin T
  refine ⟨Fintype.card T, σT ≫ SheafOfModules.freeMap e,
    SheafOfModules.freeMap e.symm ≫ πT, ?_⟩
  rw [Category.assoc, ← Category.assoc (SheafOfModules.freeMap e), freeMap_comp_freeMap]
  have : (e.symm ∘ e : T → T) = id := funext e.symm_apply_apply
  rw [this, freeMap_id, Category.id_comp, hσπ]

/-- Auxiliary: restriction of a free module is free (the iso is Mathlib's `mapFreeIso`). -/
private theorem nonempty_restr_free (R : RingSheaf X) (U : Opens X) (I : Type) :
    Nonempty ((restr R U).obj (SheafOfModules.free I) ≅
      SheafOfModules.free (R := R.over U) I) := by
  have : (restr R U).IsLeftAdjoint :=
    inferInstanceAs (SheafOfModules.pushforward.{0} (𝟙 (R.over U))).IsLeftAdjoint
  exact ⟨(SheafOfModules.mapFreeIso (restr R U) I (Iso.refl _)).symm⟩

/-- Auxiliary: if `M|U` is a summand of a finite free module and `ρ` is supported in `U`, there
are maps `σ : M → Rᵐ`, `π : Rᵐ → M` with `π σ = ρ • 1`. -/
private theorem exists_local_split {R : RingSheaf X} (hR : IsFine R) (hc : IsComm R)
    {M : Mod R} {U : Opens X} (hU : IsFinFreeSummand ((restr R U).obj M))
    {ρ : R.obj.obj (op ⊤)} (hρ : SupportedIn ρ U) :
    ∃ (m : ℕ) (σ : M ⟶ SheafOfModules.free (R := R) (Fin m))
      (π : SheafOfModules.free (R := R) (Fin m) ⟶ M),
      ∀ (V : Opens X) (s : M.val.obj (op V)),
        (π.val.app (op V)).hom ((σ.val.app (op V)).hom s) = rres R (le_top : V ≤ ⊤) ρ • s := by
  obtain ⟨m, i, p, hip⟩ := hU
  obtain ⟨ψ, hψ, hψρ⟩ := exists_cutoff hR hρ
  obtain ⟨e⟩ := nonempty_restr_free R U (Fin m)
  obtain ⟨σ, π, h⟩ := local_summand_split hc hρ hψ hψρ (i ≫ e.inv) (e.hom ≫ p) (by
    rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp, hip])
  exact ⟨m, σ, π, h⟩

/-- **S4.b.** For `R` fine and commutative on compact `X`, a module that is locally a direct
summand of a finite free module is globally one. Proof: finite cover by opens `Uᵢ` with
`M|Uᵢ` a summand of `R|Uᵢ^{mᵢ}`; a partition of unity `ρᵢ` and `ψᵢ` with `ψᵢρᵢ = ρᵢ`,
`supp ψᵢ ⊆ Uᵢ`; the global sections `ψᵢ eᵢⱼ` (generators `eᵢⱼ` of `M|Uᵢ`) and the coordinate
maps multiplied by `ρᵢ` (S1.a) give `M → R^m → M` with composite `∑ ρᵢ ψᵢ = 1`.
[A, Lemma 7.2.15, Cor 7.2.13] ⚠ needs `R` commutative. -/
theorem isFinFreeSummand_of_locally [CompactSpace X] {R : RingSheaf X} (hR : IsFine R)
    (hc : IsComm R) {M : Mod R} (hM : IsLocallyFinFreeSummand M) : IsFinFreeSummand M := by
  choose U hxU hU using hM
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  have hcov : (⨆ j : t, U j) = ⊤ := by
    refine top_unique (fun x _ => ?_)
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  obtain ⟨ρ, hρ1, hρS⟩ := hR t (fun j => U j) hcov
  have key := fun j : t => exists_local_split hR hc (hU j) (hρS j)
  choose m σ π hσπ using key
  refine isFinFreeSummand_of_family m σ π ?_
  apply hom_eq_of_app
  intro V s
  rw [app_sum]
  have : ∀ j : t, ((σ j ≫ π j).val.app (op V)).hom s = rres R (le_top : V ≤ ⊤) (ρ j) • s :=
    fun j => hσπ j V s
  simp only [this, ← Finset.sum_smul, ← map_sum, hρ1, map_one, one_smul]
  rfl

end Cohesive
end
