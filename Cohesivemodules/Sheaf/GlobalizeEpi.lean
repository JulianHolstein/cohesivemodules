import Cohesivemodules.Sheaf.Globalize.Approx

set_option linter.style.header false

/-!
# S10: globalization over a fine sheaf

Blueprint item S10 (§3, proof route of v1.8): for `R` fine and commutative on compact `X`,
every perfect complex receives a quasi-isomorphism from a strictly perfect complex.
[A, Lemma 7.2.16], [TT, Lemma 1.9.5].

Sub-lemmas S10.a–d hold on any site; "locally" means on the objects of a covering sieve
(`Sieve.generate … ∈ J X`), with the data on the over-sites `Over Y` (Mathlib's `M.over Y`, the
same restriction as `restr`). They are applied on the over-sites `Over U` where the local models
of a perfect complex live; `overOverEquiv` identifies the nested over-sites that arise.

* S10.a `nullHomotopic_locally`: a chain map from a strictly perfect complex to an acyclic one
  is locally null-homotopic.
* S10.b `lift_locally`: chain maps from a strictly perfect complex lift locally through a
  quasi-isomorphism, up to homotopy.
* S10.c `split_locally`, `isFinFreeSummand_locally_of_acyclic`: epimorphisms onto summands of
  finite free modules split locally; in a bounded acyclic complex whose terms are such summands
  except possibly the second-lowest, that term is locally one too.
* S10.d `homology_finGen_locally`: the top homology sheaf of a strictly perfect complex is
  locally a quotient of a finite free module.
* S10.e `exists_epi_free_of_locally` (on compact `X`, `R` fine): locally finitely generated
  modules are quotients of finite free modules.
* S10 `exists_strictlyPerfect_quasiIso`.

## Deviations
* S10 is stated for perfect complexes on compact `X` (globally bounded by S9.d), with an honest
  map `P ⟶ K` (C5 step 3 needs one) instead of "quasi-isomorphic". Needs `R` commutative (S4.b).
* ⚠ The proof differs from [A, Lemma 7.2.16], which applies [A, Lemma 7.2.10] on small opens
  `U` and so needs free `R|U`-modules to be projective; `IsFine` does not give that. Local
  lifting and local splitting (S10.a–c) with S4.b replace it (blueprint v1.8).

## Files
Split for size (CLAUDE.md: "New work goes in small new files"); this file holds the part on a
space (S10.e, S10). The earlier parts are
* `Sheaf/Globalize/Cone.lean`: homology of mapping cones;
* `Sheaf/Globalize/LocalFree.lean`: local images, lifting through free modules, `FS`;
* `Sheaf/Globalize/Locally.lean`: S10.a–d and `overOverEquiv`;
* `Sheaf/Globalize/Approx.lean`: local approximation on a site.

Part 1 of 2 of the original `Sheaf/Globalize.lean`, split for size; continued in
`Sheaf/Globalize.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

section Space

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

/-- Local preimages along an epimorphism of over-modules, on an open `V ≤ U`. -/
private lemma exists_local_preimage_over {M N : Mod R} {U : Opens X}
    (φ : M.over U ⟶ N.over U) [Epi φ]
    {V : Opens X} (hV : V ≤ U) (s : N.val.obj (op V)) {x : X} (hx : x ∈ V) :
    ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧ ∃ t : M.val.obj (op W),
      φ.val.app (op (Over.mk (homOfLE (hW.trans hV)))) t = (N.val.map (homOfLE hW).op).hom s := by
  let Z : Over U := Over.mk (homOfLE hV)
  have h := imSieve_mem_of_epi φ (U := Z) s
  rw [GrothendieckTopology.mem_over_iff] at h
  obtain ⟨W, f, hf, hxW⟩ := (Opens.mem_grothendieckTopology X).1 h x hx
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨t, ht⟩ := hf
  exact ⟨W, leOfHom f, hxW, t, ht⟩


/-- Restricting twice. -/
private lemma mres_mres' (M : Mod R) {U V W : Opens X} (h1 : V ≤ U) (h2 : W ≤ V)
    (s : M.val.obj (op U)) : mres M h2 (mres M h1 s) = mres M (h2.trans h1) s :=
  (M.val.map_comp_apply (homOfLE h1).op (homOfLE h2).op s).symm

/-- Restricting a ring section twice. -/
private lemma rres_rres' (R : RingSheaf X) {U V W : Opens X} (h1 : V ≤ U) (h2 : W ≤ V)
    (r : R.obj.obj (op U)) : rres R h2 (rres R h1 r) = rres R (h2.trans h1) r := by
  change (R.obj.map (homOfLE h2).op).hom ((R.obj.map (homOfLE h1).op).hom r) = _
  rw [← RingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

/-- A cutoff function: supported in `U`, equal to `1` on an open `W` with `V ⊔ W = ⊤`. -/
private lemma exists_cutoff (hR : IsFine R) {U V : Opens X} (hUV : U ⊔ V = ⊤) :
    ∃ (ρ : R.obj.obj (op ⊤)) (W : Opens X), SupportedIn ρ U ∧ V ⊔ W = ⊤ ∧
      rres R (le_top : W ≤ ⊤) ρ = 1 := by
  obtain ⟨ρ, hsum, hsupp⟩ := hR Bool (fun b => cond b U V) (by
    refine top_unique ?_
    rw [← hUV]
    exact sup_le (le_iSup (fun b => cond b U V) true) (le_iSup (fun b => cond b U V) false))
  obtain ⟨W, hW, hW0⟩ := hsupp false
  refine ⟨ρ true, W, hsupp true, hW, ?_⟩
  have h1 : ρ true + ρ false = 1 := by simpa [Fintype.sum_bool] using hsum
  have h2 := congrArg (rres R (le_top : W ≤ ⊤)) h1
  rw [map_add, hW0, add_zero, map_one] at h2
  exact h2

/-- The global section of `M` over every open determined by `σ ∈ M(⊤)`. -/
private def secTop (M : Mod R) (σ : M.val.obj (op ⊤)) : M.val.sections :=
  PresheafOfModules.sectionsMk (fun V => (M.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom σ)
    (fun V V' f => by
      have := M.val.map_comp_apply (homOfLE (le_top : V.unop ≤ ⊤)).op f σ
      exact this.symm)


/-- The value of `freeHomEquiv.symm σ` on a basis element. -/
private lemma freeHom_basis (M : Mod R) {N : ℕ} (σ : Fin N → M.val.sections) (k : Fin N)
    (V : Opens X) :
    ((SheafOfModules.freeHomEquiv M).symm σ).val.app (op V) (basisElt N k V) =
      (σ k).val (op V) := by
  have h := congrArg (fun f => (f k).val (op V))
    ((SheafOfModules.freeHomEquiv M).apply_symm_apply σ)
  exact h

/-- `freeMap` sends basis elements to basis elements. -/
private lemma freeMap_basis {N N' : ℕ} (f : Fin N → Fin N') (j : Fin N) (V : Opens X) :
    (SheafOfModules.freeMap (R := R) f).val.app (op V) (basisElt N j V) =
      basisElt N' (f j) V := by
  have := congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op V))
    (SheafOfModules.ιFree_freeMap (R := R) f j))) (1 : R.obj.obj (op V)))
  exact this


/-- Agreement of a global map with a restricted epimorphism near `U`. -/
private lemma psi_over_eq {M : Mod R} {U N : Opens X} (hNU : N ≤ U) (m : ℕ)
    (π' : (Fr R m).over U ⟶ M.over U) (ψ : Fr R m ⟶ M) {ρ : R.obj.obj (op ⊤)}
    (e : Fin m → M.val.obj (op U))
    (he : ∀ j, π'.val.app (op (termOver U)) (basisElt m j U) = e j)
    (hρ : rres R (hNU.trans le_top) ρ = 1)
    (hψ : ∀ j, mres M (le_top : U ≤ ⊤) (ψ.val.app (op ⊤) (basisElt m j ⊤)) =
      rres R (le_top : U ≤ ⊤) ρ • e j) :
    ψ.over N = homRestr (homOfLE hNU) π' := by
  refine hom_ext_free N m _ _ fun j => ?_
  have h1 : ψ.val.app (op N) (basisElt m j N) =
      mres M (le_top : N ≤ ⊤) (ψ.val.app (op ⊤) (basisElt m j ⊤)) := by
    have := PresheafOfModules.naturality_apply ψ.val (homOfLE (le_top : N ≤ ⊤)).op
      (basisElt m j ⊤)
    rw [basis_map] at this
    exact this
  have h2 := app_basis U m j π' ((Over.map (homOfLE hNU)).obj (termOver N))
  have hrhs : (homRestr (homOfLE hNU) π').val.app (op (termOver N)) (basisElt m j N) =
      mres M hNU (e j) := by
    refine h2.trans ?_
    rw [he j]
    change (M.val.map (𝟙 N ≫ homOfLE hNU).op).hom (e j) = _
    rw [Category.id_comp]
  refine h1.trans (Eq.trans ?_ hrhs.symm)
  have h3 := mres_mres' M (le_top : U ≤ ⊤) hNU (ψ.val.app (op ⊤) (basisElt m j ⊤))
  rw [← h3, hψ j]
  change (M.val.map (homOfLE hNU).op).hom (rres R (le_top : U ≤ ⊤) ρ • e j) = _
  rw [M.val.map_smul]
  have h4 : (R.obj.map (homOfLE hNU).op).hom (rres R (le_top : U ≤ ⊤) ρ) = 1 := by
    rw [← hρ]
    exact rres_rres' R _ _ _
  rw [h4, one_smul]


/-- Membership in a finite intersection of opens. -/
private lemma mem_finset_inf_opens {ι : Type} [Fintype ι] (V : ι → Opens X) (x : X) :
    x ∈ Finset.univ.inf V ↔ ∀ i, x ∈ V i := by
  classical
  have : ∀ s : Finset ι, x ∈ s.inf V ↔ ∀ i ∈ s, x ∈ V i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih => simp [Finset.inf_insert, ih]
  simp [this]

/-- `secTop σ` evaluates to `σ` at `⊤`. -/
private lemma secTop_top (M : Mod R) (σ : M.val.obj (op ⊤)) : (secTop M σ).val (op ⊤) = σ := by
  change (M.val.presheaf.map (homOfLE (le_refl (⊤ : Opens X))).op) σ = σ
  rw [show (homOfLE (le_refl (⊤ : Opens X))).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id]
  rfl


/-- Proof of `exists_epi_free_of_locally`. -/
private theorem epi_fill [CompactSpace X] (hR : IsFine R) {M : Mod R}
    (hM : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ (m : ℕ)
      (π : SheafOfModules.free (R := R.over U) (Fin m) ⟶ (restr R U).obj M), Epi π) :
    ∃ (m : ℕ) (π : SheafOfModules.free (R := R) (Fin m) ⟶ M), Epi π := by
  classical
  choose U hxU m π hπ using hM
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => ((U x : Opens X) : Set X))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  have hcov : (⨆ i : S, U i.1) = ⊤ := by
    refine top_unique fun x _ => ?_
    have := hS (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hxi⟩ := this
    exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ1, hρ⟩ := hR S (fun i => U i.1) hcov
  choose Vc hUV hρV using hρ
  choose ρ' W hρ'supp hVW hρ'W using fun i => exists_cutoff hR (hUV i)
  -- the epimorphisms over `U i`, with source the restriction of a global free module
  let π' : ∀ i : S, (Fr R (m i.1)).over (U i.1) ⟶ M.over (U i.1) :=
    fun i => (frIso (U i.1) (m i.1)).hom ≫ π i.1
  have hπ' : ∀ i : S, Epi (π' i) := fun i => by
    have := hπ i.1
    exact epi_comp _ _
  let e : ∀ i : S, Fin (m i.1) → M.val.obj (op (U i.1)) :=
    fun i j => (π' i).val.app (op (termOver (U i.1))) (basisElt (m i.1) j (U i.1))
  have hσ := fun (i : S) (j : Fin (m i.1)) =>
    (existsUnique_extend (M := M) (hρ'supp i) (e i j)).exists
  choose σ hσ using hσ
  let I := Σ i : S, Fin (m i.1)
  let eqv : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let φ : Fr R (Fintype.card I) ⟶ M := (SheafOfModules.freeHomEquiv M).symm
    (fun k => secTop M (σ (eqv.symm k).1 (eqv.symm k).2))
  let ψ : ∀ i : S, Fr R (m i.1) ⟶ M :=
    fun i => SheafOfModules.freeMap (R := R) (fun j => eqv ⟨i, j⟩) ≫ φ
  have hψtop : ∀ (i : S) (j : Fin (m i.1)),
      (ψ i).val.app (op ⊤) (basisElt (m i.1) j ⊤) = σ i j := by
    intro i j
    change φ.val.app (op ⊤) ((SheafOfModules.freeMap (R := R) (fun j => eqv ⟨i, j⟩)).val.app
      (op ⊤) (basisElt (m i.1) j ⊤)) = _
    rw [freeMap_basis, freeHom_basis, secTop_top]
    exact congrArg (fun x : I => σ x.1 x.2) (eqv.symm_apply_apply ⟨i, j⟩)
  have hψeq : ∀ i : S, (ψ i).over (U i.1 ⊓ W i) =
      homRestr (homOfLE (inf_le_left : U i.1 ⊓ W i ≤ U i.1)) (π' i) := by
    intro i
    refine psi_over_eq (inf_le_left : U i.1 ⊓ W i ≤ U i.1) (m i.1) (π' i) (ψ i) (e i)
      (fun j => rfl) ?_ (fun j => by rw [hψtop]; exact (hσ i j).1)
    · rw [← rres_rres' R (le_top : W i ≤ ⊤) (inf_le_right : U i.1 ⊓ W i ≤ W i), hρ'W i,
        map_one]
  refine ⟨Fintype.card I, φ, ?_⟩
  have key : ∀ (V : Opens X) (s : M.val.obj (op V)) (x : X), x ∈ V →
      ∃ (Wd : Opens X) (hW : Wd ≤ V), x ∈ Wd ∧
        ∃ t : (Fr R (Fintype.card I)).val.obj (op Wd),
          φ.val.app (op Wd) t = mres M hW s := by
    intro V s x hx
    by_cases hA : ∃ i : S, x ∈ U i.1 ⊓ W i
    · obtain ⟨i, hi⟩ := hA
      have : Epi ((ψ i).over (U i.1 ⊓ W i)) := by
        rw [hψeq i]
        have := hπ' i
        exact epi_homRestr _ _
      obtain ⟨Wd, hW, hxW, t, ht⟩ := exists_local_preimage_over
        ((ψ i).over (U i.1 ⊓ W i)) (V := V ⊓ (U i.1 ⊓ W i)) inf_le_right
        (mres M (inf_le_left : V ⊓ (U i.1 ⊓ W i) ≤ V) s) (x := x) ⟨hx, hi⟩
      refine ⟨Wd, hW.trans inf_le_left, hxW,
        (SheafOfModules.freeMap (R := R) (fun j => eqv ⟨i, j⟩)).val.app (op Wd) t, ?_⟩
      change (ψ i).val.app (op Wd) t = _
      refine ht.trans ?_
      exact mres_mres' M _ _ s
    · have hA' : ∀ i : S, x ∉ U i.1 ⊓ W i := fun i hi => hA ⟨i, hi⟩
      have hxV : ∀ i : S, x ∈ Vc i := by
        intro i
        by_cases hxW : x ∈ W i
        · by_cases hxU : x ∈ U i.1
          · exact absurd (Opens.mem_inf.2 ⟨hxU, hxW⟩) (hA' i)
          · have : x ∈ U i.1 ⊔ Vc i := by rw [hUV i]; trivial
            exact (Opens.mem_sup.1 this).resolve_left hxU
        · have : x ∈ Vc i ⊔ W i := by rw [hVW i]; trivial
          exact (Opens.mem_sup.1 this).resolve_right hxW
      have hxW' : x ∈ Finset.univ.inf Vc := (mem_finset_inf_opens Vc x).2 hxV
      have h1 : rres R (le_top : Finset.univ.inf Vc ≤ ⊤) (1 : R.obj.obj (op ⊤)) = 0 := by
        rw [← hρ1, map_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [← rres_rres' R (le_top : Vc i ≤ ⊤) (Finset.inf_le (Finset.mem_univ i) :
          Finset.univ.inf Vc ≤ Vc i), hρV i, map_zero]
      refine ⟨Finset.univ.inf Vc ⊓ V, inf_le_right, ⟨hxW', hx⟩, 0, ?_⟩
      have h2 : (1 : R.obj.obj (op (Finset.univ.inf Vc ⊓ V))) = 0 := by
        have := rres_rres' R (le_top : Finset.univ.inf Vc ≤ ⊤)
          (inf_le_left : Finset.univ.inf Vc ⊓ V ≤ Finset.univ.inf Vc) 1
        rw [h1, map_zero, map_one] at this
        exact this.symm
      rw [map_zero]
      calc (0 : M.val.obj (op (Finset.univ.inf Vc ⊓ V))) = (0 : R.obj.obj _) • _ :=
            (zero_smul _ _).symm
        _ = _ := by rw [← h2, one_smul]
  have hloc : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf R.obj).map φ.val) :=
    ⟨fun {V} s => (Opens.mem_grothendieckTopology X).2 fun x hx => by
      obtain ⟨Wd, hW, hxW, t, ht⟩ := key V s x hx
      exact ⟨Wd, homOfLE hW, ⟨t, ht⟩, hxW⟩⟩
  have h3 : Epi ((SheafOfModules.toSheaf R).map φ) := by
    have : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map φ) := hloc
    infer_instance
  exact (SheafOfModules.toSheaf R).epi_of_epi_map h3

/-- **S10.e. Global generation.** For `R` fine on compact `X`, a module that is locally a
quotient of a finite free module is globally one: finitely many local generators on a finite
cover, multiplied by a partition of unity and extended by zero (S1.a). -/
theorem exists_epi_free_of_locally [CompactSpace X] (hR : IsFine R) {M : Mod R}
    (hM : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ (m : ℕ)
      (π : SheafOfModules.free (R := R.over U) (Fin m) ⟶ (restr R U).obj M), Epi π) :
    ∃ (m : ℕ) (π : SheafOfModules.free (R := R) (Fin m) ⟶ M), Epi π := by
  exact epi_fill hR hM

end Space
end Cohesive
end
