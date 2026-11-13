import Cohesivemodules.Sheaf.Globalize.Cone

set_option linter.style.header false

/-!
# S10 (part 2): local images, local lifting through free modules, local summands

Blueprint item S10 (§3), sub-lemmas S10.c and S10.d on a site. Split from
`Sheaf/Globalize.lean` for size only (CLAUDE.md: "New work goes in small new files"); no
mathematical change.

Local images of morphisms of sheaves of modules, maps out of finite free modules on over-sites,
local lifting along epimorphisms, the predicate `FS` (locally a summand of a finite free module),
local splitting and the finite generation of the top homology of a strictly perfect complex.

Part 1 of 2 of the original `Sheaf/Globalize/LocalFree.lean`, split for size; continued in
`Sheaf/Globalize/LocalFree.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

section Site

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
lemma imSieve_mem_of_epi {M N : Mod R} (f : M ⟶ N) [Epi f] {U : C}
    (s : N.val.obj (op U)) : imSieve f s ∈ J U := by
  have hepi : Epi (localImage f).ι := epi_of_epi_fac (toLocalImage_ι f)
  have hiso : IsIso (localImage f).ι := isIso_of_mono_of_epi _
  have h : ((inv (localImage f).ι ≫ (localImage f).ι).val.app (op U)) s = s := by
    rw [IsIso.inv_hom_id]
    rfl
  have h' : ((inv (localImage f).ι).val.app (op U) s).1 = s := h
  exact h' ▸ ((inv (localImage f).ι).val.app (op U) s).2


/-- Restriction of a free module is free, on the over-site. -/
def frIso (Y : C) (m : ℕ) :
    (SheafOfModules.free (R := R) (Fin m)).over Y ≅ SheafOfModules.free (R := R.over Y) (Fin m) :=
  (SheafOfModules.mapFreeIso (SheafOfModules.overFunctor.{0} R Y) (Fin m) (Iso.refl _)).symm

/-- basis element of the free module, as a section over Z (of C) -/
def basisElt (m : ℕ) (j : Fin m) (Z : C) :
    (SheafOfModules.free (R := R) (Fin m)).val.obj (op Z) :=
  (SheafOfModules.ιFree (R := R) j).val.app (op Z) (1 : R.obj.obj (op Z))

/-- `frIso` sends the basis section of the free module on `Over Y` to `e_j`. -/
private lemma frIso_inv_basis (Y : C) (m : ℕ) (j : Fin m) (Z : (Over Y)ᵒᵖ) :
    (frIso (R := R) Y m).inv.val.app Z
      ((SheafOfModules.ιFree (R := R.over Y) j).val.app Z (1 : (R.over Y).obj.obj Z)) =
        basisElt m j Z.unop.left := by
  have := congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app Z)
    (SheafOfModules.ιFree_mapFreeIso_hom (SheafOfModules.overFunctor.{0} R Y) (Fin m)
      (Iso.refl _) j))) (1 : (R.over Y).obj.obj Z))
  exact this


/-- Basis elements are compatible with restriction. -/
lemma basis_map (m : ℕ) (j : Fin m) {U W : C} (g : W ⟶ U) :
    ((SheafOfModules.free (R := R) (Fin m)).val.map g.op).hom (basisElt m j U) =
      basisElt m j W := by
  have := congr(ModuleCat.Hom.hom ($((SheafOfModules.ιFree (R := R) j).val.naturality g.op))
    (1 : R.obj.obj (op U)))
  refine this.symm.trans ?_
  exact congrArg (fun x => ((SheafOfModules.ιFree (R := R) j).val.app (op W)).hom x)
    (PresheafOfModules.unit_map_one (R := R.obj) g.op)

/-- the terminal object -/
abbrev termOver (Y : C) : Over Y := Over.mk (𝟙 Y)

/-- A morphism out of a free module is determined at every `Z` by its value at `Y`. -/
lemma app_basis (Y : C) (m : ℕ) (j : Fin m) {G : Mod (R.over Y)}
    (φ : (SheafOfModules.free (R := R) (Fin m)).over Y ⟶ G) (Z : Over Y) :
    φ.val.app (op Z) (basisElt m j Z.left) =
      (G.val.map (Over.homMk Z.hom : Z ⟶ termOver Y).op).hom
        (φ.val.app (op (termOver Y)) (basisElt m j Y)) := by
  have := PresheafOfModules.naturality_apply φ.val (Over.homMk Z.hom : Z ⟶ termOver Y).op
    (basisElt m j Y)
  exact (congrArg _ (basis_map m j (Over.homMk Z.hom : Z ⟶ termOver Y).left).symm).trans this


/-- Morphisms out of a restricted free module are determined by the basis images. -/
lemma hom_ext_free (Y : C) (m : ℕ) {G : Mod (R.over Y)}
    (φ φ' : (SheafOfModules.free (R := R) (Fin m)).over Y ⟶ G)
    (h : ∀ j, φ.val.app (op (termOver Y)) (basisElt m j Y) =
      φ'.val.app (op (termOver Y)) (basisElt m j Y)) : φ = φ' := by
  rw [← cancel_epi (frIso (R := R) Y m).inv]
  refine (SheafOfModules.freeHomEquiv G).injective (funext fun j => ?_)
  refine PresheafOfModules.sections_ext _ _ fun Z => ?_
  change (φ.val.app Z) ((frIso (R := R) Y m).inv.val.app Z
      ((SheafOfModules.ιFree (R := R.over Y) j).val.app Z (1 : (R.over Y).obj.obj Z))) =
    (φ'.val.app Z) ((frIso (R := R) Y m).inv.val.app Z
      ((SheafOfModules.ιFree (R := R.over Y) j).val.app Z (1 : (R.over Y).obj.obj Z)))
  rw [frIso_inv_basis]
  exact (app_basis Y m j φ Z.unop).trans
    ((congrArg _ (h j)).trans (app_basis Y m j φ' Z.unop).symm)


/-- The section of `G` over `Over Y` determined by `t ∈ G(Y)`. -/
private def secOfElt (Y : C) {G : Mod (R.over Y)} (t : G.val.obj (op (termOver Y))) :
    G.val.sections :=
  PresheafOfModules.sectionsMk
    (fun Z => (G.val.map (Over.homMk Z.unop.hom : Z.unop ⟶ termOver Y).op).hom t)
    (fun Z Z' f => by
      have e : (Over.homMk Z.unop.hom : Z.unop ⟶ termOver Y).op ≫ f =
          (Over.homMk Z'.unop.hom : Z'.unop ⟶ termOver Y).op := by
        apply Quiver.Hom.unop_inj
        apply Over.OverMorphism.ext
        exact Over.w f.unop
      have h1 := G.val.map_comp_apply (Over.homMk Z.unop.hom : Z.unop ⟶ termOver Y).op f t
      rw [e] at h1
      exact h1.symm)

/-- Families of values at the terminal object extend to maps out of a free module. -/
private lemma exists_hom_free (Y : C) (m : ℕ) {G : Mod (R.over Y)}
    (t : Fin m → G.val.obj (op (termOver Y))) :
    ∃ φ : (SheafOfModules.free (R := R) (Fin m)).over Y ⟶ G,
      ∀ j, φ.val.app (op (termOver Y)) (basisElt m j Y) = t j := by
  refine ⟨(frIso (R := R) Y m).hom ≫ (SheafOfModules.freeHomEquiv G).symm
    (fun j => secOfElt Y (t j)), fun j => ?_⟩
  have h1 := frIso_inv_basis (R := R) Y m j (op (termOver Y))
  have h2 : (frIso (R := R) Y m).hom.val.app (op (termOver Y)) (basisElt m j Y) =
      (SheafOfModules.ιFree (R := R.over Y) j).val.app (op (termOver Y))
        (1 : (R.over Y).obj.obj (op (termOver Y))) := by
    have h3 : (frIso (R := R) Y m).hom.val.app (op (termOver Y))
        ((frIso (R := R) Y m).inv.val.app (op (termOver Y))
          ((SheafOfModules.ιFree (R := R.over Y) j).val.app (op (termOver Y))
            (1 : (R.over Y).obj.obj (op (termOver Y))))) =
        (SheafOfModules.ιFree (R := R.over Y) j).val.app (op (termOver Y))
          (1 : (R.over Y).obj.obj (op (termOver Y))) :=
      congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op (termOver Y)))
        (frIso (R := R) Y m).inv_hom_id)) _)
    exact (congrArg (fun x => (frIso (R := R) Y m).hom.val.app (op (termOver Y)) x)
      h1.symm).trans h3
  have h4 := congrArg (fun f => (f j).val (op (termOver Y)))
    ((SheafOfModules.freeHomEquiv G).apply_symm_apply (fun j => secOfElt Y (t j)))
  change (SheafOfModules.freeHomEquiv G ((SheafOfModules.freeHomEquiv G).symm
    (fun j => secOfElt Y (t j))) j).val (op (termOver Y)) =
      (secOfElt Y (t j)).val (op (termOver Y)) at h4
  change ((SheafOfModules.freeHomEquiv G).symm (fun j => secOfElt Y (t j))).val.app
    (op (termOver Y)) ((frIso (R := R) Y m).hom.val.app (op (termOver Y)) (basisElt m j Y)) = _
  rw [h2]
  refine h4.trans ?_
  change (G.val.presheaf.map (𝟙 (op (termOver Y)))) (t j) = t j
  rw [CategoryTheory.Functor.map_id]
  rfl


/-- `homRestr` is compatible with composition of morphisms. -/
lemma homRestr_mor_comp {X Y : C} (f : Y ⟶ X) {M N P : Mod R} (φ : M.over X ⟶ N.over X)
    (ψ : N.over X ⟶ P.over X) : homRestr f (φ ≫ ψ) = homRestr f φ ≫ homRestr f ψ := rfl

/-- `homRestr` is compatible with identities. -/
lemma homRestr_mor_id {X Y : C} (f : Y ⟶ X) {M : Mod R} :
    homRestr f (𝟙 (M.over X)) = 𝟙 (M.over Y) := rfl

/-- `homRestr` of a restricted morphism is the restriction. -/
lemma homRestr_over {X Y : C} (f : Y ⟶ X) {M N : Mod R} (φ : M ⟶ N) :
    homRestr f (φ.over X) = φ.over Y := rfl

/-- The free module of rank `m`. -/
abbrev Fr (R : Sheaf J RingCat.{0}) (m : ℕ) : Mod R := SheafOfModules.free (Fin m)

/-- A finite intersection of covering sieves is covering. -/
private lemma iInf_mem {Y : C} (m : ℕ) (S : Fin m → Sieve Y) (hS : ∀ j, S j ∈ J Y) :
    (Finset.univ.inf S) ∈ J Y := by
  have : ∀ s : Finset (Fin m), (s.inf S) ∈ J Y := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      rw [Finset.inf_insert]
      exact J.intersection_covering (hS a) ih
  exact this _

/-- Local lifting of a map out of a free module along an epimorphism. -/
lemma lift_free {M N : Mod R} (π : M ⟶ N) [Epi π] (Y : C) (m : ℕ)
    (φ : (Fr R m).over Y ⟶ N.over Y) :
    ∃ S ∈ J Y, ∀ ⦃V : C⦄ (h : V ⟶ Y), S h →
      ∃ q : (Fr R m).over V ⟶ M.over V, q ≫ π.over V = homRestr h φ := by
  let s : Fin m → N.val.obj (op Y) := fun j => φ.val.app (op (termOver Y)) (basisElt m j Y)
  refine ⟨Finset.univ.inf (fun j => imSieve π (s j)),
    iInf_mem m _ (fun j => imSieve_mem_of_epi π (s j)), fun V h hh => ?_⟩
  have hj : ∀ j, ∃ t : M.val.obj (op V), π.val.app (op V) t = sres N h (s j) :=
    fun j => (Finset.inf_le (f := fun j => imSieve π (s j)) (Finset.mem_univ j)) h hh
  choose t ht using hj
  obtain ⟨q, hq⟩ := exists_hom_free (R := R) V m (G := M.over V) t
  refine ⟨q, hom_ext_free V m _ _ fun j => ?_⟩
  have h1 : (q ≫ π.over V).val.app (op (termOver V)) (basisElt m j V) =
      π.val.app (op V) (t j) := by
    rw [← hq j]; rfl
  have h2 := app_basis Y m j φ ((Over.map h).obj (termOver V))
  rw [h1, ht j]
  refine Eq.trans ?_ h2.symm
  change sres N h (s j) = sres N (𝟙 V ≫ h) (s j)
  rw [Category.id_comp]

end Site
end Cohesive
end
