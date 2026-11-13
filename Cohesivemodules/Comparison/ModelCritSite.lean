import Cohesivemodules.Comparison.ModelDef
import Cohesivemodules.Algebra.TotalQuasiIso

set_option linter.style.header false

/-!
# C7.f: the quasi-isomorphism criterion for maps of `T`-complexes

Blueprint item C7.f (§4, v1.11). A `ConnHom θ₁ θ₂` between flat connections on complexes `F₁`,
`F₂` of `𝒜⁰|U`-modules is a family of closed degree-`0` maps `N₁(V) → N₂(V)` (A4) compatible with
restriction. It induces a map of complexes `TMap : T(θ₁) → T(θ₂)` and its `(0,0)`-component
`T0Map : F₁ → F₂` (A12 `comp0L`). The criterion `quasiIso_TMap`: if `T0Map` is a
quasi-isomorphism, so is `TMap`. Proof plan: form-degree filtrations of `T(θ₁)`, `T(θ₂)` (A6
`filTot` sectionwise, subsheaves by the argument of C7.a), short exact sequences
`F^{b+1} → F^b → gr^b` (degreewise split: the form-degree splitting is natural in `V`), A7 in
`Mod (R|U)`, `F^b = 0` for `b > N`; `gr^b TMap` is a retract of a finite power of `T0Map`, shifted
by `b` and restricted along `ρ` (`𝒜^b` a summand of a finite free `𝒜⁰`-module, S4.b).

`α_U(M)` is itself a `T`-complex (`ModelFil.lean`), so this is the only filtration argument.

## Deviations
* None beyond those of `ModelDef.lean`.

Part 1 of 4 of the original `Comparison/ModelCrit.lean`, split for size; continued in
`Comparison/ModelCritCoord.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable {P : PreResolvingData X} {U : Opens X}
  {F₁ F₂ : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ}

/-- C7.c: `𝕏⁰` of `N_V` is the differential of `F` on sections (`Conn.eps`). -/
theorem X0comp_N {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ}
    (θ : P.Conn U F) (V : (Over U)ᵒᵖ) (p : ℤ) (s : P.FSec U F p V) :
    (θ.N V).X0comp p s = P.fD U F p V s := by
  have h : (θ.N V).X0 (lof (P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) p s) =
      lof (P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) (p + 1) (P.fD U F p V s) := by
    show Tot.eps (P.D.𝒜 V.unop.left) (P.FSec U F · V)
      ((θ.θ V).extend (Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U F · V) 1 _)) = _
    rw [GenData.extend_tmul_one]
    exact θ.eps V p s
  show DirectSum.component (P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) (p + 1)
    ((θ.N V).X0 (lof (P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) p s)) = _
  rw [h, DirectSum.component.lof_self]

/-- **C7.f.** A map of flat connections: closed degree-`0` maps `N₁(V) → N₂(V)` compatible with
restriction. -/
structure ConnHom (θ₁ : P.Conn U F₁) (θ₂ : P.Conn U F₂) where
  /-- The map on sections over `V`. -/
  φ : ∀ V : (Over U)ᵒᵖ, (θ₁.N V).T →ₗ[ℂ] (θ₂.N V).T
  /-- Each `φ V` is closed of degree `0`. -/
  mem : ∀ V, φ V ∈ Z0 (θ₁.N V) (θ₂.N V)
  /-- `φ` commutes with restriction. -/
  natural : ∀ {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.TTot U F₁ V),
    φ W (P.tRes U F₁ f x) = P.tRes U F₂ f (φ V x)

namespace ConnHom

variable {θ₁ : P.Conn U F₁} {θ₂ : P.Conn U F₂} (Φ : ConnHom θ₁ θ₂)

/-- `φ V` is `O(V)`-linear (`Hom⁰` maps are `𝒜(V)`-linear). -/
theorem φ_smulO (V : (Over U)ᵒᵖ) (r : P.O.obj.obj (op V.unop.left)) (x : P.TTot U F₁ V) :
    Φ.φ V ((P.ρ V.unop.left r : P.D.A V.unop.left) • x) =
      (P.ρ V.unop.left r : P.D.A V.unop.left) • Φ.φ V x :=
  hom0_smul (Φ.mem V).1 _ _

/-- `TMap` on sections: `T^n(θ₁)(V) → T^n(θ₂)(V)`. -/
def TMapV (n : ℤ) (V : (Over U)ᵒᵖ) :
    P.TSec U F₁ n V →ₗ[P.O.obj.obj (op V.unop.left)] P.TSec U F₂ n V where
  toFun x := ⟨Φ.φ V x.1, by
    have := (Φ.mem V).1.1 x.2
    rwa [add_zero] at this⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' r x := Subtype.ext (Φ.φ_smulO V r x.1)

/-- `TMap` in degree `n` as a map of sheaves. -/
def TMapn [CompactSpace X] (n : ℤ) : P.TSh U F₁ n ⟶ P.TSh U F₂ n :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (Φ.TMapV n V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact Φ.natural f x.1 }⟩

/-- `TMap` commutes with the differentials (`φ V` closed). -/
theorem TMapn_comm [CompactSpace X] (n : ℤ) :
    Φ.TMapn n ≫ θ₂.TD n = θ₁.TD n ≫ Φ.TMapn (n + 1) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact closed0_X (LinearMap.mem_ker.1 (Φ.mem V).2) x.1

/-- **C7.f.** The map of complexes `T(θ₁) → T(θ₂)`. -/
def TMap [CompactSpace X] : θ₁.TC ⟶ θ₂.TC where
  f n := Φ.TMapn n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e1 : θ₂.TC.d i (i + 1) = θ₂.TD i := CochainComplex.of_d _ _ _
    have e2 : θ₁.TC.d i (i + 1) = θ₁.TD i := CochainComplex.of_d _ _ _
    rw [e1, e2]
    exact Φ.TMapn_comm i

/-- The `(0,0)`-component of `φ V` on `F₁^p(V)` (A12). -/
def T0V (p : ℤ) (V : (Over U)ᵒᵖ) :
    P.FSec U F₁ p V →ₗ[↥(P.D.𝒜 V.unop.left 0)] P.FSec U F₂ p V :=
  comp0L (Φ.mem V).1 p

/-- The `(0,0)`-component commutes with restriction. -/
theorem T0V_res (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.FSec U F₁ p V) :
    Φ.T0V p W (P.fRes U F₁ p f x) = P.fRes U F₂ p f (Φ.T0V p V x) := by
  have h1 : Tot.tmul (P.D.𝒜 W.unop.left) (P.FSec U F₁ · W) 1
      (lof ↥(P.D.𝒜 W.unop.left 0) ℤ (P.FSec U F₁ · W) p (P.fRes U F₁ p f x)) =
      P.tRes U F₁ f (Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U F₁ · V) 1
        (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F₁ · V) p x)) := by
    rw [tRes_apply, totMapAlong_tmul, DgaHom.map_one']
    simp only [DirectSum.lof_eq_of, famMap_of]
  show Tot.eps (P.D.𝒜 W.unop.left) (P.FSec U F₂ · W) (Φ.φ W (Tot.tmul (P.D.𝒜 W.unop.left)
      (P.FSec U F₁ · W) 1 (lof ↥(P.D.𝒜 W.unop.left 0) ℤ (P.FSec U F₁ · W) p
        (P.fRes U F₁ p f x)))) p =
    P.fRes U F₂ p f (Tot.eps (P.D.𝒜 V.unop.left) (P.FSec U F₂ · V) (Φ.φ V (Tot.tmul
      (P.D.𝒜 V.unop.left) (P.FSec U F₁ · V) 1
        (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F₁ · V) p x))) p)
  rw [h1, Φ.natural f]
  exact (DFunLike.congr_fun (eps_totMapAlong (P.D.res (leOfHom f.unop.left))
    (fun p => P.fRes U F₂ p f) (fun p => P.fRes_smul U F₂ f p) _) p).trans
    (famMap_apply_mdl (Q := (P.FSec U F₂ · V)) (Q' := (P.FSec U F₂ · W))
      (fun p => P.fRes U F₂ p f) _ p)

/-- The `(0,0)`-component in degree `p` as a map of sheaves of `𝒜⁰|U`-modules. -/
def T0n (p : ℤ) : F₁.X p ⟶ F₂.X p :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (Φ.T0V p V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact Φ.T0V_res p f x }⟩

/-- The `(0,0)`-component commutes with the differentials of `F₁`, `F₂` (`Conn.eps`, A12
`comp0_sq`). -/
theorem T0n_comm (p : ℤ) : Φ.T0n p ≫ F₂.d p (p + 1) = F₁.d p (p + 1) ≫ Φ.T0n (p + 1) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  have h : ((θ₂.N V).complex0.d p (p + 1)).hom (comp0L (Φ.mem V).1 p x) =
      comp0L (Φ.mem V).1 (p + 1) (((θ₁.N V).complex0.d p (p + 1)).hom x) :=
    congrArg (fun φ => φ.hom x) (comp0_sq (Φ.mem V) p)
  have h1 := ((θ₂.N V).complex0_d p (comp0L (Φ.mem V).1 p x)).symm.trans h
  have h2 : (θ₂.N V).X0comp p (comp0L (Φ.mem V).1 p x) =
      comp0L (Φ.mem V).1 (p + 1) ((θ₁.N V).X0comp p x) :=
    h1.trans (congrArg _ ((θ₁.N V).complex0_d p x))
  exact (X0comp_N θ₂ V p _).symm.trans
    (h2.trans (congrArg _ (X0comp_N θ₁ V p x)))

/-- **C7.f.** The `(0,0)`-component `F₁ → F₂` of `TMap`, a map of complexes of `𝒜⁰|U`-modules. -/
def T0Map : F₁ ⟶ F₂ where
  f p := Φ.T0n p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact Φ.T0n_comm i

section GenericSite

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {S : Sheaf J RingCat.{0}}

/-- The sieve on `U` of arrows over which `s` restricts into the image of `f`. -/
private def imSieveG {M N : Mod S} (f : M ⟶ N) {U : C}
    (s : N.val.obj (op U)) : Sieve U where
  arrows V g := ∃ t : M.val.obj (op V), f.val.app (op V) t = (N.val.map g.op).hom s
  downward_closed := by
    rintro V W g ⟨t, ht⟩ h
    refine ⟨(M.val.map h.op).hom t, ?_⟩
    have h1 := PresheafOfModules.naturality_apply f.val h.op t
    have h2 := N.val.map_comp_apply g.op h.op s
    change f.val.app (op W) (M.val.map h.op t) = N.val.map (h ≫ g).op s
    rw [h1, ht]
    exact h2.symm

/-- The sieve of `s|g` is the pullback of the sieve of `s`. -/
private lemma imSieveG_map {M N : Mod S} (f : M ⟶ N) {U W : C}
    (s : N.val.obj (op U)) (h : W ⟶ U) :
    imSieveG f (U := W) ((N.val.map h.op).hom s) = (imSieveG f s).pullback h := by
  ext V g
  simp only [imSieveG, Sieve.pullback_apply]
  change (∃ t, _ = N.val.map g.op (N.val.map h.op s)) ↔
    ∃ t, _ = N.val.map (g ≫ h).op s
  rw [← N.val.map_comp_apply]
  rfl

/-- The submodule of sections of `N` that are locally in the image of `f`. -/
private def localImageG {M N : Mod S} (f : M ⟶ N) : N.Submodule where
  obj U :=
    { carrier := {s | imSieveG f s ∈ J U.unop}
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
        refine ⟨(S.obj.map g.op).hom r • t, ?_⟩
        have h1 : f.val.app (op V) ((S.obj.map g.op).hom r • t) =
            (S.obj.map g.op).hom r • f.val.app (op V) t :=
          map_smul (f.val.app (op V)).hom _ _
        have h2 := N.val.map_smul g.op r s
        rw [h1, ht]
        exact h2.symm }
  map := by
    intro Xo Yo g s hs
    have h1 := J.pullback_stable g.unop hs
    have h2 := imSieveG_map f s g.unop
    show imSieveG f (U := Yo.unop) ((N.val.map g.unop.op).hom s) ∈ J Yo.unop
    rw [h2]
    exact h1
  isSheaf := by
    intro Xo s hs
    refine J.transitive hs _ (fun V g hg => ?_)
    have h2 := imSieveG_map f s g
    exact h2 ▸ hg

/-- `f` factors through the inclusion of its local image. -/
private def toLocalImageG {M N : Mod S} (f : M ⟶ N) :
    M ⟶ (localImageG f).toSheafOfModules :=
  ⟨{ app := fun U => ModuleCat.ofHom ((f.val.app U).hom.codRestrict ((localImageG f).obj U) (by
        intro t
        refine J.superset_covering ?_ (J.top_mem _)
        intro V g _
        refine ⟨(M.val.map g.op).hom t, ?_⟩
        exact PresheafOfModules.naturality_apply f.val g.op t))
     naturality := by
        intro U V g
        ext t
        exact Subtype.ext (PresheafOfModules.naturality_apply f.val g t) }⟩

private lemma toLocalImageG_ι {M N : Mod S} (f : M ⟶ N) :
    toLocalImageG f ≫ (localImageG f).ι = f := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext t
  rfl

/-- An epimorphism of sheaves of modules is locally surjective (any site). -/
private theorem isLocallySurjective_of_epi {M N : Mod S} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf S.obj).map f.val) := by
  have hepi : Epi (localImageG f).ι := epi_of_epi_fac (toLocalImageG_ι f)
  have hiso : IsIso (localImageG f).ι := isIso_of_mono_of_epi _
  refine ⟨fun {U} s => ?_⟩
  have hmem : s ∈ (localImageG f).obj (op U) := by
    have h : ((inv (localImageG f).ι ≫ (localImageG f).ι).val.app (op U)) s = s := by
      rw [IsIso.inv_hom_id]
      rfl
    have h' : ((inv (localImageG f).ι).val.app (op U) s).1 = s := h
    exact h' ▸ ((inv (localImageG f).ι).val.app (op U) s).2
  exact hmem

/-- Sections of a sheaf of modules vanishing on a covering sieve vanish. -/
private theorem eq_zero_of_local {M : Mod S} {Xo : Cᵒᵖ} (y : M.val.obj Xo)
    (T : Sieve Xo.unop) (hT : T ∈ J Xo.unop)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ Xo.unop), T g → (M.val.map g.op).hom y = 0) : y = 0 := by
  refine M.isSheaf.isSeparated Xo.unop T hT y 0 ?_
  intro Y g hg
  exact (h g hg).trans (map_zero (M.val.map g.op).hom).symm

/-- The submodule of sections killed by a family of endomorphisms (membership is local). -/
def kerSub {M : Mod S} {ι : Type} (fs : ι → (M ⟶ M)) : M.Submodule where
  obj V := ⨅ i, LinearMap.ker ((fs i).val.app V).hom
  map := by
    intro Xo Yo g x hx
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hx
    simp only [Submodule.mem_comap, Submodule.mem_iInf, LinearMap.mem_ker]
    intro i
    have h1 := PresheafOfModules.naturality_apply (fs i).val g x
    refine h1.trans ?_
    have h2 := hx i
    change (fs i).val.app Xo x = 0 at h2
    erw [h2]
    exact map_zero _
  isSheaf := by
    intro Xo s hs
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro i
    refine eq_zero_of_local (M := M) ((fs i).val.app Xo s) _ hs fun Y g hg => ?_
    have h1 := PresheafOfModules.naturality_apply (fs i).val g.op s
    let y : M.val.obj (op Y) := (M.val.map g.op).hom s
    have hy : y ∈ ⨅ i, LinearMap.ker ((fs i).val.app (op Y)).hom := hg
    have h2 : ((fs i).val.app (op Y)).hom y = 0 :=
      LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 hy i)
    refine h1.symm.trans ?_
    exact h2

/-- Membership in `kerSub`. -/
theorem mem_kerSub {M : Mod S} {ι : Type} (fs : ι → (M ⟶ M)) (V : Cᵒᵖ)
    (x : M.val.obj V) : x ∈ (kerSub fs).obj V ↔ ∀ i, (fs i).val.app V x = 0 := by
  simp only [kerSub, Submodule.mem_iInf, LinearMap.mem_ker]

/-- A morphism into `M` with sections in a sheaf submodule `N` lifts to `N`. -/
def subLift {M : Mod S} (N : M.Submodule) {A : Mod S} (f : A ⟶ M)
    (h : ∀ V (a : A.val.obj V), f.val.app V a ∈ N.obj V) : A ⟶ N.toSheafOfModules :=
  ⟨{ app := fun V => ModuleCat.ofHom ((f.val.app V).hom.codRestrict (N.obj V) (h V))
     naturality := by
       intro U V g
       ext t
       exact Subtype.ext (PresheafOfModules.naturality_apply f.val g t) }⟩

lemma subLift_ι {M : Mod S} (N : M.Submodule) {A : Mod S} (f : A ⟶ M)
    (h : ∀ V (a : A.val.obj V), f.val.app V a ∈ N.obj V) : subLift N f h ≫ N.ι = f := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext t
  rfl

/-- `ℤˣ`-scalars on morphisms of sheaves of modules act on sections. -/
theorem units_smul_app {M N : Mod S} (f : M ⟶ N) (ε : ℤˣ) (V : Cᵒᵖ)
    (x : M.val.obj V) : ((ε • f).val.app V).hom x = (ε : ℤ) • (f.val.app V).hom x := by
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · have : ((-1 : ℤˣ) • f) = -f := by simp [Units.smul_def]
    rw [this]
    show -(f.val.app V).hom x = _
    simp

/-- Finite sums of morphisms of sheaves of modules act on sections. -/
theorem sum_app_apply {M N : Mod S} {ι : Type} (s : Finset ι) (f : ι → (M ⟶ N))
    (V : Cᵒᵖ) (x : M.val.obj V) :
    ((∑ j ∈ s, f j).val.app V).hom x = ∑ j ∈ s, ((f j).val.app V).hom x := by
  have hs : (∑ j ∈ s, f j).val.app V = ∑ j ∈ s, (f j).val.app V :=
    Functor.map_sum (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ V) _ _
  rw [hs, ModuleCat.hom_sum]
  erw [LinearMap.sum_apply]

/-- Restriction of scalars preserves quasi-isomorphisms of complexes of sheaves of modules. -/
theorem quasiIso_restrictScalars {R R' : Sheaf J RingCat.{0}} (α : R ⟶ R')
    {K L : CochainComplex (Mod R') ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((SheafOfModules.restrictScalars.{0} α).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  have hE : (SheafOfModules.restrictScalars.{0} α).PreservesEpimorphisms := by
    refine ⟨fun {M N} f hf => ?_⟩
    have hloc := isLocallySurjective_of_epi f
    have h3 : Sheaf.IsLocallySurjective
        ((SheafOfModules.toSheaf R).map ((SheafOfModules.restrictScalars.{0} α).map f)) := hloc
    have : Epi ((SheafOfModules.toSheaf R).map
        ((SheafOfModules.restrictScalars.{0} α).map f)) := inferInstance
    exact (SheafOfModules.toSheaf R).epi_of_epi_map this
  have hL : Limits.PreservesFiniteLimits (SheafOfModules.restrictScalars.{0} α) := by
    have : Limits.PreservesFiniteLimits (SheafOfModules.restrictScalars.{0} α ⋙
        SheafOfModules.toSheaf R) :=
      inferInstanceAs (Limits.PreservesFiniteLimits (SheafOfModules.toSheaf R'))
    exact Limits.preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf R)
  have : (SheafOfModules.restrictScalars.{0} α).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  infer_instance

end GenericSite

/-- A finite biproduct of quasi-isomorphisms is a quasi-isomorphism. -/
theorem quasiIso_biproduct_map' {C : Type*} [Category C] [Abelian C]
    [Limits.HasFiniteBiproducts (CochainComplex C ℤ)] {ι : Type} [Fintype ι]
    {K L : ι → CochainComplex C ℤ} (f : ∀ i, K i ⟶ L i) [∀ i, QuasiIso (f i)] :
    QuasiIso (Limits.biproduct.map f) := by
  open Limits in
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
  have key0 : (F.mapBiproduct K).inv ≫ F.map (biproduct.map f) =
      biproduct.map (fun j => F.map (f j)) ≫ (F.mapBiproduct L).inv := by
    apply biproduct.hom_ext'
    intro j
    rw [Functor.mapBiproduct_inv, Functor.mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc,
      ← Category.assoc, biproduct.ι_map, Category.assoc, biproduct.ι_desc, ← F.map_comp,
      ← F.map_comp, biproduct.ι_map]
  have key : F.map (biproduct.map f) = (F.mapBiproduct K).hom ≫
      biproduct.map (fun j => F.map (f j)) ≫ (F.mapBiproduct L).inv :=
    (Iso.inv_comp_eq _).1 key0
  have : ∀ j, IsIso (F.map (f j)) := fun j => by
    have := (inferInstance : QuasiIso (f j)).quasiIsoAt n
    exact (quasiIsoAt_iff_isIso_homologyMap _ _).1 this
  change IsIso (F.map (biproduct.map f))
  rw [key]
  exact (F.mapBiproduct K ≪≫ biproduct.mapIso (fun j => asIso (F.map (f j))) ≪≫
    (F.mapBiproduct L).symm).isIso_hom

end ConnHom
end PreResolvingData
end Cohesive
end
