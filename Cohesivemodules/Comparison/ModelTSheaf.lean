import Cohesivemodules.Comparison.AlphaOver
import Cohesivemodules.Comparison.Setup
import Cohesivemodules.Algebra.TotMap
import Cohesivemodules.Algebra.BaseChangeLift
import Cohesivemodules.Comparison.ModelDual

set_option linter.style.header false

/-!
# C7: the explicit model `T(K)` (definitions)

Blueprint item C7 (§4, v1.11). On the over-site of an open `U`, for a complex `F` of sheaves of
`𝒜⁰|U`-modules with a flat `𝒜`-connection (`Conn`), the complex of sheaves of `R|U`-modules
`T^n(V) = (𝒜(V) ⊗_{𝒜⁰(V)} ⨁_p F^p(V))^n` (plain tensor products of sections; A3's `Tot` over
`𝒜(V)` with generators `F^p(V)`), and the comparison map `Ξ_e : α_U(M) → T` of C7.e. For
`F = 𝒜⁰ ⊗_R K` (`Comparison/ModelBC.lean`), `T` is a model of `𝒜^• ⊗_R K` whose sections are
computable; it replaces the sheafified tensor product in C2, C4 step 3 and C5.

* `FSec`, `fRes`, `fD`: sections of `F^p`, restriction, differential.
* `Conn`: generator data `θ_V` on `F^•(V)` for every `V`, of degree `1`, flat, with
  `(0,0)`-component `d_F` (`eps`) and compatible with restriction (`natural`).
* `Conn.N θ V`: the quasi-cohesive `𝒜(V)`-module `(F^•(V), 𝕏_V)` (C7.c).
* `TPre`, `TSh` (C7.a, needs `X` compact), `TD`, `TC`: the complex `T`.
* `ΞV`, `Ξ`: the comparison map (C7.e), via `bcLift`.
* `G0`, `gr0Ξ`: the form-degree-`0` part of `α_U(M)` and of `Ξ` (C7.f).

## Deviations
* Over-site of `U` (C2 and C4 work on `U`; C5 uses `U = ⊤`).
* The connection is an abstract structure (`Conn`); the one on `𝒜⁰ ⊗_R K` is constructed in
  `ModelBC.lean` (C7.b).

Part 1 of 2 of the original `Comparison/ModelDef.lean`, split for size; continued in
`Comparison/ModelDef.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X)
  (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)

/-! ## Sections of `F` -/

/-- **C7.** Sections of `F^p` over `V` (an object of the over-site of `U`). -/
abbrev FSec (p : ℤ) (V : (Over U)ᵒᵖ) : Type := (F.X p).val.obj V

/-- Sections of `F^p` over `V` are `𝒜⁰(V)`-modules (the ring of sections of `𝒜⁰|U` is
`↥(𝒜_V 0)` by `rfl`, prototype P9). -/
instance (p : ℤ) (V : (Over U)ᵒᵖ) : Module ↥(P.D.𝒜 V.unop.left 0) (P.FSec U F p V) :=
  inferInstanceAs (Module (((ringOf P.A0).over U).obj.obj V) ((F.X p).val.obj V))

/-- **C7.** Restriction of sections of `F^p` along `f : V ⟶ W`. -/
def fRes (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) : P.FSec U F p V →+ P.FSec U F p W :=
  ((F.X p).val.map f).hom.toAddMonoidHom

/-- Restriction of sections is semilinear along `res⁰`. -/
theorem fRes_smul {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (p : ℤ) (α : ↥(P.D.𝒜 V.unop.left 0))
    (s : P.FSec U F p V) :
    P.fRes U F p f (α • s) = (P.D.res (leOfHom f.unop.left)).f0 α • P.fRes U F p f s :=
  (F.X p).val.map_smul f α s

/-- **C7.** The differential of `F` on sections over `V`. -/
def fD (p : ℤ) (V : (Over U)ᵒᵖ) : P.FSec U F p V →+ P.FSec U F (p + 1) V :=
  ((F.d p (p + 1)).val.app V).hom.toAddMonoidHom

/-! ## Flat connections -/

/-- **C7.b–c.** A flat `𝒜`-connection on the complex `F`: for every `V`, generator data `θ_V`
on the `𝒜⁰(V)`-modules `F^p(V)` (A3.a; `θ_V(f) = ∇f + 1 ⊗ d_F f`), of total degree `1`, flat
(`𝕏_V² = c`), whose form-degree-`0` part is `d_F`, and compatible with restriction. -/
structure Conn where
  /-- The generator data on sections over `V`. -/
  θ : ∀ V : (Over U)ᵒᵖ, GenData (P.D.𝒜 V.unop.left) (P.FSec U F · V)
  /-- `θ_V` has total degree `1`. -/
  mem : ∀ (V : (Over U)ᵒᵖ) (p : ℤ) (e : P.FSec U F p V),
    (θ V).θ (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) p e) ∈
      totDeg (P.D.𝒜 V.unop.left) (P.FSec U F · V) (p + 1)
  /-- Flatness on the generators: `𝕏_V(θ_V e) = c·(1 ⊗ e)`. -/
  flat : ∀ (V : (Over U)ᵒᵖ) (e : ⨁ p, P.FSec U F p V),
    (θ V).extend ((θ V).θ e) =
      GCDga.c (𝒜 := P.D.𝒜 V.unop.left) • Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U F · V) 1 e
  /-- The form-degree-`0` part of `θ_V` is the differential of `F`. -/
  eps : ∀ (V : (Over U)ᵒᵖ) (p : ℤ) (e : P.FSec U F p V),
    Tot.eps (P.D.𝒜 V.unop.left) (P.FSec U F · V)
        ((θ V).θ (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) p e)) =
      lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U F · V) (p + 1) (P.fD U F p V e)
  /-- `θ` commutes with restriction. -/
  natural : ∀ {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (e : ⨁ p, P.FSec U F p V),
    totMapAlong (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
        (fun p => P.fRes_smul U F f p) ((θ V).θ e) =
      (θ W).θ (famMap (fun p => P.fRes U F p f) e)

variable {P U F}

/-- **C7.c.** The quasi-cohesive `𝒜(V)`-module `N_V = (F^•(V), 𝕏_V)`. -/
def Conn.N (θ : P.Conn U F) (V : (Over U)ᵒᵖ) : QuasiCohesive (P.D.𝒜 V.unop.left) :=
  QuasiCohesive.ofGenerators (P.FSec U F · V) (θ.θ V) (θ.mem V) (θ.flat V)

/-- The operator of `N_V` is the Leibniz extension of `θ_V` (rfl). -/
theorem Conn.N_X (θ : P.Conn U F) (V : (Over U)ᵒᵖ) (x : (θ.N V).T) :
    (θ.N V).X x = (θ.θ V).extend x := rfl

variable (P U F)

/-! ## The sheaves `T^n` -/

/-- **C7.** The total module `𝒜(V) ⊗_{𝒜⁰(V)} ⨁_p F^p(V)`. -/
abbrev TTot (V : (Over U)ᵒᵖ) : Type := Tot (P.D.𝒜 V.unop.left) (P.FSec U F · V)

/-- **C7.** Restriction of total modules along `f : V ⟶ W`, `a ⊗ e ↦ res(a) ⊗ res(e)`. -/
def tRes {V W : (Over U)ᵒᵖ} (f : V ⟶ W) : P.TTot U F V →ₗ[ℂ] P.TTot U F W where
  toFun := totMapAlong (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
    (fun p => P.fRes_smul U F f p)
  map_add' := map_add _
  map_smul' r x := totMapAlong_smul_k _ _ _ r x

/-- `tRes` on the underlying additive map (rfl). -/
theorem tRes_apply {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.TTot U F V) :
    P.tRes U F f x = totMapAlong (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
      (fun p => P.fRes_smul U F f p) x := rfl

/-- `tRes` along the identity is the identity. -/
theorem tRes_id (V : (Over U)ᵒᵖ) (x : P.TTot U F V) : P.tRes U F (𝟙 V) x = x := by
  refine totMapAlong_id (P.D.res (leOfHom (𝟙 V).unop.left)) (fun a => P.D.res_id _ a)
    (fun p => P.fRes U F p (𝟙 V)) (fun p y => ?_) (fun p => P.fRes_smul U F (𝟙 V) p) x
  have h := (F.X p).val.map_id V
  exact congrArg (fun φ => φ.hom y) h

/-- `tRes` is functorial. -/
theorem tRes_comp {V W Y : (Over U)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Y) (x : P.TTot U F V) :
    P.tRes U F (f ≫ g) x = P.tRes U F g (P.tRes U F f x) := by
  symm
  refine totMapAlong_comp (P.D.res (leOfHom g.unop.left)) (P.D.res (leOfHom f.unop.left))
    (P.D.res (leOfHom (f ≫ g).unop.left)) (fun a => P.D.res_comp _ _ a) _ _
    (fun p => P.fRes U F p (f ≫ g)) (fun p y => ?_)
    (fun p => P.fRes_smul U F f p) (fun p => P.fRes_smul U F g p)
    (fun p => P.fRes_smul U F (f ≫ g) p) x
  have h := (F.X p).val.map_comp f g
  exact congrArg (fun φ => φ.hom y) h.symm

/-- `tRes` is semilinear along `res`. -/
theorem tRes_smul {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (a : P.D.A V.unop.left) (x : P.TTot U F V) :
    P.tRes U F f (a • x) = P.D.res (leOfHom f.unop.left) a • P.tRes U F f x :=
  totMapAlong_smul (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
    (fun p => P.fRes_smul U F f p) a x

/-- The elements of total degree `n` of `TTot V`, as an `𝒜⁰(V)`-submodule. -/
def tDeg (n : ℤ) (V : (Over U)ᵒᵖ) : Submodule ↥(P.D.𝒜 V.unop.left 0) (P.TTot U F V) where
  carrier := (totDeg (P.D.𝒜 V.unop.left) (P.FSec U F · V) n : Set (P.TTot U F V))
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' a x hx := by
    have := smul_mem_totDeg (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U F · V)) a.2 hx
    rwa [zero_add] at this

/-- **C7.** `T^n(V)` as a type: the elements of total degree `n` of `TTot V`. -/
def TSec (n : ℤ) (V : (Over U)ᵒᵖ) : Type := ↥(P.tDeg U F n V)

instance (n : ℤ) (V : (Over U)ᵒᵖ) : AddCommGroup (P.TSec U F n V) :=
  inferInstanceAs (AddCommGroup ↥(P.tDeg U F n V))

/-- **C7.** `O(V)` acts on `T^n(V)` through `ρ_V : O(V) → 𝒜⁰(V)`. -/
instance (n : ℤ) (V : (Over U)ᵒᵖ) : Module (P.O.obj.obj (op V.unop.left)) (P.TSec U F n V) :=
  Module.compHom ↥(P.tDeg U F n V) (P.ρ V.unop.left)

/-- The same action, typed over the ring of sections of `R|U` (definitionally `O(V)`). -/
instance (n : ℤ) (V : (Over U)ᵒᵖ) : Module ((P.R.over U).obj.obj V) (P.TSec U F n V) :=
  inferInstanceAs (Module (P.O.obj.obj (op V.unop.left)) (P.TSec U F n V))

/-- `tRes` preserves the total degree. -/
theorem tRes_mem {n : ℤ} {V W : (Over U)ᵒᵖ} (f : V ⟶ W) {x : P.TTot U F V}
    (hx : x ∈ totDeg (P.D.𝒜 V.unop.left) (P.FSec U F · V) n) :
    P.tRes U F f x ∈ totDeg (P.D.𝒜 W.unop.left) (P.FSec U F · W) n :=
  totMapAlong_mem_totDeg (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
    (fun p => P.fRes_smul U F f p) hx

/-- `tRes` on degree-`0` scalars from `O`: `res(ρ_V r) = ρ_W(res r)`. -/
theorem tRes_smulO {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (r : P.O.obj.obj (op V.unop.left))
    (x : P.TTot U F V) :
    P.tRes U F f ((P.ρ V.unop.left r : P.D.A V.unop.left) • x) =
      (P.ρ W.unop.left ((P.O.obj.map (homOfLE (leOfHom f.unop.left)).op).hom r) :
        P.D.A W.unop.left) • P.tRes U F f x := by
  rw [P.tRes_smul U F f]
  congr 1
  exact congrArg Subtype.val (P.ρ_natural (leOfHom f.unop.left) r)

/-- **C7.** Restriction `T^n(V) → T^n(W)`, semilinear along `O(V) → O(W)`. -/
def TRes (n : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    P.TSec U F n V →ₛₗ[(P.O.obj.map (homOfLE (leOfHom f.unop.left)).op).hom]
      P.TSec U F n W where
  toFun x := ⟨P.tRes U F f x.1, P.tRes_mem U F f x.2⟩
  map_add' x y := Subtype.ext (map_add (P.tRes U F f) x.1 y.1)
  map_smul' r x := Subtype.ext (P.tRes_smulO U F f r x.1)

/-- **C7.** `T^n` as a presheaf of `R|U`-modules on the over-site of `U`. -/
def TPre (n : ℤ) : PresheafOfModules.{0} (P.R.over U).obj where
  obj V := ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.TSec U F n V)
  map {V W} f := ModuleCat.semilinearMapAddEquiv ((P.R.over U).obj.map f).hom
      (ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.TSec U F n V))
      (ModuleCat.of (P.O.obj.obj (op W.unop.left)) (P.TSec U F n W))
      (P.TRes U F n f)
  map_id V := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact P.tRes_id U F V x.1
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact P.tRes_comp U F f g x.1

/-- The product presheaf of types of a family of presheaves of types. -/
private def piFun {C : Type} [Category.{0} C] {ι : Type} (G : ι → Cᵒᵖ ⥤ Type) : Cᵒᵖ ⥤ Type where
  obj V := ∀ i, (G i).obj V
  map f := ↾(fun z i => (G i).map f (z i))
  map_id V := by
    ext z i
    show (G i).map (𝟙 V) (z i) = z i
    rw [(G i).map_id]
    rfl
  map_comp f g := by
    ext z i
    show (G i).map (f ≫ g) (z i) = (G i).map g ((G i).map f (z i))
    rw [(G i).map_comp]
    rfl

/-- A product of presheaves of types satisfying unique gluing for `S` does too. -/
private theorem isSheafFor_pi_mdl {C : Type} [Category.{0} C] {ι : Type}
    (G : ι → Cᵒᵖ ⥤ Type) {Y : C} (S : Presieve Y) (hG : ∀ i, Presieve.IsSheafFor (G i) S) :
    Presieve.IsSheafFor (piFun G) S := by
  intro x hx
  let xi : ∀ i, Presieve.FamilyOfElements (G i) S := fun i Z f hf => x f hf i
  have hxi : ∀ i, (xi i).Compatible := by
    intro i Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ hgf
    exact congrFun (hx g₁ g₂ h₁ h₂ hgf) i
  have hex := fun i => hG i (xi i) (hxi i)
  choose t ht using fun i => (hex i).exists
  refine ⟨t, fun Z f hf => funext fun i => ht i f hf, fun y hy => funext fun i => ?_⟩
  exact (hex i).unique (fun Z f hf => congrFun (hy f hf) i) (ht i)

/-- The type-valued presheaf `V ↦ T^n(V)` on the over-site of `U`. -/
private def TTy (n : ℤ) : (Over U)ᵒᵖ ⥤ Type where
  obj V := P.TSec U F n V
  map {V W} f := ↾(fun x => P.TRes U F n f x)
  map_id V := by
    ext x
    exact Subtype.ext (P.tRes_id U F V x.1)
  map_comp f g := by
    ext x
    exact Subtype.ext (P.tRes_comp U F f g x.1)

/-- The type-valued presheaf `V ↦ F^p(V)` on the over-site of `U`. -/
private def FTy (p : ℤ) : (Over U)ᵒᵖ ⥤ Type :=
  (F.X p).val.presheaf ⋙ forget AddCommGrpCat

/-- Naturality of the coordinates `iTot` for `tRes`. -/
theorem iTot_nat {N0 : ℕ} {m : ℕ → ℕ} (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m)
    (hc : ∀ (V W : Opens X) (h : W ≤ V) (q : ℕ) j (a : ↥(GCDga.piece (P.D.𝒜 V) q))
      (b : ↥(GCDga.piece (P.D.𝒜 W) q)), (b : P.D.A W) = P.D.res h a →
      (D W).c q j b = (P.D.res h).f0 ((D V).c q j a))
    (n : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.TTot U F V) (qj : DIdx N0 m) :
    (D W.unop.left).iTot n (P.tRes U F f x) qj =
      P.fRes U F (n - DIdx.deg qj) f ((D V.unop.left).iTot n x qj) :=
  Dfm.iTot_map (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
    (fun p => P.fRes_smul U F f p) (D V.unop.left) (D W.unop.left)
    (hc _ _ _) n x qj

/-- Naturality of the reconstruction `rTot` for `tRes`. -/
private theorem rTot_nat {N0 : ℕ} {m : ℕ → ℕ} (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m)
    (hs : ∀ (V W : Opens X) (h : W ≤ V) q j,
      P.D.res h ((D V).s q j : P.D.A V) = ((D W).s q j : P.D.A W))
    (n : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (z : ∀ qj : DIdx N0 m, P.FSec U F (n - DIdx.deg qj) V) :
    P.tRes U F f ((D V.unop.left).rTot n z) =
      (D W.unop.left).rTot n (fun qj => P.fRes U F (n - DIdx.deg qj) f (z qj)) :=
  Dfm.map_rTot (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
    (fun p => P.fRes_smul U F f p) (D V.unop.left) (D W.unop.left) (hs _ _ _) n z

/-- The coordinates as a natural transformation `T^n ⟶ ∏ F^{n-q}`. -/
private def iNat {N0 : ℕ} {m : ℕ → ℕ} (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m)
    (hc : ∀ (V W : Opens X) (h : W ≤ V) (q : ℕ) j (a : ↥(GCDga.piece (P.D.𝒜 V) q))
      (b : ↥(GCDga.piece (P.D.𝒜 W) q)), (b : P.D.A W) = P.D.res h a →
      (D W).c q j b = (P.D.res h).f0 ((D V).c q j a)) (n : ℤ) :
    TTy P U F n ⟶ piFun (fun qj : DIdx N0 m => FTy P U F (n - DIdx.deg qj)) where
  app V := ↾(fun x qj => (D V.unop.left).iTot n x.1 qj)
  naturality V W f := by
    ext x
    funext qj
    exact iTot_nat P U F D hc n f x.1 qj

/-- The reconstruction as a natural transformation `∏ F^{n-q} ⟶ T^n`. -/
private def rNat {N0 : ℕ} {m : ℕ → ℕ} (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m)
    (hs : ∀ (V W : Opens X) (h : W ≤ V) q j,
      P.D.res h ((D V).s q j : P.D.A V) = ((D W).s q j : P.D.A W)) (n : ℤ) :
    piFun (fun qj : DIdx N0 m => FTy P U F (n - DIdx.deg qj)) ⟶ TTy P U F n where
  app V := ↾(fun (z : ∀ qj : DIdx N0 m, P.FSec U F (n - DIdx.deg qj) V) =>
    (⟨Dfm.rTot (Q := (P.FSec U F · V)) (D V.unop.left) n z,
      Dfm.rTot_mem (Q := (P.FSec U F · V)) (D V.unop.left) n z⟩ : P.TSec U F n V))
  naturality V W f := by
    ext z
    exact Subtype.ext (rTot_nat P U F D hs n f z).symm

/-- **C7.a.** `T^n` is a sheaf: each `𝒜^q|U` is a summand of a finite free `𝒜⁰|U`-module (S4.b on
the compact `X`, restricted to `U`), so `T^n` is sectionwise a retract of a finite power of
`⨁_q F^{n-q}`, compatibly with restriction. -/
theorem isSheaf_TPre [CompactSpace X] (n : ℤ) :
    Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U) (P.TPre U F n).presheaf := by
  obtain ⟨N0, m, D, hs, hc⟩ := P.exists_dfm
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat), isSheaf_iff_isSheaf_of_type]
  have hF : ∀ p, Presieve.IsSheaf ((Opens.grothendieckTopology X).over U) (FTy P U F p) :=
    fun p => (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).1 (F.X p).isSheaf)
  intro Y S hS
  refine isSheafFor_of_retract (iNat P U F D hc n) (rNat P U F D hs n) ?_ S
    (isSheafFor_pi_mdl _ _ (fun qj => hF _ S hS))
  ext V x
  exact Subtype.ext (Dfm.rTot_iTot (D V.unop.left) n x.2)

/-- **C7.a.** The sheaf `T^n` of `R|U`-modules. -/
def TSh [CompactSpace X] (n : ℤ) : Mod (P.R.over U) := ⟨P.TPre U F n, P.isSheaf_TPre U F n⟩

end PreResolvingData
end Cohesive
end
