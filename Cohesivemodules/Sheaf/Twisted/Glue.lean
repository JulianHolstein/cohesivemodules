import Cohesivemodules.Sheaf.Twisted.GlueSec
import Cohesivemodules.Sheaf.Twisted.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

set_option linter.style.header false

/-!
# Z3.k: gluing twisted sheaves with trivial cocycle (S12)

Blueprint item Z3.k (`blueprint/blueprint-tw.md` §3 C.7 (b); prototype P21). For a twisted sheaf
`M : TwMod R U 1` (trivial cocycle), the glued sheaf of `R`-modules on `X`:
`glue M (W) = {(s_α) ∈ ∏_α M_α(W ⊓ U_α) : φ_αβ(s_α|W') = s_β|W'}`, an `R(W)`-module through
`R(W) → R(W ⊓ U_α)`, restriction componentwise. Sections of `glue M` (and of its restriction to
`U_γ`) over `W` are the compatible families definitionally.

## Deviations
* The compatibility condition is imposed on every `W' ≤ W ⊓ U_α ⊓ U_β` (not only on the
  intersection itself); equivalent by `φ_res`, and no intersections are rewritten.
* No cover hypothesis: `glue M` is defined for any family of opens; `glue (ofSheaf N) ≅ N` needs
  `⨆ U_α = ⊤` (`GlueEquiv.lean`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X}

/-- Z3.k: the restriction `R(W) → R(W ⊓ U_α)`, with target spelled as the ring of sections over
`W ⊓ U_α ≤ U_α` of the over-site. -/
abbrev glueRing (W : Opens X) (α : ι) :
    R.obj.obj (op W) →+* ((ringOf R).over (U α)).obj.obj (ovr (inf_le_right : W ⊓ U α ≤ U α)) :=
  (R.obj.map (homOfLE (inf_le_left : W ⊓ U α ≤ W)).op).hom

/-- Z3.k: sections of `M_α` over `W ⊓ U_α`, as an `R(W)`-module (restriction of scalars along
`glueRing`; `r • x = r|(W ⊓ U_α) • x` definitionally). -/
abbrev glueFac (M : TwMod R U (fun _ _ _ => 1)) (W : Opens X) (α : ι) :
    ModuleCat (R.obj.obj (op W)) :=
  (ModuleCat.restrictScalars (glueRing (U := U) W α)).obj (sec R (M.M α) inf_le_right)

/-- Z3.k: restricting `r|(W ⊓ U_α)` to `W' ≤ W ⊓ U_α` gives `r|W'`. -/
private theorem glueRing_res {W W' : Opens X} {α : ι} (h : W' ≤ W) (hα : W' ≤ U α)
    (r : R.obj.obj (op W)) :
    (R.obj.map (homOfLE (le_inf h hα : W' ≤ W ⊓ U α)).op).hom (glueRing (U := U) W α r) =
      (R.obj.map (homOfLE h).op).hom r := by
  change (R.obj.map (homOfLE (le_inf h hα : W' ≤ W ⊓ U α)).op).hom
    ((R.obj.map (homOfLE (inf_le_left : W ⊓ U α ≤ W)).op).hom r) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Z3.k: `glueRing` is natural in `W`. -/
private theorem glueRing_nat {W W' : Opens X} (h : W' ≤ W) (α : ι) (r : R.obj.obj (op W)) :
    (R.obj.map (homOfLE (inf_le_inf_right (U α) h : W' ⊓ U α ≤ W ⊓ U α)).op).hom
      (glueRing (U := U) W α r) = glueRing (U := U) W' α ((R.obj.map (homOfLE h).op).hom r) := by
  change (R.obj.map (homOfLE (inf_le_inf_right (U α) h : W' ⊓ U α ≤ W ⊓ U α)).op).hom
    ((R.obj.map (homOfLE (inf_le_left : W ⊓ U α ≤ W)).op).hom r) =
    (R.obj.map (homOfLE (inf_le_left : W' ⊓ U α ≤ W')).op).hom
      ((R.obj.map (homOfLE h).op).hom r)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- **Z3.k (b).** [Stacks 00AK], [A, Rem 7.2.4]. Compatible families: `(s_α) ∈ ∏_α M_α(W ⊓ U_α)`
with `φ_αβ(s_α|W') = s_β|W'` for every `W' ≤ W` contained in `U_α` and `U_β`. -/
def glueSub (M : TwMod R U (fun _ _ _ => 1)) (W : Opens X) :
    Submodule (R.obj.obj (op W)) (∀ α, glueFac M W α) where
  carrier := {s | ∀ α β {W' : Opens X} (h : W' ≤ W) (hα : W' ≤ U α) (hβ : W' ≤ U β),
    M.φ α β hα hβ (secRes R (M.M α) inf_le_right (le_inf h hα) (s α)) =
      secRes R (M.M β) inf_le_right (le_inf h hβ) (s β)}
  add_mem' := by
    intro s t hs ht α β W' h hα hβ
    have e1 : secRes R (M.M α) inf_le_right (le_inf h hα) ((s + t) α) =
        secRes R (M.M α) inf_le_right (le_inf h hα) (s α) +
          secRes R (M.M α) inf_le_right (le_inf h hα) (t α) :=
      map_add (secResHom R (M.M α) inf_le_right (le_inf h hα)) (s α) (t α)
    have e2 : secRes R (M.M β) inf_le_right (le_inf h hβ) ((s + t) β) =
        secRes R (M.M β) inf_le_right (le_inf h hβ) (s β) +
          secRes R (M.M β) inf_le_right (le_inf h hβ) (t β) :=
      map_add (secResHom R (M.M β) inf_le_right (le_inf h hβ)) (s β) (t β)
    rw [e1, e2, map_add, hs α β h hα hβ, ht α β h hα hβ]
  zero_mem' := by
    intro α β W' h hα hβ
    have e1 : secRes R (M.M α) inf_le_right (le_inf h hα) ((0 : ∀ α, glueFac M W α) α) = 0 :=
      map_zero (secResHom R (M.M α) inf_le_right (le_inf h hα))
    have e2 : secRes R (M.M β) inf_le_right (le_inf h hβ) ((0 : ∀ α, glueFac M W α) β) = 0 :=
      map_zero (secResHom R (M.M β) inf_le_right (le_inf h hβ))
    rw [e1, e2, map_zero]
  smul_mem' := by
    intro r s hs α β W' h hα hβ
    have e1 : ∀ γ (hγ : W' ≤ U γ),
        secRes R (M.M γ) inf_le_right (le_inf h hγ) ((r • s) γ) =
        toSec R (le_inf h hγ |>.trans inf_le_right) ((R.obj.map (homOfLE h).op).hom r) •
          secRes R (M.M γ) inf_le_right (le_inf h hγ) (s γ) := fun γ hγ => by
      refine (secRes_smul (M.M γ) inf_le_right (le_inf h hγ) _ (s γ)).trans ?_
      exact congrArg (fun a => toSec R (le_inf h hγ |>.trans inf_le_right) a •
        secRes R (M.M γ) inf_le_right (le_inf h hγ) (s γ)) (glueRing_res h hγ r)
    have e2 := e1 β hβ
    rw [e1 α hα, e2, M.φ_smul, hs α β h hα hβ]

theorem mem_glueSub {M : TwMod R U (fun _ _ _ => 1)} {W : Opens X} {s : ∀ α, glueFac M W α} :
    s ∈ glueSub M W ↔ ∀ α β {W' : Opens X} (h : W' ≤ W) (hα : W' ≤ U α) (hβ : W' ≤ U β),
      M.φ α β hα hβ (secRes R (M.M α) inf_le_right (le_inf h hα) (s α)) =
        secRes R (M.M β) inf_le_right (le_inf h hβ) (s β) :=
  Iff.rfl

/-- **Z3.k (b).** Restriction of compatible families from `W` to `W' ≤ W`, componentwise along
`W' ⊓ U_α ≤ W ⊓ U_α`; semilinear over `R(W) → R(W')`. -/
def glueRes (M : TwMod R U (fun _ _ _ => 1)) {W W' : Opens X} (h : W' ≤ W) :
    glueSub M W →ₛₗ[(R.obj.map (homOfLE h).op).hom] glueSub M W' where
  toFun s := ⟨fun α => secRes R (M.M α) inf_le_right (inf_le_inf_right (U α) h) (s.1 α), by
    intro α β W'' h'' hα hβ
    have e1 := secRes_secRes (M.M α) (inf_le_right : W ⊓ U α ≤ U α)
      (inf_le_inf_right (U α) h) (le_inf h'' hα) (s.1 α)
    have e2 := secRes_secRes (M.M β) (inf_le_right : W ⊓ U β ≤ U β)
      (inf_le_inf_right (U β) h) (le_inf h'' hβ) (s.1 β)
    exact (congrArg (M.φ α β hα hβ) e1).trans ((s.2 α β (h''.trans h) hα hβ).trans e2.symm)⟩
  map_add' := fun s t => Subtype.ext (funext fun α =>
    map_add (secResHom R (M.M α) inf_le_right (inf_le_inf_right (U α) h)) (s.1 α) (t.1 α))
  map_smul' := fun r s => Subtype.ext (funext fun α =>
    (secRes_smul (M.M α) inf_le_right (inf_le_inf_right (U α) h) (glueRing (U := U) W α r)
      (s.1 α)).trans
      (congrArg (fun a => toSec R _ a • secRes R (M.M α) inf_le_right
        (inf_le_inf_right (U α) h) (s.1 α)) (glueRing_nat h α r)))

theorem glueRes_apply (M : TwMod R U (fun _ _ _ => 1)) {W W' : Opens X} (h : W' ≤ W)
    (s : glueSub M W) (α : ι) :
    (glueRes M h s).1 α = secRes R (M.M α) inf_le_right (inf_le_inf_right (U α) h) (s.1 α) :=
  rfl

/-- **Z3.k (b).** The glued presheaf of `R`-modules: compatible families, componentwise
restriction. -/
def gluePre (M : TwMod R U (fun _ _ _ => 1)) : PresheafOfModules.{0} (ringOf R).obj where
  obj W := ModuleCat.of (R.obj.obj (op W.unop)) (glueSub M W.unop)
  map {W W'} f := ModuleCat.semilinearMapAddEquiv (R.obj.map f).hom
      (ModuleCat.of (R.obj.obj (op W.unop)) (glueSub M W.unop))
      (ModuleCat.of (R.obj.obj (op W'.unop)) (glueSub M W'.unop))
      (glueRes M (leOfHom f.unop))
  map_id W := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    exact Subtype.ext (funext fun α => secRes_id (M.M α) inf_le_right _ (x.1 α))
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    exact Subtype.ext (funext fun α =>
      (secRes_secRes (M.M α) inf_le_right (inf_le_inf_right (U α) (leOfHom f.unop))
        (inf_le_inf_right (U α) (leOfHom g.unop)) (x.1 α)).symm)

/-- Z3.k: a family of compatible families on `V i` that agrees on overlaps restricts to
compatible sections of `M_α` over the cover `V i ⊓ U_α` (compatibility on the overlaps). -/
private theorem glue_comp_compat (M : TwMod R U (fun _ _ _ => 1)) {κ : Type}
    (V : κ → Opens X) (s' : ∀ i, glueSub M (V i))
    (hc : ∀ i j α, secRes R (M.M α) (inf_le_right : V i ⊓ U α ≤ U α)
        (inf_le_inf_right (U α) (inf_le_left : V i ⊓ V j ≤ V i)) ((s' i).1 α) =
      secRes R (M.M α) (inf_le_right : V j ⊓ U α ≤ U α)
        (inf_le_inf_right (U α) (inf_le_right : V i ⊓ V j ≤ V j)) ((s' j).1 α))
    (α : ι) (i j : κ) :
    secRes R (M.M α) (inf_le_right : V i ⊓ U α ≤ U α)
        (inf_le_left : V i ⊓ U α ⊓ (V j ⊓ U α) ≤ V i ⊓ U α) ((s' i).1 α) =
      secRes R (M.M α) (inf_le_right : V j ⊓ U α ≤ U α)
        (inf_le_right : V i ⊓ U α ⊓ (V j ⊓ U α) ≤ V j ⊓ U α) ((s' j).1 α) := by
  have k : V i ⊓ U α ⊓ (V j ⊓ U α) ≤ (V i ⊓ V j) ⊓ U α :=
    le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_left.trans inf_le_right)
  have e1 := secRes_secRes (M.M α) (inf_le_right : V i ⊓ U α ≤ U α)
    (inf_le_inf_right (U α) (inf_le_left : V i ⊓ V j ≤ V i)) k ((s' i).1 α)
  have e2 := secRes_secRes (M.M α) (inf_le_right : V j ⊓ U α ≤ U α)
    (inf_le_inf_right (U α) (inf_le_right : V i ⊓ V j ≤ V j)) k ((s' j).1 α)
  exact e1.symm.trans ((congrArg (secRes R (M.M α) _ k) (hc i j α)).trans e2)

/-- **Z3.k (b).** The glued presheaf is a sheaf: compatible families on a cover glue
componentwise (`sec_existsUnique_gluing`), and the glued family is compatible by separatedness
(`sec_ext_of_cover`). -/
theorem isSheaf_gluePre (M : TwMod R U (fun _ _ _ => 1)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (gluePre M).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (X := TopCat.of X) (gluePre M).presheaf).2 ?_
  intro κ V sf hsf
  let s' : ∀ i, glueSub M (V i) := sf
  have hc : ∀ i j α, secRes R (M.M α) (inf_le_right : V i ⊓ U α ≤ U α)
        (inf_le_inf_right (U α) (inf_le_left : V i ⊓ V j ≤ V i)) ((s' i).1 α) =
      secRes R (M.M α) (inf_le_right : V j ⊓ U α ≤ U α)
        (inf_le_inf_right (U α) (inf_le_right : V i ⊓ V j ≤ V j)) ((s' j).1 α) :=
    fun i j α => congrFun (congrArg Subtype.val (hsf i j)) α
  have hcov : ∀ α, (⨆ i, V i) ⊓ U α ≤ ⨆ i, V i ⊓ U α := fun α => by
    rw [← iSup_inf_eq]
  have hex := fun α => sec_existsUnique_gluing (R := R)
    (inf_le_right : (⨆ i, V i) ⊓ U α ≤ U α)
    (M.M α) (fun i => V i ⊓ U α) (fun i => inf_le_inf_right (U α) (le_iSup V i)) (hcov α)
    (fun i => (s' i).1 α) (glue_comp_compat M V s' hc α)
  choose t ht hu using hex
  have hres : ∀ α (K : Opens X) (hK : K ≤ ⨆ i, V i) (hKα : K ≤ U α) i (hKi : K ≤ V i),
      secRes R (M.M α) (inf_le_right : (⨆ i, V i) ⊓ U α ≤ U α) (le_inf hK hKα) (t α) =
        secRes R (M.M α) (inf_le_right : V i ⊓ U α ≤ U α) (le_inf hKi hKα) ((s' i).1 α) :=
    fun α K hK hKα i hKi =>
      (secRes_secRes (M.M α) (inf_le_right : (⨆ i, V i) ⊓ U α ≤ U α)
        (inf_le_inf_right (U α) (le_iSup V i)) (le_inf hKi hKα) (t α)).symm.trans
        (congrArg (secRes R (M.M α) _ (le_inf hKi hKα)) (ht α i))
  have hT : (t : ∀ α, glueFac M (⨆ i, V i) α) ∈ glueSub M (⨆ i, V i) := by
    intro α β W' h hα hβ
    refine sec_ext_of_cover (R := R) hβ (M.M β) (fun i => W' ⊓ V i) (fun i => inf_le_left)
      (by rw [← inf_iSup_eq]; exact le_inf le_rfl h) _ _ fun i => ?_
    have hK : W' ⊓ V i ≤ ⨆ i, V i := inf_le_right.trans (le_iSup V i)
    have hKi : W' ⊓ V i ≤ V i := inf_le_right
    have hKα : W' ⊓ V i ≤ U α := inf_le_left.trans hα
    have hKβ : W' ⊓ V i ≤ U β := inf_le_left.trans hβ
    have e1 := M.φ_res α β hα hβ (inf_le_left : W' ⊓ V i ≤ W')
      (secRes R (M.M α) (inf_le_right : (⨆ i, V i) ⊓ U α ≤ U α) (le_inf h hα) (t α))
    have e2 := secRes_secRes (M.M α) (inf_le_right : (⨆ i, V i) ⊓ U α ≤ U α)
      (le_inf h hα) (inf_le_left : W' ⊓ V i ≤ W') (t α)
    have e3 := secRes_secRes (M.M β) (inf_le_right : (⨆ i, V i) ⊓ U β ≤ U β)
      (le_inf h hβ) (inf_le_left : W' ⊓ V i ≤ W') (t β)
    have e4 := (s' i).2 α β (hKi) hKα hKβ
    exact e1.symm.trans
      ((congrArg (M.φ α β hKα hKβ) (e2.trans (hres α _ hK hKα i hKi))).trans
        (e4.trans ((hres β _ hK hKβ i hKi).symm.trans e3.symm)))
  refine ⟨⟨t, hT⟩, fun i => ?_, fun s'' hs'' => ?_⟩
  · exact Subtype.ext (funext fun α => ht α i)
  · exact Subtype.ext (funext fun α =>
      hu α (s''.1 α) fun i => congrFun (congrArg Subtype.val (hs'' i)) α)

/-- **Z3.k (b).** [A, Rem 7.2.4], [Căldăraru, §1.2]. The sheaf of `R`-modules on `X` glued from a
twisted sheaf with trivial cocycle. -/
def glueObj (M : TwMod R U (fun _ _ _ => 1)) : Mod (ringOf R) := ⟨gluePre M, isSheaf_gluePre M⟩

/-- Z3.k: sections of the glued sheaf over `W` are the compatible families (rfl). -/
theorem glueObj_obj (M : TwMod R U (fun _ _ _ => 1)) (W : Opens X) :
    (glueObj M).val.obj (op W) = ModuleCat.of (R.obj.obj (op W)) (glueSub M W) :=
  rfl

/-- Z3.k: restriction in the glued sheaf is `glueRes` (rfl). -/
theorem glueObj_map_apply (M : TwMod R U (fun _ _ _ => 1)) {W W' : Opens X} (h : W' ≤ W)
    (s : glueSub M W) :
    ((glueObj M).val.map (homOfLE h).op).hom s = glueRes M h s :=
  rfl

/-- **Z3.k (b).** A morphism of twisted sheaves acts on compatible families componentwise. -/
def glueMapL {M N : TwMod R U (fun _ _ _ => 1)} (f : M ⟶ N) (W : Opens X) :
    glueSub M W →ₗ[R.obj.obj (op W)] glueSub N W where
  toFun s := ⟨fun α => ((f.f α).val.app (ovr inf_le_right)).hom (s.1 α), by
    intro α β W' h hα hβ
    have e1 := app_secRes (f.f α) (inf_le_right : W ⊓ U α ≤ U α) (le_inf h hα) (s.1 α)
    have e2 := app_secRes (f.f β) (inf_le_right : W ⊓ U β ≤ U β) (le_inf h hβ) (s.1 β)
    have e3 := f.comm α β hα hβ (secRes R (M.M α) inf_le_right (le_inf h hα) (s.1 α))
    have e4 := congrArg (((f.f β).val.app (ovr hβ)).hom) (s.2 α β h hα hβ)
    exact (congrArg (N.φ α β hα hβ) e1).symm.trans (e3.trans (e4.trans e2))⟩
  map_add' := fun s t => Subtype.ext (funext fun α =>
    (((f.f α).val.app (ovr inf_le_right)).hom.map_add (s.1 α) (t.1 α)))
  map_smul' := fun r s => Subtype.ext (funext fun α =>
    app_smul (f.f α) (inf_le_right : W ⊓ U α ≤ U α) (glueRing (U := U) W α r) (s.1 α))

theorem glueMapL_apply {M N : TwMod R U (fun _ _ _ => 1)} (f : M ⟶ N) (W : Opens X)
    (s : glueSub M W) (α : ι) :
    (glueMapL f W s).1 α = ((f.f α).val.app (ovr inf_le_right)).hom (s.1 α) :=
  rfl

/-- **Z3.k (b).** The morphism of glued sheaves induced by a morphism of twisted sheaves. -/
def glueMap {M N : TwMod R U (fun _ _ _ => 1)} (f : M ⟶ N) : glueObj M ⟶ glueObj N :=
  ⟨{ app := fun W => ModuleCat.ofHom (glueMapL f W.unop)
     naturality := by
       intro W W' g
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun s => ?_
       exact Subtype.ext (funext fun α =>
         app_secRes (f.f α) (inf_le_right : W.unop ⊓ U α ≤ U α)
           (inf_le_inf_right (U α) (leOfHom g.unop)) (s.1 α)) }⟩

theorem glueMap_app {M N : TwMod R U (fun _ _ _ => 1)} (f : M ⟶ N) (W : Opens X)
    (s : glueSub M W) : ((glueMap f).val.app (op W)).hom s = glueMapL f W s :=
  rfl

variable (R U) in
/-- **Z3.k (b).** Gluing as a functor `TwMod R U 1 ⥤ Mod R`. -/
def glue : TwMod R U (fun _ _ _ => 1) ⥤ Mod (ringOf R) where
  obj := glueObj
  map := glueMap
  map_id M := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.Hom.ext
    funext W
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun s => ?_
    exact Subtype.ext (funext fun α => rfl)
  map_comp f g := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.Hom.ext
    funext W
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun s => ?_
    exact Subtype.ext (funext fun α => rfl)

end Cohesive
