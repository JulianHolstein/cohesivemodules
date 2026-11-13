import Cohesivemodules.Sheaf.Twisted.Glue
import Cohesivemodules.Sheaf.Twisted.SecHom

set_option linter.style.header false

/-!
# Z3.k: twisted sheaves with trivial cocycle are sheaves on `X` (S12)

Blueprint item Z3.k (`blueprint/blueprint-tw.md` §3 C.7 (c)–(e)). For the trivial cocycle:
* `TwMod.ofSheafFunctor : Mod R ⥤ TwMod R U 1` (components `N|U_α`, identity gluing);
* `ofSheafGlueIso M : ofSheaf (glue M) ≅ M` (any family of opens): evaluation `(s_α) ↦ s_γ`,
  inverse `t ↦ (φ_γα(t|W ⊓ U_α))_α`;
* `toGlueOfSheaf N : N ⟶ glue (ofSheaf N)`, `t ↦ (t|W ⊓ U_α)_α`, an isomorphism if the `U_α`
  cover `X`;
* `glueEquiv : TwMod R U 1 ≌ Mod R` for a cover of `X`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X}

/-! ## `ofSheaf` as a functor -/

/-- Z3.k: `ofSheaf` on morphisms: componentwise restriction. -/
def TwMod.ofSheafMap {N N' : Mod (ringOf R)} (g : N ⟶ N') :
    TwMod.ofSheaf R U N ⟶ TwMod.ofSheaf R U N' where
  f α := (restr (ringOf R) (U α)).map g
  comm := fun _ _ _ _ _ _ => rfl

theorem TwMod.ofSheafMap_f {N N' : Mod (ringOf R)} (g : N ⟶ N') (α : ι) :
    (TwMod.ofSheafMap (U := U) g).f α = (restr (ringOf R) (U α)).map g :=
  rfl

variable (R U) in
/-- **Z3.k (c).** A sheaf of `R`-modules on `X` as a twisted sheaf for the trivial cocycle, as a
functor. -/
def TwMod.ofSheafFunctor : Mod (ringOf R) ⥤ TwMod R U (fun _ _ _ => 1) where
  obj := TwMod.ofSheaf R U
  map := TwMod.ofSheafMap
  map_id N := TwMod.hom_ext fun α => (restr (ringOf R) (U α)).map_id N
  map_comp f g := TwMod.hom_ext fun α => (restr (ringOf R) (U α)).map_comp f g

/-! ## (c) `ofSheaf (glue M) ≅ M` -/

/-- Helper: restricting ring sections twice is restricting once. -/
private theorem ringRes_ringRes {W V W' : Opens X} (h : W' ≤ V) (h' : V ≤ W)
    (r : R.obj.obj (op W)) :
    (R.obj.map (homOfLE h).op).hom ((R.obj.map (homOfLE h').op).hom r) =
      (R.obj.map (homOfLE (h.trans h')).op).hom r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Helper: restricting ring sections along `W ≤ W` is the identity. -/
private theorem ringRes_self {W : Opens X} (h : W ≤ W) (r : R.obj.obj (op W)) :
    (R.obj.map (homOfLE h).op).hom r = r := by
  have e : homOfLE h = 𝟙 W := rfl
  rw [e, op_id, R.obj.map_id]
  rfl

/-- Helper: composite of a restriction and the inverse inclusion on ring sections. -/
private theorem ringRes_round {W V : Opens X} (h : W ≤ V) (h' : V ≤ W) (r : R.obj.obj (op W)) :
    (R.obj.map (homOfLE h).op).hom ((R.obj.map (homOfLE h').op).hom r) = r :=
  (ringRes_ringRes h h' r).trans (ringRes_self _ r)

/-- Helper: the gluing maps of a twisted sheaf with trivial cocycle compose (`ȟ = 1`). -/
private theorem TwMod.φ_triple (M : TwMod R U (fun _ _ _ => 1)) (γ α β : ι) {W : Opens X}
    (hγ : W ≤ U γ) (hα : W ≤ U α) (hβ : W ≤ U β) (x : sec R (M.M γ) hγ) :
    M.φ α β hα hβ (M.φ γ α hγ hα x) = M.φ γ β hγ hβ x := by
  rw [M.cocycle γ α β hγ hα hβ x]
  simp only [map_one, Units.val_one]
  exact one_smul (((ringOf R).over (U β)).obj.obj (ovr hβ)) _

/-- **Z3.k (c).** Evaluation at `γ`: on `W ≤ U_γ`, a compatible family `(s_α)` goes to
`s_γ|W` (`W ≤ W ⊓ U_γ`). -/
def glueEval (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) :
    (restr (ringOf R) (U γ)).obj (glueObj M) ⟶ M.M γ :=
  homOfSec₀
    (fun {W} hW => ({ toFun := fun s => secRes R (M.M γ) inf_le_right (le_inf le_rfl hW) (s.1 γ)
                      map_zero' := map_zero (secResHom R (M.M γ) inf_le_right (le_inf le_rfl hW))
                      map_add' := fun s s' =>
                        map_add (secResHom R (M.M γ) inf_le_right (le_inf le_rfl hW))
                          (s.1 γ) (s'.1 γ) } : glueSub M W →+ sec R (M.M γ) hW))
    (by
      intro W hW r x
      exact (secRes_smul (M.M γ) inf_le_right (le_inf le_rfl hW) (glueRing (U := U) W γ r)
        (x.1 γ)).trans (congrArg (· • _) (ringRes_round _ _ r)))
    (by
      intro W W' hW h' x
      exact (secRes_secRes (M.M γ) inf_le_right (inf_le_inf_right (U γ) h')
        (le_inf le_rfl (h'.trans hW)) (x.1 γ)).trans
        (secRes_secRes (M.M γ) inf_le_right (le_inf le_rfl hW) h' (x.1 γ)).symm)

/-- Z3.k (c): `glueEval` on sections (should hold by `rfl`). -/
theorem glueEval_app (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) {W : Opens X} (h : W ≤ U γ)
    (s : glueSub M W) :
    ((glueEval M γ).val.app (ovr h)).hom s =
      secRes R (M.M γ) inf_le_right (le_inf le_rfl h) (s.1 γ) :=
  rfl

/-- Helper: restricting `φ_γδ x` equals `φ_γδ` of the restriction. -/
private theorem secRes_φ {M : TwMod R U (fun _ _ _ => 1)} (γ δ : ι) {V V' : Opens X}
    (hγ : V ≤ U γ) (hδ : V ≤ U δ) (h' : V' ≤ V) (x : sec R (M.M γ) hγ) :
    secRes R (M.M δ) hδ h' (M.φ γ δ hγ hδ x) =
      M.φ γ δ (h'.trans hγ) (h'.trans hδ) (secRes R (M.M γ) hγ h' x) :=
  (M.φ_res γ δ hγ hδ h' x).symm

/-- **Z3.k (c).** The compatible family `(φ_γα(t|W ⊓ U_α))_α` of a section `t` of `M_γ` over
`W ≤ U_γ` (compatible by the cocycle condition with `ȟ = 1` and `φ_res`). -/
def glueCoevalSec (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) {W : Opens X} (h : W ≤ U γ)
    (t : sec R (M.M γ) h) : glueSub M W :=
  ⟨fun α => M.φ γ α ((inf_le_left : W ⊓ U α ≤ W).trans h) inf_le_right
    (secRes R (M.M γ) h inf_le_left t), by
    intro α β W' h' hα hβ
    have e1 : ∀ (δ : ι) (hδ : W' ≤ U δ),
        secRes R (M.M δ) inf_le_right (le_inf h' hδ)
          (M.φ γ δ ((inf_le_left : W ⊓ U δ ≤ W).trans h) inf_le_right
            (secRes R (M.M γ) h inf_le_left t)) =
        M.φ γ δ (h'.trans h) hδ (secRes R (M.M γ) h h' t) := fun δ hδ =>
      (secRes_φ γ δ _ _ _ _).trans (congrArg (M.φ γ δ _ _)
        (secRes_secRes (M.M γ) h inf_le_left (le_inf h' hδ) t))
    exact (congrArg (M.φ α β hα hβ) (e1 α hα)).trans
      ((M.φ_triple γ α β (h'.trans h) hα hβ _).trans (e1 β hβ).symm)⟩

/-- **Z3.k (c).** Coevaluation `M_γ ⟶ (glue M)|U_γ`, `t ↦ (φ_γα(t|W ⊓ U_α))_α`. -/
def glueCoeval (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) :
    M.M γ ⟶ (restr (ringOf R) (U γ)).obj (glueObj M) :=
  homOfSec₀
    (fun {W} hW => ({ toFun := fun t => glueCoevalSec M γ hW t
                      map_zero' := Subtype.ext (funext fun α =>
                        (congrArg (M.φ γ α _ _)
                          (map_zero (secResHom R (M.M γ) hW inf_le_left))).trans (map_zero _))
                      map_add' := fun t t' => Subtype.ext (funext fun α =>
                        (congrArg (M.φ γ α _ _)
                          (map_add (secResHom R (M.M γ) hW inf_le_left) t t')).trans
                          (map_add _ _ _))
                      } : sec R (M.M γ) hW →+ glueSub M W))
    (by
      intro W hW r x
      refine Subtype.ext (funext fun α => ?_)
      exact (congrArg (M.φ γ α _ _) (secRes_smul (M.M γ) hW inf_le_left r x)).trans
        (M.φ_smul γ α _ _ _ _))
    (by
      intro W W' hW h' x
      refine Subtype.ext (funext fun α => ?_)
      exact (congrArg (M.φ γ α _ _) (secRes_secRes (M.M γ) hW h' inf_le_left x)).trans
        ((congrArg (M.φ γ α _ _)
          (secRes_secRes (M.M γ) hW inf_le_left (inf_le_inf_right (U α) h') x)).symm.trans
          (secRes_φ γ α _ _ _ _).symm))

/-- Z3.k (c): `glueCoeval` on sections (should hold by `rfl`). -/
theorem glueCoeval_app (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) {W : Opens X} (h : W ≤ U γ)
    (t : sec R (M.M γ) h) :
    ((glueCoeval M γ).val.app (ovr h)).hom t = glueCoevalSec M γ h t :=
  rfl

/-- Helper: coevaluation after evaluation is the identity on compatible families. -/
private theorem glueCoevalSec_glueEval (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) {W : Opens X}
    (h : W ≤ U γ) (x : glueSub M W) :
    glueCoevalSec M γ h (((glueEval M γ).val.app (ovr h)).hom x) = x :=
  Subtype.ext (funext fun δ =>
    (congrArg (M.φ γ δ _ _) (secRes_secRes (M.M γ) inf_le_right (le_inf le_rfl h) inf_le_left
      (x.1 γ))).trans
      ((x.2 γ δ (inf_le_left : W ⊓ U δ ≤ W) ((inf_le_left : W ⊓ U δ ≤ W).trans h)
        inf_le_right).trans (secRes_id (M.M δ) inf_le_right _ (x.1 δ))))

/-- Helper: evaluation after coevaluation is the identity on sections. -/
private theorem glueEval_glueCoevalSec (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) {W : Opens X}
    (h : W ≤ U γ) (t : sec R (M.M γ) h) :
    ((glueEval M γ).val.app (ovr h)).hom (glueCoevalSec M γ h t) = t :=
  (congrArg (secRes R (M.M γ) inf_le_right (le_inf le_rfl h))
    (M.φ_self γ _ (secRes R (M.M γ) h inf_le_left t))).trans
    ((secRes_secRes (M.M γ) h inf_le_left (le_inf le_rfl h) t).trans
      (secRes_id (M.M γ) h _ t))

/-- **Z3.k (c).** [Căldăraru, §1.2]. A twisted sheaf with trivial cocycle is the twisted sheaf
of its gluing: `ofSheaf (glue M) ≅ M`, with components `glueEval` and `glueCoeval`. No cover
hypothesis. -/
def ofSheafGlueIso (M : TwMod R U (fun _ _ _ => 1)) : TwMod.ofSheaf R U (glueObj M) ≅ M where
  hom := ⟨fun γ => glueEval M γ, fun α β W hα hβ x => x.2 α β le_rfl hα hβ⟩
  inv := ⟨fun γ => glueCoeval M γ, fun α β W hα hβ t =>
    Subtype.ext (funext fun δ =>
      (M.φ_triple α β δ _ _ _ _).symm.trans
        (congrArg (M.φ β δ _ _) (secRes_φ (M := M) α β _ _ _ t).symm))⟩
  hom_inv_id := by
    refine TwMod.hom_ext fun γ => ?_
    ext Y x
    exact glueCoevalSec_glueEval M γ (leOfHom Y.unop.hom) x
  inv_hom_id := by
    refine TwMod.hom_ext fun γ => ?_
    ext Y t
    exact glueEval_glueCoevalSec M γ (leOfHom Y.unop.hom) t

theorem ofSheafGlueIso_hom_f (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) :
    (ofSheafGlueIso M).hom.f γ = glueEval M γ :=
  rfl

theorem ofSheafGlueIso_inv_f (M : TwMod R U (fun _ _ _ => 1)) (γ : ι) :
    (ofSheafGlueIso M).inv.f γ = glueCoeval M γ :=
  rfl

/-- **Z3.k (c).** Naturality of `ofSheafGlueIso`. -/
theorem ofSheafGlueIso_hom_naturality {M M' : TwMod R U (fun _ _ _ => 1)} (f : M ⟶ M') :
    (TwMod.ofSheafFunctor R U).map ((glue R U).map f) ≫ (ofSheafGlueIso M').hom =
      (ofSheafGlueIso M).hom ≫ f := by
  refine TwMod.hom_ext fun γ => ?_
  ext Y x
  exact (app_secRes (f.f γ) inf_le_right (le_inf le_rfl (leOfHom Y.unop.hom)) (x.1 γ)).symm

/-! ## (d) `glue (ofSheaf N) ≅ N` -/

/-- Helper: sections and restriction of `N|U` are those of `N` (definitional). -/
private theorem secRes_restr (N : Mod (ringOf R)) {V W W' : Opens X} (h : W ≤ V) (h' : W' ≤ W)
    (x : N.val.obj (op W)) :
    secRes R ((restr (ringOf R) V).obj N) h h' x = (N.val.map (homOfLE h').op).hom x :=
  rfl

/-- Helper: restricting a section of a sheaf of modules twice is restricting once. -/
private theorem map_res_res (N : Mod (ringOf R)) {W W' W'' : Opens X} (h1 : W' ≤ W)
    (h2 : W'' ≤ W') (x : N.val.obj (op W)) :
    (N.val.map (homOfLE h2).op).hom ((N.val.map (homOfLE h1).op).hom x) =
      (N.val.map (homOfLE (h2.trans h1)).op).hom x :=
  (N.val.map_comp_apply (homOfLE h1).op (homOfLE h2).op x).symm

/-- **Z3.k (d).** The compatible family of restrictions `(t|W ⊓ U_α)_α` of a section `t` of `N`
over `W`. -/
def glueRestrSec (N : Mod (ringOf R)) (W : Opens X) (t : N.val.obj (op W)) :
    glueSub (TwMod.ofSheaf R U N) W :=
  ⟨fun α => (N.val.map (homOfLE (inf_le_left : W ⊓ U α ≤ W)).op).hom t, by
    have key : ∀ (δ : ι) {W' : Opens X} (h : W' ≤ W) (hδ : W' ≤ U δ),
        secRes R ((restr (ringOf R) (U δ)).obj N) inf_le_right (le_inf h hδ)
          ((N.val.map (homOfLE (inf_le_left : W ⊓ U δ ≤ W)).op).hom t) =
        (N.val.map (homOfLE h).op).hom t := fun δ W' h hδ =>
      (secRes_restr N (inf_le_right : W ⊓ U δ ≤ U δ) (le_inf h hδ) _).trans
        (map_res_res N (inf_le_left : W ⊓ U δ ≤ W) (le_inf h hδ) t)
    intro α β W' h hα hβ
    exact (key α h hα).trans (key β h hβ).symm⟩

/-- Helper: `glueRestrSec` is compatible with restriction. -/
private theorem glueRestrSec_res (N : Mod (ringOf R)) {W W' : Opens X} (h : W' ≤ W)
    (t : N.val.obj (op W)) (α : ι) :
    (glueRestrSec (U := U) N W' ((N.val.map (homOfLE h).op).hom t)).1 α =
      secRes R ((restr (ringOf R) (U α)).obj N) inf_le_right (inf_le_inf_right (U α) h)
        ((N.val.map (homOfLE (inf_le_left : W ⊓ U α ≤ W)).op).hom t) :=
  (map_res_res N h inf_le_left t).trans (map_res_res N inf_le_left _ t).symm

set_option linter.internalConstructors false in
/-- **Z3.k (d).** `N ⟶ glue (ofSheaf N)`, `t ↦ (t|W ⊓ U_α)_α`. -/
def toGlueOfSheaf (N : Mod (ringOf R)) : N ⟶ glueObj (TwMod.ofSheaf R U N) :=
  ⟨{ app := fun W => ModuleCat.Hom._mkInternal
        { toFun := glueRestrSec N W.unop
          map_add' := fun t t' => Subtype.ext (funext fun α =>
            map_add (N.val.map (homOfLE (inf_le_left : W.unop ⊓ U α ≤ W.unop)).op).hom t t')
          map_smul' := fun r t => Subtype.ext (funext fun α =>
            ((N.val.map (homOfLE (inf_le_left : W.unop ⊓ U α ≤ W.unop)).op).hom).map_smul r t) }
     naturality := fun {W W'} f => by
       ext t
       exact Subtype.ext (funext fun α => glueRestrSec_res N (leOfHom f.unop) t α) }⟩

/-- Z3.k (d): `toGlueOfSheaf` on sections (should hold by `rfl`). -/
theorem toGlueOfSheaf_app (N : Mod (ringOf R)) (W : Opens X) (t : N.val.obj (op W)) :
    ((toGlueOfSheaf (U := U) N).val.app (op W)).hom t = glueRestrSec N W t :=
  rfl

/-- **Z3.k (d).** Naturality of `toGlueOfSheaf`. -/
theorem toGlueOfSheaf_naturality {N N' : Mod (ringOf R)} (g : N ⟶ N') :
    g ≫ toGlueOfSheaf (U := U) N' =
      toGlueOfSheaf N ≫ (glue R U).map ((TwMod.ofSheafFunctor R U).map g) := by
  ext W t
  exact Subtype.ext (funext fun α =>
    (PresheafOfModules.naturality_apply g.val
      (homOfLE (inf_le_left : W.unop ⊓ U α ≤ W.unop)).op t).symm)

/-- Helper: a morphism of sheaves of modules that is bijective on all sections is an iso. -/
private theorem isIso_of_bijective_app {A B : Mod (ringOf R)} (f : A ⟶ B)
    (h : ∀ W : Opens X, Function.Bijective (f.val.app (op W)).hom) : IsIso f := by
  have : ∀ Y, IsIso (((PresheafOfModules.toPresheaf _).map f.val).app Y) := fun Y =>
    (ConcreteCategory.isIso_iff_bijective _).2 (h Y.unop)
  have h2 : IsIso ((PresheafOfModules.toPresheaf _).map f.val) := NatIso.isIso_of_isIso_app _
  have h2' : IsIso ((PresheafOfModules.toPresheaf (ringOf R).obj).map
      ((SheafOfModules.forget (ringOf R)).map f)) := h2
  have h3 : IsIso ((SheafOfModules.forget (ringOf R)).map f) :=
    isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

/-- Helper: for a cover of `X`, `toGlueOfSheaf N` is bijective on sections over every `W`
(sheaf condition of `N` for the cover `W ⊓ U_α`, via `N|⊤`). -/
private theorem toGlueOfSheaf_bijective (hU : ⨆ α, U α = ⊤) (N : Mod (ringOf R)) (W : Opens X) :
    Function.Bijective ((toGlueOfSheaf (U := U) N).val.app (op W)).hom := by
  have hcov : W ≤ ⨆ α, W ⊓ U α := by rw [← inf_iSup_eq, hU, inf_top_eq]
  constructor
  · intro t t' htt
    exact sec_ext_of_cover (le_top : W ≤ ⊤) ((restr (ringOf R) ⊤).obj N) (fun α => W ⊓ U α)
      (fun α => inf_le_left) hcov t t' fun α => congrFun (congrArg Subtype.val htt) α
  · intro s
    obtain ⟨t, ht, -⟩ := sec_existsUnique_gluing (le_top : W ≤ ⊤) ((restr (ringOf R) ⊤).obj N)
      (fun α => W ⊓ U α) (fun α => inf_le_left) hcov (fun α => s.1 α) (fun i j =>
        s.2 i j (inf_le_left.trans inf_le_left : (W ⊓ U i) ⊓ (W ⊓ U j) ≤ W)
          (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
    exact ⟨t, Subtype.ext (funext fun α => ht α)⟩

/-- **Z3.k (d).** [Stacks 00AK]. If the `U_α` cover `X`, `toGlueOfSheaf N` is an isomorphism:
on sections over `W` it is bijective by the sheaf condition of `N` for the cover `W ⊓ U_α`. -/
theorem isIso_toGlueOfSheaf (hU : ⨆ α, U α = ⊤) (N : Mod (ringOf R)) :
    IsIso (toGlueOfSheaf (U := U) N) :=
  isIso_of_bijective_app _ (toGlueOfSheaf_bijective hU N)

/-! ## (e) The equivalence -/

/-- **Z3.k (e).** [A, Rem 7.2.4], [Căldăraru, Prop 1.2.3] for `ȟ = 1`. For an open cover of `X`,
gluing is an equivalence between twisted sheaves with trivial cocycle and sheaves of `R`-modules
on `X`, with inverse `ofSheafFunctor` (unit from `ofSheafGlueIso`, counit from
`toGlueOfSheaf`). -/
def glueEquiv (hU : ⨆ α, U α = ⊤) : TwMod R U (fun _ _ _ => 1) ≌ Mod (ringOf R) :=
  CategoryTheory.Equivalence.mk (glue R U) (TwMod.ofSheafFunctor R U)
    (NatIso.ofComponents (fun M => (ofSheafGlueIso M).symm) (by
      intro M M' f
      exact (Iso.comp_inv_eq _).2 ((Iso.inv_hom_id_assoc (ofSheafGlueIso M) f).symm.trans
        ((congrArg ((ofSheafGlueIso M).inv ≫ ·) (ofSheafGlueIso_hom_naturality f).symm).trans
          (Category.assoc _ _ _).symm))))
    (NatIso.ofComponents (fun N => haveI := isIso_toGlueOfSheaf hU N
      (asIso (toGlueOfSheaf N)).symm) (by
      intro N N' g
      have h1 := isIso_toGlueOfSheaf hU N
      have h2 := isIso_toGlueOfSheaf hU N'
      exact (IsIso.comp_inv_eq (toGlueOfSheaf (U := U) N')).2
        ((IsIso.inv_hom_id_assoc (toGlueOfSheaf (U := U) N) _).symm.trans
          ((congrArg (inv (toGlueOfSheaf (U := U) N) ≫ ·)
            (toGlueOfSheaf_naturality g).symm).trans (Category.assoc _ _ _).symm))))

theorem glueEquiv_functor (hU : ⨆ α, U α = ⊤) :
    (glueEquiv (R := R) hU).functor = glue R U :=
  rfl

theorem glueEquiv_inverse (hU : ⨆ α, U α = ⊤) :
    (glueEquiv (R := R) hU).inverse = TwMod.ofSheafFunctor R U :=
  rfl

end Cohesive
