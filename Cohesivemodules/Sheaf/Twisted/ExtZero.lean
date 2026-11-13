import Cohesivemodules.Sheaf.Twisted.GlueSec
import Cohesivemodules.Sheaf.Twisted.SecHom
import Cohesivemodules.Sheaf.Flat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

set_option linter.style.header false

/-!
# Z3.l: explicit extension by zero

Blueprint item Z3.l (blueprint §11 v1.20 items 1, 4; `blueprint/blueprint-tw.md` C.8; prototype
P22). For an open `V` and a sheaf of modules `F` on the over-site `Over V`, the extension by zero
`extX V F = j_! F` as a sheaf of `R`-modules on `X`: sections over `W` are the `s ∈ F(W ⊓ V)` with
support closed in `W`, i.e. some open `W' ≤ W` with `W ≤ (W ⊓ V) ⊔ W'` and `s|(W' ⊓ V) = 0`.
Sections, restriction and scalars are definitional, also after `restr U` (used for `extTw`).
* `extX_locally_zero`: sections vanish near every point outside `V`;
* `extXRestrIso`: `(extX V F)|V ≅ F`;
* `isFlat_extX`: `extX V F` is flat if `F` is (S8.b, general form);
* `extXMap`: functoriality in `F`, injective on sections for monomorphisms.

## Deviations
* Mathlib's extension by zero (the left adjoint of restriction) is not used: its sections are not
  explicit, and the gluing maps of twisted sheaves are given on sections (v1.20).
* "Support closed in `W`" is stated without stalks; it is equivalent to the stalk condition.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}

/-- Z3.l: the restriction `R(W) → R(W ⊓ V)`, with target spelled as the ring of sections over
`W ⊓ V ≤ V` of the over-site. -/
abbrev extRing (V W : Opens X) :
    R.obj.obj (op W) →+* ((ringOf R).over V).obj.obj (ovr (inf_le_right : W ⊓ V ≤ V)) :=
  (R.obj.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op).hom

/-- Z3.l: sections of `F` over `W ⊓ V`, as an `R(W)`-module (restriction of scalars along
`extRing`; `r • s = r|(W ⊓ V) • s` definitionally). -/
abbrev extFac (V : Opens X) (F : Mod ((ringOf R).over V)) (W : Opens X) :
    ModuleCat (R.obj.obj (op W)) :=
  (ModuleCat.restrictScalars (extRing (R := R) V W)).obj (sec R F inf_le_right)

/-- Z3.l: restriction of sections is zero-preserving. -/
private theorem secRes_zero' {V W W' : Opens X} (F : Mod ((ringOf R).over V)) (h : W ≤ V)
    (h' : W' ≤ W) : secRes R F h h' 0 = 0 :=
  map_zero (secResHom R F h h')

/-- Z3.l: restriction of sections is additive. -/
private theorem secRes_add' {V W W' : Opens X} (F : Mod ((ringOf R).over V)) (h : W ≤ V)
    (h' : W' ≤ W) (a b : sec R F h) :
    secRes R F h h' (a + b) = secRes R F h h' a + secRes R F h h' b :=
  map_add (secResHom R F h h') a b

/-- Z3.l: a section vanishing on `W₁ ⊓ V` vanishes on every smaller `W₃ ⊓ V`. -/
private theorem extRes_zero_of_le {V W W₁ W₃ : Opens X} (F : Mod ((ringOf R).over V))
    (h₁ : W₁ ≤ W) (h₃ : W₃ ≤ W₁) (a : sec R F (inf_le_right : W ⊓ V ≤ V))
    (ha : secRes R F inf_le_right (inf_le_inf_right V h₁) a = 0) :
    secRes R F inf_le_right (inf_le_inf_right V (h₃.trans h₁)) a = 0 := by
  have e := secRes_secRes F (inf_le_right : W ⊓ V ≤ V) (inf_le_inf_right V h₁)
    (inf_le_inf_right V h₃) a
  rw [ha, secRes_zero'] at e
  exact e.symm

/-- **Z3.l.** [Stacks 02UT], [Hartshorne II Ex. 1.19]. Sections of `F` over `W ⊓ V` with support
closed in `W`: there is an open `W' ≤ W` with `W ≤ (W ⊓ V) ⊔ W'` on which the section vanishes
(`s|(W' ⊓ V) = 0`). -/
def extSub (V : Opens X) (F : Mod ((ringOf R).over V)) (W : Opens X) :
    Submodule (R.obj.obj (op W)) (extFac V F W) where
  carrier := {s | ∃ W' : Opens X, ∃ h : W' ≤ W, W ≤ (W ⊓ V) ⊔ W' ∧
    secRes R F inf_le_right (inf_le_inf_right V h) s = 0}
  add_mem' := by
    rintro a b ⟨W₁, h₁, c₁, z₁⟩ ⟨W₂, h₂, c₂, z₂⟩
    refine ⟨W₁ ⊓ W₂, inf_le_left.trans h₁, ?_, ?_⟩
    · calc W ≤ ((W ⊓ V) ⊔ W₁) ⊓ ((W ⊓ V) ⊔ W₂) := le_inf c₁ c₂
        _ = (W ⊓ V) ⊔ (W₁ ⊓ W₂) := (sup_inf_left _ _ _).symm
    · have e1 := extRes_zero_of_le F h₁ (inf_le_left : W₁ ⊓ W₂ ≤ W₁) a z₁
      have e2 := extRes_zero_of_le F h₂ (inf_le_right : W₁ ⊓ W₂ ≤ W₂) b z₂
      exact (secRes_add' F (inf_le_right : W ⊓ V ≤ V)
        (inf_le_inf_right V ((inf_le_left : W₁ ⊓ W₂ ≤ W₁).trans h₁)) a b).trans
        (by rw [e1, e2, add_zero])
  zero_mem' := ⟨W, le_rfl, le_sup_right, map_zero _⟩
  smul_mem' := by
    rintro r s ⟨W', h, c, z⟩
    refine ⟨W', h, c, ?_⟩
    have e := secRes_smul F (inf_le_right : W ⊓ V ≤ V) (inf_le_inf_right V h) (extRing V W r) s
    exact e.trans (by rw [z, smul_zero])

theorem mem_extSub {V : Opens X} {F : Mod ((ringOf R).over V)} {W : Opens X}
    {s : extFac V F W} :
    s ∈ extSub V F W ↔ ∃ W' : Opens X, ∃ h : W' ≤ W, W ≤ (W ⊓ V) ⊔ W' ∧
      secRes R F inf_le_right (inf_le_inf_right V h) s = 0 :=
  Iff.rfl

/-- Z3.l: `extRing` is natural in `W`. -/
private theorem extRing_nat {V W W₂ : Opens X} (h : W₂ ≤ W) (r : R.obj.obj (op W)) :
    (R.obj.map (homOfLE (inf_le_inf_right V h : W₂ ⊓ V ≤ W ⊓ V)).op).hom (extRing V W r) =
      extRing V W₂ ((R.obj.map (homOfLE h).op).hom r) := by
  change (R.obj.map (homOfLE (inf_le_inf_right V h : W₂ ⊓ V ≤ W ⊓ V)).op).hom
    ((R.obj.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op).hom r) =
    (R.obj.map (homOfLE (inf_le_left : W₂ ⊓ V ≤ W₂)).op).hom
      ((R.obj.map (homOfLE h).op).hom r)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Z3.l: a witness for `s ∈ extSub V F W` restricts to one over `W₂ ≤ W`. -/
private theorem ext_cover_restrict {V W W₂ W' : Opens X} (h : W₂ ≤ W) (c : W ≤ W ⊓ V ⊔ W') :
    W₂ ≤ W₂ ⊓ V ⊔ W₂ ⊓ W' :=
  calc W₂ ≤ W₂ ⊓ (W ⊓ V ⊔ W') := le_inf le_rfl (h.trans c)
    _ = W₂ ⊓ (W ⊓ V) ⊔ W₂ ⊓ W' := inf_sup_left _ _ _
    _ ≤ W₂ ⊓ V ⊔ W₂ ⊓ W' :=
      sup_le_sup_right (le_inf inf_le_left (inf_le_right.trans inf_le_right)) _

/-- **Z3.l.** Restriction from `W` to `W₂ ≤ W`, along `W₂ ⊓ V ≤ W ⊓ V`; semilinear over
`R(W) → R(W₂)`. -/
def extRes (V : Opens X) (F : Mod ((ringOf R).over V)) {W W₂ : Opens X} (h : W₂ ≤ W) :
    extSub V F W →ₛₗ[(R.obj.map (homOfLE h).op).hom] extSub V F W₂ where
  toFun s := ⟨secRes R F inf_le_right (inf_le_inf_right V h) s.1, by
    obtain ⟨W', h', c, z⟩ := s.2
    refine ⟨W₂ ⊓ W', inf_le_left, ext_cover_restrict h c, ?_⟩
    have e := secRes_secRes F (inf_le_right : W ⊓ V ≤ V) (inf_le_inf_right V h)
      (inf_le_inf_right V (inf_le_left : W₂ ⊓ W' ≤ W₂)) s.1
    have z' := extRes_zero_of_le F h' (inf_le_right : W₂ ⊓ W' ≤ W') s.1 z
    exact e.trans z'⟩
  map_add' := fun s t => Subtype.ext
    (secRes_add' F (inf_le_right : W ⊓ V ≤ V) (inf_le_inf_right V h) s.1 t.1)
  map_smul' := fun r s => Subtype.ext
    ((secRes_smul F (inf_le_right : W ⊓ V ≤ V) (inf_le_inf_right V h) (extRing V W r) s.1).trans
      (congrArg (fun a => toSec R (inf_le_inf_right V h |>.trans inf_le_right) a •
        secRes R F inf_le_right (inf_le_inf_right V h) s.1) (extRing_nat h r)))

theorem extRes_apply (V : Opens X) (F : Mod ((ringOf R).over V)) {W W₂ : Opens X} (h : W₂ ≤ W)
    (s : extSub V F W) :
    (extRes V F h s).1 = secRes R F inf_le_right (inf_le_inf_right V h) s.1 :=
  rfl

/-- **Z3.l.** The presheaf `j_! F` of `R`-modules on `X`. -/
def extPre (V : Opens X) (F : Mod ((ringOf R).over V)) : PresheafOfModules.{0} (ringOf R).obj where
  obj W := ModuleCat.of (R.obj.obj (op W.unop)) (extSub V F W.unop)
  map {W W'} f := ModuleCat.semilinearMapAddEquiv (R.obj.map f).hom
      (ModuleCat.of (R.obj.obj (op W.unop)) (extSub V F W.unop))
      (ModuleCat.of (R.obj.obj (op W'.unop)) (extSub V F W'.unop))
      (extRes V F (leOfHom f.unop))
  map_id W := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    exact Subtype.ext (secRes_id F inf_le_right _ x.1)
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    exact Subtype.ext
      (secRes_secRes F (inf_le_right : _ ⊓ V ≤ V) (inf_le_inf_right V (leOfHom f.unop))
        (inf_le_inf_right V (leOfHom g.unop)) x.1).symm

/-- Z3.l: sections over a cover that agree on `Y i ⊓ Y j ⊓ V` agree on the overlaps of the cover
`Y i ⊓ V` of `(⨆ Y i) ⊓ V`. -/
private theorem ext_comp_compat (V : Opens X) (F : Mod ((ringOf R).over V)) {κ : Type}
    (Y : κ → Opens X) (s' : ∀ i, extSub V F (Y i))
    (hc : ∀ i j, secRes R F (inf_le_right : Y i ⊓ V ≤ V)
        (inf_le_inf_right V (inf_le_left : Y i ⊓ Y j ≤ Y i)) (s' i).1 =
      secRes R F (inf_le_right : Y j ⊓ V ≤ V)
        (inf_le_inf_right V (inf_le_right : Y i ⊓ Y j ≤ Y j)) (s' j).1) (i j : κ) :
    secRes R F (inf_le_right : Y i ⊓ V ≤ V)
        (inf_le_left : Y i ⊓ V ⊓ (Y j ⊓ V) ≤ Y i ⊓ V) (s' i).1 =
      secRes R F (inf_le_right : Y j ⊓ V ≤ V)
        (inf_le_right : Y i ⊓ V ⊓ (Y j ⊓ V) ≤ Y j ⊓ V) (s' j).1 := by
  have k : Y i ⊓ V ⊓ (Y j ⊓ V) ≤ (Y i ⊓ Y j) ⊓ V :=
    le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (inf_le_left.trans inf_le_right)
  have e1 := secRes_secRes F (inf_le_right : Y i ⊓ V ≤ V)
    (inf_le_inf_right V (inf_le_left : Y i ⊓ Y j ≤ Y i)) k (s' i).1
  have e2 := secRes_secRes F (inf_le_right : Y j ⊓ V ≤ V)
    (inf_le_inf_right V (inf_le_right : Y i ⊓ Y j ≤ Y j)) k (s' j).1
  exact e1.symm.trans ((congrArg (secRes R F _ k) (hc i j)).trans e2)

/-- Z3.l: the glued section over `(⨆ Y i) ⊓ V` has support closed in `⨆ Y i`, with witness
`⨆ W'_i`, provided each `s' i` has witness `W'_i` and restricts correctly. -/
private theorem ext_glued_mem (V : Opens X) (F : Mod ((ringOf R).over V)) {κ : Type}
    (Y : κ → Opens X) (s' : ∀ i, extSub V F (Y i))
    (t : sec R F (inf_le_right : (⨆ i, Y i) ⊓ V ≤ V))
    (ht : ∀ i, secRes R F (inf_le_right : (⨆ i, Y i) ⊓ V ≤ V)
        (inf_le_inf_right V (le_iSup Y i)) t = (s' i).1) :
    t ∈ extSub V F (⨆ i, Y i) := by
  choose W' hW' hc hz using fun i => (s' i).2
  have hK : (⨆ i, W' i) ≤ ⨆ i, Y i := iSup_le fun i => (hW' i).trans (le_iSup Y i)
  refine ⟨⨆ i, W' i, hK, iSup_le fun i => (hc i).trans
    (sup_le_sup (inf_le_inf_right V (le_iSup Y i)) (le_iSup W' i)), ?_⟩
  refine sec_ext_of_cover (R := R) (inf_le_right : (⨆ i, W' i) ⊓ V ≤ V) F
    (fun i => W' i ⊓ V) (fun i => inf_le_inf_right V (le_iSup W' i))
    (by rw [← iSup_inf_eq]) _ _ fun i => ?_
  have e1 := secRes_secRes F (inf_le_right : (⨆ i, Y i) ⊓ V ≤ V) (inf_le_inf_right V hK)
    (inf_le_inf_right V (le_iSup W' i)) t
  have e2 := secRes_secRes F (inf_le_right : (⨆ i, Y i) ⊓ V ≤ V)
    (inf_le_inf_right V (le_iSup Y i))
    (inf_le_inf_right V (hW' i)) t
  have z' := extRes_zero_of_le F (hW' i) (le_refl (W' i)) (s' i).1 (hz i)
  refine e1.trans ((e2.symm.trans ((congrArg (secRes R F _ (inf_le_inf_right V (hW' i)))
    (ht i)).trans z')).trans (secRes_zero' F _ _).symm)

/-- **Z3.l.** `j_! F` is a sheaf: sections over the members of a cover glue in `F` over the
`W_i ⊓ V` (`sec_existsUnique_gluing`), and the glued section has support closed in `⨆ W_i` with
witness `⨆ W'_i`. -/
theorem isSheaf_extPre (V : Opens X) (F : Mod ((ringOf R).over V)) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (extPre V F).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (X := TopCat.of X) (extPre V F).presheaf).2 ?_
  intro κ Y sf hsf
  let s' : ∀ i, extSub V F (Y i) := sf
  have hc : ∀ i j, secRes R F (inf_le_right : Y i ⊓ V ≤ V)
        (inf_le_inf_right V (inf_le_left : Y i ⊓ Y j ≤ Y i)) (s' i).1 =
      secRes R F (inf_le_right : Y j ⊓ V ≤ V)
        (inf_le_inf_right V (inf_le_right : Y i ⊓ Y j ≤ Y j)) (s' j).1 :=
    fun i j => congrArg Subtype.val (hsf i j)
  have hcov : (⨆ i, Y i) ⊓ V ≤ ⨆ i, Y i ⊓ V := by
    rw [← iSup_inf_eq]
  obtain ⟨t, ht, hu⟩ := sec_existsUnique_gluing (R := R)
    (inf_le_right : (⨆ i, Y i) ⊓ V ≤ V) F (fun i => Y i ⊓ V)
    (fun i => inf_le_inf_right V (le_iSup Y i)) hcov (fun i => (s' i).1)
    (ext_comp_compat V F Y s' hc)
  refine ⟨⟨t, ext_glued_mem V F Y s' t ht⟩, fun i => Subtype.ext (ht i), fun s'' hs'' => ?_⟩
  exact Subtype.ext (hu s''.1 fun i => congrArg Subtype.val (hs'' i))

/-- **Z3.l.** [Stacks 02UT]. The extension by zero `j_! F` of a sheaf of modules `F` on `Over V`,
as a sheaf of `R`-modules on `X`. -/
def extX (V : Opens X) (F : Mod ((ringOf R).over V)) : Mod (ringOf R) :=
  ⟨extPre V F, isSheaf_extPre V F⟩

/-- Z3.l: sections of `j_! F` over `W` (rfl). -/
theorem extX_obj (V : Opens X) (F : Mod ((ringOf R).over V)) (W : Opens X) :
    (extX V F).val.obj (op W) = ModuleCat.of (R.obj.obj (op W)) (extSub V F W) :=
  rfl

/-- Z3.l: restriction in `j_! F` is `extRes` (rfl). -/
theorem extX_map_apply (V : Opens X) (F : Mod ((ringOf R).over V)) {W W₂ : Opens X}
    (h : W₂ ≤ W) (s : extSub V F W) :
    ((extX V F).val.map (homOfLE h).op).hom s = extRes V F h s :=
  rfl

/-- **Z3.l.** Sections of `j_! F` vanish near every point outside `V` (`x` lies in the witness
`W'`, where the section is zero). -/
theorem extX_locally_zero (V : Opens X) (F : Mod ((ringOf R).over V)) {W : Opens X}
    (s : (extX V F).val.obj (op W)) {x : X} (hxW : x ∈ W) (hxV : x ∉ V) :
    ∃ (W₂ : Opens X) (h : W₂ ≤ W), x ∈ W₂ ∧ mres (extX V F) h s = 0 := by
  obtain ⟨W', h, c, z⟩ := (show extSub V F W from s).2
  have hx : x ∈ W ⊓ V ⊔ W' := c hxW
  rcases Opens.mem_sup.1 hx with hx | hx
  · exact absurd hx.2 hxV
  · exact ⟨W', h, hx, Subtype.ext z⟩

/-- Z3.l: sections of a sheaf on `Over V` over an open `W ≤ ⊥` are zero. -/
private theorem sec_eq_zero_of_le_bot {V W : Opens X} (F : Mod ((ringOf R).over V)) (h : W ≤ V)
    (hW : W ≤ ⊥) (s : sec R F h) : s = 0 :=
  sec_ext_of_cover (R := R) h F (κ := Empty) (fun i => nomatch i) (fun i => nomatch i)
    (hW.trans (by rw [iSup_of_empty])) s 0 fun i => nomatch i

/-- **Z3.l.** Sections of a sheaf on `Over V` over the empty open are zero. -/
theorem sec_bot_eq_zero {V : Opens X} (F : Mod ((ringOf R).over V)) (h : (⊥ : Opens X) ≤ V)
    (s : sec R F h) : s = 0 :=
  sec_eq_zero_of_le_bot F h le_rfl s

/-- Z3.l: restricting `r|(W ⊓ V)` back along `W ≤ W ⊓ V` gives `r`. -/
private theorem extRing_res_self {V W : Opens X} (hW : W ≤ V) (r : R.obj.obj (op W)) :
    (R.obj.map (homOfLE (le_inf le_rfl hW : W ≤ W ⊓ V)).op).hom (extRing V W r) = r := by
  change (R.obj.map (homOfLE (le_inf le_rfl hW : W ≤ W ⊓ V)).op).hom
    ((R.obj.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op).hom r) = r
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  have e : (homOfLE (inf_le_left : W ⊓ V ≤ W)).op ≫
      (homOfLE (le_inf le_rfl hW : W ≤ W ⊓ V)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [e, R.obj.map_id]
  rfl

/-- Z3.l: the forward map of `extXRestrIso` on sections over `W ≤ V`: `s ↦ s|W`. -/
private def extRestrFwd (V : Opens X) (F : Mod ((ringOf R).over V)) {W : Opens X} (hW : W ≤ V) :
    extSub V F W →+ sec R F hW where
  toFun s := secRes R F (inf_le_right : W ⊓ V ≤ V) (le_inf le_rfl hW : W ≤ W ⊓ V) s.1
  map_zero' := secRes_zero' F _ _
  map_add' := fun s t => secRes_add' F (inf_le_right : W ⊓ V ≤ V)
    (le_inf le_rfl hW : W ≤ W ⊓ V) s.1 t.1

/-- Z3.l: the backward map of `extXRestrIso` on sections over `W ≤ V`: `t ↦ t|(W ⊓ V)`, with
witness `⊥`. -/
private def extRestrBwd (V : Opens X) (F : Mod ((ringOf R).over V)) {W : Opens X} (hW : W ≤ V) :
    sec R F hW →+ extSub V F W where
  toFun t := ⟨secRes R F hW (inf_le_left : W ⊓ V ≤ W) t, ⊥, bot_le,
    by simpa using le_inf le_rfl hW,
    sec_eq_zero_of_le_bot F _ (inf_le_left : (⊥ : Opens X) ⊓ V ≤ ⊥) _⟩
  map_zero' := Subtype.ext (secRes_zero' F _ _)
  map_add' := fun s t => Subtype.ext (secRes_add' F _ _ s t)

/-- Z3.l: the forward map is `R(W)`-linear. -/
private theorem extRestrFwd_smul (V : Opens X) (F : Mod ((ringOf R).over V)) {W : Opens X}
    (hW : W ≤ V) (r : R.obj.obj (op W)) (x : extSub V F W) :
    extRestrFwd V F hW (r • x) = toSec R hW r • extRestrFwd V F hW x :=
  (secRes_smul F (inf_le_right : W ⊓ V ≤ V) (le_inf le_rfl hW : W ≤ W ⊓ V) (extRing V W r)
    x.1).trans (congrArg (fun a => toSec R hW a • extRestrFwd V F hW x) (extRing_res_self hW r))

/-- Z3.l: the backward map is `R(W)`-linear. -/
private theorem extRestrBwd_smul (V : Opens X) (F : Mod ((ringOf R).over V)) {W : Opens X}
    (hW : W ≤ V) (r : R.obj.obj (op W)) (t : sec R F hW) :
    extRestrBwd V F hW (toSec R hW r • t) = r • extRestrBwd V F hW t :=
  Subtype.ext (secRes_smul F hW (inf_le_left : W ⊓ V ≤ W) r t)

/-- Z3.l: the forward map commutes with restriction. -/
private theorem extRestrFwd_res (V : Opens X) (F : Mod ((ringOf R).over V)) {W W' : Opens X}
    (hW : W ≤ V) (h' : W' ≤ W) (x : extSub V F W) :
    extRestrFwd V F (h'.trans hW) (extRes V F h' x) = secRes R F hW h' (extRestrFwd V F hW x) := by
  refine (secRes_secRes F (inf_le_right : W ⊓ V ≤ V) (inf_le_inf_right V h')
    (le_inf le_rfl (h'.trans hW) : W' ≤ W' ⊓ V) x.1).trans ?_
  exact (secRes_secRes F (inf_le_right : W ⊓ V ≤ V) (le_inf le_rfl hW : W ≤ W ⊓ V) h' x.1).symm

/-- Z3.l: the backward map commutes with restriction. -/
private theorem extRestrBwd_res (V : Opens X) (F : Mod ((ringOf R).over V)) {W W' : Opens X}
    (hW : W ≤ V) (h' : W' ≤ W) (t : sec R F hW) :
    extRestrBwd V F (h'.trans hW) (secRes R F hW h' t) =
      extRes V F h' (extRestrBwd V F hW t) :=
  Subtype.ext
    ((secRes_secRes F hW h' (inf_le_left : W' ⊓ V ≤ W') t).trans
      (secRes_secRes F hW (inf_le_left : W ⊓ V ≤ W) (inf_le_inf_right V h') t).symm)

/-- **Z3.l.** `(j_! F)|V ≅ F`: on `W ≤ V`, `s ↦ s|W` (`W ≤ W ⊓ V`), inverse `t ↦ t|(W ⊓ V)` with
witness `⊥`. -/
def extXRestrIso (V : Opens X) (F : Mod ((ringOf R).over V)) :
    (restr (ringOf R) V).obj (extX V F) ≅ F where
  hom := homOfSec₀ (fun hW => extRestrFwd V F hW) (fun hW r x => extRestrFwd_smul V F hW r x)
    (fun hW h' x => extRestrFwd_res V F hW h' x)
  inv := homOfSec₀ (fun hW => extRestrBwd V F hW) (fun hW r x => extRestrBwd_smul V F hW r x)
    (fun hW h' x => extRestrBwd_res V F hW h' x)
  hom_inv_id := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.Hom.ext
    funext Y
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun s => ?_
    exact Subtype.ext
      ((secRes_secRes F (inf_le_right : _ ⊓ V ≤ V) (le_inf le_rfl (leOfHom Y.unop.hom))
        (inf_le_left) s.1).trans (secRes_id F (inf_le_right : _ ⊓ V ≤ V) _ s.1))
  inv_hom_id := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.Hom.ext
    funext Y
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun t => ?_
    exact (secRes_secRes F (leOfHom Y.unop.hom) (inf_le_left)
      (le_inf le_rfl (leOfHom Y.unop.hom)) t).trans (secRes_id F _ _ t)

/-- Z3.l: `extXRestrIso` on sections (should hold by `rfl`). -/
theorem extXRestrIso_hom_app (V : Opens X) (F : Mod ((ringOf R).over V)) {W : Opens X}
    (h : W ≤ V) (s : extSub V F W) :
    ((extXRestrIso V F).hom.val.app (ovr h)).hom s =
      secRes R F inf_le_right (le_inf le_rfl h : W ≤ W ⊓ V) s.1 :=
  rfl

/-- Z3.l: flatness transfers along an isomorphism (retract argument). -/
private theorem isFlat_of_iso_ext {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {S : Sheaf J CommRingCat.{0}} {M F : Mod (ringOf S)} (e : M ≅ F) (hF : IsFlat S F) :
    IsFlat S M := by
  refine ⟨fun {N' N} f hf => ?_⟩
  have h1 : Mono (((tensorBifunctor S).obj F).map f) := hF.preserves f
  have hsplit : ((tensorBifunctor S).map e.hom).app N' ≫ ((tensorBifunctor S).map e.inv).app N' =
      𝟙 _ := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id]
    rfl
  have h2 : Mono (((tensorBifunctor S).map e.hom).app N') := mono_of_mono_fac hsplit
  have h3 : Mono (((tensorBifunctor S).map e.hom).app N' ≫ ((tensorBifunctor S).obj F).map f) :=
    mono_comp _ _
  have hnat := ((tensorBifunctor S).map e.hom).naturality f
  rw [← hnat] at h3
  exact mono_of_mono _ (((tensorBifunctor S).map e.hom).app N)

/-- **Z3.l.** [Stacks 03EV], S8.b general form. The extension by zero of a flat sheaf is flat
(`isFlat_of_locally_zero` with `extX_locally_zero` and `extXRestrIso`). -/
theorem isFlat_extX {V : Opens X} {F : Mod ((ringOf R).over V)} (hF : IsFlat (R.over V) F) :
    IsFlat R (extX V F) :=
  isFlat_of_locally_zero R V (extX V F) (fun s _ hx hxV => extX_locally_zero V F s hx hxV)
    (isFlat_of_iso_ext (extXRestrIso V F) hF)

/-- **Z3.l.** A morphism `F ⟶ F'` acts on sections with support closed in `W` (same witness). -/
def extXMapL {V : Opens X} {F F' : Mod ((ringOf R).over V)} (f : F ⟶ F') (W : Opens X) :
    extSub V F W →ₗ[R.obj.obj (op W)] extSub V F' W where
  toFun s := ⟨(f.val.app (ovr inf_le_right)).hom s.1, by
    obtain ⟨W', h, c, z⟩ := s.2
    refine ⟨W', h, c, ?_⟩
    have e := app_secRes f (inf_le_right : W ⊓ V ≤ V) (inf_le_inf_right V h) s.1
    rw [z] at e
    exact e.symm.trans (map_zero _)⟩
  map_add' := fun s t => Subtype.ext
    (((f.val.app (ovr inf_le_right)).hom.map_add s.1 t.1))
  map_smul' := fun r s => Subtype.ext
    (app_smul f (inf_le_right : W ⊓ V ≤ V) (extRing V W r) s.1)

theorem extXMapL_apply {V : Opens X} {F F' : Mod ((ringOf R).over V)} (f : F ⟶ F') (W : Opens X)
    (s : extSub V F W) : (extXMapL f W s).1 = (f.val.app (ovr inf_le_right)).hom s.1 :=
  rfl

/-- **Z3.l.** Functoriality of `j_!`: the morphism `j_! F ⟶ j_! F'` induced by `f : F ⟶ F'`. -/
def extXMap {V : Opens X} {F F' : Mod ((ringOf R).over V)} (f : F ⟶ F') : extX V F ⟶ extX V F' :=
  ⟨{ app := fun W => ModuleCat.ofHom (extXMapL f W.unop)
     naturality := by
       intro W W' g
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun s => ?_
       exact Subtype.ext
         (app_secRes f (inf_le_right : W.unop ⊓ V ≤ V)
           (inf_le_inf_right V (leOfHom g.unop)) s.1) }⟩

theorem extXMap_app {V : Opens X} {F F' : Mod ((ringOf R).over V)} (f : F ⟶ F') (W : Opens X)
    (s : extSub V F W) : ((extXMap f).val.app (op W)).hom s = extXMapL f W s :=
  rfl

theorem extXMap_id {V : Opens X} (F : Mod ((ringOf R).over V)) : extXMap (𝟙 F) = 𝟙 _ := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext W
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun s => ?_
  exact Subtype.ext rfl

theorem extXMap_comp {V : Opens X} {F F' F'' : Mod ((ringOf R).over V)} (f : F ⟶ F')
    (g : F' ⟶ F'') : extXMap (f ≫ g) = extXMap f ≫ extXMap g := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.Hom.ext
  funext W
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun s => ?_
  exact Subtype.ext rfl

/-- **Z3.l.** `j_!` preserves monomorphisms (injective on sections). -/
theorem mono_extXMap {V : Opens X} {F F' : Mod ((ringOf R).over V)} (f : F ⟶ F') [Mono f] :
    Mono (extXMap f) := by
  refine Functor.mono_of_mono_map (SheafOfModules.forget (ringOf R)) ?_
  refine PresheafOfModules.mono_of_injective fun W => ?_
  obtain ⟨W⟩ := W
  intro a b hab
  exact Subtype.ext (sec_injective_of_mono f (inf_le_right : W ⊓ V ≤ V) (congrArg Subtype.val hab))

end Cohesive
