import Cohesivemodules.Sheaf.BaseChangeRestrOver
import Cohesivemodules.Sheaf.Twisted.SubQuot
import Cohesivemodules.Sheaf.Twisted.Preadditive

set_option linter.style.header false

/-!
# Z3.l′: base change of twisted sheaves

Blueprint item Z3.l′ (`blueprint/blueprint-tw.md` §3 C.7′ (c); blueprint §11 v1.20 item 6). For a
map of sheaves of commutative rings `ψ : R ⟶ S` on `X` and a cover `U`, base change of
`ȟ`-twisted `R`-modules to `ψ(ȟ)`-twisted `S`-modules, componentwise S8.a's `sheafBC`:
* `chMap ψ ch`: the cocycle `ψ(ȟ)` (units mapped along `ψ`);
* `TwMod.bcGlue ψ M α β`: the gluing of `S ⊗ M` on `Over (U_α ⊓ U_β)`,
  `(a)⁻¹ ∘ (S ⊗ g_αβ) ∘ (a)` with `g_αβ = M.glueHom α β` (C.2′) and (a) = `sheafBCRestrOverIso`;
* `bcφ_bcUnit`: the key formula `φ′_αβ(η m) = η(φ_αβ m)`;
* `TwMod.bcObj`, `TwMod.bcMap`, `twBC ψ : TwMod R U ch ⥤ TwMod S U (chMap ψ ch)`, additive, with
  components `sheafBC` (`twBC_obj_M`, `twBC_map_f`, rfl).
Used in Z3.u (blueprint-tw G.2): `F := glue(rescale_{u⁻¹}(twBC ρ K'))`.

## Deviations
* Gluing maps of `S ⊗ M` are defined through sheaf morphisms on the double overlaps, since
  sections of `sheafBC` are not explicit; they are characterized on `η(m)` (`bcφ_bcUnit`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X]
  {R S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} (ψ : R ⟶ S)
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- **Z3.l′ (C.7′ (c)).** The cocycle `ψ(ȟ)`: the units `ȟ_αβγ ∈ R(U_αβγ)ˣ` mapped along
`ψ : R(U_αβγ) → S(U_αβγ)`. -/
def chMap (ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ) :
    ∀ α β γ, (S.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ :=
  fun α β γ => Units.map (ψ.hom.app (op (U α ⊓ U β ⊓ U γ))).hom.toMonoidHom (ch α β γ)

/-- **Z3.l′ (C.7′ (c)).** The gluing of `S ⊗ M` on the double overlap `Over (U_α ⊓ U_β)`:
`(S ⊗ M_α)|U_αβ ≅ S ⊗ (M_α|U_αβ) → S ⊗ (M_β|U_αβ) ≅ (S ⊗ M_β)|U_αβ`, the middle map `S ⊗ g_αβ`
with `g_αβ = M.glueHom α β` (the gluing maps of `M` as a sheaf morphism, C.2′). -/
def TwMod.bcGlue (M : TwMod R U ch) (α β : ι) :
    (resL α β).obj ((sheafBC (overHom ψ (U α))).obj (M.M α)) ⟶
      (resR α β).obj ((sheafBC (overHom ψ (U β))).obj (M.M β)) :=
  (sheafBCRestrOverIso ψ inf_le_left (M.M α)).hom ≫
    (sheafBC (overHom ψ (U α ⊓ U β))).map (M.glueHom α β) ≫
      (sheafBCRestrOverIso ψ inf_le_right (M.M β)).inv

/-- **Z3.l′ (C.7′ (c)).** The gluing maps of `S ⊗ M` on `η`: `φ′_αβ(1 ⊗ m) = 1 ⊗ φ_αβ(m)`. -/
theorem bcφ_bcUnit (M : TwMod R U ch) (α β : ι) {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β)
    (m : sec R (M.M α) hα) :
    secOfGlue (M.bcGlue ψ) α β hα hβ (bcUnit ψ (M.M α) hα m) =
      bcUnit ψ (M.M β) hβ (M.φ α β hα hβ m) := by
  have e1 := sheafBCRestrOverIso_bcUnit ψ (inf_le_left : U α ⊓ U β ≤ U α) (M.M α)
    (le_inf hα hβ) m
  have e2 := bcUnit_map ψ (M.glueHom α β) (le_inf hα hβ) m
  have e3 := sheafBCRestrOverIso_bcUnit ψ (inf_le_right : U α ⊓ U β ≤ U β) (M.M β)
    (le_inf hα hβ) (M.φ α β hα hβ m)
  unfold secOfGlue TwMod.bcGlue
  change (((sheafBCRestrOverIso ψ inf_le_right (M.M β)).inv.val.app (ovr (le_inf hα hβ))).hom
    ((((sheafBC (overHom ψ (U α ⊓ U β))).map (M.glueHom α β)).val.app
      (ovr (le_inf hα hβ))).hom
    (((sheafBCRestrOverIso ψ inf_le_left (M.M α)).hom.val.app (ovr (le_inf hα hβ))).hom
      (bcUnit ψ (M.M α) hα m)))) = _
  rw [e1, e2]
  refine Eq.trans (congrArg (fun y => (((sheafBCRestrOverIso ψ inf_le_right (M.M β)).inv.val.app
    (ovr (le_inf hα hβ))).hom y)) e3.symm) ?_
  exact congrArg (fun k => (k.val.app (ovr (le_inf hα hβ))).hom
    (bcUnit ψ (M.M β) hβ (M.φ α β hα hβ m))) (Iso.hom_inv_id (sheafBCRestrOverIso ψ
      (inf_le_right : U α ⊓ U β ≤ U β) (M.M β)))

/-- **Z3.l′ (C.7′ (c)).** `φ′_αα = id` (by uniqueness on `η`, `sec_eq_of_bcUnit`). -/
theorem bcφ_self (M : TwMod R U ch) (α : ι) {W : Opens X} (hα : W ≤ U α)
    (x : sec S ((sheafBC (overHom ψ (U α))).obj (M.M α)) hα) :
    secOfGlue (M.bcGlue ψ) α α hα hα x = x := by
  refine sec_eq_of_bcUnit ψ hα hα
    (fun hW' => secOfGlue (M.bcGlue ψ) α α (hW'.trans hα) (hW'.trans hα))
    (fun hW' => AddMonoidHom.id _)
    (fun hW' r y => secOfGlue_smul _ _ _ _ _ _ _)
    (fun hW' h' y => secOfGlue_res _ _ _ _ _ _ _)
    (fun hW' r y => rfl) (fun hW' h' y => rfl) ?_ x
  intro W' hW' m
  rw [bcφ_bcUnit]
  exact congrArg _ (M.φ_self α _ m)

/-- Z3.l′: `ψ` commutes with restriction of the cocycle: `ψ(ȟ|W) = ψ(ȟ)|W`. -/
private theorem psi_unitRes {W V : Opens X} (k : W ≤ V) (c : (R.obj.obj (op V))ˣ) :
    (ψ.hom.app (op W)).hom (unitRes R k c : R.obj.obj (op W)) =
      (unitRes S k (Units.map (ψ.hom.app (op V)).hom.toMonoidHom c) : S.obj.obj (op W)) := by
  change (ψ.hom.app (op W)).hom ((R.obj.map (homOfLE k).op).hom c) =
    (S.obj.map (homOfLE k).op).hom ((ψ.hom.app (op V)).hom c)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  exact congrArg (fun t => t.hom c) (ψ.hom.naturality (homOfLE k).op)

/-- Z3.l′: multiplication by a section `c` of `S` on sections of `Q`, as an additive map. -/
private def scaleHom {V : Opens X} (Q : Mod ((ringOf S).over V)) {W : Opens X} (h : W ≤ V)
    (c : S.obj.obj (op W)) : sec S Q h →+ sec S Q h :=
  DistribSMul.toAddMonoidHom _ (toSec S h c)

/-- Z3.l′: scalars commute on sections (commutativity of `S(W)`). -/
private theorem toSec_smul_comm' {V : Opens X} (N : Mod ((ringOf S).over V)) {W : Opens X}
    (h : W ≤ V) (a b : S.obj.obj (op W)) (y : sec S N h) :
    toSec S h a • toSec S h b • y = toSec S h b • toSec S h a • y := by
  rw [← mul_smul, ← mul_smul]
  exact congrArg (· • y) (mul_comm a b)

/-- Z3.l′: the composite `φ′_βγ ∘ φ′_αβ` of two gluing maps on sections over `W`. -/
private def cocA {N : ∀ α, Mod ((ringOf S).over (U α))}
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α β γ : ι) {W : Opens X}
    (hα : W ≤ U α) (hβ : W ≤ U β) (hγ : W ≤ U γ) : sec S (N α) hα →+ sec S (N γ) hγ :=
  (secOfGlue g β γ hβ hγ).comp (secOfGlue g α β hα hβ)

/-- Z3.l′: `cocA` is linear. -/
private theorem cocA_smul {N : ∀ α, Mod ((ringOf S).over (U α))}
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α β γ : ι) {W : Opens X}
    (hα : W ≤ U α) (hβ : W ≤ U β) (hγ : W ≤ U γ) (r : S.obj.obj (op W)) (y : sec S (N α) hα) :
    cocA g α β γ hα hβ hγ (toSec S hα r • y) = toSec S hγ r • cocA g α β γ hα hβ hγ y :=
  (congrArg (secOfGlue g β γ hβ hγ) (secOfGlue_smul g α β hα hβ r y)).trans
    (secOfGlue_smul g β γ hβ hγ r _)

/-- Z3.l′: `cocA` is natural. -/
private theorem cocA_res {N : ∀ α, Mod ((ringOf S).over (U α))}
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α β γ : ι) {W W' : Opens X}
    (hα : W ≤ U α) (hβ : W ≤ U β) (hγ : W ≤ U γ) (h' : W' ≤ W) (y : sec S (N α) hα) :
    cocA g α β γ (h'.trans hα) (h'.trans hβ) (h'.trans hγ) (secRes S (N α) hα h' y) =
      secRes S (N γ) hγ h' (cocA g α β γ hα hβ hγ y) :=
  (congrArg (secOfGlue g β γ (h'.trans hβ) (h'.trans hγ)) (secOfGlue_res g α β hα hβ h' y)).trans
    (secOfGlue_res g β γ hβ hγ h' _)

/-- Z3.l′: the map `x ↦ c · φ′_αγ x` on sections over `W`. -/
private def cocB {N : ∀ α, Mod ((ringOf S).over (U α))}
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α γ : ι) {W : Opens X}
    (hα : W ≤ U α) (hγ : W ≤ U γ) (c : S.obj.obj (op W)) : sec S (N α) hα →+ sec S (N γ) hγ :=
  (scaleHom (N γ) hγ c).comp (secOfGlue g α γ hα hγ)

/-- Z3.l′: `cocB` is linear. -/
private theorem cocB_smul {N : ∀ α, Mod ((ringOf S).over (U α))}
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α γ : ι) {W : Opens X}
    (hα : W ≤ U α) (hγ : W ≤ U γ) (c r : S.obj.obj (op W)) (y : sec S (N α) hα) :
    cocB g α γ hα hγ c (toSec S hα r • y) = toSec S hγ r • cocB g α γ hα hγ c y := by
  change toSec S hγ c • secOfGlue g α γ hα hγ (toSec S hα r • y) = _
  rw [secOfGlue_smul]
  exact toSec_smul_comm' _ _ _ _ _

/-- Z3.l′: `cocB` is natural (the scalar is restricted). -/
private theorem cocB_res {N : ∀ α, Mod ((ringOf S).over (U α))}
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α γ : ι) {W W' : Opens X}
    (hα : W ≤ U α) (hγ : W ≤ U γ) (h' : W' ≤ W) (c : S.obj.obj (op W)) (y : sec S (N α) hα) :
    cocB g α γ (h'.trans hα) (h'.trans hγ) ((S.obj.map (homOfLE h').op).hom c)
        (secRes S (N α) hα h' y) =
      secRes S (N γ) hγ h' (cocB g α γ hα hγ c y) := by
  change toSec S (h'.trans hγ) ((S.obj.map (homOfLE h').op).hom c) •
      secOfGlue g α γ (h'.trans hα) (h'.trans hγ) (secRes S (N α) hα h' y) =
    secRes S (N γ) hγ h' (toSec S hγ c • secOfGlue g α γ hα hγ y)
  rw [secOfGlue_res, secRes_smul]

/-- **Z3.l′ (C.7′ (c)).** The cocycle of `S ⊗ M`: `φ′_βγ φ′_αβ = ψ(ȟ_αβγ)·φ′_αγ` on every
`W ≤ U_α ∩ U_β ∩ U_γ` (on `η(m)` both sides are `η(ȟ_αβγ·φ_αγ m)`; `sec_eq_of_bcUnit`). -/
theorem bcφ_cocycle (M : TwMod R U ch) (α β γ : ι) {W : Opens X} (hα : W ≤ U α)
    (hβ : W ≤ U β) (hγ : W ≤ U γ) (x : sec S ((sheafBC (overHom ψ (U α))).obj (M.M α)) hα) :
    secOfGlue (M.bcGlue ψ) β γ hβ hγ (secOfGlue (M.bcGlue ψ) α β hα hβ x) =
      toSec S hγ (unitRes S (le_inf (le_inf hα hβ) hγ) (chMap ψ ch α β γ) : S.obj.obj (op W)) •
        secOfGlue (M.bcGlue ψ) α γ hα hγ x := by
  refine sec_eq_of_bcUnit ψ hα hγ
    (fun {W'} hW' => cocA (M.bcGlue ψ) α β γ (hW'.trans hα) (hW'.trans hβ) (hW'.trans hγ))
    (fun {W'} hW' => cocB (M.bcGlue ψ) α γ (hW'.trans hα) (hW'.trans hγ)
      (unitRes S (le_inf (le_inf (hW'.trans hα) (hW'.trans hβ)) (hW'.trans hγ))
        (chMap ψ ch α β γ) : S.obj.obj (op W')))
    (fun hW' r y => cocA_smul (M.bcGlue ψ) α β γ (hW'.trans hα) (hW'.trans hβ) (hW'.trans hγ) r y)
    (fun hW' h' y => cocA_res (M.bcGlue ψ) α β γ (hW'.trans hα) (hW'.trans hβ) (hW'.trans hγ)
      h' y)
    (fun hW' r y => cocB_smul (M.bcGlue ψ) α γ (hW'.trans hα) (hW'.trans hγ) _ r y)
    (fun hW' h' y => ?_)
    (fun hW' m => ?_) x
  · have e := cocB_res (M.bcGlue ψ) α γ (hW'.trans hα) (hW'.trans hγ) h'
      (unitRes S (le_inf (le_inf (hW'.trans hα) (hW'.trans hβ)) (hW'.trans hγ))
        (chMap ψ ch α β γ) : S.obj.obj (op _)) y
    rw [unitRes_res] at e
    exact e
  · have hα' := hW'.trans hα
    have hβ' := hW'.trans hβ
    have hγ' := hW'.trans hγ
    have e1 : cocA (M.bcGlue ψ) α β γ hα' hβ' hγ' (bcUnit ψ (M.M α) hα' m) =
        bcUnit ψ (M.M γ) hγ' (M.φ β γ hβ' hγ' (M.φ α β hα' hβ' m)) := by
      change secOfGlue (M.bcGlue ψ) β γ hβ' hγ' (secOfGlue (M.bcGlue ψ) α β hα' hβ'
        (bcUnit ψ (M.M α) hα' m)) = _
      rw [bcφ_bcUnit, bcφ_bcUnit]
    have e2 : cocB (M.bcGlue ψ) α γ hα' hγ'
        (unitRes S (le_inf (le_inf hα' hβ') hγ') (chMap ψ ch α β γ) : S.obj.obj (op _))
        (bcUnit ψ (M.M α) hα' m) =
        bcUnit ψ (M.M γ) hγ' (toSec R hγ'
          (unitRes R (le_inf (le_inf hα' hβ') hγ') (ch α β γ) : R.obj.obj (op _)) •
            M.φ α γ hα' hγ' m) := by
      rw [bcUnit_smul, psi_unitRes ψ (le_inf (le_inf hα' hβ') hγ') (ch α β γ)]
      change toSec S hγ' _ • secOfGlue (M.bcGlue ψ) α γ hα' hγ' (bcUnit ψ (M.M α) hα' m) = _
      rw [bcφ_bcUnit]
      rfl
    rw [e1, e2, M.cocycle]

/-- **Z3.l′ (C.7′ (c)).** [Căldăraru, §1.2]. The base change `S ⊗ M` of a `ȟ`-twisted
`R`-module: components `S|U_α ⊗ M_α` (S8.a `sheafBC` on `Over U_α`), gluing maps the sections of
`TwMod.bcGlue`, cocycle `ψ(ȟ)`. -/
def TwMod.bcObj (M : TwMod R U ch) : TwMod S U (chMap ψ ch) where
  M α := (sheafBC (overHom ψ (U α))).obj (M.M α)
  φ := secOfGlue (M.bcGlue ψ)
  φ_smul := secOfGlue_smul (M.bcGlue ψ)
  φ_res := secOfGlue_res (M.bcGlue ψ)
  φ_self := bcφ_self ψ M
  cocycle := bcφ_cocycle ψ M

/-- Z3.l′: the gluing maps of `S ⊗ M` (rfl). -/
theorem TwMod.bcObj_φ (M : TwMod R U ch) (α β : ι) {W : Opens X} (hα : W ≤ U α)
    (hβ : W ≤ U β) (x : sec S ((sheafBC (overHom ψ (U α))).obj (M.M α)) hα) :
    (M.bcObj ψ).φ α β hα hβ x = secOfGlue (M.bcGlue ψ) α β hα hβ x := rfl

/-- Z3.l′: the section maps of a morphism of sheaves of modules, as an additive map. -/
private def appHom {V : Opens X} {P Q : Mod ((ringOf S).over V)} (g : P ⟶ Q) {W : Opens X}
    (h : W ≤ V) : sec S P h →+ sec S Q h :=
  (g.val.app (ovr h)).hom.toAddMonoidHom

/-- Z3.l′: `ḡ_αβ ∘ F_α` for glue families `ḡ` and component morphisms `F`. -/
private def bmA {P Q : ∀ α, Mod ((ringOf S).over (U α))}
    (gQ : ∀ α β, (resL α β).obj (Q α) ⟶ (resR α β).obj (Q β)) (F : ∀ α, P α ⟶ Q α)
    (α β : ι) {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) : sec S (P α) hα →+ sec S (Q β) hβ :=
  (secOfGlue gQ α β hα hβ).comp (appHom (F α) hα)

/-- Z3.l′: `F_β ∘ g_αβ` for glue families `g` and component morphisms `F`. -/
private def bmB {P Q : ∀ α, Mod ((ringOf S).over (U α))}
    (gP : ∀ α β, (resL α β).obj (P α) ⟶ (resR α β).obj (P β)) (F : ∀ α, P α ⟶ Q α)
    (α β : ι) {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) : sec S (P α) hα →+ sec S (Q β) hβ :=
  (appHom (F β) hβ).comp (secOfGlue gP α β hα hβ)

/-- Z3.l′: `bmA` is linear. -/
private theorem bmA_smul {P Q : ∀ α, Mod ((ringOf S).over (U α))}
    (gQ : ∀ α β, (resL α β).obj (Q α) ⟶ (resR α β).obj (Q β)) (F : ∀ α, P α ⟶ Q α)
    (α β : ι) {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (r : S.obj.obj (op W))
    (y : sec S (P α) hα) :
    bmA gQ F α β hα hβ (toSec S hα r • y) = toSec S hβ r • bmA gQ F α β hα hβ y :=
  (congrArg (secOfGlue gQ α β hα hβ) (app_smul (F α) hα r y)).trans
    (secOfGlue_smul gQ α β hα hβ r _)

/-- Z3.l′: `bmA` is natural. -/
private theorem bmA_res {P Q : ∀ α, Mod ((ringOf S).over (U α))}
    (gQ : ∀ α β, (resL α β).obj (Q α) ⟶ (resR α β).obj (Q β)) (F : ∀ α, P α ⟶ Q α)
    (α β : ι) {W W' : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (h' : W' ≤ W)
    (y : sec S (P α) hα) :
    bmA gQ F α β (h'.trans hα) (h'.trans hβ) (secRes S (P α) hα h' y) =
      secRes S (Q β) hβ h' (bmA gQ F α β hα hβ y) :=
  (congrArg (secOfGlue gQ α β (h'.trans hα) (h'.trans hβ)) (app_secRes (F α) hα h' y)).trans
    (secOfGlue_res gQ α β hα hβ h' _)

/-- Z3.l′: `bmB` is linear. -/
private theorem bmB_smul {P Q : ∀ α, Mod ((ringOf S).over (U α))}
    (gP : ∀ α β, (resL α β).obj (P α) ⟶ (resR α β).obj (P β)) (F : ∀ α, P α ⟶ Q α)
    (α β : ι) {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (r : S.obj.obj (op W))
    (y : sec S (P α) hα) :
    bmB gP F α β hα hβ (toSec S hα r • y) = toSec S hβ r • bmB gP F α β hα hβ y :=
  (congrArg (appHom (F β) hβ) (secOfGlue_smul gP α β hα hβ r y)).trans
    (app_smul (F β) hβ r _)

/-- Z3.l′: `bmB` is natural. -/
private theorem bmB_res {P Q : ∀ α, Mod ((ringOf S).over (U α))}
    (gP : ∀ α β, (resL α β).obj (P α) ⟶ (resR α β).obj (P β)) (F : ∀ α, P α ⟶ Q α)
    (α β : ι) {W W' : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (h' : W' ≤ W)
    (y : sec S (P α) hα) :
    bmB gP F α β (h'.trans hα) (h'.trans hβ) (secRes S (P α) hα h' y) =
      secRes S (Q β) hβ h' (bmB gP F α β hα hβ y) :=
  (congrArg (appHom (F β) (h'.trans hβ)) (secOfGlue_res gP α β hα hβ h' y)).trans
    (app_secRes (F β) hβ h' _)

/-- **Z3.l′ (C.7′ (c)).** `S ⊗ f` commutes with the gluing maps of `S ⊗ M` and `S ⊗ N` (by
uniqueness on `η`). -/
theorem bcMap_comm {M N : TwMod R U ch} (f : M ⟶ N) (α β : ι) {W : Opens X} (hα : W ≤ U α)
    (hβ : W ≤ U β) (x : sec S ((sheafBC (overHom ψ (U α))).obj (M.M α)) hα) :
    (N.bcObj ψ).φ α β hα hβ ((((sheafBC (overHom ψ (U α))).map (f.f α)).val.app (ovr hα)).hom x) =
      (((sheafBC (overHom ψ (U β))).map (f.f β)).val.app (ovr hβ)).hom
        ((M.bcObj ψ).φ α β hα hβ x) := by
  refine sec_eq_of_bcUnit ψ hα hβ
    (fun {W'} hW' => bmA (N.bcGlue ψ) (fun α => (sheafBC (overHom ψ (U α))).map (f.f α)) α β
      (hW'.trans hα) (hW'.trans hβ))
    (fun {W'} hW' => bmB (M.bcGlue ψ) (fun α => (sheafBC (overHom ψ (U α))).map (f.f α)) α β
      (hW'.trans hα) (hW'.trans hβ))
    (fun hW' r y => bmA_smul (N.bcGlue ψ) (fun α => (sheafBC (overHom ψ (U α))).map (f.f α))
      α β (hW'.trans hα) (hW'.trans hβ) r y)
    (fun hW' h' y => bmA_res (N.bcGlue ψ) (fun α => (sheafBC (overHom ψ (U α))).map (f.f α))
      α β (hW'.trans hα) (hW'.trans hβ) h' y)
    (fun hW' r y => bmB_smul (M.bcGlue ψ) (fun α => (sheafBC (overHom ψ (U α))).map (f.f α))
      α β (hW'.trans hα) (hW'.trans hβ) r y)
    (fun hW' h' y => bmB_res (M.bcGlue ψ) (fun α => (sheafBC (overHom ψ (U α))).map (f.f α))
      α β (hW'.trans hα) (hW'.trans hβ) h' y)
    (fun hW' m => ?_) x
  change secOfGlue (N.bcGlue ψ) α β _ _ ((((sheafBC (overHom ψ (U α))).map (f.f α)).val.app
      (ovr _)).hom (bcUnit ψ (M.M α) _ m)) =
    (((sheafBC (overHom ψ (U β))).map (f.f β)).val.app (ovr _)).hom
      (secOfGlue (M.bcGlue ψ) α β _ _ (bcUnit ψ (M.M α) _ m))
  rw [bcUnit_map, bcφ_bcUnit, bcφ_bcUnit, bcUnit_map]
  exact congrArg _ (f.comm α β _ _ m)

/-- **Z3.l′ (C.7′ (c)).** Base change of a morphism of twisted sheaves: `S ⊗ f_α` componentwise. -/
def TwMod.bcMap {M N : TwMod R U ch} (f : M ⟶ N) : M.bcObj ψ ⟶ N.bcObj ψ :=
  ⟨fun α => (sheafBC (overHom ψ (U α))).map (f.f α), bcMap_comm ψ f⟩

variable (U ch) in
/-- **Z3.l′ (C.7′ (c)).** [Căldăraru, §1.2]. Base change of twisted sheaves along `ψ : R ⟶ S`:
`TwMod R U ȟ ⥤ TwMod S U ψ(ȟ)`, componentwise S8.a's `sheafBC` on `Over U_α`. -/
def twBC : TwMod R U ch ⥤ TwMod S U (chMap ψ ch) where
  obj M := M.bcObj ψ
  map f := TwMod.bcMap ψ f
  map_id M := TwMod.hom_ext fun α => (sheafBC (overHom ψ (U α))).map_id (M.M α)
  map_comp f g := TwMod.hom_ext fun α => (sheafBC (overHom ψ (U α))).map_comp (f.f α) (g.f α)

/-- Z3.l′: components of `twBC ψ M` are `S ⊗ M_α` (rfl). -/
theorem twBC_obj_M (M : TwMod R U ch) (α : ι) :
    ((twBC ψ U ch).obj M).M α = (sheafBC (overHom ψ (U α))).obj (M.M α) := rfl

/-- Z3.l′: components of `twBC ψ f` are `S ⊗ f_α` (rfl). -/
theorem twBC_map_f {M N : TwMod R U ch} (f : M ⟶ N) (α : ι) :
    ((twBC ψ U ch).map f).f α = (sheafBC (overHom ψ (U α))).map (f.f α) := rfl

/-- **Z3.l′.** Base change of twisted sheaves is additive (componentwise `sheafBC` is). -/
instance twBC_additive : (twBC ψ U ch).Additive where
  map_add := fun {M N} f g =>
    TwMod.hom_ext fun α => Functor.map_add (sheafBC (overHom ψ (U α)))

end Cohesive
