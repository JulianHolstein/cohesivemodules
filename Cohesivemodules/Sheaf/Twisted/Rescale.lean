import Cohesivemodules.Sheaf.Twisted.SecRes
import Cohesivemodules.Sheaf.Twisted.Basic

set_option linter.style.header false

/-!
# Z3.k: rescaling the gluing maps of twisted sheaves

Blueprint item Z3.k (`blueprint/blueprint-tw.md` §3 C.7 (f)). For units `g_αβ ∈ R(U_α ∩ U_β)ˣ`
with `g_αα = 1` and two families `ȟ`, `ȟ'` with `ȟ'_αβγ g_αγ = g_βγ g_αβ ȟ_αβγ` (on every
`W ≤ U_α ∩ U_β ∩ U_γ`), replacing the gluing maps `φ_αβ` by `g_αβ φ_αβ` is an equivalence
`TwMod R U ȟ ≌ TwMod R U ȟ'`, the identity on components and on morphisms. In the notation of
blueprint-tw, `ȟ' = ȟ · ďg` with `(ďg)_αβγ = g_βγ g_αβ g_αγ⁻¹`, the convention of the twist data
(`ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹`). With `g = 1` it is transport along `ȟ = ȟ'`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X}

/-- **Z3.k (f).** `ȟ' = ȟ · ďg`: `g_αα = 1`, and `ȟ'_αβγ g_αγ = g_βγ g_αβ ȟ_αβγ` restricted to
every open `W` contained in `U_α`, `U_β`, `U_γ`. -/
def IsRescale (ch ch' : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ)
    (g : ∀ α β, (R.obj.obj (op (U α ⊓ U β)))ˣ) : Prop :=
  (∀ α, g α α = 1) ∧
    ∀ α β γ {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (hγ : W ≤ U γ),
      unitRes R (le_inf (le_inf hα hβ) hγ) (ch' α β γ) * unitRes R (le_inf hα hγ) (g α γ) =
        unitRes R (le_inf hβ hγ) (g β γ) * unitRes R (le_inf hα hβ) (g α β) *
          unitRes R (le_inf (le_inf hα hβ) hγ) (ch α β γ)

variable {ch ch' : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}
  {g : ∀ α β, (R.obj.obj (op (U α ⊓ U β)))ˣ}

/-- Z3.k: group algebra for `IsRescale.symm`. -/
private theorem symm_aux {G : Type*} [CommGroup G] (c0 a b c c' : G) (e : c' * a = b * c * c0) :
    c0 * a⁻¹ = b⁻¹ * c⁻¹ * c' := by
  have e' : c' = b * c * c0 * a⁻¹ := eq_mul_inv_of_mul_eq e
  rw [e']
  have e2 : b⁻¹ * c⁻¹ = (b * c)⁻¹ := by rw [mul_inv_rev, mul_comm]
  rw [e2, mul_assoc (b * c) c0 a⁻¹, inv_mul_cancel_left]

/-- **Z3.k (f).** Rescaling is symmetric: `ȟ = ȟ' · ď(g⁻¹)`. -/
theorem IsRescale.symm (h : IsRescale ch ch' g) : IsRescale ch' ch (fun α β => (g α β)⁻¹) := by
  refine ⟨fun α => by simp only [h.1 α, inv_one], ?_⟩
  intro α β γ W hα hβ hγ
  have e := h.2 α β γ hα hβ hγ
  simp only [map_inv]
  exact symm_aux _ _ _ _ _ e

/-- **Z3.k (f).** Transport along an equality of families is rescaling by `g = 1`. -/
theorem isRescale_of_eq (h : ch = ch') : IsRescale ch ch' (fun _ _ => 1) := by
  subst h
  refine ⟨fun _ => rfl, ?_⟩
  intro α β γ W hα hβ hγ
  simp only [map_one, one_mul, mul_one]

/-- Z3.k: scalars of `R(W)` commute on sections over `W ≤ V`. -/
private theorem toSec_smul_comm' {V : Opens X} (N : Mod ((ringOf R).over V)) {W : Opens X}
    (h : W ≤ V) (a b : R.obj.obj (op W)) (y : sec R N h) :
    toSec R h a • toSec R h b • y = toSec R h b • toSec R h a • y := by
  rw [← mul_smul, ← mul_smul]
  exact congrArg (· • y) (mul_comm a b)

/-- **Z3.k (f).** The twisted sheaf with gluing maps `g_αβ φ_αβ` (same components). -/
def TwMod.rescaleObj (h : IsRescale ch ch' g) (M : TwMod R U ch) : TwMod R U ch' where
  M := M.M
  φ α β {W} hα hβ := (DistribSMul.toAddMonoidHom _
      (toSec R hβ (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)))).comp (M.φ α β hα hβ)
  φ_smul := by
    intro α β W hα hβ r x
    change toSec R hβ (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)) •
      M.φ α β hα hβ (toSec R hα r • x) = toSec R hβ r • (toSec R hβ
        (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)) • M.φ α β hα hβ x)
    rw [M.φ_smul]
    exact toSec_smul_comm' _ _ _ _ _
  φ_res := by
    intro α β W W' hα hβ h' x
    change toSec R (h'.trans hβ)
      (unitRes R (le_inf (h'.trans hα) (h'.trans hβ)) (g α β) : R.obj.obj (op W')) •
        M.φ α β (h'.trans hα) (h'.trans hβ) (secRes R (M.M α) hα h' x) =
      secRes R (M.M β) hβ h'
        (toSec R hβ (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)) • M.φ α β hα hβ x)
    rw [M.φ_res, secRes_smul, unitRes_res]
  φ_self := by
    intro α W hα x
    change toSec R hα (unitRes R (le_inf hα hα) (g α α) : R.obj.obj (op W)) •
      M.φ α α hα hα x = x
    rw [h.1 α, map_one, Units.val_one, M.φ_self]
    exact one_smul _ _
  cocycle := by
    intro α β γ W hα hβ hγ x
    change toSec R hγ _ • M.φ β γ hβ hγ (toSec R hβ _ • M.φ α β hα hβ x) =
      toSec R hγ _ • (toSec R hγ _ • M.φ α γ hα hγ x)
    rw [M.φ_smul, M.cocycle, ← mul_smul, ← mul_smul, ← mul_smul]
    have e := congrArg Units.val (h.2 α β γ hα hβ hγ)
    simp only [Units.val_mul] at e
    exact congrArg (fun a : R.obj.obj (op W) => toSec R hγ a • M.φ α γ hα hγ x) e.symm

theorem TwMod.rescaleObj_M (h : IsRescale ch ch' g) (M : TwMod R U ch) :
    (TwMod.rescaleObj h M).M = M.M :=
  rfl

theorem TwMod.rescaleObj_φ (h : IsRescale ch ch' g) (M : TwMod R U ch) (α β : ι) {W : Opens X}
    (hα : W ≤ U α) (hβ : W ≤ U β) (x : sec R (M.M α) hα) :
    (TwMod.rescaleObj h M).φ α β hα hβ x =
      toSec R hβ (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)) • M.φ α β hα hβ x :=
  rfl

/-- **Z3.k (f).** Rescaling as a functor, the identity on components of morphisms. -/
def rescaleFunctor (h : IsRescale ch ch' g) : TwMod R U ch ⥤ TwMod R U ch' where
  obj := TwMod.rescaleObj h
  map {M N} f := ⟨f.f, by
    intro α β W hα hβ (x : sec R (M.M α) hα)
    change toSec R hβ (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)) •
      N.φ α β hα hβ (((f.f α).val.app (ovr hα)).hom x) =
      ((f.f β).val.app (ovr hβ)).hom (toSec R hβ
        (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)) • M.φ α β hα hβ x)
    rw [f.comm, app_smul]⟩
  map_id M := rfl
  map_comp f g := rfl

theorem rescaleFunctor_map_f (h : IsRescale ch ch' g) {M N : TwMod R U ch} (f : M ⟶ N) :
    ((rescaleFunctor h).map f).f = f.f :=
  rfl

/-- Z3.k: `g⁻¹ (g y) = y` for a unit `g` of `R(W)` acting on sections. -/
private theorem inv_smul_smul_sec {V W : Opens X} (N : Mod ((ringOf R).over V)) (hW : W ≤ V)
    (u : (R.obj.obj (op W))ˣ) (y : sec R N hW) :
    toSec R hW ((u⁻¹ : (R.obj.obj (op W))ˣ) : R.obj.obj (op W)) • toSec R hW (u : R.obj.obj (op W))
      • y = y := by
  rw [← mul_smul]
  exact (congrArg (fun a : R.obj.obj (op W) => toSec R hW a • y) (Units.inv_mul u)).trans
    (one_smul _ _)

/-- Z3.k: `g (g⁻¹ y) = y` for a unit `g` of `R(W)` acting on sections. -/
private theorem smul_inv_smul_sec {V W : Opens X} (N : Mod ((ringOf R).over V)) (hW : W ≤ V)
    (u : (R.obj.obj (op W))ˣ) (y : sec R N hW) :
    toSec R hW (u : R.obj.obj (op W)) • toSec R hW ((u⁻¹ : (R.obj.obj (op W))ˣ) :
      R.obj.obj (op W)) • y = y := by
  rw [← mul_smul]
  exact (congrArg (fun a : R.obj.obj (op W) => toSec R hW a • y) (Units.mul_inv u)).trans
    (one_smul _ _)

/-- Z3.k: rescaling by `g` and then by `g⁻¹` does not change the gluing maps. -/
private theorem rescale_rescale_φ (h : IsRescale ch ch' g) (M : TwMod R U ch) (α β : ι)
    {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (x : sec R (M.M α) hα) :
    (TwMod.rescaleObj h.symm (TwMod.rescaleObj h M)).φ α β hα hβ x = M.φ α β hα hβ x := by
  change toSec R hβ (unitRes R (le_inf hα hβ) (g α β)⁻¹ : R.obj.obj (op W)) •
    toSec R hβ (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)) • M.φ α β hα hβ x = _
  rw [map_inv]
  exact inv_smul_smul_sec _ _ _ _

/-- Z3.k: rescaling by `g⁻¹` and then by `g` does not change the gluing maps. -/
private theorem rescale_rescale_φ' (h : IsRescale ch ch' g) (N : TwMod R U ch') (α β : ι)
    {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (x : sec R (N.M α) hα) :
    (TwMod.rescaleObj h (TwMod.rescaleObj h.symm N)).φ α β hα hβ x = N.φ α β hα hβ x := by
  change toSec R hβ (unitRes R (le_inf hα hβ) (g α β) : R.obj.obj (op W)) •
    toSec R hβ (unitRes R (le_inf hα hβ) (g α β)⁻¹ : R.obj.obj (op W)) • N.φ α β hα hβ x = _
  rw [map_inv]
  exact smul_inv_smul_sec _ _ _ _

/-- Z3.k: the unit isomorphism `M ≅ rescale g⁻¹ (rescale g M)`, identity on components. -/
private def rescaleUnitObj (h : IsRescale ch ch' g) (M : TwMod R U ch) :
    M ≅ TwMod.rescaleObj h.symm (TwMod.rescaleObj h M) where
  hom := ⟨fun α => 𝟙 (M.M α), fun α β _ hα hβ x =>
    (rescale_rescale_φ h M α β hα hβ x)⟩
  inv := ⟨fun α => 𝟙 (M.M α), fun α β _ hα hβ x =>
    (rescale_rescale_φ h M α β hα hβ x).symm⟩
  hom_inv_id := TwMod.hom_ext fun _ => Category.id_comp _
  inv_hom_id := TwMod.hom_ext fun _ => Category.id_comp _

/-- Z3.k: the counit isomorphism `rescale g (rescale g⁻¹ N) ≅ N`, identity on components. -/
private def rescaleCounitObj (h : IsRescale ch ch' g) (N : TwMod R U ch') :
    TwMod.rescaleObj h (TwMod.rescaleObj h.symm N) ≅ N where
  hom := ⟨fun α => 𝟙 (N.M α), fun α β _ hα hβ x =>
    (rescale_rescale_φ' h N α β hα hβ x).symm⟩
  inv := ⟨fun α => 𝟙 (N.M α), fun α β _ hα hβ x =>
    (rescale_rescale_φ' h N α β hα hβ x)⟩
  hom_inv_id := TwMod.hom_ext fun _ => Category.id_comp _
  inv_hom_id := TwMod.hom_ext fun _ => Category.id_comp _

/-- **Z3.k (f).** [Căldăraru, Lemma 1.2.6]. Rescaling the gluing maps by `g` is an equivalence
`TwMod R U ȟ ≌ TwMod R U ȟ'` for `ȟ' = ȟ · ďg`, with inverse rescaling by `g⁻¹`; unit and counit
have identity components. -/
def rescale (h : IsRescale ch ch' g) : TwMod R U ch ≌ TwMod R U ch' :=
  CategoryTheory.Equivalence.mk (rescaleFunctor h) (rescaleFunctor h.symm)
    (NatIso.ofComponents (fun M => rescaleUnitObj h M) (fun {_ _} _ =>
      TwMod.hom_ext fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))
    (NatIso.ofComponents (fun N => rescaleCounitObj h N) (fun {_ _} _ =>
      TwMod.hom_ext fun _ => (Category.comp_id _).trans (Category.id_comp _).symm))

theorem rescale_functor (h : IsRescale ch ch' g) : (rescale h).functor = rescaleFunctor h :=
  rfl

theorem rescale_inverse (h : IsRescale ch ch' g) :
    (rescale h).inverse = rescaleFunctor h.symm :=
  rfl

end Cohesive
