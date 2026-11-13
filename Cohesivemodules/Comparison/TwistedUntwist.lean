import Cohesivemodules.Sheaf.Twisted.BaseChange
import Cohesivemodules.Sheaf.Twisted.Rescale
import Cohesivemodules.Sheaf.Twisted.GlueEquiv
import Cohesivemodules.Comparison.ModelBC
import Cohesivemodules.Comparison.TwistDatumDef

set_option linter.style.header false

/-!
# Z3.t: untwisting a twisted complex after base change to `𝒜⁰` (blueprint-tw G′ (b))

Blueprint item Z3.t (`blueprint/blueprint-tw.md` §3 G′ (b), [A, Rem 7.2.4]). For pre-resolving
data `P` and a twist datum `T` over `P`, the units `u_αβ ∈ 𝒜⁰(U_αβ)ˣ` trivialize the cocycle
`ρ(ȟ)` (B.5: `ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹`), so a `ȟ`-twisted `O`-module becomes, after base change
to `𝒜⁰` (Z3.l′ `twBC`), an untwisted twisted `𝒜⁰`-module, which glues to a sheaf on `X`:
* `ρSheafT`: `ρ` with source spelled `P.toSheafData.O` (the ring of twisted sheaves);
* `uInv P T`: the units `u_αβ⁻¹` as sections of the sheaf `𝒜⁰`;
* `isRescale_untwist`: `ρ(ȟ)` rescaled by `u⁻¹` is trivial;
* `untwist P T : TwMod O U ȟ ⥤ Mod 𝒜⁰`, `M ↦ glue(rescale_{u⁻¹}(𝒜⁰ ⊗ M))`, additive;
* `untwistRestrIso`: `(untwist M)|U_α ≅ 𝒜⁰|U_α ⊗ M_α` (C.7 (c)), natural in `M`;
* `untwistComp`, `untwist_compat`: on `W ≤ U_α ∩ U_β`, the components of a section satisfy
  `s_β = u_αβ⁻¹ · φ^B_αβ(s_α)` (`φ^B` the gluing of `twBC`); `untwist_ext`: sections are
  determined by their components.

## Deviations
* None beyond those of `TwMod` (section-level gluing, D4) and of `twBC` (Z3.l′).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] (P : PreResolvingData X) {h : P.D.A ⊤}
  (T : TwistDatum P.toSheafData h)

/-- Z3.t: `ρ : O ⟶ 𝒜⁰` with source spelled `P.toSheafData.O`, the ring of twisted sheaves for twist
data over `P` (one spelling of the twisted ring, Z3.n lesson); definitionally `P.ρSheaf`. -/
abbrev PreResolvingData.ρSheafT : P.toSheafData.O ⟶ P.A0 := P.ρSheaf

/-- **Z3.t (G′ (b)).** The units `u_αβ⁻¹ ∈ 𝒜⁰(U_α ∩ U_β)ˣ` of the twist datum, as units of the
ring of sections of the sheaf `𝒜⁰` (the same ring, P9). -/
def uInv (α β : T.ι) : (P.A0.obj.obj (op (T.U α ⊓ T.U β)))ˣ := (T.u α β)⁻¹

/-- Z3.t: composition of restrictions on degree `0` elements. -/
private theorem res_f0_comp' {V W W' : Opens X} (h₁ : W ≤ V) (h₂ : W' ≤ W)
    (a : ↥(P.toSheafData.D.𝒜 V 0)) :
    (P.toSheafData.D.res h₂).f0 ((P.toSheafData.D.res h₁).f0 a) =
      (P.toSheafData.D.res (h₂.trans h₁)).f0 a :=
  Subtype.ext (P.toSheafData.D.res_comp _ _ _)

/-- Z3.t: unit algebra for `isRescale_untwist`. -/
private theorem units_aux {R : Type*} [CommRing R] (a b c d : Rˣ) (h : (d : R) = a * b * c⁻¹) :
    1 * c⁻¹ = a⁻¹ * b⁻¹ * d := by
  have e : d = a * b * c⁻¹ := Units.ext (by simpa using h)
  rw [e, one_mul, ← mul_inv_rev, mul_comm b a, inv_mul_cancel_left]

/-- Z3.t: `ρ(ȟ)|W = u_βγ u_αβ u_αγ⁻¹` on `W ≤ U_α, U_β, U_γ`, values in `𝒜⁰(W)`. -/
private theorem key_aux (α β γ : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (hγ : W ≤ T.U γ) :
    Units.val (unitRes P.A0 (le_inf (le_inf hα hβ) hγ) (chMap P.ρSheafT T.ch α β γ)) =
      Units.val (unitRes P.A0 (le_inf hβ hγ) (T.u β γ)) *
        Units.val (unitRes P.A0 (le_inf hα hβ) (T.u α β)) *
        Units.val (unitRes P.A0 (le_inf hα hγ) (T.u α γ)⁻¹) := by
  have h0 := congrArg (P.toSheafData.D.res (le_inf (le_inf hα hβ) hγ)).f0 (T.ρ_ch α β γ)
  rw [map_mul, map_mul, res_f0_comp', res_f0_comp', res_f0_comp'] at h0
  exact h0

/-- **Z3.t (G′ (b)).** [A, Rem 7.2.4]. The cocycle `ρ(ȟ)` of `𝒜⁰`-units is the coboundary of `u`:
rescaling by `u⁻¹` makes it trivial (`IsRescale ρ(ȟ) 1 u⁻¹`; from `T.ρ_ch`, `T.u_self`). -/
theorem isRescale_untwist :
    IsRescale (chMap P.ρSheafT T.ch) (fun _ _ _ => 1) (uInv P T) := by
  refine ⟨fun α => ?_, ?_⟩
  · simp only [uInv, T.u_self]
    exact inv_one
  · intro α β γ W hα hβ hγ
    have k := key_aux P T α β γ hα hβ hγ
    change unitRes P.A0 _ 1 * unitRes P.A0 _ (T.u α γ)⁻¹ =
      unitRes P.A0 _ (T.u β γ)⁻¹ * unitRes P.A0 _ (T.u α β)⁻¹ * unitRes P.A0 _ _
    simp only [map_one]
    refine units_aux (unitRes P.A0 (le_inf hβ hγ) (T.u β γ))
      (unitRes P.A0 (le_inf hα hβ) (T.u α β)) (unitRes P.A0 (le_inf hα hγ) (T.u α γ)) _ ?_
    exact k.trans (congrArg (fun z => _ * _ * Units.val z)
      (map_inv (unitRes P.A0 (le_inf hα hγ)) (T.u α γ)))

/-- **Z3.t (G′ (b)).** [A, Rem 7.2.4]. Untwisting after base change to `𝒜⁰`:
`M ↦ glue(rescale_{u⁻¹}(𝒜⁰ ⊗_O M))`, from `ȟ`-twisted `O`-modules to sheaves of `𝒜⁰`-modules
on `X` (Z3.l′ `twBC`, Z3.k `rescale`, `glue`). -/
def untwist : TwMod P.toSheafData.O T.U T.ch ⥤ Mod (ringOf P.A0) :=
  twBC P.ρSheafT T.U T.ch ⋙ (rescale (isRescale_untwist P T)).functor ⋙ glue P.A0 T.U

/-- Z3.t: `untwist` is additive (each of `twBC`, `rescale`, `glue` is). -/
instance untwist_additive : (untwist P T).Additive := by
  have h1 : (rescale (isRescale_untwist P T)).functor.Additive :=
    ⟨fun {M N} f g => TwMod.hom_ext fun α => rfl⟩
  have h2 : (glue P.A0 T.U).Additive :=
    ⟨fun {M N} f g => by
      apply SheafOfModules.Hom.ext
      apply PresheafOfModules.Hom.ext
      funext W
      apply ModuleCat.hom_ext
      refine DFunLike.ext _ _ fun s => ?_
      exact Subtype.ext (funext fun α => rfl)⟩
  unfold untwist
  infer_instance

/-- **Z3.t (G′ (b)).** `(untwist M)|U_α ≅ 𝒜⁰|U_α ⊗ M_α`: the restriction of the glued sheaf is the
component `α` (C.7 (c), `ofSheafGlueIso`); rescaling does not change components. -/
def untwistRestrIso (M : TwMod P.toSheafData.O T.U T.ch) (α : T.ι) :
    (restr (ringOf P.A0) (T.U α)).obj ((untwist P T).obj M) ≅
      (sheafBC (overHom P.ρSheafT (T.U α))).obj (M.M α) :=
  (TwMod.comp P.A0 T.U (fun _ _ _ => 1) α).mapIso
    (ofSheafGlueIso
      ((rescale (isRescale_untwist P T)).functor.obj ((twBC P.ρSheafT T.U T.ch).obj M)))

/-- Z3.t: naturality of `untwistRestrIso` in `M`. -/
theorem untwistRestrIso_hom_naturality {M N : TwMod P.toSheafData.O T.U T.ch} (f : M ⟶ N)
    (α : T.ι) :
    (restr (ringOf P.A0) (T.U α)).map ((untwist P T).map f) ≫ (untwistRestrIso P T N α).hom =
      (untwistRestrIso P T M α).hom ≫ (sheafBC (overHom P.ρSheafT (T.U α))).map (f.f α) :=
  congrArg (fun k => k.f α)
    (ofSheafGlueIso_hom_naturality
      ((rescale (isRescale_untwist P T)).functor.map ((twBC P.ρSheafT T.U T.ch).map f)))

/-- **Z3.t (G′ (b)).** The component `α` of a section of `untwist M` over `W ≤ U_α`. -/
def untwistComp (M : TwMod P.toSheafData.O T.U T.ch) (α : T.ι) {W : Opens X}
    (hα : W ≤ T.U α) :
    ((untwist P T).obj M).val.obj (op W) →+
      sec P.A0 ((sheafBC (overHom P.ρSheafT (T.U α))).obj (M.M α)) hα :=
  ((untwistRestrIso P T M α).hom.val.app (ovr hα)).hom.toAddMonoidHom

/-- **Z3.t (G′ (b)).** Compatibility of the components of a section of `untwist M` over
`W ≤ U_α ∩ U_β`: `s_β = u_αβ⁻¹ · φ^B_αβ(s_α)`, where `φ^B` is the gluing of `𝒜⁰ ⊗ M` (Z3.l′). -/
theorem untwist_compat (M : TwMod P.toSheafData.O T.U T.ch) (α β : T.ι) {W : Opens X}
    (hα : W ≤ T.U α) (hβ : W ≤ T.U β) (s : ((untwist P T).obj M).val.obj (op W)) :
    untwistComp P T M β hβ s =
      toSec P.A0 hβ (unitRes P.A0 (le_inf hα hβ) (uInv P T α β) : P.A0.obj.obj (op W)) •
        (M.bcObj P.ρSheafT).φ α β hα hβ (untwistComp P T M α hα s) :=
  (s.2 α β le_rfl hα hβ).symm

/-- Z3.t: the component `α` of a section restricted to `W ⊓ U_α` and then evaluated is the
component `α` of the section. -/
private theorem glue_restr_comp {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
    {ι : Type} {U : ι → Opens X} {N : TwMod R U (fun _ _ _ => 1)} {W : Opens X} (α : ι)
    (x : glueSub N W) :
    secRes R (N.M α) (inf_le_right : (W ⊓ U α) ⊓ U α ≤ U α)
      (le_inf le_rfl inf_le_right : W ⊓ U α ≤ (W ⊓ U α) ⊓ U α)
      ((glueRes N (inf_le_left : W ⊓ U α ≤ W) x).1 α) = x.1 α := by
  rw [glueRes_apply]
  exact (secRes_secRes (N.M α) (inf_le_right : W ⊓ U α ≤ U α)
    (inf_le_inf_right (U α) (inf_le_left : W ⊓ U α ≤ W)) (le_inf le_rfl inf_le_right)
    (x.1 α)).trans (secRes_id (N.M α) (inf_le_right : W ⊓ U α ≤ U α) le_rfl (x.1 α))

/-- **Z3.t (G′ (b)).** Sections of `untwist M` are determined by their components: two sections
over `W` whose restrictions to every `W ⊓ U_α` have equal components `α` are equal. -/
theorem untwist_ext (M : TwMod P.toSheafData.O T.U T.ch) {W : Opens X}
    (s t : ((untwist P T).obj M).val.obj (op W))
    (hst : ∀ α, untwistComp P T M α (inf_le_right : W ⊓ T.U α ≤ T.U α)
        ((((untwist P T).obj M).val.map (homOfLE (inf_le_left : W ⊓ T.U α ≤ W)).op).hom s) =
      untwistComp P T M α (inf_le_right : W ⊓ T.U α ≤ T.U α)
        ((((untwist P T).obj M).val.map (homOfLE (inf_le_left : W ⊓ T.U α ≤ W)).op).hom t)) :
    s = t := by
  refine Subtype.ext (funext fun α => ?_)
  have e := hst α
  have e1 := glue_restr_comp (R := P.A0) (U := T.U) (W := W) α
    (N := (rescale (isRescale_untwist P T)).functor.obj ((twBC P.ρSheafT T.U T.ch).obj M)) s
  have e2 := glue_restr_comp (R := P.A0) (U := T.U) (W := W) α
    (N := (rescale (isRescale_untwist P T)).functor.obj ((twBC P.ρSheafT T.U T.ch).obj M)) t
  exact e1.symm.trans (e.trans e2)

end Cohesive
