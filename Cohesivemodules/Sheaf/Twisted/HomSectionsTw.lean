import Cohesivemodules.Sheaf.Twisted.HomComplexTw
import Mathlib.Algebra.Category.ModuleCat.Products

set_option linter.style.header false

/-!
# Z3.r: global sections of `𝓗om^tw(K, L)` are cochains of twisted sheaves

Blueprint item Z3.r (`blueprint/blueprint-tw.md` §3 F′ (e)). For twisted sheaves `A, B`
(normalized `ȟ`), a global section of `glue(homTw A B)` is a family of morphisms
`s_α : A_α|(⊤ ⊓ U_α) ⟶ B_α|(⊤ ⊓ U_α)` compatible with conjugation, i.e. a morphism of twisted
sheaves `A ⟶ B` (`glueHomTwTopEquiv`). Hence, for complexes `K`, `L`:
* `twHomTopEquiv : Γ(𝓗om^tw(K, L)ⁿ) ≃+ Cochain K L n` (Mathlib's `HomComplex` of the preadditive
  category `TwMod R U ȟ`; evaluation preserves products, `ModuleCat.piIsoPi`);
* `twHomTopEquiv_d`: the differential is Mathlib's `δ`;
* `twHomTopEquiv_map₂`: `twHomMap₂ g` is composition with `g` (`Cochain.comp … (Cochain.ofHom g)`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite
open CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}
  (hch : ∀ α β, ch α β α = 1)

section One

variable (A B : TwMod R U ch)

/-- **Z3.r (F′ (e)).** A global section of `glue(homTw A B)` as a morphism of twisted sheaves:
component `α` is the morphism `A_α ⟶ B_α` with the sections of `s_α` over every `W ≤ U_α`
(`W ≤ ⊤ ⊓ U_α`); it commutes with the gluing maps by the compatibility of the family. -/
def glueTopHom (s : ((glue R U).obj (homTw hch A B)).val.obj (op ⊤)) : A ⟶ B where
  f α := homOfSec₀ (fun {W} hW => secApp (inf_le_right : (⊤ : Opens X) ⊓ U α ≤ U α)
      ((show glueSub (homTw hch A B) ⊤ from s).1 α) (le_inf le_top hW : W ≤ ⊤ ⊓ U α))
    (fun hW r x => secApp_smul _ _ _ r x) (fun hW h' x => secApp_res _ _ _ h' x)
  comm α β W hα hβ x := by
    have hs := (show glueSub (homTw hch A B) ⊤ from s).2 α β (le_top : W ≤ ⊤) hα hβ
    have h2 := congrArg (fun t => secApp hβ t le_rfl (A.φ α β hα hβ x))
      (show _ = _ from hs)
    simp only at h2
    have h3 := congrArg (B.φ α β hα hβ) (congrArg
      (secApp (inf_le_right : (⊤ : Opens X) ⊓ U α ≤ U α)
        ((show glueSub (homTw hch A B) ⊤ from s).1 α) (le_inf le_top hα : W ≤ ⊤ ⊓ U α))
      (TwMod.φ_symm hch A α β hα hβ x)).symm
    exact h3.trans h2

/-- **Z3.r (F′ (e)).** A morphism of twisted sheaves as a global section of `glue(homTw A B)`:
component `α` is `f_α` restricted to `⊤ ⊓ U_α` (`secHomOf`). -/
def homGlueTop (f : A ⟶ B) : ((glue R U).obj (homTw hch A B)).val.obj (op ⊤) :=
  (show glueSub (homTw hch A B) ⊤ from
    ⟨fun α => secHomOf (inf_le_right : (⊤ : Opens X) ⊓ U α ≤ U α)
        (fun {W'} h' => ((f.f α).val.app (ovr (h'.trans inf_le_right))).hom.toAddMonoidHom)
        (fun h' r x => by exact app_smul (f.f α) _ r x)
        (fun h' h'' x => by exact app_secRes (f.f α) _ h'' x),
      by
        refine mem_glueSub.2 ?_
        intro α β W' h hα hβ
        refine secHom_ext hβ fun h' x => ?_
        change B.φ α β _ _ (((f.f α).val.app _).hom (A.φ β α _ _ x)) = ((f.f β).val.app _).hom x
        rw [f.comm α β, TwMod.φ_symm hch A β α]⟩)

/-- **Z3.r (F′ (e)).** Global sections of `glue(homTw A B)` are the morphisms `A ⟶ B` of twisted
sheaves. -/
def glueHomTwTopEquiv : ((glue R U).obj (homTw hch A B)).val.obj (op ⊤) ≃+ (A ⟶ B) where
  toFun := glueTopHom hch A B
  invFun := homGlueTop hch A B
  left_inv s := by
    refine Subtype.ext (funext fun α => secHom_ext _ fun h' x => rfl)
  right_inv f := by
    refine TwMod.hom_ext fun α => ?_
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro Z
    ext m
    rfl
  map_add' s t := by
    refine TwMod.hom_ext fun α => ?_
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro Z
    ext m
    rfl

/-- Z3.r: `glueHomTwTopEquiv` on sections (rfl). -/
theorem glueHomTwTopEquiv_apply (s : ((glue R U).obj (homTw hch A B)).val.obj (op ⊤)) :
    glueHomTwTopEquiv hch A B s = glueTopHom hch A B s := rfl

/-- Z3.r: under `glueHomTwTopEquiv`, `glue (homTwPost g)` is post-composition with `g`. -/
theorem glueHomTwTopEquiv_post {B' : TwMod R U ch} (g : B ⟶ B')
    (s : ((glue R U).obj (homTw hch A B)).val.obj (op ⊤)) :
    glueHomTwTopEquiv hch A B' (((glue R U).map (homTwPost hch A g)).val.app (op ⊤) s) =
      glueHomTwTopEquiv hch A B s ≫ g := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext m
  rfl

/-- Z3.r: under `glueHomTwTopEquiv`, `glue (homTwPre f)` is pre-composition with `f`. -/
theorem glueHomTwTopEquiv_pre {A' : TwMod R U ch} (f : A' ⟶ A)
    (s : ((glue R U).obj (homTw hch A B)).val.obj (op ⊤)) :
    glueHomTwTopEquiv hch A' B (((glue R U).map (homTwPre hch f B)).val.app (op ⊤) s) =
      f ≫ glueHomTwTopEquiv hch A B s := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext m
  rfl

end One

variable (hU : ⨆ α, U α = ⊤) (K L : CochainComplex (TwMod R U ch) ℤ)

/-- **Z3.r (F′ (e)).** Global sections of `𝓗om^tw(K, L)ⁿ` are the degree-`n` cochains `K → L` of
twisted sheaves: evaluation at `⊤` preserves the product (`piComparison`, `ModuleCat.piIsoPi`),
then `glueHomTwTopEquiv` on each factor. -/
def twHomTopEquiv (n : ℤ) :
    ((twHomComplex hch K L hU).X n).val.obj (op ⊤) ≃+ Cochain K L n :=
  ((asIso (piComparison (SheafOfModules.evaluation.{0} (ringOf R) (op ⊤))
      fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))) ≪≫
    ModuleCat.piIsoPi _).toLinearEquiv.toAddEquiv.trans
    (AddEquiv.piCongrRight fun T : Triplet n ↦ glueHomTwTopEquiv hch (K.X T.p) (L.X T.q))

/-- Z3.r: the component of `twHomTopEquiv` at `p + n = q` is `glueHomTwTopEquiv` of the
`T`-factor. -/
theorem twHomTopEquiv_apply (n : ℤ) (s : ((twHomComplex hch K L hU).X n).val.obj (op ⊤))
    (T : Triplet n) :
    twHomTopEquiv hch hU K L n s T =
      glueHomTwTopEquiv hch (K.X T.p) (L.X T.q)
        (((Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T).val.app
          (op ⊤)).hom s) := by
  have h1 := congrArg (fun f ↦ ModuleCat.Hom.hom f
    (ModuleCat.Hom.hom (piComparison (SheafOfModules.evaluation.{0} (ringOf R) (op ⊤))
      fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) s))
    (ModuleCat.piIsoPi_hom_ker_subtype
      (fun T : Triplet n ↦ ((glue R U).obj (homTw hch (K.X T.p) (L.X T.q))).val.obj (op ⊤)) T)
  have h2 := congrArg (fun f ↦ ModuleCat.Hom.hom f s)
    (piComparison_comp_π (SheafOfModules.evaluation.{0} (ringOf R) (op ⊤))
      (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T)
  exact congrArg (glueHomTwTopEquiv hch (K.X T.p) (L.X T.q)) (h1.trans h2)

/-- Z3.r helper: sections of a sum of morphisms of sheaves of modules. -/
private lemma add_app_apply'' {A B : Mod (ringOf R)} (f g : A ⟶ B) (W : Opens X)
    (s : A.val.obj (op W)) :
    ((f + g).val.app (op W)).hom s = (f.val.app (op W)).hom s + (g.val.app (op W)).hom s :=
  rfl

/-- Z3.r helper: sections of a `ℤˣ`-multiple of a morphism of sheaves of modules. -/
private lemma units_smul_app_apply' {A B : Mod (ringOf R)} (z : ℤˣ) (f : A ⟶ B) (W : Opens X)
    (s : A.val.obj (op W)) :
    ((z • f).val.app (op W)).hom s = z • (f.val.app (op W)).hom s := by
  have h : (SheafOfModules.evaluation.{0} (ringOf R) (op W)).map ((z : ℤ) • f) =
      (z : ℤ) • (SheafOfModules.evaluation.{0} (ringOf R) (op W)).map f := Functor.map_zsmul _
  rw [Units.smul_def, Units.smul_def]
  exact congrArg (fun g : A.val.obj (op W) ⟶ B.val.obj (op W) ↦ g.hom s) h

/-- **Z3.r (F′ (e)).** Under `twHomTopEquiv`, the differential of `𝓗om^tw(K, L)` is Mathlib's
`δ`. -/
theorem twHomTopEquiv_d (n : ℤ) (s : ((twHomComplex hch K L hU).X n).val.obj (op ⊤)) :
    twHomTopEquiv hch hU K L (n + 1)
        (((twHomComplex hch K L hU).d n (n + 1)).val.app (op ⊤) s) =
      δ n (n + 1) (twHomTopEquiv hch hU K L n s) := by
  funext T
  rw [twHomTopEquiv_apply, twHomComplex_d]
  show glueHomTwTopEquiv hch (K.X T.p) (L.X T.q) ((((twHomD hch K L n) ≫ Pi.π (fun T :
    Triplet (n + 1) ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T).val.app (op ⊤)).hom s) =
    _
  have hp : twHomD hch K L n ≫ Pi.π (fun T : Triplet (n + 1) ↦
      (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T =
      Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
        ⟨T.p, T.p + n, rfl⟩ ≫
        (glue R U).map (homTwPost hch (K.X T.p) (L.d (T.p + n) T.q)) +
      (n + 1).negOnePow •
        (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
            ⟨T.p + 1, T.q, by have := T.hpq; lia⟩ ≫
          (glue R U).map (homTwPre hch (K.d T.p (T.p + 1)) (L.X T.q))) := Pi.lift_comp_π _ _
  rw [hp]
  erw [add_app_apply'', units_smul_app_apply']
  rw [map_add, Units.smul_def, map_zsmul]
  have hv := δ_v n (n + 1) rfl (twHomTopEquiv hch hU K L n s) T.p T.q T.hpq (T.p + n) (T.p + 1)
    (by have := T.hpq; lia) rfl
  have e1 := glueHomTwTopEquiv_post hch (K.X T.p) (L.X (T.p + n)) (L.d (T.p + n) T.q)
    (((Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
      ⟨T.p, T.p + n, rfl⟩).val.app (op ⊤)).hom s)
  have e2 := glueHomTwTopEquiv_pre hch (K.X (T.p + 1)) (L.X T.q) (K.d T.p (T.p + 1))
    (((Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
      ⟨T.p + 1, T.q, by have := T.hpq; lia⟩).val.app (op ⊤)).hom s)
  have a1 := twHomTopEquiv_apply hch hU K L n s ⟨T.p, T.p + n, rfl⟩
  have a2 := twHomTopEquiv_apply hch hU K L n s ⟨T.p + 1, T.q, by have := T.hpq; lia⟩
  change _ = (δ n (n + 1) (twHomTopEquiv hch hU K L n s)).v T.p T.q T.hpq
  rw [hv, Units.smul_def]
  refine (congrArg₂ (· + ·) e1 (congrArg (fun y => ((n + 1).negOnePow : ℤ) • y) e2)).trans ?_
  exact congrArg₂ (· + ·) (congrArg (· ≫ L.d (T.p + n) T.q) a1.symm)
    (congrArg (fun y => ((n + 1).negOnePow : ℤ) • y) (congrArg (K.d T.p (T.p + 1) ≫ ·) a2.symm))

/-- **Z3.r (F′ (e)).** Under `twHomTopEquiv`, `twHomMap₂ g` is composition with `g`. -/
theorem twHomTopEquiv_map₂ {L' : CochainComplex (TwMod R U ch) ℤ} (g : L ⟶ L') (n : ℤ)
    (s : ((twHomComplex hch K L hU).X n).val.obj (op ⊤)) :
    twHomTopEquiv hch hU K L' n (((twHomMap₂ hch hU K g).f n).val.app (op ⊤) s) =
      (twHomTopEquiv hch hU K L n s).comp (Cochain.ofHom g) (add_zero n) := by
  funext T
  rw [twHomTopEquiv_apply]
  have hp := Pi.map_π (fun T : Triplet n ↦ (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q))) T
  have e1 := glueHomTwTopEquiv_post hch (K.X T.p) (L.X T.q) (g.f T.q)
    (((Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T).val.app
      (op ⊤)).hom s)
  change _ = ((twHomTopEquiv hch hU K L n s).comp (Cochain.ofHom g) (add_zero n)).v T.p T.q T.hpq
  rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  have hs := congrArg (fun f : (∏ᶜ fun T : Triplet n ↦ (glue R U).obj
      (homTw hch (K.X T.p) (L.X T.q))) ⟶ (glue R U).obj (homTw hch (K.X T.p) (L'.X T.q)) ↦
      ((f.val.app (op ⊤)).hom (show ((∏ᶜ fun T : Triplet n ↦ (glue R U).obj
        (homTw hch (K.X T.p) (L.X T.q))).val.obj (op ⊤)) from s))) hp
  refine (congrArg (glueHomTwTopEquiv hch (K.X T.p) (L'.X T.q)) hs).trans (e1.trans ?_)
  exact congrArg (· ≫ g.f T.q) (twHomTopEquiv_apply hch hU K L n s T).symm

end Cohesive
