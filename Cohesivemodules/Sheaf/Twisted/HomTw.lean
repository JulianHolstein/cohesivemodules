import Cohesivemodules.Sheaf.Twisted.Basic
import Cohesivemodules.Sheaf.Twisted.SecHom
import Cohesivemodules.Sheaf.Twisted.SecRes
import Cohesivemodules.Sheaf.Twisted.Preadditive
import Cohesivemodules.Sheaf.Hom

set_option linter.style.header false

/-!
# Z3.r: the twisted Hom sheaf `homTw K L` (one degree)

Blueprint item Z3.r (`blueprint/blueprint-tw.md` §3 F.2, F′ (b), (c)). For twisted sheaves
`K, L : TwMod R U ȟ` with normalized `ȟ` (`ȟ_αβα = 1`):
* `secHomOf`: a morphism `P|W ⟶ Q|W` of restrictions (Mathlib's `SheafOfModules.over`, i.e. a
  section of `homSheaf P Q` over `W ≤ U`) from an `R(W')`-linear natural family of maps on
  sections over `W' ≤ W` (F′ (b)); its components are the given maps (`rfl`). Conversely `secApp`
  reads such a morphism on sections over `W' ≤ W`, and `secHom_ext` is extensionality;
* `homTw K L : TwMod R U 1`: components `homSheaf (K_α) (L_α)` on `Over U_α`, gluing by conjugation
  on sections over `W ≤ U_α ∩ U_β`: `s ↦ φ^L_αβ ∘ s ∘ φ^K_βα`. The cocycles cancel
  (`φ^K_βα φ^K_γβ = ȟ_αβγ⁻¹ φ^K_γα` and `φ^L_βγ φ^L_αβ = ȟ_αβγ φ^L_αγ`), so `homTw K L` is
  untwisted;
* `homTwPost g`, `homTwPre f`: post- and pre-composition, morphisms of twisted sheaves with
  components `homPost`, `homPre` (S7).

## Deviations
* The cocycle `ȟ` is assumed normalized (`ȟ_αβα = 1`, as for every `TwistCocycle`), which gives
  `φ_βα = φ_αβ⁻¹` (`TwMod.φ_symm`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}

/-- Z3.r: the ring sheaf of `R` on every over-site is commutative (`IsCommSheaf`, needed by S7). -/
theorem isCommSheaf_over (U : Opens X) : IsCommSheaf ((ringOf R).over U) :=
  (IsComm.isCommSheaf (fun V a b => mul_comm (show R.obj.obj (op V) from a) b)).over U

/-- Z3.r: the object `W' ⟶ W` of the over-site of `W ⟶ U` (for `W' ≤ W ≤ U`), in the opposite
category. -/
abbrev ovr₂ {U W W' : Opens X} (h : W ≤ U) (h' : W' ≤ W) : (Over (Over.mk (homOfLE h)))ᵒᵖ :=
  op (Over.mk (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans h)) ⟶ Over.mk (homOfLE h)))

section SecHom

variable {U W : Opens X} (h : W ≤ U) {P Q : Mod ((ringOf R).over U)}

/-- Z3.r: a morphism `P|W ⟶ Q|W` of restrictions on sections over `W' ≤ W` (definitionally the
sections of `P`, `Q` over `W' ≤ U`). -/
def secApp (s : P.over (Over.mk (homOfLE h)) ⟶ Q.over (Over.mk (homOfLE h))) {W' : Opens X}
    (h' : W' ≤ W) : sec R P (h'.trans h) →+ sec R Q (h'.trans h) :=
  (s.val.app (ovr₂ h h')).hom.toAddMonoidHom

set_option linter.internalConstructors false in
/-- **Z3.r (F′ (b)).** A family of additive maps on sections over every `W' ≤ W`, `R(W')`-linear
and natural in `W'`, as a morphism `P|W ⟶ Q|W` of restrictions to the over-site of `W ⟶ U`
(Mathlib's `SheafOfModules.over`), i.e. a section of `homSheaf P Q` over `W`. Built as
`homOfSec₀`; its components are the given maps (`secApp_secHomOf`, rfl). -/
def secHomOf
    (f : ∀ {W' : Opens X} (h' : W' ≤ W), sec R P (h'.trans h) →+ sec R Q (h'.trans h))
    (hsmul : ∀ {W' : Opens X} (h' : W' ≤ W) (r : R.obj.obj (op W')) x,
      f h' (toSec R (h'.trans h) r • x) = toSec R (h'.trans h) r • f h' x)
    (hres : ∀ {W' W'' : Opens X} (h' : W' ≤ W) (h'' : W'' ≤ W') x,
      f (h''.trans h') (secRes R P (h'.trans h) h'' x) =
        secRes R Q (h'.trans h) h'' (f h' x)) :
    P.over (Over.mk (homOfLE h)) ⟶ Q.over (Over.mk (homOfLE h)) where
  val :=
    { app := fun Z => ModuleCat.Hom._mkInternal
        { toFun := f (leOfHom Z.unop.hom.left)
          map_add' := map_add _
          map_smul' := fun r x => hsmul (leOfHom Z.unop.hom.left) r x }
      naturality := fun {Z Z'} g => by
        ext x
        exact hres (leOfHom Z.unop.hom.left) (leOfHom g.unop.left.left) x }

/-- Z3.r: the components of `secHomOf` are the given maps (rfl). -/
theorem secApp_secHomOf
    (f : ∀ {W' : Opens X} (h' : W' ≤ W), sec R P (h'.trans h) →+ sec R Q (h'.trans h))
    (hsmul : ∀ {W' : Opens X} (h' : W' ≤ W) (r : R.obj.obj (op W')) x,
      f h' (toSec R (h'.trans h) r • x) = toSec R (h'.trans h) r • f h' x)
    (hres : ∀ {W' W'' : Opens X} (h' : W' ≤ W) (h'' : W'' ≤ W') x,
      f (h''.trans h') (secRes R P (h'.trans h) h'' x) =
        secRes R Q (h'.trans h) h'' (f h' x))
    {W' : Opens X} (h' : W' ≤ W) (x : sec R P (h'.trans h)) :
    secApp h (secHomOf h f hsmul hres) h' x = f h' x := rfl

/-- Z3.r: `secApp` is `R(W')`-linear. -/
theorem secApp_smul (s : P.over (Over.mk (homOfLE h)) ⟶ Q.over (Over.mk (homOfLE h)))
    {W' : Opens X} (h' : W' ≤ W) (r : R.obj.obj (op W')) (x : sec R P (h'.trans h)) :
    secApp h s h' (toSec R (h'.trans h) r • x) = toSec R (h'.trans h) r • secApp h s h' x :=
  (s.val.app (ovr₂ h h')).hom.map_smul r x

/-- Z3.r: `secApp` is natural in `W'`. -/
theorem secApp_res (s : P.over (Over.mk (homOfLE h)) ⟶ Q.over (Over.mk (homOfLE h)))
    {W' W'' : Opens X} (h' : W' ≤ W) (h'' : W'' ≤ W') (x : sec R P (h'.trans h)) :
    secApp h s (h''.trans h') (secRes R P (h'.trans h) h'' x) =
      secRes R Q (h'.trans h) h'' (secApp h s h' x) := by
  exact (PresheafOfModules.naturality_apply s.val (Quiver.Hom.op (Over.homMk (Over.homMk
    (homOfLE h'') : Over.mk (homOfLE (h''.trans (h'.trans h))) ⟶ Over.mk (homOfLE (h'.trans h))) :
    (ovr₂ h (h''.trans h')).unop ⟶ (ovr₂ h h').unop)) x).symm.symm

/-- Z3.r: morphisms of restrictions are equal if they agree on sections over every `W' ≤ W`. -/
theorem secHom_ext {s t : P.over (Over.mk (homOfLE h)) ⟶ Q.over (Over.mk (homOfLE h))}
    (hst : ∀ {W' : Opens X} (h' : W' ≤ W) (x : sec R P (h'.trans h)),
      secApp h s h' x = secApp h t h' x) : s = t :=
  hom_ext_pt fun Z m => hst (leOfHom Z.unop.hom.left) m

end SecHom

variable {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

section Conj

variable (K L : TwMod R U ch) (α β : ι) {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β)

/-- Z3.r: the conjugate of `s : K_α|W ⟶ L_α|W` on sections over `W' ≤ W`:
`x ↦ φ^L_αβ (s (φ^K_βα x))`. -/
def conjSec (s : (K.M α).over (Over.mk (homOfLE hα)) ⟶ (L.M α).over (Over.mk (homOfLE hα)))
    {W' : Opens X} (h' : W' ≤ W) : sec R (K.M β) (h'.trans hβ) →+ sec R (L.M β) (h'.trans hβ) :=
  (L.φ α β (h'.trans hα) (h'.trans hβ)).comp
    ((secApp hα s h').comp (K.φ β α (h'.trans hβ) (h'.trans hα)))

/-- Z3.r: `conjSec` on an element (rfl). -/
theorem conjSec_apply
    (s : (K.M α).over (Over.mk (homOfLE hα)) ⟶ (L.M α).over (Over.mk (homOfLE hα)))
    {W' : Opens X} (h' : W' ≤ W) (x : sec R (K.M β) (h'.trans hβ)) :
    conjSec K L α β hα hβ s h' x =
      L.φ α β (h'.trans hα) (h'.trans hβ)
        (secApp hα s h' (K.φ β α (h'.trans hβ) (h'.trans hα) x)) :=
  rfl

/-- **Z3.r (F′ (c)).** Conjugation by the gluing maps: `s : K_α|W ⟶ L_α|W` gives
`φ^L_αβ ∘ s ∘ φ^K_βα : K_β|W ⟶ L_β|W`, for `W ≤ U_α ∩ U_β`. -/
def conj (s : (K.M α).over (Over.mk (homOfLE hα)) ⟶ (L.M α).over (Over.mk (homOfLE hα))) :
    (K.M β).over (Over.mk (homOfLE hβ)) ⟶ (L.M β).over (Over.mk (homOfLE hβ)) :=
  secHomOf hβ (conjSec K L α β hα hβ s)
    (fun h' r x => by
      rw [conjSec_apply, conjSec_apply, K.φ_smul, secApp_smul, L.φ_smul])
    (fun h' h'' x => by
      rw [conjSec_apply, conjSec_apply, K.φ_res, secApp_res, L.φ_res])

/-- Z3.r: `conj` on sections (rfl). -/
theorem secApp_conj
    (s : (K.M α).over (Over.mk (homOfLE hα)) ⟶ (L.M α).over (Over.mk (homOfLE hα)))
    {W' : Opens X} (h' : W' ≤ W) (x : sec R (K.M β) (h'.trans hβ)) :
    secApp hβ (conj K L α β hα hβ s) h' x =
      L.φ α β (h'.trans hα) (h'.trans hβ)
        (secApp hα s h' (K.φ β α (h'.trans hβ) (h'.trans hα) x)) :=
  rfl

end Conj

section ConjAlg

variable (K L : TwMod R U ch) (α β : ι) {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β)

/-- Z3.r helper: `conj` is additive. -/
private theorem conj_add
    (s t : (K.M α).over (Over.mk (homOfLE hα)) ⟶ (L.M α).over (Over.mk (homOfLE hα))) :
    conj K L α β hα hβ (s + t) = conj K L α β hα hβ s + conj K L α β hα hβ t :=
  secHom_ext hβ fun h' x => by
    rw [secApp_conj]
    change L.φ α β _ _ (secApp hα s h' (K.φ β α _ _ x) + secApp hα t h' (K.φ β α _ _ x)) =
      secApp hβ (conj K L α β hα hβ s) h' x + secApp hβ (conj K L α β hα hβ t) h' x
    rw [map_add]
    rfl

/-- Z3.r helper: `conj` is additive (zero). -/
private theorem conj_zero :
    conj K L α β hα hβ (0 : (K.M α).over (Over.mk (homOfLE hα)) ⟶
      (L.M α).over (Over.mk (homOfLE hα))) = 0 :=
  secHom_ext hβ fun h' x => by
    rw [secApp_conj]
    change L.φ α β _ _ (0 : sec R (L.M α) _) = (0 : sec R (L.M β) _)
    exact map_zero _

/-- Z3.r helper: `conj` commutes with the target action of `R(W)`. -/
private theorem conj_smul (r : R.obj.obj (op W))
    (s : (K.M α).over (Over.mk (homOfLE hα)) ⟶ (L.M α).over (Over.mk (homOfLE hα))) :
    conj K L α β hα hβ (homSmul (isCommSheaf_over (U α)) (toSec R hα r) s) =
      homSmul (isCommSheaf_over (U β)) (toSec R hβ r) (conj K L α β hα hβ s) :=
  secHom_ext hβ fun h' x => by
    rw [secApp_conj]
    change L.φ α β _ _ (toSec R (h'.trans hα) ((R.obj.map (homOfLE h').op).hom r) •
        secApp hα s h' (K.φ β α _ _ x)) =
      toSec R (h'.trans hβ) ((R.obj.map (homOfLE h').op).hom r) •
        secApp hβ (conj K L α β hα hβ s) h' x
    exact L.φ_smul _ _ _ _ _ _

/-- Z3.r helper: the cocycles of `K` and `L` cancel on sections (`ȟ` and `ȟ⁻¹`). -/
private theorem cocycle_sec (hch : ∀ α β, ch α β α = 1) (γ : ι) (hγ : W ≤ U γ)
    (s : (K.M α).over (Over.mk (homOfLE hα)) ⟶ (L.M α).over (Over.mk (homOfLE hα)))
    {W' : Opens X} (h' : W' ≤ W) (x : sec R (K.M γ) (h'.trans hγ)) :
    L.φ β γ (h'.trans hβ) (h'.trans hγ) (L.φ α β (h'.trans hα) (h'.trans hβ)
      (secApp hα s h' (K.φ β α (h'.trans hβ) (h'.trans hα)
        (K.φ γ β (h'.trans hγ) (h'.trans hβ) x)))) =
    L.φ α γ (h'.trans hα) (h'.trans hγ)
      (secApp hα s h' (K.φ γ α (h'.trans hγ) (h'.trans hα) x)) := by
  set y := K.φ β α (h'.trans hβ) (h'.trans hα) (K.φ γ β (h'.trans hγ) (h'.trans hβ) x) with hy
  have e1 : K.φ α β (h'.trans hα) (h'.trans hβ) y = K.φ γ β (h'.trans hγ) (h'.trans hβ) x :=
    TwMod.φ_symm hch K β α _ _ _
  have e2 : K.φ β γ (h'.trans hβ) (h'.trans hγ) (K.φ γ β (h'.trans hγ) (h'.trans hβ) x) = x :=
    TwMod.φ_symm hch K γ β _ _ _
  have e3 := K.cocycle α β γ (h'.trans hα) (h'.trans hβ) (h'.trans hγ) y
  rw [e1, e2] at e3
  have e4 := congrArg (K.φ γ α (h'.trans hγ) (h'.trans hα)) e3
  rw [K.φ_smul, TwMod.φ_symm hch K α γ] at e4
  rw [e4, secApp_smul, L.φ_smul, ← L.cocycle α β γ]

end ConjAlg

variable (hch : ∀ α β, ch α β α = 1)

/-- **Z3.r (F′ (c)).** [Căldăraru, §1.2]. The twisted Hom sheaf of `K, L : TwMod R U ȟ` (one
degree), an untwisted (`ȟ = 1`) twisted sheaf: components `homSheaf (K_α) (L_α)` on `Over U_α`
(S7; sections over `W` are the morphisms `K_α|W ⟶ L_α|W`), gluing maps `conj`
(`s ↦ φ^L_αβ ∘ s ∘ φ^K_βα`). The cocycle holds with `1`: the scalars `ȟ_αβγ` of `L` and `ȟ_αβγ⁻¹`
of `K` cancel (`s` is linear). ⚠ Needs `ȟ` normalized (`hch`). -/
def homTw (hch : ∀ α β, ch α β α = 1) (K L : TwMod R U ch) : TwMod R U (fun _ _ _ => 1) where
  M α := homSheaf (isCommSheaf_over (U α)) (K.M α) (L.M α)
  φ α β _ hα hβ :=
    { toFun := fun s => conj K L α β hα hβ s
      map_zero' := conj_zero K L α β hα hβ
      map_add' := fun s t => conj_add K L α β hα hβ s t }
  φ_smul α β _ hα hβ r s := conj_smul K L α β hα hβ r s
  φ_res α β _ _ hα hβ h' s := secHom_ext _ fun h'' x => rfl
  φ_self α _ hα s := secHom_ext hα fun h' x =>
    (L.φ_self α _ _).trans (congrArg (secApp hα s h') (K.φ_self α _ _))
  cocycle α β γ _ hα hβ hγ s := by
    refine secHom_ext hγ fun h' x => ?_
    change L.φ β γ _ _ (L.φ α β _ _ (secApp hα s h' (K.φ β α _ _ (K.φ γ β _ _ x)))) =
      toSec R (h'.trans hγ) ((R.obj.map (homOfLE h').op).hom (((unitRes R (le_inf (le_inf hα hβ) hγ)
        (1 : (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ) : (R.obj.obj (op _))ˣ) :
        R.obj.obj (op _)))) •
        L.φ α γ _ _ (secApp hα s h' (K.φ γ α _ _ x))
    simp only [map_one, Units.val_one]
    exact (cocycle_sec K L α β hα hβ hch γ hγ s h' x).trans
      (one_smul (((ringOf R).over (U γ)).obj.obj (ovr (h'.trans hγ))) _).symm

/-- Z3.r: components of `homTw` (rfl). -/
theorem homTw_M (K L : TwMod R U ch) (α : ι) :
    (homTw hch K L).M α = homSheaf (isCommSheaf_over (U α)) (K.M α) (L.M α) := rfl

/-- Z3.r: gluing maps of `homTw` (rfl). -/
theorem homTw_φ (K L : TwMod R U ch) (α β : ι) {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β)
    (s : (K.M α).over (Over.mk (homOfLE hα)) ⟶ (L.M α).over (Over.mk (homOfLE hα))) :
    (homTw hch K L).φ α β hα hβ s = conj K L α β hα hβ s := rfl

/-- **Z3.r.** Post-composition with `g : L ⟶ L'`: `homTw K L ⟶ homTw K L'`, components `homPost`
(`s ↦ s ≫ g_α|W`). -/
def homTwPost (K : TwMod R U ch) {L L' : TwMod R U ch} (g : L ⟶ L') :
    homTw hch K L ⟶ homTw hch K L' where
  f α := homPost (isCommSheaf_over (U α)) (K.M α) (g.f α)
  comm α β _ hα hβ _ :=
    secHom_ext hβ fun h' _ => g.comm α β (h'.trans hα) (h'.trans hβ) _

/-- **Z3.r.** Pre-composition with `f : K' ⟶ K`: `homTw K L ⟶ homTw K' L`, components `homPre`
(`s ↦ f_α|W ≫ s`). -/
def homTwPre {K K' : TwMod R U ch} (f : K' ⟶ K) (L : TwMod R U ch) :
    homTw hch K L ⟶ homTw hch K' L where
  f α := homPre (isCommSheaf_over (U α)) (f.f α) (L.M α)
  comm α β _ hα hβ s :=
    secHom_ext hβ fun h' x =>
      congrArg (fun y => L.φ α β (h'.trans hα) (h'.trans hβ) (secApp hα s h' y))
        (f.comm β α (h'.trans hβ) (h'.trans hα) x).symm

/-- Z3.r: components of `homTwPost` (rfl). -/
theorem homTwPost_f (K : TwMod R U ch) {L L' : TwMod R U ch} (g : L ⟶ L') (α : ι) :
    (homTwPost hch K g).f α = homPost (isCommSheaf_over (U α)) (K.M α) (g.f α) := rfl

/-- Z3.r: components of `homTwPre` (rfl). -/
theorem homTwPre_f {K K' : TwMod R U ch} (f : K' ⟶ K) (L : TwMod R U ch) (α : ι) :
    (homTwPre hch f L).f α = homPre (isCommSheaf_over (U α)) (f.f α) (L.M α) := rfl

/-- Z3.r: `homTwPost` is functorial. -/
theorem homTwPost_comp (K : TwMod R U ch) {L L' L'' : TwMod R U ch} (g : L ⟶ L') (g' : L' ⟶ L'') :
    homTwPost hch K (g ≫ g') = homTwPost hch K g ≫ homTwPost hch K g' := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

/-- Z3.r: `homTwPre` is contravariantly functorial. -/
theorem homTwPre_comp {K K' K'' : TwMod R U ch} (f : K' ⟶ K) (f' : K'' ⟶ K') (L : TwMod R U ch) :
    homTwPre hch f L ≫ homTwPre hch f' L = homTwPre hch (f' ≫ f) L := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

/-- Z3.r: `homTwPre` and `homTwPost` commute. -/
theorem homTwPre_homTwPost {K K' L L' : TwMod R U ch} (f : K' ⟶ K) (g : L ⟶ L') :
    homTwPre hch f L ≫ homTwPost hch K' g = homTwPost hch K g ≫ homTwPre hch f L' := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

/-- Z3.r: `homTwPost` is additive. -/
theorem homTwPost_add (K : TwMod R U ch) {L L' : TwMod R U ch} (g g' : L ⟶ L') :
    homTwPost hch K (g + g') = homTwPost hch K g + homTwPost hch K g' := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

/-- Z3.r: `homTwPre` is additive. -/
theorem homTwPre_add {K K' : TwMod R U ch} (f f' : K' ⟶ K) (L : TwMod R U ch) :
    homTwPre hch (f + f') L = homTwPre hch f L + homTwPre hch f' L := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦
    (φ.val.app Z).hom.map_add _ _)

/-- Z3.r: `homTwPost 0 = 0`. -/
theorem homTwPost_zero (K : TwMod R U ch) (L L' : TwMod R U ch) :
    homTwPost hch K (0 : L ⟶ L') = 0 := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

/-- Z3.r: `homTwPre 0 = 0`. -/
theorem homTwPre_zero (K K' : TwMod R U ch) (L : TwMod R U ch) :
    homTwPre hch (0 : K' ⟶ K) L = 0 := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦
    (φ.val.app Z).hom.map_zero)

end Cohesive
