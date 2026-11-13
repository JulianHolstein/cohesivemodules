import Cohesivemodules.Sheaf.Twisted.ExtTw

set_option linter.style.header false

/-!
# Z3.l: `extTw α ⊣ comp_α`, and `comp_α` preserves injectives (C.5)

Blueprint item Z3.l (blueprint §11 v1.20 item 3; `blueprint/blueprint-tw.md` C.5, C.8). For a
twist cocycle `T` and `f : N ⟶ M_α`, the lift `extTwLift f : extTw α N ⟶ M` sends a section `s` of
`(extTw α N)_β` over `W` (a section of `N` over `W ⊓ U_α` vanishing on `W' ⊓ U_α`, with
`W ≤ (W ⊓ U_α) ⊔ W'`) to the unique section of `M_β` over `W` that is `φ_αβ(f s)` on `W ⊓ U_α` and
`0` on `W'`. With the unit `N ⟶ (extTw α N)_α`, `s ↦ s|(W ⊓ U_α)`, this is an adjunction
`extTw α ⊣ comp_α`; as `extTw α` preserves monomorphisms, `comp_α` preserves injective objects.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  (T : TwistCocycle R)

/-- **Z3.l.** Extension of a section by zero: if `t₀` over `W ⊓ V` vanishes on `W' ⊓ V` and
`W ≤ (W ⊓ V) ⊔ W'`, there is a unique section over `W` restricting to `t₀` on `W ⊓ V` and to `0` on
`W'` (`sec_existsUnique_gluing` for the cover `{W ⊓ V, W'}`). -/
theorem existsUnique_extend_zero {U W V W' : Opens X} (hW : W ≤ U) (G : Mod ((ringOf R).over U))
    (hW' : W' ≤ W) (hcov : W ≤ (W ⊓ V) ⊔ W')
    (t₀ : sec R G ((inf_le_left : W ⊓ V ≤ W).trans hW))
    (h₀ : secRes R G ((inf_le_left : W ⊓ V ≤ W).trans hW) (inf_le_inf_right V hW') t₀ = 0) :
    ∃! t : sec R G hW, secRes R G hW inf_le_left t = t₀ ∧ secRes R G hW hW' t = 0 := by
  let V' : Bool → Opens X := fun b => cond b (W ⊓ V) W'
  have hV : ∀ i, V' i ≤ W := by
    intro i
    cases i
    · exact hW'
    · exact inf_le_left
  have hcov' : W ≤ ⨆ i, V' i :=
    hcov.trans (sup_le (le_iSup V' true) (le_iSup V' false))
  let s : ∀ i, sec R G ((hV i).trans hW) :=
    fun i => Bool.rec (motive := fun i => sec R G ((hV i).trans hW)) 0 t₀ i
  have hz : secRes R G ((inf_le_left : W ⊓ V ≤ W).trans hW)
      (inf_le_left : W ⊓ V ⊓ W' ≤ W ⊓ V) t₀ = 0 := by
    have k : W ⊓ V ⊓ W' ≤ W' ⊓ V := le_inf inf_le_right (inf_le_left.trans inf_le_right)
    have e : (inf_le_left : W ⊓ V ⊓ W' ≤ W ⊓ V) = k.trans (inf_le_inf_right V hW') := rfl
    rw [e, ← secRes_secRes G _ (inf_le_inf_right V hW') k t₀, h₀]
    exact map_zero _
  have hz' : secRes R G ((inf_le_left : W ⊓ V ≤ W).trans hW)
      (inf_le_right : W' ⊓ (W ⊓ V) ≤ W ⊓ V) t₀ = 0 := by
    have k : W' ⊓ (W ⊓ V) ≤ W' ⊓ V := le_inf inf_le_left (inf_le_right.trans inf_le_right)
    have e : (inf_le_right : W' ⊓ (W ⊓ V) ≤ W ⊓ V) = k.trans (inf_le_inf_right V hW') := rfl
    rw [e, ← secRes_secRes G _ (inf_le_inf_right V hW') k t₀, h₀]
    exact map_zero _
  have hs : ∀ i j, secRes R G ((hV i).trans hW) (inf_le_left : V' i ⊓ V' j ≤ V' i) (s i) =
      secRes R G ((hV j).trans hW) (inf_le_right : V' i ⊓ V' j ≤ V' j) (s j) := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact (map_zero _).trans hz'.symm
    · exact hz.trans (map_zero _).symm
    · rfl
  obtain ⟨t, ht, ht'⟩ := sec_existsUnique_gluing hW G V' hV hcov' s hs
  refine ⟨t, ⟨ht true, ht false⟩, fun y hy => ht' y ?_⟩
  intro i
  cases i
  · exact hy.2
  · exact hy.1

/-- Helper: a chosen support witness `W'` of a section of `j_! N` over `W`. -/
private def extWit {V : Opens X} {F : Mod ((ringOf R).over V)} {W : Opens X}
    (s : extSub V F W) : Opens X :=
  (mem_extSub.1 s.2).choose

/-- Helper: the chosen witness lies in `W`. -/
private theorem extWit_le {V : Opens X} {F : Mod ((ringOf R).over V)} {W : Opens X}
    (s : extSub V F W) : extWit s ≤ W :=
  (mem_extSub.1 s.2).choose_spec.choose

/-- Helper: `W ≤ (W ⊓ V) ⊔ W'` for the chosen witness. -/
private theorem extWit_cov {V : Opens X} {F : Mod ((ringOf R).over V)} {W : Opens X}
    (s : extSub V F W) : W ≤ (W ⊓ V) ⊔ extWit s :=
  (mem_extSub.1 s.2).choose_spec.choose_spec.1

/-- Helper: the section vanishes on the chosen witness. -/
private theorem extWit_zero {V : Opens X} {F : Mod ((ringOf R).over V)} {W : Opens X}
    (s : extSub V F W) :
    secRes R F inf_le_right (inf_le_inf_right V (extWit_le s)) s.1 = 0 :=
  (mem_extSub.1 s.2).choose_spec.choose_spec.2

/-- Helper: the section `φ_αβ(f s)` over `W ⊓ U_α`, the datum glued by `extTwLiftSec`. -/
private def extTwT₀ (α : T.ι) {N : Mod ((ringOf R).over (T.U α))} {M : TwMod R T.U T.ch}
    (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β) (s : extSub (T.U α) N W) :
    sec R (M.M β) ((inf_le_left : W ⊓ T.U α ≤ W).trans hβ) :=
  M.φ α β (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_left.trans hβ)
    ((f.val.app (ovr inf_le_right)).hom s.1)

/-- Helper: `φ_αβ(f s)` vanishes on `W' ⊓ U_α` whenever `s` does. -/
private theorem extTwT₀_res (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W W' : Opens X} (hβ : W ≤ T.U β)
    (hW' : W' ≤ W) (s : extSub (T.U α) N W)
    (hs : secRes R N inf_le_right (inf_le_inf_right (T.U α) hW') s.1 = 0) :
    secRes R (M.M β) ((inf_le_left : W ⊓ T.U α ≤ W).trans hβ) (inf_le_inf_right (T.U α) hW')
      (extTwT₀ T α f β hβ s) = 0 := by
  unfold extTwT₀
  have h1 := app_secRes f (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_inf_right (T.U α) hW')
    (s.1 : sec R N inf_le_right)
  have h2 : secRes R N inf_le_right (inf_le_inf_right (T.U α) hW')
      (s.1 : sec R N inf_le_right) = 0 := hs
  rw [← M.φ_res, ← h1, h2]
  simp only [map_zero]

/-- **Z3.l.** The section map of the lift of `f : N ⟶ M_α` on the component `β`: the unique
section over `W` equal to `φ_αβ(f s)` on `W ⊓ U_α` and to `0` on a witness `W'` of `s`. -/
def extTwLiftSec (α : T.ι) {N : Mod ((ringOf R).over (T.U α))} {M : TwMod R T.U T.ch}
    (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β) (s : extSub (T.U α) N W) :
    sec R (M.M β) hβ :=
  (existsUnique_extend_zero hβ (M.M β) (extWit_le s) (extWit_cov s) (extTwT₀ T α f β hβ s)
    (extTwT₀_res T α f β hβ (extWit_le s) s (extWit_zero s))).exists.choose

/-- Helper: the defining properties of `extTwLiftSec`. -/
private theorem extTwLiftSec_spec (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β)
    (s : extSub (T.U α) N W) :
    secRes R (M.M β) hβ (inf_le_left : W ⊓ T.U α ≤ W) (extTwLiftSec T α f β hβ s) =
      extTwT₀ T α f β hβ s ∧
    secRes R (M.M β) hβ (extWit_le s) (extTwLiftSec T α f β hβ s) = 0 :=
  (existsUnique_extend_zero hβ (M.M β) (extWit_le s) (extWit_cov s) (extTwT₀ T α f β hβ s)
    (extTwT₀_res T α f β hβ (extWit_le s) s (extWit_zero s))).exists.choose_spec

/-- **Z3.l.** On `W ⊓ U_α` the lifted section is `φ_αβ(f s)`. -/
theorem extTwLiftSec_res_inf (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β)
    (s : extSub (T.U α) N W) :
    secRes R (M.M β) hβ (inf_le_left : W ⊓ T.U α ≤ W) (extTwLiftSec T α f β hβ s) =
      M.φ α β (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_left.trans hβ)
        ((f.val.app (ovr inf_le_right)).hom s.1) :=
  (extTwLiftSec_spec T α f β hβ s).1

/-- **Z3.l.** The lifted section vanishes on every open `W' ≤ W` on which `s` vanishes. -/
theorem extTwLiftSec_res_zero (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W W' : Opens X} (hβ : W ≤ T.U β)
    (hW' : W' ≤ W) (s : extSub (T.U α) N W)
    (hs : secRes R N inf_le_right (inf_le_inf_right (T.U α) hW') s.1 = 0) :
    secRes R (M.M β) hβ hW' (extTwLiftSec T α f β hβ s) = 0 := by
  let V' : Bool → Opens X := fun b => cond b (W' ⊓ T.U α) (W' ⊓ extWit s)
  have hV : ∀ i, V' i ≤ W' := by
    intro i
    cases i
    · exact inf_le_left
    · exact inf_le_left
  have hcov : W' ≤ ⨆ i, V' i := by
    intro x hx
    rcases extWit_cov s (hW' hx) with h | h
    · exact le_iSup V' true ⟨hx, h.2⟩
    · exact le_iSup V' false ⟨hx, h⟩
  refine sec_ext_of_cover (hW'.trans hβ) (M.M β) V' hV hcov _ 0 ?_
  intro i
  have z0 : secRes R (M.M β) (hW'.trans hβ) (hV i) 0 = 0 :=
    map_zero (secResHom R (M.M β) (hW'.trans hβ) (hV i))
  rw [secRes_secRes, z0]
  cases i
  · have e := (secRes_secRes (M.M β) hβ (extWit_le s) (inf_le_right : W' ⊓ extWit s ≤ extWit s)
      (extTwLiftSec T α f β hβ s)).symm
    refine e.trans ?_
    rw [(extTwLiftSec_spec T α f β hβ s).2]
    exact map_zero (secResHom R (M.M β) _ _)
  · have e := (secRes_secRes (M.M β) hβ (inf_le_left : W ⊓ T.U α ≤ W)
      (inf_le_inf_right (T.U α) hW') (extTwLiftSec T α f β hβ s)).symm
    refine e.trans ?_
    rw [(extTwLiftSec_spec T α f β hβ s).1]
    exact extTwT₀_res T α f β hβ hW' s hs

/-- Helper: characterization of the lift by any witness `W'` of `s`. -/
private theorem extTwLiftSec_eq (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W W' : Opens X} (hβ : W ≤ T.U β)
    (hW' : W' ≤ W) (hcov : W ≤ (W ⊓ T.U α) ⊔ W') (s : extSub (T.U α) N W)
    (hs : secRes R N inf_le_right (inf_le_inf_right (T.U α) hW') s.1 = 0)
    (t : sec R (M.M β) hβ)
    (h1 : secRes R (M.M β) hβ (inf_le_left : W ⊓ T.U α ≤ W) t = extTwT₀ T α f β hβ s)
    (h2 : secRes R (M.M β) hβ hW' t = 0) : t = extTwLiftSec T α f β hβ s :=
  (existsUnique_extend_zero hβ (M.M β) hW' hcov (extTwT₀ T α f β hβ s)
    (extTwT₀_res T α f β hβ hW' s hs)).unique ⟨h1, h2⟩
    ⟨extTwLiftSec_res_inf T α f β hβ s, extTwLiftSec_res_zero T α f β hβ hW' s hs⟩

/-- Helper: vanishing of a section of `j_! F` passes to smaller opens. -/
private theorem extSub_zero_mono {V : Opens X} {F : Mod ((ringOf R).over V)} {W W₁ W₂ : Opens X}
    (s : extSub V F W) (h₁ : W₁ ≤ W) (h₂ : W₂ ≤ W₁)
    (hs : secRes R F inf_le_right (inf_le_inf_right V h₁) s.1 = 0) :
    secRes R F inf_le_right (inf_le_inf_right V (h₂.trans h₁)) s.1 = 0 := by
  have e := secRes_secRes F (inf_le_right : W ⊓ V ≤ V) (inf_le_inf_right V h₁)
    (inf_le_inf_right V h₂) (s.1 : sec R F inf_le_right)
  rw [show secRes R F inf_le_right (inf_le_inf_right V h₁) (s.1 : sec R F inf_le_right) = 0 from
    hs] at e
  exact e.symm.trans (map_zero (secResHom R F _ (inf_le_inf_right V h₂)))

/-- Helper: `extTwT₀` is additive. -/
private theorem extTwT₀_add (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β)
    (s s' : extSub (T.U α) N W) :
    extTwT₀ T α f β hβ (s + s') = extTwT₀ T α f β hβ s + extTwT₀ T α f β hβ s' := by
  unfold extTwT₀
  exact (congrArg (M.φ α β _ _) (map_add (f.val.app (ovr inf_le_right)).hom
    (s.1 : sec R N inf_le_right) s'.1)).trans (map_add _ _ _)

/-- Helper: `extTwT₀` of a scalar multiple. -/
private theorem extTwT₀_smul (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β)
    (r : R.obj.obj (op W)) (s : extSub (T.U α) N W) :
    extTwT₀ T α f β hβ (toSec R hβ r • (show sec R ((extTwObj T α N).M β) hβ from s) :
        extSub (T.U α) N W) =
      toSec R ((inf_le_left : W ⊓ T.U α ≤ W).trans hβ)
        ((R.obj.map (homOfLE (inf_le_left : W ⊓ T.U α ≤ W)).op).hom r) • extTwT₀ T α f β hβ s := by
  unfold extTwT₀
  exact (congrArg (M.φ α β _ _) (app_smul f (inf_le_right : W ⊓ T.U α ≤ T.U α)
    ((R.obj.map (homOfLE (inf_le_left : W ⊓ T.U α ≤ W)).op).hom r)
    (s.1 : sec R N inf_le_right))).trans (M.φ_smul α β _ _ _ _)

/-- Helper: the lifted section is additive in `s`. -/
private theorem extTwLiftSec_add (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β)
    (s s' : extSub (T.U α) N W) :
    extTwLiftSec T α f β hβ (s + s') =
      extTwLiftSec T α f β hβ s + extTwLiftSec T α f β hβ s' := by
  have hW' : extWit s ⊓ extWit s' ≤ W := inf_le_left.trans (extWit_le s)
  have z1 := extSub_zero_mono s (extWit_le s) (inf_le_left : extWit s ⊓ extWit s' ≤ extWit s)
    (extWit_zero s)
  have z2 := extSub_zero_mono s' (extWit_le s') (inf_le_right : extWit s ⊓ extWit s' ≤ extWit s')
    (extWit_zero s')
  refine (extTwLiftSec_eq T α f β hβ hW' ?_ (s + s') ?_ _ ?_ ?_).symm
  · intro x hx
    by_cases hxU : x ∈ T.U α
    · exact Or.inl ⟨hx, hxU⟩
    · rcases extWit_cov s hx with h1 | h1
      · exact absurd h1.2 hxU
      rcases extWit_cov s' hx with h2 | h2
      · exact absurd h2.2 hxU
      exact Or.inr ⟨h1, h2⟩
  · exact (map_add (secResHom R N inf_le_right (inf_le_inf_right (T.U α) hW'))
      (s.1 : sec R N inf_le_right) s'.1).trans (by
        show secRes R N (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_inf_right (T.U α) hW')
            (s.1 : sec R N inf_le_right) +
          secRes R N (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_inf_right (T.U α) hW')
            (s'.1 : sec R N inf_le_right) = 0
        rw [z1, z2, add_zero])
  · exact (map_add (secResHom R (M.M β) hβ (inf_le_left : W ⊓ T.U α ≤ W)) _ _).trans
      ((congr_arg₂ (· + ·) (extTwLiftSec_res_inf T α f β hβ s)
        (extTwLiftSec_res_inf T α f β hβ s')).trans (extTwT₀_add T α f β hβ s s').symm)
  · have a1 := extTwLiftSec_res_zero T α f β hβ hW' s z1
    have a2 := extTwLiftSec_res_zero T α f β hβ hW' s' z2
    exact (map_add (secResHom R (M.M β) hβ hW') _ _).trans (by
      show secRes R (M.M β) hβ hW' _ + secRes R (M.M β) hβ hW' _ = 0
      rw [a1, a2, add_zero])

/-- Helper: the lifted section is `R(W)`-linear in `s`. -/
private theorem extTwLiftSec_smul (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β)
    (r : R.obj.obj (op W)) (s : extSub (T.U α) N W) :
    extTwLiftSec T α f β hβ (toSec R hβ r •
        (show sec R ((extTwObj T α N).M β) hβ from s) : extSub (T.U α) N W) =
      toSec R hβ r • extTwLiftSec T α f β hβ s := by
  refine (extTwLiftSec_eq T α f β hβ (extWit_le s) (extWit_cov s) _ ?_ _ ?_ ?_).symm
  · exact (secRes_smul N (inf_le_right : W ⊓ T.U α ≤ T.U α)
      (inf_le_inf_right (T.U α) (extWit_le s))
      ((R.obj.map (homOfLE (inf_le_left : W ⊓ T.U α ≤ W)).op).hom r)
      (s.1 : sec R N inf_le_right)).trans (by
        rw [show secRes R N inf_le_right (inf_le_inf_right (T.U α) (extWit_le s))
          (s.1 : sec R N inf_le_right) = 0 from extWit_zero s]
        exact smul_zero _)
  · refine (secRes_smul (M.M β) hβ (inf_le_left : W ⊓ T.U α ≤ W) r _).trans ?_
    rw [(extTwLiftSec_spec T α f β hβ s).1]
    exact (extTwT₀_smul T α f β hβ r s).symm
  · refine (secRes_smul (M.M β) hβ (extWit_le s) r _).trans ?_
    rw [(extTwLiftSec_spec T α f β hβ s).2]
    exact smul_zero _

/-- Helper: the lifted section is natural in `W`. -/
private theorem extTwLiftSec_res (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β : T.ι) {W W₂ : Opens X} (hβ : W ≤ T.U β)
    (h' : W₂ ≤ W) (s : extSub (T.U α) N W) :
    extTwLiftSec T α f β (h'.trans hβ) (extRes (T.U α) N h' s) =
      secRes R (M.M β) hβ h' (extTwLiftSec T α f β hβ s) := by
  have hW' : extWit s ⊓ W₂ ≤ W₂ := inf_le_right
  have z := extSub_zero_mono s (extWit_le s) (inf_le_left : extWit s ⊓ W₂ ≤ extWit s)
    (extWit_zero s)
  refine (extTwLiftSec_eq T α f β (h'.trans hβ) hW' ?_ (extRes (T.U α) N h' s) ?_ _ ?_ ?_).symm
  · intro x hx
    by_cases hxU : x ∈ T.U α
    · exact Or.inl ⟨hx, hxU⟩
    · rcases extWit_cov s (h' hx) with h1 | h1
      · exact absurd h1.2 hxU
      exact Or.inr ⟨h1, hx⟩
  · exact (secRes_secRes N (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_inf_right (T.U α) h')
      (inf_le_inf_right (T.U α) hW') (s.1 : sec R N inf_le_right)).trans z
  · refine (secRes_secRes (M.M β) hβ h' (inf_le_left : W₂ ⊓ T.U α ≤ W₂) _).trans ?_
    refine (secRes_secRes (M.M β) hβ (inf_le_left : W ⊓ T.U α ≤ W)
      (inf_le_inf_right (T.U α) h') _).symm.trans ?_
    rw [(extTwLiftSec_spec T α f β hβ s).1]
    unfold extTwT₀
    exact (M.φ_res α β _ _ (inf_le_inf_right (T.U α) h') _).symm.trans
      (congrArg (M.φ α β _ _) (app_secRes f (inf_le_right : W ⊓ T.U α ≤ T.U α)
        (inf_le_inf_right (T.U α) h') (s.1 : sec R N inf_le_right)).symm)
  · refine (secRes_secRes (M.M β) hβ h' hW' _).trans ?_
    refine (secRes_secRes (M.M β) hβ (extWit_le s)
      (inf_le_left : extWit s ⊓ W₂ ≤ extWit s) _).symm.trans ?_
    rw [(extTwLiftSec_spec T α f β hβ s).2]
    exact map_zero (secResHom R (M.M β) _ _)

/-- Helper: the lift commutes with the gluing (cocycle at `(α, β, γ)`). -/
private theorem extTwLiftSec_comm (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) (β γ : T.ι) {W : Opens X} (hβ : W ≤ T.U β)
    (hγ : W ≤ T.U γ) (s : extSub (T.U α) N W) :
    M.φ β γ hβ hγ (extTwLiftSec T α f β hβ s) =
      extTwLiftSec T α f γ hγ (extTwφ T α N β γ hβ hγ s) := by
  refine (extTwLiftSec_eq T α f γ hγ (extWit_le s) (extWit_cov s) (extTwφ T α N β γ hβ hγ s)
    ?_ _ ?_ ?_)
  · exact (secRes_smul N (inf_le_right : W ⊓ T.U α ≤ T.U α)
      (inf_le_inf_right (T.U α) (extWit_le s)) _ (s.1 : sec R N inf_le_right)).trans (by
        rw [show secRes R N inf_le_right (inf_le_inf_right (T.U α) (extWit_le s))
          (s.1 : sec R N inf_le_right) = 0 from extWit_zero s]
        exact smul_zero _)
  · rw [← M.φ_res, (extTwLiftSec_spec T α f β hβ s).1]
    unfold extTwT₀
    refine (M.cocycle α β γ (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_left.trans hβ)
      (inf_le_left.trans hγ) _).trans ?_
    exact (M.φ_smul α γ _ _ _ _).symm.trans (congrArg (M.φ α γ _ _)
      (app_smul f (inf_le_right : W ⊓ T.U α ≤ T.U α) _ (s.1 : sec R N inf_le_right)).symm)
  · rw [← M.φ_res, (extTwLiftSec_spec T α f β hβ s).2]
    exact map_zero _

/-- Helper: the additive lift on sections of `extTw α N`, component `β`. -/
private def extTwLiftHom (α : T.ι) {N : Mod ((ringOf R).over (T.U α))} {M : TwMod R T.U T.ch}
    (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β) :
    sec R ((extTwObj T α N).M β) hβ →+ sec R (M.M β) hβ :=
  AddMonoidHom.mk' (fun s => extTwLiftSec T α f β hβ s) (extTwLiftSec_add T α f β hβ)

/-- **Z3.l.** The lift `extTw α N ⟶ M` of `f : N ⟶ M_α`. -/
def extTwLift (α : T.ι) {N : Mod ((ringOf R).over (T.U α))} {M : TwMod R T.U T.ch}
    (f : N ⟶ M.M α) : extTwObj T α N ⟶ M where
  f β := homOfSec₀ (P := (extTwObj T α N).M β) (Q := M.M β)
    (fun {_} hβ => extTwLiftHom T α f β hβ)
    (fun {_} hβ r x => extTwLiftSec_smul T α f β hβ r x)
    (fun {_ _} hβ h' x => extTwLiftSec_res T α f β hβ h' x)
  comm β γ _ hβ hγ x := extTwLiftSec_comm T α f β γ hβ hγ x

/-- Z3.l: `extTwLift` on sections (should hold by `rfl`). -/
theorem extTwLift_app (α : T.ι) {N : Mod ((ringOf R).over (T.U α))} {M : TwMod R T.U T.ch}
    (f : N ⟶ M.M α) (β : T.ι) {W : Opens X} (hβ : W ≤ T.U β) (s : extSub (T.U α) N W) :
    (((extTwLift T α f).f β).val.app (ovr hβ)).hom s = extTwLiftSec T α f β hβ s :=
  rfl

/-- Helper: a section over an open equal to `⊥` vanishes. -/
private theorem sec_zero_of_eq_bot {V : Opens X} (F : Mod ((ringOf R).over V)) {W₁ : Opens X}
    (e : W₁ = ⊥) (h : W₁ ≤ V) (t : sec R F h) : t = 0 := by
  subst e
  exact sec_bot_eq_zero F h t

/-- Helper: `s|(W ⊓ U_α)` is a section of `j_! N` over `W` (support closed, witness `⊥`). -/
private theorem extTwUnit_mem (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) {W : Opens X}
    (h : W ≤ T.U α) (s : sec R N h) :
    secRes R N h (inf_le_left : W ⊓ T.U α ≤ W) s ∈ extSub (T.U α) N W :=
  ⟨⊥, bot_le, fun _ hx => Or.inl ⟨hx, h hx⟩,
    sec_zero_of_eq_bot N (bot_inf_eq _) _ _⟩

/-- Helper: the additive map `s ↦ s|(W ⊓ U_α)` into sections of `j_! N`. -/
private def extTwUnitHom (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) {W : Opens X}
    (h : W ≤ T.U α) : sec R N h →+ sec R ((extTwObj T α N).M α) h where
  toFun s := (⟨secRes R N h (inf_le_left : W ⊓ T.U α ≤ W) s, extTwUnit_mem T α N h s⟩ :
    extSub (T.U α) N W)
  map_zero' := Subtype.ext (map_zero (secResHom R N h (inf_le_left : W ⊓ T.U α ≤ W)))
  map_add' x y := Subtype.ext (map_add (secResHom R N h (inf_le_left : W ⊓ T.U α ≤ W)) x y)

/-- **Z3.l.** The unit `N ⟶ (extTw α N)_α`, `s ↦ s|(W ⊓ U_α)` (support condition with witness
`⊥`). -/
def extTwUnit (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) : N ⟶ (extTwObj T α N).M α :=
  homOfSec₀ (P := N) (Q := (extTwObj T α N).M α) (fun {_} h => extTwUnitHom T α N h)
    (fun {W} h r x => Subtype.ext (secRes_smul N h (inf_le_left : W ⊓ T.U α ≤ W) r x))
    (fun {W W'} h h' x => Subtype.ext
      ((secRes_secRes N h h' (inf_le_left : W' ⊓ T.U α ≤ W') x).trans
        (secRes_secRes N h (inf_le_left : W ⊓ T.U α ≤ W)
          (inf_le_inf_right (T.U α) h') x).symm))

/-- Z3.l: `extTwUnit` on sections. -/
theorem extTwUnit_app (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) {W : Opens X}
    (h : W ≤ T.U α) (s : sec R N h) :
    (show extSub (T.U α) N W from ((extTwUnit T α N).val.app (ovr h)).hom s).1 =
      secRes R N h (inf_le_left : W ⊓ T.U α ≤ W) s :=
  rfl

/-- **Z3.l.** The lift recovers `f` through the unit. -/
theorem extTwUnit_comp_lift (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) :
    extTwUnit T α N ≫ (extTwLift T α f).f α = f := by
  have key : ∀ {W : Opens X} (hW : W ≤ T.U α) (x : sec R N hW),
      ((extTwUnit T α N ≫ (extTwLift T α f).f α).val.app (ovr hW)).hom x =
        (f.val.app (ovr hW)).hom x := by
    intro W hW x
    refine sec_ext_of_cover hW (M.M α) (fun _ : Unit => W ⊓ T.U α) (fun _ => inf_le_left)
      (fun y hy => le_iSup (fun _ : Unit => W ⊓ T.U α) () ⟨hy, hW hy⟩) _ _ ?_
    intro _
    refine (extTwLiftSec_res_inf T α f α hW (extTwUnitHom T α N hW x)).trans ?_
    rw [M.φ_self]
    exact app_secRes f hW (inf_le_left : W ⊓ T.U α ≤ W) x
  ext Y x
  exact key (leOfHom Y.unop.hom) x

/-- Helper: the gluing of `extTw α N` from `α` is the identity on sections (`ȟ_ααβ = 1`). -/
private theorem extTwφ_self_left (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) (β : T.ι)
    {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β) (y : extSub (T.U α) N W) :
    extTwφ T α N α β hα hβ y = (show sec R ((extTwObj T α N).M β) hβ from y) := by
  refine Subtype.ext ?_
  rw [extTwφ_apply, TwistCocycle.unitRes_normalized T (Or.inl rfl)]
  simp only [Units.val_one]
  exact one_smul (((ringOf R).over (T.U α)).obj.obj (ovr inf_le_right)) _

/-- **Z3.l.** Uniqueness of the lift: a morphism `extTw α N ⟶ M` is the lift of its composite
with the unit (it commutes with the gluing, `ȟ_ααβ = 1`, and kills sections vanishing on `W'`). -/
theorem extTwLift_unit_comp (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (g : extTwObj T α N ⟶ M) :
    extTwLift T α (extTwUnit T α N ≫ g.f α) = g := by
  refine TwMod.hom_ext fun β => ?_
  have key : ∀ {W : Opens X} (hβ : W ≤ T.U β) (s : extSub (T.U α) N W),
      extTwLiftSec T α (extTwUnit T α N ≫ g.f α) β hβ s = ((g.f β).val.app (ovr hβ)).hom s := by
    intro W hβ s
    have z : (secRes R ((extTwObj T α N).M β) hβ (extWit_le s) s :
        extSub (T.U α) N (extWit s)) = 0 := Subtype.ext (extWit_zero s)
    refine (extTwLiftSec_eq T α _ β hβ (extWit_le s) (extWit_cov s) s (extWit_zero s) _ ?_ ?_).symm
    · have hc := g.comm α β (inf_le_right : W ⊓ T.U α ≤ T.U α) (inf_le_left.trans hβ)
        (extTwUnitHom T α N inf_le_right (s.1 : sec R N inf_le_right))
      have hy := extTwφ_self_left T α N β (inf_le_right : W ⊓ T.U α ≤ T.U α)
        (inf_le_left.trans hβ)
        (show extSub (T.U α) N (W ⊓ T.U α) from
          extTwUnitHom T α N inf_le_right (s.1 : sec R N inf_le_right))
      exact (app_secRes (g.f β) hβ (inf_le_left : W ⊓ T.U α ≤ W) s).symm.trans
        ((congrArg ((g.f β).val.app (ovr _)).hom hy.symm).trans hc.symm)
    · refine (app_secRes (g.f β) hβ (extWit_le s) s).symm.trans ?_
      rw [z]
      exact map_zero _
  ext Y s
  exact key (leOfHom Y.unop.hom) s

/-- **Z3.l.** `Hom(extTw α N, M) ≃ Hom(N, M_α)`. -/
def extTwHomEquiv (α : T.ι) (N : Mod ((ringOf R).over (T.U α))) (M : TwMod R T.U T.ch) :
    (extTwObj T α N ⟶ M) ≃ (N ⟶ M.M α) where
  toFun g := extTwUnit T α N ≫ g.f α
  invFun f := extTwLift T α f
  left_inv g := extTwLift_unit_comp T α g
  right_inv f := extTwUnit_comp_lift T α f

/-- Helper: naturality of the unit `N ⟶ (extTw α N)_α` in `N`. -/
private theorem extTwUnit_naturality (α : T.ι) {N' N : Mod ((ringOf R).over (T.U α))}
    (f : N' ⟶ N) :
    f ≫ extTwUnit T α N = extTwUnit T α N' ≫ (extTwMap T α f).f α := by
  have key : ∀ {W : Opens X} (h : W ≤ T.U α) (x : sec R N' h),
      (((f ≫ extTwUnit T α N).val.app (ovr h)).hom x :
        sec R ((extTwObj T α N).M α) h) =
        ((extTwUnit T α N' ≫ (extTwMap T α f).f α).val.app (ovr h)).hom x :=
    fun h x => Subtype.ext (app_secRes f h inf_le_left x).symm
  ext Y x
  exact key (leOfHom Y.unop.hom) x

/-- **Z3.l.** [Căldăraru, §1.2], blueprint-tw C.5. The twisted extension by zero is left adjoint
to the component functor. -/
def extTwAdj (α : T.ι) : extTw T α ⊣ TwMod.comp R T.U T.ch α :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extTwHomEquiv T α
      homEquiv_naturality_left_symm := fun {N' N M} f g => by
        change (N ⟶ M.M α) at g
        show extTwLift T α (f ≫ g) = extTwMap T α f ≫ extTwLift T α g
        have e : extTwUnit T α N' ≫ (extTwMap T α f ≫ extTwLift T α g).f α = f ≫ g := by
          rw [TwMod.comp_f, ← Category.assoc, ← extTwUnit_naturality, Category.assoc]
          exact congrArg (fun k => f ≫ k) (extTwUnit_comp_lift T α g)
        rw [← e]
        exact extTwLift_unit_comp T α _
      homEquiv_naturality_right := fun {N M M'} f g => by
        change (extTwObj T α N ⟶ M) at f
        show extTwUnit T α N ≫ (f ≫ g).f α = (extTwUnit T α N ≫ f.f α) ≫ g.f α
        exact (Category.assoc _ _ _).symm }

/-- **Z3.l.** Blueprint-tw C.5 (`comp_α` part). The component functor preserves injective
objects: its left adjoint `extTw α` preserves monomorphisms. -/
instance comp_preservesInjectiveObjects (α : T.ι) :
    (TwMod.comp R T.U T.ch α).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (extTwAdj T α)

end Cohesive
