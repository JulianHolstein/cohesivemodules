import Cohesivemodules.Sheaf.Twisted.SecHom

set_option linter.style.header false

/-!
# Z3.h: sub- and quotient objects of twisted sheaves

Blueprint item Z3.h (`blueprint/blueprint-tw.md` §3 C.2′). Kernels and cokernels of twisted
sheaves are built componentwise; their gluing maps are induced morphisms of sheaves on the double
overlaps `Over (U α ⊓ U β)` (`restrOver` is exact). This file turns such data into twisted sheaves:
* `TwMod.glueHom M α β`: the gluing maps of `M` as one morphism of sheaves on `Over (U α ⊓ U β)`;
* `secOfGlue g`: conversely, the section maps of a family `g α β` of such morphisms;
* `TwMod.ofMono M N i g`: if `i α : N α ⟶ M α` are monomorphisms and `g` is compatible with `i`
  and the gluing of `M`, then `(N, secOfGlue g)` is a twisted sheaf (the identity and cocycle
  axioms are inherited, by injectivity of `i` on sections), with `TwMod.homOfMono` to `M`;
* `TwMod.ofEpi M N p g`: dually for epimorphisms `p α : M α ⟶ N α` (the axioms are inherited by
  cancelling `restrOver p`, `sec_eq_of_epi`), with `TwMod.homOfEpi` from `M`;
* `TwMod.liftOfMono`, `TwMod.descOfEpi`: componentwise factorizations through `i` or `p` are
  morphisms of twisted sheaves;
* `TwMod.Hom.glue_comm`: the compatibility of a morphism with the gluing, as an equation of sheaf
  morphisms on `Over (U α ⊓ U β)`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- Z3.h: restriction from `Over U_α` to the double overlap `Over (U_α ⊓ U_β)`. -/
abbrev resL (α β : ι) : Mod ((ringOf R).over (U α)) ⥤ Mod ((ringOf R).over (U α ⊓ U β)) :=
  restrOver (ringOf R) (inf_le_left : U α ⊓ U β ≤ U α)

/-- Z3.h: restriction from `Over U_β` to the double overlap `Over (U_α ⊓ U_β)`. -/
abbrev resR (α β : ι) : Mod ((ringOf R).over (U β)) ⥤ Mod ((ringOf R).over (U α ⊓ U β)) :=
  restrOver (ringOf R) (inf_le_right : U α ⊓ U β ≤ U β)

/-- **Z3.h.** [Căldăraru, Def 1.2.1], blueprint-tw §3 C.2′. The gluing maps `φ α β` of a twisted
sheaf as one morphism of sheaves `M_α|U_αβ ⟶ M_β|U_αβ` on the over-site `Over (U_α ⊓ U_β)`. -/
def TwMod.glueHom (M : TwMod R U ch) (α β : ι) :
    (resL α β).obj (M.M α) ⟶ (resR α β).obj (M.M β) :=
  homOfSec inf_le_left inf_le_right
    (fun hW => M.φ α β (hW.trans inf_le_left) (hW.trans inf_le_right))
    (fun _ r x => M.φ_smul α β _ _ r x) (fun _ h' x => M.φ_res α β _ _ h' x)

variable {N : ∀ α, Mod ((ringOf R).over (U α))}

/-- **Z3.h.** The section maps of a family of sheaf morphisms `g α β : N_α|U_αβ ⟶ N_β|U_αβ`: on
sections over `W ≤ U_α ⊓ U_β`, the component of `g α β` at `W`. -/
def secOfGlue (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α β : ι) {W : Opens X}
    (hα : W ≤ U α) (hβ : W ≤ U β) : sec R (N α) hα →+ sec R (N β) hβ :=
  ((g α β).val.app (ovr (le_inf hα hβ))).hom.toAddMonoidHom

/-- Z3.h: `secOfGlue` is `R(W)`-linear. -/
theorem secOfGlue_smul (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α β : ι)
    {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (r : R.obj.obj (op W)) (x : sec R (N α) hα) :
    secOfGlue g α β hα hβ (toSec R hα r • x) = toSec R hβ r • secOfGlue g α β hα hβ x :=
  ((g α β).val.app (ovr (le_inf hα hβ))).hom.map_smul r x

/-- Z3.h: `secOfGlue` is natural in `W`. -/
theorem secOfGlue_res (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β)) (α β : ι)
    {W W' : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (h' : W' ≤ W) (x : sec R (N α) hα) :
    secOfGlue g α β (h'.trans hα) (h'.trans hβ) (secRes R (N α) hα h' x) =
      secRes R (N β) hβ h' (secOfGlue g α β hα hβ x) :=
  congrArg (fun k => (ModuleCat.Hom.hom k) x) ((g α β).val.naturality
    (Over.homMk (homOfLE h') : Over.mk (homOfLE (le_inf (h'.trans hα) (h'.trans hβ))) ⟶
      Over.mk (homOfLE (le_inf hα hβ))).op)

/-- Z3.h: the section maps of `glueHom` are the gluing maps (rfl). -/
theorem secOfGlue_glueHom (M : TwMod R U ch) (α β : ι) {W : Opens X} (hα : W ≤ U α)
    (hβ : W ≤ U β) (x : sec R (M.M α) hα) :
    secOfGlue M.glueHom α β hα hβ x = M.φ α β hα hβ x := rfl

/-- **Z3.h.** Sections of a commutative square of sheaf morphisms on the double overlaps: if
`resL (p α) ≫ g' α β = g α β ≫ resR (p β)`, then `g' (p x) = p (g x)` on sections. -/
theorem secOfGlue_comm {N' : ∀ α, Mod ((ringOf R).over (U α))}
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β))
    (g' : ∀ α β, (resL α β).obj (N' α) ⟶ (resR α β).obj (N' β)) (p : ∀ α, N α ⟶ N' α)
    (hp : ∀ α β, (resL α β).map (p α) ≫ g' α β = g α β ≫ (resR α β).map (p β)) (α β : ι)
    {W : Opens X} (hα : W ≤ U α) (hβ : W ≤ U β) (x : sec R (N α) hα) :
    secOfGlue g' α β hα hβ (((p α).val.app (ovr hα)).hom x) =
      ((p β).val.app (ovr hβ)).hom (secOfGlue g α β hα hβ x) :=
  congrArg (fun k => (ModuleCat.Hom.hom (k.val.app (ovr (le_inf hα hβ)))) x) (hp α β)

/-- **Z3.h.** The compatibility of a morphism of twisted sheaves with the gluing maps, as an
equation of sheaf morphisms on `Over (U α ⊓ U β)`. -/
theorem TwMod.Hom.glue_comm {M P : TwMod R U ch} (q : M ⟶ P) (α β : ι) :
    (resL α β).map (q.f α) ≫ P.glueHom α β = M.glueHom α β ≫ (resR α β).map (q.f β) := by
  ext Y x
  exact q.comm α β _ _ x

/-- **Z3.h.** [Căldăraru, §1.2], blueprint-tw §3 C.2′. Sub-objects: if `i α : N α ⟶ M_α` are
monomorphisms and the sheaf morphisms `g α β` on the double overlaps satisfy
`g α β ≫ resR (i β) = resL (i α) ≫ M.glueHom α β`, then `N` with the gluing maps `secOfGlue g` is
a twisted sheaf. `φ_self` and the cocycle hold because `i γ` is injective on sections. -/
def TwMod.ofMono (M : TwMod R U ch) (N : ∀ α, Mod ((ringOf R).over (U α)))
    (i : ∀ α, N α ⟶ M.M α) [∀ α, Mono (i α)]
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β))
    (hg : ∀ α β, g α β ≫ (resR α β).map (i β) = (resL α β).map (i α) ≫ M.glueHom α β) :
    TwMod R U ch where
  M := N
  φ := secOfGlue g
  φ_smul := secOfGlue_smul g
  φ_res := secOfGlue_res g
  φ_self := fun α {W} hα x => by
    apply sec_injective_of_mono (i α) hα
    have h1 := secOfGlue_comm g M.glueHom i (fun α β => (hg α β).symm) α α hα hα x
    refine (h1.symm.trans ?_)
    exact M.φ_self α hα _
  cocycle := fun α β γ {W} hα hβ hγ x => by
    apply sec_injective_of_mono (i γ) hγ
    have h1 := secOfGlue_comm g M.glueHom i (fun α β => (hg α β).symm)
    have e1 := h1 β γ hβ hγ (secOfGlue g α β hα hβ x)
    have e2 := h1 α β hα hβ x
    have e3 := h1 α γ hα hγ x
    refine (e1.symm.trans ?_)
    change M.φ β γ hβ hγ (((i β).val.app (ovr hβ)).hom (secOfGlue g α β hα hβ x)) = _
    rw [← e2]
    change M.φ β γ hβ hγ (M.φ α β hα hβ _) = _
    rw [M.cocycle α β γ hα hβ hγ]
    change _ • secOfGlue M.glueHom α γ hα hγ _ = _
    rw [e3]
    exact (((i γ).val.app (ovr hγ)).hom.map_smul _ _).symm

/-- Z3.h: the inclusion `TwMod.ofMono M N i g hg ⟶ M`, with components `i α`. -/
def TwMod.homOfMono (M : TwMod R U ch) (N : ∀ α, Mod ((ringOf R).over (U α)))
    (i : ∀ α, N α ⟶ M.M α) [∀ α, Mono (i α)]
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β))
    (hg : ∀ α β, g α β ≫ (resR α β).map (i β) = (resL α β).map (i α) ≫ M.glueHom α β) :
    M.ofMono N i g hg ⟶ M where
  f := i
  comm α β _ hα hβ x := secOfGlue_comm g M.glueHom i (fun α β => (hg α β).symm) α β hα hβ x

/-- **Z3.h.** A componentwise factorization `h α ≫ i α = q.f α` of a morphism of twisted sheaves
`q : P ⟶ M` through the monomorphisms `i` is a morphism of twisted sheaves `P ⟶ ofMono`. -/
def TwMod.liftOfMono (M : TwMod R U ch) (N : ∀ α, Mod ((ringOf R).over (U α)))
    (i : ∀ α, N α ⟶ M.M α) [∀ α, Mono (i α)]
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β))
    (hg : ∀ α β, g α β ≫ (resR α β).map (i β) = (resL α β).map (i α) ≫ M.glueHom α β)
    {P : TwMod R U ch} (q : P ⟶ M) (h : ∀ α, P.M α ⟶ N α) (hq : ∀ α, h α ≫ i α = q.f α) :
    P ⟶ M.ofMono N i g hg where
  f := h
  comm α β {W} hα hβ x := by
    apply sec_injective_of_mono (i β) hβ
    have e1 := secOfGlue_comm g M.glueHom i (fun α β => (hg α β).symm) α β hα hβ
      (((h α).val.app (ovr hα)).hom x)
    have hqα : ((i α).val.app (ovr hα)).hom (((h α).val.app (ovr hα)).hom x) =
        ((q.f α).val.app (ovr hα)).hom x := by
      rw [← hq α]; rfl
    have hqβ : ((i β).val.app (ovr hβ)).hom (((h β).val.app (ovr hβ)).hom (P.φ α β hα hβ x)) =
        ((q.f β).val.app (ovr hβ)).hom (P.φ α β hα hβ x) := by
      rw [← hq β]; rfl
    exact e1.symm.trans ((congrArg (secOfGlue M.glueHom α β hα hβ) hqα).trans
      ((q.comm α β hα hβ x).trans hqβ.symm))

/-- Z3.h: restriction of sections is semilinear over the restriction of scalars. -/
private theorem secRes_smul' {U : Opens X} (M : Mod ((ringOf R).over U)) {W W' : Opens X}
    (h : W ≤ U) (h' : W' ≤ W) (r : R.obj.obj (op W)) (x : sec R M h) :
    secRes R M h h' (toSec R h r • x) =
      toSec R (h'.trans h) ((R.obj.map (homOfLE h').op).hom r) • secRes R M h h' x :=
  (M.val.map (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans h)) ⟶
    Over.mk (homOfLE h)).op).hom.map_smul r x

/-- Z3.h: restriction of a restricted unit is the unit restricted along the composite. -/
private theorem unitRes_res {V W' W'' : Opens X} (k : W' ≤ V) (h' : W'' ≤ W')
    (c : (R.obj.obj (op V))ˣ) :
    (R.obj.map (homOfLE h').op).hom ((unitRes R k c : R.obj.obj (op W'))) =
      (unitRes R (h'.trans k) c : R.obj.obj (op W'')) := by
  change (R.obj.map (homOfLE h').op).hom ((R.obj.map (homOfLE k).op).hom c) =
    (R.obj.map (homOfLE (h'.trans k)).op).hom c
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- **Z3.h.** [Căldăraru, §1.2], blueprint-tw §3 C.2′. Quotients: if `p α : M_α ⟶ N α` are
epimorphisms and the sheaf morphisms `g α β` on the double overlaps satisfy
`resL (p α) ≫ g α β = M.glueHom α β ≫ resR (p β)`, then `N` with the gluing maps `secOfGlue g` is
a twisted sheaf. `φ_self` and the cocycle hold by `sec_eq_of_epi` (sections of `N α` are only
locally images of sections of `M_α`). -/
def TwMod.ofEpi (M : TwMod R U ch) (N : ∀ α, Mod ((ringOf R).over (U α)))
    (p : ∀ α, M.M α ⟶ N α) [∀ α, Epi (p α)]
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β))
    (hg : ∀ α β, (resL α β).map (p α) ≫ g α β = M.glueHom α β ≫ (resR α β).map (p β)) :
    TwMod R U ch where
  M := N
  φ := secOfGlue g
  φ_smul := secOfGlue_smul g
  φ_res := secOfGlue_res g
  φ_self := fun α {W} hα x =>
    sec_eq_of_epi hα hα (p α)
      (fun {W'} hW' => secOfGlue g α α (hW'.trans hα) (hW'.trans hα))
      (fun {_} _ => AddMonoidHom.id _)
      (fun {_} hW' r y => secOfGlue_smul g α α (hW'.trans hα) (hW'.trans hα) r y)
      (fun {_ _} hW' h' y => secOfGlue_res g α α (hW'.trans hα) (hW'.trans hα) h' y)
      (fun {_} _ _ _ => rfl) (fun {_ _} _ _ _ => rfl)
      (fun {W'} hW' y => by
        have e := secOfGlue_comm M.glueHom g p hg α α (hW'.trans hα) (hW'.trans hα) y
        exact e.trans (congrArg _ (M.φ_self α (hW'.trans hα) y))) x
  cocycle := fun α β γ {W} hα hβ hγ x =>
    sec_eq_of_epi hα hγ (p α)
      (fun {W'} hW' => (secOfGlue g β γ (hW'.trans hβ) (hW'.trans hγ)).comp
        (secOfGlue g α β (hW'.trans hα) (hW'.trans hβ)))
      (fun {W'} hW' => DistribSMul.toAddMonoidHom
        (sec R (N γ) (hW'.trans hγ))
        (toSec R (hW'.trans hγ)
          ((unitRes R (le_inf (le_inf (hW'.trans hα) (hW'.trans hβ)) (hW'.trans hγ))
            (ch α β γ) : R.obj.obj (op W')))) |>.comp
        (secOfGlue g α γ (hW'.trans hα) (hW'.trans hγ)))
      (fun {W'} hW' r y => by
        change secOfGlue g β γ _ _ (secOfGlue g α β _ _ (toSec R _ r • y)) = _
        rw [secOfGlue_smul, secOfGlue_smul]
        rfl)
      (fun {_ _} hW' h' y => by
        change secOfGlue g β γ _ _ (secOfGlue g α β _ _ (secRes R _ _ h' y)) = _
        rw [secOfGlue_res, secOfGlue_res]
        rfl)
      (fun {W'} hW' r y => by
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
        rw [secOfGlue_smul, ← mul_smul, ← mul_smul]
        exact congrArg (· • _) (mul_comm (_ : R.obj.obj (op W')) r))
      (fun {_ _} hW' h' y => by
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
        rw [secOfGlue_res, secRes_smul', unitRes_res])
      (fun {W'} hW' y => by
        have h1 := secOfGlue_comm M.glueHom g p hg
        have e1 := h1 α β (hW'.trans hα) (hW'.trans hβ) y
        have e2 := h1 β γ (hW'.trans hβ) (hW'.trans hγ) (secOfGlue M.glueHom α β _ _ y)
        have e3 := h1 α γ (hW'.trans hα) (hW'.trans hγ) y
        simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
        rw [e1, e2, e3]
        change ((p γ).val.app (ovr (hW'.trans hγ))).hom
          (M.φ β γ _ _ (M.φ α β _ _ y)) = _
        rw [M.cocycle α β γ (hW'.trans hα) (hW'.trans hβ) (hW'.trans hγ) y]
        exact ((p γ).val.app (ovr (hW'.trans hγ))).hom.map_smul _ _) x

/-- Z3.h: the projection `M ⟶ TwMod.ofEpi M N p g hg`, with components `p α`. -/
def TwMod.homOfEpi (M : TwMod R U ch) (N : ∀ α, Mod ((ringOf R).over (U α)))
    (p : ∀ α, M.M α ⟶ N α) [∀ α, Epi (p α)]
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β))
    (hg : ∀ α β, (resL α β).map (p α) ≫ g α β = M.glueHom α β ≫ (resR α β).map (p β)) :
    M ⟶ M.ofEpi N p g hg where
  f := p
  comm α β _ hα hβ x := secOfGlue_comm M.glueHom g p hg α β hα hβ x

/-- **Z3.h.** A componentwise factorization `p α ≫ h α = q.f α` of a morphism of twisted sheaves
`q : M ⟶ P` through the epimorphisms `p` is a morphism of twisted sheaves `ofEpi ⟶ P`. -/
def TwMod.descOfEpi (M : TwMod R U ch) (N : ∀ α, Mod ((ringOf R).over (U α)))
    (p : ∀ α, M.M α ⟶ N α) [∀ α, Epi (p α)]
    (g : ∀ α β, (resL α β).obj (N α) ⟶ (resR α β).obj (N β))
    (hg : ∀ α β, (resL α β).map (p α) ≫ g α β = M.glueHom α β ≫ (resR α β).map (p β))
    {P : TwMod R U ch} (q : M ⟶ P) (h : ∀ α, N α ⟶ P.M α) (hq : ∀ α, p α ≫ h α = q.f α) :
    M.ofEpi N p g hg ⟶ P where
  f := h
  comm α β {W} hα hβ x := by
    have hsq : ∀ α β, (resL α β).map (h α) ≫ P.glueHom α β = g α β ≫ (resR α β).map (h β) :=
      fun α β => by
        rw [← cancel_epi ((resL α β).map (p α)), ← Category.assoc, ← Functor.map_comp, hq α,
          TwMod.Hom.glue_comm q α β, ← Category.assoc, hg α β, Category.assoc,
          ← Functor.map_comp, hq β]
    exact secOfGlue_comm g P.glueHom h hsq α β hα hβ x

end Cohesive
