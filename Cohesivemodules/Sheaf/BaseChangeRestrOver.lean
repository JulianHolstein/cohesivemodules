import Cohesivemodules.Sheaf.BaseChange
import Cohesivemodules.Sheaf.Twisted.SecHom
import Cohesivemodules.Sheaf.Twisted.SecRes

set_option linter.style.header false

/-!
# Z3.l′: base change and restriction between over-sites

Blueprint item Z3.l′ (`blueprint/blueprint-tw.md` §3 C.7′ (a), (b); blueprint §11 v1.20 item 6;
prototype P24). For a map of sheaves of commutative rings `ψ : R ⟶ S` on `X`, base change
`S ⊗ −` (S8.a `sheafBC`) on the over-site of an open `U`:
* `bcUnit ψ M hW`: the unit `η(m) = 1 ⊗ m` on sections over `W ≤ U` (as C7.b's `bcη`), with its
  linearity, naturality and compatibility with morphisms;
* `sheafBCRestrOverIso ψ h M`: `(S|U ⊗ M)|V ≅ S|V ⊗ M|V` for `V ≤ U` (C.7′ (a)), natural in `M`,
  sending `η(m)` to `η(m)`; proof as S8.a's `sheafBCOverIso`, with `Over.map` in place of
  `Over.forget`;
* `sec_eq_of_bcUnit`: section families out of `S ⊗ M` that are linear and natural are determined
  by their values on the `η(m)` (C.7′ (b)).

## Deviations
* None: sections of `sheafBC` are not explicit (sheafification), so they are only used through
  `η` and the adjunction `sheafBC ⊣ restrictScalars`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X]
  {R S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} (ψ : R ⟶ S)

/-! ## The unit `η(m) = 1 ⊗ m` -/

/-- **Z3.l′ (C.7′).** The unit `η : M → S ⊗ M`, `m ↦ 1 ⊗ m`, on sections over `W ≤ U` of a sheaf
of modules `M` on `Over U` (the unit of `sheafBC ⊣ restrictScalars`, as C7.b's `bcη`). -/
def bcUnit {U : Opens X} (M : Mod ((ringOf R).over U)) {W : Opens X} (hW : W ≤ U) :
    sec R M hW →+ sec S ((sheafBC (overHom ψ U)).obj M) hW :=
  (((sheafBCAdj (overHom ψ U)).unit.app M).val.app (ovr hW)).hom.toAddMonoidHom

/-- Z3.l′: `η` is linear along `ψ`: `η(r·m) = ψ(r)·η(m)`. -/
theorem bcUnit_smul {U : Opens X} (M : Mod ((ringOf R).over U)) {W : Opens X} (hW : W ≤ U)
    (r : R.obj.obj (op W)) (m : sec R M hW) :
    bcUnit ψ M hW (toSec R hW r • m) =
      toSec S hW ((ψ.hom.app (op W)).hom r) • bcUnit ψ M hW m :=
  (((sheafBCAdj (overHom ψ U)).unit.app M).val.app (ovr hW)).hom.map_smul (toSec R hW r) m

/-- Z3.l′: `η` commutes with restriction of sections. -/
theorem bcUnit_res {U : Opens X} (M : Mod ((ringOf R).over U)) {W W' : Opens X} (hW : W ≤ U)
    (h' : W' ≤ W) (m : sec R M hW) :
    bcUnit ψ M (h'.trans hW) (secRes R M hW h' m) =
      secRes S ((sheafBC (overHom ψ U)).obj M) hW h' (bcUnit ψ M hW m) := by
  have := PresheafOfModules.naturality_apply ((sheafBCAdj (overHom ψ U)).unit.app M).val
    (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans hW)) ⟶ Over.mk (homOfLE hW)).op m
  exact this

/-- Z3.l′: `η` is natural in `M`: `(S ⊗ f)(η m) = η(f m)`. -/
theorem bcUnit_map {U : Opens X} {M M' : Mod ((ringOf R).over U)} (f : M ⟶ M') {W : Opens X}
    (hW : W ≤ U) (m : sec R M hW) :
    (((sheafBC (overHom ψ U)).map f).val.app (ovr hW)).hom (bcUnit ψ M hW m) =
      bcUnit ψ M' hW ((f.val.app (ovr hW)).hom m) :=
  congrArg (fun k => (k.val.app (ovr hW)).hom m) ((sheafBCAdj (overHom ψ U)).unit.naturality f).symm

/-! ## Base change commutes with restriction between over-sites -/

/-- Z3.l′ helper: the pushforward of presheaves of modules along `Over.map (V ≤ U)`. -/
private abbrev roPush (S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})
    {U V : Opens X} (h : V ≤ U) :=
  PresheafOfModules.pushforward.{0} (F := Over.map (homOfLE h))
      (R := ((ringOf S).over U).obj) (S := ((ringOf S).over V).obj)
      (Sheaf.pushforwardOverMapIso (ringOf S) (homOfLE h)).inv.hom

set_option backward.isDefEq.respectTransparency false in
/-- Z3.l′ helper: base change of presheaves commutes with restriction along `Over.map`
(sectionwise the same object). -/
private def roBCPre {U V : Opens X} (h : V ≤ U) (M : Mod ((ringOf R).over U)) :
    presheafBC (overHom ψ V) ((restrOver (ringOf R) h).obj M).val ≅
      (roPush S h).obj (presheafBC (overHom ψ U) M.val) :=
  PresheafOfModules.isoMk (fun Y => Iso.refl _) (fun Y Z f => by
    refine ModuleCat.ExtendScalars.hom_ext (fun m => ?_)
    rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Z3.l′ helper: the comparison `S|V ⊗ M|V ⟶ (S ⊗ M)|V`, adjoint to the restriction of the unit
of sheafification. -/
private def roBCComp {U V : Opens X} (h : V ≤ U) (M : Mod ((ringOf R).over U)) :
    (sheafBC (overHom ψ V)).obj ((restrOver (ringOf R) h).obj M) ⟶
      (restrOver (ringOf S) h).obj ((sheafBC (overHom ψ U)).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (S.over V)).obj)).symm
    ((roBCPre ψ h M).hom ≫ (roPush S h).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf (S.over U)).obj)).unit.app
        ((presheafBCFunctor (overHom ψ U)).obj M.val)))

-- raised: unifying sheaf-level morphism types (pushforward vs sheafification) is expensive
set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Z3.l′ helper: `roBCComp` is an isomorphism; on underlying sheaves of abelian groups it is
Mathlib's compatibility of pushforward along `Over.map` with sheafification. -/
private instance isIso_roBCComp {U V : Opens X} (h : V ≤ U) (M : Mod ((ringOf R).over U)) :
    IsIso (roBCComp ψ h M) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf (ringOf (S.over V)))]
  have hh := PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm
    (𝟙 (ringOf (S.over V)).obj)
    (P := (presheafBC (overHom ψ V) ((restrOver (ringOf R) h).obj M).val))
    (F := (restrOver (ringOf S) h).obj ((sheafBC (overHom ψ U)).obj M))
    ((roBCPre ψ h M).hom ≫ (roPush S h).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf (S.over U)).obj)).unit.app
        ((presheafBCFunctor (overHom ψ U)).obj M.val)))
  have key : (SheafOfModules.toSheaf (ringOf (S.over V))).map (roBCComp ψ h M) =
      ((Over.map (homOfLE h)).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{0}
        ((Opens.grothendieckTopology X).over V) ((Opens.grothendieckTopology X).over U)).hom.app
          (PresheafOfModules.presheaf (presheafBC (overHom ψ U) M.val)) := by
    refine Sheaf.hom_ext (F := (SheafOfModules.toSheaf (ringOf (S.over V))).obj
      ((sheafBC (overHom ψ V)).obj ((restrOver (ringOf R) h).obj M)))
      (G := (SheafOfModules.toSheaf (ringOf (S.over V))).obj
      ((restrOver (ringOf S) h).obj ((sheafBC (overHom ψ U)).obj M))) ?_
    rw [Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom]
    exact congrArg (fun k => k.hom) hh
  rw [key]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Z3.l′ helper: naturality of `roBCPre` in `M`. -/
private lemma roBCPre_naturality {U V : Opens X} (h : V ≤ U) {M M' : Mod ((ringOf R).over U)}
    (g : M ⟶ M') :
    (roBCPre ψ h M).hom ≫ (roPush S h).map (presheafBCMap (overHom ψ U) g.val) =
      presheafBCMap (overHom ψ V) ((restrOver (ringOf R) h).map g).val ≫ (roBCPre ψ h M').hom := by
  ext Y : 1
  refine ModuleCat.ExtendScalars.hom_ext (fun m => ?_)
  rfl

/-- Z3.l′ helper: a commuting square of two isomorphisms gives the square of their inverses. -/
private lemma ro_iso_square {A : Type*} [Category A] {a b a' b' : A} (c : a ⟶ b) (c' : a' ⟶ b')
    (u : a ⟶ a') (v : b ⟶ b') (h : c ≫ v = u ≫ c') (hc : IsIso c) (hc' : IsIso c') :
    v ≫ inv c' = inv c ≫ u := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Z3.l′ helper: postcomposing a commuting square with a morphism. -/
private lemma ro_comp_square {A : Type*} [Category A] {a b c d e : A} (p : a ⟶ b)
    (pf : b ⟶ c) (k : a ⟶ d) (p' : d ⟶ c) (h2 : p ≫ pf = k ≫ p') (q : c ⟶ e) :
    k ≫ (p' ≫ q) = p ≫ (pf ≫ q) := by
  rw [← Category.assoc, ← h2, Category.assoc]

/-- Z3.l′ helper: a square on the right-adjoint side gives one on the left-adjoint side. -/
private lemma ro_adj_symm_square {A B : Type*} [Category A] [Category B] {L : A ⥤ B}
    {G : B ⥤ A} (adj : L ⊣ G) {P P' : A} {F F' : B} (a : P ⟶ G.obj F) (a' : P' ⟶ G.obj F')
    (k : P ⟶ P') (h : F ⟶ F') (w : a ≫ G.map h = k ≫ a') :
    (adj.homEquiv P F).symm a ≫ h = L.map k ≫ (adj.homEquiv P' F').symm a' := by
  rw [← adj.homEquiv_naturality_right_symm, ← adj.homEquiv_naturality_left_symm, w]

set_option backward.isDefEq.respectTransparency false in
/-- Z3.l′ helper: naturality of the comparison `roBCComp` in `M`. -/
private lemma roBCComp_naturality {U V : Opens X} (h : V ≤ U) {M M' : Mod ((ringOf R).over U)}
    (g : M ⟶ M') :
    roBCComp ψ h M ≫ (restrOver (ringOf S) h).map ((sheafBC (overHom ψ U)).map g) =
      (sheafBC (overHom ψ V)).map ((restrOver (ringOf R) h).map g) ≫ roBCComp ψ h M' := by
  unfold roBCComp
  have e1 : (sheafBC (overHom ψ V)).map ((restrOver (ringOf R) h).map g) =
      (PresheafOfModules.sheafification.{0} (𝟙 (ringOf (S.over V)).obj)).map
        (presheafBCMap (overHom ψ V) ((restrOver (ringOf R) h).map g).val) :=
    rfl
  have e2 : ∀ {P : PresheafOfModules.{0} (ringOf (S.over V)).obj}
      {F : SheafOfModules.{0} (ringOf (S.over V))}
      (a : P ⟶ (PresheafOfModules.restrictScalars.{0} (𝟙 (ringOf (S.over V)).obj)).obj
        ((SheafOfModules.forget _).obj F)),
      (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (S.over V)).obj)).symm a =
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf (S.over V)).obj)).homEquiv
        P F).symm a := fun {P F} a => by
    apply ((PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf (S.over V)).obj)).homEquiv P F).injective
    rw [Equiv.apply_symm_apply, PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
      Equiv.apply_symm_apply]
  rw [e1, e2, e2]
  exact ro_adj_symm_square (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (S.over V)).obj))
    (P := presheafBC (overHom ψ V) ((restrOver (ringOf R) h).obj M).val)
    (P' := presheafBC (overHom ψ V) ((restrOver (ringOf R) h).obj M').val)
    (F := (restrOver (ringOf S) h).obj ((sheafBC (overHom ψ U)).obj M))
    (F' := (restrOver (ringOf S) h).obj ((sheafBC (overHom ψ U)).obj M'))
    ((roBCPre ψ h M).hom ≫ (roPush S h).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf (S.over U)).obj)).unit.app
        ((presheafBCFunctor (overHom ψ U)).obj M.val)))
    ((roBCPre ψ h M').hom ≫ (roPush S h).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf (S.over U)).obj)).unit.app
        ((presheafBCFunctor (overHom ψ U)).obj M'.val)))
    (presheafBCMap (overHom ψ V) ((restrOver (ringOf R) h).map g).val)
    ((restrOver (ringOf S) h).map ((sheafBC (overHom ψ U)).map g)) (by
    have hu := (PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf (S.over U)).obj)).unit.naturality (presheafBCMap (overHom ψ U) g.val)
    have h1 := congrArg (roPush S h).map hu
    rw [Functor.map_comp, Functor.map_comp] at h1
    rw [Functor.id_map] at h1
    exact (congrArg (_ ≫ ·) h1.symm).trans
      (ro_comp_square _ _ _ _ (roBCPre_naturality ψ h g) _).symm)

/-- **Z3.l′ (C.7′ (a)).** For `V ≤ U` and a sheaf of modules `M` on `Over U`, base change commutes
with restriction to `Over V`: `(S|U ⊗ M)|V ≅ S|V ⊗ M|V`. As S8.a's `sheafBCOverIso` (both sides
are sheafifications of the same presheaf), with `Over.map (V ≤ U)` in place of `Over.forget`. -/
def sheafBCRestrOverIso {U V : Opens X} (h : V ≤ U) (M : Mod ((ringOf R).over U)) :
    (restrOver (ringOf S) h).obj ((sheafBC (overHom ψ U)).obj M) ≅
      (sheafBC (overHom ψ V)).obj ((restrOver (ringOf R) h).obj M) :=
  (asIso (roBCComp ψ h M)).symm

set_option backward.isDefEq.respectTransparency false in
open scoped ChangeOfRings TensorProduct in
/-- Z3.l′ helper: the comparison `roBCComp` sends `η(m)` to `η(m)` (adjunction of sheafification
and `toSheafify`). -/
private theorem roBCComp_bcUnit {U V : Opens X} (h : V ≤ U) (M : Mod ((ringOf R).over U))
    {W : Opens X} (hW : W ≤ V) (m : sec R M (hW.trans h)) :
    ((roBCComp ψ h M).val.app (ovr hW)).hom
        (bcUnit ψ ((restrOver (ringOf R) h).obj M) hW m) = bcUnit ψ M (hW.trans h) m := by
  have hg : (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (S.over V)).obj))
      (roBCComp ψ h M) = (roBCPre ψ h M).hom ≫ (roPush S h).map
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf (S.over U)).obj)).unit.app
        ((presheafBCFunctor (overHom ψ U)).obj M.val)) := Equiv.apply_symm_apply _ _
  exact congrArg (fun (k : presheafBC (overHom ψ V) ((restrOver (ringOf R) h).obj M).val ⟶ _) =>
    (k.app (ovr hW)).hom
    ((1 : (S.over V).obj.obj (ovr hW)) ⊗ₜ[(R.over V).obj.obj (ovr hW),
      ((overHom ψ V).hom.app (ovr hW)).hom] (m : sec R ((restrOver (ringOf R) h).obj M) hW) :
      bcObj (overHom ψ V) ((restrOver (ringOf R) h).obj M).val (ovr hW))) hg

/-- **Z3.l′ (C.7′ (a)).** `sheafBCRestrOverIso` sends `η(m)` to `η(m)`: for `W ≤ V ≤ U` and a
section `m` of `M` over `W`, the image of `1 ⊗ m` is `1 ⊗ m`. -/
theorem sheafBCRestrOverIso_bcUnit {U V : Opens X} (h : V ≤ U) (M : Mod ((ringOf R).over U))
    {W : Opens X} (hW : W ≤ V) (m : sec R M (hW.trans h)) :
    (((sheafBCRestrOverIso ψ h M).hom.val.app (ovr hW)).hom (bcUnit ψ M (hW.trans h) m)) =
      bcUnit ψ ((restrOver (ringOf R) h).obj M) hW m :=
  (congrArg (fun z => (((sheafBCRestrOverIso ψ h M).hom).val.app (ovr hW)).hom z)
    (roBCComp_bcUnit ψ h M hW m).symm).trans
    (congrArg (fun k => (k.val.app (ovr hW)).hom
      (bcUnit ψ ((restrOver (ringOf R) h).obj M) hW m)) (IsIso.hom_inv_id (roBCComp ψ h M)))

/-- Z3.l′: naturality of `sheafBCRestrOverIso` in `M`. -/
theorem sheafBCRestrOverIso_hom_naturality {U V : Opens X} (h : V ≤ U)
    {M M' : Mod ((ringOf R).over U)} (f : M ⟶ M') :
    (restrOver (ringOf S) h).map ((sheafBC (overHom ψ U)).map f) ≫
        (sheafBCRestrOverIso ψ h M').hom =
      (sheafBCRestrOverIso ψ h M).hom ≫
        (sheafBC (overHom ψ V)).map ((restrOver (ringOf R) h).map f) :=
  ro_iso_square (roBCComp ψ h M) (roBCComp ψ h M') _ _
    (roBCComp_naturality ψ h f) (isIso_roBCComp ψ h M) (isIso_roBCComp ψ h M')

/-! ## Uniqueness on `η` -/

/-- **Z3.l′ (C.7′ (b)).** Two families of additive maps on sections of `S ⊗ M` over `W' ≤ W`, with
values in a sheaf of `S`-modules `Q`, that are `S(W')`-linear and natural in `W'`, are equal if
they agree on all `η(m)`. Proof: as morphisms on `Over W` (`homOfSec`), transported along
`sheafBCRestrOverIso`, they correspond under `sheafBC ⊣ restrictScalars` to their composites
with `η`. -/
theorem sec_eq_of_bcUnit {U₁ U₂ W : Opens X} (h₁ : W ≤ U₁) (h₂ : W ≤ U₂)
    {M : Mod ((ringOf R).over U₁)} {Q : Mod ((ringOf S).over U₂)}
    (a b : ∀ {W' : Opens X} (hW' : W' ≤ W),
      sec S ((sheafBC (overHom ψ U₁)).obj M) (hW'.trans h₁) →+ sec S Q (hW'.trans h₂))
    (ha_smul : ∀ {W' : Opens X} (hW' : W' ≤ W) (r : S.obj.obj (op W')) x,
      a hW' (toSec S (hW'.trans h₁) r • x) = toSec S (hW'.trans h₂) r • a hW' x)
    (ha_res : ∀ {W' W'' : Opens X} (hW' : W' ≤ W) (h' : W'' ≤ W') x,
      a (h'.trans hW') (secRes S _ (hW'.trans h₁) h' x) = secRes S Q (hW'.trans h₂) h' (a hW' x))
    (hb_smul : ∀ {W' : Opens X} (hW' : W' ≤ W) (r : S.obj.obj (op W')) x,
      b hW' (toSec S (hW'.trans h₁) r • x) = toSec S (hW'.trans h₂) r • b hW' x)
    (hb_res : ∀ {W' W'' : Opens X} (hW' : W' ≤ W) (h' : W'' ≤ W') x,
      b (h'.trans hW') (secRes S _ (hW'.trans h₁) h' x) = secRes S Q (hW'.trans h₂) h' (b hW' x))
    (hab : ∀ {W' : Opens X} (hW' : W' ≤ W) (m : sec R M (hW'.trans h₁)),
      a hW' (bcUnit ψ M (hW'.trans h₁) m) = b hW' (bcUnit ψ M (hW'.trans h₁) m))
    (x : sec S ((sheafBC (overHom ψ U₁)).obj M) h₁) : a (le_refl W) x = b (le_refl W) x := by
  let e := sheafBCRestrOverIso ψ h₁ M
  let A := homOfSec h₁ h₂ a ha_smul ha_res
  let B := homOfSec h₁ h₂ b hb_smul hb_res
  have hinv : ∀ {W' : Opens X} (hW' : W' ≤ W) (m : sec R M (hW'.trans h₁)),
      (e.inv.val.app (ovr hW')).hom
        (bcUnit ψ ((restrOver (ringOf R) h₁).obj M) hW' m) = bcUnit ψ M (hW'.trans h₁) m := by
    intro W' hW' m
    have h1 := sheafBCRestrOverIso_bcUnit ψ h₁ M hW' m
    have h2 := congrArg (fun k => (k.val.app (ovr hW')).hom
      (bcUnit ψ M (hW'.trans h₁) m)) e.hom_inv_id
    exact (congrArg (fun z => (e.inv.val.app (ovr hW')).hom z) h1.symm).trans h2
  have hA : (sheafBCAdj (overHom ψ W)).unit.app ((restrOver (ringOf R) h₁).obj M) ≫
      (SheafOfModules.restrictScalars.{0} (ringHomOf (overHom ψ W))).map (e.inv ≫ A) =
      (sheafBCAdj (overHom ψ W)).unit.app ((restrOver (ringOf R) h₁).obj M) ≫
      (SheafOfModules.restrictScalars.{0} (ringHomOf (overHom ψ W))).map (e.inv ≫ B) := by
    ext Y y
    refine congrArg (fun z => (A.val.app Y).hom z) (hinv (leOfHom Y.unop.hom) y) |>.trans ?_
    refine (hab (leOfHom Y.unop.hom) y).trans ?_
    exact (congrArg (fun z => (B.val.app Y).hom z) (hinv (leOfHom Y.unop.hom) y)).symm
  have h3 : e.inv ≫ A = e.inv ≫ B :=
    ((sheafBCAdj (overHom ψ W)).homEquiv _ _).injective
      (((sheafBCAdj (overHom ψ W)).homEquiv_unit _ _ _).trans
        (hA.trans ((sheafBCAdj (overHom ψ W)).homEquiv_unit _ _ _).symm))
  have h4 : A = B := (Iso.cancel_iso_inv_left e A B).1 h3
  exact congrArg (fun k => (k.val.app (ovr (le_refl W))).hom x) h4

end Cohesive
