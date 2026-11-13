import Cohesivemodules.Sheaf.Twisted.SecHom

set_option linter.style.header false

/-!
# Z3.i: calculus of restriction of sections

Blueprint item Z3.i (`blueprint/blueprint-tw.md` §3 C.4′). Restriction of sections of sheaves of
modules on over-sites (`secRes`): additive (`secResHom`), identity along `W ≤ W`, functorial,
semilinear over restriction of scalars, and natural for morphisms of sheaves; restriction of
units (`unitRes`) is compatible with restriction of scalars.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {U : Opens X}

variable (R) in
/-- Z3.i: restriction of sections along `W' ≤ W ≤ U` as an additive map. -/
def secResHom (M : Mod ((ringOf R).over U)) {W W' : Opens X} (h : W ≤ U) (h' : W' ≤ W) :
    sec R M h →+ sec R M (h'.trans h) where
  toFun := secRes R M h h'
  map_zero' := map_zero _
  map_add' := fun x y => map_add _ x y

/-- Z3.i: `secResHom` is `secRes` (rfl). -/
@[simp] theorem secResHom_apply (M : Mod ((ringOf R).over U)) {W W' : Opens X} (h : W ≤ U)
    (h' : W' ≤ W) (x : sec R M h) : secResHom R M h h' x = secRes R M h h' x := rfl

/-- Z3.i: restriction along `W ≤ W` is the identity. -/
theorem secRes_id (M : Mod ((ringOf R).over U)) {W : Opens X} (h : W ≤ U) (h' : W ≤ W)
    (x : sec R M h) : secRes R M h h' x = x := by
  have e : (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans h)) ⟶ Over.mk (homOfLE h)) =
      𝟙 _ := Over.OverMorphism.ext (Subsingleton.elim _ _)
  unfold secRes
  rw [e]
  change (M.val.map (𝟙 _) x : M.val.obj _) = x
  rw [PresheafOfModules.map_id]
  rfl

/-- Z3.i: restriction is functorial. -/
theorem secRes_secRes (M : Mod ((ringOf R).over U)) {W W' W'' : Opens X} (h : W ≤ U)
    (h' : W' ≤ W) (h'' : W'' ≤ W') (x : sec R M h) :
    secRes R M (h'.trans h) h'' (secRes R M h h' x) = secRes R M h (h''.trans h') x := by
  have e : (Over.homMk (homOfLE (h''.trans h')) :
      Over.mk (homOfLE ((h''.trans h').trans h)) ⟶ Over.mk (homOfLE h)) =
      (Over.homMk (homOfLE h'') : Over.mk (homOfLE ((h''.trans h').trans h)) ⟶
        Over.mk (homOfLE (h'.trans h))) ≫
      (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans h)) ⟶ Over.mk (homOfLE h)) :=
    Over.OverMorphism.ext (Subsingleton.elim _ _)
  unfold secRes
  rw [e, op_comp]
  exact (PresheafOfModules.map_comp_apply _ _ _ _).symm

/-- Z3.i: restriction is semilinear: `r • x` restricts to `r|W' • x|W'`. -/
theorem secRes_smul (M : Mod ((ringOf R).over U)) {W W' : Opens X} (h : W ≤ U) (h' : W' ≤ W)
    (r : R.obj.obj (op W)) (x : sec R M h) :
    secRes R M h h' (toSec R h r • x) =
      toSec R (h'.trans h) ((R.obj.map (homOfLE h').op).hom r) • secRes R M h h' x :=
  (M.val.map (Over.homMk (homOfLE h') : Over.mk (homOfLE (h'.trans h)) ⟶
    Over.mk (homOfLE h)).op).hom.map_smul r x

/-- Z3.i: morphisms of sheaves of modules commute with restriction of sections. -/
theorem app_secRes {M N : Mod ((ringOf R).over U)} (g : M ⟶ N) {W W' : Opens X} (h : W ≤ U)
    (h' : W' ≤ W) (x : sec R M h) :
    (g.val.app (ovr (h'.trans h))).hom (secRes R M h h' x) =
      secRes R N h h' ((g.val.app (ovr h)).hom x) := by
  have := (PresheafOfModules.naturality_apply g.val (Over.homMk (homOfLE h') :
    Over.mk (homOfLE (h'.trans h)) ⟶ Over.mk (homOfLE h)).op x)
  exact this

/-- Z3.i: morphisms of sheaves of modules are `R(W)`-linear on sections. -/
theorem app_smul {M N : Mod ((ringOf R).over U)} (g : M ⟶ N) {W : Opens X} (h : W ≤ U)
    (r : R.obj.obj (op W)) (x : sec R M h) :
    (g.val.app (ovr h)).hom (toSec R h r • x) = toSec R h r • (g.val.app (ovr h)).hom x :=
  (g.val.app (ovr h)).hom.map_smul r x

/-- Z3.i: restricting a restricted unit is restricting it in one step. -/
theorem unitRes_res {V W W' : Opens X} (k : W ≤ V) (h' : W' ≤ W) (c : (R.obj.obj (op V))ˣ) :
    (R.obj.map (homOfLE h').op).hom (unitRes R k c : R.obj.obj (op W)) =
      (unitRes R (h'.trans k) c : R.obj.obj (op W')) := by
  change (R.obj.map (homOfLE h').op).hom ((R.obj.map (homOfLE k).op).hom c) =
    (R.obj.map (homOfLE (h'.trans k)).op).hom c
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end Cohesive
