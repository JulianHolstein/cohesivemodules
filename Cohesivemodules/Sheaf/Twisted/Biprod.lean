import Cohesivemodules.Sheaf.Twisted.SubQuot
import Cohesivemodules.Sheaf.Twisted.Preadditive

set_option linter.style.header false

/-!
# Z3.h: zero object and binary biproducts of twisted sheaves

Blueprint item Z3.h (`blueprint/blueprint-tw.md` §3 C.3). Both are componentwise:
* `TwMod.zeroObj`: components `0`, gluing maps `0`;
* `TwMod.biprodObj M N`: components `M_α ⊞ N_α`; the gluing map on `Over (U_α ⊓ U_β)` is
  `biprod.map (M.glueHom α β) (N.glueHom α β)` transported along `restrOver` (an additive functor,
  so it preserves biproducts); the axioms hold because the two projections are jointly injective on
  sections (`sec_biprod_ext`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite ZeroObject

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- Z3.h: restriction between over-sites preserves binary biproducts (it is additive). -/
instance restrOver_preservesBinaryBiproducts {U₀ V : Opens X} (h : V ≤ U₀) :
    PreservesBinaryBiproducts (restrOver (ringOf R) h) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- Z3.h: the two projections of a biproduct of sheaves of modules are jointly injective on
sections (`fst ≫ inl + snd ≫ inr = 𝟙`). -/
theorem sec_biprod_ext {V : Opens X} {A B : Mod ((ringOf R).over V)} {W : Opens X} (h : W ≤ V)
    {y z : sec R (A ⊞ B) h}
    (h₁ : ((biprod.fst : A ⊞ B ⟶ A).val.app (ovr h)).hom y =
      ((biprod.fst : A ⊞ B ⟶ A).val.app (ovr h)).hom z)
    (h₂ : ((biprod.snd : A ⊞ B ⟶ B).val.app (ovr h)).hom y =
      ((biprod.snd : A ⊞ B ⟶ B).val.app (ovr h)).hom z) : y = z := by
  have key : ∀ w : sec R (A ⊞ B) h, w =
      ((biprod.inl : A ⟶ A ⊞ B).val.app (ovr h)).hom
        (((biprod.fst : A ⊞ B ⟶ A).val.app (ovr h)).hom w) +
      ((biprod.inr : B ⟶ A ⊞ B).val.app (ovr h)).hom
        (((biprod.snd : A ⊞ B ⟶ B).val.app (ovr h)).hom w) := fun w => by
    have e := congrArg (fun k : A ⊞ B ⟶ A ⊞ B => (k.val.app (ovr h)).hom w)
      (biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (A ⊞ B))
    refine e.symm.trans ?_
    exact app_add h _ _ w
  rw [key y, key z, h₁, h₂]

/-- Z3.h: any two sections of a zero object of sheaves of modules are equal. -/
private theorem sec_zero_eq {V : Opens X} {W : Opens X} (h : W ≤ V)
    (x y : sec R (0 : Mod ((ringOf R).over V)) h) : x = y :=
  (sec_eq_zero_of_isZero (isZero_zero _) h x).trans (sec_eq_zero_of_isZero (isZero_zero _) h y).symm

namespace TwMod

variable (R U ch) in
/-- **Z3.h.** The zero twisted sheaf: components `0`, gluing maps `0`. -/
def zeroObj : TwMod R U ch where
  M _ := 0
  φ _ _ _ _ _ := 0
  φ_smul := fun _ _ _ _ _ _ _ => sec_zero_eq _ _ _
  φ_res := fun _ _ _ _ _ _ _ _ => sec_zero_eq _ _ _
  φ_self := fun _ _ _ _ => sec_zero_eq _ _ _
  cocycle := fun _ _ _ _ _ _ _ _ => sec_zero_eq _ _ _

/-- **Z3.h.** `zeroObj` is a zero object (all components are zero objects). -/
theorem isZero_zeroObj : IsZero (zeroObj R U ch) :=
  ⟨fun M => ⟨⟨(0 : zeroObj R U ch ⟶ M)⟩, fun _ => TwMod.hom_ext fun α =>
      IsZero.eq_of_src (isZero_zero (Mod ((ringOf R).over (U α)))) _ _⟩,
   fun M => ⟨⟨(0 : M ⟶ zeroObj R U ch)⟩, fun _ => TwMod.hom_ext fun α =>
      IsZero.eq_of_tgt (isZero_zero (Mod ((ringOf R).over (U α)))) _ _⟩⟩

/-- Z3.h: twisted sheaves have a zero object. -/
instance : HasZeroObject (TwMod R U ch) :=
  ⟨⟨zeroObj R U ch, isZero_zeroObj⟩⟩

section mapBiprod

variable {U₀ V : Opens X} (h : V ≤ U₀) (A B : Mod ((ringOf R).over U₀))

/-- Z3.h: `mapBiprod.hom` followed by the first projection. -/
private theorem mapBiprod_hom_fst :
    ((restrOver (ringOf R) h).mapBiprod A B).hom ≫ biprod.fst =
      (restrOver (ringOf R) h).map biprod.fst := by
  rw [Functor.mapBiprod_hom]; simp only [biprod.lift_fst]

/-- Z3.h: `mapBiprod.hom` followed by the second projection. -/
private theorem mapBiprod_hom_snd :
    ((restrOver (ringOf R) h).mapBiprod A B).hom ≫ biprod.snd =
      (restrOver (ringOf R) h).map biprod.snd := by
  rw [Functor.mapBiprod_hom]; simp only [biprod.lift_snd]

/-- Z3.h: the inclusion followed by `mapBiprod.inv`. -/
private theorem inl_mapBiprod_inv :
    biprod.inl ≫ ((restrOver (ringOf R) h).mapBiprod A B).inv =
      (restrOver (ringOf R) h).map biprod.inl := by
  rw [Functor.mapBiprod_inv]; simp only [biprod.inl_desc]

/-- Z3.h: the inclusion followed by `mapBiprod.inv`. -/
private theorem inr_mapBiprod_inv :
    biprod.inr ≫ ((restrOver (ringOf R) h).mapBiprod A B).inv =
      (restrOver (ringOf R) h).map biprod.inr := by
  rw [Functor.mapBiprod_inv]; simp only [biprod.inr_desc]

/-- Z3.h: `mapBiprod.inv` followed by the first projection. -/
private theorem mapBiprod_inv_fst :
    ((restrOver (ringOf R) h).mapBiprod A B).inv ≫ (restrOver (ringOf R) h).map biprod.fst =
      biprod.fst := by
  rw [Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, biprod.inl_fst, ← Functor.map_comp]
    exact CategoryTheory.Functor.map_id _ _
  · simp only [biprod.inr_desc_assoc, biprod.inr_fst, ← Functor.map_comp, Functor.map_zero]

/-- Z3.h: `mapBiprod.inv` followed by the second projection. -/
private theorem mapBiprod_inv_snd :
    ((restrOver (ringOf R) h).mapBiprod A B).inv ≫ (restrOver (ringOf R) h).map biprod.snd =
      biprod.snd := by
  rw [Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, biprod.inl_snd, ← Functor.map_comp, Functor.map_zero]
  · simp only [biprod.inr_desc_assoc, biprod.inr_snd, ← Functor.map_comp]
    exact CategoryTheory.Functor.map_id _ _

/-- Z3.h: the inclusion followed by `mapBiprod.hom`. -/
private theorem map_inl_mapBiprod_hom :
    (restrOver (ringOf R) h).map biprod.inl ≫ ((restrOver (ringOf R) h).mapBiprod A B).hom =
      biprod.inl := by
  rw [Functor.mapBiprod_hom]
  apply biprod.hom_ext
  · simp only [biprod.lift_fst, Category.assoc, ← Functor.map_comp, biprod.inl_fst]
    exact CategoryTheory.Functor.map_id _ _
  · simp only [biprod.lift_snd, Category.assoc, ← Functor.map_comp, biprod.inl_snd,
      Functor.map_zero]

/-- Z3.h: the inclusion followed by `mapBiprod.hom`. -/
private theorem map_inr_mapBiprod_hom :
    (restrOver (ringOf R) h).map biprod.inr ≫ ((restrOver (ringOf R) h).mapBiprod A B).hom =
      biprod.inr := by
  rw [Functor.mapBiprod_hom]
  apply biprod.hom_ext
  · simp only [biprod.lift_fst, Category.assoc, ← Functor.map_comp, biprod.inr_fst,
      Functor.map_zero]
  · simp only [biprod.lift_snd, Category.assoc, ← Functor.map_comp, biprod.inr_snd]
    exact CategoryTheory.Functor.map_id _ _

end mapBiprod

variable (M N : TwMod R U ch)

/-- **Z3.h.** The gluing map of the biproduct on `Over (U_α ⊓ U_β)`: `biprod.map` of the gluing
maps, transported along `restrOver` (`Functor.mapBiprod`). -/
def biprodGlue (α β : ι) :
    (resL α β).obj (M.M α ⊞ N.M α) ⟶ (resR α β).obj (M.M β ⊞ N.M β) :=
  ((resL α β).mapBiprod (M.M α) (N.M α)).hom ≫ biprod.map (M.glueHom α β) (N.glueHom α β) ≫
    ((resR α β).mapBiprod (M.M β) (N.M β)).inv

/-- Z3.h: `biprodGlue` is compatible with the first projections. -/
theorem biprodGlue_fst (α β : ι) :
    biprodGlue M N α β ≫ (resR α β).map biprod.fst =
      (resL α β).map biprod.fst ≫ M.glueHom α β := by
  unfold biprodGlue
  simp only [Category.assoc, mapBiprod_inv_fst, biprod.map_fst]
  rw [← Category.assoc, mapBiprod_hom_fst]

/-- Z3.h: `biprodGlue` is compatible with the second projections. -/
theorem biprodGlue_snd (α β : ι) :
    biprodGlue M N α β ≫ (resR α β).map biprod.snd =
      (resL α β).map biprod.snd ≫ N.glueHom α β := by
  unfold biprodGlue
  simp only [Category.assoc, mapBiprod_inv_snd, biprod.map_snd]
  rw [← Category.assoc, mapBiprod_hom_snd]

/-- Z3.h: `biprodGlue` is compatible with the first inclusions. -/
theorem inl_biprodGlue (α β : ι) :
    (resL α β).map biprod.inl ≫ biprodGlue M N α β =
      M.glueHom α β ≫ (resR α β).map biprod.inl := by
  unfold biprodGlue
  rw [← Category.assoc, map_inl_mapBiprod_hom, biprod.inl_map_assoc, inl_mapBiprod_inv]

/-- Z3.h: `biprodGlue` is compatible with the second inclusions. -/
theorem inr_biprodGlue (α β : ι) :
    (resL α β).map biprod.inr ≫ biprodGlue M N α β =
      N.glueHom α β ≫ (resR α β).map biprod.inr := by
  unfold biprodGlue
  rw [← Category.assoc, map_inr_mapBiprod_hom, biprod.inr_map_assoc, inr_mapBiprod_inv]

/-- **Z3.h.** [Căldăraru, §1.2]. The biproduct of twisted sheaves: components `M_α ⊞ N_α`, gluing
maps induced on sections by `biprodGlue`. -/
def biprodObj : TwMod R U ch where
  M α := M.M α ⊞ N.M α
  φ := secOfGlue (biprodGlue M N)
  φ_smul := secOfGlue_smul _
  φ_res := secOfGlue_res _
  φ_self := fun α {W} hα x => by
    apply sec_biprod_ext hα
    · have e := secOfGlue_comm (biprodGlue M N) M.glueHom (fun _ => biprod.fst)
        (fun α β => (biprodGlue_fst M N α β).symm) α α hα hα x
      exact e.symm.trans (M.φ_self α hα _)
    · have e := secOfGlue_comm (biprodGlue M N) N.glueHom (fun _ => biprod.snd)
        (fun α β => (biprodGlue_snd M N α β).symm) α α hα hα x
      exact e.symm.trans (N.φ_self α hα _)
  cocycle := fun α β γ {W} hα hβ hγ x => by
    apply sec_biprod_ext hγ
    · have e1 := secOfGlue_comm (biprodGlue M N) M.glueHom (fun _ => biprod.fst)
        (fun α β => (biprodGlue_fst M N α β).symm)
      have e2 := e1 β γ hβ hγ (secOfGlue (biprodGlue M N) α β hα hβ x)
      have e3 := e1 α β hα hβ x
      have e4 := e1 α γ hα hγ x
      refine e2.symm.trans ?_
      change M.φ β γ hβ hγ (((biprod.fst : M.M β ⊞ N.M β ⟶ M.M β).val.app (ovr hβ)).hom
        (secOfGlue (biprodGlue M N) α β hα hβ x)) = _
      rw [← e3]
      change M.φ β γ hβ hγ (M.φ α β hα hβ _) = _
      rw [M.cocycle α β γ hα hβ hγ]
      change _ • secOfGlue M.glueHom α γ hα hγ _ = _
      rw [e4]
      exact (((biprod.fst : M.M γ ⊞ N.M γ ⟶ M.M γ).val.app (ovr hγ)).hom.map_smul _ _).symm
    · have e1 := secOfGlue_comm (biprodGlue M N) N.glueHom (fun _ => biprod.snd)
        (fun α β => (biprodGlue_snd M N α β).symm)
      have e2 := e1 β γ hβ hγ (secOfGlue (biprodGlue M N) α β hα hβ x)
      have e3 := e1 α β hα hβ x
      have e4 := e1 α γ hα hγ x
      refine e2.symm.trans ?_
      change N.φ β γ hβ hγ (((biprod.snd : M.M β ⊞ N.M β ⟶ N.M β).val.app (ovr hβ)).hom
        (secOfGlue (biprodGlue M N) α β hα hβ x)) = _
      rw [← e3]
      change N.φ β γ hβ hγ (N.φ α β hα hβ _) = _
      rw [N.cocycle α β γ hα hβ hγ]
      change _ • secOfGlue N.glueHom α γ hα hγ _ = _
      rw [e4]
      exact (((biprod.snd : M.M γ ⊞ N.M γ ⟶ N.M γ).val.app (ovr hγ)).hom.map_smul _ _).symm

/-- Z3.h: the first projection of the biproduct. -/
def biprodFst : biprodObj M N ⟶ M where
  f _ := biprod.fst
  comm α β _ hα hβ x :=
    secOfGlue_comm (biprodGlue M N) M.glueHom (fun _ => biprod.fst)
      (fun α β => (biprodGlue_fst M N α β).symm) α β hα hβ x

/-- Z3.h: the second projection of the biproduct. -/
def biprodSnd : biprodObj M N ⟶ N where
  f _ := biprod.snd
  comm α β _ hα hβ x :=
    secOfGlue_comm (biprodGlue M N) N.glueHom (fun _ => biprod.snd)
      (fun α β => (biprodGlue_snd M N α β).symm) α β hα hβ x

/-- Z3.h: the first inclusion of the biproduct. -/
def biprodInl : M ⟶ biprodObj M N where
  f _ := biprod.inl
  comm α β _ hα hβ x :=
    secOfGlue_comm M.glueHom (biprodGlue M N) (fun _ => biprod.inl)
      (fun α β => inl_biprodGlue M N α β) α β hα hβ x

/-- Z3.h: the second inclusion of the biproduct. -/
def biprodInr : N ⟶ biprodObj M N where
  f _ := biprod.inr
  comm α β _ hα hβ x :=
    secOfGlue_comm N.glueHom (biprodGlue M N) (fun _ => biprod.inr)
      (fun α β => inr_biprodGlue M N α β) α β hα hβ x

/-- Z3.h: the biproduct bicone. -/
def biprodBicone : BinaryBicone M N where
  pt := biprodObj M N
  fst := biprodFst M N
  snd := biprodSnd M N
  inl := biprodInl M N
  inr := biprodInr M N
  inl_fst := TwMod.hom_ext fun _ => biprod.inl_fst
  inl_snd := TwMod.hom_ext fun _ => biprod.inl_snd
  inr_fst := TwMod.hom_ext fun _ => biprod.inr_fst
  inr_snd := TwMod.hom_ext fun _ => biprod.inr_snd

/-- **Z3.h.** The biproduct bicone is a bilimit (`fst ≫ inl + snd ≫ inr = 𝟙`, componentwise). -/
def biprodIsBilimit : (biprodBicone M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (TwMod.hom_ext fun _ => biprod.total)

/-- **Z3.h.** Twisted sheaves have binary biproducts. -/
instance : HasBinaryBiproducts (TwMod R U ch) :=
  ⟨fun M N => HasBinaryBiproduct.mk ⟨biprodBicone M N, biprodIsBilimit M N⟩⟩

end TwMod

end Cohesive
