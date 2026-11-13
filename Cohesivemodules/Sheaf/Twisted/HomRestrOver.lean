import Cohesivemodules.Sheaf.Twisted.HomTw
import Cohesivemodules.Sheaf.HomSheafComplex
import Cohesivemodules.Sheaf.RestrOver

set_option linter.style.header false

/-!
# Z3.r: restriction between over-sites commutes with Hom sheaves

Blueprint item Z3.r (`blueprint/blueprint-tw.md` §3 F′ (f)). For `V ≤ U` and sheaves of modules
`P`, `Q` on `Over U`, sections of `homSheaf P Q` over `W ≤ V` (morphisms `P|W ⟶ Q|W`) and of
`homSheaf (P|V) (Q|V)` over `W` are both the `R(W′)`-linear natural section families on `W′ ≤ W`
(F′ (b); sections of `restrOver` are the original sections, P19). Hence:
* `homSheafRestrOverIso : (homSheaf P Q)|V ≅ homSheaf (P|V) (Q|V)`, natural in both variables;
* `homComplexRestrOverIso : 𝓗om(K, L)|V ≅ 𝓗om(K|V, L|V)` for complexes (restriction preserves
  products), natural in `K` and `L`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite
open CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {U V : Opens X} (h : V ≤ U)

section One

variable (P Q : Mod ((ringOf R).over U))

/-- Z3.r: a section of `homSheaf P Q` over `W ≤ V` (a morphism `P|W ⟶ Q|W`) as a section of
`homSheaf (P|V) (Q|V)` over `W`: the same section family. -/
def homRestrOverSec {W : Opens X} (hW : W ≤ V)
    (s : P.over (Over.mk (homOfLE (hW.trans h))) ⟶ Q.over (Over.mk (homOfLE (hW.trans h)))) :
    ((restrOver (ringOf R) h).obj P).over (Over.mk (homOfLE hW)) ⟶
      ((restrOver (ringOf R) h).obj Q).over (Over.mk (homOfLE hW)) :=
  secHomOf hW (fun {_} h' => secApp (hW.trans h) s h')
    (fun h' r x => secApp_smul (hW.trans h) s h' r x)
    (fun h' h'' x => secApp_res (hW.trans h) s h' h'' x)

/-- Z3.r: the inverse of `homRestrOverSec`. -/
def homRestrOverSecInv {W : Opens X} (hW : W ≤ V)
    (s : ((restrOver (ringOf R) h).obj P).over (Over.mk (homOfLE hW)) ⟶
      ((restrOver (ringOf R) h).obj Q).over (Over.mk (homOfLE hW))) :
    P.over (Over.mk (homOfLE (hW.trans h))) ⟶ Q.over (Over.mk (homOfLE (hW.trans h))) :=
  secHomOf (hW.trans h) (fun {_} h' => secApp hW s h')
    (fun h' r x => secApp_smul hW s h' r x)
    (fun h' h'' x => secApp_res hW s h' h'' x)

/-- **Z3.r (F′ (f)).** `(homSheaf P Q)|V ≅ homSheaf (P|V) (Q|V)` on `Over V`: on sections over
`W ≤ V`, the identity of section families (`homRestrOverSec`, inverse `homRestrOverSecInv`). -/
def homSheafRestrOverIso :
    (restrOver (ringOf R) h).obj (homSheaf (isCommSheaf_over U) P Q) ≅
      homSheaf (isCommSheaf_over V) ((restrOver (ringOf R) h).obj P)
        ((restrOver (ringOf R) h).obj Q) where
  hom := homOfSec₀
    (fun {W} hW =>
      { toFun := homRestrOverSec h P Q hW
        map_zero' := by
          exact secHom_ext hW (fun h' x => rfl)
        map_add' := fun a b => by
          exact secHom_ext hW (fun h' x => rfl) })
    (fun hW r x => by
      refine secHom_ext hW (fun h' y => ?_)
      rfl)
    (fun hW h' x => by
      refine secHom_ext (h'.trans hW) (fun h'' y => ?_)
      rfl)
  inv := homOfSec₀
    (fun {W} hW =>
      { toFun := homRestrOverSecInv h P Q hW
        map_zero' := by
          exact secHom_ext (hW.trans h) (fun h' x => rfl)
        map_add' := fun a b => by
          exact secHom_ext (hW.trans h) (fun h' x => rfl) })
    (fun hW r x => by
      refine secHom_ext (hW.trans h) (fun h' y => ?_)
      rfl)
    (fun hW h' x => by
      refine secHom_ext (h'.trans (hW.trans h)) (fun h'' y => ?_)
      rfl)
  hom_inv_id := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro Y
    ext m
    refine secHom_ext (P := P) (Q := Q) (U := U) (W := Y.unop.left) ((leOfHom Y.unop.hom).trans h)
      (fun h' y => ?_)
    rfl
  inv_hom_id := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro Y
    ext m
    refine secHom_ext (leOfHom Y.unop.hom) (fun h' y => ?_)
    rfl

end One

/-- Z3.r: `homSheafRestrOverIso` is natural in the target. -/
theorem homSheafRestrOverIso_naturality_post (P : Mod ((ringOf R).over U))
    {Q Q' : Mod ((ringOf R).over U)} (g : Q ⟶ Q') :
    (restrOver (ringOf R) h).map (homPost (isCommSheaf_over U) P g) ≫
        (homSheafRestrOverIso h P Q').hom =
      (homSheafRestrOverIso h P Q).hom ≫
        homPost (isCommSheaf_over V) ((restrOver (ringOf R) h).obj P)
          ((restrOver (ringOf R) h).map g) := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Y
  ext m
  refine secHom_ext (P := (restrOver (ringOf R) h).obj P) (Q := (restrOver (ringOf R) h).obj Q')
    (U := V) (W := Y.unop.left) (leOfHom Y.unop.hom) (fun h' y => ?_)
  rfl

/-- Z3.r: `homSheafRestrOverIso` is natural in the source. -/
theorem homSheafRestrOverIso_naturality_pre {P P' : Mod ((ringOf R).over U)} (f : P' ⟶ P)
    (Q : Mod ((ringOf R).over U)) :
    (restrOver (ringOf R) h).map (homPre (isCommSheaf_over U) f Q) ≫
        (homSheafRestrOverIso h P' Q).hom =
      (homSheafRestrOverIso h P Q).hom ≫
        homPre (isCommSheaf_over V) ((restrOver (ringOf R) h).map f)
          ((restrOver (ringOf R) h).obj Q) := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Y
  ext m
  refine secHom_ext (P := (restrOver (ringOf R) h).obj P') (Q := (restrOver (ringOf R) h).obj Q)
    (U := V) (W := Y.unop.left) (leOfHom Y.unop.hom) (fun h' y => ?_)
  rfl

/-- Z3.r: termwise restriction of complexes between over-sites. -/
abbrev restrOverC : CochainComplex (Mod ((ringOf R).over U)) ℤ ⥤
    CochainComplex (Mod ((ringOf R).over V)) ℤ :=
  (restrOver (ringOf R) h).mapHomologicalComplex (ComplexShape.up ℤ)

variable (K L : CochainComplex (Mod ((ringOf R).over U)) ℤ)

/-- Z3.r: degree `n` of `homComplexRestrOverIso`: restriction preserves the product
(`restrOver` is a right adjoint), then `homSheafRestrOverIso` on each factor. -/
def homComplexXRestrOverIso (n : ℤ) :
    (restrOver (ringOf R) h).obj (homComplexX (isCommSheaf_over U) K L n) ≅
      homComplexX (isCommSheaf_over V) ((restrOverC h).obj K) ((restrOverC h).obj L) n :=
  PreservesProduct.iso (restrOver (ringOf R) h) _ ≪≫
    Pi.mapIso fun T : Triplet n ↦ homSheafRestrOverIso h (K.X T.p) (L.X T.q)

/-- Z3.r: the factors of `homComplexXRestrOverIso` are `homSheafRestrOverIso`. -/
private theorem homComplexXRestrOverIso_hom_π (n : ℤ) (T : Triplet n) :
    (homComplexXRestrOverIso h K L n).hom ≫
        Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over V) ((restrOver (ringOf R) h).obj
          (K.X T.p)) ((restrOver (ringOf R) h).obj (L.X T.q))) T =
      (restrOver (ringOf R) h).map
          (Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over U) (K.X T.p) (L.X T.q)) T) ≫
        (homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom := by
  rw [homComplexXRestrOverIso, Iso.trans_hom]
  erw [Category.assoc]
  have key : (Pi.mapIso fun T : Triplet n ↦ homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom ≫
      Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over V) ((restrOver (ringOf R) h).obj
        (K.X T.p)) ((restrOver (ringOf R) h).obj (L.X T.q))) T =
      Pi.π (fun T : Triplet n ↦ (restrOver (ringOf R) h).obj
        (homSheaf (isCommSheaf_over U) (K.X T.p) (L.X T.q))) T ≫
        (homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom :=
    Pi.map_π (fun T : Triplet n ↦ (homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom) T
  refine (congrArg (fun z => (PreservesProduct.iso (restrOver (ringOf R) h)
    fun T : Triplet n ↦ homSheaf (isCommSheaf_over U) (K.X T.p) (L.X T.q)).hom ≫ z) key).trans ?_
  rw [PreservesProduct.iso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (piComparison_comp_π (restrOver (ringOf R) h)
      (fun T : Triplet n ↦ homSheaf (isCommSheaf_over U) (K.X T.p) (L.X T.q)) T))

/-- `homComplexXRestrOverIso_hom_π` with the target factor spelled through `restrOverC` (defeq). -/
private theorem homComplexXRestrOverIso_hom_π' (n : ℤ) (T : Triplet n) :
    (homComplexXRestrOverIso h K L n).hom ≫
        Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over V) (((restrOverC h).obj K).X T.p)
          (((restrOverC h).obj L).X T.q)) T =
      (restrOver (ringOf R) h).map
          (Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over U) (K.X T.p) (L.X T.q)) T) ≫
        (homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom :=
  homComplexXRestrOverIso_hom_π h K L n T

/-- Z3.r: `homComplexXRestrOverIso` is compatible with the differentials `homComplexD`. -/
private theorem homComplexD_restrOver (n : ℤ) :
    (restrOver (ringOf R) h).map (homComplexD (isCommSheaf_over U) K L n) ≫
        (homComplexXRestrOverIso h K L (n + 1)).hom =
      (homComplexXRestrOverIso h K L n).hom ≫
        homComplexD (isCommSheaf_over V) ((restrOverC h).obj K) ((restrOverC h).obj L) n := by
  apply Pi.hom_ext
  intro T
  rw [Category.assoc, Category.assoc, homComplexD_π, homComplexXRestrOverIso_hom_π']
  conv_rhs => rw [Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc,
    ← Category.assoc, homComplexXRestrOverIso_hom_π', homComplexXRestrOverIso_hom_π']
  have h1 := homSheafRestrOverIso_naturality_post h (K.X T.p) (L.d (T.p + n) T.q)
  have h2 := homSheafRestrOverIso_naturality_pre h (K.d T.p (T.p + 1)) (L.X T.q)
  erw [← Category.assoc (f := (restrOver (ringOf R) h).map (homComplexD _ K L n)),
    ← Functor.map_comp, homComplexD_π]
  rw [Functor.map_add, Functor.map_units_smul]
  erw [Preadditive.add_comp, Linear.units_smul_comp]
  rw [Functor.map_comp, Functor.map_comp]
  congr 1

/-- **Z3.r (F′ (f)).** `𝓗om(K, L)|V ≅ 𝓗om(K|V, L|V)` as complexes on `Over V`. -/
def homComplexRestrOverIso :
    (restrOverC h).obj (homSheafComplex (isCommSheaf_over U) K L) ≅
      homSheafComplex (isCommSheaf_over V) ((restrOverC h).obj K) ((restrOverC h).obj L) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => homComplexXRestrOverIso h K L n)
    (fun i j hij => by
      obtain rfl : i + 1 = j := hij
      exact ((congrArg (fun z => (restrOver (ringOf R) h).map z ≫ _)
        (homComplex_d (isCommSheaf_over U) K L i)).trans
        ((homComplexD_restrOver h K L i).trans
          (congrArg (fun z => _ ≫ z) (homComplex_d (isCommSheaf_over V) _ _ i).symm))).symm)

/-- Z3.r: the components of `homComplexRestrOverIso` (rfl). -/
theorem homComplexRestrOverIso_hom_f (n : ℤ) :
    (homComplexRestrOverIso h K L).hom.f n = (homComplexXRestrOverIso h K L n).hom := rfl

variable {K L}

/-- **Z3.r.** `homComplexRestrOverIso` is natural in the target. -/
theorem homComplexRestrOverIso_naturality₂ (K : CochainComplex (Mod ((ringOf R).over U)) ℤ)
    {L L' : CochainComplex (Mod ((ringOf R).over U)) ℤ} (g : L ⟶ L') :
    (restrOverC h).map (homComplexMap₂ (isCommSheaf_over U) K g) ≫
        (homComplexRestrOverIso h K L').hom =
      (homComplexRestrOverIso h K L).hom ≫
        homComplexMap₂ (isCommSheaf_over V) ((restrOverC h).obj K) ((restrOverC h).map g) := by
  ext n : 1
  apply Pi.hom_ext
  intro T
  show (restrOver (ringOf R) h).map (Limits.Pi.map _) ≫ (homComplexXRestrOverIso h K L' n).hom ≫
      _ = (homComplexXRestrOverIso h K L n).hom ≫ Limits.Pi.map _ ≫ _
  rw [homComplexXRestrOverIso_hom_π', Limits.Pi.map_π, ← Category.assoc, ← Category.assoc,
    ← Functor.map_comp, Limits.Pi.map_π, Functor.map_comp, Category.assoc,
    homSheafRestrOverIso_naturality_post, homComplexXRestrOverIso_hom_π']
  rfl

/-- **Z3.r.** `homComplexRestrOverIso` is natural in the source. -/
theorem homComplexRestrOverIso_naturality₁ {K K' : CochainComplex (Mod ((ringOf R).over U)) ℤ}
    (f : K' ⟶ K) (L : CochainComplex (Mod ((ringOf R).over U)) ℤ) :
    (restrOverC h).map (homComplexMap₁ (isCommSheaf_over U) f L) ≫
        (homComplexRestrOverIso h K' L).hom =
      (homComplexRestrOverIso h K L).hom ≫
        homComplexMap₁ (isCommSheaf_over V) ((restrOverC h).map f) ((restrOverC h).obj L) := by
  ext n : 1
  apply Pi.hom_ext
  intro T
  show (restrOver (ringOf R) h).map (Limits.Pi.map _) ≫ (homComplexXRestrOverIso h K' L n).hom ≫
      _ = (homComplexXRestrOverIso h K L n).hom ≫ Limits.Pi.map _ ≫ _
  rw [homComplexXRestrOverIso_hom_π', Limits.Pi.map_π, ← Category.assoc, ← Category.assoc,
    ← Functor.map_comp, Limits.Pi.map_π, Functor.map_comp, Category.assoc,
    homSheafRestrOverIso_naturality_pre, homComplexXRestrOverIso_hom_π']
  rfl

end Cohesive
