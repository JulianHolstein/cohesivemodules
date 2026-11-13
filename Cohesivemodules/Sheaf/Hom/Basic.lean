import Cohesivemodules.Sheaf.Basic
import Cohesivemodules.Sheaf.PerfectDef
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.CategoryTheory.Sites.SheafHom

set_option linter.style.header false

/-!
# S7 (part 1): the Hom sheaf of two sheaves of modules

Blueprint item S7 (§3). For sheaves of modules `M`, `N` over a sheaf of commutative rings `R` on
any site (so that it applies on the over-sites `Over U` of restrictions), the Hom sheaf
`homSheaf hR M N` has sections over `X` the morphisms `M|X ⟶ N|X` (Mathlib's `M.over X`, the
same restriction as `restr`); `R(X)` acts through the target. For complexes `K`, `L`,
`homSheafComplex hR K L` is the complex of sheaves of `R`-modules with
`homSheafComplex(K, L)ⁿ = ∏_{p + n = q} homSheaf (Kᵖ) (L^q)` and Mathlib's sign convention
`δ z = z ≫ d + (-1)^{n+1} d ≫ z` (conventions §2, `CochainComplex.HomComplex.δ`). ✗ in Mathlib
(only the type-valued `presheafHom`).

* S7 the definitions, sections (`homSheaf` over `X` is `M|X ⟶ N|X` by definition), and the
  compatibility with restriction.
* S7.a: the module structure is through the target here; see the deviation below.
* S7.b `homSheafComplex P -` preserves quasi-isomorphisms for `P` strictly perfect.
* S7.c `homSheafComplex C I` is acyclic for `C` acyclic and `I` bounded below with injective terms.

Split from `Sheaf/Hom.lean` for size only (no statement changes): this file holds `IsCommSheaf`,
restriction and the target action on `M|X ⟶ N|X`, the sheaf property (from Mathlib's
`presheafHom_isSheafFor`), `homSheaf`, `homPre`, `homPost`. `hom_ext_pt` is public because the second
part uses it.

## Deviations
* `R` commutative is a hypothesis (`IsCommSheaf R`), not a type class: rings of sections are
  `RingCat`-valued (conventions §7).
* S7.a ("a complex of S-modules via the source") is not formalized; blueprint v1.9
  replaces it by S7.a′, a termwise source action, which is what C3/C4 need.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}}

/-- The sheaf of rings `R` is commutative: all rings of sections are commutative. (General-site
form of `IsComm` of S1.) -/
def IsCommSheaf (R : Sheaf J RingCat.{0}) : Prop :=
  ∀ (X : Cᵒᵖ) (a b : R.obj.obj X), a * b = b * a

/-- **S7.** Restriction along `f : Y ⟶ X` of a morphism `M|X ⟶ N|X`: the component at
`Z ⟶ Y` is the component of `φ` at `Z ⟶ Y ⟶ X` (sections of `M|X` over `Z ⟶ X` are sections
of `M` over `Z`, definitionally). -/
def homRestr {X Y : C} (f : Y ⟶ X) {M N : Mod R} (φ : M.over X ⟶ N.over X) :
    M.over Y ⟶ N.over Y where
  val :=
    { app := fun Z ↦ φ.val.app (op ((Over.map f).obj Z.unop))
      naturality := fun {_ _} g ↦ φ.val.naturality ((Over.map f).map g.unop).op }

@[simp]
lemma homRestr_val_app {X Y : C} (f : Y ⟶ X) {M N : Mod R} (φ : M.over X ⟶ N.over X)
    (Z : (Over Y)ᵒᵖ) : (homRestr f φ).val.app Z = φ.val.app (op ((Over.map f).obj Z.unop)) :=
  rfl

/-- Components of a morphism of restrictions at objects of `Over X` with the same underlying
object and equal structure morphisms agree (up to `HEq`, the types being defeq). -/
private lemma app_heq {X : C} {M N : Mod R} (φ : M.over X ⟶ N.over X) {l : C}
    {r : Discrete PUnit} {h h' : l ⟶ X} (e : h = h') :
    HEq (φ.val.app (op (Comma.mk l r h))) (φ.val.app (op (Comma.mk l r h'))) := by
  subst e; rfl

lemma homRestr_id {X : C} {M N : Mod R} (φ : M.over X ⟶ N.over X) :
    homRestr (𝟙 X) φ = φ := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  obtain ⟨Z⟩ := Z
  obtain ⟨l, r, h⟩ := Z
  exact eq_of_heq (app_heq φ (Category.comp_id h))

lemma homRestr_comp {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) {M N : Mod R}
    (φ : M.over X ⟶ N.over X) : homRestr (g ≫ f) φ = homRestr g (homRestr f φ) := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  obtain ⟨Z⟩ := Z
  obtain ⟨l, r, h⟩ := Z
  exact eq_of_heq (app_heq φ (Category.assoc h g f).symm)

lemma homRestr_add {X Y : C} (f : Y ⟶ X) {M N : Mod R} (φ ψ : M.over X ⟶ N.over X) :
    homRestr f (φ + ψ) = homRestr f φ + homRestr f ψ := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  rfl

/-- The restriction of `r ∈ R(X)` to an object `Z ⟶ X` of the over-site, as a section of the
restricted ring `R.over X`. -/
abbrev overRes {X : C} (r : R.obj.obj (op X)) (Z : (Over X)ᵒᵖ) : (R.over X).obj.obj Z :=
  (R.obj.map Z.unop.hom.op).hom r

/-- **S7.** `r ∈ R(X)` acting on `φ : M|X ⟶ N|X` through the target: `(r • φ)(m) = r|Z • φ(m)`.
`R`-linear because `R` is commutative. -/
def homSmul (hR : IsCommSheaf R) {X : C} {M N : Mod R} (r : R.obj.obj (op X))
    (φ : M.over X ⟶ N.over X) : M.over X ⟶ N.over X where
  val :=
    { app := fun Z ↦ ModuleCat.ofHom (X := (M.over X).val.obj Z) (Y := (N.over X).val.obj Z)
        { toFun := fun (m : (M.over X).val.obj Z) ↦ overRes r Z • φ.val.app Z m
          map_add' := fun x y ↦ by
            simp only [map_add, smul_add]
          map_smul' := fun s x ↦ by
            refine (congrArg _ ((φ.val.app Z).hom.map_smul s x)).trans ?_
            have key : ∀ (a b : ↑((R.over X).obj.obj Z))
                (y : ↑((SheafOfModules.over N X).val.obj Z)), a • b • y = b • a • y :=
              fun a b y ↦ by
                rw [← mul_smul, ← mul_smul]
                exact congrArg (· • y) (hR (op Z.unop.left) a b)
            exact key _ _ _ }
      naturality := fun {Z Z'} g ↦ by
        ext m
        have h1 := congrArg (fun f ↦ ModuleCat.Hom.hom f m) (φ.val.naturality g)
        have h2 : overRes r Z' = (R.over X).obj.map g (overRes r Z) := by
          have := congrArg (fun f ↦ (R.obj.map f.op).hom r) g.unop.w
          simp only [op_comp, Functor.map_comp, RingCat.comp_apply] at this
          exact this.symm
        have h3 := PresheafOfModules.map_smul (N.over X).val g (overRes r Z)
          (φ.val.app Z m)
        have h1' : (φ.val.app Z').hom ((M.over X).val.map g m) =
            (N.over X).val.map g ((φ.val.app Z).hom m) := h1
        have h4 : overRes r Z' • (φ.val.app Z').hom ((M.over X).val.map g m) =
            (N.over X).val.map g (overRes r Z • (φ.val.app Z).hom m) := by
          exact (congrArg (overRes r Z' • ·) h1').trans ((congrArg (· • _) h2).trans h3.symm)
        exact h4 }

/-- Pointwise extensionality for morphisms of restricted sheaves of modules. -/
lemma hom_ext_pt {X : C} {M N : Mod R} {φ ψ : M.over X ⟶ N.over X}
    (h : ∀ (Z : (Over X)ᵒᵖ) (m : (M.over X).val.obj Z),
      (φ.val.app Z).hom m = (ψ.val.app Z).hom m) : φ = ψ := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  ext m
  exact h Z m

/-- Components of `homSmul`. -/
private lemma homSmul_app_apply (hR : IsCommSheaf R) {X : C} {M N : Mod R}
    (r : R.obj.obj (op X)) (φ : M.over X ⟶ N.over X) (Z : (Over X)ᵒᵖ)
    (m : (M.over X).val.obj Z) :
    ((homSmul hR r φ).val.app Z).hom m = overRes r Z • (φ.val.app Z).hom m := rfl

/-- Components of a sum of morphisms. -/
private lemma add_app_apply {X : C} {M N : Mod R} (φ ψ : M.over X ⟶ N.over X)
    (Z : (Over X)ᵒᵖ) (m : (M.over X).val.obj Z) :
    ((φ + ψ).val.app Z).hom m = (φ.val.app Z).hom m + (ψ.val.app Z).hom m := rfl

/-- Components of the zero morphism. -/
private lemma zero_app_apply {X : C} {M N : Mod R}
    (Z : (Over X)ᵒᵖ) (m : (M.over X).val.obj Z) :
    ((0 : M.over X ⟶ N.over X).val.app Z).hom m = 0 := rfl

/-- **S7.** The `R(X)`-module structure on `M|X ⟶ N|X` (through the target). -/
@[instance_reducible]
def homModule (hR : IsCommSheaf R) (X : C) (M N : Mod R) :
    Module (R.obj.obj (op X)) (M.over X ⟶ N.over X) where
  smul := homSmul hR
  one_smul φ := hom_ext_pt fun Z m ↦ by
    have h : overRes (1 : R.obj.obj (op X)) Z = 1 := map_one _
    exact (congrArg (· • _) h).trans (one_smul _ _)
  mul_smul r s φ := hom_ext_pt fun Z m ↦ by
    have h : overRes (r * s) Z = overRes r Z * overRes s Z := map_mul _ _ _
    exact (congrArg (· • _) h).trans (mul_smul _ _ _)
  smul_zero r := hom_ext_pt fun Z m ↦ by
    have h : overRes r Z • (0 : ↑((N.over X).val.obj Z)) = 0 := smul_zero _
    exact h
  smul_add r φ ψ := hom_ext_pt fun Z m ↦ by
    exact smul_add (overRes r Z) ((φ.val.app Z).hom m) ((ψ.val.app Z).hom m)
  add_smul r s φ := hom_ext_pt fun Z m ↦ by
    have h : overRes (r + s) Z = overRes r Z + overRes s Z := map_add _ _ _
    exact (congrArg (· • _) h).trans (add_smul _ _ _)
  zero_smul φ := hom_ext_pt fun Z m ↦ by
    have h : overRes (0 : R.obj.obj (op X)) Z = 0 := map_zero _
    exact (congrArg (· • _) h).trans (zero_smul _ _)

/-- **S7.** The Hom presheaf of abelian groups: `X ↦ (M|X ⟶ N|X)`, restriction `homRestr`. -/
def homAb (M N : Mod R) : Cᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj X := AddCommGrpCat.of (M.over X.unop ⟶ N.over X.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := homRestr f.unop
      map_zero' := hom_ext_pt fun _ _ ↦ rfl
      map_add' := homRestr_add f.unop }
  map_id _ := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ homRestr_id φ)
  map_comp f g := AddCommGrpCat.hom_ext
    (AddMonoidHom.ext fun φ ↦ homRestr_comp f.unop g.unop φ)

/-- The underlying morphism of abelian presheaves on `Over X` of a morphism of restrictions. -/
private def toNatTrans {X : C} {M N : Mod R} (φ : M.over X ⟶ N.over X) :
    (Over.forget X).op ⋙ M.val.presheaf ⟶ (Over.forget X).op ⋙ N.val.presheaf :=
  (PresheafOfModules.toPresheaf _).map φ.val

/-- `toNatTrans` is injective. -/
private lemma toNatTrans_injective {X : C} {M N : Mod R} {φ ψ : M.over X ⟶ N.over X}
    (h : toNatTrans φ = toNatTrans ψ) : φ = ψ :=
  hom_ext_pt fun Z m ↦ congrArg (fun t ↦ AddCommGrpCat.Hom.hom (t.app Z) m) h

/-- `toNatTrans` as a morphism of type-valued presheaves `homAb ⋙ forget ⟶ presheafHom`. -/
private def homAbToHom (M N : Mod R) :
    homAb M N ⋙ forget AddCommGrpCat.{0} ⟶ presheafHom M.val.presheaf N.val.presheaf where
  app X := ↾fun φ ↦ toNatTrans φ
  naturality X Y f := by
    ext φ
    rfl

/-- **S7.** `homAb M N` is a sheaf of abelian groups. -/
private lemma homAb_isSheaf (M N : Mod R) : Presheaf.IsSheaf J (homAb M N) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat.{0}),
    isSheaf_iff_isSheaf_of_type]
  intro X S hS x hx
  have hN : Presieve.IsSheaf J (N.val.presheaf ⋙ forget AddCommGrpCat.{0}) :=
    (isSheaf_iff_isSheaf_of_type J _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat.{0})).1 N.isSheaf)
  have hQ := presheafHom_isSheafFor (F := M.val.presheaf) (G := N.val.presheaf) S
    (fun _ f ↦ ((Presheaf.isSheaf_iff_isLimit J _).1 N.isSheaf _ (J.pullback_stable f hS)).some)
  let xQ : Presieve.FamilyOfElements (presheafHom M.val.presheaf N.val.presheaf) S.arrows :=
    fun Y g hg ↦ toNatTrans (x g hg)
  have hxQ : xQ.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    exact congrArg (fun φ ↦ toNatTrans φ) (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨y, hy, huniq⟩ := hQ xQ hxQ
  have hy' := (PresheafHom.isAmalgamation_iff S xQ hxQ y).1 hy
  have lin : ∀ (Z : Over X) (s : R.obj.obj (op Z.left)) (m : M.val.obj (op Z.left)),
      (y.app (op Z)).hom (s • m) =
        s • (show ↑(N.val.obj (op Z.left)) from (y.app (op Z)).hom m) := by
    intro Z s m
    refine (hN _ (J.pullback_stable Z.hom hS)).isSeparatedFor.ext ?_
    intro W w hw
    have hnat : ∀ m' : ↑(M.val.obj (op Z.left)),
        (N.val.presheaf.map w.op) ((y.app (op Z)).hom m') =
          (y.app (op (Over.mk (w ≫ Z.hom)))).hom (M.val.presheaf.map w.op m') := fun m' ↦
      (congrArg (fun f ↦ f.hom m')
        (y.naturality (Over.homMk w : Over.mk (w ≫ Z.hom) ⟶ Z).op)).symm
    have hyx := hy' W (w ≫ Z.hom) hw
    have hlin : ∀ (r : R.obj.obj (op W)) (n : ↑(M.val.obj (op W))),
        (y.app (op (Over.mk (w ≫ Z.hom)))).hom (r • n) =
          r • (show ↑(N.val.obj (op W)) from (y.app (op (Over.mk (w ≫ Z.hom)))).hom n) :=
      fun r n ↦ by
        refine (congrArg (fun f ↦ AddCommGrpCat.Hom.hom f (r • n)) hyx).trans ?_
        refine (((x (w ≫ Z.hom) hw).val.app (op (Over.mk (𝟙 W)))).hom.map_smul r n).trans ?_
        exact congrArg (fun a : ↑(N.val.obj (op W)) ↦ r • a)
          (congrArg (fun f ↦ AddCommGrpCat.Hom.hom f n) hyx).symm
    have h1 := PresheafOfModules.map_smul M.val w.op s m
    have h2 := PresheafOfModules.map_smul N.val w.op s ((y.app (op Z)).hom m)
    refine (hnat (s • m)).trans ?_
    refine (congrArg (fun a ↦ AddCommGrpCat.Hom.hom
      (y.app (op (Over.mk (w ≫ Z.hom)))) a) h1).trans ?_
    refine (hlin _ _).trans ?_
    refine (congrArg (fun a : ↑(N.val.obj (op W)) ↦ (R.obj.map w.op).hom s • a)
      (hnat m).symm).trans ?_
    exact h2.symm
  let y' : M.over X ⟶ N.over X :=
    ⟨PresheafOfModules.homMk (M₁ := (M.over X).val) (M₂ := (N.over X).val) y
      (fun Z r m ↦ lin Z.unop r m)⟩
  have hy'y : toNatTrans y' = y := rfl
  refine ⟨y', ?_, ?_⟩
  · intro Y g hg
    apply toNatTrans_injective
    exact hy g hg
  · intro z hz
    apply toNatTrans_injective
    exact (huniq (toNatTrans z) (fun Y g hg ↦ congrArg (fun φ ↦ toNatTrans φ) (hz g hg))).trans
      hy'y.symm


/-- **S7. The Hom sheaf** `𝓗om(M, N)`: sections over `X` are the morphisms `M|X ⟶ N|X` of
sheaves of `R.over X`-modules, `R(X)` acting through the target (`R` commutative). -/
def homSheaf (hR : IsCommSheaf R) (M N : Mod R) : Mod R where
  val := @PresheafOfModules.ofPresheaf _ _ _ (homAb M N) (fun X ↦ homModule hR X.unop M N)
    (fun {X Y} f r φ ↦ hom_ext_pt fun Z m ↦ by
      have h : overRes (R.obj.map f r) Z = overRes r ((Over.map f.unop).op.obj Z) := by
        simp only [overRes, Functor.op_obj, Over.map_obj_hom, op_comp, Functor.map_comp,
          RingCat.comp_apply]
        rfl
      exact congrArg (fun a : ↑((R.over Y.unop).obj.obj Z) ↦
        a • (show ↑((N.over Y.unop).val.obj Z) from
          (φ.val.app (op ((Over.map f.unop).obj Z.unop))).hom m)) h.symm)
  isSheaf := homAb_isSheaf M N

/-- **S7.** Sections of `homSheaf hR M N` over `X` are, by definition, the morphisms
`M|X ⟶ N|X`. -/
def homSheafSectionsEquiv (hR : IsCommSheaf R) (M N : Mod R) (X : C) :
    (homSheaf hR M N).val.obj (op X) ≃ (M.over X ⟶ N.over X) :=
  Equiv.refl _

/-- **S7.** Post-composition with `g : N ⟶ N'`: `homSheaf M N ⟶ homSheaf M N'`,
`φ ↦ φ ≫ g|X` on sections over `X`. -/
def homPost (hR : IsCommSheaf R) (M : Mod R) {N N' : Mod R} (g : N ⟶ N') :
    homSheaf hR M N ⟶ homSheaf hR M N' where
  val :=
    { app := fun X ↦ ModuleCat.ofHom (X := (homSheaf hR M N).val.obj X)
        (Y := (homSheaf hR M N').val.obj X)
        { toFun := fun φ ↦ (homSheafSectionsEquiv hR M N' X.unop).symm
            (homSheafSectionsEquiv hR M N X.unop φ ≫ g.over X.unop)
          map_add' := fun φ ψ ↦ hom_ext_pt fun Z m ↦
            map_add ((g.over X.unop).val.app Z).hom _ _
          map_smul' := fun r φ ↦ hom_ext_pt fun Z m ↦
            ((g.over X.unop).val.app Z).hom.map_smul (overRes r Z) _ }
      naturality := fun {X Y} f ↦ by
        ext φ
        exact hom_ext_pt fun Z m ↦ rfl }

/-- **S7.** Pre-composition with `f : M' ⟶ M`: `homSheaf M N ⟶ homSheaf M' N`,
`φ ↦ f|X ≫ φ` on sections over `X`. -/
def homPre (hR : IsCommSheaf R) {M M' : Mod R} (f : M' ⟶ M) (N : Mod R) :
    homSheaf hR M N ⟶ homSheaf hR M' N where
  val :=
    { app := fun X ↦ ModuleCat.ofHom (X := (homSheaf hR M N).val.obj X)
        (Y := (homSheaf hR M' N).val.obj X)
        { toFun := fun φ ↦ (homSheafSectionsEquiv hR M' N X.unop).symm
            (f.over X.unop ≫ homSheafSectionsEquiv hR M N X.unop φ)
          map_add' := fun φ ψ ↦ hom_ext_pt fun Z m ↦ rfl
          map_smul' := fun r φ ↦ hom_ext_pt fun Z m ↦ rfl }
      naturality := fun {X Y} f ↦ by
        ext φ
        exact hom_ext_pt fun Z m ↦ rfl }

end Cohesive
