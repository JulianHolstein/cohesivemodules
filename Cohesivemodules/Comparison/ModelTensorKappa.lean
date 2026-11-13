import Cohesivemodules.Comparison.ModelTensorPair

set_option linter.style.header false

/-!
# C7.d (part 2): the dual-basis maps `σ`, `c` and the iso `κ : a(𝒜⁰ ⊗_O K^p) ≅ F^p`

Blueprint item C7.d (split from `ModelTensor.lean` for size). Auxiliary declarations for
`exists_TC_iso_tensorC`; the `_mdl` lemmas are copies of private lemmas of `Sheaf/BaseChange.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X) (K : CochainComplex (Mod (P.R.over U)) ℤ)

section SigmaC

variable {N0 : ℕ} {m : ℕ → ℕ} (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m)

/-- `γ ↦ γ s_{qj}`, `O(W)`-linear. -/
def σL (q : ℕ) (j : Fin (m q)) (W : Opens X) :
    P.PieceO 0 W →ₗ[P.O.obj.obj (op W)] P.PieceO q W where
  toFun γ := (show P.PieceO q W from
        ((⟨γ.1, γ.2⟩ : ↥(P.D.𝒜 W 0)) • (D W).s q j))
  map_add' x y := by
    show ((⟨(x + y).1, (x + y).2⟩ : ↥(P.D.𝒜 W 0)) • (D W).s q j :
        ↥(GCDga.piece (P.D.𝒜 W) q)) =
      (⟨x.1, x.2⟩ : ↥(P.D.𝒜 W 0)) • (D W).s q j +
        (⟨y.1, y.2⟩ : ↥(P.D.𝒜 W 0)) • (D W).s q j
    rw [← add_smul]
    rfl
  map_smul' r x := by
    have h : (⟨(r • x).1, (r • x).2⟩ : ↥(P.D.𝒜 W 0)) = P.ρ W r * ⟨x.1, x.2⟩ :=
      Subtype.ext rfl
    show ((⟨(r • x).1, (r • x).2⟩ : ↥(P.D.𝒜 W 0)) • (D W).s q j :
        ↥(GCDga.piece (P.D.𝒜 W) q)) =
      P.ρ W r • ((⟨x.1, x.2⟩ : ↥(P.D.𝒜 W 0)) • (D W).s q j)
    rw [h, mul_smul]

/-- `σ_{qj}` on sections over `V`. -/
def σV (q : ℕ) (j : Fin (m q)) (V : (Over U)ᵒᵖ) :
    (P.AqU U 0).val.obj V ⟶ (P.AqU U q).val.obj V :=
  (ModuleCat.ofHom (P.σL D q j V.unop.left) :
    ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.PieceO 0 V.unop.left) ⟶
    ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.PieceO q V.unop.left))

/-- `c_{qj}`, `O(W)`-linear. -/
def cL (q : ℕ) (j : Fin (m q)) (W : Opens X) :
    P.PieceO q W →ₗ[P.O.obj.obj (op W)] P.PieceO 0 W where
  toFun a := (show P.PieceO 0 W from ((D W).c q j a : ↥(P.D.𝒜 W 0)))
  map_add' x y := by
    refine Subtype.ext ?_
    exact congrArg Subtype.val (map_add ((D W).c q j) x y)
  map_smul' r x := by
    refine Subtype.ext ?_
    exact congrArg Subtype.val (map_smul ((D W).c q j) (P.ρ W r)
      (show ↥(GCDga.piece (P.D.𝒜 W) q) from x))

/-- `c_{qj}` on sections over `V`. -/
def cV (q : ℕ) (j : Fin (m q)) (V : (Over U)ᵒᵖ) :
    (P.AqU U q).val.obj V ⟶ (P.AqU U 0).val.obj V :=
  (ModuleCat.ofHom (P.cL D q j V.unop.left) :
    ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.PieceO q V.unop.left) ⟶
    ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.PieceO 0 V.unop.left))

variable (hs : ∀ (V W : Opens X) (h : W ≤ V) q j,
      P.D.res h ((D V).s q j : P.D.A V) = ((D W).s q j : P.D.A W))

include hs in
/-- `σ_{qj}` as a morphism of sheaves of `R|U`-modules. -/
def σSh (q : ℕ) (j : Fin (m q)) : P.AqU U 0 ⟶ P.AqU U q :=
  ⟨{ app := fun V ↦ P.σV U D q j V
     naturality := by
       intro V W f
       refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
       refine Subtype.ext ?_
       obtain ⟨h, hh⟩ : ∃ h : W.unop.left ≤ V.unop.left, h = leOfHom f.unop.left :=
         ⟨leOfHom f.unop.left, rfl⟩
       show P.D.res h (show P.D.A V.unop.left from x.1) *
           ((D W.unop.left).s q j : P.D.A W.unop.left) =
         P.D.res h ((show P.D.A V.unop.left from x.1) *
           ((D V.unop.left).s q j : P.D.A V.unop.left))
       rw [(P.D.res h).map_mul', hs] }⟩

variable (hc : ∀ (V W : Opens X) (h : W ≤ V) (q : ℕ) j (a : ↥(GCDga.piece (P.D.𝒜 V) q))
      (b : ↥(GCDga.piece (P.D.𝒜 W) q)), (b : P.D.A W) = P.D.res h a →
      (D W).c q j b = (P.D.res h).f0 ((D V).c q j a))

include hc in
/-- `c_{qj}` as a morphism of sheaves of `R|U`-modules. -/
def cSh (q : ℕ) (j : Fin (m q)) : P.AqU U q ⟶ P.AqU U 0 :=
  ⟨{ app := fun V ↦ P.cV U D q j V
     naturality := by
       intro V W f
       refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
       refine Subtype.ext ?_
       obtain ⟨h, hh⟩ : ∃ h : W.unop.left ≤ V.unop.left, h = leOfHom f.unop.left :=
         ⟨leOfHom f.unop.left, rfl⟩
       exact congrArg Subtype.val (hc V.unop.left W.unop.left h q j
         (⟨x.1, x.2⟩ : ↥(GCDga.piece (P.D.𝒜 V.unop.left) q))
         (P.resPiece q h ⟨x.1, x.2⟩) rfl) }⟩

include hs hc in
/-- `∑_j c_{qj} ≫ σ_{qj} = 𝟙` on `𝒜^q|U`. -/
theorem sum_cSh_σSh (q : ℕ) :
    ∑ j, P.cSh U D hc q j ≫ P.σSh U D hs q j = 𝟙 (P.AqU U q) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  have hs' : (∑ j, P.cSh U D hc q j ≫ P.σSh U D hs q j).val.app V =
      ∑ j, ((P.cSh U D hc q j ≫ P.σSh U D hs q j).val.app V) :=
    Functor.map_sum (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ V) _ _
  rw [hs']
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
  rw [ModuleCat.hom_sum]
  erw [LinearMap.sum_apply]
  have key := (D V.unop.left).expand q (⟨x.1, x.2⟩ : ↥(GCDga.piece (P.D.𝒜 V.unop.left) q))
  refine Eq.trans ?_ key.symm
  exact (AddSubmonoidClass.coe_finsetSum _ _).trans rfl

end SigmaC

/-- `F^p_K` viewed as a sheaf of `R|U`-modules (restriction of scalars along `ρ`). -/
abbrev RsF (p : ℤ) : Mod (P.R.over U) :=
  (SheafOfModules.restrictScalars.{0} (ringHomOf (overHom P.ρSheaf U))).obj
    ((P.FK U K).X p)

/-- Sections of `F^p_K` over `V` as an `O(V)`-module (through `ρ_V`). -/
def FSecO (p : ℤ) (V : (Over U)ᵒᵖ) : Type := P.FSec U (P.FK U K) p V

instance (p : ℤ) (V : (Over U)ᵒᵖ) : AddCommGroup (P.FSecO U K p V) :=
  inferInstanceAs (AddCommGroup (P.FSec U (P.FK U K) p V))

/-- The identity `FSecO ≃ FSec`. -/
def FSecO.val {p : ℤ} {V : (Over U)ᵒᵖ} (z : P.FSecO U K p V) :
    P.FSec U (P.FK U K) p V := z

/-- `val` is additive (rfl). -/
theorem FSecO.val_add {p : ℤ} {V : (Over U)ᵒᵖ} (x y : P.FSecO U K p V) :
    FSecO.val P U K (x + y) = FSecO.val P U K x + FSecO.val P U K y := rfl

instance (p : ℤ) (V : (Over U)ᵒᵖ) :
    Module (P.O.obj.obj (op V.unop.left)) (P.FSecO U K p V) :=
  Module.compHom (P.FSec U (P.FK U K) p V) (P.ρ V.unop.left)

/-- `val` is `ρ`-semilinear (rfl). -/
theorem FSecO.val_smul {p : ℤ} {V : (Over U)ᵒᵖ} (r : P.O.obj.obj (op V.unop.left))
    (x : P.FSecO U K p V) :
    FSecO.val P U K (r • x) = (P.ρ V.unop.left r) • FSecO.val P U K x := rfl

/-- The bilinear map `(γ, k) ↦ γ • η k` on sections over `V`, `𝒜⁰ ⊗_O K^p → F^p`. -/
def κV (p : ℤ) (V : (Over U)ᵒᵖ) :
    (P.PreT U K 0 p).obj V ⟶ (P.RsF U K p).val.obj V :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (a : (P.AqU U 0).val.obj V) (k : (K.X p).val.obj V) =>
      ((⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k :
        P.FSec U (P.FK U K) p V))
    (fun a a' k => by
      show ((⟨(a + a').1, (a + a').2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k :
          P.FSec U (P.FK U K) p V) =
        (⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k +
          (⟨a'.1, a'.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k
      rw [← add_smul]
      rfl)
    (fun r a k => by
      have h : (⟨(r • a).1, (r • a).2⟩ : ↥(P.D.𝒜 V.unop.left 0)) =
          P.ρ V.unop.left r * ⟨a.1, a.2⟩ := Subtype.ext rfl
      show ((⟨(r • a).1, (r • a).2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k :
          P.FSec U (P.FK U K) p V) =
        P.ρ V.unop.left r • ((⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k)
      rw [h, mul_smul])
    (fun a k k' => by
      show ((⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V (k + k') :
          P.FSec U (P.FK U K) p V) = (⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) •
            P.bcη U K p V k + (⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k'
      rw [map_add, smul_add])
    (fun r a k => by
      have h := (((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val.app V).hom.map_smul r k
      have h2 : P.bcη U K p V (r • k) = (P.ρ V.unop.left r : ↥(P.D.𝒜 V.unop.left 0)) •
          P.bcη U K p V k := h
      show ((⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V (r • k) :
          P.FSec U (P.FK U K) p V) =
        P.ρ V.unop.left r • ((⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k)
      rw [h2, smul_comm])

/-- `κV` on pure tensors. -/
theorem κV_tmul (p : ℤ) (V : (Over U)ᵒᵖ) (a : (P.AqU U 0).val.obj V)
    (k : (K.X p).val.obj V) :
    (P.κV U K p V).hom (a ⊗ₜ k) =
      ((⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k : P.FSec U (P.FK U K) p V) := rfl

/-- `κV` as a morphism of presheaves of modules `𝒜⁰ ⊗_O K^p ⟶ F^p`. -/
def κPre (p : ℤ) :
    P.PreT U K 0 p ⟶ (SheafOfModules.forget _).obj (P.RsF U K p) where
  app V := P.κV U K p V
  naturality {V W} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun a k => ?_
    have hn : P.bcη U K p W ((K.X p).val.map f k) = P.fRes U (P.FK U K) p f (P.bcη U K p V k) :=
      (PresheafOfModules.naturality_apply
        ((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val f k)
    refine Eq.trans (κV_tmul P U K p W _ _) (Eq.trans ?_ (congrArg (P.fRes U (P.FK U K) p f)
      (κV_tmul P U K p V a k)).symm)
    show ((⟨(P.resPiece 0 (leOfHom f.unop.left) a).1, (P.resPiece 0 (leOfHom f.unop.left) a).2⟩ :
        ↥(P.D.𝒜 W.unop.left 0)) • P.bcη U K p W ((K.X p).val.map f k) :
          P.FSec U (P.FK U K) p W) = _
    rw [hn, P.fRes_smul U (P.FK U K) f p]
    rfl

open scoped ChangeOfRings TensorProduct in
/-- `η` is the sheafification unit at `1 ⊗ k`. -/
theorem bcη_eq (p : ℤ) (V : (Over U)ᵒᵖ) (k : (K.X p).val.obj V) :
    P.bcη U K p V k =
      (((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf (P.A0.over U)).obj)).unit.app
        ((presheafBCFunctor (overHom P.ρSheaf U)).obj
          ((SheafOfModules.forget _).obj (K.X p)))).app V).hom
        ((1 : (P.A0.over U).obj.obj V) ⊗ₜ[(P.O.over U).obj.obj V,
          ((overHom P.ρSheaf U).hom.app V).hom] (k : (K.X p).val.obj V)) := rfl

section BCAux

open scoped ChangeOfRings TensorProduct

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R S : Sheaf J CommRingCat.{0}} (φ : R ⟶ S)

-- as in Sheaf/BaseChange.lean (instance path through restrictScalars)
set_option backward.isDefEq.respectTransparency false in
/-- The sheafification unit of `presheafBC` is `S`-linear: on `s ⊗ m` it is `s • unit (1 ⊗ m)`. -/
lemma unit_tmul_mdl (M : PMod R) {X : Cᵒᵖ} (s : S.obj.obj X) (m : secC M X) :
    (((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
        (presheafBC φ M)).app X).hom (s ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m) =
      s • (((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
        (presheafBC φ M)).app X).hom
          ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m) := by
  have e : (s ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m : bcObj φ M X) =
      s • ((1 : S.obj.obj X) ⊗ₜ[R.obj.obj X, (φ.hom.app X).hom] m : bcObj φ M X) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [e]
  exact map_smul _ s _

-- as in Sheaf/BaseChange.lean (instance path through restrictScalars)
set_option backward.isDefEq.respectTransparency false in
/-- The inverse of `sheafificationHomEquiv` is the inverse of the adjunction's `homEquiv`. -/
lemma sheafificationHomEquiv_symm_mdl {P : PresheafOfModules.{0} (ringOf R).obj}
    {F : SheafOfModules.{0} (ringOf R)}
    (g : P ⟶ (PresheafOfModules.restrictScalars (𝟙 (ringOf R).obj)).obj
      ((SheafOfModules.forget (ringOf R)).obj F)) :
    (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf R).obj)).symm g =
      ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).homEquiv P F).symm
        g := by
  refine ((PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf R).obj)).symm_apply_eq).2 ?_
  exact (((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf R).obj)).homEquiv P F
    ).apply_symm_apply g).symm

-- as in Sheaf/BaseChange.lean (instance path through restrictScalars)
set_option backward.isDefEq.respectTransparency false in
/-- Generic form of the iso `a_R(B|_R) ≅ (a_S B)|_R`: the adjoint transpose of
`e.hom ≫ unit` is an isomorphism, for `e : T ≅ B|_R`. -/
lemma isIso_transpose_mdl (M : PMod R) (T : PresheafOfModules.{0} (ringOf R).obj)
    (e : T ≅ (PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj (presheafBC φ M)) :
    IsIso ((PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf R).obj)
      (F := (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj
        ((sheafifyF S).obj (presheafBC φ M)))).symm
      (e.hom ≫ (PresheafOfModules.restrictScalars (ringHomOf φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
          (presheafBC φ M)))) := by
  have h : (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf R).obj)
      (F := (SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj
        ((sheafifyF S).obj (presheafBC φ M)))).symm
      (e.hom ≫ (PresheafOfModules.restrictScalars (ringHomOf φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
          (presheafBC φ M))) =
      (sheafifyF R).map e.hom ≫ rsSheafifyComp φ (presheafBC φ M) :=
    (by
      unfold rsSheafifyComp
      rw [sheafificationHomEquiv_symm_mdl, sheafificationHomEquiv_symm_mdl]
      exact ((PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf R).obj)).homEquiv_naturality_left_symm e.hom
      (show (PresheafOfModules.restrictScalars (ringHomOf φ).hom).obj (presheafBC φ M) ⟶
        (SheafOfModules.forget (ringOf R) ⋙
          PresheafOfModules.restrictScalars (𝟙 (ringOf R).obj)).obj
          ((SheafOfModules.restrictScalars.{0} (ringHomOf φ)).obj
            ((sheafifyF S).obj (presheafBC φ M))) from
        (PresheafOfModules.restrictScalars (ringHomOf φ).hom).map
        ((PresheafOfModules.sheafificationAdjunction.{0} (𝟙 (ringOf S).obj)).unit.app
          (presheafBC φ M)))))
  rw [h]
  have := isIso_rsSheafifyComp φ (presheafBC φ M)
  exact IsIso.comp_isIso

end BCAux

/-- `κPre` is the unit of the sheafification of `presheafBC`, transported along `bcTensorIso`. -/
theorem κPre_eq (p : ℤ) :
    P.κPre U K p = (bcTensorIso (overHom P.ρSheaf U)
      ((SheafOfModules.forget _).obj (K.X p))).inv ≫
      (PresheafOfModules.restrictScalars (ringHomOf (overHom P.ρSheaf U)).hom).map
        ((PresheafOfModules.sheafificationAdjunction.{0}
          (𝟙 (ringOf (P.A0.over U)).obj)).unit.app
          ((presheafBCFunctor (overHom P.ρSheaf U)).obj
            ((SheafOfModules.forget _).obj (K.X p)))) := by
  refine PresheafOfModules.hom_ext fun V => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a k => ?_
  exact (unit_tmul_mdl (overHom P.ρSheaf U) _ a k).symm

/-- The comparison `a(𝒜⁰ ⊗_O K^p) ⟶ F^p` (as `R|U`-modules), induced by `κPre`. -/
def κSh (p : ℤ) :
    ((tensorBifunctor (P.O.over U)).obj (P.AqU U 0)).obj (K.X p) ⟶ P.RsF U K p :=
  (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (P.O.over U)).obj)).symm
    (P.κPre U K p)

/-- `κSh` is an isomorphism (`a_R(B|_R) ≅ (a_S B)|_R`). -/
instance isIso_κSh (p : ℤ) : IsIso (P.κSh U K p) := by
  unfold κSh
  rw [P.κPre_eq U K p]
  exact isIso_transpose_mdl (overHom P.ρSheaf U) ((SheafOfModules.forget _).obj (K.X p)) _
    (bcTensorIso (overHom P.ρSheaf U) ((SheafOfModules.forget _).obj (K.X p))).symm


end PreResolvingData

end Cohesive
