import Cohesivemodules.Comparison.Perfect
import Cohesivemodules.Comparison.FullyFaithfulAux
import Cohesivemodules.Comparison.FullyFaithfulTop
import Cohesivemodules.Comparison.HomSheaf
import Cohesivemodules.Algebra.BaseChangeExt
import Cohesivemodules.Sheaf.HomAction
import Cohesivemodules.Sheaf.HomAcyclic
import Cohesivemodules.Sheaf.Derived

set_option linter.style.header false

/-!
# C4: J is fully faithful

Blueprint items C3–C4 (§4), [A, Prop 7.2.19], [CHL, Prop 7.4]. For resolving data `D` on a
compact Hausdorff space, `J : Ho(P_A) ⥤ D(O)` is bijective on morphisms.

* `Ψ : ℋ(M₁, M₂) ⟶ 𝓗om(α(M₁), α(M₂))` (blueprint C4 step 2, before composing with `r`): a section
  `χ ∈ ℋ^n(V)` goes, on `W ≤ V` and in source degree `p`, to the base-change extension
  `extAlong (χ|W)` of `χ` restricted to `W` (`b ⊗ (β ⊗ q) ↦ (-1)^{n|b|} b·β·χ(1 ⊗ q)|W`).
* `Ψ_top`: at `V = X`, on `F ∘ φ` for a closed degree-`0` `φ`, `Ψ` is the cocycle of `α(φ)`
  (the compatibility used in step 5).
* Step 3 `quasiIso_Ψ_comp`: for an injective resolution `r : α(M₂) → I`, `Ψ ≫ 𝓗om(α(M₁), r)` is a
  quasi-isomorphism (local, by LL, A10.a, S7.b, S7.c).
* Step 2 `isSoft_homSheafComplex_sheafOf_X` (C3.a(i), S7.a′) and `isSoft_homSh` (C3.a(ii)).
* Step 4 boundedness `exists_isStrictlyGE_ℋ`, `exists_isStrictlyGE_homSheafComplex` (audit G6).
* Global sections of `𝓗om` (audit G4): `exists_homComplex_top_equiv`.
* Step 5 `bijective_J_map`; `full_J`, `faithful_J`.
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X)

/-- The sheaf of rings `O` is commutative (`IsCommSheaf`, needed by S7). -/
theorem isCommSheaf_R : IsCommSheaf P.R :=
  IsComm.isCommSheaf (isComm_ringOf P.O)

variable (M₁ M₂ : CohesiveModule P.𝒜X)

/-- `ℋ^n(V)` membership is `HomAlong` membership along `res_V` (the same condition). -/
theorem mem_homAlong_iff (n : ℤ) {V : Opens X} (h : V ≤ ⊤)
    (χ : M₁.T →ₗ[ℂ] P.TotSec M₂ h) :
    χ ∈ P.homAlong M₁ M₂ n h ↔
      χ ∈ HomAlong (P.D.res h) M₁.toQuasiCohesive M₂.toQuasiCohesive n :=
  Iff.rfl

/-- A section `χ ∈ ℋ^n(V)` restricted to `W ≤ V`, as a map along `res_W`. -/
def homAt (n : ℤ) {V W : Opens X} (hW : W ≤ V)
    (χ : P.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) :
    HomAlong (P.D.res (le_top : W ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n :=
  ⟨(P.homRes M₁ M₂ n le_top hW χ).1,
    (P.mem_homAlong_iff M₁ M₂ n _ _).1 (P.homRes M₁ M₂ n le_top hW χ).2⟩

/-- `extAlong` maps degree `p` to degree `q` for a triplet `p + n = q`. -/
theorem extAlong_mem_totDeg (n : ℤ) (T : Triplet n) {W : Opens X}
    (χ : HomAlong (P.D.res (le_top : W ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n)
    {x : P.TotSec M₁ (le_top : W ≤ ⊤)}
    (hx : x ∈ totDeg (P.D.𝒜 W) (M₁.baseChange (P.D.res le_top)).Q T.p) :
    extAlong χ x ∈ totDeg (P.D.𝒜 W) (M₂.baseChange (P.D.res le_top)).Q T.q := by
  have := (extAlong_mem χ).1 hx
  rwa [T.hpq] at this

/-- `extAlong` commutes with the `O(W)`-action (degree-`0` scalars). -/
theorem extAlong_smulO (n : ℤ) {W : Opens X}
    (χ : HomAlong (P.D.res (le_top : W ≤ ⊤)) M₁.toQuasiCohesive M₂.toQuasiCohesive n)
    (f : P.O.obj.obj (op W)) (x : P.TotSec M₁ (le_top : W ≤ ⊤)) :
    extAlong χ ((P.ρ W f) • x) = (P.ρ W f) • extAlong χ x := by
  have h := (extAlong_mem χ).2 (P.ρ W f).2 x
  simp only [mul_zero, Int.negOnePow_zero, one_smul] at h
  exact h

/-- **C4.** The component of `Ψ(χ)` on `W ≤ V`, from degree `p` to degree `q = p + n`. -/
def ΨW (n : ℤ) (T : Triplet n) {V W : Opens X} (hW : W ≤ V)
    (χ : P.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) :
    P.sheafOfSec M₁ T.p (le_top : W ≤ ⊤) →ₗ[P.O.obj.obj (op W)]
      P.sheafOfSec M₂ T.q (le_top : W ≤ ⊤) where
  toFun x := ⟨extAlong (P.homAt M₁ M₂ n hW χ) x.1,
    P.extAlong_mem_totDeg M₁ M₂ n T (P.homAt M₁ M₂ n hW χ) x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (P.extAlong_smulO M₁ M₂ n (P.homAt M₁ M₂ n hW χ) f x.1)

/-- `ΨW` intertwines `δ`: for `T : Triplet (n + 1)`,
`Ψ(δχ)(x) = 𝕏(Ψ(χ)_{p,p+n}(x)) + (-1)^{n+1} Ψ(χ)_{p+1,q}(𝕏 x)`. -/
theorem ΨW_homδ (n : ℤ) (T : Triplet (n + 1)) {V W : Opens X} (hW : W ≤ V)
    (χ : P.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) (x : P.sheafOfSec M₁ T.p (le_top : W ≤ ⊤)) :
    (P.ΨW M₁ M₂ (n + 1) T hW (P.homδV M₁ M₂ n le_top χ) x).1 =
      (M₂.baseChange (P.D.res (le_top : W ≤ ⊤))).X
          (P.ΨW M₁ M₂ n ⟨T.p, T.p + n, rfl⟩ hW χ x).1 +
        (n + 1).negOnePow •
          (P.ΨW M₁ M₂ n ⟨T.p + 1, T.q, by have := T.hpq; lia⟩ hW χ
            (P.sheafOfDV M₁ T.p le_top x)).1 := by
  have hX : ∀ y : M₁.T, (P.homAt M₁ M₂ (n + 1) hW (P.homδV M₁ M₂ n le_top χ)).1 y =
      ((M₂.toQuasiCohesive.baseChange (P.D.res (le_top : W ≤ ⊤))).X ∘ₗ
          (P.homAt M₁ M₂ n hW χ).1 -
        n.negOnePow • ((P.homAt M₁ M₂ n hW χ).1 ∘ₗ M₁.X)) y := by
    intro y
    refine (map_sub (P.totRes M₂ (le_top : V ≤ ⊤) hW) _ _).trans
      (congrArg₂ (· - ·) (P.X_totRes M₂ le_top hW _).symm ?_)
    change P.totRes M₂ (le_top : V ≤ ⊤) hW (n.negOnePow • χ.1 (M₁.X y)) =
      n.negOnePow • P.totRes M₂ (le_top : V ≤ ⊤) hW (χ.1 (M₁.X y))
    rw [Units.smul_def, Units.smul_def, map_zsmul]
  have h := extAlong_δ (P.homAt M₁ M₂ n hW χ) (P.homAt M₁ M₂ (n + 1) hW (P.homδV M₁ M₂ n le_top χ))
    (fun y => hX y)
  change extAlong (P.homAt M₁ M₂ (n + 1) hW (P.homδV M₁ M₂ n le_top χ)) x.1 = _
  rw [h, δ_eq_mathlib]
  rfl

/-- **C4.** `Ψ(χ)` in the factor `(p, q)`: a morphism `α(M₁)^p|V ⟶ α(M₂)^q|V`. -/
def ΨV (n : ℤ) (T : Triplet n) (V : Opens X) (χ : P.HomSec M₁ M₂ n (le_top : V ≤ ⊤)) :
    ((P.sheafOf M₁).X T.p).over V ⟶ ((P.sheafOf M₂).X T.q).over V :=
  ⟨{ app := fun W ↦ (show ModuleCat.of (P.O.obj.obj (op W.unop.left))
          (P.sheafOfSec M₁ T.p (le_top : W.unop.left ≤ ⊤)) ⟶
        ModuleCat.of (P.O.obj.obj (op W.unop.left)) (P.sheafOfSec M₂ T.q (le_top : W.unop.left ≤ ⊤))
        from ModuleCat.ofHom (P.ΨW M₁ M₂ n T (leOfHom W.unop.hom) χ))
     naturality := by
       intro V' W' f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       change extAlong (P.homAt M₁ M₂ n (leOfHom W'.unop.hom) χ)
           (P.totRes M₁ (le_top : V'.unop.left ≤ ⊤) (leOfHom f.unop.left) x.1) =
         P.totRes M₂ (le_top : V'.unop.left ≤ ⊤) (leOfHom f.unop.left)
           (extAlong (P.homAt M₁ M₂ n (leOfHom V'.unop.hom) χ) x.1)
       exact (totRes_extAlong P M₁ M₂ n (leOfHom f.unop.left)
         (P.homAt M₁ M₂ n (leOfHom V'.unop.hom) χ) (P.homAt M₁ M₂ n (leOfHom W'.unop.hom) χ)
         (fun y => (P.totRes_comp M₂ (le_top : V ≤ ⊤) (leOfHom V'.unop.hom)
           (leOfHom f.unop.left) (χ.1 y)).symm) x.1).symm }⟩

/-- `ΨV` is additive in `χ`. -/
def ΨVAdd (n : ℤ) (T : Triplet n) (V : Opens X) :
    P.HomSec M₁ M₂ n (le_top : V ≤ ⊤) →+
      (((P.sheafOf M₁).X T.p).over V ⟶ ((P.sheafOf M₂).X T.q).over V) where
  toFun := P.ΨV M₁ M₂ n T V
  map_zero' := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    change extAlong (P.homAt M₁ M₂ n (leOfHom W.unop.hom) 0) x.1 = 0
    have h0 : P.homAt M₁ M₂ n (leOfHom W.unop.hom) 0 =
        (0 : HomAlong (P.D.res (le_top : W.unop.left ≤ ⊤)) M₁.toQuasiCohesive
          M₂.toQuasiCohesive n) := Subtype.ext (LinearMap.ext fun y => by
      change P.totRes M₂ (le_top : V ≤ ⊤) (leOfHom W.unop.hom) 0 = 0
      exact map_zero _)
    rw [h0]
    exact LinearMap.congr_fun extAlong_zero x.1
  map_add' χ ψ := by
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    change extAlong (P.homAt M₁ M₂ n (leOfHom W.unop.hom) (χ + ψ)) x.1 =
      extAlong (P.homAt M₁ M₂ n (leOfHom W.unop.hom) χ) x.1 +
        extAlong (P.homAt M₁ M₂ n (leOfHom W.unop.hom) ψ) x.1
    have h0 : P.homAt M₁ M₂ n (leOfHom W.unop.hom) (χ + ψ) =
        P.homAt M₁ M₂ n (leOfHom W.unop.hom) χ + P.homAt M₁ M₂ n (leOfHom W.unop.hom) ψ :=
      Subtype.ext (LinearMap.ext fun y => by
        change P.totRes M₂ (le_top : V ≤ ⊤) (leOfHom W.unop.hom) (χ.1 y + ψ.1 y) =
          P.totRes M₂ (le_top : V ≤ ⊤) (leOfHom W.unop.hom) (χ.1 y) +
            P.totRes M₂ (le_top : V ≤ ⊤) (leOfHom W.unop.hom) (ψ.1 y)
        exact map_add _ _ _)
    rw [h0]
    exact LinearMap.congr_fun (extAlong_add _ _) x.1

/-- **C4.** `Ψ` in degree `n` and factor `(p, q)`: `ℋ^n ⟶ 𝓗om(α(M₁)^p, α(M₂)^q)`. -/
def ΨT (n : ℤ) (T : Triplet n) :
    P.homSh M₁ M₂ n ⟶ homSheaf P.isCommSheaf_R ((P.sheafOf M₁).X T.p) ((P.sheafOf M₂).X T.q) :=
  ⟨PresheafOfModules.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom (P.ΨVAdd M₁ M₂ n T V.unop)
      naturality := by
        intro V' W' f
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun χ => ?_)
        refine hom_ext_pt fun Z x => ?_
        apply Subtype.ext
        change extAlong (P.homAt M₁ M₂ n (leOfHom Z.unop.hom)
            (P.homRes M₁ M₂ n (le_top : unop V' ≤ ⊤) (leOfHom f.unop) χ)) x.1 =
          extAlong (P.homAt M₁ M₂ n ((leOfHom Z.unop.hom).trans (leOfHom f.unop)) χ) x.1
        refine congrArg (fun φ => extAlong φ x.1) (Subtype.ext (LinearMap.ext fun y => ?_))
        exact P.totRes_comp M₂ (le_top : unop V' ≤ ⊤) (leOfHom f.unop) (leOfHom Z.unop.hom)
          (χ.1 y) }
    (fun V r χ => by
      refine hom_ext_pt fun Z x => ?_
      apply Subtype.ext
      change extAlong (P.homAt M₁ M₂ n (leOfHom Z.unop.hom) (r • χ)) x.1 =
        ((P.ρ Z.unop.left ((P.O.obj.map Z.unop.hom.op).hom r) :
          ↥(P.D.𝒜 Z.unop.left 0)) : P.D.A Z.unop.left) •
          extAlong (P.homAt M₁ M₂ n (leOfHom Z.unop.hom) χ) x.1
      refine extAlong_smul0 (P.ρ Z.unop.left ((P.O.obj.map Z.unop.hom.op).hom r)) _ _
        (fun y => ?_) x.1
      change P.totRes M₂ (le_top : unop V ≤ ⊤) (leOfHom Z.unop.hom) (P.ρ (unop V) r • χ.1 y) =
        ((P.ρ Z.unop.left ((P.O.obj.map Z.unop.hom.op).hom r) :
          ↥(P.D.𝒜 Z.unop.left 0)) : P.D.A Z.unop.left) •
          P.totRes M₂ (le_top : unop V ≤ ⊤) (leOfHom Z.unop.hom) (χ.1 y)
      rw [P.totRes_smul0]
      exact congrArg (fun c : ↥(P.D.𝒜 Z.unop.left 0) => (c : P.D.A Z.unop.left) •
        P.totRes M₂ (le_top : unop V ≤ ⊤) (leOfHom Z.unop.hom) (χ.1 y))
        (P.ρ_natural (leOfHom Z.unop.hom) r))⟩

/-- Sections of a sum of morphisms of sheaves of modules. -/
private lemma sheaf_add_app {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {A B : Mod R} (f g : A ⟶ B) (Z : Cᵒᵖ) (s : A.val.obj Z) :
    ((f + g).val.app Z).hom s = (f.val.app Z).hom s + (g.val.app Z).hom s := rfl

/-- Sections of a `ℤˣ`-multiple of a morphism of sheaves of modules. -/
private lemma sheaf_units_app {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {A B : Mod R} (z : ℤˣ) (f : A ⟶ B) (Z : Cᵒᵖ)
    (s : A.val.obj Z) :
    ((z • f).val.app Z).hom s = z • (f.val.app Z).hom s := by
  have h : (SheafOfModules.evaluation.{0} R Z).map ((z : ℤ) • f) =
      (z : ℤ) • (SheafOfModules.evaluation.{0} R Z).map f := Functor.map_zsmul _
  rw [Units.smul_def, Units.smul_def]
  exact congrArg (fun g : A.val.obj Z ⟶ B.val.obj Z ↦ g.hom s) h

/-- `Ψ` commutes with the differentials, in degree `n`. -/
theorem Ψ_comm (n : ℤ) :
    (Limits.Pi.lift fun T : Triplet n ↦ P.ΨT M₁ M₂ n T) ≫
        homComplexD P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂) n =
      P.homD M₁ M₂ n ≫ Limits.Pi.lift fun T : Triplet (n + 1) ↦ P.ΨT M₁ M₂ (n + 1) T := by
  refine Limits.Pi.hom_ext _ _ fun T => ?_
  obtain ⟨p, q, hpq⟩ := T
  obtain rfl : q = p + n + 1 := by lia
  simp only [Category.assoc, homComplexD, Limits.Pi.lift_comp_π, Preadditive.comp_add]
  rw [Linear.comp_units_smul, ← Category.assoc, ← Category.assoc, Limits.Pi.lift_comp_π,
    Limits.Pi.lift_comp_π]
  have e2 : ∀ (M : CohesiveModule P.𝒜X) (i : ℤ), (P.sheafOf M).d i (i + 1) = P.sheafOfD M i :=
    fun M i => CochainComplex.of_d _ _ i
  rw [e2 M₂ (p + n), e2 M₁ p]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun s => ?_
  refine hom_ext_pt fun Z x => ?_
  apply Subtype.ext
  rw [sheaf_add_app, sheaf_units_app]
  set a : ((P.sheafOf M₁).X p).over V.unop ⟶ ((P.sheafOf M₂).X (p + n + 1)).over V.unop :=
    ((P.ΨT M₁ M₂ n ⟨p, p + n, rfl⟩ ≫ homPost P.isCommSheaf_R ((P.sheafOf M₁).X p)
      (P.sheafOfD M₂ (p + n))).val.app V).hom s with ha
  set b : ((P.sheafOf M₁).X p).over V.unop ⟶ ((P.sheafOf M₂).X (p + n + 1)).over V.unop :=
    ((P.ΨT M₁ M₂ n ⟨p + 1, p + n + 1, by lia⟩ ≫ Cohesive.homPre P.isCommSheaf_R
      (P.sheafOfD M₁ p) ((P.sheafOf M₂).X (p + n + 1))).val.app V).hom s with hb
  have e1 : ((a + (n + 1).negOnePow • b).val.app Z).hom x =
      (a.val.app Z).hom x + (n + 1).negOnePow • (b.val.app Z).hom x := by
    rw [sheaf_add_app, sheaf_units_app]
  have key := P.ΨW_homδ M₁ M₂ n ⟨p, p + n + 1, hpq⟩ (leOfHom Z.unop.hom) s x
  refine (congrArg Subtype.val e1).trans ?_
  exact key.symm

/-- **C4 step 2.** `Ψ : ℋ(M₁, M₂) ⟶ 𝓗om(α(M₁), α(M₂))`, `χ ↦ α(χ)` termwise (S7). -/
def Ψ : P.ℋ M₁ M₂ ⟶ homSheafComplex P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂) where
  f n := Limits.Pi.lift fun T : Triplet n ↦ P.ΨT M₁ M₂ n T
  comm' := by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have h1 : (homSheafComplex P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂)).d i (i + 1) =
        homComplexD P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂) i := CochainComplex.of_d _ _ i
    have h2 : (P.ℋ M₁ M₂).d i (i + 1) = P.homD M₁ M₂ i := CochainComplex.of_d _ _ i
    rw [h1, h2]
    exact P.Ψ_comm M₁ M₂ i

/-- On `F ∘ φ`, `extAlong` is the base change `bcHomL` of `φ`. -/
theorem extAlong_homAt_top (φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive) {W : Opens X} :
    extAlong (P.homAt M₁ M₂ 0 (le_top : W ≤ ⊤) (P.homTop M₁ M₂ 0 (P.toHom0 φ))) =
      bcHomL (P.D.res (le_top : W ≤ ⊤)) 0 (P.toHom0 φ) := by
  refine (eq_extAlong _ (bcHomL_mem (P.D.res (le_top : W ≤ ⊤)) 0 (P.toHom0 φ)) fun x => ?_).symm
  have h1 : bcHomL (P.D.res (le_top : W ≤ ⊤)) 0 (P.toHom0 φ) (bcF (P.D.res le_top) M₁.Q x) =
      bcF (P.D.res (le_top : W ≤ ⊤)) M₂.Q (φ.1 x) := bcHomL_bcF _ 0 (P.toHom0 φ) x
  refine h1.trans ?_
  exact (bcTotRes_bcF (P.D.res (le_top : W ≤ ⊤)) (P.D.res (le_top : (⊤ : Opens X) ≤ ⊤))
    (P.D.res (le_top : W ≤ ⊤)) (P.D.res_comp le_top le_top) M₂.Q (φ.1 x)).symm

/-- Sections of a morphism into a product, followed by a projection. -/
private lemma lift_sections {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{0}} {ι : Type} (F : ι → Mod R) {Y : Mod R} (g : ∀ i, Y ⟶ F i) (i : ι)
    (V : Cᵒᵖ) (s : Y.val.obj V) :
    ((Limits.Pi.π F i).val.app V).hom (((Limits.Pi.lift g).val.app V).hom s) =
      ((g i).val.app V).hom s :=
  congrArg (fun m : Y ⟶ F i => (m.val.app V).hom s) (Limits.Pi.lift_comp_π g i)

/-- **C4 step 5 (compatibility).** At `V = X`, `Ψ` sends `F ∘ φ` for a closed degree-`0` map `φ`
to the cocycle of `α(φ)` (through S7's description of sections of `𝓗om`). -/
theorem Ψ_top (φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive) :
    homComplexSectionsEquiv P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂) 0 ⊤
        (((P.Ψ M₁ M₂).f 0).val.app (op ⊤) (P.homTop M₁ M₂ 0 (P.toHom0 φ))) =
      Cochain.ofHom ((overC ⊤).map (P.sheafOfMap φ)) := by
  funext T
  obtain ⟨p, q, hpq⟩ := T
  obtain rfl : q = p := by lia
  rw [homComplexSectionsEquiv_apply]
  refine hom_ext_pt fun Z x => ?_
  apply Subtype.ext
  erw [lift_sections]
  change extAlong (P.homAt M₁ M₂ 0 (leOfHom Z.unop.hom) (P.homTop M₁ M₂ 0 (P.toHom0 φ))) x.1 =
    bcHomL (P.D.res (leOfHom Z.unop.hom)) 0 (P.toHom0 φ) x.1
  exact LinearMap.congr_fun (P.extAlong_homAt_top M₁ M₂ φ) x.1

/-- **C4 step 4.** `ℋ(M₁, M₂)` is bounded below (`Q₁`, `Q₂` bounded, `𝒜` bounded). -/
theorem exists_isStrictlyGE_ℋ : ∃ a : ℤ, (P.ℋ M₁ M₂).IsStrictlyGE a := by
  obtain ⟨a₁, b₁, h₁⟩ := M₁.bounded
  obtain ⟨a₂, b₂, h₂⟩ := M₂.bounded
  refine ⟨a₂ - b₁ - GCDga.N (𝒜 := P.𝒜X), ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  change Limits.IsZero (P.homSh M₁ M₂ n)
  refine isZero_of_sections_subsingleton fun V => ⟨fun χ χ' => ?_⟩
  have hz : ∀ ψ : P.HomSec M₁ M₂ n (le_top : V.unop ≤ ⊤), ψ = 0 := fun ψ =>
    Subtype.ext (linearMap_eq_zero_of_totDeg ψ.1 a₁ b₁ h₁ fun m _ hm x hx =>
      eq_zero_of_totDeg_lt a₂ (fun p hp => bcGen_subsingleton (P.D.res le_top) (Q := M₂.Q) p
        (h₂ p (Or.inl hp))) (by lia) (ψ.2.1 hx))
  exact (hz χ).trans (hz χ').symm

/-- Multiplication by `res_V(a)` on `α(M₁)^p(V)` (`a ∈ 𝒜⁰(X)`), `O(V)`-linear. -/
private def actSheafOfV (a : ↥(P.𝒜X 0)) (p : ℤ) {V : Opens X} (h : V ≤ ⊤) :
    P.sheafOfSec M₁ p h →ₗ[P.O.obj.obj (op V)] P.sheafOfSec M₁ p h where
  toFun x := (P.D.res h).f0 a • (show ↥(P.deg0 M₁ p h) from x)
  map_add' x y := smul_add _ (show ↥(P.deg0 M₁ p h) from x) y
  map_smul' f x := by
    change (P.D.res h).f0 a • (P.ρ V f • (show ↥(P.deg0 M₁ p h) from x)) =
      P.ρ V f • ((P.D.res h).f0 a • (show ↥(P.deg0 M₁ p h) from x))
    exact smul_comm _ _ _

/-- `actSheafOfV` commutes with restriction. -/
private theorem actSheafOfV_res (a : ↥(P.𝒜X 0)) (p : ℤ) {V W : Opens X} (hV : V ≤ ⊤) (hW : W ≤ V)
    (x : P.sheafOfSec M₁ p hV) :
    P.sheafOfRes M₁ p hV hW (P.actSheafOfV M₁ a p hV x) =
      P.actSheafOfV M₁ a p (hW.trans hV) (P.sheafOfRes M₁ p hV hW x) := by
  refine Subtype.ext ?_
  change P.totRes M₁ hV hW ((P.D.res hV).f0 a • x.1) =
    (P.D.res (hW.trans hV)).f0 a • P.totRes M₁ hV hW x.1
  rw [P.totRes_smul0 M₁ hV hW ((P.D.res hV).f0 a)]
  refine congrArg (· • _) (Subtype.ext ?_)
  exact P.D.res_comp hV hW a

/-- The action of `a ∈ 𝒜⁰(X)` as an endomorphism of the sheaf `α(M₁)^p`. -/
private def actSheafOf (a : ↥(P.𝒜X 0)) (p : ℤ) : P.sheafOfSh M₁ p ⟶ P.sheafOfSh M₁ p :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (P.actSheafOfV M₁ a p (le_top : V.unop ≤ ⊤))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact (P.actSheafOfV_res M₁ a p le_top (leOfHom f.unop) x).symm }⟩

/-- **C3.a(i) + S7.a′.** On compact Hausdorff `X`, every term of `𝓗om(α(M₁), L)` is soft:
`𝒜⁰(X)` acts on each `α(M₁)^p` by multiplication with `res_V(a)` (S3.b(i)). -/
theorem isSoft_homSheafComplex_sheafOf_X [CompactSpace X] [T2Space X]
    (L : CochainComplex (Mod P.R) ℤ) (n : ℤ) :
    IsSoft ((homSheafComplex P.isCommSheaf_R (P.sheafOf M₁) L).X n) := by
  let act : ∀ p : ℤ, (ringOf P.A0).obj.obj (op ⊤) →+ ((P.sheafOf M₁).X p ⟶ (P.sheafOf M₁).X p) :=
    fun p =>
    { toFun := fun a => P.actSheafOf M₁ (a : ↥(P.𝒜X 0)) p
      map_zero' := by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
        apply ModuleCat.hom_ext
        refine DFunLike.ext _ _ fun x => ?_
        refine Subtype.ext ?_
        change (P.D.res (le_top : V.unop ≤ ⊤)).f0 0 • x.1 = (0 : P.TotSec M₁ le_top)
        rw [map_zero, zero_smul]
      map_add' := fun (a b : ↥(P.𝒜X 0)) => by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
        apply ModuleCat.hom_ext
        refine DFunLike.ext _ _ fun x => ?_
        refine Subtype.ext ?_
        change (P.D.res (le_top : V.unop ≤ ⊤)).f0 (a + b : ↥(P.𝒜X 0)) • x.1 =
          (P.D.res (le_top : V.unop ≤ ⊤)).f0 (a : ↥(P.𝒜X 0)) • x.1 +
            (P.D.res (le_top : V.unop ≤ ⊤)).f0 (b : ↥(P.𝒜X 0)) • x.1
        rw [map_add, add_smul] }
  refine isSoft_homSheafComplex_X P.isFine0 P.isCommSheaf_R act (fun p => ?_)
    (fun p ρ V hρ => ?_) L n
  · refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    refine Subtype.ext ?_
    change (P.D.res (le_top : V.unop ≤ ⊤)).f0 1 • x.1 = x.1
    rw [map_one, one_smul]
  · apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    refine Subtype.ext ?_
    change (P.D.res (le_top : V ≤ ⊤)).f0 ρ • x.1 = (0 : P.TotSec M₁ le_top)
    rw [show (P.D.res (le_top : V ≤ ⊤)).f0 ρ = 0 from hρ, zero_smul]

end PreResolvingData

/-- `𝓗om(M, N)` is zero when `M` is zero. -/
private lemma isZero_homSheaf_left {R : RingSheaf X} (hR : IsCommSheaf R) {M : Mod R}
    (N : Mod R) (hM : Limits.IsZero M) : Limits.IsZero (homSheaf hR M N) := by
  refine isZero_of_sections_subsingleton fun V => ?_
  have hz : Limits.IsZero (M.over V.unop) := Functor.map_isZero _ hM
  exact (homSheafSectionsEquiv hR M N V.unop).subsingleton_congr.2
    ⟨fun f g => hz.eq_of_src f g⟩

/-- `𝓗om(M, N)` is zero when `N` is zero. -/
private lemma isZero_homSheaf_right {R : RingSheaf X} (hR : IsCommSheaf R) (M : Mod R)
    {N : Mod R} (hN : Limits.IsZero N) : Limits.IsZero (homSheaf hR M N) := by
  refine isZero_of_sections_subsingleton fun V => ?_
  have hz : Limits.IsZero (N.over V.unop) := Functor.map_isZero _ hN
  exact (homSheafSectionsEquiv hR M N V.unop).subsingleton_congr.2
    ⟨fun f g => hz.eq_of_tgt f g⟩

/-- **Audit G6.** `𝓗om(K, L)` is bounded below when `K` is bounded above and `L` bounded below. -/
theorem exists_isStrictlyGE_homSheafComplex {R : RingSheaf X} (hR : IsCommSheaf R)
    (K L : CochainComplex (Mod R) ℤ) (a b : ℤ) [K.IsStrictlyLE b] [L.IsStrictlyGE a] :
    (homSheafComplex hR K L).IsStrictlyGE (a - b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  change Limits.IsZero (homComplexX hR K L n)
  rw [Limits.IsZero.iff_id_eq_zero]
  refine Limits.Pi.hom_ext _ _ fun T => ?_
  by_cases hp : b < T.p
  · exact (isZero_homSheaf_left hR _ (K.isZero_of_isStrictlyLE b T.p hp)).eq_of_tgt _ _
  · have hq : T.q < a := by have := T.hpq; lia
    exact (isZero_homSheaf_right hR _ (L.isZero_of_isStrictlyGE a T.q hq)).eq_of_tgt _ _

/-- **Audit G4.** Cochains between the restrictions to `X` itself (over-site of `⊤`, where S7
describes global sections of `𝓗om`) are the cochains on `X`: additive equivalences, natural in the
target, compatible with `δ` and with `Cochain.ofHom` (`⊤` is terminal in `Opens X`). -/
theorem exists_cochain_overTop_equiv (R : RingSheaf X) :
    ∃ e : ∀ (K L : CochainComplex (Mod R) ℤ) (n : ℤ),
        Cochain ((overC (⊤ : Opens X)).obj K) ((overC (⊤ : Opens X)).obj L) n ≃+ Cochain K L n,
      (∀ (K L : CochainComplex (Mod R) ℤ) (n : ℤ) (c : Cochain ((overC (⊤ : Opens X)).obj K)
          ((overC (⊤ : Opens X)).obj L) n),
        e K L (n + 1) (CochainComplex.HomComplex.δ n (n + 1) c) =
          CochainComplex.HomComplex.δ n (n + 1) (e K L n c)) ∧
      (∀ (K L : CochainComplex (Mod R) ℤ) (f : K ⟶ L),
        e K L 0 (Cochain.ofHom ((overC (⊤ : Opens X)).map f)) = Cochain.ofHom f) ∧
      ∀ (K L L' : CochainComplex (Mod R) ℤ) (n : ℤ)
        (c : Cochain ((overC (⊤ : Opens X)).obj K) ((overC (⊤ : Opens X)).obj L) n)
        (g : L ⟶ L'),
        e K L' n (c.comp (Cochain.ofHom ((overC (⊤ : Opens X)).map g)) (add_zero n)) =
          (e K L n c).comp (Cochain.ofHom g) (add_zero n) := by
  let E : ∀ (K L : CochainComplex (Mod R) ℤ) (n : ℤ),
      Cochain ((overC (⊤ : Opens X)).obj K) ((overC (⊤ : Opens X)).obj L) n ≃+ Cochain K L n :=
    fun K L n =>
    { toFun := fun c => Cochain.mk fun p q hpq ↦ overTopEquiv (K.X p) (L.X q) (c.v p q hpq)
      invFun := fun c => Cochain.mk fun p q hpq ↦ (c.v p q hpq).over (⊤ : Opens X)
      left_inv := fun c => by
        refine Cochain.ext _ _ fun p q hpq => ?_
        exact (overTopEquiv (K.X p) (L.X q)).left_inv (c.v p q hpq)
      right_inv := fun c => by
        refine Cochain.ext _ _ fun p q hpq => ?_
        exact (overTopEquiv (K.X p) (L.X q)).right_inv (c.v p q hpq)
      map_add' := fun c c' => by
        refine Cochain.ext _ _ fun p q hpq => ?_
        exact map_add (overTopEquiv (K.X p) (L.X q)) (c.v p q hpq) (c'.v p q hpq) }
  refine ⟨E, ?_, ?_, ?_⟩
  · intro K L n c
    refine Cochain.ext _ _ fun p q hpq => ?_
    change overTopEquiv (K.X p) (L.X q)
        ((CochainComplex.HomComplex.δ n (n + 1) c).v p q hpq) =
      (CochainComplex.HomComplex.δ n (n + 1) (E K L n c)).v p q hpq
    rw [δ_v (n := n) (m := n + 1) rfl c p q hpq (q - 1) (p + 1) rfl rfl,
      δ_v (n := n) (m := n + 1) rfl (E K L n c) p q hpq (q - 1) (p + 1) rfl rfl, map_add,
      Units.smul_def, Units.smul_def, map_zsmul]
    exact congrArg₂ (· + ·) (overTopHom_comp_over (c.v p (q - 1) _) (L.d (q - 1) q))
      (congrArg _ (overTopHom_over_comp (K.d p (p + 1)) (c.v (p + 1) q _)))
  · intro K L f
    refine Cochain.ext₀ _ _ fun p => ?_
    rw [Cochain.ofHom_v]
    exact overTopHom_over (f.f p)
  · intro K L L' n c g
    refine Cochain.ext _ _ fun p q hpq => ?_
    change overTopEquiv (K.X p) (L'.X q)
        ((c.comp (Cochain.ofHom ((overC (⊤ : Opens X)).map g)) (add_zero n)).v p q hpq) =
      ((E K L n c).comp (Cochain.ofHom g) (add_zero n)).v p q hpq
    rw [Cochain.comp_zero_cochain_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      Cochain.ofHom_v]
    exact overTopHom_comp_over (c.v p q hpq) (g.f q)

-- C4 steps 3 and 5 (`quasiIso_Ψ_comp`, `bijective_J_map`, `full_J`, `faithful_J`) are in
-- `Comparison/FullyFaithfulLocal.lean` (v1.11).

end Cohesive
