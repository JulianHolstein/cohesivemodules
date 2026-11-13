-- FROZEN (gate 4, 29 Oct 2026; C1 the functor J, in the main statement). Do not edit.
import Cohesivemodules.Comparison.AlphaSheaf
import Cohesivemodules.Algebra.BaseChangeHomDef
import Cohesivemodules.Algebra.BaseChange
import Mathlib.Algebra.Homology.DerivedCategory.Basic

set_option linter.style.header false

/-!
# C1: the functor `J : Ho(P_A) ⥤ D(O)`

Blueprint item C1 (§4), [B, §4.1, Thm 4.1.3 (the functor α)], [A, Def 7.2.3 at h = 0]. These
definitions enter the main statement (`blockFunctor E X := J` for the Dolbeault data, F15); they
are frozen at gate 4.

For pre-resolving data `P` (C0.a, no H1/H2 needed):
* `P.sheafOfSh M n : Mod P.R`: the sheaf `α(M)^n` (`sheafOfPre`, sheaf by C1.a);
* `P.sheafOfD M n`: its differential (`𝕏` of `M|V` on sections over `V`);
* `P.sheafOf M : CochainComplex (Mod P.R) ℤ`: the complex `α(M)` (`d² = 0` from `𝕏² = c = 0`);
* `P.sheafOfMap φ : α(M) ⟶ α(N)` for a closed degree-`0` map `φ`: on `α(M)^n(V)` the base change
  `bcHomL (r_V) 0 φ` of `φ` to `V` (A9), `b ⊗ (β ⊗ q) ↦ b·β·φ(1 ⊗ q)` up to A9's comparison;
* `P.JK : HoP 𝒜(X) ⥤ K(Mod P.R)`: `M ↦ α(M)`, `[φ] ↦ [α(φ)]` (closed maps to chain maps,
  coboundaries to null-homotopic maps; C1.b);
* `P.J : HoP 𝒜(X) ⥤ D(Mod P.R)`: `JK` followed by the localization `Qh`.

## Deviations
* `J` lands in the whole derived category `D(Mod P.R)`, not in `D_perf` (blueprint §1 ⚠: that
  `J` lands in `D_perf` is C2 and needs LL). The `HasDerivedCategory` instance is an instance
  argument, as for `Perf` (S9); `Statements.lean` fixes `HasDerivedCategory.standard` for both.
* `α(M)^n(V)` is spelled through A9's base change (see `Comparison/AlphaDef.lean`).
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X)

section Complex

variable (M : CohesiveModule P.𝒜X)

/-- **C1.** The sheaf of `O`-modules `α(M)^n` (C1.a: `isSheaf_sheafOfPre`). -/
def sheafOfSh (n : ℤ) : Mod P.R := ⟨P.sheafOfPre M n, P.isSheaf_sheafOfPre M n⟩

/-- **C1.** The differential `α(M)^n ⟶ α(M)^{n+1}`: `𝕏` of `M|V` on sections over `V`. -/
def sheafOfD (n : ℤ) : P.sheafOfSh M n ⟶ P.sheafOfSh M (n + 1) :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (P.sheafOfDV M n (le_top : V.unop ≤ ⊤))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact P.X_totRes M le_top (leOfHom f.unop) x.1 }⟩

/-- `sheafOfD ≫ sheafOfD = 0` (`𝕏² = c = 0`, `P.c_eq_zero`). -/
theorem sheafOfD_sheafOfD (n : ℤ) : P.sheafOfD M n ≫ P.sheafOfD M (n + 1) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  have h := (M.baseChange (P.D.res (le_top : V.unop ≤ ⊤))).flat x.1
  rw [P.c_eq_zero, zero_smul] at h
  exact h

/-- **C1.** The complex of sheaves of `O`-modules `α(M)`, `α(M)^n(V) = Tot(M|V)` in degree `n`. -/
def sheafOf : CochainComplex (Mod P.R) ℤ :=
  CochainComplex.of (P.sheafOfSh M) (P.sheafOfD M) (P.sheafOfD_sheafOfD M)

/-- The terms of `α(M)` (rfl). -/
theorem sheafOf_X (n : ℤ) : (P.sheafOf M).X n = P.sheafOfSh M n := rfl

end Complex

section MorphismsV

variable {U₀ : Opens X} {M N : CohesiveModule (P.D.𝒜 U₀)}

/-- A closed degree-`0` map, as an element of `Hom^0` (forgetting closedness). -/
def toHom0 (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) :
    Hom M.toQuasiCohesive N.toQuasiCohesive 0 :=
  ⟨φ.1, (Submodule.mem_inf.1 φ.2).1⟩

/-- The base change of a degree-`0` map preserves the total degree. -/
theorem bcHomL_mem_totDeg (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) {n : ℤ} {V : Opens X}
    {h : V ≤ U₀} {x : P.TotSec M h} (hx : x ∈ totDeg (P.D.𝒜 V) (M.baseChange (P.D.res h)).Q n) :
    bcHomL (P.D.res h) 0 (P.toHom0 φ) x ∈ totDeg (P.D.𝒜 V) (N.baseChange (P.D.res h)).Q n := by
  have := (bcHomL_mem (P.D.res h) 0 (P.toHom0 φ)).1 hx
  rwa [add_zero] at this

/-- The base change of a degree-`0` map commutes with the `O(V)`-action. -/
theorem bcHomL_smulO (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) {V : Opens X} (h : V ≤ U₀)
    (f : P.O.obj.obj (op V)) (x : P.TotSec M h) :
    bcHomL (P.D.res h) 0 (P.toHom0 φ) ((P.ρ V f) • x) =
      (P.ρ V f) • bcHomL (P.D.res h) 0 (P.toHom0 φ) x := by
  have := (bcHomL_mem (P.D.res h) 0 (P.toHom0 φ)).2 (P.ρ V f).2 x
  rw [zero_mul, Int.negOnePow_zero, one_smul] at this
  exact this

/-- **C1.** `α(φ)` on `α(M)^n(V)` for `V ≤ U₀`: the base change `bcHomL (res h) 0 φ` (A9). -/
def sheafOfMapV (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) {V : Opens X} (h : V ≤ U₀) :
    P.sheafOfSec M n h →ₗ[P.O.obj.obj (op V)] P.sheafOfSec N n h where
  toFun x := ⟨bcHomL (P.D.res h) 0 (P.toHom0 φ) x.1, P.bcHomL_mem_totDeg φ x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (P.bcHomL_smulO φ h f x.1)

/-- `sheafOfMapV` on the underlying element (rfl). -/
theorem sheafOfMapV_val (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) {V : Opens X}
    (h : V ≤ U₀) (x : P.sheafOfSec M n h) :
    (P.sheafOfMapV φ n h x).1 = bcHomL (P.D.res h) 0 (P.toHom0 φ) x.1 := rfl

/-- The base change of a closed degree-`0` map commutes with `𝕏`. -/
theorem bcHomL_X (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) {V : Opens X} (h : V ≤ U₀)
    (x : P.TotSec M h) :
    bcHomL (P.D.res h) 0 (P.toHom0 φ) ((M.baseChange (P.D.res h)).X x) =
      (N.baseChange (P.D.res h)).X (bcHomL (P.D.res h) 0 (P.toHom0 φ) x) := by
  exact closed_comm (M₁ := M.toQuasiCohesive.baseChange (P.D.res h))
    (M₂ := N.toQuasiCohesive.baseChange (P.D.res h)) (bcHomL (P.D.res h) 0 (P.toHom0 φ))
    (bcHomL_mem_Z0 (P.D.res h) φ) x

/-- The base change of a map `h ∈ Hom^{-1}` on `α(M)^i(V) → α(N)^j(V)` (`i + -1 = j`);
the homotopy of `α` for `α(δh)`. -/
def hMapV (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) (hij : i + -1 = j)
    {V : Opens X} (hV : V ≤ U₀) :
    P.sheafOfSec M i hV →ₗ[P.O.obj.obj (op V)] P.sheafOfSec N j hV where
  toFun x := ⟨bcHomL (P.D.res hV) (-1) h x.1, by
    subst hij; exact (bcHomL_mem (P.D.res hV) (-1) h).1 x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (by
    have := (bcHomL_mem (P.D.res hV) (-1) h).2 (P.ρ V f).2 x.1
    rw [mul_zero, Int.negOnePow_zero, one_smul] at this
    exact this)

/-- Homotopy formula: if `φ - ψ = δh` then `α(φ) = h𝕏 + 𝕏h + α(ψ)` on sections. -/
theorem bcHomL_homotopy (a b : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1))
    (hab : δ _ _ (-1) h.1 = a.1 - b.1) {V : Opens X} (hV : V ≤ U₀) :
    δ (M.toQuasiCohesive.baseChange (P.D.res hV)) (N.toQuasiCohesive.baseChange (P.D.res hV))
      (-1) (bcHomL (P.D.res hV) (-1) h) =
      bcHomL (P.D.res hV) 0 (P.toHom0 a) - bcHomL (P.D.res hV) 0 (P.toHom0 b) := by
  have hm : (-1 : ℤ) + 1 = 0 := by norm_num
  have hc : P.toHom0 a = P.toHom0 b + (⟨δ _ _ (-1) h.1, hm ▸ δ_mem _ _ h.2⟩ :
      Hom M.toQuasiCohesive N.toQuasiCohesive 0) :=
    Subtype.ext (by
      change a.1 = b.1 + δ _ _ (-1) h.1
      rw [hab]; abel)
  have hd := bcHomL_δ (P.D.res hV) (-1) h hm
  rw [hc, bcHomL_add, ← hd]
  abel

/-- `hMapV` on the underlying element (rfl). -/
theorem hMapV_val (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ)
    (hij : i + -1 = j) {V : Opens X} (hV : V ≤ U₀) (x : P.sheafOfSec M i hV) :
    (P.hMapV h i j hij hV x).1 = bcHomL (P.D.res hV) (-1) h x.1 := rfl

end MorphismsV

section Morphisms

variable {M N : CohesiveModule P.𝒜X}

/-- **C1.b** `α(φ) : α(M) ⟶ α(N)` for a closed degree-`0` map `φ`. -/
def sheafOfMap (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) : P.sheafOf M ⟶ P.sheafOf N where
  f n := ⟨{ app := fun V ↦ ModuleCat.ofHom (P.sheafOfMapV φ n (le_top : V.unop ≤ ⊤))
            naturality := by
              intro U V f
              apply ModuleCat.hom_ext
              refine DFunLike.ext _ _ fun x => ?_
              apply Subtype.ext
              exact bcHomL_bcTotRes (P.D.res (leOfHom f.unop)) (P.D.res (le_top : U.unop ≤ ⊤))
                (P.D.res (le_top : V.unop ≤ ⊤)) (P.D.res_comp _ _) 0 (P.toHom0 φ) x.1 }⟩
  comm' := by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have e1 : (P.sheafOf N).d i (i + 1) = P.sheafOfD N i := CochainComplex.of_d _ _ _
    have e2 : (P.sheafOf M).d i (i + 1) = P.sheafOfD M i := CochainComplex.of_d _ _ _
    rw [e1, e2]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact (P.bcHomL_X φ le_top x.1).symm

/-- The homotopy component `α(M)^i ⟶ α(N)^j` (`i + -1 = j`) given by `h ∈ Hom^{-1}`. -/
def hMap (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) (hij : i + -1 = j) :
    P.sheafOfSh M i ⟶ P.sheafOfSh N j :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (P.hMapV h i j hij (le_top : V.unop ≤ ⊤))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact bcHomL_bcTotRes (P.D.res (leOfHom f.unop)) (P.D.res (le_top : U.unop ≤ ⊤))
         (P.D.res (le_top : V.unop ≤ ⊤)) (P.D.res_comp _ _) (-1) h x.1 }⟩

/-- The homotopy `α(M) ⟶ α(N)` of degree `-1` given by `h ∈ Hom^{-1}`. -/
def hHom (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) :
    (P.sheafOf M).X i ⟶ (P.sheafOf N).X j :=
  if hij : i + -1 = j then P.hMap h i j hij else 0

/-- If `φ - ψ = δh` for `h ∈ Hom^{-1}` then `α(φ)` and `α(ψ)` are homotopic. -/
theorem sheafOfMap_homotopic (a b : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (hab : δ _ _ (-1) h.1 = a.1 - b.1) :
    Nonempty (Homotopy (P.sheafOfMap a) (P.sheafOfMap b)) := by
  refine ⟨{ hom := P.hHom h, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    have : ¬ (i + -1 = j) := by
      intro h'
      apply hij
      change j + 1 = i
      omega
    simp only [hHom, this, ↓reduceDIte]
  · intro i'
    obtain ⟨i, rfl⟩ : ∃ i, i' = i + 1 := ⟨i' - 1, by omega⟩
    have e1 : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    have e2 : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    rw [dNext_eq _ e1, prevD_eq _ e2]
    have h1 : i + 1 + -1 = i := by omega
    have h2 : i + 1 + 1 + -1 = i + 1 := by omega
    have d1 : (P.sheafOf M).d (i + 1) (i + 1 + 1) = P.sheafOfD M (i + 1) :=
      CochainComplex.of_d _ _ _
    have d2 : (P.sheafOf N).d i (i + 1) = P.sheafOfD N i := CochainComplex.of_d _ _ _
    rw [d1, d2]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    have k1 : P.hHom h (i + 1 + 1) (i + 1) = P.hMap h _ _ h2 := by
      simp only [hHom, h2, ↓reduceDIte]
      rfl
    have k2 : P.hHom h (i + 1) i = P.hMap h _ _ h1 := by
      simp only [hHom, h1, ↓reduceDIte]
      rfl
    rw [k1, k2]
    exact hty_formula (M₁ := M.toQuasiCohesive.baseChange (P.D.res (le_top : V.unop ≤ ⊤)))
      (M₂ := N.toQuasiCohesive.baseChange (P.D.res (le_top : V.unop ≤ ⊤)))
      (bcHomL (P.D.res (le_top : V.unop ≤ ⊤)) (-1) h) _ _
      (P.bcHomL_homotopy a b h hab le_top) x.1

/-- `α` preserves identities. -/
theorem sheafOfMap_id (M : CohesiveModule P.𝒜X) :
    P.sheafOfMap (idZ0 M.toQuasiCohesive) = 𝟙 (P.sheafOf M) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact DFunLike.congr_fun (bcHomL_id (P.D.res (le_top : V.unop ≤ ⊤)) M.toQuasiCohesive) x.1

/-- `α` preserves composition. -/
theorem sheafOfMap_comp {L : CohesiveModule P.𝒜X} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (ψ : Z0 N.toQuasiCohesive L.toQuasiCohesive) :
    P.sheafOfMap (compZ0 _ _ _ ψ φ) = P.sheafOfMap φ ≫ P.sheafOfMap ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact DFunLike.congr_fun (bcHomL_comp (P.D.res (le_top : V.unop ≤ ⊤)) 0 0
    (P.toHom0 ψ) (P.toHom0 φ)) x.1

end Morphisms

/-- **C1.b** `J` into the homotopy category: `M ↦ α(M)`, `[φ] ↦ [α(φ)]`; well defined because
`α` of a coboundary `δh` is null-homotopic (homotopy `bcHomL (r_V) (-1) h`). -/
def JK : HoP P.𝒜X ⥤ HomotopyCategory (Mod P.R) (ComplexShape.up ℤ) where
  obj M := (HomotopyCategory.quotient _ _).obj (P.sheafOf M.as)
  map {M N} f := Quotient.liftOn' f
    (fun φ ↦ (HomotopyCategory.quotient _ _).map (P.sheafOfMap φ)) (by
      intro a b hab
      rw [Submodule.quotientRel_def] at hab
      obtain ⟨h, hh, hδ⟩ := hab
      obtain ⟨H⟩ := P.sheafOfMap_homotopic a b ⟨h, hh⟩ (by
        change δ _ _ (-1) h = a.1 - b.1
        exact hδ)
      exact HomotopyCategory.eq_of_homotopy _ _ H)
  map_id M := by
    change (HomotopyCategory.quotient _ _).map (P.sheafOfMap (idZ0 M.as.toQuasiCohesive)) = _
    rw [P.sheafOfMap_id, CategoryTheory.Functor.map_id]
  map_comp f g := by
    induction f using Submodule.Quotient.induction_on with
    | H z =>
    induction g using Submodule.Quotient.induction_on with
    | H w =>
    exact (congrArg (HomotopyCategory.quotient _ _).map (P.sheafOfMap_comp z w)).trans
      (CategoryTheory.Functor.map_comp _ _ _)

/-- **C1. The functor `J : Ho(P_A) ⥤ D(O)`,** `M ↦ α(M)`. [B, Thm 4.1.3], [A, Def 7.2.3]. The
`HasDerivedCategory` instance is an argument, as for `Perf`. -/
def J [HasDerivedCategory.{w} (Mod P.R)] : HoP P.𝒜X ⥤ DerivedCategory (Mod P.R) :=
  P.JK ⋙ DerivedCategory.Qh

/-- `J` on objects (rfl). -/
theorem J_obj [HasDerivedCategory.{w} (Mod P.R)] (M : HoP P.𝒜X) :
    P.J.obj M = DerivedCategory.Q.obj (P.sheafOf M.as) := rfl

end PreResolvingData

end Cohesive
