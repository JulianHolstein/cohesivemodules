-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Comparison.SheafDataAlpha
import Cohesivemodules.Comparison.FunctorDef

set_option linter.style.header false

/-!
# Z3.m: `α` on morphisms and homotopies over `DgaSheafData` (copy of C1.b), bridges to C1

Blueprint item Z3.m (`blueprint/blueprint-tw.md` §2.4, D11). The section-level part of C1.b
(`Comparison/FunctorDef.lean`, frozen, section `MorphismsV`) word for word over
`S : DgaSheafData X`, and its sheaf-level per-degree maps:
* `S.sheafOfMapV φ n h`: for a closed degree-`0` map `φ : M ⟶ N`, the base change `bcHomL` of `φ`
  on `α(M)^n(V)`; `S.sheafOfMapN φ n : α(M)^n ⟶ α(N)^n`;
* `S.hMapV h i j`: for `h ∈ Hom^{-1}`, on `α(M)^i(V) → α(N)^j(V)`; `S.hMapN h i j`;
* `bcHomL_X` (`α(φ)` commutes with `𝕏`), `bcHomL_homotopy` (`α(a) − α(b) = δ(α(h))` on sections).

**Bridges**: for pre-resolving data `P`, the copies at `P.toSheafData` are the frozen C1
definitions, by `rfl` (`toSheafData_sheafOfPre`, `_sheafOfSh`, `_sheafOfX`, `_sheafOfMapN`,
`_hMapN`).

## Deviations
* No complex `α(M)`, chain map `α(φ)`, `JK` or `J`: they need `𝕏² = 0` (`c_eq_zero`); the twisted
  functor builds its complexes with `𝕏 − h⁰_α·` on `U_α` (Z3.n).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace DgaSheafData

variable (S : DgaSheafData X)

section MorphismsV

variable {U₀ : Opens X} {M N : CohesiveModule (S.D.𝒜 U₀)}

/-- **Z3.m** (copy of C1 `toHom0`). A closed degree-`0` map, as an element of `Hom^0`. -/
def toHom0 (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) :
    Hom M.toQuasiCohesive N.toQuasiCohesive 0 :=
  ⟨φ.1, (Submodule.mem_inf.1 φ.2).1⟩

/-- The base change of a degree-`0` map preserves the total degree. -/
theorem bcHomL_mem_totDeg (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) {n : ℤ} {V : Opens X}
    {h : V ≤ U₀} {x : S.TotSec M h} (hx : x ∈ totDeg (S.D.𝒜 V) (M.baseChange (S.D.res h)).Q n) :
    bcHomL (S.D.res h) 0 (S.toHom0 φ) x ∈ totDeg (S.D.𝒜 V) (N.baseChange (S.D.res h)).Q n := by
  have := (bcHomL_mem (S.D.res h) 0 (S.toHom0 φ)).1 hx
  rwa [add_zero] at this

/-- The base change of a degree-`0` map commutes with the `O(V)`-action. -/
theorem bcHomL_smulO (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) {V : Opens X} (h : V ≤ U₀)
    (f : S.O.obj.obj (op V)) (x : S.TotSec M h) :
    bcHomL (S.D.res h) 0 (S.toHom0 φ) ((S.ρ V f) • x) =
      (S.ρ V f) • bcHomL (S.D.res h) 0 (S.toHom0 φ) x := by
  have := (bcHomL_mem (S.D.res h) 0 (S.toHom0 φ)).2 (S.ρ V f).2 x
  rw [zero_mul, Int.negOnePow_zero, one_smul] at this
  exact this

/-- **Z3.m** (copy of C1 `sheafOfMapV`). `α(φ)` on `α(M)^n(V)` for `V ≤ U₀`: the base change
`bcHomL (res h) 0 φ` (A9). -/
def sheafOfMapV (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) {V : Opens X} (h : V ≤ U₀) :
    S.sheafOfSec M n h →ₗ[S.O.obj.obj (op V)] S.sheafOfSec N n h where
  toFun x := ⟨bcHomL (S.D.res h) 0 (S.toHom0 φ) x.1, S.bcHomL_mem_totDeg φ x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (S.bcHomL_smulO φ h f x.1)

/-- `sheafOfMapV` on the underlying element (rfl). -/
theorem sheafOfMapV_val (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) {V : Opens X}
    (h : V ≤ U₀) (x : S.sheafOfSec M n h) :
    (S.sheafOfMapV φ n h x).1 = bcHomL (S.D.res h) 0 (S.toHom0 φ) x.1 := rfl

/-- The base change of a closed degree-`0` map commutes with `𝕏`. -/
theorem bcHomL_X (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) {V : Opens X} (h : V ≤ U₀)
    (x : S.TotSec M h) :
    bcHomL (S.D.res h) 0 (S.toHom0 φ) ((M.baseChange (S.D.res h)).X x) =
      (N.baseChange (S.D.res h)).X (bcHomL (S.D.res h) 0 (S.toHom0 φ) x) := by
  exact closed_comm (M₁ := M.toQuasiCohesive.baseChange (S.D.res h))
    (M₂ := N.toQuasiCohesive.baseChange (S.D.res h)) (bcHomL (S.D.res h) 0 (S.toHom0 φ))
    (bcHomL_mem_Z0 (S.D.res h) φ) x

/-- **Z3.m** (copy of C1 `hMapV`). The base change of a map `h ∈ Hom^{-1}` on
`α(M)^i(V) → α(N)^j(V)` (`i + -1 = j`). -/
def hMapV (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) (hij : i + -1 = j)
    {V : Opens X} (hV : V ≤ U₀) :
    S.sheafOfSec M i hV →ₗ[S.O.obj.obj (op V)] S.sheafOfSec N j hV where
  toFun x := ⟨bcHomL (S.D.res hV) (-1) h x.1, by
    subst hij; exact (bcHomL_mem (S.D.res hV) (-1) h).1 x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (by
    have := (bcHomL_mem (S.D.res hV) (-1) h).2 (S.ρ V f).2 x.1
    rw [mul_zero, Int.negOnePow_zero, one_smul] at this
    exact this)

/-- Homotopy formula: if `φ - ψ = δh` then `α(φ) = h𝕏 + 𝕏h + α(ψ)` on sections. -/
theorem bcHomL_homotopy (a b : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1))
    (hab : δ _ _ (-1) h.1 = a.1 - b.1) {V : Opens X} (hV : V ≤ U₀) :
    δ (M.toQuasiCohesive.baseChange (S.D.res hV)) (N.toQuasiCohesive.baseChange (S.D.res hV))
      (-1) (bcHomL (S.D.res hV) (-1) h) =
      bcHomL (S.D.res hV) 0 (S.toHom0 a) - bcHomL (S.D.res hV) 0 (S.toHom0 b) := by
  have hm : (-1 : ℤ) + 1 = 0 := by norm_num
  have hc : S.toHom0 a = S.toHom0 b + (⟨δ _ _ (-1) h.1, hm ▸ δ_mem _ _ h.2⟩ :
      Hom M.toQuasiCohesive N.toQuasiCohesive 0) :=
    Subtype.ext (by
      change a.1 = b.1 + δ _ _ (-1) h.1
      rw [hab]; abel)
  have hd := bcHomL_δ (S.D.res hV) (-1) h hm
  rw [hc, bcHomL_add, ← hd]
  abel

/-- `hMapV` on the underlying element (rfl). -/
theorem hMapV_val (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ)
    (hij : i + -1 = j) {V : Opens X} (hV : V ≤ U₀) (x : S.sheafOfSec M i hV) :
    (S.hMapV h i j hij hV x).1 = bcHomL (S.D.res hV) (-1) h x.1 := rfl

end MorphismsV

section Morphisms

variable {M N : CohesiveModule S.𝒜X}

/-- **Z3.m** (copy of the components of C1 `sheafOfMap`). `α(φ)` in degree `n`, as a morphism of
sheaves `α(M)^n ⟶ α(N)^n`, for a closed degree-`0` map `φ`. -/
def sheafOfMapN (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) :
    S.sheafOfSh M n ⟶ S.sheafOfSh N n :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (S.sheafOfMapV φ n (le_top : V.unop ≤ ⊤))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact bcHomL_bcTotRes (S.D.res (leOfHom f.unop)) (S.D.res (le_top : U.unop ≤ ⊤))
         (S.D.res (le_top : V.unop ≤ ⊤)) (S.D.res_comp _ _) 0 (S.toHom0 φ) x.1 }⟩

/-- **Z3.m** (copy of C1 `hMap`). The homotopy component `α(M)^i ⟶ α(N)^j` (`i + -1 = j`) given
by `h ∈ Hom^{-1}`. -/
def hMapN (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) (hij : i + -1 = j) :
    S.sheafOfSh M i ⟶ S.sheafOfSh N j :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (S.hMapV h i j hij (le_top : V.unop ≤ ⊤))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact bcHomL_bcTotRes (S.D.res (leOfHom f.unop)) (S.D.res (le_top : U.unop ≤ ⊤))
         (S.D.res (le_top : V.unop ≤ ⊤)) (S.D.res_comp _ _) (-1) h x.1 }⟩

/-- `α(φ)` commutes with `𝕏`: `sheafOfX ≫ sheafOfMapN = sheafOfMapN ≫ sheafOfX`. -/
theorem sheafOfX_sheafOfMapN (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) :
    S.sheafOfX M n ≫ S.sheafOfMapN φ (n + 1) = S.sheafOfMapN φ n ≫ S.sheafOfX N n := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact S.bcHomL_X φ le_top x.1

/-- `α` preserves identities, degreewise. -/
theorem sheafOfMapN_id (M : CohesiveModule S.𝒜X) (n : ℤ) :
    S.sheafOfMapN (idZ0 M.toQuasiCohesive) n = 𝟙 (S.sheafOfSh M n) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact DFunLike.congr_fun (bcHomL_id (S.D.res (le_top : V.unop ≤ ⊤)) M.toQuasiCohesive) x.1

/-- `α` preserves composition, degreewise. -/
theorem sheafOfMapN_comp {L : CohesiveModule S.𝒜X} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (ψ : Z0 N.toQuasiCohesive L.toQuasiCohesive) (n : ℤ) :
    S.sheafOfMapN (compZ0 _ _ _ ψ φ) n = S.sheafOfMapN φ n ≫ S.sheafOfMapN ψ n := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact DFunLike.congr_fun (bcHomL_comp (S.D.res (le_top : V.unop ≤ ⊤)) 0 0
    (S.toHom0 ψ) (S.toHom0 φ)) x.1

end Morphisms

end DgaSheafData

/-! ## Bridges: the copies at `P.toSheafData` are the frozen C1 definitions -/

namespace PreResolvingData

variable (P : PreResolvingData X) (M : CohesiveModule P.𝒜X)

/-- **Z3.m** (bridge). The presheaf `α(M)^n` of the copy is the frozen one (rfl). -/
theorem toSheafData_sheafOfPre (n : ℤ) : P.toSheafData.sheafOfPre M n = P.sheafOfPre M n :=
  rfl

/-- **Z3.m** (bridge). The sheaf `α(M)^n` of the copy is the frozen one (rfl). -/
theorem toSheafData_sheafOfSh (n : ℤ) : P.toSheafData.sheafOfSh M n = P.sheafOfSh M n :=
  rfl

/-- **Z3.m** (bridge). The operator `𝕏` of the copy is the frozen differential (rfl). -/
theorem toSheafData_sheafOfX (n : ℤ) : P.toSheafData.sheafOfX M n = P.sheafOfD M n :=
  rfl

/-- **Z3.m** (bridge). `α(φ)` in degree `n` of the copy is the component of the frozen chain map
(rfl). -/
theorem toSheafData_sheafOfMapN {N : CohesiveModule P.𝒜X}
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ) :
    P.toSheafData.sheafOfMapN φ n = (P.sheafOfMap φ).f n :=
  rfl

/-- **Z3.m** (bridge). The homotopy components of the copy are the frozen ones (rfl). -/
theorem toSheafData_hMapN {N : CohesiveModule P.𝒜X}
    (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) (hij : i + -1 = j) :
    P.toSheafData.hMapN h i j hij = P.hMap h i j hij :=
  rfl

end PreResolvingData

end Cohesive
