import Cohesivemodules.Comparison.FullyFaithful
import Cohesivemodules.Comparison.FullyFaithfulPhi

set_option linter.style.header false

/-!
# C4 step 3: the commuting square for `quasiIso_Φ`

Blueprint item C4 (§4), step 3 (v1.11). Fix `Y : Over U`, `V = Y.left`. On sections over `Y`,
the map `Φ = Ψ|U ≫ (𝓗om restriction iso) ≫ ι^*` of `quasiIso_Φ` sits in the square

```
Hom^•_{along res}(M₁|U, M₂|V) --alongPre φ--> Hom^•_{along res}(𝒜(U) ⊗ W, M₂|V)
        | jK (iso)                                       | alongEv (iso, A10.a)
        v                                                v
ℋ(M₁, M₂)(V) --Φ_Y--> 𝓗om(L, α(M₂)|U)(Y) ≅ Cochain(L|Y, α(M₂)|Y) --evL (iso)--> Hom^•(W, M₂|V)
```

(`jK_Φ_evL`). Elementwise, on `χ'` and `w ∈ W^p`, both ways give `χ'(φ(1 ⊗ 1 ⊗ w))`:
`homComplexOverIso_map₁_sections` (restriction then precomposition), `ι_app_res` (the value of
`ι` on `(ε⁻¹ w)|Y`), and the value of `Ψ(χ' ∘ F)` on `res(y)` (`extAlong`, `totRes_extAlong`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X)
  (W : CochainComplex (ModuleCat.{0} (P.O.obj.obj (op U))) ℤ)
  (hW : IsBoundedFGProj (P.O.obj.obj (op U)) W)
  (L : CochainComplex (Mod (P.R.over U)) ℤ)
  (ε : ((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ≅ W)
  (u : L ⟶ P.sheafOfOver U (P.fcMod U W hW))
  (M₁ M₂ : CohesiveModule P.𝒜X)
  (φ : Z0 (P.fcMod U W hW).toQuasiCohesive (M₁.baseChange (P.r U)).toQuasiCohesive)
  (Y : Over U)

/-- Step 1: `evLVal` of the cochain of the `Ψ`-section, via `homComplexOverIso_map₁_sections`. -/
private lemma evLVal_map₁ (f : L ⟶ (overC U).obj (P.sheafOf M₁)) (n : ℤ)
    (s : ((homSheafComplex P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂)).X n).val.obj (op Y.left))
    (p : ℤ) (w : W.X p) :
    P.evLVal U W L ε M₂ Y
      (homComplexSectionsEquiv (P.isCommSheaf_R.over U) L ((overC U).obj (P.sheafOf M₂)) n Y
        ((((homComplexOverIso P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂) U).hom ≫
          homComplexMap₁ (P.isCommSheaf_R.over U) f ((overC U).obj (P.sheafOf M₂))).f n).val.app
            (op Y) s)) p w =
    ((((homComplexSectionsEquiv P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂) n Y.left s
        ⟨p, p + n, rfl⟩).val.app (op (Over.mk (𝟙 Y.left)))).hom
      (((f.f p).val.app (op Y)).hom (((L.X p).val.map
        ((Over.mkIdTerminal (X := U)).from Y).op).hom ((ε.inv.f p).hom w)))) :
          P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)).1 :=
  congrArg Subtype.val (homComplexOverIso_map₁_sections P.isCommSheaf_R (P.sheafOf M₁)
    (P.sheafOf M₂) U f n
    Y s ⟨p, p + n, rfl⟩ (((L.X p).val.map ((Over.mkIdTerminal (X := U)).from Y).op).hom
      ((ε.inv.f p).hom w)))

/-- Step 2: the value of the `Ψ`-section of `χ` on `x` is `extAlong (χ|V) x`. -/
private lemma ψ_sec_val (n : ℤ) (p : ℤ) (χ : P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤))
    (x : P.sheafOfSec M₁ p (le_top : Y.left ≤ ⊤)) :
    (((homComplexSectionsEquiv P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂) n Y.left
      ((((P.Ψ M₁ M₂).f n).val.app (op Y.left)).hom χ) ⟨p, p + n, rfl⟩).val.app
        (op (Over.mk (𝟙 Y.left)))).hom x : P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)).1 =
      extAlong (P.homAt M₁ M₂ n (le_refl Y.left) χ) x.1 := by
  rw [homComplexSectionsEquiv_apply]
  have := congrArg (fun m : _ ⟶ _ => (m.val.app (op Y.left)).hom χ)
    (Limits.Pi.lift_comp_π (fun T : Triplet n ↦ P.ΨT M₁ M₂ n T) ⟨p, p + n, rfl⟩)
  erw [this]
  rfl

/-- Step 3: `extAlong (χ'∘F |_V)` on `totRes y` is `χ' y`. -/
private lemma extAlong_jK_totRes (n : ℤ)
    (χ' : HomAlongT (P.D.res (leOfHom Y.hom)) (M₁.baseChange (P.r U)).toQuasiCohesive
      (P.NY U M₂ Y) n) (y : (M₁.baseChange (P.r U)).T) :
    extAlong (P.homAt M₁ M₂ n (le_refl Y.left)
      (((P.jKf U M₁ M₂ Y n).hom χ' : P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤))))
      (P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) y) = χ'.1 y := by
  have key := bc_ext_semilinear (g := P.D.res (leOfHom Y.hom)) (f := P.r U) (Q := M₁.Q) n
    ((extAlong (P.homAt M₁ M₂ n (le_refl Y.left)
      (((P.jKf U M₁ M₂ Y n).hom χ' : P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤))))).toAddMonoidHom.comp
        (P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom)))
    χ'.1.toAddMonoidHom
    (fun {p b} hb y => by
      have hs : P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (b • y) =
          P.D.res (leOfHom Y.hom) b • P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) y :=
        bcTotRes_smul (P.D.res (leOfHom Y.hom)) (P.D.res (le_top : U ≤ ⊤))
          (P.D.res (le_top : Y.left ≤ ⊤)) _ M₁.Q b y
      change extAlong (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n)
        (P.homAt M₁ M₂ n (le_refl Y.left)
          (((P.jKf U M₁ M₂ Y n).hom χ' : P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤))))
        (P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (b • y)) = _
      rw [hs]
      exact (extAlong_mem (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n) _).2
        ((P.D.res (leOfHom Y.hom)).map_mem hb) _)
    (fun {p b} hb y => χ'.2.2 hb y)
    (fun x => by
      change extAlong (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n)
        (P.homAt M₁ M₂ n (le_refl Y.left)
          (((P.jKf U M₁ M₂ Y n).hom χ' : P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤))))
        (P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (bcF (P.r U) M₁.Q x)) = _
      rw [show P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (bcF (P.r U) M₁.Q x) =
        bcF (P.D.res (le_top : Y.left ≤ ⊤)) M₁.Q x from
        bcTotRes_bcF (P.D.res (leOfHom Y.hom)) (P.D.res (le_top : U ≤ ⊤))
          (P.D.res (le_top : Y.left ≤ ⊤)) _ M₁.Q x]
      refine (extAlong_bcF (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n) _ x).trans ?_
      change P.totRes M₂ (le_top : Y.left ≤ ⊤) (le_refl Y.left) (χ'.1 (bcF (P.r U) M₁.Q x)) = _
      exact P.totRes_id M₂ _ _)
  exact DFunLike.congr_fun key y

/-- **C4 step 3, L10 (the square).** For `Y : Over U` (`V = Y.left`), C2's `u` with
`Γ_U(u) = ε ≫ unitMap` and a closed degree-`0` map `φ : 𝒜(U) ⊗ W → M₁|U`:
`jK ≫ Φ_Y ≫ (sections of 𝓗om ≅ Cochain) ≫ evL = alongPre φ ≫ alongEv`, as chain maps of
complexes of abelian groups `Hom^•_{along res_{V ≤ U}}(M₁|U, M₂|V) ⟶ Hom^•_{O(U)}(W, M₂|V)`.
Here `Φ = Ψ|U ≫ (homComplexOverIso).hom ≫ ι^*`, `ι = u ≫ α_U(φ) ≫ (restrSheafOfIso)⁻¹`, exactly as
in `quasiIso_Φ`. Elementwise both sides send `χ'` to `w ↦ χ'(φ(1 ⊗ 1 ⊗ w))`. -/
theorem jK_Φ_evL
    (hu : ((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u = ε.hom ≫ P.unitMap U W hW) :
    P.jK U M₁ M₂ Y ≫
      (secAb (P.R.over U) (op Y)).map ((overC U).map (P.Ψ M₁ M₂) ≫
        (homComplexOverIso P.isCommSheaf_R (P.sheafOf M₁) (P.sheafOf M₂) U).hom ≫
        homComplexMap₁ (P.isCommSheaf_R.over U)
          (u ≫ P.sheafOfOverMap U φ ≫ (P.restrSheafOfIso U M₁).inv)
          ((overC U).obj (P.sheafOf M₂))) ≫
      (homSectionsIso (P.isCommSheaf_R.over U) L ((overC U).obj (P.sheafOf M₂)) Y).hom ≫
      P.evL U W L ε M₂ Y =
    alongPre (P.D.res (leOfHom Y.hom)) (P.NY U M₂ Y) φ ≫
      alongEv (P.D.res (leOfHom Y.hom)) W (P.d_ρ U) (P.c_eq_zero U) (P.c_eq_zero Y.left)
        (P.NY U M₂ Y) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro χ'
  apply Subtype.ext
  funext p
  apply LinearMap.ext
  intro w
  refine Eq.trans (P.evLf_apply U W L ε M₂ Y n _ p w) ?_
  change _ = χ'.1 (φ.1 (fcι (P.ρ U) W w))
  refine (P.evLVal_map₁ U W L ε M₁ M₂ Y (u ≫ P.sheafOfOverMap U φ ≫ (P.restrSheafOfIso U M₁).inv) n
    ((((P.Ψ M₁ M₂).f n).val.app (op Y.left)).hom
      ((P.jKf U M₁ M₂ Y n).hom χ')) p w).trans ?_
  refine (P.ψ_sec_val U M₁ M₂ Y n p _ _).trans ?_
  have h := P.ι_app_res U W hW L ε u M₁ φ Y hu p w
  refine (congrArg (extAlong (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n)
    (P.homAt M₁ M₂ n (le_refl Y.left) ((P.jKf U M₁ M₂ Y n).hom χ'))) h).trans ?_
  exact P.extAlong_jK_totRes U M₁ M₂ Y n χ' _

end PreResolvingData

end Cohesive
