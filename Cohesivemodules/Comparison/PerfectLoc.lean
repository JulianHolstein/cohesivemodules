import Cohesivemodules.Comparison.AlphaOver
import Cohesivemodules.Comparison.Setup
import Cohesivemodules.Comparison.PerfectAux

set_option linter.style.header false

/-!
# C2 auxiliary: the unit map `W → Γ(α_U(𝒜(U) ⊗_{O(U)} W))`

For a bounded complex `W` of finitely generated projective `O(U)`-modules, the chain map
`W^p → Γ(α_U(𝒜(U) ⊗ W)^p)`, `w ↦ 1 ⊗ 1 ⊗ w`, where `Γ` is evaluation at the terminal object
`Over.mk (𝟙 U)` of the over-site of `U`; its lift `u : W̃ → α_U(𝒜(U) ⊗ W)` is the map of C2
(`Comparison/Perfect.lean`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace TensorProduct

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X)
  (W : CochainComplex (ModuleCat.{0} (P.O.obj.obj (op U))) ℤ)
  (hW : IsBoundedFGProj (P.O.obj.obj (op U)) W)

/-- The cohesive module `𝒜(U) ⊗_{O(U)} W` of C2 (A10). -/
abbrev fcMod : CohesiveModule (P.D.𝒜 U) :=
  CohesiveModule.fromComplex (ρ := P.ρ U) W (P.d_ρ U) (P.c_eq_zero U) hW

/-- The element `1 ⊗ 1 ⊗ w` of `α_U(𝒜(U) ⊗ W)^p(U)`. -/
def unitElt (p : ℤ) (w : W.X p) : P.sheafOfSec (P.fcMod U W hW) p (le_refl U) :=
  ⟨bcF (P.D.res (le_refl U)) (P.fcMod U W hW).Q (fcι (P.ρ U) W w),
    bcF_mem_totDeg _ _ (fcι_mem (P.ρ U) W w)⟩

/-- `w ↦ 1 ⊗ 1 ⊗ w` is `O(U)`-linear. -/
def unitLin (p : ℤ) :
    W.X p →ₗ[P.O.obj.obj (op U)] P.sheafOfSec (P.fcMod U W hW) p (le_refl U) where
  toFun := P.unitElt U W hW p
  map_add' w w' := by
    apply Subtype.ext
    change bcF _ _ (fcι (P.ρ U) W (w + w')) =
      bcF _ _ (fcι (P.ρ U) W w) + bcF _ _ (fcι (P.ρ U) W w')
    rw [fcι_add, map_add]
    rfl
  map_smul' r w := by
    apply Subtype.ext
    refine Eq.trans ?_ (P.sheafOfSec_smul_val (P.fcMod U W hW) r (P.unitElt U W hW p w)).symm
    change bcF (P.D.res (le_refl U)) (FCGen (P.ρ U) W) (fcι (P.ρ U) W (r • w)) =
      ((P.ρ U r : P.D.𝒜 U 0) : P.D.A U) •
        bcF (P.D.res (le_refl U)) (FCGen (P.ρ U) W) (fcι (P.ρ U) W w)
    rw [fcι_smulR, bcF_smul, P.D.res_id]

/-- The map `W^p → Γ(α_U(𝒜(U) ⊗ W)^p)`. -/
def unitHom (p : ℤ) : W.X p ⟶
    (gammaT (P.R.over U) (Over.mk (𝟙 U))).obj ((P.sheafOfOver U (P.fcMod U W hW)).X p) :=
  ModuleCat.ofHom (P.unitLin U W hW p)

/-- `unitHom` commutes with the differentials. -/
theorem unitHom_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    W.d i j ≫ P.unitHom U W hW j = P.unitHom U W hW i ≫
      (((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P.sheafOfOver U (P.fcMod U W hW))).d i j := by
  obtain rfl : i + 1 = j := hij
  have e1 : (P.sheafOfOver U (P.fcMod U W hW)).d i (i + 1) = P.sheafOfOverD U (P.fcMod U W hW) i :=
    CochainComplex.of_d _ _ _
  have e2 : (((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (P.sheafOfOver U (P.fcMod U W hW))).d i (i + 1) =
      (gammaT (P.R.over U) (Over.mk (𝟙 U))).map (P.sheafOfOverD U (P.fcMod U W hW) i) := by
    change (gammaT (P.R.over U) (Over.mk (𝟙 U))).map
      ((P.sheafOfOver U (P.fcMod U W hW)).d i (i + 1)) = _
    exact congrArg _ e1
  rw [e2]
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun w => ?_
  apply Subtype.ext
  change bcF (P.D.res (le_refl U)) (FCGen (P.ρ U) W) (fcι (P.ρ U) W (dW W i w)) =
    ((P.fcMod U W hW).baseChange (P.D.res (le_refl U))).X
      (bcF (P.D.res (le_refl U)) (FCGen (P.ρ U) W) (fcι (P.ρ U) W w))
  exact (congrArg (bcF (P.D.res (le_refl U)) (FCGen (P.ρ U) W))
    (fc_extend_fcι W (P.d_ρ U) w)).symm.trans
    (bc_extend_bcF (P.D.res (le_refl U)) (P.fcMod U W hW).toQuasiCohesive
      (fcι (P.ρ U) W w)).symm

/-- The chain map `W ⟶ Γ α_U(𝒜(U) ⊗ W)`, `w ↦ 1 ⊗ 1 ⊗ w`. -/
def unitMap : W ⟶ ((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (P.sheafOfOver U (P.fcMod U W hW)) where
  f p := P.unitHom U W hW p
  comm' i j hij := (P.unitHom_comm U W hW i j hij).symm

end PreResolvingData

end Cohesive
