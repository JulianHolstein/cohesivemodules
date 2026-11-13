import Cohesivemodules.Comparison.AlphaOver
import Cohesivemodules.Comparison.AlphaOverAux
import Cohesivemodules.Sheaf.RestrOver

set_option linter.style.header false

/-!
# Z3.p: `α_U(N)|U′ ≅ α_{U′}(N|U′)` (C1.c between opens)

Blueprint item Z3.p (`blueprint/blueprint-tw.md` §3 E.2, "C2's over-site core, base generalized
`⊤ → U₀`", V3). For pre-resolving data `P`, opens `U′ ≤ U` and a cohesive module `N` over `𝒜(U)`:
the restriction to `Over U′` (`restrOver`) of `α_U(N)` (C1.c, `sheafOfOver`) is `α_{U′}` of the base
change `N|U′` along `res : 𝒜(U) → 𝒜(U′)`. The proof of `restrSheafOfIso` (the case `U = ⊤` with
`restr`) with base `U` in place of `X`: sectionwise A9's comparison `cmpTot`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) {U U' : Opens X} (hU' : U' ≤ U) (N : CohesiveModule (P.D.𝒜 U))

/-- Z3.p: `res_{V ≤ U} = res_{V ≤ U′} ∘ res_{U′ ≤ U}` as dga maps. -/
theorem res_comp_eq' {V : Opens X} (hV : V ≤ U') :
    (P.D.res hV).comp (P.D.res hU') = P.D.res (hV.trans hU') :=
  dgaHom_ext' fun a => P.D.res_comp hU' hV a

/-- **Z3.p.** Sectionwise comparison `α_U(N)^n(V) ≃ α_{U′}(N|U′)^n(V)` for `V ≤ U′ ≤ U`
(`cmpTot`, A9). -/
def restrOverEquiv (n : ℤ) {V : Opens X} (hV : V ≤ U') :
    P.sheafOfSec N n (hV.trans hU') ≃ₗ[P.O.obj.obj (op V)]
      P.sheafOfSec (N.baseChange (P.D.res hU')) n hV where
  toFun x := ⟨cmpTot (P.D.res hU') (P.D.res hV) (P.D.res (hV.trans hU')) (P.res_comp_eq' hU' hV)
    N.toQuasiCohesive x.1, cmpTot_mem _ _ _ _ _ x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (cmpTot_smul _ _ _ _ _ (P.ρ V f : P.D.A V) x.1)
  invFun y := ⟨cmpTotInv (P.D.res hU') (P.D.res hV) (P.D.res (hV.trans hU'))
    (P.res_comp_eq' hU' hV) N.toQuasiCohesive y.1, cmpTotInv_mem _ _ _ _ _ y.2⟩
  left_inv x := Subtype.ext (cmpTotInv_cmpTot _ _ _ _ _ x.1)
  right_inv y := Subtype.ext (cmpTot_cmpTotInv _ _ _ _ _ y.1)

/-- **Z3.p.** `α_U(N)^n|U′ ≅ α_{U′}(N|U′)^n` (termwise). -/
def restrOverIsoSh (n : ℤ) :
    (restrOver P.R hU').obj (P.sheafOfOverSh U N n) ≅
      P.sheafOfOverSh U' (N.baseChange (P.D.res hU')) n :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (P.restrOverEquiv hU' N n (leOfHom V.unop.hom)).toModuleIso) (by
        intro V W f
        apply ModuleCat.hom_ext
        refine DFunLike.ext _ _ fun x => ?_
        apply Subtype.ext
        exact cmpTot_bcTotRes (P.D.res hU') (P.D.res (leOfHom V.unop.hom))
          (P.D.res ((leOfHom V.unop.hom).trans hU'))
          (P.res_comp_eq' hU' _) N.toQuasiCohesive (P.D.res (leOfHom f.unop.left))
          (P.D.res ((leOfHom f.unop.left).trans (leOfHom V.unop.hom)))
          (P.D.res (((leOfHom f.unop.left).trans (leOfHom V.unop.hom)).trans hU'))
          (P.res_comp_eq' hU' _) (P.D.res_comp _ _) (P.D.res_comp _ _) x.1))

/-- **Z3.p.** C1.c between opens. `α_U(N)|U′ ≅ α_{U′}(N|U′)` as complexes on `Over U′`, for
`U′ ≤ U` and `N` over `𝒜(U)` (`restrSheafOfIso` is the case `U = ⊤`, with `restr`). -/
def restrOverSheafOfIso :
    ((restrOver P.R hU').mapHomologicalComplex (ComplexShape.up ℤ)).obj (P.sheafOfOver U N) ≅
      P.sheafOfOver U' (N.baseChange (P.D.res hU')) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => P.restrOverIsoSh hU' N n) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have e1 : (P.sheafOfOver U' (N.baseChange (P.D.res hU'))).d i (i + 1) =
        P.sheafOfOverD U' (N.baseChange (P.D.res hU')) i := CochainComplex.of_d _ _ _
    have e2 : (P.sheafOfOver U N).d i (i + 1) = P.sheafOfOverD U N i := CochainComplex.of_d _ _ _
    have e3 : (((restrOver P.R hU').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P.sheafOfOver U N)).d i (i + 1) = (restrOver P.R hU').map (P.sheafOfOverD U N i) := by
      change (restrOver P.R hU').map ((P.sheafOfOver U N).d i (i + 1)) = _
      rw [e2]
      rfl
    rw [e1, e3]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact cmpTot_X (P.D.res hU') (P.D.res (leOfHom V.unop.hom))
      (P.D.res ((leOfHom V.unop.hom).trans hU'))
      (P.res_comp_eq' hU' _) N.toQuasiCohesive x.1)

end PreResolvingData

end Cohesive
