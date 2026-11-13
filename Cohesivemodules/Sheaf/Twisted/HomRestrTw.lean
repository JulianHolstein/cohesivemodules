import Cohesivemodules.Sheaf.Twisted.HomComplexTw
import Cohesivemodules.Sheaf.Twisted.HomRestrOver

set_option linter.style.header false

/-!
# Z3.r: `𝓗om^tw(K, L)|V ≅ 𝓗om(K_α|V, L_α|V)` for `V ≤ U_α`

Blueprint item Z3.r (`blueprint/blueprint-tw.md` §3 F′ (f)). For `V ≤ U_α` the restriction of the
twisted Hom complex to `V` is the untwisted Hom complex of the restricted components:
`restr V ≅ restr U_α ⋙ restrOver (V ≤ U_α)` (`restr_restrOver`), `twHomRestrIso` on `U_α`, and
`restrOver` commutes with Hom complexes (`homComplexRestrOverIso`). Natural in both variables.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}
  (hch : ∀ α β, ch α β α = 1) (hU : ⨆ α, U α = ⊤) (α : ι) {V : Opens X} (hV : V ≤ U α)

/-- **Z3.r (F′ (f)).** `𝓗om^tw(K, L)|V ≅ 𝓗om(K_α|V, L_α|V)` for `V ≤ U_α`, as complexes of
sheaves on `Over V`. -/
def twHomRestrOverIso (K L : CochainComplex (TwMod R U ch) ℤ) :
    ((restr (ringOf R) V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (twHomComplex hch K L hU) ≅
      homSheafComplex (isCommSheaf_over V) ((restrOverC hV).obj ((compC α).obj K))
        ((restrOverC hV).obj ((compC α).obj L)) :=
  ((NatIso.mapHomologicalComplex (restr_restrOver (ringOf R) hV) (ComplexShape.up ℤ)).app
      (twHomComplex hch K L hU)).symm ≪≫
    (restrOverC hV).mapIso (twHomRestrIso hch K L hU α) ≪≫ homComplexRestrOverIso hV _ _

/-- **Z3.r.** `twHomRestrOverIso` is natural in the target. -/
theorem twHomRestrOverIso_naturality₂ (K : CochainComplex (TwMod R U ch) ℤ)
    {L L' : CochainComplex (TwMod R U ch) ℤ} (g : L ⟶ L') :
    ((restr (ringOf R) V).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (twHomMap₂ hch hU K g) ≫ (twHomRestrOverIso hch hU α hV K L').hom =
      (twHomRestrOverIso hch hU α hV K L).hom ≫
        homComplexMap₂ (isCommSheaf_over V) ((restrOverC hV).obj ((compC α).obj K))
          ((restrOverC hV).map ((compC α).map g)) := by
  have h1 : ((restr (ringOf R) V).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (twHomMap₂ hch hU K g) ≫ ((NatIso.mapHomologicalComplex (restr_restrOver (ringOf R) hV)
          (ComplexShape.up ℤ)).app (twHomComplex hch K L' hU)).inv =
      ((NatIso.mapHomologicalComplex (restr_restrOver (ringOf R) hV)
          (ComplexShape.up ℤ)).app (twHomComplex hch K L hU)).inv ≫
        (restrOverC hV).map (((restr (ringOf R) (U α)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (twHomMap₂ hch hU K g)) :=
    (NatIso.mapHomologicalComplex (restr_restrOver (ringOf R) hV)
      (ComplexShape.up ℤ)).inv.naturality (twHomMap₂ hch hU K g)
  have h2 := congrArg (restrOverC hV).map (twHomRestrIso_naturality₂ hch hU K g α)
  have h3 := homComplexRestrOverIso_naturality₂ hV ((compC α).obj K) ((compC α).map g)
  simp only [twHomRestrOverIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp] at h2
  rw [← Category.assoc, h1]
  simp only [Category.assoc]
  rw [reassoc_of% h2, h3]

/-- **Z3.r.** `twHomRestrOverIso` is natural in the source. -/
theorem twHomRestrOverIso_naturality₁ {K K' : CochainComplex (TwMod R U ch) ℤ} (f : K' ⟶ K)
    (L : CochainComplex (TwMod R U ch) ℤ) :
    ((restr (ringOf R) V).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (twHomMap₁ hch hU f L) ≫ (twHomRestrOverIso hch hU α hV K' L).hom =
      (twHomRestrOverIso hch hU α hV K L).hom ≫
        homComplexMap₁ (isCommSheaf_over V) ((restrOverC hV).map ((compC α).map f))
          ((restrOverC hV).obj ((compC α).obj L)) := by
  have h1 : ((restr (ringOf R) V).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (twHomMap₁ hch hU f L) ≫ ((NatIso.mapHomologicalComplex (restr_restrOver (ringOf R) hV)
          (ComplexShape.up ℤ)).app (twHomComplex hch K' L hU)).inv =
      ((NatIso.mapHomologicalComplex (restr_restrOver (ringOf R) hV)
          (ComplexShape.up ℤ)).app (twHomComplex hch K L hU)).inv ≫
        (restrOverC hV).map (((restr (ringOf R) (U α)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (twHomMap₁ hch hU f L)) :=
    (NatIso.mapHomologicalComplex (restr_restrOver (ringOf R) hV)
      (ComplexShape.up ℤ)).inv.naturality (twHomMap₁ hch hU f L)
  have h2 := congrArg (restrOverC hV).map (twHomRestrIso_naturality₁ hch hU f L α)
  have h3 := homComplexRestrOverIso_naturality₁ hV ((compC α).map f) ((compC α).obj L)
  simp only [twHomRestrOverIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp] at h2
  rw [← Category.assoc, h1]
  simp only [Category.assoc]
  rw [reassoc_of% h2, h3]

end Cohesive
