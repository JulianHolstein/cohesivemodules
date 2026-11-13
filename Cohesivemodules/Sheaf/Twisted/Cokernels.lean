import Cohesivemodules.Sheaf.Twisted.SubQuot
import Cohesivemodules.Sheaf.Twisted.Preadditive

set_option linter.style.header false

/-!
# Z3.h: cokernels of twisted sheaves

Blueprint item Z3.h (`blueprint/blueprint-tw.md` §3 C.2, C.2′). The cokernel of `f : M ⟶ N` has
components `cokernel (f.f α)` in `Mod (R.over U_α)`; its gluing map on `Over (U_α ⊓ U_β)` is
induced by `N.glueHom α β`, because `restrOver` preserves cokernels (`cokGlue`). It is a twisted
sheaf by `TwMod.ofEpi`: sections of a cokernel sheaf are only locally images of sections, so the
gluing maps cannot be defined section by section (C.2′). The component functors preserve these
cokernels.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

namespace TwMod

variable {M N : TwMod R U ch} (f : M ⟶ N)

/-- Z3.h: `resL (f α) ≫ N.glueHom ≫ resR (cokernel.π) = 0`. -/
theorem cokGlue_aux (α β : ι) :
    (resL α β).map (f.f α) ≫ N.glueHom α β ≫ (resR α β).map (cokernel.π (f.f β)) = 0 := by
  rw [← Category.assoc, TwMod.Hom.glue_comm f,Category.assoc, ← Functor.map_comp,
    cokernel.condition, Functor.map_zero, comp_zero]

/-- **Z3.h.** The gluing map of the cokernel on `Over (U_α ⊓ U_β)`: the morphism induced by
`N.glueHom α β` on cokernels (`restrOver` preserves cokernels, `PreservesCokernel.iso`). -/
def cokGlue (α β : ι) :
    (resL α β).obj (cokernel (f.f α)) ⟶ (resR α β).obj (cokernel (f.f β)) :=
  (PreservesCokernel.iso (resL α β) (f.f α)).hom ≫
    cokernel.desc ((resL α β).map (f.f α)) (N.glueHom α β ≫ (resR α β).map (cokernel.π (f.f β)))
      (cokGlue_aux f α β)

/-- Z3.h: `cokGlue` is compatible with the projections and the gluing of `N`. -/
theorem cokGlue_comp (α β : ι) :
    (resL α β).map (cokernel.π (f.f α)) ≫ cokGlue f α β =
      N.glueHom α β ≫ (resR α β).map (cokernel.π (f.f β)) := by
  unfold cokGlue
  rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

/-- **Z3.h.** [Căldăraru, §1.2]. The cokernel of a morphism of twisted sheaves: components
`cokernel (f.f α)`, gluing maps induced on sections by `cokGlue` (`TwMod.ofEpi`). -/
def cok : TwMod R U ch :=
  N.ofEpi (fun α => cokernel (f.f α)) (fun α => cokernel.π (f.f α)) (cokGlue f) (cokGlue_comp f)

/-- Z3.h: the projection to the cokernel, with components `cokernel.π (f.f α)`. -/
def cokπ : N ⟶ cok f :=
  N.homOfEpi (fun α => cokernel (f.f α)) (fun α => cokernel.π (f.f α)) (cokGlue f)
    (cokGlue_comp f)

/-- Z3.h: components of `cokπ` (rfl). -/
@[simp] theorem cokπ_f (α : ι) : (cokπ f).f α = cokernel.π (f.f α) := rfl

/-- Z3.h: `f ≫ cokπ f = 0`. -/
theorem comp_cokπ : f ≫ cokπ f = 0 :=
  TwMod.hom_ext fun α => cokernel.condition (f.f α)

/-- Z3.h: the factorization through the cokernel, with components
`cokernel.desc (f.f α) (g.f α)`. -/
def cokDesc {P : TwMod R U ch} (g : N ⟶ P) (hg : f ≫ g = 0) : cok f ⟶ P :=
  N.descOfEpi (fun α => cokernel (f.f α)) (fun α => cokernel.π (f.f α)) (cokGlue f)
    (cokGlue_comp f) g (fun α => cokernel.desc (f.f α) (g.f α) (by
      simpa only [comp_f, zero_f] using congrArg (fun k => k.f α) hg))
    (fun α => cokernel.π_desc _ _ _)

/-- **Z3.h.** The cokernel cofork `cokπ f` is a colimit. -/
def cokIsColimit : IsColimit (CokernelCofork.ofπ (cokπ f) (comp_cokπ f)) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun g hg => cokDesc f g hg)
    (fun g hg => TwMod.hom_ext fun α => by
      simp only [comp_f]
      exact cokernel.π_desc _ _ _)
    (fun g hg m hm => TwMod.hom_ext fun α => by
      have h1 : (cokπ f ≫ m).f α = g.f α := by rw [hm]
      rw [comp_f, cokπ_f] at h1
      refine (cancel_epi (cokernel.π (f.f α))).mp ?_
      exact h1.trans (cokernel.π_desc _ _ _).symm)

/-- **Z3.h.** Twisted sheaves have cokernels. -/
instance : HasCokernels (TwMod R U ch) :=
  ⟨fun f => HasColimit.mk ⟨_, cokIsColimit f⟩⟩

variable (R U ch) in
/-- **Z3.h.** The component functors preserve cokernels (the cokernel of `f` has components the
cokernels of `f.f α`). -/
instance comp_preservesCokernel (α : ι) {M N : TwMod R U ch} (f : M ⟶ N) :
    PreservesColimit (parallelPair f 0) (TwMod.comp R U ch α) :=
  preservesColimit_of_preserves_colimit_cocone (cokIsColimit f)
    ((isColimitMapCoconeCoforkEquiv (TwMod.comp R U ch α) _).symm
      (cokernelIsCokernel (f.f α)))

end TwMod

end Cohesive
