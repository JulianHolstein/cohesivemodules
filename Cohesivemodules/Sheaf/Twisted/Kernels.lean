import Cohesivemodules.Sheaf.Twisted.SubQuot
import Cohesivemodules.Sheaf.Twisted.Preadditive

set_option linter.style.header false

/-!
# Z3.h: kernels of twisted sheaves

Blueprint item Z3.h (`blueprint/blueprint-tw.md` §3 C.2, C.2′). The kernel of `f : M ⟶ N` has
components `kernel (f.f α)` in `Mod (R.over U_α)`; its gluing map on `Over (U_α ⊓ U_β)` is induced
by `M.glueHom α β`, because `restrOver` preserves kernels (`kerGlue`). It is a twisted sheaf by
`TwMod.ofMono`. The component functors preserve these kernels.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

namespace TwMod

variable {M N : TwMod R U ch} (f : M ⟶ N)

/-- Z3.h: `resL (kernel.ι) ≫ M.glueHom ≫ resR (f β) = 0`. -/
theorem kerGlue_aux (α β : ι) :
    ((resL α β).map (kernel.ι (f.f α)) ≫ M.glueHom α β) ≫ (resR α β).map (f.f β) = 0 := by
  rw [Category.assoc, ← TwMod.Hom.glue_comm f, ← Functor.map_comp_assoc, kernel.condition,
    Functor.map_zero, zero_comp]

/-- **Z3.h.** The gluing map of the kernel on `Over (U_α ⊓ U_β)`: the morphism induced by
`M.glueHom α β` on kernels (`restrOver` preserves kernels, `PreservesKernel.iso`). -/
def kerGlue (α β : ι) :
    (resL α β).obj (kernel (f.f α)) ⟶ (resR α β).obj (kernel (f.f β)) :=
  kernel.lift ((resR α β).map (f.f β)) ((resL α β).map (kernel.ι (f.f α)) ≫ M.glueHom α β)
    (kerGlue_aux f α β) ≫ (PreservesKernel.iso (resR α β) (f.f β)).inv

/-- Z3.h: `kerGlue` is compatible with the inclusions and the gluing of `M`. -/
theorem kerGlue_comp (α β : ι) :
    kerGlue f α β ≫ (resR α β).map (kernel.ι (f.f β)) =
      (resL α β).map (kernel.ι (f.f α)) ≫ M.glueHom α β := by
  unfold kerGlue
  rw [Category.assoc, PreservesKernel.iso_inv_ι, kernel.lift_ι]

/-- **Z3.h.** [Căldăraru, §1.2]. The kernel of a morphism of twisted sheaves: components
`kernel (f.f α)`, gluing maps induced on sections by `kerGlue` (`TwMod.ofMono`). -/
def ker : TwMod R U ch :=
  M.ofMono (fun α => kernel (f.f α)) (fun α => kernel.ι (f.f α)) (kerGlue f) (kerGlue_comp f)

/-- Z3.h: the inclusion of the kernel, with components `kernel.ι (f.f α)`. -/
def kerι : ker f ⟶ M :=
  M.homOfMono (fun α => kernel (f.f α)) (fun α => kernel.ι (f.f α)) (kerGlue f) (kerGlue_comp f)

/-- Z3.h: components of `kerι` (rfl). -/
@[simp] theorem kerι_f (α : ι) : (kerι f).f α = kernel.ι (f.f α) := rfl

/-- Z3.h: `kerι f ≫ f = 0`. -/
theorem kerι_comp : kerι f ≫ f = 0 :=
  TwMod.hom_ext fun α => kernel.condition (f.f α)

/-- Z3.h: the factorization through the kernel, with components `kernel.lift (f.f α) (g.f α)`. -/
def kerLift {P : TwMod R U ch} (g : P ⟶ M) (hg : g ≫ f = 0) : P ⟶ ker f :=
  M.liftOfMono (fun α => kernel (f.f α)) (fun α => kernel.ι (f.f α)) (kerGlue f) (kerGlue_comp f)
    g (fun α => kernel.lift (f.f α) (g.f α) (by
      simpa only [comp_f, zero_f] using congrArg (fun k => k.f α) hg))
    (fun α => kernel.lift_ι _ _ _)

/-- **Z3.h.** The kernel fork `kerι f` is a limit. -/
def kerIsLimit : IsLimit (KernelFork.ofι (kerι f) (kerι_comp f)) :=
  KernelFork.IsLimit.ofι _ _ (fun {P} g hg => kerLift f g hg)
    (fun {P} g hg => TwMod.hom_ext fun α => kernel.lift_ι _ _ _)
    (fun {P} g hg m hm => TwMod.hom_ext fun α => by
      refine (cancel_mono (kernel.ι (f.f α))).1 ?_
      have h := congrArg (fun k => k.f α) hm
      simp only [comp_f, kerι_f] at h
      exact h.trans (kernel.lift_ι (f.f α) (g.f α) _).symm)

/-- **Z3.h.** Twisted sheaves have kernels. -/
instance : HasKernels (TwMod R U ch) :=
  ⟨fun f => HasLimit.mk ⟨_, kerIsLimit f⟩⟩

variable (R U ch) in
/-- **Z3.h.** The component functors preserve kernels (the kernel of `f` has components the kernels
of `f.f α`). -/
instance comp_preservesKernel (α : ι) {M N : TwMod R U ch} (f : M ⟶ N) :
    PreservesLimit (parallelPair f 0) (TwMod.comp R U ch α) :=
  preservesLimit_of_preserves_limit_cone (kerIsLimit f)
    ((KernelFork.isLimitMapConeEquiv _ _).symm
      (IsLimit.ofIsoLimit (kernelIsKernel (f.f α)) (Fork.ext (Iso.refl _) (Category.id_comp _))))

end TwMod

end Cohesive
