import Cohesivemodules.Sheaf.Twisted.PushAdj
import Cohesivemodules.Sheaf.Twisted.Abelian

set_option linter.style.header false

/-!
# Z3.i: twisted sheaves have enough injectives

Blueprint item Z3.i (`blueprint/blueprint-tw.md` §3 C.4′(f)–(g)). The component functors preserve
monomorphisms, so their right adjoints `push T α` preserve injective objects. For `M`, choose monos
`M_α ↪ I_α` into injectives; the induced `M ⟶ ∏_α push T α I_α` is a monomorphism into an
injective object (finite product).

## Deviations
[A, Lemma 7.1.6] (via [Toda, §4.3]) for arbitrary covers; here the cover is finite (twist cocycles
are on finite covers, `TwistCocycle`), so the product is finite.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}

namespace TwMod

variable {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- **Z3.i.** A morphism of twisted sheaves whose components are monomorphisms is a monomorphism. -/
theorem mono_of_mono_f {M N : TwMod R U ch} (f : M ⟶ N) [∀ α, Mono (f.f α)] : Mono f :=
  ⟨fun g h hgh => TwMod.hom_ext fun α =>
    (cancel_mono (f.f α)).1 (by simpa only [TwMod.comp_f] using congrArg (fun k => k.f α) hgh)⟩

variable (R U ch) in
/-- **Z3.i.** The component functors preserve monomorphisms (they preserve kernels). -/
instance comp_preservesMonomorphisms (α : ι) :
    (TwMod.comp R U ch α).PreservesMonomorphisms :=
  NormalEpiCategory.preservesMonomorphisms_of_preservesKernels (TwMod.comp R U ch α)

end TwMod

variable (T : TwistCocycle R)

/-- **Z3.i.** The twisted pushforward preserves injective objects (right adjoint of the
component functor, which preserves monomorphisms). -/
instance push_preservesInjectiveObjects (α : T.ι) : (push T α).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (pushAdj T α)

/-- Z3.i: the morphism `pushLift g` followed by the counit is `g` (`pushHomEquiv`). -/
theorem pushLift_f_comp_counit (α : T.ι) {M : TwMod R T.U T.ch}
    {N : Mod ((ringOf R).over (T.U α))} (g : M.M α ⟶ N) :
    (pushLift T α g).f α ≫ pushCounit T α N = g :=
  (pushHomEquiv T α M N).apply_symm_apply g

/-- **Z3.i.** [A, Lemma 7.1.6], [Toda, §4.3]. Twisted sheaves of modules on a finite cover with a
normalized Čech 2-cocycle of units have enough injectives. -/
instance enoughInjectives : EnoughInjectives (TwMod R T.U T.ch) := by
  refine ⟨fun M => ⟨⟨∏ᶜ (fun α => (push T α).obj (Injective.under (M.M α))), inferInstance,
    Pi.lift (fun α => pushLift T α (Injective.ι (M.M α))), ?_⟩⟩⟩
  have h : ∀ β, Mono ((Pi.lift (fun α => pushLift T α (Injective.ι (M.M α)))).f β) := by
    intro β
    have h1 : Mono ((pushLift T β (Injective.ι (M.M β))).f β) :=
      mono_of_mono_fac (pushLift_f_comp_counit T β (Injective.ι (M.M β)))
    have h2 : (Pi.lift (fun α => pushLift T α (Injective.ι (M.M α)))).f β ≫
        (Pi.π (fun α => (push T α).obj (Injective.under (M.M α))) β).f β =
        (pushLift T β (Injective.ι (M.M β))).f β := by
      rw [← TwMod.comp_f, Pi.lift_comp_π]
    exact mono_of_mono_fac h2
  exact TwMod.mono_of_mono_f _

end Cohesive
