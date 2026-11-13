import Cohesivemodules.Comparison.TwistDatumBasic
import Cohesivemodules.Forms.TwistExists
import Cohesivemodules.Forms.CurvedRestrictDef
import Cohesivemodules.Sheaf.Twisted.Abelian
import Cohesivemodules.Sheaf.Twisted.Injective
import Cohesivemodules.Sheaf.Twisted.Perfect
import Cohesivemodules.Sheaf.Twisted.GlueEquiv
import Cohesivemodules.Sheaf.Twisted.Rescale
import Cohesivemodules.Sheaf.Twisted.FlatResolution
import Cohesivemodules.Comparison.SheafDataMap
import Cohesivemodules.Comparison.TwistedFunctorDef
import Cohesivemodules.Comparison.TwistedPerfect

set_option linter.style.header false

/-!
# Checks for Z3 (blueprint-tw §5)

Non-vacuity and special cases of the twisted definitions, filled in as stage 1–3 items land.
-/

noncomputable section

namespace Cohesive.Checks

open TopologicalSpace Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- Z3.a non-vacuity: `withC` with the curvature of the instance gives the instance back. -/
example : (GCDga.withC (inferInstance : GCDga (dolbeault E X)) 0 (Submodule.zero_mem _)
    (map_zero _)) = (inferInstance : GCDga (dolbeault E X)) := rfl

/-- Z3.c (P15): at `h = 0` the curved Dolbeault algebra is the Dolbeault algebra of the main
statement, with the same instance. -/
example : HoP (curvedDolbeault (0 : DolbeaultClosed2 E X)) = HoP (dolbeault E X) := rfl

/-- Z3.c: the curvature of `curvedDolbeault h` is `h`. -/
example (h : DolbeaultClosed2 E X) : GCDga.c (𝒜 := curvedDolbeault h) = h.1 := rfl

/-- Z3.e: over an open `U`, the curved instance at `h = 0` has curvature `0` (propositionally:
`res 0 = 0`), and its curvature is `h|U` in general (rfl). -/
example (U : Opens X) : (curvedInstU (0 : DolbeaultClosed2 E X) U).c = 0 := map_zero _

example (h : DolbeaultClosed2 E X) (U : Opens X) :
    (curvedInstU h U).c = dolbeaultRes E (le_top : U ≤ ⊤) h.1 := rfl

variable [T2Space X] [CompactSpace X]

/-- Z3.m: for the curved Dolbeault data, `α(M)^n` is a sheaf of `O`-modules for every cohesive
module `M` over the curved algebra `(𝒜(X), ∂̄, h)` (the copy of C1 over `DgaSheafData`). -/
example (h : DolbeaultClosed2 E X) (M : CohesiveModule (curvedDolbeault h)) (n : ℤ) :
    Mod (ringOf (holSheaf E X)) :=
  ((dolbeaultPreData E X).toSheafData.withCurvature h.1 h.2.1 h.2.2).sheafOfSh M n

/-- Z3.m: at `h = 0` the copy is the frozen `α(M)^n` of C1, by `rfl`. -/
example (M : CohesiveModule (dolbeault E X)) (n : ℤ) :
    ((dolbeaultPreData E X).toSheafData.withCurvature (0 : DolbeaultClosed2 E X).1
      (0 : DolbeaultClosed2 E X).2.1 (0 : DolbeaultClosed2 E X).2.2).sheafOfSh M n =
      (dolbeaultPreData E X).sheafOfSh M n :=
  rfl

/-- Z3.n: for the Dolbeault data, a closed `h` and a twist datum `T`, the twisted functor
`J_T : Ho(P_{(𝒜_X(X), ∂̄, h)}) ⥤ D(X, ȟ)`. -/
example (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    [HasDerivedCategory.{0} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)] :
    CategoryTheory.Functor (HoP (curvedDolbeault h))
      (DerivedCategory (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)) :=
  T.twistedJ h.2.1 h.2.2

/-- Z3.p (C2^tw): `J_T` lands in `D_perf(X, ȟ)`. -/
example (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    [HasDerivedCategory.{0} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)]
    (M : HoP (curvedDolbeault h)) :
    TwPerf (dolbeaultPreData E X).toSheafData.O T.U T.ch ((T.twistedJ h.2.1 h.2.2).obj M) :=
  twPerf_twistedJ_obj h T M

/-- Z3.d non-vacuity: every closed `h ∈ 𝒜^{0,2}(X)` has a twist datum. -/
example (h : DolbeaultClosed2 E X) : Nonempty (TwistData E X h) := exists_twistData E h

/-- Z3.c non-vacuity (K8): a twist datum for `h = 0`. -/
example : TwistData E X 0 := trivialTwistDatum (dolbeaultPreData E X).toSheafData

/-- Z3.c non-vacuity (K14): a twist datum for every exact `h = ∂̄β`, `β ∈ 𝒜^{0,1}(X)`. -/
example (β : DolbeaultAlg E (⊤ : Opens X)) (hβ : β ∈ dolbeault E X 1) :
    TwistData E X ⟨GCDga.d (𝒜 := dolbeault E X) β,
      by simpa using GCDga.d_mem (𝒜 := dolbeault E X) hβ, GCDga.d_d _⟩ :=
  exactTwistDatum (dolbeaultPreData E X).toSheafData β hβ _ rfl

section TwMod

open CategoryTheory Limits Opposite

variable {X} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} {ι : Type}
  {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-- Z3.h: twisted sheaves form an abelian category, for every family of units `ch`. -/
example : Abelian (TwMod R U ch) := inferInstance

/-- Z3.h: kernels are componentwise. -/
example {M N : TwMod R U ch} (f : M ⟶ N) (α : ι) : (kernel f).M α ≅ kernel (f.f α) :=
  PreservesKernel.iso (TwMod.comp R U ch α) f

/-- Z3.h: cokernels are componentwise. -/
example {M N : TwMod R U ch} (f : M ⟶ N) (α : ι) : (cokernel f).M α ≅ cokernel (f.f α) :=
  PreservesCokernel.iso (TwMod.comp R U ch α) f

/-- Z3.h non-vacuity: for the trivial cocycle, a sheaf of modules on `X` is a twisted sheaf, and
the abelian structure is available on it. -/
example (N : Mod (ringOf R)) : IsZero (kernel (𝟙 (TwMod.ofSheaf R U N))) :=
  isZero_kernel_of_mono _

/-- Z3.i: twisted sheaves on a twist cocycle have enough injectives. -/
example (T : TwistCocycle R) : EnoughInjectives (TwMod R T.U T.ch) := inferInstance

/-- Z3.i: the component functor is left adjoint to Toda's twisted pushforward. -/
example (T : TwistCocycle R) (α : T.ι) : TwMod.comp R T.U T.ch α ⊣ push T α := pushAdj T α

/-- Z3.i: for `g : M_α ⟶ N`, the corresponding `M ⟶ push N` recovers `g` through the counit. -/
example (T : TwistCocycle R) (α : T.ι) {M : TwMod R T.U T.ch}
    {N : Mod ((ringOf R).over (T.U α))} (g : M.M α ⟶ N) :
    (pushLift T α g).f α ≫ pushCounit T α N = g :=
  pushLift_f_comp_counit T α g

/-- Z3.k (S12): for an open cover of `X`, twisted sheaves with trivial cocycle are sheaves of
`R`-modules on `X` (gluing is an equivalence). -/
example (hU : ⨆ α, U α = ⊤) : TwMod R U (fun _ _ _ => 1) ≌ Mod (ringOf R) := glueEquiv hU

/-- Z3.k: the gluing of `ofSheaf N` is `N` again. -/
example (hU : ⨆ α, U α = ⊤) (N : Mod (ringOf R)) : (glue R U).obj (TwMod.ofSheaf R U N) ≅ N :=
  haveI := isIso_toGlueOfSheaf hU N
  (asIso (toGlueOfSheaf N)).symm

/-- Z3.k: `ofSheaf (glue M) ≅ M` for any family of opens (no cover needed). -/
example (M : TwMod R U (fun _ _ _ => 1)) : TwMod.ofSheaf R U ((glue R U).obj M) ≅ M :=
  ofSheafGlueIso M

/-- Z3.k: rescaling the gluing maps by `g` is an equivalence `TwMod R U ȟ ≌ TwMod R U (ȟ·ďg)`;
transport along `ȟ = ȟ'` is the case `g = 1`. -/
example {ch' : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}
    {g : ∀ α β, (R.obj.obj (op (U α ⊓ U β)))ˣ} (h : IsRescale ch ch' g) :
    TwMod R U ch ≌ TwMod R U ch' :=
  rescale h

example : TwMod R U ch ≌ TwMod R U ch := rescale (isRescale_of_eq rfl)

/-- Z3.l: the twisted extension by zero is left adjoint to the component functor. -/
example (T : TwistCocycle R) (α : T.ι) : extTw T α ⊣ TwMod.comp R T.U T.ch α := extTwAdj T α

/-- Z3.l (C.5): the component functors preserve injective objects. -/
example (T : TwistCocycle R) (α : T.ι) {I : TwMod R T.U T.ch} [Injective I] :
    Injective (I.M α) :=
  (TwMod.comp R T.U T.ch α).injective_obj I

/-- Z3.l: for `f : N ⟶ M_α`, the lift `extTw α N ⟶ M` recovers `f` through the unit. -/
example (T : TwistCocycle R) (α : T.ι) {N : Mod ((ringOf R).over (T.U α))}
    {M : TwMod R T.U T.ch} (f : N ⟶ M.M α) :
    extTwUnit T α N ≫ (extTwLift T α f).f α = f :=
  extTwUnit_comp_lift T α f

/-- Z3.l: the extension by zero of a flat sheaf is flat (S8.b, general form). -/
example {V : TopologicalSpace.Opens X} {F : Mod ((ringOf R).over V)}
    (hF : IsFlat (R.over V) F) : IsFlat R (extX V F) :=
  isFlat_extX hF

/-- Z3.l (C.8, G.1): complexes of twisted sheaves strictly zero above `b` have componentwise flat
resolutions strictly zero above `b`. -/
example (T : TwistCocycle R) (K : CochainComplex (TwMod R T.U T.ch) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] :
    ∃ (F : CochainComplex (TwMod R T.U T.ch) ℤ) (f : F ⟶ K),
      F.IsStrictlyLE b ∧ (∀ n, TwIsFlat (F.X n)) ∧ QuasiIso f :=
  exists_quasiIso_twIsFlat T K b

end TwMod

section TwPerf

open CategoryTheory Limits Opposite

variable {X}

omit [T2Space X] [CompactSpace X]

/-- Z3.j (h): faithfulness check of `IsPerfectOver` against the frozen S9.b `IsPerfect`. -/
example {R : RingSheaf X} (K : CochainComplex (Mod R) ℤ) :
    IsPerfectOver (((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ↔
      IsPerfect K :=
  isPerfectOver_restr_top_iff K

/-- A summand of a finite free module in degree `0` is a strictly perfect complex (any site). -/
theorem isStrictlyPerfect_single {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {R : Sheaf J RingCat.{0}} {M : Mod R} (hM : IsFinFreeSummand M) :
    IsStrictlyPerfect ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) 0).obj M) := by
  refine ⟨⟨0, 0, inferInstance, inferInstance⟩, fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    obtain ⟨m, i, p, hip⟩ := hM
    let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M
    exact ⟨m, e.hom ≫ i, p ≫ e.inv, by simp [reassoc_of% hip]⟩
  · exact ⟨0, 0, 0, (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn).eq_of_src _ _⟩

/-- Z3.j: a strictly perfect complex on an over-site is perfect (the identity roof). -/
theorem IsStrictlyPerfect.isPerfectOver {R : RingSheaf X} {V : Opens X}
    {P : CochainComplex (Mod (R.over V)) ℤ} (hP : IsStrictlyPerfect P) : IsPerfectOver P := by
  obtain ⟨⟨a, b, ha, hb⟩, -⟩ := id hP
  exact (isPerfectOverIn_of_roof (𝟙 P) (𝟙 P) hP (a := a) (b := b)).isPerfectOver

variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}} {ι : Type} (U : ι → Opens X)

/-- Z3.j non-vacuity: for the trivial cocycle, a summand `N` of a finite free `O`-module, as a
twisted sheaf in degree `0`, is a twisted perfect complex. -/
theorem twIsPerfect_single_ofSheaf {N : Mod (ringOf R)} (hN : IsFinFreeSummand N) :
    TwIsPerfect ((HomologicalComplex.single (TwMod R U (fun _ _ _ => 1)) (ComplexShape.up ℤ)
      0).obj (TwMod.ofSheaf R U N)) := by
  intro α
  refine IsPerfectOver.of_quasiIso_left
    ((HomologicalComplex.singleMapHomologicalComplex (TwMod.comp R U _ α) (ComplexShape.up ℤ)
      0).app (TwMod.ofSheaf R U N)).inv ?_
  exact IsStrictlyPerfect.isPerfectOver (isStrictlyPerfect_single (hN.restr (ringOf R) (U α)))

/-- Z3.j non-vacuity: `O` in degree `0` lies in `D_perf(X, ȟ)` for the trivial cocycle. -/
example [HasDerivedCategory.{0} (TwMod R U (fun _ _ _ => 1))] :
    TwPerf R U (fun _ _ _ => 1) (DerivedCategory.Q.obj
      ((HomologicalComplex.single (TwMod R U (fun _ _ _ => 1)) (ComplexShape.up ℤ) 0).obj
        (TwMod.ofSheaf R U (SheafOfModules.free (Fin 1))))) :=
  ⟨_, twIsPerfect_single_ofSheaf U ⟨1, 𝟙 _, 𝟙 _, by simp⟩, ⟨Iso.refl _⟩⟩

/-- Z3.j: on compact `X`, the homology of a twisted perfect complex is bounded. -/
example (T : TwistCocycle R) {K : CochainComplex (TwMod R T.U T.ch) ℤ}
    (hK : TwIsPerfect K) : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → K.ExactAt i :=
  TwIsPerfect.exists_exactAt T hK

end TwPerf

end Cohesive.Checks
