import Cohesivemodules.Sheaf.Perfect
import Cohesivemodules.Sheaf.Projective
import Mathlib.Algebra.Category.Ring.Limits

set_option linter.style.header false

/-!
# Checks for layer S (blueprint §9, non-vacuity)

Layer-S part of the checks, in a separate file to keep `Checks.lean` small (blueprint §9 puts
all checks in `Checks.lean`; this is a split, size only). Trap: anything mentioning
`sheafCompose _ (forget₂ CommRingCat RingCat)` needs `Mathlib.Algebra.Category.Ring.Limits`
imported, or instance search for `HasSheafCompose` does not terminate.
-/

namespace Cohesive.Checks

/-! ## Layer S: non-vacuity (blueprint §9)

* S1 `IsFine`: every sheaf of rings on a one-point space is fine; `IsComm` holds for the
  underlying ring sheaf of a sheaf of commutative rings.
* S9: `R` in degree 0 is strictly perfect and perfect, and its image lies in `D_perf`. -/

section LayerS

open CategoryTheory Opposite TopologicalSpace

/-- Every sheaf of rings on a one-point space is fine: in a finite cover some member is `⊤`;
take `ρ = 1` there and `0` elsewhere (`1` is supported in `⊤` with witness `⊥`, since `R(∅)` is
the zero ring). -/
theorem isFine_punit (R : RingSheaf PUnit.{1}) : IsFine R := by
  classical
  intro ι _ U hU
  have hsub : Subsingleton (R.obj.obj (op ⊥)) := by
    have hT : Limits.IsTerminal (R.obj.obj (op ⊥)) :=
      Sheaf.isTerminalOfBotCover R ⊥ (by
        rw [Opens.mem_grothendieckTopology]
        intro x hx; exact absurd hx (by simp))
    refine ⟨fun a b => ?_⟩
    let f : RingCat.of (R.obj.obj (op ⊥) × R.obj.obj (op ⊥)) ⟶ R.obj.obj (op ⊥) :=
      RingCat.ofHom (RingHom.fst _ _)
    let g : RingCat.of (R.obj.obj (op ⊥) × R.obj.obj (op ⊥)) ⟶ R.obj.obj (op ⊥) :=
      RingCat.ofHom (RingHom.snd _ _)
    exact congrArg (fun h => h.hom (a, b)) (hT.hom_ext f g)
  have hx : (PUnit.unit : PUnit.{1}) ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 hx
  have htop : U i₀ = ⊤ := by
    ext y; simp only [Opens.coe_top, Set.mem_univ, iff_true]
    have : y = PUnit.unit := Subsingleton.elim _ _
    subst this; exact hi₀
  refine ⟨fun i => if i = i₀ then 1 else 0, ?_, ?_⟩
  · simp
  · intro i
    by_cases h : i = i₀
    · subst h
      refine ⟨⊥, by rw [htop]; simp, Subsingleton.elim _ _⟩
    · refine ⟨⊤, by simp, ?_⟩
      simp only [h, ite_false]
      exact map_zero _

/-- `IsComm` holds for the ring sheaf underlying a sheaf of commutative rings. -/
theorem isComm_forget₂ {X : Type} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}) :
    IsComm ((sheafCompose _ (forget₂ CommRingCat RingCat)).obj R) := by
  intro U a b
  exact mul_comm (show R.obj.obj (op U) from a) b

variable {X : Type} [TopologicalSpace X] (R : RingSheaf X)

/-- A finite free module is a direct summand of a finite free module. -/
theorem isFinFreeSummand_free (m : ℕ) :
    IsFinFreeSummand (SheafOfModules.free (R := R) (Fin m)) :=
  ⟨m, 𝟙 _, 𝟙 _, by simp⟩

/-- Finite-free-summand transfers along an isomorphism. -/
private lemma isFinFreeSummand_of_iso {M N : Mod R} (e : M ≅ N) (h : IsFinFreeSummand N) :
    IsFinFreeSummand M := by
  obtain ⟨m, i, p, hip⟩ := h
  exact ⟨m, e.hom ≫ i, p ≫ e.inv, by simp [reassoc_of% hip]⟩

/-- A zero module is a finite-free summand (of the free module on `Fin 0`). -/
private lemma isFinFreeSummand_of_isZero {M : Mod R} (h : Limits.IsZero M) : IsFinFreeSummand M :=
  ⟨0, 0, 0, h.eq_of_src _ _⟩

/-- `R` in degree `0` is a strictly perfect complex. -/
theorem isStrictlyPerfect_single_unit :
    IsStrictlyPerfect ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.free (R := R) (Fin 1))) := by
  refine ⟨⟨0, 0, inferInstance, inferInstance⟩, fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact isFinFreeSummand_of_iso R (HomologicalComplex.singleObjXSelf _ _ _)
      (isFinFreeSummand_free R 1)
  · exact isFinFreeSummand_of_isZero R (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- A strictly perfect complex is perfect: on every open `U`, the identity roof on `P|U`, which
is strictly perfect (`IsFinFreeSummand.restr`). -/
theorem IsStrictlyPerfect.isPerfect {P : CochainComplex (Mod R) ℤ} (hP : IsStrictlyPerfect P) :
    IsPerfect P := by
  intro x
  obtain ⟨⟨a, b, hGE, hLE⟩, hX⟩ := hP
  refine ⟨⊤, trivial, ((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    ((restr R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj P, 𝟙 _, 𝟙 _,
    inferInstance, inferInstance, ⟨⟨a, b, ?_, ?_⟩, fun n => (hX n).restr R ⊤⟩⟩
  · exact (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
      (restr R ⊤).map_isZero (CochainComplex.isZero_of_isStrictlyGE P a i hi)
  · exact (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
      (restr R ⊤).map_isZero (CochainComplex.isZero_of_isStrictlyLE P b i hi)

/-- `R` in degree `0` lies in `D_perf(X, R)`. -/
theorem perf_single_unit [HasDerivedCategory.{0} (Mod R)] :
    Perf R (DerivedCategory.Q.obj ((HomologicalComplex.single (Mod R) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.free (R := R) (Fin 1)))) :=
  ⟨_, IsStrictlyPerfect.isPerfect R (isStrictlyPerfect_single_unit R), ⟨Iso.refl _⟩⟩

end LayerS

end Cohesive.Checks
