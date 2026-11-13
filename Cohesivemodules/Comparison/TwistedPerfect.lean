import Cohesivemodules.Comparison.TwistedLocal
import Cohesivemodules.Comparison.AlphaOverRestr
import Cohesivemodules.Comparison.Perfect
import Cohesivemodules.Sheaf.Twisted.Perfect
import Cohesivemodules.Main
import Cohesivemodules.Forms.DolbeaultGrothendieck
import Cohesivemodules.Forms.LocalGauge
import Cohesivemodules.Forms.LocalGaugeOpen

set_option linter.style.header false

/-!
# Z3.p: `J_T(M)` is a twisted perfect complex (C2^tw)

Blueprint item Z3.p (`blueprint/blueprint-tw.md` §3 E.1–E.2; [A, Lemma 7.2.17, §7.4]). For the
Dolbeault data on a compact Hausdorff complex manifold:
* `isPerfectOver_sheafOfOver`: for every open `U` and cohesive `N` over `𝒜_X(U)`, the complex
  `α_U(N)` on `Over U` is perfect: near `x ∈ U`, H2 over opens (`localGaugeLemmaOpen`, Z3.e) gives
  `N|U′ ≅ 𝒜_X(U′) ⊗ W`, C2's local model gives a strictly perfect `L → α_{U′}(𝒜 ⊗ W)`, and
  `α_U(N)|U′ ≅ α_{U′}(N|U′)` (`restrOverSheafOfIso`);
* `twIsPerfect_twistedSheafOf`: each component `J_T(M)_α ≅ α_{U_α}(gauge_{h⁰_α}(M|U_α))` (Z3.o,
  `twLocalIso`, `gaugedRes`) is perfect by the previous item, so `J_T(M)` is twisted perfect;
* `twPerf_twistedJ_obj`: `J_T(M) ∈ D_perf(X, ȟ)`.

## Deviations
* As for C2: `X` compact Hausdorff (the source's setting; used by the explicit model C7 behind
  C2's local model). H1 and H2 are the theorems of phases 6–7 (`dolbeaultGrothendieck`,
  `localGaugeLemma`), not hypotheses.
-/

noncomputable section

universe w

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  [T2Space X] [CompactSpace X]

omit [T2Space X] [CompactSpace X] in
/-- Z3.p, generic roof step: a quasi-isomorphism `L → α_{U'}(M₀)` and `N|U' ≅ M₀` in `Ho(P)`
give a quasi-isomorphism `L → α_U(N)|U'`. -/
theorem exists_quasiIso_to_restrOver (P : PreResolvingData X) {U U' : Opens X}
    (hU' : U' ≤ U) (N : CohesiveModule (P.D.𝒜 U)) (M₀ : CohesiveModule (P.D.𝒜 U'))
    (e : HoP.mk (N.baseChange (P.D.res hU')) ≅ HoP.mk M₀)
    {L : CochainComplex (Mod (P.R.over U')) ℤ} (u : L ⟶ P.sheafOfOver U' M₀) (hu : QuasiIso u) :
    ∃ f : L ⟶ ((restrOver P.R hU').mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (P.sheafOfOver U N), QuasiIso f := by
  obtain ⟨φ, hφ⟩ := P.exists_quasiIso_sheafOfOverMap_of_iso U' e.symm
  have := hu
  refine ⟨(u ≫ P.sheafOfOverMap U' φ) ≫ (P.restrOverSheafOfIso hU' N).inv, ?_⟩
  infer_instance

omit [T2Space X] [CompactSpace X] in
/-- Z3.p: perfectness on `Over V` transfers along an isomorphism of complexes (generic ring
sheaf). -/
theorem isPerfectOver_of_iso {R : RingSheaf X} {V : Opens X}
    {K K' : CochainComplex (Mod (R.over V)) ℤ} (e : K ≅ K') (hK : IsPerfectOver K) :
    IsPerfectOver K' :=
  IsPerfectOver.of_quasiIso_left e.hom hK

variable (E) in
/-- **Z3.p.** [A, Lemma 7.2.17] over an open, blueprint-tw E.2. For an open `U` and a cohesive
module `N` over `𝒜_X(U)`, `α_U(N)` (C1.c) is a perfect complex on `Over U`. -/
theorem isPerfectOver_sheafOfOver (U : Opens X) (N : CohesiveModule (dolbeaultGrade E U)) :
    IsPerfectOver ((dolbeaultPreData E X).sheafOfOver U N) := by
  intro x hx
  obtain ⟨U', hU', hxU', W, hW, ⟨e⟩⟩ := localGaugeLemmaOpen E N hx
  have key : ∃ (L : CochainComplex (Mod ((dolbeaultPreData E X).R.over U')) ℤ)
      (u : L ⟶ (dolbeaultPreData E X).sheafOfOver U'
        (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E U') W (dbar_dolbeaultRhoU E U') rfl hW)),
      QuasiIso u ∧ IsStrictlyPerfect L :=
    (dolbeaultData E X (dolbeaultGrothendieck E X)
      (localGaugeLemma E X)).exists_quasiIso_sheafOfOver_fromComplex U' W hW
  obtain ⟨L, u, hu, hL⟩ := key
  obtain ⟨f, hf⟩ := exists_quasiIso_to_restrOver (dolbeaultPreData E X) hU' N _ e u hu
  exact ⟨U', hU', hxU', L, L, f, 𝟙 L, hf, inferInstance, hL⟩

/-- **Z3.p.** [A, §7.4], blueprint-tw E. For a closed `h`, a twist datum `T` and a cohesive
module `M` over `(𝒜_X(X), ∂̄, h)`, the complex of twisted sheaves `J_T(M)` is twisted perfect:
its component on `U_α` is `α_{U_α}(gauge_{h⁰_α}(M|U_α))` up to isomorphism (Z3.o). -/
theorem twIsPerfect_twistedSheafOf (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    (M : CohesiveModule (curvedDolbeault h)) :
    TwIsPerfect (T.twistedSheafOf h.2.1 h.2.2 M) := by
  intro α
  exact isPerfectOver_of_iso
    (twLocalIso (dolbeaultPreData E X) T h.2.1 h.2.2 α M).symm
    (isPerfectOver_sheafOfOver E (T.U α) (gaugedRes (dolbeaultPreData E X) T h.2.1 h.2.2 α M))

/-- **Z3.p.** [A, Lemma 7.2.17], blueprint-tw E. `J_T(M) ∈ D_perf(X, ȟ)`. -/
theorem twPerf_twistedJ_obj (h : DolbeaultClosed2 E X) (T : TwistData E X h)
    [HasDerivedCategory.{0} (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)]
    (M : HoP (curvedDolbeault h)) :
    TwPerf (dolbeaultPreData E X).toSheafData.O T.U T.ch ((T.twistedJ h.2.1 h.2.2).obj M) := by
  exact (twPerf_Q_obj_iff _).2 (twIsPerfect_twistedSheafOf h T M.as)

end Cohesive
