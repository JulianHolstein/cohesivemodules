import Cohesivemodules.Comparison.TwistedPerfect
import Cohesivemodules.Comparison.TwistedFullyFaithful

set_option linter.style.header false

/-!
# Z3.p for abstract resolving data

Blueprint item Z3.p (`blueprint/blueprint-tw.md` §3 E.1–E.2; [A, Lemma 7.2.17, §7.4]), stated for
resolving data `D` with the local gauge lemma over opens as a hypothesis (`LLOpen D`), as
`full_twistedJ` and `faithful_twistedJ` are. `Comparison/TwistedPerfect.lean` proves the same for
the Dolbeault data, where `LLOpen` is the theorem `localGaugeLemmaOpen`; the proofs are the same.
* `isPerfectOver_sheafOfOver_of_llOpen`: `α_U(N)` is perfect on `Over U` for every open `U` and
  cohesive `N` over `𝒜(U)`;
* `twIsPerfect_twistedSheafOf_of_llOpen`: `J_T(M)` is twisted perfect;
* `twPerf_twistedJ_obj_of_llOpen`: `J_T(M) ∈ D_perf(X, ȟ)`.
Together with `full_twistedJ` and `faithful_twistedJ` this makes every ingredient of the twisted
theorem available for abstract resolving data.

## Deviations
* As for C2: `X` compact Hausdorff (the explicit model C7 behind C2's local model).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace CategoryTheory Opposite

variable {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X] (D : ResolvingData X)

/-- **Z3.p** (abstract form). [A, Lemma 7.2.17] over an open, blueprint-tw E.2. For resolving data
`D` with LL over opens (`LLOpen D`), an open `U` and a cohesive module `N` over `𝒜(U)`, `α_U(N)`
(C1.c) is a perfect complex on `Over U`. -/
theorem isPerfectOver_sheafOfOver_of_llOpen (hLL : LLOpen D) (U : Opens X)
    (N : CohesiveModule (D.D.𝒜 U)) : IsPerfectOver (D.sheafOfOver U N) := by
  intro x hx
  obtain ⟨U', hU', hxU', W, hW, ⟨e⟩⟩ := hLL U N x hx
  obtain ⟨L, u, hu, hL⟩ := D.exists_quasiIso_sheafOfOver_fromComplex U' W hW
  obtain ⟨f, hf⟩ := exists_quasiIso_to_restrOver D.toPreResolvingData hU' N _ e u hu
  exact ⟨U', hU', hxU', L, L, f, 𝟙 L, hf, inferInstance, hL⟩

variable {h : D.D.A ⊤} (T : TwistDatum D.toSheafData h) (hh : h ∈ D.D.𝒜 ⊤ 2)
  (hd : GCDga.d (𝒜 := D.D.𝒜 ⊤) h = 0)

/-- **Z3.p** (abstract form). [A, §7.4], blueprint-tw E. For resolving data `D` with LL over opens,
a closed `h ∈ 𝒜²(X)`, a twist datum `T` and a cohesive module `M` over `(𝒜(X), h)`, the complex of
twisted sheaves `J_T(M)` is twisted perfect: its component on `U_α` is
`α_{U_α}(gauge_{h⁰_α}(M|U_α))` up to isomorphism (Z3.o). -/
theorem twIsPerfect_twistedSheafOf_of_llOpen (hLL : LLOpen D)
    (M : CohesiveModule (D.toSheafData.withCurvature h hh hd).𝒜X) :
    TwIsPerfect (T.twistedSheafOf hh hd M) := by
  intro α
  exact isPerfectOver_of_iso (twLocalIso D.toPreResolvingData T hh hd α M).symm
    (isPerfectOver_sheafOfOver_of_llOpen D hLL (T.U α)
      (gaugedRes D.toPreResolvingData T hh hd α M))

/-- **Z3.p** (abstract form). [A, Lemma 7.2.17], blueprint-tw E. `J_T(M) ∈ D_perf(X, ȟ)`. -/
theorem twPerf_twistedJ_obj_of_llOpen (hLL : LLOpen D)
    [HasDerivedCategory.{0} (TwMod D.toSheafData.O T.U T.ch)]
    (M : HoP (D.toSheafData.withCurvature h hh hd).𝒜X) :
    TwPerf D.toSheafData.O T.U T.ch ((T.twistedJ hh hd).obj M) :=
  (twPerf_Q_obj_iff _).2 (twIsPerfect_twistedSheafOf_of_llOpen D T hh hd hLL M.as)

end Cohesive
