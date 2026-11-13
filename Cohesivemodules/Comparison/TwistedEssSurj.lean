import Cohesivemodules.Comparison.TwistedLift
import Cohesivemodules.Comparison.ModelTensor
import Cohesivemodules.Sheaf.Globalize
import Cohesivemodules.Comparison.ModelConn

set_option linter.style.header false

/-!
# Z3.u: essential surjectivity of `J_T` onto twisted perfect complexes (blueprint-tw G′ (l))

Blueprint item Z3.u (`blueprint/blueprint-tw.md` §3 G′ (l); G.10), [A, Prop 7.2.18, §7.4].
For resolving data `D` on a compact space, a closed `h ∈ 𝒜²(X)` and a twist datum `T` for `h`,
every twisted perfect object `K` of `D(TwMod O U ȟ)` is isomorphic to `J_T(M)` for a cohesive
module `M` over the curved algebra `(𝒜(X), h)`. Steps:
1. flat model `f : K' → K` (`TwIsPerfect.exists_flat_model`, G′ (a));
2. `F = untwist(K')` is perfect (`isPerfect_untwF`, G′ (c)); S10 gives `f⁰ : Pt → F` (G′ (d));
3. connections `θ_α` on `F_{K'_α}` (`exists_conn`, C7.b); `M`, `e` (`exists_twisted_lift`, G′ (i));
4. `Ξ^tw : J_T(M) → T^tw(K')` (`quasiIso_twXi`, G′ (k)) and `ιT^tw : K' → T^tw(K')`
   (`quasiIso_ιTtw`, G′ (f); `ρ̂` a resolution, components K-flat) are quasi-isomorphisms;
5. `J_T(M) ≅ T^tw(K') ≅ K' ≅ K` in the derived category.

## Deviations
* As C5: the K-flat variant (no Malgrange flatness, §0 decision 5). Only `X` compact is assumed
  (C5 also assumes Hausdorff; not needed here).
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X] [CompactSpace X] (D : ResolvingData X) {h : D.D.A ⊤}
  (T : TwistDatum D.toSheafData h) (hh : h ∈ D.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := D.D.𝒜 ⊤) h = 0)

/-- **Z3.u (C5^tw).** [A, Prop 7.2.18, §7.4], blueprint-tw G.10, G′ (l). Every twisted perfect
object `K` of the derived category of `ȟ`-twisted `O`-modules is isomorphic to `J_T(M)` for some
`M` in `Ho(P_{(𝒜(X), h)})`. -/
theorem exists_twistedJ_obj_iso [HasDerivedCategory.{w} (TwMod D.toSheafData.O T.U T.ch)]
    (K : DerivedCategory (TwMod D.toSheafData.O T.U T.ch))
    (hK : TwPerf D.toSheafData.O T.U T.ch K) :
    ∃ M : HoP (D.toSheafData.withCurvature h hh hd).𝒜X,
      Nonempty ((T.twistedJ hh hd).obj M ≅ K) := by
  obtain ⟨K₀, hK₀, ⟨i⟩⟩ := hK
  obtain ⟨K', f, b, hf, hb, hflat⟩ := TwIsPerfect.exists_flat_model T.toTwistCocycle hK₀
  have hK' : TwIsPerfect K' := TwIsPerfect.of_quasiIso_right f hK₀
  have hF := isPerfect_untwF D.toPreResolvingData T K' hK' b hflat
  obtain ⟨Pt, f₀, hPt, hq⟩ :=
    exists_strictlyPerfect_quasiIso D.isFine0 (isComm_ringOf _) hF
  choose θ hθ using fun α =>
    D.exists_conn (T.U α) (twKα D.toPreResolvingData T K' α)
  obtain ⟨M, e, he, hgr⟩ :=
    exists_twisted_lift D.toPreResolvingData T hh hd K' θ hθ hPt f₀
  have h1 := quasiIso_twXi D.toPreResolvingData T hh hd K' θ hθ M e he hgr
  have h2 := quasiIso_ιTtw D.toPreResolvingData T K' θ hθ D.quasiIso_ρhat
    (isKFlat_twComp T.toTwistCocycle b hflat)
  have i1 : IsIso (DerivedCategory.Q.map (twXi D.toPreResolvingData T hh hd K' θ hθ M e he)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h1
  have i2 : IsIso (DerivedCategory.Q.map (ιTtw D.toPreResolvingData T K' θ hθ)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 h2
  have i3 : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  exact ⟨⟨M⟩, ⟨@asIso _ _ _ _ (DerivedCategory.Q.map (twXi _ T hh hd K' θ hθ M e he)) i1 ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (ιTtw _ T K' θ hθ)) i2).symm ≪≫
    @asIso _ _ _ _ (DerivedCategory.Q.map f) i3 ≪≫ i.symm⟩⟩

end Cohesive
