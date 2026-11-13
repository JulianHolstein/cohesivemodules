import Cohesivemodules.Comparison.AlphaOver
import Cohesivemodules.Comparison.Setup
import Cohesivemodules.Comparison.PerfectAux
import Cohesivemodules.Comparison.PerfectModel
import Cohesivemodules.Sheaf.Perfect

set_option linter.style.header false

/-!
# C2: J lands in perfect complexes

Blueprint item C2 (§4), [A, Lemma 7.2.17]. For resolving data `D` (C0.b) and a cohesive module
`M` over `𝒜(X)`, `α(M)` is perfect (S9.b), so `J(M) ∈ D_perf(X, O)`.

Proof (blueprint C2, v1.9 roof): at `x`, LL gives `U′ ∋ x`, a bounded complex `W` of finitely
generated projective `O(U′)`-modules and `M|U′ ≅ 𝒜(U′) ⊗ W` in `Ho(P_{𝒜(U′)})`. The sheafified
`W̃` (sections `O(V) ⊗_{O(U′)} W`) is strictly perfect on the over-site of `U′` and maps
quasi-isomorphically to `α_{U′}(𝒜(U′) ⊗ W) ≅ 𝒜|U′ ⊗ W̃` (ρ a resolution; audit G1, G2:
`exists_quasiIso_sheafOfOver_fromComplex`); compose with `α_{U′}` of the LL homotopy equivalence and
with C1.c (`restrSheafOfIso`). Roof `α(M)|U′ ← W̃ → W̃` with `g = 𝟙`.

* `perf_Q_obj_iff'`: S9.c's `perf_Q_obj_iff` for a `HasDerivedCategory` instance in any universe
  (the main statement uses `HasDerivedCategory.standard`, universe `max u v = 1` for `Mod R`,
  while `perf_Q_obj_iff` is stated for universe `0`).
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- **S9.c, any universe.** `Q K ∈ D_perf(X, R)` iff `K` is perfect, for a `HasDerivedCategory`
instance in any universe `w` (`perf_Q_obj_iff` is the case `w = 0`). -/
theorem perf_Q_obj_iff' {R : RingSheaf X} [HasDerivedCategory.{w} (Mod R)]
    (K : CochainComplex (Mod R) ℤ) : Perf R (DerivedCategory.Q.obj K) ↔ IsPerfect K := by
  constructor
  · rintro ⟨K', hK', ⟨e⟩⟩
    obtain ⟨M, s, hs, g, hg⟩ := DerivedCategory.right_fac e.hom
    have h4 : IsIso (DerivedCategory.Q.map g) := by
      have : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ e.hom := by
        rw [hg, IsIso.hom_inv_id_assoc]
      rw [this]; infer_instance
    have h5 : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs
    have h6 : QuasiIso g := (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 h4
    exact IsPerfect.of_quasiIso_left s (IsPerfect.of_quasiIso_right g hK')
  · intro hK
    exact ⟨K, hK, ⟨Iso.refl _⟩⟩

namespace ResolvingData

variable (D : ResolvingData X)

/-- **C2, local model (audit G1, G2).** For a bounded complex `W` of finitely generated projective
`O(U)`-modules, there are a strictly perfect complex `L` of `O|U`-modules (`W̃`, sections
`O(V) ⊗_{O(U)} W`) and a quasi-isomorphism `L → α_U(𝒜(U) ⊗_{O(U)} W)` (A10). Uses that `ρ` is a
resolution (`quasiIso_ρhat`) and that each `W̃^p` is a summand of a finite free module.
Deviation (v1.11): `X` compact Hausdorff, used by the explicit model C7. -/
theorem exists_quasiIso_sheafOfOver_fromComplex [CompactSpace X] [T2Space X] (U : Opens X)
    (W : CochainComplex (ModuleCat.{0} (D.O.obj.obj (op U))) ℤ)
    (hW : IsBoundedFGProj (D.O.obj.obj (op U)) W) :
    ∃ (L : CochainComplex (Mod (D.R.over U)) ℤ)
      (u : L ⟶ D.sheafOfOver U (CohesiveModule.fromComplex (ρ := D.ρ U) W (D.d_ρ U)
        (D.c_eq_zero U) hW)),
      QuasiIso u ∧ IsStrictlyPerfect L := by
  obtain ⟨a, b, hab⟩ := hW.bounded
  obtain ⟨L, hL, ⟨ε⟩⟩ := exists_lift_complex (R := D.R.over U) (Over.mkIdTerminal (X := U)) W
    hW.finite hW.projective a b hab
  obtain ⟨u, hu⟩ := exists_lift_hom (Over.mkIdTerminal (X := U)) hL.2
    (ε.hom ≫ D.unitMap U W hW)
  exact ⟨L, u, D.quasiIso_of_gamma_eq U W hW L hL ε u hu, hL⟩

/-- **C2.** `α(M)` is a perfect complex. [A, Lemma 7.2.17]. Deviation (v1.11): `X` compact
Hausdorff (the source's setting; used by the explicit model C7). -/
theorem isPerfect_sheafOf [CompactSpace X] [T2Space X] (M : CohesiveModule D.𝒜X) :
    IsPerfect (D.sheafOf M) := by
  intro x
  obtain ⟨U, hx, W, hW, ⟨e⟩⟩ := D.LL M x
  obtain ⟨L, u, hu, hL⟩ := D.exists_quasiIso_sheafOfOver_fromComplex U W hW
  obtain ⟨φ, hφ⟩ := D.toPreResolvingData.exists_quasiIso_sheafOfOverMap_of_iso U e.symm
  have h1 : QuasiIso (u ≫ D.sheafOfOverMap U φ) := inferInstance
  have h2 : QuasiIso (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M).inv) := by
    rw [← Category.assoc]
    infer_instance
  exact ⟨U, hx, L, L, u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M).inv, 𝟙 L, h2,
    inferInstance, hL⟩

/-- **C2.** `J(M) ∈ D_perf(X, O)`. Deviation (v1.11): `X` compact Hausdorff. -/
theorem perf_J_obj [CompactSpace X] [T2Space X] [HasDerivedCategory.{w} (Mod D.R)]
    (M : HoP D.𝒜X) :
    Perf D.R (D.J.obj M) := by
  rw [PreResolvingData.J_obj]
  exact (perf_Q_obj_iff' _).2 (D.isPerfect_sheafOf M.as)

end ResolvingData

end Cohesive
