import Cohesivemodules.Comparison.Perfect
import Cohesivemodules.Comparison.EssSurjAux
import Cohesivemodules.Comparison.EssSurjCore
import Cohesivemodules.Sheaf.FlatResolution
import Cohesivemodules.Sheaf.BaseChange
import Cohesivemodules.Sheaf.Globalize

set_option linter.style.header false

/-!
# C5: essential surjectivity onto `D_perf`

Blueprint item C5 (§4, v1.9 C5.a–c, v1.10 sign), [A, Prop 7.2.18] ⚠ K-flat variant (no
Malgrange flatness, §0 decision 5). For resolving data `D` on a compact Hausdorff space, every
object of `D_perf(X, O)` is isomorphic to `J(M)` for a cohesive module `M` over `𝒜(X)`.

Steps (blueprint C5), each a lemma below:
1. `exists_flat_model` (C5.0, step 1): a perfect `K` receives a quasi-isomorphism from a bounded
   above complex `K'` of flat sheaves (S9.d global bound, `truncLE` (audit G12), S8.d).
2. `isPerfect_sheafBC` (step 2): `𝒜⁰ ⊗_O K'` is perfect over `𝒜⁰` (S8.f, S8.g; v1.9 F4: truncate
   the roof's middle term before resolving). `ρSheaf : O ⟶ 𝒜⁰` is `ρ` as a map of sheaves of rings.
3. S10 (`exists_strictlyPerfect_quasiIso`, used directly): a strictly perfect `Pt → 𝒜⁰ ⊗ K'`.
4.–5. `exists_sheafOfMap_quasiIso` (C5.a–c, steps 4–5): from `Pt → 𝒜⁰ ⊗_O K'` a cohesive `M` and a
   quasi-isomorphism `α(M) → 𝒜^• ⊗_O K'` (`tensorC O 𝒜^• K'`, `𝒜^•` first: v1.10). Γ, A11, the
   quasi-cohesive structure on `Γ(𝒜^• ⊗_O K')` (C5.a), the sheaf map (C5.b), A7/A12 (C5.c).
6. `quasiIso_tensorCMap_ρhat` (step 6): `O[0] ⊗ K' → 𝒜^• ⊗ K'` is a quasi-isomorphism (`ρ` a
   resolution, `K'` K-flat); `tensorC_single_unit_iso`: `O[0] ⊗ K' ≅ K'`.
7. `exists_J_obj_iso`: assemble in `D(O)`.
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace ResolvingData

variable (D : ResolvingData X)

/-- **C5 step 1 (C5.0).** A perfect complex receives a quasi-isomorphism from a bounded above
complex of flat sheaves of `O`-modules (S9.d, `truncLE`, S8.d). -/
theorem exists_flat_model [CompactSpace X] [T2Space X] {K : CochainComplex (Mod D.R) ℤ}
    (hK : IsPerfect K) :
    ∃ (K' : CochainComplex (Mod D.R) ℤ) (f : K' ⟶ K) (b : ℤ),
      QuasiIso f ∧ K'.IsStrictlyLE b ∧ ∀ n, IsFlat D.O (K'.X n) := by
  obtain ⟨a, b, hab⟩ := hK.exists_isPerfectIn
  have hLE : K.IsLE b := by
    rw [CochainComplex.isLE_iff]
    exact fun i hi => hab.exactAt i (Or.inr hi)
  have : (K.truncLE b).IsStrictlyLE b := inferInstance
  obtain ⟨F, f, hF, hflat, hq⟩ := exists_quasiIso_flat D.O (K.truncLE b) b
  exact ⟨F, f ≫ K.ιTruncLE b, b, inferInstance, hF, hflat⟩

/-- **C5 step 2.** For a perfect, bounded above, termwise flat `K'`, the base change
`𝒜⁰ ⊗_O K'` is a perfect complex of `𝒜⁰`-modules (S8.f, S8.g). -/
theorem isPerfect_sheafBC [CompactSpace X] [T2Space X] {K' : CochainComplex (Mod D.R) ℤ}
    (hK' : IsPerfect K') (b : ℤ) [K'.IsStrictlyLE b] (hflat : ∀ n, IsFlat D.O (K'.X n)) :
    IsPerfect (((sheafBC D.ρSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K') := by
  intro x
  obtain ⟨U, hU, L, P, f, g, hf, hg, hP⟩ := hK' x
  obtain ⟨L', P', f', g', h1, h2, h3⟩ :=
    @exists_roof_sheafBC _ _ _ _ D.ρSheaf U K' b _ hflat L P f g hf hg hP
  exact ⟨U, hU, L', P', f', g', h1, h2, h3⟩

/-- **C5 steps 4–5 (C5.a–c).** From a strictly perfect complex `Pt` of `𝒜⁰`-modules and a
quasi-isomorphism `f⁰ : Pt → 𝒜⁰ ⊗_O K'`: a cohesive module `M` over `𝒜(X)` (A11 on `P = Γ(Pt)`
and the quasi-cohesive structure on `Γ(𝒜^• ⊗_O K')`, C5.a) and a quasi-isomorphism
`α(M) → 𝒜^• ⊗_O K'` (C5.b, C5.c). (v1.11) Proof via the explicit model C7 on the over-site of
`⊤` (`EssSurjModel.lean`): `α(M)|⊤ ≅ α_⊤(M) →Ξ T(K'|⊤) ≅ 𝒜^•|⊤ ⊗ K'|⊤ ≅ (𝒜^• ⊗ K')|⊤`, a
quasi-isomorphism (C7.f, C7.d), brought back to `X` by restriction to `⊤`. -/
theorem exists_sheafOfMap_quasiIso [CompactSpace X] [T2Space X] {K' : CochainComplex (Mod D.R) ℤ}
    (b : ℤ) [K'.IsStrictlyLE b] (hflat : ∀ n, IsFlat D.O (K'.X n))
    {Pt : CochainComplex (Mod (ringOf D.A0)) ℤ} (hPt : IsStrictlyPerfect Pt)
    (f₀ : Pt ⟶ ((sheafBC D.ρSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K')
    [QuasiIso f₀] :
    ∃ (M : CohesiveModule D.𝒜X) (e : D.sheafOf M ⟶ tensorC D.O D.dgaComplex K'), QuasiIso e := by
  obtain ⟨θ, hθ⟩ := D.exists_conn ⊤ (((restr D.R ⊤).mapHomologicalComplex _).obj K')
  obtain ⟨M, e, hgr⟩ := D.exists_cohesive_gr0_quasiIso b hflat hPt f₀ θ hθ
  have hΞ : QuasiIso (PreResolvingData.Ξ e) := PreResolvingData.quasiIso_Ξ e hgr
  obtain ⟨eT, -, -⟩ := D.exists_TC_iso_tensorC ⊤ (((restr D.R ⊤).mapHomologicalComplex _).obj K')
    θ hθ
  obtain ⟨iα⟩ := D.exists_restrTop_sheafOf_iso M
  obtain ⟨iT⟩ := exists_restr_tensorC_iso D.O ⊤ D.dgaComplex K'
  obtain ⟨f, hf⟩ := exists_preimage_restrTop (iα.hom ≫ PreResolvingData.Ξ e ≫ (eT ≪≫ iT.symm).hom)
  refine ⟨M, f, quasiIso_of_restrTop f ?_⟩
  rw [hf]
  infer_instance

/-- **C5 step 6.** `ρ̂ ⊗ K' : O[0] ⊗ K' → 𝒜^• ⊗ K'` is a quasi-isomorphism for bounded above,
termwise flat `K'` (`quasiIso_ρhat`, `K'` K-flat, S8.e). -/
theorem quasiIso_tensorCMap_ρhat {K' : CochainComplex (Mod D.R) ℤ} (b : ℤ)
    [K'.IsStrictlyLE b] (hflat : ∀ n, IsFlat D.O (K'.X n)) :
    QuasiIso (tensorCMap₁ D.O D.ρhat K') := by
  have hK : IsKFlat D.O K' := isKFlat_of_isFlat D.O K' b hflat
  have hc : (CochainComplex.mappingCone D.ρhat).Acyclic :=
    (quasiIso_iff_acyclic_mappingCone D.ρhat).1 D.quasiIso_ρhat
  have h1 : (tensorC D.O K' (CochainComplex.mappingCone D.ρhat)).Acyclic := hK _ hc
  refine (quasiIso_iff_acyclic_mappingCone (tensorCMap₁ D.O D.ρhat K')).2 ?_
  exact fun i => (h1 i).of_iso
    ((tensorCSymIso D.O _ _).symm ≪≫ tensorCConeIso₁ D.O D.ρhat K')

/-- **C5 step 6.** `O[0] ⊗ K' ≅ K'`. -/
theorem tensorC_single_unit_iso (K' : CochainComplex (Mod D.R) ℤ) :
    Nonempty (tensorC D.O ((HomologicalComplex.single (Mod D.R) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit D.R)) K' ≅ K') :=
  ⟨tensorCSingleIso D.O _ K' ≪≫
    (NatIso.mapHomologicalComplex (unitTensorIso D.O) (ComplexShape.up ℤ)).app K'⟩

/-- **C5.** Every object of `D_perf(X, O)` is isomorphic to some `J(M)`. [A, Prop 7.2.18]. -/
theorem exists_J_obj_iso [CompactSpace X] [T2Space X] [HasDerivedCategory.{w} (Mod D.R)]
    (K : DerivedCategory (Mod D.R)) (hK : Perf D.R K) :
    ∃ M : HoP D.𝒜X, Nonempty (D.J.obj M ≅ K) := by
  obtain ⟨K₀, hK₀, ⟨e⟩⟩ := hK
  obtain ⟨K', f, b, hf, hb, hflat⟩ := D.exists_flat_model hK₀
  have hK' : IsPerfect K' := IsPerfect.of_quasiIso_right f hK₀
  have hB := D.isPerfect_sheafBC hK' b hflat
  obtain ⟨Pt, f₀, hPt, hq⟩ := exists_strictlyPerfect_quasiIso D.isFine0 (isComm_ringOf _) hB
  obtain ⟨M, e', hqe⟩ := D.exists_sheafOfMap_quasiIso b hflat hPt f₀
  have h6 := D.quasiIso_tensorCMap_ρhat b hflat
  obtain ⟨u⟩ := D.tensorC_single_unit_iso K'
  have i1 : IsIso (DerivedCategory.Q.map e') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Mod D.R) e').2 hqe
  have i2 : IsIso (DerivedCategory.Q.map (tensorCMap₁ D.O D.ρhat K')) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Mod D.R) _).2 h6
  have i3 : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Mod D.R) f).2 hf
  exact ⟨⟨M⟩, ⟨@asIso _ _ _ _ (DerivedCategory.Q.map e') i1 ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (tensorCMap₁ D.O D.ρhat K')) i2).symm ≪≫
    DerivedCategory.Q.mapIso u ≪≫ @asIso _ _ _ _ (DerivedCategory.Q.map f) i3 ≪≫
    e.symm⟩⟩

end ResolvingData

end Cohesive
