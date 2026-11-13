import Cohesivemodules.Comparison.TwistedCurvedComp
import Cohesivemodules.Comparison.EssSurjAux
import Cohesivemodules.Sheaf.Twisted.FlatResolution
import Cohesivemodules.Sheaf.Twisted.Perfect
import Cohesivemodules.Sheaf.BaseChangeRestrOver
import Cohesivemodules.Sheaf.Flat.KFlat

set_option linter.style.header false

/-!
# Z3.u: flat model and perfectness of `F = untwist(K')` (blueprint-tw G′ (a), (b), (c))

Blueprint item Z3.u (`blueprint/blueprint-tw.md` §3 G′ (a), (c); G.1, G.3), first part.
* `TwIsPerfect.exists_flat_model` (G′ (a)): a twisted perfect complex `K` receives a
  quasi-isomorphism from a bounded above complex `K'` with componentwise flat terms (C.6 (g) bounds,
  `truncLE`, Z3.l);
* `isKFlat_twComp`: the components `K'_α` of such a `K'` are K-flat on `Over U_α` (S8.e);
* `untwFRestrIso` (G′ (b)): `F|U_α ≅ F_{K'_α}` as complexes (`untwistRestrIso` termwise);
* `exists_roof_sheafBC_restrOver`: S8.g's `exists_roof_sheafBC` on over-sites (C.7′ (a) in place of
  `sheafBCOverIso`);
* `isPerfect_untwF` (G′ (c)): `F` is perfect on `X`.

## Deviations
* None.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

section Generic

variable {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}

/-- **Z3.u (G′ (a)).** [A, Prop 7.2.18 step 1], blueprint-tw G.1. A twisted perfect complex `K`
(`X` compact) receives a quasi-isomorphism `f : K' → K` from a complex `K'` that is strictly
bounded above (`≤ b`) with componentwise flat terms (C.6 (g) gives `K` exact above some `b`;
then `truncLE b` and Z3.l `exists_quasiIso_twIsFlat`). -/
theorem TwIsPerfect.exists_flat_model [CompactSpace X] (T : TwistCocycle R)
    {K : CochainComplex (TwMod R T.U T.ch) ℤ} (hK : TwIsPerfect K) :
    ∃ (K' : CochainComplex (TwMod R T.U T.ch) ℤ) (f : K' ⟶ K) (b : ℤ),
      QuasiIso f ∧ K'.IsStrictlyLE b ∧ ∀ n, TwIsFlat (K'.X n) := by
  obtain ⟨a, b, hab⟩ := TwIsPerfect.exists_exactAt T hK
  have hLE : K.IsLE b := by
    rw [CochainComplex.isLE_iff]
    exact fun i hi => hab i (Or.inr hi)
  have : (K.truncLE b).IsStrictlyLE b := inferInstance
  obtain ⟨F, f, hF, hflat, hq⟩ := exists_quasiIso_twIsFlat T (K.truncLE b) b
  exact ⟨F, f ≫ K.ιTruncLE b, b, inferInstance, hF, hflat⟩

/-- **Z3.u (G′ (a)).** S8.e on the components: if `K'` is strictly bounded above with
componentwise flat terms, each component `K'_α` is K-flat on `Over U_α`. -/
theorem isKFlat_twComp (T : TwistCocycle R) {K' : CochainComplex (TwMod R T.U T.ch) ℤ} (b : ℤ)
    [K'.IsStrictlyLE b] (hflat : ∀ n, TwIsFlat (K'.X n)) (α : T.ι) :
    IsKFlat (R.over (T.U α))
      (((TwMod.comp R T.U T.ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K') := by
  have : CochainComplex.IsStrictlyLE
      (((TwMod.comp R T.U T.ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K') b :=
    (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
      (TwMod.comp R T.U T.ch α).map_isZero (CochainComplex.isZero_of_isStrictlyLE K' b i hi)
  exact @isKFlat_of_isFlat _ _ _ _ _ (R.over (T.U α)) _ b this (fun n => hflat n α)

/-- Flatness transfers along an isomorphism (retract argument). -/
private theorem isFlat_of_iso' {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
    {S : Sheaf J CommRingCat.{0}} {M F : Mod (ringOf S)} (e : M ≅ F) (hF : IsFlat S F) :
    IsFlat S M := by
  refine ⟨fun {N' N} f hf => ?_⟩
  have h1 : Mono (((tensorBifunctor S).obj F).map f) := hF.preserves f
  have hsplit : ((tensorBifunctor S).map e.hom).app N' ≫ ((tensorBifunctor S).map e.inv).app N' =
      𝟙 _ := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id]
    rfl
  have h2 : Mono (((tensorBifunctor S).map e.hom).app N') := mono_of_mono_fac hsplit
  have h3 : Mono (((tensorBifunctor S).map e.hom).app N' ≫ ((tensorBifunctor S).obj F).map f) :=
    mono_comp _ _
  have hnat := ((tensorBifunctor S).map e.hom).naturality f
  rw [← hnat] at h3
  exact mono_of_mono _ (((tensorBifunctor S).map e.hom).app N)

/-- Flatness restricts along `restrOver` (via `extX`, `isFlat_extX` and `IsFlat.restr`). -/
private theorem isFlat_restrOver' {V W : Opens X} (hW : W ≤ V) {M : Mod ((ringOf R).over V)}
    (hM : IsFlat (R.over V) M) : IsFlat (R.over W) ((restrOver (ringOf R) hW).obj M) := by
  have h1 : IsFlat (R.over W) ((restr (ringOf R) W).obj (extX V M)) :=
    IsFlat.restr R (isFlat_extX hM) W
  have e : (restrOver (ringOf R) hW).obj M ≅ (restr (ringOf R) W).obj (extX V M) :=
    ((restrOver (ringOf R) hW).mapIso (extXRestrIso V M)).symm ≪≫
      (restr_restrOver (ringOf R) hW).app (extX V M)
  exact isFlat_of_iso' e h1

/-- Complex-level `sheafBCRestrOverIso`. -/
private def sheafBCRestrOverComplexIso {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
    (ψ : R ⟶ S) {V W : Opens X} (hW : W ≤ V) (K : CochainComplex (Mod ((ringOf R).over V)) ℤ) :
    ((restrOver (ringOf S) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((sheafBC (overHom ψ V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
    ((sheafBC (overHom ψ W)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((restrOver (ringOf R) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => sheafBCRestrOverIso ψ hW (K.X n))
    (fun i j _ => (sheafBCRestrOverIso_hom_naturality ψ hW (K.d i j)).symm)

/-- **Z3.u (G′ (c)).** S8.g on over-sites: for `ψ : R ⟶ S`, `W ≤ V` and a strictly bounded above
complex `K` of flat `R|V`-modules whose restriction to `W` has a roof to a strictly perfect
complex, the restriction to `W` of `S|V ⊗ K` has a roof to a strictly perfect complex. As
`exists_roof_sheafBC`, with `restrOver` and `sheafBCRestrOverIso` (C.7′ (a)) in place of `restr`
and `sheafBCOverIso`. -/
theorem exists_roof_sheafBC_restrOver {S : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
    (ψ : R ⟶ S) {V W : Opens X} (hW : W ≤ V) (K : CochainComplex (Mod ((ringOf R).over V)) ℤ)
    (b : ℤ) [K.IsStrictlyLE b] (hflat : ∀ n, IsFlat (R.over V) (K.X n))
    (L P : CochainComplex (Mod ((ringOf R).over W)) ℤ)
    (f : L ⟶ ((restrOver (ringOf R) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (g : L ⟶ P) [QuasiIso f] [QuasiIso g] (hP : IsStrictlyPerfect P) :
    ∃ (L' P' : CochainComplex (Mod ((ringOf S).over W)) ℤ)
      (f' : L' ⟶ ((restrOver (ringOf S) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((sheafBC (overHom ψ V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      (g' : L' ⟶ P'), QuasiIso f' ∧ QuasiIso g' ∧ IsStrictlyPerfect P' := by
  obtain ⟨⟨a, bP, -, hbP⟩, -⟩ := id hP
  have := isStrictlyLE_restrOver (R := ringOf R) hW K b
  have hKU : IsKFlat (R.over W)
      (((restrOver (ringOf R) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    @isKFlat_of_isFlat _ _ _ _ _ (R.over W)
      (((restrOver (ringOf R) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) b this
      fun n => isFlat_restrOver' hW (hflat n)
  have hPK : IsKFlat (R.over W) P := isKFlat_of_isStrictlyPerfect (R.over W) hP
  have hLE : L.IsLE bP := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    have := ‹QuasiIso g›.quasiIsoAt i
    exact (exactAt_iff_of_quasiIsoAt g i).2 (P.exactAt_of_isLE bP i hi)
  have : (L.truncLE bP).IsStrictlyLE bP := by
    unfold CochainComplex.IsStrictlyLE
    infer_instance
  obtain ⟨F, h, hFle, hFflat, hh⟩ : ∃ (F : CochainComplex (Mod ((ringOf R).over W)) ℤ)
      (h : F ⟶ L.truncLE bP), F.IsStrictlyLE bP ∧ (∀ n, IsFlat (R.over W) (F.X n)) ∧
      QuasiIso h :=
    @exists_quasiIso_flat_site _ _ _ _ _ (R.over W) (L.truncLE bP) bP this
  have hF : IsKFlat (R.over W) F :=
    @isKFlat_of_isFlat _ _ _ _ _ (R.over W) F bP hFle hFflat
  have i1 : QuasiIso (L.ιTruncLE bP) := inferInstance
  have h01 : QuasiIso (L.ιTruncLE bP ≫ f) := inferInstance
  have h02 : QuasiIso (L.ιTruncLE bP ≫ g) := inferInstance
  have h1 : QuasiIso (h ≫ L.ιTruncLE bP ≫ f) := quasiIso_comp h (L.ιTruncLE bP ≫ f)
  have h2 : QuasiIso (h ≫ L.ιTruncLE bP ≫ g) := quasiIso_comp h (L.ιTruncLE bP ≫ g)
  have q1 := @quasiIso_sheafBC_of_isKFlat _ _ _ _ _ _ _ (overHom ψ W) _ _ hF hKU
    (h ≫ L.ιTruncLE bP ≫ f) h1
  have q2 := @quasiIso_sheafBC_of_isKFlat _ _ _ _ _ _ _ (overHom ψ W) _ _ hF hPK
    (h ≫ L.ιTruncLE bP ≫ g) h2
  refine ⟨_, _, ((sheafBC (overHom ψ W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (h ≫ L.ιTruncLE bP ≫ f) ≫ (sheafBCRestrOverComplexIso ψ hW K).inv,
    ((sheafBC (overHom ψ W)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (h ≫ L.ιTruncLE bP ≫ g), quasiIso_comp_inv _ (sheafBCRestrOverComplexIso ψ hW K)
        (hf := q1), q2, IsStrictlyPerfect.sheafBC (overHom ψ W) hP⟩

end Generic

variable (P : PreResolvingData X) {h : P.D.A ⊤} (T : TwistDatum P.toSheafData h)
  (K' : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ)

/-- Z3.u: `untwistRestrIso` commutes with the differentials of `F = untwist(K')` and of
`F_{K'_α}`. -/
theorem untwFRestrIso_comm (α : T.ι) (i j : ℤ) :
    (restr (ringOf P.A0) (T.U α)).map ((untwF P T K').d i j) ≫
        (untwistRestrIso P T (K'.X j) α).hom =
      (untwistRestrIso P T (K'.X i) α).hom ≫ (twFα P T K' α).d i j :=
  untwistRestrIso_hom_naturality P T (K'.d i j) α

/-- **Z3.u (G′ (b)).** [A, Rem 7.2.4]. `F|U_α ≅ F_{K'_α}` as complexes of `𝒜⁰|U_α`-modules
(`untwistRestrIso` in each degree; C.7 (c)). -/
def untwFRestrIso (α : T.ι) :
    ((restr (ringOf P.A0) (T.U α)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (untwF P T K') ≅ twFα P T K' α :=
  HomologicalComplex.Hom.isoOfComponents (fun n => untwistRestrIso P T (K'.X n) α)
    (fun i j _ => (untwFRestrIso_comm P T K' α i j).symm)

/-- **Z3.u (G′ (c)).** [A, Prop 7.2.18 step 2], blueprint-tw G.3. If `K'` is twisted perfect,
strictly bounded above with componentwise flat terms, then `F = untwist(K')` is a perfect complex
of `𝒜⁰`-modules on `X`: near `x ∈ U_α`, `F|W ≅ (𝒜⁰ ⊗ K'_α)|W` (`untwFRestrIso`,
`restr_restrOver`, C.7′ (a)) has a roof to a strictly perfect complex
(`exists_roof_sheafBC_restrOver`). -/
theorem isPerfect_untwF (hK' : TwIsPerfect K') (b : ℤ) [K'.IsStrictlyLE b]
    (hflat : ∀ n, TwIsFlat (K'.X n)) : IsPerfect (untwF P T K') := by
  intro x
  obtain ⟨α, hα⟩ : ∃ α, x ∈ T.U α := by
    have hx : x ∈ (⨆ α, T.U α : Opens X) := by rw [T.iSup_eq]; trivial
    exact Opens.mem_iSup.1 hx
  obtain ⟨W, hW, hxW, L, P', f, g, hf, hg, hP⟩ := hK' α x hα
  have : CochainComplex.IsStrictlyLE (twKα P T K' α) b :=
    (CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
      (TwMod.comp _ T.U T.ch α).map_isZero (CochainComplex.isZero_of_isStrictlyLE K' b i hi)
  obtain ⟨L', P'', f', g', h1, h2, h3⟩ :=
    exists_roof_sheafBC_restrOver (R := P.toSheafData.O) P.ρSheafT hW
      (twKα P T K' α) b (fun n => hflat n α) L P' f g hP
  let e : ((restr (ringOf P.A0) W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (untwF P T K') ≅
      ((restrOver (ringOf P.A0) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (twFα P T K' α) :=
    ((Functor.mapHomologicalComplexCompIso (restr_restrOver (ringOf P.A0) hW)
      (ComplexShape.up ℤ)).app (untwF P T K')).symm ≪≫
      ((restrOver (ringOf P.A0) hW).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (untwFRestrIso P T K' α)
  have : IsIso e.inv := Iso.isIso_inv e
  exact ⟨W, hxW, L', P'', f' ≫ e.inv, g', quasiIso_comp_inv f' e (hf := h1), h2, h3⟩

end Cohesive
