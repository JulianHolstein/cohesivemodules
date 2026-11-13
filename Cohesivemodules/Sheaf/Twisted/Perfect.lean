import Cohesivemodules.Sheaf.Twisted.PerfectOver
import Cohesivemodules.Sheaf.Twisted.SubQuot

set_option linter.style.header false

/-!
# Z3.j: twisted perfect complexes

Blueprint item Z3.j (`blueprint/blueprint-tw.md` §3 C.6 (e)–(g)). For `ȟ`-twisted sheaves:
* the component functors `comp_α` are exact, so they preserve quasi-isomorphisms and homology;
  a twisted sheaf with zero components is zero;
* `TwIsPerfect` is invariant under quasi-isomorphism, and `Q K ∈ TwPerf ↔ TwIsPerfect K`;
* for a normalized `ch`, the gluing maps form an isomorphism `comp_α ⋙ resL ≅ comp_β ⋙ resR`;
* twisted S9.d: on compact `X`, a twisted perfect complex has local models in one degree range
  `[a, b]` for all components (`TwIsPerfectIn K a b`), and its homology vanishes outside `[a, b]`.

## Deviations
* S9.d is stated for any family `ch` with `ch_αβα = 1` and any cover of `X`; a `TwistCocycle`
  satisfies both (`TwIsPerfect.exists_twIsPerfectIn_cocycle`). The cover need not be finite.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}

/-! ## (e) Exactness of the component functors -/

/-- Z3.j (e): the component functor preserves finite limits (it preserves kernels, Z3.h). -/
instance comp_preservesFiniteLimits (α : ι) : PreservesFiniteLimits (TwMod.comp R U ch α) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- Z3.j (e): the component functor preserves finite colimits (it preserves cokernels, Z3.h). -/
instance comp_preservesFiniteColimits (α : ι) : PreservesFiniteColimits (TwMod.comp R U ch α) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- Z3.j (e): the component functors preserve quasi-isomorphisms (instance search). -/
example (α : ι) {K L : CochainComplex (TwMod R U ch) ℤ} (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  inferInstance

/-- **Z3.j (e).** A twisted sheaf whose components are all zero is zero. -/
theorem TwMod.isZero_of_comp {M : TwMod R U ch} (h : ∀ α, IsZero ((TwMod.comp R U ch α).obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact TwMod.hom_ext fun α => (h α).eq_of_src _ _

/-- **Z3.j (e).** A complex of twisted sheaves is exact at `i` if all its component complexes are
(homology commutes with the exact functors `comp_α`). -/
theorem exactAt_of_comp {K : CochainComplex (TwMod R U ch) ℤ} (i : ℤ)
    (h : ∀ α, (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt i) :
    K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
  refine TwMod.isZero_of_comp fun α => ?_
  have h1 : ((K.sc i).map (TwMod.comp R U ch α)).Exact := h α
  rw [ShortComplex.exact_iff_isZero_homology] at h1
  exact IsZero.of_iso h1 ((K.sc i).mapHomologyIso (TwMod.comp R U ch α)).symm

/-! ## Invariance under quasi-isomorphism -/

/-- **Z3.j (e).** As S9.c. The target of a quasi-isomorphism out of a twisted perfect complex is
twisted perfect (componentwise, `IsPerfectOver.of_quasiIso_left`). -/
theorem TwIsPerfect.of_quasiIso_left {K K' : CochainComplex (TwMod R U ch) ℤ} (f : K ⟶ K')
    [QuasiIso f] (hK : TwIsPerfect K) : TwIsPerfect K' := fun α =>
  IsPerfectOver.of_quasiIso_left
    (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).map f) (hK α)

/-- **Z3.j (e).** As S9.c. The source of a quasi-isomorphism into a twisted perfect complex is
twisted perfect (componentwise, `IsPerfectOver.of_quasiIso_right`). -/
theorem TwIsPerfect.of_quasiIso_right {K K' : CochainComplex (TwMod R U ch) ℤ} (f : K ⟶ K')
    [QuasiIso f] (hK' : TwIsPerfect K') : TwIsPerfect K := fun α =>
  IsPerfectOver.of_quasiIso_right
    (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).map f) (hK' α)

/-- An isomorphism in the derived category of twisted sheaves is a roof of quasi-isomorphisms. -/
private lemma twExists_roof_of_iso [HasDerivedCategory.{0} (TwMod R U ch)]
    {K K' : CochainComplex (TwMod R U ch) ℤ}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj K') :
    ∃ (M : CochainComplex (TwMod R U ch) ℤ) (s : M ⟶ K) (g : M ⟶ K'), QuasiIso s ∧ QuasiIso g := by
  obtain ⟨M, s, hs, g, hg⟩ := DerivedCategory.right_fac e.hom
  have h4 : IsIso (DerivedCategory.Q.map g) := by
    have : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ e.hom := by
      rw [hg, IsIso.hom_inv_id_assoc]
    rw [this]; infer_instance
  exact ⟨M, s, g, (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hs,
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).1 h4⟩

/-- **Z3.j (e).** As S9.c (`perf_Q_obj_iff`). `Q K` lies in `D_perf(X, ȟ)` iff `K` is twisted
perfect: an isomorphism `Q K ≅ Q K'` in the derived category is a roof of quasi-isomorphisms. -/
theorem twPerf_Q_obj_iff [HasDerivedCategory.{0} (TwMod R U ch)]
    (K : CochainComplex (TwMod R U ch) ℤ) :
    TwPerf R U ch (DerivedCategory.Q.obj K) ↔ TwIsPerfect K := by
  constructor
  · rintro ⟨K', hK', ⟨e⟩⟩
    obtain ⟨M, s, g, hs, hg⟩ := twExists_roof_of_iso e
    exact TwIsPerfect.of_quasiIso_left s (TwIsPerfect.of_quasiIso_right g hK')
  · intro hK
    exact ⟨K, hK, ⟨Iso.refl _⟩⟩

/-! ## (f) The gluing isomorphism -/

/-- The inverse gluing map `M_β|U_αβ ⟶ M_α|U_αβ`, given on sections by `φ_βα`. -/
private def glueInv (M : TwMod R U ch) (α β : ι) :
    (resR (R := R) (U := U) α β).obj (M.M β) ⟶ (resL (R := R) (U := U) α β).obj (M.M α) :=
  homOfSec inf_le_right inf_le_left
    (fun hW => M.φ β α (hW.trans inf_le_right) (hW.trans inf_le_left))
    (fun _ r x => M.φ_smul β α _ _ r x) (fun _ h' x => M.φ_res β α _ _ h' x)

/-- **Z3.j (f).** [Căldăraru, Def 1.2.1]. For a normalized family (`ȟ_αβα = 1`), the gluing maps
`glueHom M α β : M_α|U_αβ ⟶ M_β|U_αβ` are the components of a natural isomorphism; the inverse is
given on sections by `φ_βα` (`TwMod.φ_symm`). -/
def glueNatIso (hch : ∀ α β, ch α β α = 1) (α β : ι) :
    TwMod.comp R U ch α ⋙ resL (R := R) (U := U) α β ≅
      TwMod.comp R U ch β ⋙ resR (R := R) (U := U) α β :=
  NatIso.ofComponents
    (fun M => ⟨M.glueHom α β, glueInv M α β,
      by
        ext Y x
        exact TwMod.φ_symm hch M α β _ _ x,
      by
        ext Y x
        exact TwMod.φ_symm hch M β α _ _ x⟩)
    (fun {M N} q => TwMod.Hom.glue_comm q α β)

/-- **Z3.j (f).** The components of `glueNatIso` are the gluing maps. -/
theorem glueNatIso_hom_app (hch : ∀ α β, ch α β α = 1) (α β : ι) (M : TwMod R U ch) :
    (glueNatIso hch α β).hom.app M = M.glueHom α β :=
  rfl

/-- Composite of functors on complexes is the composite of the complex functors (rfl). -/
private def compResLIso {K : CochainComplex (TwMod R U ch) ℤ} {α β : ι} :
    (((TwMod.comp R U ch α) ⋙ resL (R := R) (U := U) α β).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ≅
    ((resL (R := R) (U := U) α β).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := Iso.refl _

/-- Composite of functors on complexes is the composite of the complex functors (rfl). -/
private def compResRIso {K : CochainComplex (TwMod R U ch) ℤ} {α β : ι} :
    (((TwMod.comp R U ch β) ⋙ resR (R := R) (U := U) α β).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K ≅
    ((resR (R := R) (U := U) α β).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((TwMod.comp R U ch β).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := Iso.refl _

/-- Restrictions compose (rfl), on complexes. -/
private def restrOverCompIso {α : ι} {V W : Opens X} (hW : W ≤ V) (h : V ≤ U α)
    (Y : CochainComplex (Mod ((ringOf R).over (U α))) ℤ) :
    ((restrOver (ringOf R) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((restrOver (ringOf R) h).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≅
    ((restrOver (ringOf R) (hW.trans h)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y :=
  Iso.refl _

/-- The gluing isomorphism restricted to `W ≤ U_α ⊓ U_β`, on component complexes. -/
private def glueRestrIso (hch : ∀ α β, ch α β α = 1)
    {K : CochainComplex (TwMod R U ch) ℤ} {α β : ι} {W : Opens X} (hW : W ≤ U α ⊓ U β) :
    ((restrOver (ringOf R) (hW.trans inf_le_left)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
    ((restrOver (ringOf R) (hW.trans inf_le_right)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((TwMod.comp R U ch β).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (restrOverCompIso hW inf_le_left _).symm ≪≫
    ((restrOver (ringOf R) hW).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (compResLIso.symm ≪≫
        (NatIso.mapHomologicalComplex (glueNatIso hch α β) (ComplexShape.up ℤ)).app K
          ≪≫ compResRIso) ≪≫ restrOverCompIso hW inf_le_right _

/-- **Z3.j (f).** Transport of local models along the gluing isomorphism: on `W ≤ U_α ⊓ U_β`, the
restrictions `K_α|W` and `K_β|W` of the components of a complex of twisted sheaves are isomorphic,
so local models in `[a, b]` of one are local models of the other. -/
theorem isPerfectOverIn_comp_of_inf (hch : ∀ α β, ch α β α = 1)
    {K : CochainComplex (TwMod R U ch) ℤ} {α β : ι} {W : Opens X} (hW : W ≤ U α ⊓ U β) {a b : ℤ}
    (h : IsPerfectOverIn (((restrOver (ringOf R) (hW.trans inf_le_right)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((TwMod.comp R U ch β).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a b) :
    IsPerfectOverIn (((restrOver (ringOf R) (hW.trans inf_le_left)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a b := by
  exact IsPerfectOverIn.of_quasiIso_left (glueRestrIso hch hW (K := K)).inv h

/-! ## (g) Twisted S9.d -/

/-- **Z3.j (g).** As S9.d (`IsPerfectIn`). A complex of twisted sheaves whose component
complexes all have local strictly perfect models concentrated in degrees `[a, b]`. -/
def TwIsPerfectIn (K : CochainComplex (TwMod R U ch) ℤ) (a b : ℤ) : Prop :=
  ∀ α : ι,
    IsPerfectOverIn (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) a b

/-- Z3.j (g): local models in `[a, b]` are local models. -/
theorem TwIsPerfectIn.twIsPerfect {K : CochainComplex (TwMod R U ch) ℤ} {a b : ℤ}
    (hK : TwIsPerfectIn K a b) : TwIsPerfect K := fun α => (hK α).isPerfectOver

/-- **Z3.j (g).** As S9.d. The homology of a complex of twisted sheaves with local models in
`[a, b]` vanishes outside `[a, b]` (componentwise, `IsPerfectOverIn.exactAt`, `exactAt_of_comp`).
-/
theorem TwIsPerfectIn.exactAt {K : CochainComplex (TwMod R U ch) ℤ} {a b : ℤ}
    (hK : TwIsPerfectIn K a b) (i : ℤ) (hi : i < a ∨ b < i) : K.ExactAt i :=
  exactAt_of_comp i fun α => (hK α).exactAt i hi

/-- Local models in `[a, b]` are local models in any larger range. -/
private lemma isPerfectOverIn_mono {V : Opens X} {K : CochainComplex (Mod ((ringOf R).over V)) ℤ}
    {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') (h : IsPerfectOverIn K a b) :
    IsPerfectOverIn K a' b' := by
  intro x hx
  obtain ⟨W, hW, hxW, L, P, f, g, hf, hg, hP, hGE, hLE⟩ := h x hx
  exact ⟨W, hW, hxW, L, P, f, g, hf, hg, hP, P.isStrictlyGE_of_ge a' a ha,
    P.isStrictlyLE_of_le b b' hb⟩

/-- Pointwise step of twisted S9.d: near each `x` some component has local models in a range. -/
private lemma exists_local_range (hU : ⨆ α, U α = ⊤) {K : CochainComplex (TwMod R U ch) ℤ}
    (hK : TwIsPerfect K) (x : X) :
    ∃ (β : ι) (W : Opens X) (hW : W ≤ U β), x ∈ W ∧ ∃ a b : ℤ, IsPerfectOverIn
      (((restrOver (ringOf R) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((TwMod.comp R U ch β).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a b := by
  have hx : x ∈ ⨆ α, U α := by rw [hU]; trivial
  obtain ⟨β, hβ⟩ := Opens.mem_iSup.1 hx
  obtain ⟨W, hW, hxW, L, P, f, g, hf, hg, hP⟩ := hK β x hβ
  obtain ⟨⟨a, b, ha, hb⟩, -⟩ := id hP
  have := ha
  have := hb
  have := hf
  have := hg
  exact ⟨β, W, hW, hxW, a, b, isPerfectOverIn_of_roof f g hP⟩

/-- Twisted S9.d, transport step: models of `K_β` on `W` restrict to models of `K_α` on `W ⊓ U_α`
(`IsPerfectOverIn` restricts, glues along `glueNatIso`). -/
private lemma isPerfectOverIn_transport (hch : ∀ α β, ch α β α = 1)
    {K : CochainComplex (TwMod R U ch) ℤ} (α β : ι) {W : Opens X} (hW : W ≤ U β) {a b : ℤ}
    (h : IsPerfectOverIn
      (((restrOver (ringOf R) hW).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((TwMod.comp R U ch β).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a b) :
    IsPerfectOverIn
      (((restrOver (ringOf R) (inf_le_right : W ⊓ U α ≤ U α)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a b := by
  have hV : W ⊓ U α ≤ U α ⊓ U β := le_inf inf_le_right (inf_le_left.trans hW)
  have h1 := h.restrOver (inf_le_left : W ⊓ U α ≤ W)
  have h2 : IsPerfectOverIn
      (((restrOver (ringOf R) (hV.trans inf_le_right)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((TwMod.comp R U ch β).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) a b :=
    IsPerfectOverIn.of_quasiIso_left
      (restrOverCompIso (inf_le_left : W ⊓ U α ≤ W) hW _).hom h1
  exact isPerfectOverIn_comp_of_inf hch hV h2

/-- **Z3.j (g).** [A, Def 7.2.11 (3)], as S9.d. On compact `X`, for a normalized family `ch` on
a cover of `X`, every twisted perfect complex has local models in one degree range `[a, b]` for
all components (finite subcover; models of `K_β` near a point of `U_α` are transported to `K_α`
along the gluing isomorphism). ⚠ Any cover and any family with `ȟ_αβα = 1`. -/
theorem TwIsPerfect.exists_twIsPerfectIn [CompactSpace X] (hch : ∀ α β, ch α β α = 1)
    (hU : ⨆ α, U α = ⊤) {K : CochainComplex (TwMod R U ch) ℤ} (hK : TwIsPerfect K) :
    ∃ a b : ℤ, TwIsPerfectIn K a b := by
  choose β W hW hxW a b hab using exists_local_range hU hK
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨-(∑ i ∈ t, |a i|), ∑ i ∈ t, |b i|, fun α => ?_⟩
  refine IsPerfectOverIn.of_restrOver fun y hy => ?_
  obtain ⟨i, hi, hyi⟩ : ∃ i ∈ t, y ∈ (W i : Set X) := by
    have := ht (Set.mem_univ y)
    simpa only [Set.mem_iUnion, exists_prop] using this
  have h1 : |a i| ≤ ∑ j ∈ t, |a j| :=
    Finset.single_le_sum (f := fun j => |a j|) (fun j _ => abs_nonneg _) hi
  have h2 : |b i| ≤ ∑ j ∈ t, |b j| :=
    Finset.single_le_sum (f := fun j => |b j|) (fun j _ => abs_nonneg _) hi
  have h3 : IsPerfectOverIn _ (-(∑ j ∈ t, |a j|)) (∑ j ∈ t, |b j|) :=
    isPerfectOverIn_mono (by linarith [neg_abs_le (a i)]) (by linarith [le_abs_self (b i)])
      (hab i)
  exact ⟨W i ⊓ U α, inf_le_right, ⟨hyi, hy⟩, isPerfectOverIn_transport hch α (β i) (hW i) h3⟩

/-- **Z3.j (g).** Twisted S9.d for a twist cocycle `T` on compact `X`. -/
theorem TwIsPerfect.exists_twIsPerfectIn_cocycle [CompactSpace X] (T : TwistCocycle R)
    {K : CochainComplex (TwMod R T.U T.ch) ℤ} (hK : TwIsPerfect K) :
    ∃ a b : ℤ, TwIsPerfectIn K a b :=
  TwIsPerfect.exists_twIsPerfectIn (fun α β => T.normalized α β α (Or.inr (Or.inr rfl)))
    T.iSup_eq hK

/-- **Z3.j (g).** On compact `X`, the homology of a twisted perfect complex (for a twist cocycle)
is bounded: it vanishes outside some `[a, b]`. -/
theorem TwIsPerfect.exists_exactAt [CompactSpace X] (T : TwistCocycle R)
    {K : CochainComplex (TwMod R T.U T.ch) ℤ} (hK : TwIsPerfect K) :
    ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → K.ExactAt i := by
  obtain ⟨a, b, h⟩ := TwIsPerfect.exists_twIsPerfectIn_cocycle T hK
  exact ⟨a, b, fun i hi => TwIsPerfectIn.exactAt h i hi⟩

end Cohesive
