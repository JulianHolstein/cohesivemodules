import Cohesivemodules.Sheaf.Twisted.ExtTwAdj
import Cohesivemodules.Sheaf.FlatResolution

set_option linter.style.header false

/-!
# Z3.l: componentwise flat resolutions of twisted complexes

Blueprint item Z3.l (blueprint §11 v1.20 item 5; `blueprint/blueprint-tw.md` C.8, G.1). For a
twist cocycle `T`:
* `TwIsFlat M`: every component `M_α` is a flat sheaf of `R|U_α`-modules;
* every twisted sheaf `M` is a quotient of a componentwise flat one: `⊕_α extTw α F_α ↠ M` for
  flat epis `F_α ↠ M_α` (S8.c on `Over U_α`), a finite biproduct;
* every complex of twisted sheaves strictly zero above `b` receives a quasi-isomorphism from a
  complex strictly zero above `b` with componentwise flat terms (`exists_quasiIso_of_enough`).

## Deviations
* "Flat" componentwise ([A, §7.2] uses K-flatness of `𝒜` over `ℛ` instead, Malgrange; not assumed,
  blueprint-tw a9, D8).
-/

noncomputable section

namespace Cohesive

open CategoryTheory TopologicalSpace Opposite Limits

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}

/-- **Z3.l.** A twisted sheaf is componentwise flat if each component `M_α` is a flat sheaf of
`R|U_α`-modules (S8, `IsFlat` on the over-site `Over U_α`). -/
def TwIsFlat {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}
    (M : TwMod R U ch) : Prop :=
  ∀ α, IsFlat (R.over (U α)) (M.M α)

/-- Z3.l: twisted sheaves have finite biproducts (preadditive with finite products, Z3.h). -/
instance {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ} :
    HasFiniteBiproducts (TwMod R U ch) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Z3.l: flatness transfers along an isomorphism (retract argument). -/
private theorem isFlat_of_iso_aux {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
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

variable (T : TwistCocycle R)

/-- Z3.l: a zero twisted sheaf is componentwise flat. -/
theorem twIsFlat_of_isZero {M : TwMod R T.U T.ch} (hM : IsZero M) : TwIsFlat M := fun α =>
  isFlat_of_isZero (R.over (T.U α)) (Functor.map_isZero (TwMod.comp R T.U T.ch α) hM)

/-- **Z3.l.** A morphism of twisted sheaves whose components are epimorphisms is an epimorphism.
-/
theorem TwMod.epi_of_epi_f {M N : TwMod R T.U T.ch} (f : M ⟶ N) [∀ α, Epi (f.f α)] : Epi f :=
  ⟨fun g h hgh => TwMod.hom_ext fun α =>
    (cancel_epi (f.f α)).1 (by simpa only [TwMod.comp_f] using congrArg (fun k => k.f α) hgh)⟩

/-- **Z3.l.** A finite biproduct of componentwise flat twisted sheaves is componentwise flat
(`comp_β` is additive, so preserves biproducts; finite sums of flat sheaves are flat). -/
theorem twIsFlat_biproduct (F : T.ι → TwMod R T.U T.ch) (hF : ∀ i, TwIsFlat (F i)) :
    TwIsFlat (⨁ F) := fun β => by
  let e : (⨁ F).M β ≅ ∐ fun i => (F i).M β :=
    (TwMod.comp R T.U T.ch β).mapBiproduct F ≪≫ biproduct.isoCoproduct _
  exact isFlat_of_iso_aux e (isFlat_sigma (R.over (T.U β)) _ (fun i => hF i β))

/-- **Z3.l.** Blueprint §11 v1.20 item 5. Every twisted sheaf is a quotient of a componentwise
flat one: `⊕_α extTw α F_α ⟶ M` with `F_α ↠ M_α` flat (S8.c on `Over U_α`); its component `β`
is an epimorphism because `F_β ↠ M_β` factors through it (`extTwUnit_comp_lift`). -/
theorem exists_epi_twIsFlat (M : TwMod R T.U T.ch) :
    ∃ (F : TwMod R T.U T.ch) (f : F ⟶ M), TwIsFlat F ∧ Epi f := by
  have key : ∀ α, ∃ (F : Mod ((ringOf R).over (T.U α))) (f : F ⟶ M.M α),
      IsFlat (R.over (T.U α)) F ∧ Epi f := fun α => exists_epi_flat (R.over (T.U α)) (M.M α)
  choose F p hF hp using key
  refine ⟨⨁ fun α => extTwObj T α (F α), biproduct.desc fun α => extTwLift T α (p α),
    twIsFlat_biproduct T _ (fun α => isFlat_extTwObj T α (hF α)), ?_⟩
  have : ∀ β, Epi ((biproduct.desc fun α => extTwLift T α (p α)).f β) := fun β => by
    have h : (extTwUnit T β (F β) ≫ (biproduct.ι (fun α => extTwObj T α (F α)) β).f β) ≫
        (biproduct.desc fun α => extTwLift T α (p α)).f β = p β := by
      rw [Category.assoc, ← TwMod.comp_f, biproduct.ι_desc, extTwUnit_comp_lift]
    have := hp β
    exact epi_of_epi_fac h
  exact TwMod.epi_of_epi_f T _

/-- **Z3.l.** [A, §7.2], blueprint-tw C.8, G.1, as S8.d. Every complex `K` of twisted sheaves
strictly zero above degree `b` receives a quasi-isomorphism `f : F ⟶ K` from a complex strictly
zero above `b` whose terms are componentwise flat. -/
theorem exists_quasiIso_twIsFlat (K : CochainComplex (TwMod R T.U T.ch) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] :
    ∃ (F : CochainComplex (TwMod R T.U T.ch) ℤ) (f : F ⟶ K),
      F.IsStrictlyLE b ∧ (∀ n, TwIsFlat (F.X n)) ∧ QuasiIso f :=
  exists_quasiIso_of_enough (fun M => TwIsFlat M) (exists_epi_twIsFlat T)
    (fun _ hZ => twIsFlat_of_isZero T hZ) K b

end Cohesive
