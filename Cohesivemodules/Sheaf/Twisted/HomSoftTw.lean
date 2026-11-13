import Cohesivemodules.Sheaf.Twisted.HomComplexTw
import Cohesivemodules.Sheaf.Soft

set_option linter.style.header false

/-!
# Z3.r: softness and bounds of `𝓗om^tw(K, L)`

Blueprint item Z3.r (`blueprint/blueprint-tw.md` §3 F′ (h)); twisted form of S7.a′ + S3.b(i)
(`isSoft_homSheafComplex_X`) and of the bound `exists_isStrictlyGE_homSheafComplex`.
* `isSoft_twHomComplex_X`: if the global sections of a fine sheaf of rings `S` act on every term
  `Kᵖ` by endomorphisms of twisted sheaves, additively, unitally, and `ρ` acts as `0` on the
  sections over every `W ≤ V ⊓ U_α` whenever `ρ|V = 0`, then every term of `𝓗om^tw(K, L)` is soft:
  `S(X)` acts on it by precomposition (`glue (homTwPre ·)` on each factor).
* `twHomComplex_isStrictlyGE`: for `K` strictly `≤ b` and `L` strictly `≥ a`, `𝓗om^tw(K, L)` is
  strictly `≥ a - b` (every factor of a term of degree `< a - b` has a zero source or target).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite
open CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}
  (hch : ∀ α β, ch α β α = 1) (hU : ⨆ α, U α = ⊤)

/-- `homPre` of a morphism vanishing on all `Z.left` for `Z` over `X0` vanishes over `X0`. -/
private lemma homPre_app_zero_gen {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
    {S : Sheaf J RingCat.{0}} (hS : IsCommSheaf S) {M M' : Mod S} (N : Mod S) (f : M' ⟶ M)
    (X0 : C) (h : ∀ Z : Over X0, f.val.app (op Z.left) = 0) :
    (homPre hS f N).val.app (op X0) = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
  change f.over X0 ≫ (φ : M.over X0 ⟶ N.over X0) = (0 : M'.over X0 ⟶ N.over X0)
  refine hom_ext_pt fun Z m ↦ ?_
  have h2 : ((f.val.app (op Z.unop.left)).hom m : M.val.obj (op Z.unop.left)) = 0 := by
    rw [h Z.unop]; rfl
  show (φ.val.app Z).hom ((f.val.app (op Z.unop.left)).hom m) = _
  rw [h2]
  exact map_zero _

/-- A product of morphisms vanishing on sections over `V` vanishes on sections over `V`. -/
private lemma pi_map_app_eq_zero' {κ : Type} {S : RingSheaf X} (F G : κ → Mod S)
    (g : ∀ i, F i ⟶ G i) [HasProduct F] [HasProduct G] (V : Opens X)
    (h : ∀ i, (g i).val.app (op V) = 0) : (Limits.Pi.map g).val.app (op V) = 0 := by
  let E := SheafOfModules.evaluation.{0} S (op V)
  have key : E.map (Limits.Pi.map g) ≫ piComparison E G = 0 := by
    apply Limits.Pi.hom_ext
    intro i
    rw [Category.assoc, piComparison_comp_π, zero_comp, ← E.map_comp, Limits.Pi.map_π,
      E.map_comp]
    have : E.map (g i) = 0 := h i
    rw [this, comp_zero]
  have := (cancel_mono (piComparison E G)).1 (key.trans (zero_comp).symm)
  exact this

/-- `glue` of the zero morphism is zero. -/
private lemma glue_map_zero (M N : TwMod R U (fun _ _ _ => 1)) :
    (glue R U).map (0 : M ⟶ N) = 0 := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro W
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ Subtype.ext (funext fun α ↦ ?_))
  exact map_zero (((0 : M ⟶ N).f α).val.app (ovr inf_le_right)).hom

/-- `glue` is additive on morphisms. -/
private lemma glue_map_add {M N : TwMod R U (fun _ _ _ => 1)} (f g : M ⟶ N) :
    (glue R U).map (f + g) = (glue R U).map f + (glue R U).map g := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro W
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ Subtype.ext (funext fun α ↦ ?_))
  rfl

/-- `homTwPre` of the identity is the identity. -/
private lemma homTwPre_id (K L : TwMod R U ch) : homTwPre hch (𝟙 K) L = 𝟙 _ := by
  refine TwMod.hom_ext fun α => ?_
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro Z
  exact ModuleCat.hom_ext (LinearMap.ext fun φ ↦ hom_ext_pt fun Z m ↦ rfl)

/-- If `K` or `L` is zero, the glued Hom sheaf `glue (homTw K L)` is zero. -/
private lemma isZero_glue_homTw (K L : TwMod R U ch) (h : IsZero K ∨ IsZero L) :
    IsZero ((glue R U).obj (homTw hch K L)) := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro W
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ Subtype.ext (funext fun α ↦ ?_))
  have hz : ∀ {W' : Opens X} (hW : W' ≤ U α),
      Subsingleton (sec R ((homTw hch K L).M α) hW) := fun {W'} hW ↦ by
    refine (homSheafSectionsEquiv (isCommSheaf_over (U α)) (K.M α) (L.M α)
      (Over.mk (homOfLE hW))).subsingleton_congr.2 ?_
    rcases h with h | h
    · have h1 : IsZero ((K.M α).over (Over.mk (homOfLE hW))) :=
        Functor.map_isZero (SheafOfModules.overFunctor.{0} _ _)
          (Functor.map_isZero (TwMod.comp R U ch α) h)
      exact ⟨fun a b ↦ h1.eq_of_src a b⟩
    · have h1 : IsZero ((L.M α).over (Over.mk (homOfLE hW))) :=
        Functor.map_isZero (SheafOfModules.overFunctor.{0} _ _)
          (Functor.map_isZero (TwMod.comp R U ch α) h)
      exact ⟨fun a b ↦ h1.eq_of_tgt a b⟩
  exact @Subsingleton.elim _ (hz (inf_le_right : W.unop ⊓ U α ≤ U α)) _ _

/-- **Z3.r (F′ (h)).** [A, Lemma 7.2.8], twisted S7.a′ + S3.b(i). An additive, unital action of
the global sections of a fine sheaf of rings `S` on the terms of `K` by endomorphisms of twisted
sheaves, vanishing on sections over `W ≤ V ⊓ U_α` when `ρ|V = 0`, makes every term of
`𝓗om^tw(K, L)` soft. As S7.a′, the action need not commute with the differential of `K`. -/
theorem isSoft_twHomComplex_X {S : RingSheaf X} (hS : IsFine S)
    {K : CochainComplex (TwMod R U ch) ℤ} (act : ∀ p : ℤ, S.obj.obj (op ⊤) →+ (K.X p ⟶ K.X p))
    (h1 : ∀ p, act p 1 = 𝟙 (K.X p))
    (hloc : ∀ (p : ℤ) (ρ : S.obj.obj (op ⊤)) (V : Opens X), rres S (le_top : V ≤ ⊤) ρ = 0 →
      ∀ (α : ι) {W : Opens X} (_ : W ≤ V) (hα : W ≤ U α), ((act p ρ).f α).val.app (ovr hα) = 0)
    (L : CochainComplex (TwMod R U ch) ℤ) (n : ℤ) :
    IsSoft ((twHomComplex hch K L hU).X n) := by
  let A : S.obj.obj (op ⊤) →+ (twHomX hch K L n ⟶ twHomX hch K L n) :=
    { toFun := fun ρ ↦ Limits.Pi.map fun T : Triplet n ↦
        (glue R U).map (homTwPre hch (act T.p ρ) (L.X T.q))
      map_zero' := by
        apply Limits.Pi.hom_ext
        intro T
        rw [Limits.Pi.map_π, zero_comp, map_zero, homTwPre_zero, glue_map_zero, comp_zero]
      map_add' := fun ρ σ ↦ by
        apply Limits.Pi.hom_ext
        intro T
        rw [Preadditive.add_comp, Limits.Pi.map_π, Limits.Pi.map_π, Limits.Pi.map_π,
          ← Preadditive.comp_add, map_add, homTwPre_add, glue_map_add] }
  refine IsSoft.of_action hS (twHomX hch K L n) A ?_ fun ρ V hV ↦ ?_
  · apply Limits.Pi.hom_ext
    intro T
    refine (Limits.Pi.map_π (fun T : Triplet n ↦
      (glue R U).map (homTwPre hch (act T.p 1) (L.X T.q))) T).trans ?_
    rw [h1, homTwPre_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · refine pi_map_app_eq_zero' (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
      (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
      (fun T : Triplet n ↦ (glue R U).map (homTwPre hch (act T.p ρ) (L.X T.q))) V fun T ↦ ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ Subtype.ext (funext fun α ↦ ?_))
    have key := homPre_app_zero_gen (isCommSheaf_over (U α)) ((L.X T.q).M α)
      ((act T.p ρ).f α) (Over.mk (homOfLE (inf_le_right : V ⊓ U α ≤ U α))) (fun Z ↦
        hloc T.p ρ V hV α (Z.hom.left.le.trans inf_le_left) Z.left.hom.le)
    exact congrArg (fun φ ↦ (φ.hom (s.1 α))) key

/-- **Z3.r (F′ (h)).** For `K` strictly `≤ b` and `L` strictly `≥ a`, `𝓗om^tw(K, L)` is strictly
`≥ a - b`. -/
theorem twHomComplex_isStrictlyGE (K L : CochainComplex (TwMod R U ch) ℤ) (a b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyGE a] : (twHomComplex hch K L hU).IsStrictlyGE (a - b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  change Limits.IsZero (twHomX hch K L n)
  rw [Limits.IsZero.iff_id_eq_zero]
  refine Limits.Pi.hom_ext _ _ fun T => ?_
  refine (isZero_glue_homTw hch _ _ ?_).eq_of_tgt _ _
  by_cases hp : b < T.p
  · exact Or.inl (K.isZero_of_isStrictlyLE b T.p hp)
  · have hq : T.q < a := by have := T.hpq; lia
    exact Or.inr (L.isZero_of_isStrictlyGE a T.q hq)

end Cohesive
