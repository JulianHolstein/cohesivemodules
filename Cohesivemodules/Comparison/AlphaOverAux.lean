import Cohesivemodules.Comparison.AlphaDef
import Cohesivemodules.Comparison.HomSheafRetract
import Cohesivemodules.Algebra.BaseChange
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Sites.Over

set_option linter.style.header false

/-!
# C1.c helpers: `α_U(M)^n` is a sheaf on the over-site

Helpers for `Comparison/AlphaOver.lean`: the retract of `α_U(M)^n(V)` onto a finite product of
the groups `𝒜^q(V)` (the retract data `Frm`, `iTot`, `rTot` of
`Comparison/HomSheafRetract.lean`, namespace `HomRetract`, with base `U₀` instead of `⊤`), and
the sheaf condition on the over-site.
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum HomRetract

section Transport

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]
  (f : DgaHom 𝒜 ℬ) (g : DgaHom ℬ 𝒞) (f₂ : DgaHom 𝒜 𝒞) (hf : g.comp f = f₂)
  (M : QuasiCohesive 𝒜)

/-- Two maps of (possibly curved) dgas that agree pointwise are equal. -/
theorem dgaHom_ext' {f f' : DgaHom 𝒜 ℬ} (h : ∀ a, f a = f' a) : f = f' := by
  cases f
  cases f'
  congr
  exact AlgHom.ext h

/-- A9.a transported: the comparison `(f₂)^*M → g^*(f^*M)` on total modules, for a map `f₂`
equal to `g ∘ f` (by `subst`, it is `bcCompTot`). -/
def cmpTot : Tot 𝒞 (BCGen f₂ M.Q) →+ Tot 𝒞 (BCGen g (BCGen f M.Q)) := by
  subst hf
  exact (bcCompTot f g M).toAddMonoidHom

/-- The inverse comparison `g^*(f^*M) → (f₂)^*M`, for `f₂ = g ∘ f`. -/
def cmpTotInv : Tot 𝒞 (BCGen g (BCGen f M.Q)) →+ Tot 𝒞 (BCGen f₂ M.Q) := by
  subst hf
  exact (bcCompTotInv f g M).toAddMonoidHom

/-- `cmpTot` along `rfl` is `bcCompTot`. -/
theorem cmpTot_rfl (x : Tot 𝒞 (BCGen (g.comp f) M.Q)) :
    cmpTot f g (g.comp f) rfl M x = bcCompTot f g M x := rfl

/-- `cmpTotInv` along `rfl` is `bcCompTotInv`. -/
theorem cmpTotInv_rfl (y : Tot 𝒞 (BCGen g (BCGen f M.Q))) :
    cmpTotInv f g (g.comp f) rfl M y = bcCompTotInv f g M y := rfl

/-- `cmpTot` preserves the total degree. -/
theorem cmpTot_mem {n : ℤ} {x : Tot 𝒞 (BCGen f₂ M.Q)} (hx : x ∈ totDeg 𝒞 (BCGen f₂ M.Q) n) :
    cmpTot f g f₂ hf M x ∈ totDeg 𝒞 (BCGen g (BCGen f M.Q)) n := by
  subst hf
  exact famTot_mem_totDeg (bcCompU f M.Q g) (bcCompU_smul f M.Q g) hx

/-- `cmpTotInv` preserves the total degree. -/
theorem cmpTotInv_mem {n : ℤ} {y : Tot 𝒞 (BCGen g (BCGen f M.Q))}
    (hy : y ∈ totDeg 𝒞 (BCGen g (BCGen f M.Q)) n) :
    cmpTotInv f g f₂ hf M y ∈ totDeg 𝒞 (BCGen f₂ M.Q) n := by
  subst hf
  exact famTot_mem_totDeg (bcCompV f M.Q g) (bcCompV_smul f M.Q g) hy

/-- `cmpTot` is `C`-linear. -/
theorem cmpTot_smul (c : C) (x : Tot 𝒞 (BCGen f₂ M.Q)) :
    cmpTot f g f₂ hf M (c • x) = c • cmpTot f g f₂ hf M x := by
  subst hf
  exact famTot_smul (bcCompU f M.Q g) (bcCompU_smul f M.Q g) c x

/-- `cmpTotInv` is `C`-linear. -/
theorem cmpTotInv_smul (c : C) (y : Tot 𝒞 (BCGen g (BCGen f M.Q))) :
    cmpTotInv f g f₂ hf M (c • y) = c • cmpTotInv f g f₂ hf M y := by
  subst hf
  exact famTot_smul (bcCompV f M.Q g) (bcCompV_smul f M.Q g) c y

/-- `cmpTotInv ∘ cmpTot = id`. -/
theorem cmpTotInv_cmpTot (x : Tot 𝒞 (BCGen f₂ M.Q)) :
    cmpTotInv f g f₂ hf M (cmpTot f g f₂ hf M x) = x := by
  subst hf
  exact bcCompTotInv_bcCompTot f g M x

/-- `cmpTot ∘ cmpTotInv = id`. -/
theorem cmpTot_cmpTotInv (y : Tot 𝒞 (BCGen g (BCGen f M.Q))) :
    cmpTot f g f₂ hf M (cmpTotInv f g f₂ hf M y) = y := by
  subst hf
  exact bcCompTot_bcCompTotInv f g M y

/-- `cmpTot` commutes with the operators `𝕏`. -/
theorem cmpTot_X (x : Tot 𝒞 (BCGen f₂ M.Q)) :
    ((M.baseChange f).baseChange g).X (cmpTot f g f₂ hf M x) =
      cmpTot f g f₂ hf M ((M.baseChange f₂).X x) := by
  subst hf
  exact bcCompTot_X f g M x

variable {D : Type} [Ring D] [Algebra k D] {𝒟 : ℤ → Submodule k D} [GradedAlgebra 𝒟] [GCDga 𝒟]
  (k' : DgaHom 𝒞 𝒟) (g' : DgaHom ℬ 𝒟) (f₃ : DgaHom 𝒜 𝒟) (hf' : g'.comp f = f₃)
  (hk : ∀ b, k' (g b) = g' b) (hkf : ∀ a, k' (f₂ a) = f₃ a)

/-- `cmpTot` is natural for restriction. -/
theorem cmpTot_bcTotRes (x : Tot 𝒞 (BCGen f₂ M.Q)) :
    cmpTot f g' f₃ hf' M (bcTotRes k' f₂ f₃ hkf M.Q x) =
      bcTotRes k' g g' hk (BCGen f M.Q) (cmpTot f g f₂ hf M x) := by
  subst hf hf'
  induction x using Tot.induction_on with
  | ht b e =>
    induction e using DirectSum.induction_on with
    | zero => simp only [Tot.tmul_zero, map_zero]
    | of p z =>
      induction z using BCGen.induction_on with
      | ht γ q =>
        simp only [bcTotRes_tmul, cmpTot_rfl, bcCompTot, famTot_tmul, DirectSum.map_of, famMap_of,
          bcGenRes_tmul, bcCompU_tmul]
      | hadd x y hx hy =>
        simp only [map_add, Tot.tmul_add, hx, hy]
    | add x y hx hy => simp only [map_add, Tot.tmul_add, hx, hy]
  | hadd x y hx hy => simp only [map_add, hx, hy]

end Transport

open CategoryTheory Opposite TopologicalSpace

section Sheaf

universe u v

/-- C1.c/C7: unique gluing (Yoneda form) passes to a retract of presheaves of types. -/
theorem isSheafFor_of_retract {C : Type u} [Category.{v} C] {F G : Cᵒᵖ ⥤ Type v}
    (i : F ⟶ G) (r : G ⟶ F) (hri : i ≫ r = 𝟙 F) {Y : C} (S : Sieve Y)
    (hG : Presieve.IsSheafFor G (S : Presieve Y)) : Presieve.IsSheafFor F (S : Presieve Y) := by
  rw [Presieve.isSheafFor_iff_yonedaSheafCondition] at hG ⊢
  intro s
  obtain ⟨g, hg, hu⟩ := hG (s ≫ i)
  refine ⟨g ≫ r, ?_, ?_⟩
  · show S.functorInclusion ≫ (g ≫ r) = s
    rw [← Category.assoc, hg, Category.assoc, hri, Category.comp_id]
  · intro g' hg'
    have h1 : g' ≫ i = g := hu _ (by
      show S.functorInclusion ≫ (g' ≫ i) = s ≫ i
      rw [← Category.assoc, hg'])
    calc g' = g' ≫ i ≫ r := by rw [hri, Category.comp_id]
      _ = (g' ≫ i) ≫ r := (Category.assoc _ _ _).symm
      _ = g ≫ r := by rw [h1]

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) {U : Opens X}

/-- Helper (C1.c): the type-valued presheaf `V ↦ α_U(M)^n(V)` on the over-site of `U`. -/
def sheafOfOverTy (M : CohesiveModule (P.D.𝒜 U)) (n : ℤ) : (Over U)ᵒᵖ ⥤ Type where
  obj V := P.sheafOfSec M n (leOfHom V.unop.hom)
  map {V W} f := ↾(fun x => P.sheafOfRes M n (leOfHom V.unop.hom) (leOfHom f.unop.left) x)
  map_id V := by
    ext x
    exact Subtype.ext (P.totRes_id M _ x.1)
  map_comp f g := by
    ext x
    exact Subtype.ext (P.totRes_comp M _ _ _ x.1).symm

/-- The presheaf `V ↦ ∏_i 𝒜^{q_i}(V)` of types on `X`. -/
private def gTy (I : Type) (q : I → ℤ) : (Opens X)ᵒᵖ ⥤ Type where
  obj V := ∀ i, ↥(P.D.𝒜 V.unop (q i))
  map {V W} f := ↾(fun y i => ⟨P.D.res (leOfHom f.unop) (y i), (P.D.res _).map_mem (y i).2⟩)
  map_id V := by
    ext y i
    exact P.D.res_id _ _
  map_comp f g := by
    ext y i
    exact (P.D.res_comp _ _ _).symm

/-- `gTy` is a sheaf of types (`P.glue` and `P.degree_local`). -/
private theorem isSheaf_gTy (I : Type) (q : I → ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (P.gTy I q) := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types (X := TopCat.of X)
    (P.gTy I q)).2 ?_
  intro ι U sf hsf
  have h : ∀ i j a, P.D.res (inf_le_left : U i ⊓ U j ≤ U i) (sf i a : P.D.A (U i)) =
      P.D.res (inf_le_right : U i ⊓ U j ≤ U j) (sf j a : P.D.A (U j)) :=
    fun i j a => congrArg Subtype.val (congrFun (hsf i j) a)
  have hmem : ∀ a, ∃! b : ↥(P.D.𝒜 (⨆ i, U i) (q a)),
      ∀ i, P.D.res (le_iSup U i) (b : P.D.A (⨆ i, U i)) = (sf i a : P.D.A (U i)) := by
    intro a
    obtain ⟨b, hb, hb'⟩ := P.glue U (fun i => (sf i a : P.D.A (U i))) (fun i j => h i j a)
    have hm : b ∈ P.D.𝒜 (⨆ i, U i) (q a) := by
      refine P.degree_local (q a) b fun x hx => ?_
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
      exact ⟨U i, le_iSup U i, hi, by rw [hb i]; exact (sf i a).2⟩
    exact ⟨⟨b, hm⟩, hb, fun b'' hb'' => Subtype.ext (hb' _ hb'')⟩
  choose t ht hu using hmem
  exact ⟨t, fun i => funext fun a => Subtype.ext (ht a i),
    fun t' ht' => funext fun a => hu a (t' a) fun i =>
      congrArg Subtype.val (congrFun (ht' i) a)⟩

/-- **C1.c (C1.a on `U`), type-valued form.** `α_U(M)^n` satisfies the sheaf condition on the
over-site of `U`: a retract of `(Over.forget U).op ⋙ ∏_i 𝒜^{n-p_i}`. -/
theorem isSheaf_sheafOfOverTy (M : CohesiveModule (P.D.𝒜 U)) (n : ℤ) :
    Presieve.IsSheaf ((Opens.grothendieckTopology X).over U) (P.sheafOfOverTy M n) := by
  obtain ⟨F⟩ := exists_frm (P.D.𝒜 U) M
  have hG : Presieve.IsSheaf ((Opens.grothendieckTopology X).over U)
      ((Over.forget U).op ⋙ P.gTy F.Idx (fun pj => n - pj.1)) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Over.forget U).op_comp_isSheaf_of_isSheaf _ _ _ (P.isSheaf_gTy F.Idx (fun pj => n - pj.1)))
  intro Y S hS
  refine isSheafFor_of_retract (F := P.sheafOfOverTy M n)
    (G := (Over.forget U).op ⋙ P.gTy F.Idx (fun pj => n - pj.1))
    { app := fun V => ↾(fun x pj =>
        ⟨iTot (P.D.res (leOfHom V.unop.hom)) F x.1 pj, iTot_mem _ F x.2 pj⟩)
      naturality := fun V W f => by
        ext x
        funext pj
        exact Subtype.ext (iTot_bcTotRes _ F (P.D.res (leOfHom f.unop.left)) _
          (P.D.res_comp _ _) x.1 pj) }
    { app := fun V => ↾(fun (a : ∀ pj : F.Idx, ↥(P.D.𝒜 V.unop.left (n - pj.1))) =>
        (⟨rTot (P.D.res (leOfHom V.unop.hom)) F (fun pj => (a pj : P.D.A _)),
          rTot_mem _ F (fun pj => (a pj).2)⟩ : P.sheafOfSec M n (leOfHom V.unop.hom)))
      naturality := fun V W f => by
        ext y
        exact Subtype.ext (bcTotRes_rTot _ F (P.D.res (leOfHom f.unop.left)) _
          (P.D.res_comp _ _) _).symm }
    ?_ S (hG S hS)
  ext V x
  exact Subtype.ext (rTot_iTot _ F x.1)

end PreResolvingData

end Sheaf

end Cohesive
