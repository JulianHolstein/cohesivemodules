import Cohesivemodules.Sheaf.Twisted.HomRestrTw
import Cohesivemodules.Sheaf.HomOverSections

set_option linter.style.header false

/-!
# Z3.s: sections of `𝓗om^tw(K, L)|V ≅ 𝓗om(K_α|V, L_α|V)` followed by `f^*`, elementwise

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F′ (f), (j)); the twisted analogue of S7's
`homComplexOverIso_map₁_sections` (`Sheaf/HomOverSections.lean`), used by C4^tw step 3. For
`V ≤ U_α`, a complex `K'` on `Over V` with `f : K' ⟶ K_α|V`, a section `s` of `𝓗om^tw(K, L)ⁿ`
over `Y.left` (`Y : Over V`) and `T : Triplet n`:
* `twHomRestrOverIso_hom_f_π`: the `T`-factor of `twHomRestrOverIso` in degree `n` is the
  restriction of the `T`-factor followed by the per-factor isomorphism `twFactorIso`
  (`restr_restrOver`, `glueRestrIso`, `homSheafRestrOverIso`);
* `twHomRestrOver_map₁_sections`: the `(p, q)` component of the image of `s` under
  `twHomRestrOverIso ≫ f^*`, read as a cochain and evaluated at `Y` on `m ∈ K'^p(Y)`, is the
  `α`-component of the `T`-factor of `s` (a morphism `K^p_α|(Y ⊓ U_α) ⟶ L^q_α|(Y ⊓ U_α)`)
  evaluated over `Y.left` on `f(m)`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite
open CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X} {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ}
  (hch : ∀ α β, ch α β α = 1) (hU : ⨆ α, U α = ⊤) (α : ι) {V : Opens X} (hV : V ≤ U α)

/-- **Z3.s.** The per-factor isomorphism `glue(homTw(A, B))|V ≅ homSheaf (A_α|V) (B_α|V)` for
`V ≤ U_α` (`restr_restrOver`, `glueRestrIso`, `homSheafRestrOverIso`). -/
def twFactorIso (A B : TwMod R U ch) :
    (restr (ringOf R) V).obj ((glue R U).obj (homTw hch A B)) ≅
      homSheaf (isCommSheaf_over V) ((restrOver (ringOf R) hV).obj (A.M α))
        ((restrOver (ringOf R) hV).obj (B.M α)) :=
  ((restr_restrOver (ringOf R) hV).app _).symm ≪≫
    (restrOver (ringOf R) hV).mapIso (glueRestrIso (homTw hch A B) α) ≪≫
    homSheafRestrOverIso hV _ _

/-- The factors of `homComplexXRestrOverIso` (copy of the private lemma of
`Sheaf/Twisted/HomRestrOver.lean`). -/
private theorem homComplexXRestrOverIso_hom_π'' {U₀ : Opens X} (h : V ≤ U₀)
    (K L : CochainComplex (Mod ((ringOf R).over U₀)) ℤ) (n : ℤ) (T : Triplet n) :
    (homComplexXRestrOverIso h K L n).hom ≫
        Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over V) (((restrOverC h).obj K).X T.p)
          (((restrOverC h).obj L).X T.q)) T =
      (restrOver (ringOf R) h).map
          (Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over U₀) (K.X T.p) (L.X T.q)) T) ≫
        (homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom := by
  rw [homComplexXRestrOverIso, Iso.trans_hom]
  erw [Category.assoc]
  have key : (Pi.mapIso fun T : Triplet n ↦ homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom ≫
      Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over V) ((restrOver (ringOf R) h).obj
        (K.X T.p)) ((restrOver (ringOf R) h).obj (L.X T.q))) T =
      Pi.π (fun T : Triplet n ↦ (restrOver (ringOf R) h).obj
        (homSheaf (isCommSheaf_over U₀) (K.X T.p) (L.X T.q))) T ≫
        (homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom :=
    Pi.map_π (fun T : Triplet n ↦ (homSheafRestrOverIso h (K.X T.p) (L.X T.q)).hom) T
  refine (congrArg (fun z => (PreservesProduct.iso (restrOver (ringOf R) h)
    fun T : Triplet n ↦ homSheaf (isCommSheaf_over U₀) (K.X T.p) (L.X T.q)).hom ≫ z) key).trans ?_
  rw [PreservesProduct.iso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (piComparison_comp_π (restrOver (ringOf R) h)
      (fun T : Triplet n ↦ homSheaf (isCommSheaf_over U₀) (K.X T.p) (L.X T.q)) T))

/-- **Z3.s.** The `T`-factor of `twHomRestrOverIso` in degree `n`: restriction of the `T`-factor
of `𝓗om^tw(K, L)ⁿ` to `V`, then `twFactorIso`. -/
theorem twHomRestrOverIso_hom_f_π (K L : CochainComplex (TwMod R U ch) ℤ) (n : ℤ)
    (T : Triplet n) :
    (twHomRestrOverIso hch hU α hV K L).hom.f n ≫
        Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over V)
          (((restrOverC hV).obj ((compC α).obj K)).X T.p)
          (((restrOverC hV).obj ((compC α).obj L)).X T.q)) T =
      (restr (ringOf R) V).map
          (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T) ≫
        (twFactorIso hch α hV (K.X T.p) (L.X T.q)).hom := by
  have e2 : (twHomXRestrIso hch K L n α).hom ≫
      Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over (U α)) (((compC α).obj K).X T.p)
        (((compC α).obj L).X T.q)) T =
      (restr (ringOf R) (U α)).map
          (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T) ≫
        (glueRestrIso (homTw hch (K.X T.p) (L.X T.q)) α).hom :=
    twHomXRestrIso_hom_π hch K L n α T
  have e3 := (restr_restrOver (ringOf R) hV).inv.naturality
    (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T)
  show (restr_restrOver (ringOf R) hV).inv.app (twHomX hch K L n) ≫
      (restrOver (ringOf R) hV).map (twHomXRestrIso hch K L n α).hom ≫
      (homComplexXRestrOverIso hV ((compC α).obj K) ((compC α).obj L) n).hom ≫
      Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over V)
          (((restrOverC hV).obj ((compC α).obj K)).X T.p)
          (((restrOverC hV).obj ((compC α).obj L)).X T.q)) T = _
  rw [homComplexXRestrOverIso_hom_π'' hV]
  rw [← Category.assoc ((restrOver (ringOf R) hV).map (twHomXRestrIso hch K L n α).hom),
    ← Functor.map_comp]
  rw [e2]
  erw [Functor.map_comp]
  simp only [twFactorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
  erw [← Category.assoc, ← Category.assoc, ← e3]

/-- **Z3.s.** [twisted S7, elementwise]. For `f : K' ⟶ K_α|V`, a section `s` of `𝓗om^tw(K, L)ⁿ`
over `Y.left` (`Y : Over V`), `T : Triplet n` and `m ∈ K'^p(Y)`: the `T`-component of the cochain
of `(twHomRestrOverIso ≫ f^*)(s)` at `Y`, evaluated on `m`, is the `α`-component of the
`T`-factor of `s` evaluated over `Y.left` on `f(m)`. -/
theorem twHomRestrOver_map₁_sections (K L : CochainComplex (TwMod R U ch) ℤ)
    {K' : CochainComplex (Mod ((ringOf R).over V)) ℤ}
    (f : K' ⟶ (restrOverC hV).obj ((compC α).obj K)) (n : ℤ) (Y : Over V)
    (s : ((twHomComplex hch K L hU).X n).val.obj (op Y.left)) (T : Triplet n)
    (m : (K'.X T.p).val.obj (op Y)) :
    ((homComplexSectionsEquiv (isCommSheaf_over V) K' ((restrOverC hV).obj ((compC α).obj L)) n
        Y ((((twHomRestrOverIso hch hU α hV K L).hom ≫
          homComplexMap₁ (isCommSheaf_over V) f _).f n).val.app (op Y) s) T).val.app
          (op (Over.mk (𝟙 Y)))).hom m =
      secApp inf_le_right
        ((((Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T).val.app
          (op Y.left)).hom s).1 α) (le_inf le_rfl ((leOfHom Y.hom).trans hV))
        (((f.f T.p).val.app (op Y)).hom m) := by
  rw [homComplexSectionsEquiv_apply]
  have h1 := Pi.map_π (fun T : Triplet n ↦ homPre (isCommSheaf_over V) (f.f T.p)
    (((restrOverC hV).obj ((compC α).obj L)).X T.q)) T
  have h2 := twHomRestrOverIso_hom_f_π hch hU α hV K L n T
  have key : (twHomRestrOverIso hch hU α hV K L).hom.f n ≫
      (homComplexMap₁ (isCommSheaf_over V) f ((restrOverC hV).obj ((compC α).obj L))).f n ≫
      Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over V) (K'.X T.p)
        (((restrOverC hV).obj ((compC α).obj L)).X T.q)) T =
      (restr (ringOf R) V).map
          (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T) ≫
        (twFactorIso hch α hV (K.X T.p) (L.X T.q)).hom ≫
        homPre (isCommSheaf_over V) (f.f T.p) (((restrOverC hV).obj ((compC α).obj L)).X T.q) := by
    erw [h1, ← Category.assoc, h2, Category.assoc]
  exact congrArg (fun g => (((g.val.app (op Y)).hom s :
    (K'.X T.p).over Y ⟶ _).val.app (op (Over.mk (𝟙 Y)))).hom m) key

end Cohesive
