import Cohesivemodules.Comparison.HomSheafRetract
import Cohesivemodules.Comparison.SheafDataAlphaDef

set_option linter.style.header false

/-!
# Z3.q: unique gluing for Tot(M|V) over DgaSheafData (copy of the C3 helpers)

The `PreResolvingData` part of `Comparison/HomSheafRetract.lean` word for word over
`S : DgaSheafData X` (blueprint-tw F′ (a)); the generic `HomRetract` namespace is reused.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace DgaSheafData

variable (S : DgaSheafData X) {U₀ : Opens X}

/-- Gluing of families of sections of the algebras `A(U)`, indexed by a type `J`. -/
theorem glue_fun (J : Type) {ι : Type} (U : ι → Opens X) (s : ∀ a, J → S.D.A (U a))
    (h : ∀ a b j, S.D.res (inf_le_left : U a ⊓ U b ≤ U a) (s a j) =
      S.D.res (inf_le_right : U a ⊓ U b ≤ U b) (s b j)) :
    ∃! t : J → S.D.A (⨆ a, U a), ∀ a j, S.D.res (le_iSup U a) (t j) = s a j := by
  choose t ht hu using fun j => S.glue U (fun a => s a j) (fun a b => h a b j)
  exact ⟨t, fun a j => ht j a, fun t' ht' => funext fun j => hu j (t' j) fun a => ht' a j⟩

/-- Unique gluing in `Tot(M|V)`, `V ↦ Tot(M|V)` (`M` cohesive over `𝒜(X)`). -/
theorem car_glue (M : CohesiveModule S.𝒜X) {ι : Type} (U : ι → Opens X)
    (s : ∀ a, S.TotSec M (le_top : U a ≤ ⊤))
    (hs : ∀ a b, S.totRes M le_top (inf_le_left : U a ⊓ U b ≤ U a) (s a) =
      S.totRes M le_top (inf_le_right : U a ⊓ U b ≤ U b) (s b)) :
    ∃! t : S.TotSec M (le_top : (⨆ a, U a) ≤ ⊤),
      ∀ a, S.totRes M le_top (le_iSup U a) t = s a := by
  obtain ⟨F⟩ := HomRetract.exists_frm S.𝒜X M
  refine HomRetract.glue_of_retract (Fv := fun V => S.TotSec M (le_top : V ≤ ⊤))
    (Gv := fun V => F.Idx → S.D.A V)
    (fun {V W} h x => S.totRes M le_top h x)
    (fun {V W} h y pj => S.D.res h (y pj))
    (fun V x => HomRetract.iTot (S.D.res (le_top : V ≤ ⊤)) F x)
    (fun V a => HomRetract.rTot (S.D.res (le_top : V ≤ ⊤)) F a)
    ?_ ?_ ?_ ?_ U s hs
  · intro V x
    exact HomRetract.rTot_iTot _ F x
  · intro V W h x
    funext pj
    exact (HomRetract.iTot_bcTotRes _ F (S.D.res h) _ (S.D.res_comp le_top h) x pj).symm
  · intro V W h y
    exact HomRetract.bcTotRes_rTot _ F (S.D.res h) _ (S.D.res_comp le_top h) y
  · intro ι' U' s' hs'
    obtain ⟨t, ht, hu⟩ := S.glue_fun F.Idx U' s' (fun a b j => congrFun (hs' a b) j)
    exact ⟨t, fun a => funext (ht a), fun t' ht' => hu t' fun a j => congrFun (ht' a) j⟩

/-- Being of total degree `k` in `Tot(M|V)` is a local property. -/
theorem car_mem_totDeg_of_local (M : CohesiveModule S.𝒜X) {V : Opens X}
    (y : S.TotSec M (le_top : V ≤ ⊤)) (k : ℤ)
    (h : ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧
      S.totRes M le_top hW y ∈ totDeg (S.D.𝒜 W) (M.baseChange (S.D.res (hW.trans le_top))).Q k) :
    y ∈ totDeg (S.D.𝒜 V) (M.baseChange (S.D.res (le_top : V ≤ ⊤))).Q k := by
  obtain ⟨F⟩ := HomRetract.exists_frm S.𝒜X M
  rw [← HomRetract.rTot_iTot (S.D.res (le_top : V ≤ ⊤)) F y]
  refine HomRetract.rTot_mem _ F fun pj => ?_
  refine S.degree_local (k - pj.1) _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hmem⟩ := h x hx
  refine ⟨W, hW, hxW, ?_⟩
  have := HomRetract.iTot_mem _ F hmem pj
  exact (congrArg (· ∈ S.D.𝒜 W (k - pj.1))
    (HomRetract.iTot_bcTotRes _ F (S.D.res hW) _ (S.D.res_comp le_top hW) y pj)).mp this

end DgaSheafData

end Cohesive
