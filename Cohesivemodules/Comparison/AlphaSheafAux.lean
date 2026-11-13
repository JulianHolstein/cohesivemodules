import Cohesivemodules.Comparison.AlphaDef
import Cohesivemodules.Comparison.HomSheafRetract
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

set_option linter.style.header false

/-!
# C1.a helpers: `α(M)^n` is a retract of a finite product of the sheaves `𝒜^q`

Private helpers for `Comparison/AlphaSheaf.lean`. The retract data (`Frm`, `iTot`, `rTot`,
`glue_of_retract`) are those of `Comparison/HomSheafRetract.lean` (namespace `HomRetract`).
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum HomRetract

open CategoryTheory Opposite TopologicalSpace

section Sheaf

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X)

/-- Gluing of degree-`q` sections (`P.glue` and `P.degree_local`). -/
private theorem glue_piece' (q : ℤ) {ι : Type} (U : ι → Opens X)
    (a : ∀ i, ↥(P.D.𝒜 (U i) q))
    (h : ∀ i j, P.D.res (inf_le_left : U i ⊓ U j ≤ U i) (a i : P.D.A (U i)) =
      P.D.res (inf_le_right : U i ⊓ U j ≤ U j) (a j : P.D.A (U j))) :
    ∃! b : ↥(P.D.𝒜 (⨆ i, U i) q),
      ∀ i, P.D.res (le_iSup U i) (b : P.D.A (⨆ i, U i)) = (a i : P.D.A (U i)) := by
  obtain ⟨b, hb, hb'⟩ := P.glue U (fun i => (a i : P.D.A (U i))) h
  have hmem : b ∈ P.D.𝒜 (⨆ i, U i) q := by
    refine P.degree_local q b fun x hx => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    exact ⟨U i, le_iSup U i, hi, by rw [hb i]; exact (a i).2⟩
  exact ⟨⟨b, hmem⟩, hb, fun b'' hb'' => Subtype.ext (hb' _ hb'')⟩

/-- Gluing in a product of the pieces `𝒜^{q_j}`. -/
private theorem glue_pi (J : Type) (q : J → ℤ) {ι : Type} (U : ι → Opens X)
    (s : ∀ a, ∀ j, ↥(P.D.𝒜 (U a) (q j)))
    (h : ∀ a b j, P.D.res (inf_le_left : U a ⊓ U b ≤ U a) (s a j : P.D.A (U a)) =
      P.D.res (inf_le_right : U a ⊓ U b ≤ U b) (s b j : P.D.A (U b))) :
    ∃! t : ∀ j, ↥(P.D.𝒜 (⨆ a, U a) (q j)),
      ∀ a j, P.D.res (le_iSup U a) (t j : P.D.A (⨆ a, U a)) = (s a j : P.D.A (U a)) := by
  choose t ht hu using fun j => P.glue_piece' (q j) U (fun a => s a j) (fun a b => h a b j)
  exact ⟨t, fun a j => ht j a, fun t' ht' => funext fun j => hu j (t' j) fun a => ht' a j⟩

/-- **C1.a** (proof). `α(M)^n` is a sheaf: a retract of a finite-type product of the `𝒜^q`. -/
theorem isSheaf_sheafOfPre_aux (M : CohesiveModule P.𝒜X) (n : ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (P.sheafOfPre M n).presheaf := by
  obtain ⟨F⟩ := exists_frm P.𝒜X M
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (X := TopCat.of X) (P.sheafOfPre M n).presheaf).2 ?_
  intro ι U sf hsf
  refine glue_of_retract (Fv := fun V => P.sheafOfSec M n (le_top : V ≤ ⊤))
    (Gv := fun V => ∀ pj : F.Idx, ↥(P.D.𝒜 V (n - pj.1)))
    (fun {V W} h x => P.sheafOfRes M n le_top h x)
    (fun {V W} h y pj => ⟨P.D.res h (y pj), (P.D.res h).map_mem (y pj).2⟩)
    (fun V x pj => ⟨iTot (P.D.res le_top) F x.1 pj, iTot_mem _ F x.2 pj⟩)
    (fun V a => ⟨rTot (P.D.res le_top) F (fun pj => (a pj : P.D.A V)),
      rTot_mem _ F (fun pj => (a pj).2)⟩)
    ?_ ?_ ?_ ?_ U sf hsf
  · intro V x
    exact Subtype.ext (rTot_iTot _ F x.1)
  · intro V W h x
    funext pj
    exact Subtype.ext (iTot_bcTotRes _ F (P.D.res h) _ (P.D.res_comp le_top h) x.1 pj).symm
  · intro V W h y
    exact Subtype.ext (bcTotRes_rTot _ F (P.D.res h) _ (P.D.res_comp le_top h) _)
  · intro ι' U' s hs
    obtain ⟨t, ht, hu⟩ := P.glue_pi F.Idx (fun pj => n - pj.1) U' s
      (fun a b j => congrArg Subtype.val (congrFun (hs a b) j))
    exact ⟨t, fun a => funext fun j => Subtype.ext (ht a j),
      fun t' ht' => hu t' fun a j => congrArg Subtype.val (congrFun (ht' a) j)⟩

end PreResolvingData

end Sheaf

end Cohesive
