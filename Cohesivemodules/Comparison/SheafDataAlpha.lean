-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Comparison.SheafDataAlphaDef
import Cohesivemodules.Comparison.HomSheafRetract
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

set_option linter.style.header false

/-!
# Z3.m: `α(M)^n` over `DgaSheafData` is a sheaf (copy of C1.a)

Blueprint item Z3.m (`blueprint/blueprint-tw.md` §2.4, D11). The proof of C1.a
(`Comparison/AlphaSheafAux.lean`, `AlphaSheaf.lean`) word for word over `S : DgaSheafData X`:
`α(M)^n` is a retract of a finite product of the sheaves `𝒜^q` (neither the curvature nor
fineness nor local freeness is used). Then:
* `S.sheafOfSh M n : Mod S.R`, the sheaf `α(M)^n` (copy of C1 `sheafOfSh`);
* `S.sheafOfX M n : α(M)^n ⟶ α(M)^{n+1}`, the operator `𝕏` on sections (copy of C1 `sheafOfD`,
  ⚠ not a differential for curved data).
-/

noncomputable section

namespace Cohesive

open TensorProduct DirectSum HomRetract

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace DgaSheafData

variable (S : DgaSheafData X)

/-- Gluing of degree-`q` sections (`S.glue` and `S.degree_local`). -/
private theorem glue_piece' (q : ℤ) {ι : Type} (U : ι → Opens X)
    (a : ∀ i, ↥(S.D.𝒜 (U i) q))
    (h : ∀ i j, S.D.res (inf_le_left : U i ⊓ U j ≤ U i) (a i : S.D.A (U i)) =
      S.D.res (inf_le_right : U i ⊓ U j ≤ U j) (a j : S.D.A (U j))) :
    ∃! b : ↥(S.D.𝒜 (⨆ i, U i) q),
      ∀ i, S.D.res (le_iSup U i) (b : S.D.A (⨆ i, U i)) = (a i : S.D.A (U i)) := by
  obtain ⟨b, hb, hb'⟩ := S.glue U (fun i => (a i : S.D.A (U i))) h
  have hmem : b ∈ S.D.𝒜 (⨆ i, U i) q := by
    refine S.degree_local q b fun x hx => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    exact ⟨U i, le_iSup U i, hi, by rw [hb i]; exact (a i).2⟩
  exact ⟨⟨b, hmem⟩, hb, fun b'' hb'' => Subtype.ext (hb' _ hb'')⟩

/-- Gluing in a product of the pieces `𝒜^{q_j}`. -/
private theorem glue_pi (J : Type) (q : J → ℤ) {ι : Type} (U : ι → Opens X)
    (s : ∀ a, ∀ j, ↥(S.D.𝒜 (U a) (q j)))
    (h : ∀ a b j, S.D.res (inf_le_left : U a ⊓ U b ≤ U a) (s a j : S.D.A (U a)) =
      S.D.res (inf_le_right : U a ⊓ U b ≤ U b) (s b j : S.D.A (U b))) :
    ∃! t : ∀ j, ↥(S.D.𝒜 (⨆ a, U a) (q j)),
      ∀ a j, S.D.res (le_iSup U a) (t j : S.D.A (⨆ a, U a)) = (s a j : S.D.A (U a)) := by
  choose t ht hu using fun j => S.glue_piece' (q j) U (fun a => s a j) (fun a b => h a b j)
  exact ⟨t, fun a j => ht j a, fun t' ht' => funext fun j => hu j (t' j) fun a => ht' a j⟩

variable (M : CohesiveModule S.𝒜X)

/-- **Z3.m** (copy of C1.a). `α(M)^n` is a sheaf: a retract of a finite-type product of the
`𝒜^q`. [B, §4.1], [A, Lemma 7.2.7 (proof)]. -/
theorem isSheaf_sheafOfPre (n : ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (S.sheafOfPre M n).presheaf := by
  obtain ⟨F⟩ := exists_frm S.𝒜X M
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (X := TopCat.of X) (S.sheafOfPre M n).presheaf).2 ?_
  intro ι U sf hsf
  refine glue_of_retract (Fv := fun V => S.sheafOfSec M n (le_top : V ≤ ⊤))
    (Gv := fun V => ∀ pj : F.Idx, ↥(S.D.𝒜 V (n - pj.1)))
    (fun {V W} h x => S.sheafOfRes M n le_top h x)
    (fun {V W} h y pj => ⟨S.D.res h (y pj), (S.D.res h).map_mem (y pj).2⟩)
    (fun V x pj => ⟨iTot (S.D.res le_top) F x.1 pj, iTot_mem _ F x.2 pj⟩)
    (fun V a => ⟨rTot (S.D.res le_top) F (fun pj => (a pj : S.D.A V)),
      rTot_mem _ F (fun pj => (a pj).2)⟩)
    ?_ ?_ ?_ ?_ U sf hsf
  · intro V x
    exact Subtype.ext (rTot_iTot _ F x.1)
  · intro V W h x
    funext pj
    exact Subtype.ext (iTot_bcTotRes _ F (S.D.res h) _ (S.D.res_comp le_top h) x.1 pj).symm
  · intro V W h y
    exact Subtype.ext (bcTotRes_rTot _ F (S.D.res h) _ (S.D.res_comp le_top h) _)
  · intro ι' U' s hs
    obtain ⟨t, ht, hu⟩ := S.glue_pi F.Idx (fun pj => n - pj.1) U' s
      (fun a b j => congrArg Subtype.val (congrFun (hs a b) j))
    exact ⟨t, fun a => funext fun j => Subtype.ext (ht a j),
      fun t' ht' => hu t' fun a j => congrArg Subtype.val (congrFun (ht' a) j)⟩

/-- **Z3.m** (copy of C1 `sheafOfSh`). The sheaf of `O`-modules `α(M)^n`. -/
def sheafOfSh (n : ℤ) : Mod S.R := ⟨S.sheafOfPre M n, S.isSheaf_sheafOfPre M n⟩

/-- **Z3.m** (copy of C1 `sheafOfD`). The operator `α(M)^n ⟶ α(M)^{n+1}`: `𝕏` of `M|V` on
sections over `V`. ⚠ For curved data `𝕏² = c·`, so this is not a differential. -/
def sheafOfX (n : ℤ) : S.sheafOfSh M n ⟶ S.sheafOfSh M (n + 1) :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (S.sheafOfDV M n (le_top : V.unop ≤ ⊤))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact S.X_totRes M le_top (leOfHom f.unop) x.1 }⟩

/-- Sections of `α(M)^n` over `V` (rfl). -/
theorem sheafOfSh_obj (n : ℤ) (V : Opens X) :
    (S.sheafOfSh M n).val.obj (op V) =
      ModuleCat.of (S.O.obj.obj (op V)) (S.sheafOfSec M n (le_top : V ≤ ⊤)) :=
  rfl

/-- `sheafOfX` on sections is `sheafOfDV` (rfl). -/
theorem sheafOfX_app (n : ℤ) (V : Opens X) (x : S.sheafOfSec M n (le_top : V ≤ ⊤)) :
    ((S.sheafOfX M n).val.app (op V)).hom x = S.sheafOfDV M n le_top x :=
  rfl

end DgaSheafData

end Cohesive
