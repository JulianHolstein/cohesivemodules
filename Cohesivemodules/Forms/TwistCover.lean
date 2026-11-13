import Cohesivemodules.Forms.LocalFree
import Cohesivemodules.Forms.CurvedDolbeault
import Cohesivemodules.Forms.DolbeaultGrothendieck
import Mathlib.Topology.ShrinkingLemma

set_option linter.style.header false

/-!
# Z3.d: a cover with primitives (B.1–B.3)

Blueprint item Z3.d (`blueprint/blueprint-tw.md` §3 B.1–B.3; blueprint §11 v1.19). For a compact
Hausdorff complex manifold `X` and a `∂̄`-closed `h ∈ 𝒜^{0,2}(X)`: a finite cover `U_α` with
primitives `h⁰_α` of `h|U_α` and primitives `η_αβ ∈ 𝒜⁰(U_α ∩ U_β)` of `h⁰_β − h⁰_α`,
normalized (`η_αα = 0`, `η_βα = −η_αβ`, stated pointwise). Uses H1 in degrees `q = 1` and `q = 0`
(`dolbeaultGrothendieck`), compactness and the shrinking lemma.

## Deviations
* [A, Def 7.2.2] takes primitives of `h⁰_β − h⁰_α` on the double intersections of the given cover,
  which needs a cover on which closed 1-forms on double intersections are exact (implicit Leray
  hypothesis, audit a6). Here the cover is refined so that local H1 suffices (B.3).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- Helper: a union of sets covering `univ` gives `⨆ = ⊤` in `Opens X`. -/
private theorem iSup_eq_top_of_iUnion {ι : Type*} {U : ι → Opens X}
    (h : ⋃ i, (U i : Set X) = Set.univ) : ⨆ i, U i = ⊤ := by
  refine Opens.ext ?_
  rw [Opens.coe_iSup, Opens.coe_top]
  exact h

/-- Helper: a compact space is covered by finitely many of the members of a family of open
neighbourhoods. -/
private theorem exists_finite_subcover_opens [CompactSpace X] (V : X → Opens X)
    (hV : ∀ x, x ∈ V x) : ∃ t : Finset X, ⨆ a : t, V a.1 = ⊤ := by
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen.mem_nhds (hV x))
  refine ⟨t, iSup_eq_top_of_iUnion ?_⟩
  refine Set.eq_univ_of_forall fun y => ?_
  have : y ∈ ⋃ x ∈ t, (V x : Set X) := by rw [ht]; trivial
  simp only [Set.mem_iUnion] at this ⊢
  obtain ⟨x, hx, hy⟩ := this
  exact ⟨⟨x, hx⟩, hy⟩

/-- Helper (B.1): a finite cover of `X` with primitives of `h` on each member. -/
private theorem exists_cover_h0 [CompactSpace X] (h : DolbeaultClosed2 E X) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Opens X) (_ : ⨆ i, U i = ⊤)
      (h0 : ∀ α, DolbeaultAlg E (U α)) (_ : ∀ α, h0 α ∈ dolbeaultGrade E (U α) 1),
      ∀ α, GCDga.d (𝒜 := dolbeaultGrade E (U α)) (h0 α) = dolbeaultRes E le_top h.1 := by
  have key : ∀ x : X, ∃ (V : Opens X), x ∈ V ∧ ∃ η : DolbeaultAlg E V,
      η ∈ dolbeaultGrade E V 1 ∧
      GCDga.d (𝒜 := dolbeaultGrade E V) η = dolbeaultRes E le_top h.1 := by
    intro x
    have h2 : h.1 ∈ dolbeaultGrade E (⊤ : Opens X) (((1 : ℕ) : ℤ) + 1) := by
      simpa using h.2.1
    obtain ⟨V, hV, hx, η, hη, hd⟩ := dolbeaultGrothendieck E X (⊤ : Opens X) 1 x trivial
      h.1 h2 h.2.2
    exact ⟨V, hx, η, by simpa using hη, hd⟩
  choose V hxV η hη hd using key
  obtain ⟨t, ht⟩ := exists_finite_subcover_opens V hxV
  exact ⟨t, inferInstance, fun a => V a.1, ht, fun a => η a.1, fun a => hη a.1,
    fun a => hd a.1⟩

/-- Helper: `½((a − b) − (b − a)) = a − b` in any `ℂ`-module. -/
private theorem half_sub_sub_swap {M : Type*} [AddCommGroup M] [Module ℂ M] (a b : M) :
    (1 / 2 : ℂ) • (a - b - (b - a)) = a - b := by
  module

/-- Helper: pointwise value of `½(a − b)` for degree-`0` forms. -/
private theorem evalForm0_half_sub {U : Opens X} (a b : dolbeaultGrade E U 0)
    (hm : (1 / 2 : ℂ) • ((a : DolbeaultAlg E U) - b) ∈ dolbeaultGrade E U 0) (y : U) :
    evalForm0 E y ⟨(1 / 2 : ℂ) • ((a : DolbeaultAlg E U) - b), hm⟩ =
      (1 / 2) * (evalForm0 E y a - evalForm0 E y b) := by
  show coef0 E ((((1 / 2 : ℂ) • ((a : DolbeaultAlg E U) - b) : DolbeaultAlg E U) :
    U → TotFibre E) y) = _
  have h1 : (((1 / 2 : ℂ) • ((a : DolbeaultAlg E U) - b) : DolbeaultAlg E U) :
      U → TotFibre E) y = (1 / 2 : ℂ) • (((a : DolbeaultAlg E U) : U → TotFibre E) y -
        ((b : DolbeaultAlg E U) : U → TotFibre E) y) := rfl
  rw [h1, map_smul, map_sub, smul_eq_mul]
  rfl

/-- Helper: restriction `𝒜(V ∩ U) → 𝒜(U ∩ V)` along the swap of the factors. -/
private def swapRes (U V : Opens X) :
    DgaHom (dolbeaultGrade E (V ⊓ U)) (dolbeaultGrade E (U ⊓ V)) :=
  dolbeaultRes E (le_inf inf_le_right inf_le_left : U ⊓ V ≤ V ⊓ U)

/-- Helper (B.3): the antisymmetrization `½(η_αβ − η_βα|)` of primitives is a primitive. -/
private theorem symmetrize_primitives {ι : Type} (U : ι → Opens X)
    (h0 : ∀ α, DolbeaultAlg E (U α)) (η0 : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (hη0 : ∀ α β, GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β))
        ((η0 α β : dolbeaultGrade E (U α ⊓ U β) 0) : DolbeaultAlg E (U α ⊓ U β)) =
      dolbeaultRes E (inf_le_right : U α ⊓ U β ≤ U β) (h0 β) -
        dolbeaultRes E (inf_le_left : U α ⊓ U β ≤ U α) (h0 α)) :
    ∃ (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0),
      (∀ α β, GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β))
          ((η α β : dolbeaultGrade E (U α ⊓ U β) 0) : DolbeaultAlg E (U α ⊓ U β)) =
        dolbeaultRes E (inf_le_right : U α ⊓ U β ≤ U β) (h0 β) -
          dolbeaultRes E (inf_le_left : U α ⊓ U β ≤ U α) (h0 α)) ∧
      (∀ α (y : ↥(U α ⊓ U α)), evalForm0 E y (η α α) = 0) ∧
      (∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
        -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
          ↥(U α ⊓ U β)) (η α β)) := by
  have hmem : ∀ α β, (1 / 2 : ℂ) • ((η0 α β : DolbeaultAlg E (U α ⊓ U β)) -
      swapRes E (U α) (U β) (η0 β α)) ∈ dolbeaultGrade E (U α ⊓ U β) 0 := fun α β =>
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (η0 α β).2
      ((swapRes E (U α) (U β)).map_mem (η0 β α).2))
  refine ⟨fun α β => ⟨_, hmem α β⟩, ?_, ?_, ?_⟩
  · intro α β
    have e := (swapRes E (U α) (U β)).map_d (η0 β α)
    show GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β))
      ((1 / 2 : ℂ) • ((η0 α β : DolbeaultAlg E (U α ⊓ U β)) -
        swapRes E (U α) (U β) (η0 β α))) = _
    have e1 : ∀ x : DolbeaultAlg E (U α), swapRes E (U α) (U β)
        (dolbeaultRes E (inf_le_right : U β ⊓ U α ≤ U α) x) =
        dolbeaultRes E (inf_le_left : U α ⊓ U β ≤ U α) x := fun _ => rfl
    have e2 : ∀ x : DolbeaultAlg E (U β), swapRes E (U α) (U β)
        (dolbeaultRes E (inf_le_left : U β ⊓ U α ≤ U β) x) =
        dolbeaultRes E (inf_le_right : U α ⊓ U β ≤ U β) x := fun _ => rfl
    rw [map_smul, map_sub, ← e, hη0 α β, hη0 β α, map_sub, e1, e2]
    exact half_sub_sub_swap (M := DolbeaultAlg E (U α ⊓ U β)) _ _
  · intro α y
    refine (evalForm0_half_sub E (η0 α α) ((swapRes E (U α) (U α)).f0 (η0 α α)) (hmem α α) y).trans
      ?_
    have e : evalForm0 E y ((swapRes E (U α) (U α)).f0 (η0 α α)) = evalForm0 E y (η0 α α) :=
      evalForm0_res E _ _ y
    rw [e, sub_self, mul_zero]
  · intro α β y
    refine (evalForm0_half_sub E (η0 β α) ((swapRes E (U β) (U α)).f0 (η0 α β)) (hmem β α) y).trans
      ?_
    refine Eq.trans ?_ (congrArg Neg.neg (evalForm0_half_sub E (η0 α β)
      ((swapRes E (U α) (U β)).f0 (η0 β α)) (hmem α β) _).symm)
    have e1 : evalForm0 E y ((swapRes E (U β) (U α)).f0 (η0 α β)) = evalForm0 E
        (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
          ↥(U α ⊓ U β)) (η0 α β) := evalForm0_res E _ _ y
    have e2 : evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2,
          (Opens.mem_inf.1 y.2).1⟩⟩ : ↥(U α ⊓ U β)) ((swapRes E (U α) (U β)).f0 (η0 β α)) =
        evalForm0 E y (η0 β α) := evalForm0_res E _ _ _
    rw [e1, e2]
    ring

/-- Helper: restrictions compose (pointwise form of `dolbeaultRes_comp`). -/
private theorem dolbeaultRes_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (x : DolbeaultAlg E U) :
    dolbeaultRes E h₂ (dolbeaultRes E h₁ x) = dolbeaultRes E (h₂.trans h₁) x := rfl

/-- Helper: `Y` carries a degree-`0` primitive of `ω`. -/
private def HasPrim {Y : Opens X} (w : DolbeaultAlg E Y) : Prop :=
  ∃ η ∈ dolbeaultGrade E Y 0, GCDga.d (𝒜 := dolbeaultGrade E Y) η = w

/-- Helper: primitives restrict. -/
private theorem HasPrim.res {Y Y' : Opens X} (hle : Y' ≤ Y) {w : DolbeaultAlg E Y}
    (h : HasPrim E w) : HasPrim E (dolbeaultRes E hle w) := by
  obtain ⟨η, hη, hd⟩ := h
  exact ⟨dolbeaultRes E hle η, (dolbeaultRes E hle).map_mem hη,
    ((dolbeaultRes E hle).map_d η).symm.trans (congrArg _ hd)⟩

/-- Helper: on an open with no points every form has the primitive `0`. -/
private theorem HasPrim.of_empty {Y : Opens X} (hY : Y = ⊥) (w : DolbeaultAlg E Y) :
    HasPrim E w := by
  have : IsEmpty ↥Y := ⟨fun y => absurd (hY.le y.2) (Set.notMem_empty (y : X))⟩
  have hs : Subsingleton (DolbeaultAlg E Y) := inferInstance
  exact ⟨0, Submodule.zero_mem _, hs.elim _ _⟩

/-- Helper: `ω_αβ = h⁰_β| − h⁰_α|` on `U_α ∩ U_β`. -/
private def omegaAB {ι : Type} (U : ι → Opens X) (h0 : ∀ α, DolbeaultAlg E (U α)) (a b : ι) :
    DolbeaultAlg E (U a ⊓ U b) :=
  dolbeaultRes E (inf_le_right : U a ⊓ U b ≤ U b) (h0 b) -
    dolbeaultRes E (inf_le_left : U a ⊓ U b ≤ U a) (h0 a)

/-- Helper (B.2): `ω_αβ` is a `∂̄`-closed form of degree `1`. -/
private theorem omegaAB_closed {ι : Type} (h : DolbeaultClosed2 E X) (U : ι → Opens X)
    (h0 : ∀ α, DolbeaultAlg E (U α)) (hm : ∀ α, h0 α ∈ dolbeaultGrade E (U α) 1)
    (hd : ∀ α, GCDga.d (𝒜 := dolbeaultGrade E (U α)) (h0 α) = dolbeaultRes E le_top h.1)
    (a b : ι) : omegaAB E U h0 a b ∈ dolbeaultGrade E (U a ⊓ U b) 1 ∧
      GCDga.d (𝒜 := dolbeaultGrade E (U a ⊓ U b)) (omegaAB E U h0 a b) = 0 := by
  refine ⟨Submodule.sub_mem _
    ((dolbeaultRes E (inf_le_right : U a ⊓ U b ≤ U b)).map_mem (hm b))
    ((dolbeaultRes E (inf_le_left : U a ⊓ U b ≤ U a)).map_mem (hm a)), ?_⟩
  unfold omegaAB
  rw [map_sub, ← (dolbeaultRes E (inf_le_right : U a ⊓ U b ≤ U b)).map_d,
    ← (dolbeaultRes E (inf_le_left : U a ⊓ U b ≤ U a)).map_d, hd a, hd b]
  exact sub_self _

/-- Helper (B.3): on `W`, the triple intersection with `V_α ∩ V_β` is empty or `ω_αβ` has a
primitive there. -/
private def PairGood {ι : Type} (U V : ι → Opens X) (h0 : ∀ α, DolbeaultAlg E (U α)) (a b : ι)
    (W : Opens X) : Prop :=
  W ⊓ V a ⊓ V b = ⊥ ∨ ∃ hle : W ⊓ V a ⊓ V b ≤ U a ⊓ U b,
    HasPrim E (dolbeaultRes E hle (omegaAB E U h0 a b))

/-- Helper: `PairGood` passes to smaller opens. -/
private theorem PairGood.mono {ι : Type} {U V : ι → Opens X} {h0 : ∀ α, DolbeaultAlg E (U α)}
    {a b : ι} {W W' : Opens X} (hle : W' ≤ W) (hg : PairGood E U V h0 a b W) :
    PairGood E U V h0 a b W' := by
  have hm : W' ⊓ V a ⊓ V b ≤ W ⊓ V a ⊓ V b := inf_le_inf_right _ (inf_le_inf_right _ hle)
  rcases hg with h | ⟨h1, hp⟩
  · exact Or.inl (le_bot_iff.1 (hm.trans h.le))
  · exact Or.inr ⟨hm.trans h1, HasPrim.res E hm hp⟩

/-- Helper (B.3): every point has an open neighbourhood that is good for the pair `(α, β)`. -/
private theorem exists_nbhd_pair {ι : Type} (h : DolbeaultClosed2 E X) (U V : ι → Opens X)
    (h0 : ∀ α, DolbeaultAlg E (U α)) (hm : ∀ α, h0 α ∈ dolbeaultGrade E (U α) 1)
    (hd : ∀ α, GCDga.d (𝒜 := dolbeaultGrade E (U α)) (h0 α) = dolbeaultRes E le_top h.1)
    (hcl : ∀ a, closure (V a : Set X) ⊆ U a) (a b : ι) (x : X) :
    ∃ W : Opens X, x ∈ W ∧ PairGood E U V h0 a b W := by
  by_cases hx : x ∈ closure (V a : Set X) ∩ closure (V b : Set X)
  · have hxU : x ∈ U a ⊓ U b := Opens.mem_inf.2 ⟨hcl a hx.1, hcl b hx.2⟩
    have hc := omegaAB_closed E h U h0 hm hd a b
    obtain ⟨U', hle, hxU', η, hη, hd'⟩ := dolbeaultGrothendieck E X (U a ⊓ U b) 0 x hxU
      (omegaAB E U h0 a b) (by simpa using hc.1) hc.2
    have h1 : U' ⊓ V a ⊓ V b ≤ U' := inf_le_left.trans inf_le_left
    exact ⟨U', hxU', Or.inr ⟨h1.trans hle, HasPrim.res E h1 ⟨η, hη, hd'⟩⟩⟩
  · refine ⟨⟨(closure (V a : Set X) ∩ closure (V b : Set X))ᶜ,
      (isClosed_closure.inter isClosed_closure).isOpen_compl⟩, hx, Or.inl ?_⟩
    refine eq_bot_iff.2 fun y hy => ?_
    exact absurd ⟨subset_closure hy.1.2, subset_closure hy.2⟩ hy.1.1

/-- Helper (B.3): every point has an open neighbourhood good for all pairs. -/
private theorem exists_nbhd_good {ι : Type} [Fintype ι] (h : DolbeaultClosed2 E X)
    (U V : ι → Opens X) (h0 : ∀ α, DolbeaultAlg E (U α))
    (hm : ∀ α, h0 α ∈ dolbeaultGrade E (U α) 1)
    (hd : ∀ α, GCDga.d (𝒜 := dolbeaultGrade E (U α)) (h0 α) = dolbeaultRes E le_top h.1)
    (hcl : ∀ a, closure (V a : Set X) ⊆ U a) (x : X) :
    ∃ W : Opens X, x ∈ W ∧ ∀ a b, PairGood E U V h0 a b W := by
  choose Wp hxW hW using fun p : ι × ι => exists_nbhd_pair E h U V h0 hm hd hcl p.1 p.2 x
  refine ⟨⨅ p, Wp p, ?_, fun a b => PairGood.mono E (iInf_le _ (a, b)) (hW (a, b))⟩
  have : x ∈ (↑(⨅ p, Wp p) : Set X) := by
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.2 hxW
  exact this

/-- Helper (B.3): a good `W` gives primitives of `h⁰_β − h⁰_α` on every `Y ⊆ W ∩ V_α ∩ V_β`. -/
private theorem hasPrim_of_good {ι : Type} {U V : ι → Opens X} {h0 : ∀ α, DolbeaultAlg E (U α)}
    {a b : ι} {W : Opens X} (hg : PairGood E U V h0 a b W) (Y : Opens X)
    (hY : Y ≤ W ⊓ V a ⊓ V b) (hYa : Y ≤ U a) (hYb : Y ≤ U b) :
    HasPrim E (dolbeaultRes E hYb (h0 b) - dolbeaultRes E hYa (h0 a)) := by
  rcases hg with h | ⟨hle, hp⟩
  · exact HasPrim.of_empty E (le_bot_iff.1 (hY.trans h.le)) _
  · have e : dolbeaultRes E hY (dolbeaultRes E hle (omegaAB E U h0 a b)) =
        dolbeaultRes E hYb (h0 b) - dolbeaultRes E hYa (h0 a) := by
      unfold omegaAB
      rw [map_sub, map_sub]
      rfl
    exact e ▸ HasPrim.res E hY hp

/-- Helper (B.3): a finite cover with primitives `h⁰_α` and (unnormalized) primitives `η_αβ`. -/
private theorem exists_cover_prim0 [T2Space X] [CompactSpace X] (h : DolbeaultClosed2 E X) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Opens X) (_ : ⨆ i, U i = ⊤)
      (h0 : ∀ α, DolbeaultAlg E (U α)) (_ : ∀ α, h0 α ∈ dolbeaultGrade E (U α) 1)
      (_ : ∀ α, GCDga.d (𝒜 := dolbeaultGrade E (U α)) (h0 α) = dolbeaultRes E le_top h.1),
      ∀ α β, HasPrim E (dolbeaultRes E (inf_le_right : U α ⊓ U β ≤ U β) (h0 β) -
        dolbeaultRes E (inf_le_left : U α ⊓ U β ≤ U α) (h0 α)) := by
  obtain ⟨ι₀, _, U₀, hU₀, h0₀, hm₀, hd₀⟩ := exists_cover_h0 E h
  have hcov : ⋃ a, (U₀ a : Set X) = Set.univ := by
    have := congrArg (fun s : Opens X => (s : Set X)) hU₀
    simpa only [Opens.coe_iSup, Opens.coe_top] using this
  obtain ⟨v, hv, hvo, hvcl⟩ := exists_iUnion_eq_closure_subset (u := fun a => (U₀ a : Set X))
    (fun a => (U₀ a).isOpen) (fun x => Set.toFinite _) hcov
  let V : ι₀ → Opens X := fun a => ⟨v a, hvo a⟩
  have hcl : ∀ a, closure (V a : Set X) ⊆ U₀ a := hvcl
  have hVU : ∀ a, V a ≤ U₀ a := fun a => subset_closure.trans (hcl a)
  have hVtop : ⨆ a, V a = ⊤ := iSup_eq_top_of_iUnion hv
  choose W hxW hW using exists_nbhd_good E h U₀ V h0₀ hm₀ hd₀ hcl
  obtain ⟨t, ht⟩ := exists_finite_subcover_opens W hxW
  have hle : ∀ p : ι₀ × t, V p.1 ⊓ W p.2.1 ≤ U₀ p.1 := fun p => inf_le_left.trans (hVU p.1)
  refine ⟨ι₀ × t, inferInstance, fun p => V p.1 ⊓ W p.2.1, ?_,
    fun p => dolbeaultRes E (hle p) (h0₀ p.1),
    fun p => (dolbeaultRes E (hle p)).map_mem (hm₀ p.1),
    fun p => (((dolbeaultRes E (hle p)).map_d (h0₀ p.1)).symm.trans
      (congrArg (dolbeaultRes E (hle p)).toAlgHom (hd₀ p.1))).trans
      (dolbeaultRes_res E _ _ _), ?_⟩
  · refine iSup_eq_top_of_iUnion (Set.eq_univ_of_forall fun y => ?_)
    have hy1 : y ∈ (⨆ a, V a : Opens X) := by rw [hVtop]; trivial
    have hy2 : y ∈ (⨆ a : t, W a.1 : Opens X) := by rw [ht]; trivial
    obtain ⟨a, hya⟩ := Opens.mem_iSup.1 hy1
    obtain ⟨j, hyj⟩ := Opens.mem_iSup.1 hy2
    exact Set.mem_iUnion.2 ⟨(a, j), Opens.mem_inf.2 ⟨hya, hyj⟩⟩
  · intro p q
    exact hasPrim_of_good E (hW p.2.1 p.1 q.1) _
      (le_inf (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))
        (inf_le_right.trans inf_le_left))
      ((inf_le_left.trans inf_le_left).trans (hVU _))
      ((inf_le_right.trans inf_le_left).trans (hVU _))

/-- Helper (B.3): `symmetrize_primitives` for primitives given as plain forms. -/
private theorem symmetrize_primitives_raw {ι : Type} (U : ι → Opens X)
    (h0 : ∀ α, DolbeaultAlg E (U α)) (η0 : ∀ α β, DolbeaultAlg E (U α ⊓ U β))
    (hη0m : ∀ α β, η0 α β ∈ dolbeaultGrade E (U α ⊓ U β) 0)
    (hη0 : ∀ α β, GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β)) (η0 α β) =
      dolbeaultRes E (inf_le_right : U α ⊓ U β ≤ U β) (h0 β) -
        dolbeaultRes E (inf_le_left : U α ⊓ U β ≤ U α) (h0 α)) :
    ∃ (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0),
      (∀ α β, GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β))
          ((η α β : dolbeaultGrade E (U α ⊓ U β) 0) : DolbeaultAlg E (U α ⊓ U β)) =
        dolbeaultRes E (inf_le_right : U α ⊓ U β ≤ U β) (h0 β) -
          dolbeaultRes E (inf_le_left : U α ⊓ U β ≤ U α) (h0 α)) ∧
      (∀ α (y : ↥(U α ⊓ U α)), evalForm0 E y (η α α) = 0) ∧
      (∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
        -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
          ↥(U α ⊓ U β)) (η α β)) :=
  symmetrize_primitives E U h0 (fun α β => ⟨η0 α β, hη0m α β⟩) hη0

/-- **Z3.d (B.1–B.3).** A finite open cover `U_α` of `X` with primitives `h⁰_α ∈ 𝒜¹(U_α)` of
`h|U_α` and primitives `η_αβ ∈ 𝒜⁰(U_α ∩ U_β)` of `h⁰_β − h⁰_α`, normalized: `η_αα = 0` and
`η_βα = −η_αβ`, both pointwise (`evalForm0`). -/
theorem exists_cover_primitives [T2Space X] [CompactSpace X] (h : DolbeaultClosed2 E X) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Opens X) (_ : ⨆ i, U i = ⊤)
      (h0 : ∀ α, DolbeaultAlg E (U α)) (_ : ∀ α, h0 α ∈ dolbeaultGrade E (U α) 1)
      (_ : ∀ α, GCDga.d (𝒜 := dolbeaultGrade E (U α)) (h0 α) = dolbeaultRes E le_top h.1)
      (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0),
      (∀ α β, GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β))
          ((η α β : dolbeaultGrade E (U α ⊓ U β) 0) : DolbeaultAlg E (U α ⊓ U β)) =
        dolbeaultRes E inf_le_right (h0 β) - dolbeaultRes E inf_le_left (h0 α)) ∧
      (∀ α (y : ↥(U α ⊓ U α)), evalForm0 E y (η α α) = 0) ∧
      (∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
        -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
          ↥(U α ⊓ U β)) (η α β)) := by
  have key := exists_cover_prim0 E h
  cases key with | intro ι key =>
  cases key with | intro hι key =>
  cases key with | intro U key =>
  cases key with | intro hU key =>
  cases key with | intro h0 key =>
  cases key with | intro hm key =>
  cases key with | intro hd hP =>
  choose η0 hη0m hη0 using hP
  exact ⟨ι, hι, U, hU, h0, hm, hd, symmetrize_primitives_raw E U h0 η0 hη0m hη0⟩

end Cohesive
