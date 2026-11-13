import Cohesivemodules.Sheaf.Restriction
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Algebra.Homology.Embedding.CochainComplex

set_option linter.style.header false

/-!
# S3.b: soft sheaves

Blueprint item S3.b (§3, added in v1.7). On a compact Hausdorff space, Γ of a bounded-below
acyclic complex of sheaves of `R`-modules with soft terms is acyclic, with no sheaf cohomology.
This replaces [A, Lemma 7.2.8] (Γ-acyclic terms, [Stacks, Tag 015E]) in C4 step 4, where the
terms are `𝒜⁰`-modules but the differentials are not `𝒜⁰`-linear, so S3 does not apply.

* `IsSoft M`: stalk-free softness. A section over an open neighbourhood `U` of a closed set `K`
  agrees, on a smaller open neighbourhood of `K`, with a global section.
* S3.b(i) `IsSoft.of_action`: the global sections of a fine sheaf of rings acting on `M` by
  sheaf endomorphisms (additively, unitally, locally) make `M` soft; in particular modules over
  a fine commutative sheaf of rings are soft (`isSoft_of_isFine`).
* S3.b(ii) `surjective_globalSections_of_isSoft`: for `0 → A → B → C → 0` exact with `A` soft,
  `Γ(B) → Γ(C)` is surjective (compact Hausdorff `X`).
* S3.b(iii) `IsSoft.of_shortExact`: `A`, `B` soft ⇒ `C` soft.
* S3.b(iv) `acyclic_globalSections_of_isSoft`, `quasiIso_globalSections_of_isSoft`.

## Deviations
* Softness is defined without stalks or sections over closed sets: sections near `K` are
  sections over open neighbourhoods of `K`. On compact Hausdorff (hence paracompact) `X` this
  is the usual notion ([Bredon, II.9]).
* S3.b(i) asks only for an additive, unital and local action of the global sections; this is
  what the proof uses, and what the `𝒜⁰`-action on Hom sheaves through the source provides.

Part 1 of 2 of the original `Sheaf/Soft.lean`, split for size; continued in
`Sheaf/Soft.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

/-- **S3.b. Soft sheaves** (stalk-free). For every closed `K`, open `U ⊇ K` and section `s` of
`M` over `U`, there are a global section `t` and an open `V` with `K ⊆ V ⊆ U` on which `t` and
`s` agree. -/
def IsSoft (M : Mod R) : Prop :=
  ∀ (K : Set X), IsClosed K → ∀ (U : Opens X), K ⊆ U → ∀ s : M.val.obj (op U),
    ∃ (t : M.val.obj (op ⊤)) (V : Opens X) (hVU : V ≤ U),
      K ⊆ V ∧ mres M (le_top : V ≤ ⊤) t = mres M hVU s

/-- Restricting twice. -/
private lemma mres_mres {M : Mod R} {U V W : Opens X} (h1 : V ≤ U) (h2 : W ≤ V)
    (s : M.val.obj (op U)) : mres M h2 (mres M h1 s) = mres M (h2.trans h1) s :=
  (M.val.map_comp_apply (homOfLE h1).op (homOfLE h2).op s).symm

/-- Restriction is additive. -/
private lemma mres_add {M : Mod R} {U V : Opens X} (h : V ≤ U) (s t : M.val.obj (op U)) :
    mres M h (s + t) = mres M h s + mres M h t :=
  map_add _ _ _

/-- Restriction is compatible with subtraction. -/
private lemma mres_sub {M : Mod R} {U V : Opens X} (h : V ≤ U) (s t : M.val.obj (op U)) :
    mres M h (s - t) = mres M h s - mres M h t :=
  map_sub _ _ _

/-- Naturality of a morphism of sheaves of modules with respect to restriction. -/
private lemma mres_map {M N : Mod R} (φ : M ⟶ N) {U V : Opens X} (h : V ≤ U)
    (s : M.val.obj (op U)) :
    φ.val.app (op V) (mres M h s) = mres N h (φ.val.app (op U) s) :=
  congr(ModuleCat.Hom.hom $(φ.val.naturality (homOfLE h).op) s)

/-- Restriction is compatible with scalar multiplication. -/
private lemma mres_smul {M : Mod R} {U V : Opens X} (h : V ≤ U) (r : R.obj.obj (op U))
    (t : M.val.obj (op U)) : mres M h (r • t) = rres R h r • mres M h t :=
  M.val.map_smul _ r t

/-- Restriction of ring sections twice. -/
private lemma rres_rres' {U V W : Opens X} (h1 : V ≤ U) (h2 : W ≤ V) (r : R.obj.obj (op U)) :
    rres R h2 (rres R h1 r) = rres R (h2.trans h1) r := by
  change (R.obj.map (homOfLE h2).op).hom ((R.obj.map (homOfLE h1).op).hom r) = _
  rw [← RingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The underlying sheaf of abelian groups of `M`, as a `TopCat` sheaf. -/
private def topSheaf (M : Mod R) : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of X) :=
  ⟨M.val.presheaf, M.isSheaf⟩

/-- Locality for a cover of `V` by two opens. -/
private lemma eq_of_cover₂ {M : Mod R} {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V)
    (hV : V ≤ A ⊔ B) (s s' : M.val.obj (op V)) (h1 : mres M hA s = mres M hA s')
    (h2 : mres M hB s = mres M hB s') : s = s' :=
  TopCat.Sheaf.eq_of_locally_eq₂ (topSheaf M) (homOfLE hA) (homOfLE hB) hV s s' h1 h2

/-- Gluing for a cover of `V` by two opens. -/
private lemma exists_glue₂ {M : Mod R} {V A B : Opens X} (hA : A ≤ V) (hB : B ≤ V)
    (hV : V ≤ A ⊔ B) (a : M.val.obj (op A)) (b : M.val.obj (op B))
    (h : mres M (inf_le_left : A ⊓ B ≤ A) a = mres M (inf_le_right : A ⊓ B ≤ B) b) :
    ∃ s : M.val.obj (op V), mres M hA s = a ∧ mres M hB s = b := by
  let U : Bool → Opens X := fun t => cond t A B
  let sf : ∀ i : Bool, (topSheaf M).1.obj (op (U i)) :=
    Bool.rec (motive := fun t => (topSheaf M).1.obj (op (U t))) b a
  have hc : TopCat.Presheaf.IsCompatible (topSheaf M).1 U sf := by
    rintro (i|i) (j|j)
    · rfl
    · have h' := congrArg (mres M (inf_comm B A).le) h
      rw [mres_mres, mres_mres] at h'
      exact h'.symm
    · exact h
    · rfl
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (topSheaf M) U V
    (fun i => Bool.rec (motive := fun t => U t ⟶ V) (homOfLE hB) (homOfLE hA) i)
    (by
      refine le_trans hV (sup_le ?_ ?_)
      · exact le_iSup U true
      · exact le_iSup U false) sf hc
  exact ⟨s, hs true, hs false⟩

/-- Sections over the empty open set are unique. -/
private lemma subsingleton_bot (M : Mod R) : Subsingleton (M.val.obj (op (⊥ : Opens X))) :=
  ⟨fun s t => TopCat.Sheaf.eq_of_locally_eq' (topSheaf M) (fun i : Empty => i.elim) ⊥
    (fun i => i.elim) bot_le s t (fun i => i.elim)⟩

/-- **S3.b(i).** If the global sections of a fine sheaf of rings `S` act on `M` by sheaf
endomorphisms, additively, with `1` acting as the identity and `ρ` acting as `0` on every open
where `ρ` vanishes, then `M` is soft: for `K ⊆ U`, take a partition of unity `ρ₁ + ρ₂ = 1` for
the cover `{U, X ∖ K}`; `ρ₁ • s` extends by zero, and equals `s` near `K`. -/
theorem IsSoft.of_action {S : RingSheaf X} (hS : IsFine S) (M : Mod R)
    (act : S.obj.obj (op ⊤) →+ (M ⟶ M)) (h1 : act 1 = 𝟙 M)
    (hloc : ∀ (ρ : S.obj.obj (op ⊤)) (V : Opens X), rres S (le_top : V ≤ ⊤) ρ = 0 →
      (act ρ).val.app (op V) = 0) :
    IsSoft M := by
  intro K hK U hKU s
  let Uc : Opens X := ⟨Kᶜ, hK.isOpen_compl⟩
  obtain ⟨ρ, hsum, hρ⟩ := hS Bool (fun b => cond b U Uc) (by
    refine top_unique fun x _ => ?_
    by_cases hx : x ∈ K
    · exact Opens.mem_iSup.2 ⟨true, hKU hx⟩
    · exact Opens.mem_iSup.2 ⟨false, hx⟩)
  obtain ⟨W₁, hW₁, hρ₁⟩ := hρ true
  obtain ⟨W₂, hW₂, hρ₂⟩ := hρ false
  have hW₂' : Uc ⊔ W₂ = ⊤ := hW₂
  have hsum' : ρ true + ρ false = 1 := by
    rw [← hsum, Fintype.sum_bool]
  have hKW₂ : K ⊆ W₂ := by
    intro x hx
    have hx' : x ∈ (Uc ⊔ W₂ : Opens X) := by rw [hW₂']; trivial
    rcases Opens.mem_sup.1 hx' with h | h
    · exact absurd hx h
    · exact h
  have hzero : ∀ (r : S.obj.obj (op ⊤)) (W V : Opens X), rres S (le_top : W ≤ ⊤) r = 0 →
      V ≤ W → rres S (le_top : V ≤ ⊤) r = 0 := by
    intro r W V hr hV
    have := rres_rres' (R := S) (le_top : W ≤ ⊤) hV r
    rw [hr, map_zero] at this
    exact this.symm
  have hloc' : ∀ (r : S.obj.obj (op ⊤)) (V : Opens X), rres S (le_top : V ≤ ⊤) r = 0 →
      ∀ m, (act r).val.app (op V) m = 0 := by
    intro r V h m
    rw [hloc r V h]
    rfl
  have hφ : ∀ (V : Opens X) (m : M.val.obj (op V)),
      (act (ρ true)).val.app (op V) m + (act (ρ false)).val.app (op V) m = m := by
    intro V m
    have h : act (ρ true) + act (ρ false) = 𝟙 M := by rw [← map_add, hsum', h1]
    exact congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op V)) h)) m)
  have hglue := exists_glue₂ (M := M) (le_top : U ≤ ⊤) (le_top : W₁ ≤ ⊤) hW₁.ge
    ((act (ρ true)).val.app (op U) s) 0 (by
      rw [← mres_map, hloc' (ρ true) (U ⊓ W₁) (hzero _ W₁ _ hρ₁ inf_le_right)]
      exact (map_zero _).symm)
  obtain ⟨t, ht, -⟩ := hglue
  refine ⟨t, U ⊓ W₂, inf_le_left, fun x hx => ⟨hKU hx, hKW₂ hx⟩, ?_⟩
  have h2 := hloc' (ρ false) (U ⊓ W₂) (hzero _ W₂ _ hρ₂ inf_le_right)
    (mres M (inf_le_left : U ⊓ W₂ ≤ U) s)
  have h3 := hφ (U ⊓ W₂) (mres M (inf_le_left : U ⊓ W₂ ≤ U) s)
  rw [h2, add_zero, mres_map] at h3
  rw [← h3, ← ht, mres_mres]

/-- Multiplication by a global section `r` of a commutative sheaf of rings, as an endomorphism
of `M`. -/
private def smulHom (hc : IsComm R) (M : Mod R) (r : R.obj.obj (op ⊤)) : M ⟶ M :=
  ⟨{ app := fun V => ModuleCat.ofHom
        { toFun := fun m => rres R (le_top : V.unop ≤ ⊤) r • m
          map_add' := fun a b => smul_add _ a b
          map_smul' := fun a m => by
            change _ • (a • m) = a • (_ • m)
            rw [smul_smul, smul_smul, hc] }
     naturality := by
        intro V V' g
        ext m
        change rres R (le_top : V'.unop ≤ ⊤) r • mres M g.unop.le m =
          mres M g.unop.le (rres R (le_top : V.unop ≤ ⊤) r • m)
        rw [mres_smul, rres_rres'] }⟩

/-- **S3.b(i).** Every module over a fine commutative sheaf of rings is soft (`R(X)` acts by
multiplication). -/
theorem isSoft_of_isFine (hR : IsFine R) (hc : IsComm R) (M : Mod R) : IsSoft M := by
  let act : R.obj.obj (op ⊤) →+ (M ⟶ M) :=
    { toFun := smulHom hc M
      map_zero' := by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
        ext m
        exact congrArg (· • m) (map_zero _) |>.trans (zero_smul _ m)
      map_add' := by
        intro a b
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
        ext m
        exact congrArg (· • m) (map_add _ a b) |>.trans (add_smul _ _ m) }
  refine IsSoft.of_action hR M act ?_ ?_
  · refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    ext m
    change rres R (le_top : V.unop ≤ ⊤) 1 • m = m
    rw [map_one, one_smul]
  · intro r V hr
    ext m
    change rres R (le_top : V ≤ ⊤) r • m = 0
    rw [hr, zero_smul]

/-- Zero modules are soft (non-vacuity of `IsSoft` on the trivial side). -/
theorem IsSoft.of_isZero {M : Mod R} (hM : IsZero M) : IsSoft M := by
  intro K _ U _ s
  have hz : Subsingleton (M.val.obj (op U)) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (Functor.map_isZero (SheafOfModules.evaluation.{0} R (op U)) hM)
  exact ⟨0, U, le_rfl, by assumption, hz.elim _ _⟩

/-- A section of a binary biproduct is the sum of the images of its components. -/
private lemma biprod_decomp {M N : Mod R} (V : Opens X) (s : (M ⊞ N).val.obj (op V)) :
    (biprod.inl : M ⟶ M ⊞ N).val.app (op V) ((biprod.fst : M ⊞ N ⟶ M).val.app (op V) s) +
      (biprod.inr : N ⟶ M ⊞ N).val.app (op V) ((biprod.snd : M ⊞ N ⟶ N).val.app (op V) s) =
        s :=
  congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op V)) (biprod.total (X := M)
    (Y := N)))) s)

/-- Finite direct sums of soft modules are soft (used for mapping cones). -/
theorem IsSoft.biprod {M N : Mod R} (hM : IsSoft M) (hN : IsSoft N) : IsSoft (M ⊞ N) := by
  intro K hK U hKU s
  obtain ⟨t₁, V₁, hV₁, hK₁, ht₁⟩ := hM K hK U hKU
    ((biprod.fst : M ⊞ N ⟶ M).val.app (op U) s)
  obtain ⟨t₂, V₂, hV₂, hK₂, ht₂⟩ := hN K hK U hKU
    ((biprod.snd : M ⊞ N ⟶ N).val.app (op U) s)
  have hle₁ : V₁ ⊓ V₂ ≤ V₁ := inf_le_left
  have hle₂ : V₁ ⊓ V₂ ≤ V₂ := inf_le_right
  have hVU : V₁ ⊓ V₂ ≤ U := hle₁.trans hV₁
  refine ⟨(biprod.inl : M ⟶ M ⊞ N).val.app (op ⊤) t₁ +
    (biprod.inr : N ⟶ M ⊞ N).val.app (op ⊤) t₂, V₁ ⊓ V₂, hVU, fun x hx => ⟨hK₁ hx, hK₂ hx⟩, ?_⟩
  have e1 : mres M (le_top : V₁ ⊓ V₂ ≤ ⊤) t₁ =
      (biprod.fst : M ⊞ N ⟶ M).val.app (op (V₁ ⊓ V₂)) (mres (M ⊞ N) hVU s) := by
    have := congrArg (mres M hle₁) ht₁
    rw [mres_mres, mres_mres, ← mres_map (biprod.fst : M ⊞ N ⟶ M)] at this
    exact this
  have e2 : mres N (le_top : V₁ ⊓ V₂ ≤ ⊤) t₂ =
      (biprod.snd : M ⊞ N ⟶ N).val.app (op (V₁ ⊓ V₂)) (mres (M ⊞ N) hVU s) := by
    have := congrArg (mres N hle₂) ht₂
    rw [mres_mres, mres_mres, ← mres_map (biprod.snd : M ⊞ N ⟶ N)] at this
    exact this
  have hadd : ∀ (A B : Opens X) (h : B ≤ A) (x y : (M ⊞ N).val.obj (op A)),
      mres (M ⊞ N) h (x + y) = mres (M ⊞ N) h x + mres (M ⊞ N) h y :=
    fun _ _ _ _ _ => map_add _ _ _
  rw [hadd, ← mres_map (biprod.inl : M ⟶ M ⊞ N), ← mres_map (biprod.inr : N ⟶ M ⊞ N), e1, e2]
  exact biprod_decomp _ _

/-- Soft is invariant under isomorphism. -/
theorem IsSoft.of_iso {M N : Mod R} (e : M ≅ N) (hM : IsSoft M) : IsSoft N := by
  intro K hK U hKU s
  obtain ⟨t, V, hVU, hKV, ht⟩ := hM K hK U hKU (e.inv.val.app (op U) s)
  refine ⟨e.hom.val.app (op ⊤) t, V, hVU, hKV, ?_⟩
  rw [← mres_map, ht, ← mres_map e.inv]
  exact congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op V)) e.inv_hom_id))
    (mres N hVU s))

/-- Sections of the middle term killed by `g` come from sections of the first term. -/
private lemma sections_exact {S : ShortComplex (Mod R)} (hS : S.ShortExact) (V : Opens X) :
    ∀ b : S.X₂.val.obj (op V), S.g.val.app (op V) b = 0 → ∃ a, S.f.val.app (op V) a = b := by
  have hex := hS.exact.map_of_mono_of_preservesKernel (SheafOfModules.evaluation.{0} R (op V))
    hS.mono_f inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).1 hex

/-- `g ∘ f = 0` on sections. -/
private lemma sections_zero {S : ShortComplex (Mod R)} (V : Opens X) (a : S.X₁.val.obj (op V)) :
    S.g.val.app (op V) (S.f.val.app (op V) a) = 0 :=
  congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op V)) S.zero)) a)

/-- Gluing step for lifts: lifts of `c` on neighbourhoods `O ⊇ P` and `O₂ ⊇ Q` of closed sets
combine to a lift on a neighbourhood of `P ∪ Q` (softness of `A` corrects the second lift near
`P ∩ Q`; normality separates the rest). -/
private lemma lift_union [NormalSpace X] {S : ShortComplex (Mod R)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) {U : Opens X} (c : S.X₃.val.obj (op U)) {P Q : Set X}
    (hP : IsClosed P) (hQ : IsClosed Q) {O O₂ : Opens X} (hO : O ≤ U) (hO₂ : O₂ ≤ U)
    (hPO : P ⊆ O) (hQO : Q ⊆ O₂) (b : S.X₂.val.obj (op O)) (b₂ : S.X₂.val.obj (op O₂))
    (hb : S.g.val.app (op O) b = mres S.X₃ hO c)
    (hb₂ : S.g.val.app (op O₂) b₂ = mres S.X₃ hO₂ c) :
    ∃ (O₃ : Opens X) (h : O₃ ≤ U), P ∪ Q ⊆ O₃ ∧ ∃ b₃ : S.X₂.val.obj (op O₃),
      S.g.val.app (op O₃) b₃ = mres S.X₃ h c := by
  let I : Opens X := O ⊓ O₂
  let d : S.X₂.val.obj (op I) :=
    mres S.X₂ (inf_le_left : I ≤ O) b - mres S.X₂ (inf_le_right : I ≤ O₂) b₂
  have hd : S.g.val.app (op I) d = 0 := by
    have e1 := mres_map S.g (inf_le_left : I ≤ O) b
    have e2 := mres_map S.g (inf_le_right : I ≤ O₂) b₂
    show S.g.val.app (op I) (_ - _) = 0
    rw [map_sub, e1, e2, hb, hb₂, mres_mres, mres_mres, sub_self]
  obtain ⟨a, ha⟩ := sections_exact hS I d hd
  have hLI : P ∩ Q ⊆ I := fun x hx => ⟨hPO hx.1, hQO hx.2⟩
  obtain ⟨a', V₀, hV₀I, hLV₀, ha'⟩ := hA (P ∩ Q) (hP.inter hQ) I hLI a
  let b₂' : S.X₂.val.obj (op O₂) :=
    b₂ + S.f.val.app (op O₂) (mres S.X₁ (le_top : O₂ ≤ ⊤) a')
  have hb₂' : S.g.val.app (op O₂) b₂' = mres S.X₃ hO₂ c := by
    show S.g.val.app (op O₂) (_ + _) = _
    rw [map_add, sections_zero, add_zero, hb₂]
  have hV₀O : V₀ ≤ O := hV₀I.trans inf_le_left
  have hV₀O₂ : V₀ ≤ O₂ := hV₀I.trans inf_le_right
  have hagree : mres S.X₂ hV₀O b = mres S.X₂ hV₀O₂ b₂' := by
    have h1 : mres S.X₂ hV₀O₂ b₂' =
        mres S.X₂ hV₀O₂ b₂ + S.f.val.app (op V₀) (mres S.X₁ (le_top : V₀ ≤ ⊤) a') := by
      show mres S.X₂ hV₀O₂ (_ + _) = _
      rw [mres_add, ← mres_map, mres_mres]
    have h2 : S.f.val.app (op V₀) (mres S.X₁ (le_top : V₀ ≤ ⊤) a') =
        mres S.X₂ hV₀O b - mres S.X₂ hV₀O₂ b₂ := by
      rw [ha', mres_map, ha]
      show mres S.X₂ hV₀I (_ - _) = _
      rw [mres_sub, mres_mres, mres_mres]
    rw [h1, h2]
    abel
  have hP1 : IsClosed (P \ V₀) := hP.sdiff V₀.isOpen
  have hQ1 : IsClosed (Q \ V₀) := hQ.sdiff V₀.isOpen
  have hdisj : Disjoint (P \ V₀) (Q \ V₀) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxP, hx0⟩ ⟨hxQ, -⟩
    exact hx0 (hLV₀ ⟨hxP, hxQ⟩)
  obtain ⟨u, v, hu, hv, hPu, hQv, huv⟩ := NormalSpace.normal _ _ hP1 hQ1 hdisj
  let E₁ : Opens X := O ⊓ (⟨u, hu⟩ ⊔ V₀)
  let E₂ : Opens X := O₂ ⊓ (⟨v, hv⟩ ⊔ V₀)
  have hE₁O : E₁ ≤ O := inf_le_left
  have hE₂O : E₂ ≤ O₂ := inf_le_left
  have hE12 : E₁ ⊓ E₂ ≤ V₀ := by
    intro x hx
    obtain ⟨⟨_, hx1⟩, ⟨_, hx2⟩⟩ := hx
    rcases Opens.mem_sup.1 hx1 with h1 | h1
    · rcases Opens.mem_sup.1 hx2 with h2 | h2
      · exact absurd h2 (Set.disjoint_left.1 huv h1)
      · exact h2
    · exact h1
  have hagree' : mres S.X₂ (inf_le_left : E₁ ⊓ E₂ ≤ E₁) (mres S.X₂ hE₁O b) =
      mres S.X₂ (inf_le_right : E₁ ⊓ E₂ ≤ E₂) (mres S.X₂ hE₂O b₂') := by
    rw [mres_mres, mres_mres]
    have h1 := congrArg (mres S.X₂ hE12) hagree
    rw [mres_mres, mres_mres] at h1
    exact h1
  obtain ⟨b₃, hb₃1, hb₃2⟩ := exists_glue₂ (M := S.X₂) (le_sup_left : E₁ ≤ E₁ ⊔ E₂)
    (le_sup_right : E₂ ≤ E₁ ⊔ E₂) le_rfl (mres S.X₂ hE₁O b) (mres S.X₂ hE₂O b₂') hagree'
  have hle : E₁ ⊔ E₂ ≤ U := sup_le (hE₁O.trans hO) (hE₂O.trans hO₂)
  refine ⟨E₁ ⊔ E₂, hle, ?_, b₃, ?_⟩
  · rintro x (hx | hx)
    · by_cases hx0 : x ∈ V₀
      · exact Opens.mem_sup.2 (Or.inl ⟨hPO hx, Opens.mem_sup.2 (Or.inr hx0)⟩)
      · exact Opens.mem_sup.2 (Or.inl ⟨hPO hx, Opens.mem_sup.2 (Or.inl (hPu ⟨hx, hx0⟩))⟩)
    · by_cases hx0 : x ∈ V₀
      · exact Opens.mem_sup.2 (Or.inr ⟨hQO hx, Opens.mem_sup.2 (Or.inr hx0)⟩)
      · exact Opens.mem_sup.2 (Or.inr ⟨hQO hx, Opens.mem_sup.2 (Or.inl (hQv ⟨hx, hx0⟩))⟩)
  · refine eq_of_cover₂ (le_sup_left : E₁ ≤ E₁ ⊔ E₂) (le_sup_right : E₂ ≤ E₁ ⊔ E₂) le_rfl _ _ ?_
      ?_
    · rw [← mres_map, hb₃1, mres_map, hb, mres_mres, mres_mres]
    · rw [← mres_map, hb₃2, mres_map, hb₂', mres_mres, mres_mres]

/-- Restriction along `U ≤ U` is the identity. -/
private lemma mres_self {M : Mod R} (U : Opens X) (s : M.val.obj (op U)) :
    mres M (le_refl U) s = s := by
  have h := PresheafOfModules.congr_map_apply M.val
    (show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl) s
  refine h.trans ?_
  simp only [PresheafOfModules.map_id]
  rfl

/-- Lifts on a neighbourhood of any closed set contained in a finite union of opens over which
`c` lifts. -/
private lemma lift_finset [NormalSpace X] {S : ShortComplex (Mod R)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) {U : Opens X} (c : S.X₃.val.obj (op U)) {ι : Type}
    (V : ι → Opens X) (hV : ∀ i, V i ≤ U) (bf : ∀ i, S.X₂.val.obj (op (V i)))
    (hbf : ∀ i, S.g.val.app (op (V i)) (bf i) = mres S.X₃ (hV i) c) (F : Finset ι) :
    ∀ K : Set X, IsClosed K → K ⊆ (⋃ i ∈ F, (V i : Set X)) →
      ∃ (O : Opens X) (h : O ≤ U), K ⊆ O ∧
        ∃ b : S.X₂.val.obj (op O), S.g.val.app (op O) b = mres S.X₃ h c := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro K _ hKF
    have hK0 : K = ∅ := by simpa using hKF
    exact ⟨⊥, bot_le, by simp only [hK0, Set.empty_subset], 0,
      (subsingleton_bot S.X₃).elim _ _⟩
  | insert i F hi ih =>
    intro K hK hKF
    have hP : IsClosed (K \ V i) := hK.sdiff (V i).isOpen
    have hPF : K \ V i ⊆ ⋃ j ∈ F, (V j : Set X) := by
      rintro x ⟨hxK, hxV⟩
      have := hKF hxK
      simp only [Finset.mem_insert, Set.mem_iUnion, exists_prop] at this ⊢
      rcases this with ⟨j, hj | hj, hxj⟩
      · exact absurd (hj ▸ hxj) hxV
      · exact ⟨j, hj, hxj⟩
    obtain ⟨O, hO, hPO, b, hb⟩ := ih _ hP hPF
    obtain ⟨u, hu, hPu, hcl⟩ := normal_exists_closure_subset hP O.isOpen hPO
    have hQV : K \ u ⊆ V i := by
      intro x hx
      by_contra hxV
      exact hx.2 (hPu ⟨hx.1, hxV⟩)
    obtain ⟨O₃, h, hsub, b₃, hb₃⟩ := lift_union hS hA c (isClosed_closure.inter hK)
      (hK.sdiff hu) hO (hV i) ((Set.inter_subset_left).trans hcl) hQV b (bf i) hb (hbf i)
    refine ⟨O₃, h, ?_, b₃, hb₃⟩
    intro x hx
    apply hsub
    by_cases hxu : x ∈ u
    · exact Or.inl ⟨subset_closure hxu, hx⟩
    · exact Or.inr ⟨hx, hxu⟩

/-- A section of `C` over `U` lifts to `B` on an open neighbourhood of every closed `K ⊆ U`
(compact Hausdorff `X`, `A` soft). -/
private lemma lift_nbhd [CompactSpace X] [T2Space X] {S : ShortComplex (Mod R)}
    (hS : S.ShortExact) (hA : IsSoft S.X₁) {K : Set X} (hK : IsClosed K) {U : Opens X}
    (hKU : K ⊆ U) (c : S.X₃.val.obj (op U)) :
    ∃ (O : Opens X) (h : O ≤ U), K ⊆ O ∧
      ∃ b : S.X₂.val.obj (op O), S.g.val.app (op O) b = mres S.X₃ h c := by
  have := hS.epi_g
  have hloc : ∀ x : K, ∃ (V : Opens X) (hVU : V ≤ U), (x : X) ∈ V ∧
      ∃ t : S.X₂.val.obj (op V), S.g.val.app (op V) t = mres S.X₃ hVU c := fun x => by
    obtain ⟨V, hVU, hx, t, ht⟩ := exists_local_preimage_of_epi S.g c (hKU x.2)
    exact ⟨V, hVU, hx, t, ht⟩
  choose V hVU hxV t ht using hloc
  obtain ⟨F, hF⟩ := hK.isCompact.elim_finite_subcover (fun x : K => (V x : Set X))
    (fun x => (V x).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV _⟩)
  exact lift_finset hS hA c V hVU t ht F K hK hF

/-- **S3.b(ii).** For `0 → A → B → C → 0` exact with `A` soft, on compact Hausdorff `X`,
`Γ(B) → Γ(C)` is surjective. Proof: local lifts on a finite cover, shrunk to closed sets
`Kᵢ ⊆ Uᵢ` (normality); glue inductively: on a neighbourhood of `(K₁ ∪ ⋯ ∪ Kⱼ) ∩ Kⱼ₊₁` two lifts
differ by a section of `A`, which softness extends to a global section; correct and glue on
open neighbourhoods separated by normality. -/
theorem surjective_globalSections_of_isSoft [CompactSpace X] [T2Space X]
    {S : ShortComplex (Mod R)} (hS : S.ShortExact) (hA : IsSoft S.X₁) :
    Function.Surjective ((globalSections R).map S.g).hom := by
  intro y
  obtain ⟨O, hO, hKO, b, hb⟩ := lift_nbhd hS hA isClosed_univ (U := ⊤)
    (fun _ _ => trivial) y
  have hOt : O = ⊤ := top_unique fun x _ => hKO (Set.mem_univ x)
  subst hOt
  exact ⟨b, hb.trans (mres_self _ _)⟩

/-- **S3.b(iii).** In a short exact sequence `0 → A → B → C → 0` with `A`, `B` soft, `C` is soft
(on compact Hausdorff `X`): lift a section of `C` near `K` to `B` as in (ii), extend by softness
of `B`, and project. -/
theorem IsSoft.of_shortExact [CompactSpace X] [T2Space X] {S : ShortComplex (Mod R)}
    (hS : S.ShortExact) (hA : IsSoft S.X₁) (hB : IsSoft S.X₂) : IsSoft S.X₃ := by
  intro K hK U hKU c
  obtain ⟨O, hO, hKO, b, hb⟩ := lift_nbhd hS hA hK hKU c
  obtain ⟨t, V, hVO, hKV, ht⟩ := hB K hK O hKO b
  refine ⟨S.g.val.app (op ⊤) t, V, hVO.trans hO, hKV, ?_⟩
  rw [← mres_map, ht, mres_map, hb, mres_mres]

end Cohesive
end
