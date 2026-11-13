import Cohesivemodules.Sheaf.FineDef
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

set_option linter.style.header false

/-!
# S1–S2: fine sheaves of rings, Γ exact over them

Blueprint items S1–S2 (§3). `X` is a topological space (compact where needed), `R` a sheaf of
rings on `Opens X`, modules are `Mod R = SheafOfModules.{0} R`. S3 is in `Sheaf/Acyclic.lean`,
S4 in `Sheaf/Projective.lean` (split of blueprint §7's `Fine.lean`, size only).

* S1 `IsFine R`: partitions of unity subordinate to finite open covers. S1.a extension by
  zero of `ρ • t` for `ρ` supported in `U` (`existsUnique_extend`), and of morphisms
  (`exists_hom_extend`, needs `R` commutative).
* S2 over a fine `R` on compact `X`, `Γ` maps epimorphisms to surjections
  (`surjective_globalSections_of_epi`), through local surjectivity of epimorphisms
  (`exists_local_preimage_of_epi`, any `R`).

## Support without stalks
The support of `ρ ∈ R(X)` is the closed set of points where the germ of `ρ` is nonzero. We use
the equivalent stalk-free form: `supp ρ ⊆ U` iff there is an open `V` with `U ∪ V = X` and
`ρ|V = 0` (`SupportedIn`). For a sheaf the two agree: take `V = X ∖ supp ρ`; conversely
`supp ρ ⊆ X ∖ V ⊆ U`.

## Deviations
* ⚠ Finite covers (and compactness of `X` where needed) replace softness and arbitrary covers
  of [A] (blueprint S1, §9 deviation 2). `IsFine` alone says nothing about infinite covers.
* The extension of morphisms needs `R` commutative (`IsComm R`): `ρ • φ` is `R`-linear only
  for central `ρ`. Blueprint §3 assumes commutative rings throughout.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace Limits

variable {X : Type} [TopologicalSpace X]

/-! ## S1 Fine sheaves (definitions `rres`, `mres`, `IsComm`, `SupportedIn`, `IsFine` in
`Sheaf/FineDef.lean`) -/

/-- The underlying sheaf of abelian groups of `M`, as a `TopCat` sheaf. -/
private def topSheaf {R : RingSheaf X} (M : Mod R) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of X) :=
  ⟨M.val.presheaf, M.isSheaf⟩

/-- Locality for a cover of `V` by two opens. -/
private lemma eq_of_cover₂ {R : RingSheaf X} (M : Mod R) {V A B : Opens X} (hA : A ≤ V)
    (hB : B ≤ V) (hV : V ≤ A ⊔ B) (s s' : M.val.obj (op V))
    (h1 : mres M hA s = mres M hA s') (h2 : mres M hB s = mres M hB s') : s = s' :=
  TopCat.Sheaf.eq_of_locally_eq₂ (topSheaf M) (homOfLE hA) (homOfLE hB) hV s s' h1 h2

/-- Restricting twice. -/
private lemma mres_mres {R : RingSheaf X} (M : Mod R) {U V W : Opens X} (h1 : V ≤ U)
    (h2 : W ≤ V) (s : M.val.obj (op U)) :
    mres M h2 (mres M h1 s) = mres M (h2.trans h1) s :=
  (M.val.map_comp_apply (homOfLE h1).op (homOfLE h2).op s).symm

/-- Restricting a ring section twice. -/
private lemma rres_rres (R : RingSheaf X) {U V W : Opens X} (h1 : V ≤ U) (h2 : W ≤ V)
    (r : R.obj.obj (op U)) : rres R h2 (rres R h1 r) = rres R (h2.trans h1) r :=
  by
  change (R.obj.map (homOfLE h2).op).hom ((R.obj.map (homOfLE h1).op).hom r) = _
  rw [← RingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction is compatible with scalar multiplication. -/
private lemma mres_smul {R : RingSheaf X} (M : Mod R) {U V : Opens X} (h : V ≤ U)
    (r : R.obj.obj (op U)) (t : M.val.obj (op U)) :
    mres M h (r • t) = rres R h r • mres M h t :=
  M.val.map_smul _ r t

/-- Restriction of zero. -/
private lemma mres_zero {R : RingSheaf X} (M : Mod R) {U V : Opens X} (h : V ≤ U) :
    mres M h (0 : M.val.obj (op U)) = 0 :=
  map_zero _

/-- Gluing for a cover of `V` by two opens. -/
private lemma exists_glue₂ {R : RingSheaf X} (M : Mod R) {V A B : Opens X} (hA : A ≤ V)
    (hB : B ≤ V) (hV : V ≤ A ⊔ B) (a : M.val.obj (op A)) (b : M.val.obj (op B))
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

/-- **S1.a. Extension by zero of sections.** If `ρ` is supported in `U` and `t ∈ M(U)`, there
is a unique global section `s` with `s|U = ρ|U • t` that vanishes on every open where `ρ`
vanishes. [A, proof of Lemma 7.2.7] -/
theorem existsUnique_extend {R : RingSheaf X} {M : Mod R} {ρ : R.obj.obj (op ⊤)}
    {U : Opens X} (hρ : SupportedIn ρ U) (t : M.val.obj (op U)) :
    ∃! s : M.val.obj (op ⊤), mres M (le_top : U ≤ ⊤) s = rres R (le_top : U ≤ ⊤) ρ • t ∧
      ∀ V : Opens X, rres R (le_top : V ≤ ⊤) ρ = 0 → mres M (le_top : V ≤ ⊤) s = 0 := by
  obtain ⟨W, hUW, hW0⟩ := hρ
  have hcov : (⊤ : Opens X) ≤ U ⊔ W := hUW.ge
  -- `ρ` restricts to zero on every open inside `W`
  have hzero : ∀ A : Opens X, A ≤ W → rres R (le_top : A ≤ ⊤) ρ = 0 := by
    intro A hA
    have := rres_rres R (le_top : W ≤ ⊤) hA ρ
    rw [hW0, map_zero] at this
    exact this.symm
  obtain ⟨s, hsU, hsW⟩ := exists_glue₂ M (le_top : U ≤ ⊤) (le_top : W ≤ ⊤) hcov
    (rres R (le_top : U ≤ ⊤) ρ • t) 0 (by
      rw [mres_smul, mres_zero, rres_rres, hzero (U ⊓ W) inf_le_right, zero_smul])
  have hvan : ∀ V : Opens X, rres R (le_top : V ≤ ⊤) ρ = 0 →
      mres M (le_top : V ≤ ⊤) s = 0 := by
    intro V hV
    refine eq_of_cover₂ M (inf_le_left : V ⊓ U ≤ V) (inf_le_left : V ⊓ W ≤ V) ?_ _ _ ?_ ?_
    · rw [← inf_sup_left, hUW, inf_top_eq]
    · rw [mres_mres, mres_zero, ← mres_mres M (le_top : U ≤ ⊤) (inf_le_right : V ⊓ U ≤ U), hsU,
        mres_smul, rres_rres, ← rres_rres R (le_top : V ≤ ⊤) (inf_le_left : V ⊓ U ≤ V) ρ, hV,
        map_zero, zero_smul]
    · rw [mres_mres, mres_zero, ← mres_mres M (le_top : W ≤ ⊤) (inf_le_right : V ⊓ W ≤ W), hsW,
        mres_zero]
  refine ⟨s, ⟨hsU, hvan⟩, ?_⟩
  rintro s' ⟨hs'U, hs'⟩
  exact eq_of_cover₂ M (le_top : U ≤ ⊤) (le_top : W ≤ ⊤) hcov s' s (hs'U.trans hsU.symm)
    ((hs' W (hzero W le_rfl)).trans hsW.symm)

/-- The component at an open `V ⊆ U` of a morphism `φ : M|U ⟶ N|U`, as a map `M(V) → N(V)`:
sections of `M|U` over the object `Over.mk (homOfLE h)` of the over-site are, by definition,
sections of `M` over `V`. -/
def restrApp {R : RingSheaf X} {M N : Mod R} {U : Opens X}
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) {V : Opens X} (h : V ≤ U)
    (m : M.val.obj (op V)) : N.val.obj (op V) :=
  φ.val.app (op (Over.mk (homOfLE h))) m

/-- `restrApp` is natural in the open. -/
private lemma restrApp_mres {R : RingSheaf X} {M N : Mod R} {U : Opens X}
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) {V V' : Opens X} (h₁ : V ≤ U) (h₂ : V' ≤ U)
    (h : V' ≤ V) (m : M.val.obj (op V)) :
    restrApp φ h₂ (mres M h m) = mres N h (restrApp φ h₁ m) := by
  have := PresheafOfModules.naturality_apply φ.val
    (show op (Over.mk (homOfLE h₁) : Over U) ⟶ op (Over.mk (homOfLE h₂)) from
      (Over.homMk (homOfLE h)).op) m
  exact this

/-- `restrApp` is additive. -/
private lemma restrApp_add {R : RingSheaf X} {M N : Mod R} {U : Opens X}
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) {V : Opens X} (h : V ≤ U)
    (m m' : M.val.obj (op V)) : restrApp φ h (m + m') = restrApp φ h m + restrApp φ h m' :=
  map_add (φ.val.app (op (Over.mk (homOfLE h)))).hom m m'

/-- `restrApp` is linear. -/
private lemma restrApp_smul {R : RingSheaf X} {M N : Mod R} {U : Opens X}
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) {V : Opens X} (h : V ≤ U)
    (r : R.obj.obj (op V)) (m : M.val.obj (op V)) :
    restrApp φ h (r • m) = r • restrApp φ h m :=
  by
  have := map_smul (φ.val.app (op (Over.mk (homOfLE h)))).hom
    (show (R.over U).obj.obj (op (Over.mk (homOfLE h))) from r)
    (show ((restr R U).obj M).val.obj (op (Over.mk (homOfLE h))) from m)
  exact this

/-- `n ∈ N(V)` is the extension by zero of `ρ • φ(m)`: it restricts to `ρ • φ(m)` on `V ∩ U`
and to `0` on `V ∩ W`. -/
private def IsExt {R : RingSheaf X} {M N : Mod R} {U : Opens X} (ρ : R.obj.obj (op ⊤))
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) (W : Opens X) {V : Opens X}
    (m : M.val.obj (op V)) (n : N.val.obj (op V)) : Prop :=
  mres N (inf_le_left : V ⊓ U ≤ V) n = rres R (le_top : V ⊓ U ≤ ⊤) ρ •
      restrApp φ (inf_le_right : V ⊓ U ≤ U) (mres M (inf_le_left : V ⊓ U ≤ V) m) ∧
    mres N (inf_le_left : V ⊓ W ≤ V) n = 0

/-- Uniqueness of the extension by zero. -/
private lemma isExt_unique {R : RingSheaf X} {M N : Mod R} {U W : Opens X} {ρ : R.obj.obj (op ⊤)}
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) (hUW : U ⊔ W = ⊤) {V : Opens X}
    {m : M.val.obj (op V)} {n n' : N.val.obj (op V)} (h : IsExt ρ φ W m n)
    (h' : IsExt ρ φ W m n') : n = n' := by
  refine eq_of_cover₂ N (inf_le_left : V ⊓ U ≤ V) (inf_le_left : V ⊓ W ≤ V) ?_ n n'
    (h.1.trans h'.1.symm) (h.2.trans h'.2.symm)
  rw [← inf_sup_left, hUW, inf_top_eq]

/-- Existence of the extension by zero. -/
private lemma isExt_exists {R : RingSheaf X} {M N : Mod R} {U W : Opens X}
    {ρ : R.obj.obj (op ⊤)} (hW0 : rres R (le_top : W ≤ ⊤) ρ = 0)
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) (hUW : U ⊔ W = ⊤) {V : Opens X}
    (m : M.val.obj (op V)) : ∃ n : N.val.obj (op V), IsExt ρ φ W m n := by
  have hzero : ∀ A : Opens X, A ≤ W → rres R (le_top : A ≤ ⊤) ρ = 0 := by
    intro A hA
    have := rres_rres R (le_top : W ≤ ⊤) hA ρ
    rw [hW0, map_zero] at this
    exact this.symm
  obtain ⟨n, hn1, hn2⟩ := exists_glue₂ N (inf_le_left : V ⊓ U ≤ V) (inf_le_left : V ⊓ W ≤ V)
    (by rw [← inf_sup_left, hUW, inf_top_eq])
    (rres R (le_top : V ⊓ U ≤ ⊤) ρ •
      restrApp φ (inf_le_right : V ⊓ U ≤ U) (mres M (inf_le_left : V ⊓ U ≤ V) m)) 0 (by
      rw [mres_smul, mres_zero, rres_rres]
      rw [hzero ((V ⊓ U) ⊓ (V ⊓ W)) (inf_le_right.trans inf_le_right), zero_smul])
  exact ⟨n, hn1, hn2⟩

/-- Extensions by zero are additive. -/
private lemma isExt_add {R : RingSheaf X} {M N : Mod R} {U W : Opens X} {ρ : R.obj.obj (op ⊤)}
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) {V : Opens X}
    {m m' : M.val.obj (op V)} {n n' : N.val.obj (op V)} (h : IsExt ρ φ W m n)
    (h' : IsExt ρ φ W m' n') : IsExt ρ φ W (m + m') (n + n') := by
  refine ⟨?_, ?_⟩
  · have e1 : ∀ (A : Opens X) (hA : A ≤ V) (x y : N.val.obj (op V)),
        mres N hA (x + y) = mres N hA x + mres N hA y := fun _ _ _ _ => map_add _ _ _
    have e2 : ∀ (A : Opens X) (hA : A ≤ V) (x y : M.val.obj (op V)),
        mres M hA (x + y) = mres M hA x + mres M hA y := fun _ _ _ _ => map_add _ _ _
    rw [e1, h.1, h'.1, e2, restrApp_add, smul_add]
  · have e1 : ∀ (A : Opens X) (hA : A ≤ V) (x y : N.val.obj (op V)),
        mres N hA (x + y) = mres N hA x + mres N hA y := fun _ _ _ _ => map_add _ _ _
    rw [e1, h.2, h'.2, add_zero]

/-- Extensions by zero are linear (`R` commutative). -/
private lemma isExt_smul {R : RingSheaf X} (hR : IsComm R) {M N : Mod R} {U W : Opens X}
    {ρ : R.obj.obj (op ⊤)} (φ : (restr R U).obj M ⟶ (restr R U).obj N) {V : Opens X}
    (r : R.obj.obj (op V)) {m : M.val.obj (op V)} {n : N.val.obj (op V)}
    (h : IsExt ρ φ W m n) : IsExt ρ φ W (r • m) (r • n) := by
  refine ⟨?_, ?_⟩
  · rw [mres_smul, h.1, mres_smul, restrApp_smul, smul_smul, smul_smul, hR]
  · rw [mres_smul, h.2, smul_zero]

/-- Extensions by zero are compatible with restriction. -/
private lemma isExt_mres {R : RingSheaf X} {M N : Mod R} {U W : Opens X} {ρ : R.obj.obj (op ⊤)}
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) {V V' : Opens X} (hV : V' ≤ V)
    {m : M.val.obj (op V)} {n : N.val.obj (op V)} (h : IsExt ρ φ W m n) :
    IsExt ρ φ W (mres M hV m) (mres N hV n) := by
  refine ⟨?_, ?_⟩
  · have hle : V' ⊓ U ≤ V ⊓ U := inf_le_inf_right U hV
    have e1 : mres N (inf_le_left : V' ⊓ U ≤ V') (mres N hV n) =
        mres N hle (mres N (inf_le_left : V ⊓ U ≤ V) n) := by
      rw [mres_mres, mres_mres]
    rw [e1, h.1, mres_smul, rres_rres, ← restrApp_mres φ (inf_le_right : V ⊓ U ≤ U)
      (inf_le_right : V' ⊓ U ≤ U) hle, mres_mres, mres_mres]
  · have hle : V' ⊓ W ≤ V ⊓ W := inf_le_inf_right W hV
    have e1 : mres N (inf_le_left : V' ⊓ W ≤ V') (mres N hV n) =
        mres N hle (mres N (inf_le_left : V ⊓ W ≤ V) n) := by
      rw [mres_mres, mres_mres]
    rw [e1, h.2, mres_zero]

/-- **S1.a for morphisms.** For `R` commutative and `ρ` supported in `U`, a morphism
`φ : M|U ⟶ N|U` gives a global morphism `ψ : M ⟶ N` with `ψ = ρ • φ` on opens `V ⊆ U` and
`ψ = 0` on opens where `ρ` vanishes. -/
theorem exists_hom_extend {R : RingSheaf X} (hR : IsComm R) {M N : Mod R}
    {ρ : R.obj.obj (op ⊤)} {U : Opens X} (hρ : SupportedIn ρ U)
    (φ : (restr R U).obj M ⟶ (restr R U).obj N) :
    ∃ ψ : M ⟶ N,
      (∀ (V : Opens X) (h : V ≤ U) (m : M.val.obj (op V)),
        ψ.val.app (op V) m = rres R (le_top : V ≤ ⊤) ρ • restrApp φ h m) ∧
      ∀ V : Opens X, rres R (le_top : V ≤ ⊤) ρ = 0 → ψ.val.app (op V) = 0 := by
  obtain ⟨W, hUW, hW0⟩ := hρ
  have hex : ∀ (V : Opens X) (m : M.val.obj (op V)), ∃ n : N.val.obj (op V), IsExt ρ φ W m n :=
    fun V m => isExt_exists hW0 φ hUW m
  choose ψf hψ using hex
  have hadd : ∀ (V : Opens X) (m m' : M.val.obj (op V)), ψf V (m + m') = ψf V m + ψf V m' :=
    fun V m m' => isExt_unique φ hUW (hψ V (m + m')) (isExt_add φ (hψ V m) (hψ V m'))
  have hsmul : ∀ (V : Opens X) (r : R.obj.obj (op V)) (m : M.val.obj (op V)),
      ψf V (r • m) = r • ψf V m :=
    fun V r m => isExt_unique φ hUW (hψ V (r • m)) (isExt_smul hR φ r (hψ V m))
  have hnat : ∀ (V V' : Opens X) (h : V' ≤ V) (m : M.val.obj (op V)),
      ψf V' (mres M h m) = mres N h (ψf V m) :=
    fun V V' h m => isExt_unique φ hUW (hψ V' _) (isExt_mres φ h (hψ V m))
  let ψ : M ⟶ N := ⟨
    { app := fun V => ModuleCat.ofHom
        { toFun := ψf V.unop
          map_add' := hadd V.unop
          map_smul' := fun r m => hsmul V.unop r m }
      naturality := by
        intro V V' g
        ext m
        exact hnat V.unop V'.unop g.unop.le m }⟩
  refine ⟨ψ, ?_, ?_⟩
  · intro V h m
    have hzero : rres R (le_top : V ⊓ W ≤ ⊤) ρ = 0 := by
      have := rres_rres R (le_top : W ≤ ⊤) (inf_le_right : V ⊓ W ≤ W) ρ
      rw [hW0, map_zero] at this
      exact this.symm
    refine isExt_unique φ hUW (hψ V m) ⟨?_, ?_⟩
    · rw [mres_smul, rres_rres, restrApp_mres φ h inf_le_right inf_le_left]
    · rw [mres_smul, rres_rres, hzero, zero_smul]
  · intro V hV
    ext m
    show ψf V m = 0
    refine isExt_unique φ hUW (hψ V m) ⟨?_, ?_⟩
    · have hz : rres R (le_top : V ⊓ U ≤ ⊤) ρ = 0 := by
        have := rres_rres R (le_top : V ≤ ⊤) (inf_le_left : V ⊓ U ≤ V) ρ
        rw [hV, map_zero] at this
        exact this.symm
      rw [mres_zero, hz, zero_smul]
    · rw [mres_zero]

/-! ## S2 Γ is exact on modules over a fine sheaf -/

/-- The sieve on `U` of opens `V ≤ U` over which `s ∈ N(U)` restricts into the image of `f`. -/
private def imSieve {R : RingSheaf X} {M N : Mod R} (f : M ⟶ N) {U : Opens X}
    (s : N.val.obj (op U)) : Sieve U where
  arrows V g := ∃ t : M.val.obj (op V), f.val.app (op V) t = (N.val.map g.op).hom s
  downward_closed := by
    rintro V W g ⟨t, ht⟩ h
    refine ⟨(M.val.map h.op).hom t, ?_⟩
    have h1 := PresheafOfModules.naturality_apply f.val h.op t
    have h2 := N.val.map_comp_apply g.op h.op s
    change f.val.app (op W) (M.val.map h.op t) = N.val.map (h ≫ g).op s
    rw [h1, ht]
    exact h2.symm

/-- The sieve of `s|W` is the pullback of the sieve of `s`. -/
private lemma imSieve_map {R : RingSheaf X} {M N : Mod R} (f : M ⟶ N) {U : Opens X}
    (s : N.val.obj (op U)) {W : Opens X} (h : W ≤ U) :
    imSieve f (mres N h s) = (imSieve f s).pullback (homOfLE h) := by
  ext V g
  simp only [imSieve, Sieve.pullback_apply]
  change (∃ t, _ = N.val.map g.op (N.val.map (homOfLE h).op s)) ↔
    ∃ t, _ = N.val.map (g ≫ homOfLE h).op s
  rw [← N.val.map_comp_apply]
  rfl

/-- The submodule of sections of `N` that are locally in the image of `f`. -/
private def localImage {R : RingSheaf X} {M N : Mod R} (f : M ⟶ N) : N.Submodule where
  obj U :=
    { carrier := {s | imSieve f s ∈ Opens.grothendieckTopology X U.unop}
      add_mem' := by
        intro s s' hs hs'
        refine (Opens.grothendieckTopology X).superset_covering ?_
          ((Opens.grothendieckTopology X).intersection_covering hs hs')
        rintro V g ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
        refine ⟨t + t', ?_⟩
        simp only [map_add, ht, ht']
        rfl
      zero_mem' := by
        refine (Opens.grothendieckTopology X).superset_covering ?_
          ((Opens.grothendieckTopology X).top_mem _)
        intro V g _
        exact ⟨0, by simp only [map_zero]; rfl⟩
      smul_mem' := by
        intro r s hs
        refine (Opens.grothendieckTopology X).superset_covering ?_ hs
        rintro V g ⟨t, ht⟩
        refine ⟨rres R g.le r • t, ?_⟩
        have h1 : f.val.app (op V) (rres R g.le r • t) = rres R g.le r • f.val.app (op V) t :=
          map_smul (f.val.app (op V)).hom _ _
        have h2 := N.val.map_smul g.op r s
        rw [h1, ht]
        exact h2.symm }
  map := by
    intro Xo Yo g s hs
    have h1 := (Opens.grothendieckTopology X).pullback_stable g.unop hs
    have h2 := imSieve_map f s (leOfHom g.unop)
    show imSieve f (mres N (leOfHom g.unop) s) ∈ Opens.grothendieckTopology X Yo.unop
    rw [h2]
    exact h1
  isSheaf := by
    intro Xo s hs
    refine (Opens.grothendieckTopology X).transitive hs _ (fun V g hg => ?_)
    have h2 := imSieve_map f s (leOfHom g)
    exact h2 ▸ hg

/-- `f` factors through the inclusion of its local image. -/
private def toLocalImage {R : RingSheaf X} {M N : Mod R} (f : M ⟶ N) :
    M ⟶ (localImage f).toSheafOfModules :=
  ⟨{ app := fun U => ModuleCat.ofHom ((f.val.app U).hom.codRestrict ((localImage f).obj U) (by
        intro t
        refine (Opens.grothendieckTopology X).superset_covering ?_
          ((Opens.grothendieckTopology X).top_mem _)
        intro V g _
        refine ⟨(M.val.map g.op).hom t, ?_⟩
        exact PresheafOfModules.naturality_apply f.val g.op t))
     naturality := by
        intro U V g
        ext t
        exact Subtype.ext (PresheafOfModules.naturality_apply f.val g t) }⟩

private lemma toLocalImage_ι {R : RingSheaf X} {M N : Mod R} (f : M ⟶ N) :
    toLocalImage f ≫ (localImage f).ι = f := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  ext t
  rfl

/-- **S2, local part.** An epimorphism of sheaves of modules is locally surjective: every
section of `N` over `U` lifts to `M` near every point of `U`. Any sheaf of rings `R`.
(Mathlib has the converse; the module version of `Sheaf.isLocallySurjective_iff_epi'` is ✗.) -/
theorem exists_local_preimage_of_epi {R : RingSheaf X} {M N : Mod R} (f : M ⟶ N) [Epi f]
    {U : Opens X} (s : N.val.obj (op U)) {x : X} (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : M.val.obj (op V), f.val.app (op V) t = mres N hVU s := by
  have hepi : Epi (localImage f).ι := epi_of_epi_fac (toLocalImage_ι f)
  have hiso : IsIso (localImage f).ι := isIso_of_mono_of_epi _
  have hmem : s ∈ (localImage f).obj (op U) := by
    have h : ((inv (localImage f).ι ≫ (localImage f).ι).val.app (op U)) s = s := by
      rw [IsIso.inv_hom_id]
      rfl
    have h' : ((inv (localImage f).ι).val.app (op U) s).1 = s := h
    exact h' ▸ ((inv (localImage f).ι).val.app (op U) s).2
  obtain ⟨V, g, hg, hxV⟩ := (Opens.mem_grothendieckTopology X).1 hmem x hx
  exact ⟨V, leOfHom g, hxV, hg⟩

/-- A morphism of modules maps the extension by zero of `t` to that of `f t`, namely `ρ • y`
when `y|U = f t`. -/
private lemma app_extend_eq {R : RingSheaf X} {M N : Mod R} (f : M ⟶ N)
    {ρ : R.obj.obj (op ⊤)} {U : Opens X} (hρ : SupportedIn ρ U) (t : M.val.obj (op U))
    (σ : M.val.obj (op ⊤))
    (hσ : mres M (le_top : U ≤ ⊤) σ = rres R (le_top : U ≤ ⊤) ρ • t ∧
      ∀ V : Opens X, rres R (le_top : V ≤ ⊤) ρ = 0 → mres M (le_top : V ≤ ⊤) σ = 0)
    (y : N.val.obj (op ⊤)) (hy : mres N (le_top : U ≤ ⊤) y = f.val.app (op U) t) :
    f.val.app (op ⊤) σ = ρ • y := by
  refine (existsUnique_extend (M := N) hρ (f.val.app (op U) t)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · have h1 := PresheafOfModules.naturality_apply f.val (homOfLE (le_top : U ≤ ⊤)).op σ
    change N.val.map _ (f.val.app (op ⊤) σ) = _
    rw [← h1]
    change f.val.app (op U) (mres M (le_top : U ≤ ⊤) σ) = _
    rw [hσ.1]
    exact map_smul (f.val.app (op U)).hom _ _
  · intro V hV
    have h1 := PresheafOfModules.naturality_apply f.val (homOfLE (le_top : V ≤ ⊤)).op σ
    change N.val.map _ (f.val.app (op ⊤) σ) = _
    rw [← h1]
    change f.val.app (op V) (mres M (le_top : V ≤ ⊤) σ) = _
    rw [hσ.2 V hV]
    exact map_zero (f.val.app (op V)).hom
  · rw [mres_smul, hy]
  · intro V hV
    rw [mres_smul, hV, zero_smul]

/-- **S2. Γ is exact on modules over a fine sheaf.** For `R` fine on compact `X`, an
epimorphism `f : M ⟶ N` of `R`-modules is surjective on global sections. Proof: lift locally
(`exists_local_preimage_of_epi`), take a finite subcover and glue `∑ ρ i • tᵢ` with a
partition of unity (S1.a). -/
theorem surjective_globalSections_of_epi [CompactSpace X] {R : RingSheaf X} (hR : IsFine R)
    {M N : Mod R} (f : M ⟶ N) [Epi f] :
    Function.Surjective ((globalSections R).map f).hom := by
  intro y
  have hloc : ∀ x : X, ∃ (V : Opens X), x ∈ V ∧ ∃ t : M.val.obj (op V),
      f.val.app (op V) t = mres N (le_top : V ≤ ⊤) y := fun x => by
    obtain ⟨V, _, hx, t, ht⟩ := exists_local_preimage_of_epi f y (U := ⊤) (x := x) trivial
    exact ⟨V, hx, t, ht⟩
  choose V hxV t ht using hloc
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => ((V x : Opens X) : Set X))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hcov : (⨆ i : S, V i.1) = ⊤ := by
    refine top_unique fun x _ => ?_
    have := hS (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hxi⟩ := this
    exact Opens.mem_iSup.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ1, hρ⟩ := hR S (fun i => V i.1) hcov
  have hex := fun i : S => existsUnique_extend (M := M) (hρ i) (t i.1)
  choose σ hσ _ using hex
  refine ⟨∑ i, σ i, ?_⟩
  have hsum : f.val.app (op ⊤) (∑ i, σ i) = ∑ i, ρ i • y := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ =>
      app_extend_eq f (hρ i) (t i.1) (σ i) (hσ i) y (ht i.1).symm
  change f.val.app (op ⊤) (∑ i, σ i) = y
  rw [hsum, ← Finset.sum_smul, hρ1, one_smul]

end Cohesive
