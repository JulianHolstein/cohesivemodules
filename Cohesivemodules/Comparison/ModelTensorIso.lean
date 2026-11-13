import Cohesivemodules.Comparison.ModelTensorCoord

set_option linter.style.header false

/-!
# C7.d (part 4): `Φn : (𝒜^•|U ⊗ K)^n ≅ T^n`

Blueprint item C7.d (split from `ModelTensor.lean` for size). `Φn` assembled from `Φc`, with
inverse `Gn` built from the dual-basis data. Auxiliary declarations for `exists_TC_iso_tensorC`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X) (K : CochainComplex (Mod (P.R.over U)) ℤ)

section GenTot

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  (R : Sheaf J CommRingCat.{0})

/-- Morphisms out of the `n`-th term of `tensorC R A K` from its summands. -/
def tensorCDesc (A K : CochainComplex (Mod (ringOf R)) ℤ) (n : ℤ) {T : Mod (ringOf R)}
    (f : ∀ q p : ℤ, q + p = n → (((tensorBifunctor R).obj (A.X q)).obj (K.X p) ⟶ T)) :
    (tensorC R A K).X n ⟶ T :=
  HomologicalComplex.mapBifunctorDesc (K₁ := A) (K₂ := K)
    (F := tensorBifunctor R) (c := ComplexShape.up ℤ) f

/-- The inclusion of the summand `(q, p)` into the `n`-th term of `tensorC R A K`. -/
def tensorCι (A K : CochainComplex (Mod (ringOf R)) ℤ) (q p n : ℤ) (h : q + p = n) :
    ((tensorBifunctor R).obj (A.X q)).obj (K.X p) ⟶ (tensorC R A K).X n :=
  HomologicalComplex.ιMapBifunctor (K₁ := A) (K₂ := K) (tensorBifunctor R)
    (ComplexShape.up ℤ) q p n h

/-- `tensorCDesc` on a summand. -/
theorem tensorCι_desc (A K : CochainComplex (Mod (ringOf R)) ℤ) (n : ℤ)
    {T : Mod (ringOf R)}
    (f : ∀ q p : ℤ, q + p = n → (((tensorBifunctor R).obj (A.X q)).obj (K.X p) ⟶ T))
    (q p : ℤ) (h : q + p = n) : tensorCι R A K q p n h ≫ tensorCDesc R A K n f = f q p h :=
  HomologicalComplex.ι_mapBifunctorDesc _ q p h

/-- Morphisms out of the `n`-th term of `tensorC R A K` are determined on the summands. -/
theorem tensorC_hom_ext (A K : CochainComplex (Mod (ringOf R)) ℤ) (n : ℤ)
    {T : Mod (ringOf R)} {f g : (tensorC R A K).X n ⟶ T}
    (h : ∀ (q p : ℤ) (hqp : q + p = n),
      tensorCι R A K q p n hqp ≫ f = tensorCι R A K q p n hqp ≫ g) :
    f = g :=
  HomologicalComplex.mapBifunctor.hom_ext h

/-- `tensorBifunctor` is additive on sums of morphisms in the first variable. -/
theorem tensor_app_map_sum {M M' : Mod (ringOf R)} {ι : Type} (s : Finset ι)
    (f : ι → (M ⟶ M')) (N : Mod (ringOf R)) :
    ((tensorBifunctor R).map (∑ i ∈ s, f i)).app N =
      ∑ i ∈ s, ((tensorBifunctor R).map (f i)).app N := by
  rw [Functor.map_sum, NatTrans.app_sum]

/-- Summands: `∑ (F f_i)_K ≫ ι = (F (∑ f_i))_K ≫ ι`. -/
theorem sum_tensor_ι (A K : CochainComplex (Mod (ringOf R)) ℤ) (q p n : ℤ)
    (h : q + p = n) {ι : Type} (s : Finset ι) (f : ι → (A.X q ⟶ A.X q)) :
    ∑ i ∈ s, ((tensorBifunctor R).map (f i)).app (K.X p) ≫ tensorCι R A K q p n h =
      ((tensorBifunctor R).map (∑ i ∈ s, f i)).app (K.X p) ≫ tensorCι R A K q p n h := by
  rw [tensor_app_map_sum, Preadditive.sum_comp]

/-- `tensorCMap₁` preserves identities. -/
theorem tensorCMap₁_id (A K : CochainComplex (Mod (ringOf R)) ℤ) :
    tensorCMap₁ R (𝟙 A) K = 𝟙 _ := by
  unfold tensorCMap₁
  refine HomologicalComplex.hom_ext _ _ fun n =>
    tensorC_hom_ext R A K n fun i j h => ?_
  simp only [tensorCι]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]
  erw [Category.comp_id]

/-- `tensorCMap₁` preserves composition. -/
theorem tensorCMap₁_comp {A A' A'' : CochainComplex (Mod (ringOf R)) ℤ} (f : A ⟶ A')
    (g : A' ⟶ A'') (K : CochainComplex (Mod (ringOf R)) ℤ) :
    tensorCMap₁ R (f ≫ g) K = tensorCMap₁ R f K ≫ tensorCMap₁ R g K := by
  unfold tensorCMap₁
  refine HomologicalComplex.hom_ext _ _ fun n =>
    tensorC_hom_ext R A K n fun i j h => ?_
  simp only [tensorCι]
  erw [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Functor.map_comp,
    NatTrans.comp_app, Category.id_comp, Category.assoc,
    CategoryTheory.Functor.map_id]

/-- An isomorphism `A ≅ A'` induces `A ⊗ K ≅ A' ⊗ K`. -/
def tensorCIso₁ {A A' : CochainComplex (Mod (ringOf R)) ℤ} (f : A ≅ A')
    (K : CochainComplex (Mod (ringOf R)) ℤ) : tensorC R A K ≅ tensorC R A' K where
  hom := tensorCMap₁ R f.hom K
  inv := tensorCMap₁ R f.inv K
  hom_inv_id := by rw [← tensorCMap₁_comp, f.hom_inv_id, tensorCMap₁_id]
  inv_hom_id := by rw [← tensorCMap₁_comp, f.inv_hom_id, tensorCMap₁_id]

/-- Degree `p` of `A[0] ⊗ K ≅ F(A)(K)` followed by `γ ⊗ K` and any map out of the target. -/
theorem single_comp_tensorC {A : Mod (ringOf R)} {A' K : CochainComplex (Mod (ringOf R)) ℤ}
    (γ : (HomologicalComplex.single (Mod (ringOf R)) (ComplexShape.up ℤ) 0).obj A ⟶ A') (p : ℤ)
    {T : Mod (ringOf R)} (Φ : (tensorC R A' K).X p ⟶ T) :
    (tensorCSingleIso R A K).inv.f p ≫ (tensorCMap₁ R γ K).f p ≫ Φ =
      ((tensorBifunctor R).map
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫ γ.f 0)).app (K.X p) ≫
        (tensorCι R A' K 0 p p (zero_add p) ≫ Φ) := by
  have h1 : (tensorCSingleIso R A K).inv.f p =
      ((tensorBifunctor R).map
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv).app (K.X p) ≫
      tensorCι R ((HomologicalComplex.single (Mod (ringOf R)) (ComplexShape.up ℤ) 0).obj A) K
        0 p p (zero_add p) := rfl
  have h2 : tensorCι R ((HomologicalComplex.single (Mod (ringOf R)) (ComplexShape.up ℤ) 0).obj A) K
        0 p p (zero_add p) ≫ (tensorCMap₁ R γ K).f p =
      ((tensorBifunctor R).map (γ.f 0)).app (K.X p) ≫ tensorCι R A' K 0 p p (zero_add p) := by
    unfold tensorCMap₁ tensorCι
    erw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [h1, Category.assoc, ← Category.assoc (tensorCι _ _ _ _ _ _ _), h2, Category.assoc,
    Functor.map_comp, NatTrans.comp_app, Category.assoc]

/-- Degree `p` of a composite `a ≫ (b ≫ γ₁ ⊗ K) ≫ (γ₂ ⊗ K) ≫ Φ`. -/
theorem chain_f {A₀ A₁ A₂ K X₁ Y : CochainComplex (Mod (ringOf R)) ℤ}
    (a : K ⟶ X₁) (b : X₁ ⟶ tensorC R A₀ K) (γ₁ : A₀ ⟶ A₁) (γ₂ : A₁ ⟶ A₂)
    (Φ : tensorC R A₂ K ⟶ Y) (p : ℤ) :
    ((a ≫ b ≫ tensorCMap₁ R γ₁ K) ≫ tensorCMap₁ R γ₂ K ≫ Φ).f p =
      a.f p ≫ b.f p ≫ (tensorCMap₁ R (γ₁ ≫ γ₂) K).f p ≫ Φ.f p := by
  rw [tensorCMap₁_comp]
  simp only [HomologicalComplex.comp_f, Category.assoc]

end GenTot

/-- `𝒜^•|U`, the restriction of the Dolbeault-type complex to `U`. -/
abbrev Atil : CochainComplex (Mod (ringOf (P.O.over U))) ℤ :=
  ((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj P.dgaComplex

/-- `T^n` as a module over `ringOf (O|U)` (the same sheaf as `TSh`). -/
abbrev TShO [CompactSpace X] (n : ℤ) : Mod (ringOf (P.O.over U)) := P.TSh U (P.FK U K) n

/-- The comparison `(𝒜^•|U ⊗ K)^n ⟶ T^n`, assembled from the components `Φc`. -/
def Φn [CompactSpace X] (n : ℤ) :
    (tensorC (P.O.over U) (P.Atil U) K).X n ⟶ P.TShO U K n :=
  tensorCDesc (P.O.over U) (P.Atil U) K n (fun q p h => P.Φc U K q p n h)

/-- `Φn` on a summand. -/
theorem ι_Φn [CompactSpace X] (n q p : ℤ) (h : q + p = n) :
    tensorCι (P.O.over U) (P.Atil U) K q p n h ≫ P.Φn U K n = P.Φc U K q p n h :=
  tensorCι_desc (P.O.over U) (P.Atil U) K n (fun q p h => P.Φc U K q p n h) q p h

/-- The inverse of `κSh`. -/
def κInv (p : ℤ) : P.RsF U K p ⟶ ((tensorBifunctor (P.O.over U)).obj (P.AqU U 0)).obj
    (K.X p) :=
  (@asIso _ _ _ _ (P.κSh U K p) (P.isIso_κSh U K p)).inv

section SumSigma

/-- A sum over `DIdx` supported on the fibre over `q0` is the sum over that fibre. -/
theorem sum_didx_single {C : Type*} [Category C] [Preadditive C] {N0 : ℕ} {m : ℕ → ℕ}
    {A B : C} (f : DIdx N0 m → (A ⟶ B)) (q0 : Fin (N0 + 1))
    (h0 : ∀ qj : DIdx N0 m, qj.1 ≠ q0 → f qj = 0) :
    ∑ qj : DIdx N0 m, f qj = ∑ j : Fin (m q0), f ⟨q0, j⟩ := by
  rw [← Finset.univ_sigma_univ, ← Finset.sum_sigma' (Finset.univ : Finset (Fin (N0 + 1)))
    (fun q => (Finset.univ : Finset (Fin (m q)))) (fun q j => f ⟨q, j⟩)]
  rw [Finset.sum_eq_single q0]
  · intro q _ hq
    exact Finset.sum_eq_zero fun j _ => h0 ⟨q, j⟩ hq
  · intro h
    exact absurd (Finset.mem_univ q0) h

end SumSigma

section IsoN

variable {N0 : ℕ} {m : ℕ → ℕ} (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m)
  (hs : ∀ (V W : Opens X) (h : W ≤ V) q j,
      P.D.res h ((D V).s q j : P.D.A V) = ((D W).s q j : P.D.A W))
  (hc : ∀ (V W : Opens X) (h : W ≤ V) (q : ℕ) j (a : ↥(GCDga.piece (P.D.𝒜 V) q))
      (b : ↥(GCDga.piece (P.D.𝒜 W) q)), (b : P.D.A W) = P.D.res h a →
      (D W).c q j b = (P.D.res h).f0 ((D V).c q j a))

include hs hc in
/-- The candidate inverse `T^n ⟶ (𝒜^•|U ⊗ K)^n` of `Φn`. -/
def Gn [CompactSpace X] (n : ℤ) :
    P.TShO U K n ⟶ (tensorC (P.O.over U) (P.Atil U) K).X n :=
  ∑ qj : DIdx N0 m, P.ISh U K D hc qj n ≫ P.κInv U K (n - DIdx.deg qj) ≫
    ((tensorBifunctor (P.O.over U)).map (P.σSh U D hs qj.1 qj.2)).app
      (K.X (n - DIdx.deg qj)) ≫
    tensorCι (P.O.over U) (P.Atil U) K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring)

include hs hc in
/-- `G ≫ Φ = 𝟙`. -/
theorem Gn_Φn [CompactSpace X] (n : ℤ) : P.Gn U K D hs hc n ≫ P.Φn U K n = 𝟙 _ := by
  unfold Gn
  refine Eq.trans ?_ (P.sum_ISh_RSh U K D hc hs n)
  rw [Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun qj _ => ?_
  have e := (congrArg (((tensorBifunctor (P.O.over U)).map (P.σSh U D hs qj.1 qj.2)).app
      (K.X (n - DIdx.deg qj)) ≫ ·) (P.ι_Φn U K n (DIdx.deg qj) (n - DIdx.deg qj) (by ring))).trans
    (P.E2 U K D hs qj n)
  have h2 := (@asIso _ _ _ _ (P.κSh U K (n - DIdx.deg qj))
    (P.isIso_κSh U K _)).inv_hom_id_assoc (P.RSh U K D hs qj n)
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))))).trans
    (congrArg (_ ≫ ·) ((congrArg (P.κInv U K (n - DIdx.deg qj) ≫ ·) e).trans h2))

include hs hc in
/-- Off-diagonal terms of `ι ≫ Φ ≫ G` vanish. -/
theorem ι_Φn_term_zero [CompactSpace X] (n q p : ℤ) (h : q + p = n) (qj : DIdx N0 m)
    (hne : p ≠ n - DIdx.deg qj) :
    P.Φc U K q p n h ≫ (P.ISh U K D hc qj n ≫ P.κInv U K (n - DIdx.deg qj) ≫
      ((tensorBifunctor (P.O.over U)).map (P.σSh U D hs qj.1 qj.2)).app
        (K.X (n - DIdx.deg qj)) ≫
      tensorCι (P.O.over U) (P.Atil U) K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring)) = 0 := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (P.E1b U K D hc qj n q p h hne)).trans Limits.zero_comp)

include hs hc in
/-- The diagonal term of `ι ≫ Φ ≫ G` is `((c_{qj} ≫ σ_{qj}) ⊗ K) ≫ ι`. -/
theorem ι_Φn_term_diag [CompactSpace X] (n : ℤ) (qj : DIdx N0 m) :
    P.Φc U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring) ≫
      (P.ISh U K D hc qj n ≫ P.κInv U K (n - DIdx.deg qj) ≫
      ((tensorBifunctor (P.O.over U)).map (P.σSh U D hs qj.1 qj.2)).app
        (K.X (n - DIdx.deg qj)) ≫
      tensorCι (P.O.over U) (P.Atil U) K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring)) =
    ((tensorBifunctor (P.O.over U)).map (P.cSh U D hc qj.1 qj.2 ≫ P.σSh U D hs qj.1 qj.2)).app
      (K.X (n - DIdx.deg qj)) ≫
      tensorCι (P.O.over U) (P.Atil U) K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring) := by
  have h2 := (@asIso _ _ _ _ (P.κSh U K (n - DIdx.deg qj))
    (P.isIso_κSh U K _)).hom_inv_id_assoc
    (((tensorBifunctor (P.O.over U)).map (P.σSh U D hs qj.1 qj.2)).app
        (K.X (n - DIdx.deg qj)) ≫
      tensorCι (P.O.over U) (P.Atil U) K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring))
  erw [← Category.assoc, P.E1a U K D hc qj n, Category.assoc, h2]
  erw [Functor.map_comp, NatTrans.comp_app, Category.assoc]

include hs hc in
/-- `𝒜^q|U = 0` outside `0 ≤ q ≤ N0`. -/
theorem isZero_AqU (q : ℤ) (hq : ¬ ∃ q0 : Fin (N0 + 1), ((q0 : ℕ) : ℤ) = q) :
    Limits.IsZero (P.AqU U q) := by
  have h : Limits.IsZero (P.dgaO q) := by
    refine isZero_of_sections_subsingleton fun V => ⟨fun a b => ?_⟩
    have key : ∀ y : (P.dgaO q).val.obj V, y.1 = 0 := fun y => by
      by_cases hlt : q < 0
      · exact GCDga.eq_zero_of_neg (P.D.𝒜 V.unop) hlt y.2
      · have hgt : (N0 : ℤ) < q := by
          by_contra hle
          exact hq ⟨⟨q.toNat, by omega⟩, by simp only; omega⟩
        exact (D V.unop).zero_of_gt q hgt y.1 y.2
    exact Subtype.ext ((key a).trans (key b).symm)
  exact Functor.map_isZero (restr P.R U) h

include hs hc in
/-- `Φ ≫ G = 𝟙`. -/
theorem Φn_Gn [CompactSpace X] (n : ℤ) : P.Φn U K n ≫ P.Gn U K D hs hc n = 𝟙 _ := by
  refine tensorC_hom_ext (P.O.over U) (P.Atil U) K n fun q p hqp => ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (· ≫ P.Gn U K D hs hc n) (P.ι_Φn U K n q p hqp)) ?_
  refine Eq.trans ?_ (Category.comp_id _).symm
  unfold Gn
  refine Eq.trans (Preadditive.comp_sum _ _ _) ?_
  by_cases hq : ∃ q0 : Fin (N0 + 1), ((q0 : ℕ) : ℤ) = q
  · obtain ⟨q0, rfl⟩ := hq
    obtain rfl : p = n - ((q0 : ℕ) : ℤ) := by omega
    refine Eq.trans (sum_didx_single _ q0 (fun qj hqj => ?_)) ?_
    · refine P.ι_Φn_term_zero U K D hs hc n _ _ hqp qj ?_
      intro h
      apply hqj
      apply Fin.ext
      have h' : ((q0 : ℕ) : ℤ) = ((qj.1 : ℕ) : ℤ) := by
        simp only [DIdx.deg] at h
        omega
      exact_mod_cast h'.symm
    · refine Eq.trans (Finset.sum_congr rfl fun j _ =>
        P.ι_Φn_term_diag U K D hs hc n ⟨q0, j⟩) ?_
      refine Eq.trans (sum_tensor_ι (P.O.over U) (P.Atil U) K _ _ n hqp Finset.univ
        (fun j : Fin (m q0) => P.cSh U D hc q0 j ≫ P.σSh U D hs q0 j)) ?_
      have hsum := P.sum_cSh_σSh U D hs hc (q0 : ℕ)
      refine (congrArg (fun F => ((tensorBifunctor (P.O.over U)).map F).app
        (K.X (n - ((q0 : ℕ) : ℤ))) ≫ tensorCι (P.O.over U) (P.Atil U) K _ _ n hqp) hsum).trans ?_
      exact (congrArg (fun F => NatTrans.app F (K.X (n - ((q0 : ℕ) : ℤ))) ≫
        tensorCι (P.O.over U) (P.Atil U) K _ _ n hqp)
        (CategoryTheory.Functor.map_id (tensorBifunctor (P.O.over U))
          (P.AqU U ((q0 : ℕ) : ℤ)))).trans (Category.id_comp _)
  · have hz : Limits.IsZero (((tensorBifunctor (P.O.over U)).obj ((P.Atil U).X q)).obj
        (K.X p)) :=
      ((CategoryTheory.evaluation _ _).obj (K.X p)).map_isZero
        ((tensorBifunctor (P.O.over U)).map_isZero (P.isZero_AqU U D hs hc q hq))
    refine Eq.trans (Finset.sum_eq_zero fun qj _ => ?_) (hz.eq_of_src _ _)
    refine P.ι_Φn_term_zero U K D hs hc n q p hqp qj ?_
    intro h
    exact hq ⟨qj.1, by simp only [DIdx.deg] at h; omega⟩

end IsoN

/-- `Φn` is an isomorphism: the dual-basis data gives the inverse `Gn`. -/
theorem isIso_Φn [CompactSpace X] (n : ℤ) : IsIso (P.Φn U K n) := by
  obtain ⟨N0, m, D, hs, hc⟩ := P.exists_dfm
  exact ⟨⟨P.Gn U K D hs hc n, P.Φn_Gn U K D hs hc n, P.Gn_Φn U K D hs hc n⟩⟩

end PreResolvingData

end Cohesive
