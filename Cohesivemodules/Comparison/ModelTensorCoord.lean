import Cohesivemodules.Comparison.ModelTensorKappa

set_option linter.style.header false

/-!
# C7.d (part 3): coordinates `I_{qj}`, reconstructions `R_{qj}` and the components `Φc`

Blueprint item C7.d (split from `ModelTensor.lean` for size). The relations E1, E2 between `Φc`,
the coordinates of `T^n` and `κ`. Auxiliary declarations for `exists_TC_iso_tensorC`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X) (K : CochainComplex (Mod (P.R.over U)) ℤ)

section Coord

variable {N0 : ℕ} {m : ℕ → ℕ} (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m)

/-- The coordinate `x ↦ iTot x (qj)` on sections over `V`. -/
def IV (qj : DIdx N0 m) (n : ℤ) (V : (Over U)ᵒᵖ) :
    (P.TPre U (P.FK U K) n).obj V ⟶ (P.RsF U K (n - DIdx.deg qj)).val.obj V :=
  (ModuleCat.ofHom
    ({ toFun := fun x => (D V.unop.left).iTot n x.1 qj
       map_add' := fun x y => by
         exact congrFun (map_add ((D V.unop.left).iTot n) x.1 y.1) qj
       map_smul' := fun r x => by
         exact congrFun (Dfm.iTot_smul0 (D V.unop.left) n (P.ρ V.unop.left r) x.1) qj } :
      P.TSec U (P.FK U K) n V →ₗ[P.O.obj.obj (op V.unop.left)]
        P.FSecO U K (n - DIdx.deg qj) V) :
    ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.TSec U (P.FK U K) n V) ⟶
      ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.FSecO U K (n - DIdx.deg qj) V))

variable (hc : ∀ (V W : Opens X) (h : W ≤ V) (q : ℕ) j (a : ↥(GCDga.piece (P.D.𝒜 V) q))
      (b : ↥(GCDga.piece (P.D.𝒜 W) q)), (b : P.D.A W) = P.D.res h a →
      (D W).c q j b = (P.D.res h).f0 ((D V).c q j a))

include hc in
/-- The coordinate `I_{qj} : T^n ⟶ F^{n-q}` as a morphism of sheaves of `R|U`-modules. -/
def ISh [CompactSpace X] (qj : DIdx N0 m) (n : ℤ) :
    P.TSh U (P.FK U K) n ⟶ P.RsF U K (n - DIdx.deg qj) :=
  ⟨{ app := fun V ↦ P.IV U K D qj n V
     naturality := by
       intro V W f
       refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
       exact P.iTot_nat U (P.FK U K) D hc n f x.1 qj }⟩

variable (hs : ∀ (V W : Opens X) (h : W ≤ V) q j,
      P.D.res h ((D V).s q j : P.D.A V) = ((D W).s q j : P.D.A W))

/-- The reconstruction `z ↦ s_{qj} ⊗ z` on sections over `V`. -/
def RV (qj : DIdx N0 m) (n : ℤ) (V : (Over U)ᵒᵖ) :
    (P.RsF U K (n - DIdx.deg qj)).val.obj V ⟶ (P.TPre U (P.FK U K) n).obj V :=
  (ModuleCat.ofHom
   ({ toFun := fun z => (⟨Dfm.rTot (Q := (P.FSec U (P.FK U K) · V)) (D V.unop.left) n
        (Pi.single qj (FSecO.val P U K z)), Dfm.rTot_mem _ n _⟩ : P.TSec U (P.FK U K) n V)
      map_add' := fun x y => by
        refine Subtype.ext ?_
        show Dfm.rTot (Q := (P.FSec U (P.FK U K) · V)) (D V.unop.left) n
          (Pi.single qj (FSecO.val P U K (x + y))) = _ + _
        rw [FSecO.val_add, Pi.single_add, map_add]
      map_smul' := fun r x => by
        refine Subtype.ext ?_
        have h := Dfm.rTot_smul0 (Q := (P.FSec U (P.FK U K) · V)) (D V.unop.left) n
          (P.ρ V.unop.left r) (Pi.single qj (FSecO.val P U K x))
        have h2 : (Pi.single qj (FSecO.val P U K (r • x)) :
            ∀ qj' : DIdx N0 m, P.FSec U (P.FK U K) (n - DIdx.deg qj') V) =
            (P.ρ V.unop.left r) • Pi.single qj (FSecO.val P U K x) := by
          funext qj'
          by_cases hq : qj' = qj
          · subst hq
            simp only [Pi.single_eq_same, Pi.smul_apply, FSecO.val_smul]
          · simp only [Pi.single_eq_of_ne hq, Pi.smul_apply, smul_zero]
        exact (congrArg _ h2).trans h } :
      P.FSecO U K (n - DIdx.deg qj) V →ₗ[P.O.obj.obj (op V.unop.left)]
        P.TSec U (P.FK U K) n V) :
    ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.FSecO U K (n - DIdx.deg qj) V) ⟶
      ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.TSec U (P.FK U K) n V))

include hs in
/-- The reconstruction `ρ_{qj} : F^{n-q} ⟶ T^n`, `z ↦ s_{qj} ⊗ z`, as a morphism of sheaves. -/
def RSh [CompactSpace X] (qj : DIdx N0 m) (n : ℤ) :
    P.RsF U K (n - DIdx.deg qj) ⟶ P.TSh U (P.FK U K) n :=
  ⟨{ app := fun V ↦ P.RV U K D qj n V
     naturality := by
       intro V W f
       refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
       refine Subtype.ext ?_
       have h := Dfm.map_rTot (P.D.res (leOfHom f.unop.left))
         (fun p => P.fRes U (P.FK U K) p f) (fun p => P.fRes_smul U (P.FK U K) f p)
         (D V.unop.left) (D W.unop.left) (hs _ _ _) n (Pi.single qj z)
       refine Eq.trans (congrArg (Dfm.rTot (Q := (P.FSec U (P.FK U K) · W))
         (D W.unop.left) n) ?_) h.symm
       funext qj'
       by_cases hq : qj' = qj
       · subst hq
         erw [Pi.single_eq_same, Pi.single_eq_same]
         rfl
       · erw [Pi.single_eq_of_ne hq, Pi.single_eq_of_ne hq]
         exact (map_zero _).symm }⟩

include hs hc in
/-- `∑_{qj} I_{qj} ≫ ρ_{qj} = 𝟙` on `T^n` (`rTot ∘ iTot = id`). -/
theorem sum_ISh_RSh [CompactSpace X] (n : ℤ) :
    ∑ qj : DIdx N0 m, P.ISh U K D hc qj n ≫ P.RSh U K D hs qj n = 𝟙 (P.TSh U (P.FK U K) n) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  have hs' : (∑ qj : DIdx N0 m, P.ISh U K D hc qj n ≫ P.RSh U K D hs qj n).val.app V =
      ∑ qj : DIdx N0 m, ((P.ISh U K D hc qj n ≫ P.RSh U K D hs qj n).val.app V) :=
    Functor.map_sum (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ V) _ _
  rw [hs']
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
  rw [ModuleCat.hom_sum]
  erw [LinearMap.sum_apply]
  have key := Dfm.rTot_iTot (Q := (P.FSec U (P.FK U K) · V)) (D V.unop.left) n x.2
  refine Eq.trans ?_ key
  rw [← Finset.univ_sum_single (((D V.unop.left).iTot n) x.1), map_sum]
  exact (map_sum (P.tDeg U (P.FK U K) n V).subtype _ Finset.univ).trans
    (Finset.sum_congr rfl fun qj _ => rfl)

end Coord

/-- The component `a(𝒜^q ⊗ K^p) ⟶ T^n` of the comparison map, induced by `φPre`. -/
def Φc [CompactSpace X] (q p n : ℤ) (h : q + p = n) :
    ((tensorBifunctor (P.O.over U)).obj (P.AqU U q)).obj (K.X p) ⟶ P.TSh U (P.FK U K) n :=
  (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (P.O.over U)).obj)).symm
    (P.φPre U K q p n h)

/-- The transpose of `Φc` is `φPre`. -/
theorem Φc_equiv [CompactSpace X] (q p n : ℤ) (h : q + p = n) :
    (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (P.O.over U)).obj))
      (P.Φc U K q p n h) = P.φPre U K q p n h :=
  Equiv.apply_symm_apply _ _

section RSingle

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {N0 : ℕ} {m : ℕ → ℕ}
  {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- `rTot` of a single coordinate is one pure tensor `s_{qj} ⊗ z`. -/
theorem Dfm.rTot_single (D : Dfm 𝒜 N0 m) (n : ℤ) (qj : DIdx N0 m)
    (z : Q (n - DIdx.deg qj)) :
    D.rTot n (Pi.single qj z) =
      Tot.tmul 𝒜 Q (D.s qj.1 qj.2 : A) (lof (𝒜 0) ℤ Q (n - DIdx.deg qj) z) := by
  obtain ⟨q0, j0⟩ := qj
  unfold Dfm.rTot
  rw [AddMonoidHom.mk'_apply]
  rw [Finset.sum_eq_single q0]
  · rw [Finset.sum_eq_single j0]
    · erw [Pi.single_eq_same]
    · intro j _ hj
      have hne : (⟨q0, j⟩ : DIdx N0 m) ≠ ⟨q0, j0⟩ := fun h => hj (by simpa using h)
      erw [Pi.single_eq_of_ne hne]
      rw [map_zero, Tot.tmul_zero]
    · intro h
      exact absurd (Finset.mem_univ j0) h
  · intro q _ hq
    refine Finset.sum_eq_zero fun j _ => ?_
    have hne : (⟨q, j⟩ : DIdx N0 m) ≠ ⟨q0, j0⟩ := fun h =>
      hq (by simpa using congrArg Sigma.fst h)
    erw [Pi.single_eq_of_ne hne]
    rw [map_zero, Tot.tmul_zero]
  · intro h
    exact absurd (Finset.mem_univ q0) h

end RSingle

section Eqs

variable {N0 : ℕ} {m : ℕ → ℕ} (D : ∀ V : Opens X, Dfm (P.D.𝒜 V) N0 m)
  (hs : ∀ (V W : Opens X) (h : W ≤ V) q j,
      P.D.res h ((D V).s q j : P.D.A V) = ((D W).s q j : P.D.A W))

include hs in
/-- E2 at the presheaf level: `(σ ⊗ K) ≫ φ = κ ≫ ρ`. -/
theorem E2_pre [CompactSpace X] (qj : DIdx N0 m) (n : ℤ) :
    MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
      (P.σSh U D hs qj.1 qj.2).val (K.X (n - DIdx.deg qj)).val ≫
      P.φPre U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring) =
    P.κPre U K (n - DIdx.deg qj) ≫ (SheafOfModules.forget _).map (P.RSh U K D hs qj n) := by
  refine PresheafOfModules.hom_ext fun V => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a k => ?_
  refine Subtype.ext ?_
  refine Eq.trans ?_ (Dfm.rTot_single (Q := (P.FSec U (P.FK U K) · V)) (D V.unop.left) n qj
    (((⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K (n - DIdx.deg qj) V k :
      P.FSec U (P.FK U K) (n - DIdx.deg qj) V))).symm
  show Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V)
      (((⟨a.1, a.2⟩ : ↥(P.D.𝒜 V.unop.left 0)) • (D V.unop.left).s qj.1 qj.2 :
        ↥(GCDga.piece (P.D.𝒜 V.unop.left) (qj.1 : ℕ))) : P.D.A V.unop.left)
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) (n - DIdx.deg qj)
        (P.bcη U K (n - DIdx.deg qj) V k)) = _
  rw [map_smul, Tot.tmul_smul0]
  exact congrArg (fun x => Tot.tmul _ _ x _) (GCDga.central (P.D.𝒜 V.unop.left) a.2 _)

include hs in
/-- E2: `(σ_{qj} ⊗ K) ≫ Φ = κ ≫ ρ_{qj}`. -/
theorem E2 [CompactSpace X] (qj : DIdx N0 m) (n : ℤ) :
    ((tensorBifunctor (P.O.over U)).map (P.σSh U D hs qj.1 qj.2)).app
        (K.X (n - DIdx.deg qj)) ≫ P.Φc U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring) =
      P.κSh U K (n - DIdx.deg qj) ≫ P.RSh U K D hs qj n := by
  have e1 : ((tensorBifunctor (P.O.over U)).map (P.σSh U D hs qj.1 qj.2)).app
      (K.X (n - DIdx.deg qj)) = (sheafifyF (P.O.over U)).map
        (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          (P.σSh U D hs qj.1 qj.2).val (K.X (n - DIdx.deg qj)).val) := rfl
  rw [e1]
  apply ((PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  have h2 := P.Φc_equiv U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring)
  have h3 : (PresheafOfModules.sheafificationHomEquiv.{0} (𝟙 (ringOf (P.O.over U)).obj))
      (P.κSh U K (n - DIdx.deg qj)) = P.κPre U K (n - DIdx.deg qj) :=
    Equiv.apply_symm_apply _ _
  erw [h2, h3]
  exact P.E2_pre U K D hs qj n

variable (hc : ∀ (V W : Opens X) (h : W ≤ V) (q : ℕ) j (a : ↥(GCDga.piece (P.D.𝒜 V) q))
      (b : ↥(GCDga.piece (P.D.𝒜 W) q)), (b : P.D.A W) = P.D.res h a →
      (D W).c q j b = (P.D.res h).f0 ((D V).c q j a))

include hc in
/-- E1 at the presheaf level, off-diagonal: `φ ≫ I_{qj} = 0` when `i₂ ≠ n - q`. -/
theorem E1b_pre [CompactSpace X] (qj : DIdx N0 m) (n i₁ i₂ : ℤ) (h : i₁ + i₂ = n)
    (hne : i₂ ≠ n - DIdx.deg qj) :
    P.φPre U K i₁ i₂ n h ≫ (SheafOfModules.forget _).map (P.ISh U K D hc qj n) = 0 := by
  refine PresheafOfModules.hom_ext fun V => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a k => ?_
  show (D V.unop.left).iTot n (P.pairElt U K i₁ i₂ V a k) qj = 0
  show (D V.unop.left).coef qj (a.1 : P.D.A V.unop.left) •
    (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) i₂
      (P.bcη U K i₂ V k)) (n - DIdx.deg qj) = 0
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hne), smul_zero]

include hc in
/-- E1 at the presheaf level, diagonal: `φ ≫ I_{qj} = (c_{qj} ⊗ K) ≫ κ`. -/
theorem E1a_pre [CompactSpace X] (qj : DIdx N0 m) (n : ℤ) :
    P.φPre U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring) ≫
        (SheafOfModules.forget _).map (P.ISh U K D hc qj n) =
      MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
        (P.cSh U D hc qj.1 qj.2).val (K.X (n - DIdx.deg qj)).val ≫
        P.κPre U K (n - DIdx.deg qj) := by
  refine PresheafOfModules.hom_ext fun V => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a k => ?_
  show (D V.unop.left).coef qj (a.1 : P.D.A V.unop.left) •
    (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) (n - DIdx.deg qj)
      (P.bcη U K (n - DIdx.deg qj) V k)) (n - DIdx.deg qj) =
    (⟨((D V.unop.left).c qj.1 qj.2 (⟨a.1, a.2⟩ : ↥(GCDga.piece (P.D.𝒜 V.unop.left) qj.1)) :
      ↥(P.D.𝒜 V.unop.left 0)).1, ((D V.unop.left).c qj.1 qj.2 ⟨a.1, a.2⟩).2⟩ :
        ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K (n - DIdx.deg qj) V k
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
  exact congrArg (· • _) (Dfm.coef_of_eq (D V.unop.left) qj.1 a.2 qj.2)

include hc in
/-- E1, off-diagonal: `Φ_{i₁,i₂} ≫ I_{qj} = 0` when `i₂ ≠ n - q`. -/
theorem E1b [CompactSpace X] (qj : DIdx N0 m) (n i₁ i₂ : ℤ) (h : i₁ + i₂ = n)
    (hne : i₂ ≠ n - DIdx.deg qj) :
    P.Φc U K i₁ i₂ n h ≫ P.ISh U K D hc qj n = 0 := by
  have h1 := (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv_naturality_right_symm (P.φPre U K i₁ i₂ n h)
    (P.ISh U K D hc qj n)
  erw [P.E1b_pre U K D hc qj n i₁ i₂ h hne] at h1
  have h2 : P.Φc U K i₁ i₂ n h = ((PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf (P.O.over U)).obj)).homEquiv _ _).symm (P.φPre U K i₁ i₂ n h) :=
    sheafificationHomEquiv_symm_mdl _
  rw [h2]
  refine Eq.trans h1.symm ?_
  erw [Adjunction.homEquiv_counit, Functor.map_zero, Limits.zero_comp]
  rfl

include hc in
/-- E1, diagonal: `Φ_{q,n-q} ≫ I_{qj} = (c_{qj} ⊗ K) ≫ κ`. -/
theorem E1a [CompactSpace X] (qj : DIdx N0 m) (n : ℤ) :
    P.Φc U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring) ≫ P.ISh U K D hc qj n =
      ((tensorBifunctor (P.O.over U)).map (P.cSh U D hc qj.1 qj.2)).app
        (K.X (n - DIdx.deg qj)) ≫ P.κSh U K (n - DIdx.deg qj) := by
  have e1 : ((tensorBifunctor (P.O.over U)).map (P.cSh U D hc qj.1 qj.2)).app
      (K.X (n - DIdx.deg qj)) = (sheafifyF (P.O.over U)).map
        (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          (P.cSh U D hc qj.1 qj.2).val (K.X (n - DIdx.deg qj)).val) := rfl
  rw [e1]
  have h1 := (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv_naturality_right_symm
    (P.φPre U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring)) (P.ISh U K D hc qj n)
  erw [P.E1a_pre U K D hc qj n] at h1
  have h2 : P.Φc U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring) =
      ((PresheafOfModules.sheafificationAdjunction.{0}
      (𝟙 (ringOf (P.O.over U)).obj)).homEquiv _ _).symm
        (P.φPre U K (DIdx.deg qj) (n - DIdx.deg qj) n (by ring)) :=
    sheafificationHomEquiv_symm_mdl _
  rw [h2]
  refine Eq.trans h1.symm ?_
  have h3 := (PresheafOfModules.sheafificationAdjunction.{0}
    (𝟙 (ringOf (P.O.over U)).obj)).homEquiv_naturality_left_symm
    (MonoidalCategory.whiskerRight (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
          (P.cSh U D hc qj.1 qj.2).val (K.X (n - DIdx.deg qj)).val) (P.κPre U K (n - DIdx.deg qj))
  erw [h3]
  congr 1
  exact (sheafificationHomEquiv_symm_mdl _).symm

end Eqs

end PreResolvingData

end Cohesive
