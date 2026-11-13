import Cohesivemodules.Sheaf.Flat.TotAuxBasic

set_option linter.style.header false

/-!
# S8 (part 2): total complexes of bifunctors (part 2 of 2)

Split from `Sheaf/Flat/TotAux.lean` for size; continues `Sheaf/Flat/TotAuxBasic.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace
section TotAux
open HomologicalComplex

section ConeIso

open CochainComplex HomComplex

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D] [HasBinaryBiproducts C₂] [HasBinaryBiproducts D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  (K : CochainComplex C₁ ℤ) {L L' : CochainComplex C₂ ℤ} (g : L ⟶ L')
  [∀ M : CochainComplex C₂ ℤ, K.HasMapBifunctor M F (ComplexShape.up ℤ)]

/-- `Φ M := K ⊗ M` (total complex of the bifunctor `F`). -/
private noncomputable abbrev Φ (M : CochainComplex C₂ ℤ) : CochainComplex D ℤ :=
  K.mapBifunctor M F (ComplexShape.up ℤ)

/-- `Φ g`. -/
private noncomputable abbrev Φmap : Φ F K L ⟶ Φ F K L' :=
  mapBifunctorMap (𝟙 K) g F (ComplexShape.up ℤ)

/-- `ι` into the total complex of `Φ M`. -/
private noncomputable abbrev Φι (M : CochainComplex C₂ ℤ) (p q n : ℤ) (h : p + q = n) :
    (F.obj (K.X p)).obj (M.X q) ⟶ (Φ F K M).X n :=
  ιMapBifunctor K M F (ComplexShape.up ℤ) p q n h

omit [HasBinaryBiproducts C₂] [HasBinaryBiproducts D] in
/-- The differential of `Φ M` on a summand. -/
private lemma Φι_d (M : CochainComplex C₂ ℤ) (p q n n' : ℤ) (h : p + q = n) (hn : n + 1 = n') :
    Φι F K M p q n h ≫ (Φ F K M).d n n' =
      (F.map (K.d p (p + 1))).app (M.X q) ≫ Φι F K M (p + 1) q n' (by omega) +
        (Int.negOnePow p) • ((F.obj (K.X p)).map (M.d q (q + 1)) ≫
          Φι F K M p (q + 1) n' (by omega)) := by
  subst hn
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel p (p + 1) by simp) _ _
      (by show p + 1 + q = n + 1; omega),
    mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel q (q + 1) by simp) _
      (by show p + (q + 1) = n + 1; omega)]
  simp [ComplexShape.ε₁, ComplexShape.ε₂]

/-- The cochain `α : Φ L → Φ (cone g)` of degree `-1`. -/
private noncomputable def coneα : Cochain (Φ F K L) (Φ F K (mappingCone g)) (-1) :=
  Cochain.mk (fun n m h => mapBifunctorDesc (fun p q hpq =>
    (Int.negOnePow p) • ((F.obj (K.X p)).map ((mappingCone.inl g).v q (q - 1) (by omega)) ≫
      Φι F K (mappingCone g) p (q - 1) m
        (by have : p + q = n := hpq; show p + (q - 1) = m; omega))))

/-- `ι` followed by `α`. -/
private lemma Φι_coneα (p q n n' : ℤ) (h : p + q = n) (hn : n + (-1) = n') :
    Φι F K L p q n h ≫ (coneα F K g).v n n' hn =
      (Int.negOnePow p) • ((F.obj (K.X p)).map ((mappingCone.inl g).v q (q - 1) (by omega)) ≫
        Φι F K (mappingCone g) p (q - 1) n' (by omega)) := by
  simp [coneα]

/-- `ι` followed by `α`, with the target index as a variable. -/
private lemma Φι_coneα' (p q q' n n' : ℤ) (h : p + q = n) (hq : q' + 1 = q)
    (hn : n + (-1) = n') :
    Φι F K L p q n h ≫ (coneα F K g).v n n' hn =
      (Int.negOnePow p) • ((F.obj (K.X p)).map ((mappingCone.inl g).v q q' (by omega)) ≫
        Φι F K (mappingCone g) p q' n' (by omega)) := by
  obtain rfl : q' = q - 1 := by omega
  exact Φι_coneα F K g p q n n' h hn

/-- The equation making `α` and `Φ (inr g)` define a map out of `cone (Φ g)`. -/
private lemma coneα_eq : δ (-1) 0 (coneα F K g) =
    Cochain.ofHom (Φmap F K g ≫
      mapBifunctorMap (𝟙 K) (mappingCone.inr g) F (ComplexShape.up ℤ)) := by
  refine Cochain.ext₀ _ _ fun n => ?_
  refine mapBifunctor.hom_ext fun p q h => ?_
  have h' : p + q = n := h
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [δ_v (-1) 0 (by omega) _ n n (by omega) (n - 1) (n + 1) (by omega) (by omega)]
  rw [Preadditive.comp_add, ← Category.assoc, Φι_coneα' F K g p (q' + 1) q' n (n - 1) h rfl
      (by omega),
    Linear.units_smul_comp, Category.assoc,
    Φι_d F K (mappingCone g) p q' (n - 1) n (by omega) (by omega),
    Linear.comp_units_smul, Int.negOnePow_zero, one_smul, ← Category.assoc,
    Φι_d F K L p (q' + 1) n (n + 1) h rfl, Preadditive.add_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    Φι_coneα' F K g (p + 1) (q' + 1) q' (n + 1) n (by omega) rfl (by omega),
    Φι_coneα' F K g p (q' + 1 + 1) (q' + 1) (n + 1) n (by omega) rfl (by omega)]
  simp only [Linear.comp_units_smul, Preadditive.comp_add, Preadditive.comp_neg,
    smul_add, smul_smul, Int.negOnePow_succ,
    Units.neg_smul, Int.units_mul_self, one_smul]
  have h1 : (F.obj (K.X p)).map ((mappingCone.inl g).v (q' + 1) q' (by omega)) ≫
      (F.map (K.d p (p + 1))).app ((mappingCone g).X q') =
      (F.map (K.d p (p + 1))).app (L.X (q' + 1)) ≫
        (F.obj (K.X (p + 1))).map ((mappingCone.inl g).v (q' + 1) q' (by omega)) :=
    (F.map (K.d p (p + 1))).naturality _
  have h2 := mappingCone.inl_v_d g (q' + 1) q' (q' + 1 + 1) (by omega) (by omega)
  have hsum : (F.obj (K.X p)).map ((mappingCone.inl g).v (q' + 1) q' (by omega)) ≫
        (F.obj (K.X p)).map ((mappingCone g).d q' (q' + 1)) ≫
          Φι F K (mappingCone g) p (q' + 1) n (by omega) +
      (F.obj (K.X p)).map (L.d (q' + 1) (q' + 1 + 1)) ≫
        (F.obj (K.X p)).map ((mappingCone.inl g).v (q' + 1 + 1) (q' + 1) (by omega)) ≫
          Φι F K (mappingCone g) p (q' + 1) n (by omega) =
      (F.obj (K.X p)).map (g.f (q' + 1)) ≫ (F.obj (K.X p)).map ((mappingCone.inr g).f (q' + 1)) ≫
          Φι F K (mappingCone g) p (q' + 1) n (by omega) := by
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← Preadditive.add_comp, ← Functor.map_add, h2]
    simp
  have hRHS : ιMapBifunctor K L F (ComplexShape.up ℤ) p (q' + 1) n h ≫
      (Cochain.ofHom (Φmap F K g ≫ mapBifunctorMap (𝟙 K) (mappingCone.inr g) F
        (ComplexShape.up ℤ))).v n n (add_zero n) =
      (F.obj (K.X p)).map (g.f (q' + 1)) ≫ (F.obj (K.X p)).map ((mappingCone.inr g).f (q' + 1)) ≫
          Φι F K (mappingCone g) p (q' + 1) n (by omega) := by
    simp
  rw [reassoc_of% h1, hRHS, ← hsum]
  abel

/-- The cochain `α' : Φ (cone g) → Φ L` of degree `1`. -/
private noncomputable def coneα' : Cochain (Φ F K (mappingCone g)) (Φ F K L) 1 :=
  Cochain.mk (fun n m h => mapBifunctorDesc (fun p q hpq =>
    (Int.negOnePow p) • ((F.obj (K.X p)).map ((mappingCone.fst g).1.v q (q + 1) rfl) ≫
      Φι F K L p (q + 1) m (by have : p + q = n := hpq; show p + (q + 1) = m; omega))))

/-- The cochain `β' : Φ (cone g) → Φ L'` of degree `0`. -/
private noncomputable def coneβ' : Cochain (Φ F K (mappingCone g)) (Φ F K L') 0 :=
  Cochain.mk (fun n m h => mapBifunctorDesc (fun p q hpq =>
    (F.obj (K.X p)).map ((mappingCone.snd g).v q q (add_zero q)) ≫
      Φι F K L' p q m (by have : p + q = n := hpq; show p + q = m; omega)))

/-- `ι` followed by `α'`. -/
private lemma Φι_coneα'' (p q q' n n' : ℤ) (h : p + q = n) (hq : q + 1 = q') (hn : n + 1 = n') :
    Φι F K (mappingCone g) p q n h ≫ (coneα' F K g).v n n' hn =
      (Int.negOnePow p) • ((F.obj (K.X p)).map ((mappingCone.fst g).1.v q q' hq) ≫
        Φι F K L p q' n' (by omega)) := by
  subst hq
  simp [coneα']

/-- `ι` followed by `β'`. -/
private lemma Φι_coneβ' (p q n : ℤ) (h : p + q = n) (hn : n + 0 = n) :
    Φι F K (mappingCone g) p q n h ≫ (coneβ' F K g).v n n hn =
      (F.obj (K.X p)).map ((mappingCone.snd g).v q q (add_zero q)) ≫ Φι F K L' p q n h := by
  simp [coneβ']

/-- `α'` is a cocycle. -/
private lemma coneα'_cocycle : δ 1 2 (coneα' F K g) = 0 := by
  refine Cochain.ext _ _ fun n m hnm => ?_
  refine mapBifunctor.hom_ext fun p q h => ?_
  have h' : p + q = n := h
  obtain rfl : m = n + 2 := by omega
  rw [δ_v 1 2 (by omega) _ n (n + 2) hnm (n + 1) (n + 1) (by omega) (by omega)]
  rw [Preadditive.comp_add, ← Category.assoc,
    Φι_coneα'' F K g p q (q + 1) n (n + 1) h rfl rfl,
    Linear.units_smul_comp, Category.assoc,
    Φι_d F K L p (q + 1) (n + 1) (n + 2) (by omega) (by omega),
    Linear.comp_units_smul, ← Category.assoc,
    Φι_d F K (mappingCone g) p q n (n + 1) h rfl, Preadditive.add_comp,
    Linear.units_smul_comp, Category.assoc, Category.assoc,
    Φι_coneα'' F K g (p + 1) q (q + 1) (n + 1) (n + 2) (by omega) rfl (by omega),
    Φι_coneα'' F K g p (q + 1) (q + 1 + 1) (n + 1) (n + 2) (by omega) rfl (by omega)]
  simp only [Linear.comp_units_smul, Preadditive.comp_add, Preadditive.comp_neg,
    smul_add, smul_smul, Int.negOnePow_succ, Units.neg_smul, Int.units_mul_self, one_smul,
    Cochain.zero_v, comp_zero]
  have h1 : (F.obj (K.X p)).map ((mappingCone.fst g).1.v q (q + 1) rfl) ≫
      (F.map (K.d p (p + 1))).app (L.X (q + 1)) =
      (F.map (K.d p (p + 1))).app ((mappingCone g).X q) ≫
        (F.obj (K.X (p + 1))).map ((mappingCone.fst g).1.v q (q + 1) rfl) :=
    (F.map (K.d p (p + 1))).naturality _
  have h2 := mappingCone.d_fst_v g q (q + 1) (q + 1 + 1) rfl rfl
  have hsum : (F.obj (K.X p)).map ((mappingCone.fst g).1.v q (q + 1) rfl) ≫
        (F.obj (K.X p)).map (L.d (q + 1) (q + 1 + 1)) ≫
          Φι F K L p (q + 1 + 1) (n + 2) (by omega) +
      (F.obj (K.X p)).map ((mappingCone g).d q (q + 1)) ≫
        (F.obj (K.X p)).map ((mappingCone.fst g).1.v (q + 1) (q + 1 + 1) rfl) ≫
          Φι F K L p (q + 1 + 1) (n + 2) (by omega) = 0 := by
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      ← Preadditive.add_comp, ← Functor.map_add, h2]
    simp
  have e2 : Int.negOnePow 2 = 1 := Int.negOnePow_even 2 even_two
  simp only [e2, one_smul]
  rw [reassoc_of% h1, ← hsum]
  abel

/-- `α'` as a cocycle. -/
private noncomputable def coneα'c : Cocycle (Φ F K (mappingCone g)) (Φ F K L) 1 :=
  Cocycle.mk (coneα' F K g) 2 rfl (coneα'_cocycle F K g)

/-- The equation making `α'`, `β'` define a map into `cone (Φ g)`. -/
private lemma coneβ'_eq : δ 0 1 (coneβ' F K g) +
    (coneα'c F K g).1.comp (Cochain.ofHom (Φmap F K g)) (add_zero 1) = 0 := by
  refine Cochain.ext _ _ fun n m hnm => ?_
  refine mapBifunctor.hom_ext fun p q h => ?_
  have h' : p + q = n := h
  obtain rfl : m = n + 1 := by omega
  rw [Cochain.add_v, δ_v 0 1 (by omega) _ n (n + 1) hnm n (n + 1) (by omega) (by omega),
    Cochain.comp_v _ _ (add_zero 1) n (n + 1) (n + 1) (by omega) (by omega),
    Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc,
    Φι_coneβ' F K g p q n h (add_zero n), Category.assoc,
    Φι_d F K L' p q n (n + 1) h rfl, Linear.comp_units_smul, ← Category.assoc,
    Φι_d F K (mappingCone g) p q n (n + 1) h rfl, Preadditive.add_comp, Linear.units_smul_comp,
    Category.assoc, Category.assoc,
    Φι_coneβ' F K g (p + 1) q (n + 1) (by omega) (add_zero _),
    Φι_coneβ' F K g p (q + 1) (n + 1) (by omega) (add_zero _)]
  have e1 : (coneα'c F K g).1 = coneα' F K g := rfl
  rw [e1, ← Category.assoc (Φι F K (mappingCone g) p q n h),
    Φι_coneα'' F K g p q (q + 1) n (n + 1) h rfl rfl,
    Linear.units_smul_comp, Category.assoc, Cochain.ofHom_v, Cochain.zero_v, comp_zero]
  simp only [Φmap, ι_mapBifunctorMap]
  simp only [Linear.comp_units_smul, Preadditive.comp_add, smul_add, smul_smul,
    Units.neg_smul, one_smul, Int.negOnePow_one, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, HomologicalComplex.id_f, neg_one_mul, neg_smul,
    Units.val_neg, Units.val_one]
  have h1 : (F.obj (K.X p)).map ((mappingCone.snd g).v q q (add_zero q)) ≫
      (F.map (K.d p (p + 1))).app (L'.X q) =
      (F.map (K.d p (p + 1))).app ((mappingCone g).X q) ≫
        (F.obj (K.X (p + 1))).map ((mappingCone.snd g).v q q (add_zero q)) :=
    (F.map (K.d p (p + 1))).naturality _
  have h2 := mappingCone.d_snd_v g q (q + 1) rfl
  have hsum : (F.obj (K.X p)).map ((mappingCone.snd g).v q q (add_zero q)) ≫
        (F.obj (K.X p)).map (L'.d q (q + 1)) ≫ Φι F K L' p (q + 1) (n + 1) (by omega) -
      (F.obj (K.X p)).map ((mappingCone g).d q (q + 1)) ≫
        (F.obj (K.X p)).map ((mappingCone.snd g).v (q + 1) (q + 1) (add_zero _)) ≫
          Φι F K L' p (q + 1) (n + 1) (by omega) +
      (F.obj (K.X p)).map ((mappingCone.fst g).1.v q (q + 1) rfl) ≫
        (F.obj (K.X p)).map (g.f (q + 1)) ≫ Φι F K L' p (q + 1) (n + 1) (by omega) = 0 := by
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, ← Preadditive.sub_comp, ← Preadditive.add_comp,
      ← Functor.map_sub, ← Functor.map_add, h2]
    simp
  rw [reassoc_of% h1]
  have key := congrArg (fun t => p.negOnePow • t) hsum
  simp only [smul_add, smul_sub, smul_zero] at key
  convert key using 1
  abel

/-- `cone (Φ g) ⟶ Φ (cone g)`. -/
private noncomputable def coneθ : mappingCone (Φmap F K g) ⟶ Φ F K (mappingCone g) :=
  mappingCone.desc (Φmap F K g) (coneα F K g)
    (mapBifunctorMap (𝟙 K) (mappingCone.inr g) F (ComplexShape.up ℤ)) (coneα_eq F K g)

/-- `Φ (cone g) ⟶ cone (Φ g)`. -/
private noncomputable def coneθ' : Φ F K (mappingCone g) ⟶ mappingCone (Φmap F K g) :=
  mappingCone.lift (Φmap F K g) (coneα'c F K g) (coneβ' F K g) (coneβ'_eq F K g)

/-- `θ' ≫ θ = 𝟙`. -/
private lemma coneθ'_θ : coneθ' F K g ≫ coneθ F K g = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine mapBifunctor.hom_ext fun p q h => ?_
  have h' : p + q = n := h
  rw [HomologicalComplex.comp_f, coneθ', mappingCone.lift_f _ _ _ _ n (n + 1) rfl,
    Preadditive.add_comp, Category.assoc, Category.assoc, coneθ,
    mappingCone.inl_v_desc_f, mappingCone.inr_f_desc_f]
  have e1 : (coneα'c F K g).1 = coneα' F K g := rfl
  rw [e1, Preadditive.comp_add, ← Category.assoc, ← Category.assoc,
    Φι_coneα'' F K g p q (q + 1) n (n + 1) h rfl rfl, Linear.units_smul_comp, Category.assoc,
    Φι_coneα' F K g p (q + 1) q (n + 1) n (by omega) rfl (by omega),
    Φι_coneβ' F K g p q n h (add_zero n), Category.assoc, ι_mapBifunctorMap]
  simp only [Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, Category.assoc,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, HomologicalComplex.id_f]
  have hid := (F.obj (K.X p)).congr_map (mappingCone.id_X g q (q + 1) rfl)
  rw [Functor.map_add, Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id] at hid
  rw [Category.comp_id, ← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, hid,
    Category.id_comp]

/-- `θ ≫ θ' = 𝟙`. -/
private lemma coneθ_θ' : coneθ F K g ≫ coneθ' F K g = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.comp_f]
  refine (mappingCone.ext_from_iff _ (n + 1) n rfl _ _).2 ⟨?_, ?_⟩
  · refine (mappingCone.ext_to_iff _ n (n + 1) rfl _ _).2 ⟨?_, ?_⟩
    · simp only [Category.assoc, HomologicalComplex.id_f, Category.id_comp]
      unfold coneθ coneθ'
      rw [mappingCone.inl_v_desc_f_assoc, mappingCone.lift_f_fst_v, mappingCone.inl_v_fst_v]
      refine mapBifunctor.hom_ext fun p q h => ?_
      have h' : p + q = n + 1 := h
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have e1 : (coneα'c F K g).1 = coneα' F K g := rfl
      rw [e1, ← Category.assoc, Φι_coneα' F K g p (q' + 1) q' (n + 1) n h rfl (by omega),
        Linear.units_smul_comp, Category.assoc,
        Φι_coneα'' F K g p q' (q' + 1) n (n + 1) (by omega) rfl rfl]
      simp only [Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, Category.assoc,
        ← Functor.map_comp_assoc, mappingCone.inl_v_fst_v, CategoryTheory.Functor.map_id,
        Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, HomologicalComplex.id_f, Category.id_comp]
      unfold coneθ coneθ'
      rw [mappingCone.inl_v_desc_f_assoc, mappingCone.lift_f_snd_v, mappingCone.inl_v_snd_v]
      refine mapBifunctor.hom_ext fun p q h => ?_
      have h' : p + q = n + 1 := h
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [← Category.assoc, Φι_coneα' F K g p (q' + 1) q' (n + 1) n h rfl (by omega),
        Linear.units_smul_comp, Category.assoc,
        Φι_coneβ' F K g p q' n (by omega) (add_zero n)]
      simp [← Functor.map_comp_assoc, mappingCone.inl_v_snd_v]
  · refine (mappingCone.ext_to_iff _ n (n + 1) rfl _ _).2 ⟨?_, ?_⟩
    · simp only [Category.assoc, HomologicalComplex.id_f, Category.id_comp]
      unfold coneθ coneθ'
      rw [mappingCone.inr_f_desc_f_assoc, mappingCone.lift_f_fst_v, mappingCone.inr_f_fst_v]
      refine mapBifunctor.hom_ext fun p q h => ?_
      have h' : p + q = n := h
      rw [← Category.assoc, ι_mapBifunctorMap, Category.assoc, Category.assoc]
      have e1 : (coneα'c F K g).1 = coneα' F K g := rfl
      rw [e1, Φι_coneα'' F K g p q (q + 1) n (n + 1) h rfl rfl]
      simp [← Functor.map_comp_assoc, mappingCone.inr_f_fst_v]
    · simp only [Category.assoc, HomologicalComplex.id_f, Category.id_comp]
      unfold coneθ coneθ'
      rw [mappingCone.inr_f_desc_f_assoc, mappingCone.lift_f_snd_v, mappingCone.inr_f_snd_v]
      refine mapBifunctor.hom_ext fun p q h => ?_
      have h' : p + q = n := h
      rw [← Category.assoc, ι_mapBifunctorMap, Category.assoc, Category.assoc,
        Φι_coneβ' F K g p q n h (add_zero n)]
      simp [← Functor.map_comp_assoc, mappingCone.inr_f_snd_v]

/-- `K ⊗ cone g ≅ cone (K ⊗ g)` for a bifunctor `F` over `ComplexShape.up ℤ`. -/
noncomputable def coneIso₂ : Φ F K (mappingCone g) ≅ mappingCone (Φmap F K g) where
  hom := coneθ' F K g
  inv := coneθ F K g
  hom_inv_id := coneθ'_θ F K g
  inv_hom_id := coneθ_θ' F K g

end ConeIso

section ShiftIso

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (K₁ : CochainComplex C₁ ℤ) (K₂ : CochainComplex C₂ ℤ)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ (X₁ : C₁), (F.obj X₁).PreservesZeroMorphisms] (x : ℤ)

-- Mathlib's `CochainComplex.mapBifunctorShift₁Iso` is proved with these two options; we do not
-- import that file (it would capture the dot-notation `K.mapBifunctor` used by `tensorC`).
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Shifting the first complex shifts the bicomplex in the first index. -/
private def shiftBicomplexIso :
    ((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj
      (K₁⟦x⟧)).obj K₂ ≅
    (HomologicalComplex₂.shiftFunctor₁ D x).obj
      (((F.mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K₁).obj
        K₂) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intros
    ext
    dsimp
    simp only [Linear.comp_units_smul, Category.id_comp, Functor.map_units_smul,
      NatTrans.app_units_zsmul, Category.comp_id])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The total complex of a shifted first factor is the shifted total complex. -/
noncomputable def mapBifunctorShift₁IsoAux
    [HomologicalComplex.HasMapBifunctor K₁ K₂ F (ComplexShape.up ℤ)]
    [HomologicalComplex.HasMapBifunctor (K₁⟦x⟧) K₂ F (ComplexShape.up ℤ)] :
    HomologicalComplex.mapBifunctor (K₁⟦x⟧) K₂ F (ComplexShape.up ℤ) ≅
      (HomologicalComplex.mapBifunctor K₁ K₂ F (ComplexShape.up ℤ))⟦x⟧ :=
  HomologicalComplex₂.total.mapIso (shiftBicomplexIso K₁ K₂ F x) _ ≪≫
    (((F.mapBifunctorHomologicalComplex _ _).obj K₁).obj K₂).totalShift₁Iso x

end ShiftIso

end TotAux

end Cohesive
