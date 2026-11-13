import Cohesivemodules.Sheaf.FlatBasic

set_option linter.style.header false

/-!
# S8: tensor products and K-flat complexes (part 2 of 2)

Split from `Sheaf/Flat.lean` for size;
continues `Sheaf/FlatBasic.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite Limits MonoidalCategory TopologicalSpace
section Space
variable {X : Type} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0})

/-- **S8.f.** Flatness restricts to opens: for `N' ↪ N` on `U`, `j_! N' ↪ j_! N` (S5.b), tensor
with `M` and restrict back (`restrTensorIso`, unit iso of S5.b). -/
theorem IsFlat.restr {M : Mod (ringOf R)} (hM : IsFlat R M) (U : TopologicalSpace.Opens X) :
    IsFlat (R.over U) ((restr (ringOf R) U).obj M) := by
  refine ⟨fun {N' N} f hf => ?_⟩
  -- `K = (M|U) ⊗ -`
  have := hf
  have hpf : PreservesFiniteLimits (extZero (ringOf R) U) := extZero_preservesFiniteLimits _ _
  have hpc : PreservesLimitsOfShape WalkingCospan (extZero (ringOf R) U) := inferInstance
  have hpm : (extZero (ringOf R) U).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have hmono : Mono ((extZero (ringOf R) U).map f) := by
    exact @hpm.preserves N' N f hf
  have h1 : Mono (((tensorBifunctor R).obj M).map ((extZero (ringOf R) U).map f)) :=
    hM.1 _
  have h2 : Mono ((Cohesive.restr (ringOf R) U).map
      (((tensorBifunctor R).obj M).map ((extZero (ringOf R) U).map f))) := inferInstance
  have hnat := restrTensorIso_naturality R U M ((extZero (ringOf R) U).map f)
  -- `W = (M|U ⊗ -)((j_! f)|U)` is a monomorphism, being conjugate to `(M ⊗ j_! f)|U`
  have hW : Mono (((tensorBifunctor (R.over U)).obj ((Cohesive.restr (ringOf R) U).obj M)).map
      ((Cohesive.restr (ringOf R) U).map ((extZero (ringOf R) U).map f))) := by
    have e : ((tensorBifunctor (R.over U)).obj ((Cohesive.restr (ringOf R) U).obj M)).map
        ((Cohesive.restr (ringOf R) U).map ((extZero (ringOf R) U).map f)) =
        (restrTensorIso R U M ((extZero (ringOf R) U).obj N')).inv ≫
          ((Cohesive.restr (ringOf R) U).map
            (((tensorBifunctor R).obj M).map ((extZero (ringOf R) U).map f)) ≫
            (restrTensorIso R U M ((extZero (ringOf R) U).obj N)).hom) :=
      (Iso.eq_inv_comp _).2 hnat.symm
    rw [e]
    have hm1 : Mono (restrTensorIso R U M ((extZero (ringOf R) U).obj N)).hom :=
      @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom _)
    have hm2 : Mono (restrTensorIso R U M ((extZero (ringOf R) U).obj N')).inv :=
      @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_inv _)
    have h3 := @mono_comp _ _ _ _ _ ((Cohesive.restr (ringOf R) U).map
            (((tensorBifunctor R).obj M).map ((extZero (ringOf R) U).map f))) h2
            (restrTensorIso R U M ((extZero (ringOf R) U).obj N)).hom hm1
    exact @mono_comp _ _ _ _ _ (restrTensorIso R U M ((extZero (ringOf R) U).obj N')).inv hm2
      _ h3
  have hu := isIso_extZeroAdj_unit (ringOf R) U N'
  have hnu := (extZeroAdj (ringOf R) U).unit.naturality f
  let K := (tensorBifunctor (R.over U)).obj ((Cohesive.restr (ringOf R) U).obj M)
  have hK : IsIso (K.map ((extZeroAdj (ringOf R) U).unit.app N')) :=
    (K.mapIso (@asIso _ _ _ _ ((extZeroAdj (ringOf R) U).unit.app N') hu)).isIso_hom
  have e1 : K.map f ≫ K.map ((extZeroAdj (ringOf R) U).unit.app N) =
      K.map ((extZeroAdj (ringOf R) U).unit.app N') ≫
        K.map ((Cohesive.restr (ringOf R) U).map ((extZero (ringOf R) U).map f)) :=
    (K.map_comp _ _).symm.trans ((congrArg K.map hnu).trans (K.map_comp _ _))
  have hm1 : Mono (K.map ((extZeroAdj (ringOf R) U).unit.app N')) :=
    @IsIso.mono_of_iso _ _ _ _ _ hK
  have hm2 := @mono_comp _ _ _ _ _ (K.map ((extZeroAdj (ringOf R) U).unit.app N')) hm1
    (K.map ((Cohesive.restr (ringOf R) U).map ((extZero (ringOf R) U).map f))) hW
  rw [← e1] at hm2
  exact @mono_of_mono _ _ _ _ _ (K.map f) (K.map ((extZeroAdj (ringOf R) U).unit.app N)) hm2

/-- Naturality of a morphism of sheaves of modules with respect to restriction of sections. -/
private lemma mres_map_aux {M N : Mod (ringOf R)} (φ : M ⟶ N) {A B : TopologicalSpace.Opens X}
    (h : B ≤ A) (s : M.val.obj (op A)) :
    φ.val.app (op B) (mres M h s) = mres N h (φ.val.app (op A) s) :=
  congr(ModuleCat.Hom.hom $(φ.val.naturality (homOfLE h).op) s)

/-- A section of a sheaf of modules that is locally zero is zero. -/
private lemma sec_eq_zero_of_locally (c : Mod (ringOf R)) {V : TopologicalSpace.Opens X}
    (s : c.val.obj (op V))
    (h : ∀ x ∈ V, ∃ (W : TopologicalSpace.Opens X) (hW : W ≤ V), x ∈ W ∧ mres c hW s = 0) :
    s = 0 := by
  have hsep := Presheaf.IsSheaf.isSeparated c.isSheaf
  obtain ⟨y, hy⟩ : ∃ y : c.val.presheaf.obj (op V), y = s := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : c.val.presheaf.obj (op V), z = 0 := ⟨_, rfl⟩
  suffices key : y = z by
    rw [hy, hz] at key
    exact key
  refine hsep V
    ⟨fun {Y} f => c.val.presheaf.map f.op y = c.val.presheaf.map f.op z, ?_⟩ ?_ y z ?_
  · intro Y Z f hf g
    simp only at hf ⊢
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hf]
    rfl
  · intro x hx
    obtain ⟨W, hW, hxW, hw⟩ := h x hx
    refine ⟨W, homOfLE hW, ?_, hxW⟩
    show c.val.map (homOfLE hW).op y = c.val.map (homOfLE hW).op z
    rw [hy, hz]
    exact hw.trans (map_zero _).symm
  · intro Y f hf
    exact hf

/-- Restricting twice. -/
private lemma mres_mres_aux (c : Mod (ringOf R)) {A B D : TopologicalSpace.Opens X}
    (h1 : B ≤ A) (h2 : D ≤ B) (s : c.val.obj (op A)) :
    mres c h2 (mres c h1 s) = mres c (h2.trans h1) s :=
  (c.val.map_comp_apply (homOfLE h1).op (homOfLE h2).op s).symm

/-- If sections of `P` vanish locally near `x`, so do sections of the presheaf tensor product
`P ⊗ N'`. -/
private lemma tensor_presheaf_locally_zero (P N' : PresheafOfModulesOfCommRing.{0} R.obj) (x : X)
    (hP : ∀ {W : TopologicalSpace.Opens X} (r : P.obj (op W)), x ∈ W →
      ∃ (W₂ : TopologicalSpace.Opens X) (h : W₂ ≤ W), x ∈ W₂ ∧
        (P.map (homOfLE h).op).hom r = 0)
    {W₁ : TopologicalSpace.Opens X} (q : (P ⊗ N').obj (op W₁)) (hx : x ∈ W₁) :
    ∃ (W₂ : TopologicalSpace.Opens X) (h : W₂ ≤ W₁), x ∈ W₂ ∧
      ((P ⊗ N').map (homOfLE h).op).hom q = 0 := by
  induction q using TensorProduct.inductionOn with
  | tmul r n =>
    obtain ⟨W₂, h, hx₂, hr⟩ := hP r hx
    refine ⟨W₂, h, hx₂, ?_⟩
    show (P.map (homOfLE h).op).hom r ⊗ₜ[R.obj.obj (op W₂)] (N'.map (homOfLE h).op).hom n = 0
    rw [hr, TensorProduct.zero_tmul]
  | add q q' hq hq' =>
    obtain ⟨W₂, h₂, hx₂, hz⟩ := hq
    obtain ⟨W₃, h₃, hx₃, hz'⟩ := hq'
    refine ⟨W₂ ⊓ W₃, inf_le_left.trans h₂, ⟨hx₂, hx₃⟩, ?_⟩
    have e1 : ((P ⊗ N').map (homOfLE (inf_le_left.trans h₂)).op).hom q =
        ((P ⊗ N').map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op).hom
          (((P ⊗ N').map (homOfLE h₂).op).hom q) :=
      PresheafOfModules.map_comp_apply (P ⊗ N') (homOfLE h₂).op (homOfLE inf_le_left).op q
    have e2 : ((P ⊗ N').map (homOfLE (inf_le_right.trans h₃)).op).hom q' =
        ((P ⊗ N').map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op).hom
          (((P ⊗ N').map (homOfLE h₃).op).hom q') :=
      PresheafOfModules.map_comp_apply (P ⊗ N') (homOfLE h₃).op (homOfLE inf_le_right).op q'
    have e3 := map_add ((P ⊗ N').map (homOfLE (inf_le_left.trans h₂ : W₂ ⊓ W₃ ≤ W₁)).op).hom q q'
    have z1 := e1.trans ((congrArg ((P ⊗ N').map
      (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op).hom hz).trans (map_zero _))
    have z2 := e2.trans ((congrArg ((P ⊗ N').map
      (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op).hom hz').trans (map_zero _))
    exact e3.trans ((congrArg₂ _ z1 z2).trans (add_zero _))

/-- Sections of `(j_! M) ⊗ N'` vanish near every point outside `U`: locally they come from
the presheaf tensor product, whose elements are finite sums of pure tensors with a factor in
`j_! M`. -/
private lemma tensor_extZero_locally_zero (U : TopologicalSpace.Opens X)
    (M : Mod ((ringOf R).over U)) (N' : Mod (ringOf R)) {V : TopologicalSpace.Opens X}
    (s : (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj M)).obj N').val.obj (op V))
    {x : X} (hxV : x ∈ V) (hxU : x ∉ U) :
    ∃ (W : TopologicalSpace.Opens X) (h : W ≤ V), x ∈ W ∧
      mres (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj M)).obj N') h s = 0 := by
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (unitR R (MonoidalCategory.tensorObj
        (C := PresheafOfModulesOfCommRing.{0} R.obj) ((extZero (ringOf R) U).obj M).val N'.val))) :=
    (inferInstance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (toSheafify _ (MonoidalCategory.tensorObj
        (C := PresheafOfModulesOfCommRing.{0} R.obj) ((extZero (ringOf R) U).obj M).val
          N'.val).presheaf))
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (unitR R (MonoidalCategory.tensorObj
      (C := PresheafOfModulesOfCommRing.{0} R.obj) ((extZero (ringOf R) U).obj M).val N'.val)))
    (U := op V) s
  obtain ⟨W₁, g, ⟨q, hq⟩, hxW₁⟩ := (Opens.mem_grothendieckTopology X).1 hmem x hxV
  have hle : W₁ ≤ V := leOfHom g
  obtain ⟨W₂, h₂, hx₂, hz⟩ := tensor_presheaf_locally_zero R
    ((extZero (ringOf R) U).obj M).val N'.val x
    (fun {W} r hxW => extZero_locally_zero (ringOf R) U M r hxW hxU) q hxW₁
  refine ⟨W₂, h₂.trans hle, hx₂, ?_⟩
  have h1 := PresheafOfModules.naturality_apply (unitR R (MonoidalCategory.tensorObj
    (C := PresheafOfModulesOfCommRing.{0} R.obj) ((extZero (ringOf R) U).obj M).val N'.val))
    (homOfLE h₂).op q
  have e1 : mres (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj M)).obj N') (h₂.trans hle) s
      = mres (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj M)).obj N') h₂
        (mres (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj M)).obj N') hle s) :=
    (mres_mres_aux R _ hle h₂ s).symm
  have e2 : mres (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj M)).obj N') hle s =
      (unitR R (MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj)
        ((extZero (ringOf R) U).obj M).val N'.val)).app (op W₁) q := hq.symm
  rw [e1, e2]
  exact h1.symm.trans ((congrArg
    ((unitR R (MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj)
      ((extZero (ringOf R) U).obj M).val N'.val)).app (op W₂)).hom hz).trans (map_zero _))

/-- A morphism conjugate to a monomorphism by isomorphisms is a monomorphism. -/
private lemma mono_of_conj {𝒞 : Type*} [Category 𝒞] {a b c d : 𝒞} (i : a ≅ c) (j : b ≅ d)
    (m : a ⟶ b) (hm : Mono m) (m' : c ⟶ d) (h : i.hom ≫ m' = m ≫ j.hom) : Mono m' := by
  have : m' = i.inv ≫ m ≫ j.hom := by rw [← h, Iso.inv_hom_id_assoc]
  rw [this]
  have := hm
  infer_instance

/-- Over `U`, `(M ⊗ -)` for `M = j_! R|U` preserves monomorphisms after restriction to `U`:
`(j_! R|U)|U ≅ R|U` is flat. -/
private lemma mono_restr_tensor_extZero_unit (U : TopologicalSpace.Opens X)
    {N' N : Mod (ringOf R)} (f : N' ⟶ N) [Mono f] :
    Mono ((Cohesive.restr (ringOf R) U).map
      (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj (SheafOfModules.unit _))).map f)) := by
  have hεiso := isIso_extZeroAdj_unit (ringOf R) U (SheafOfModules.unit _)
  let e := @asIso _ _ _ _ _ hεiso
  have hflat := isFlat_unit (R.over U)
  have hpf : PreservesFiniteLimits (Cohesive.restr (ringOf R) U) := inferInstance
  have hpc : PreservesLimitsOfShape WalkingCospan (Cohesive.restr (ringOf R) U) := inferInstance
  have hpm : (Cohesive.restr (ringOf R) U).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have hg : Mono ((Cohesive.restr (ringOf R) U).map f) := @hpm.preserves N' N f inferInstance
  have hpmU : ((tensorBifunctor (R.over U)).obj
      (SheafOfModules.unit ((ringOf R).over U))).PreservesMonomorphisms := hflat
  have h1 : Mono (((tensorBifunctor (R.over U)).obj (SheafOfModules.unit _)).map
      ((Cohesive.restr (ringOf R) U).map f)) := @hpmU.preserves _ _ _ hg
  have hW : Mono (((tensorBifunctor (R.over U)).obj
      ((Cohesive.restr (ringOf R) U).obj ((extZero (ringOf R) U).obj
        (SheafOfModules.unit _)))).map ((Cohesive.restr (ringOf R) U).map f)) :=
    mono_of_conj (((tensorBifunctor (R.over U)).mapIso e).app _)
      (((tensorBifunctor (R.over U)).mapIso e).app _) _ h1 _
      (((tensorBifunctor (R.over U)).map e.hom).naturality _).symm
  have hnat := restrTensorIso_naturality R U
    ((extZero (ringOf R) U).obj (SheafOfModules.unit _)) f
  exact mono_of_conj (restrTensorIso R U _ _).symm (restrTensorIso R U _ _).symm _ hW _
    ((Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 hnat).trans (Category.assoc _ _ _)))

/-- **S8.b.** Extension by zero of `R|U` is flat (stalks: `R_x` for `x ∈ U`, `0` otherwise;
here through S5.b and the compatibility of tensor products with restriction). -/
theorem isFlat_extZero_unit (U : TopologicalSpace.Opens X) :
    IsFlat R ((extZero (ringOf R) U).obj (SheafOfModules.unit _)) := by
  refine ⟨fun {N' N} f hf => ?_⟩
  have := hf
  refine Functor.mono_of_mono_map (SheafOfModules.forget (ringOf R)) ?_
  refine PresheafOfModules.mono_of_injective fun V => ?_
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨V⟩ := V
  refine sec_eq_zero_of_locally R
    (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj (SheafOfModules.unit _))).obj N') s
    fun x hx => ?_
  by_cases hxU : x ∈ U
  · refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
    have hmono := mono_restr_tensor_extZero_unit R U f
    have hmono' : Mono ((SheafOfModules.forget (ringOf (R.over U))).map
        ((Cohesive.restr (ringOf R) U).map
          (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj
            (SheafOfModules.unit _))).map f))) :=
      @Functor.map_mono _ _ _ _ (SheafOfModules.forget (ringOf (R.over U))) _ _ _ _ hmono
    have hinj := PresheafOfModules.injective_of_mono
      ((SheafOfModules.forget (ringOf (R.over U))).map
        ((Cohesive.restr (ringOf R) U).map
          (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj
            (SheafOfModules.unit _))).map f)))
      (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))
    have h0 := (mres_map_aux R
      (((tensorBifunctor R).obj ((extZero (ringOf R) U).obj (SheafOfModules.unit _))).map f)
      (inf_le_left : V ⊓ U ≤ V) s).trans ((congrArg _ hs).trans (map_zero _))
    exact hinj (h0.trans (map_zero _).symm)
  · exact tensor_extZero_locally_zero R U _ N' s hx hxU

/-- General form of `tensor_extZero_locally_zero`: if sections of `M` vanish near points outside
`U`, so do sections of `M ⊗ N'`. -/
private lemma tensor_locally_zero_of (U : TopologicalSpace.Opens X) (M : Mod (ringOf R))
    (hM : ∀ {V : TopologicalSpace.Opens X} (s : M.val.obj (op V)) {x : X}, x ∈ V → x ∉ U →
      ∃ (W : TopologicalSpace.Opens X) (h : W ≤ V), x ∈ W ∧ mres M h s = 0)
    (N' : Mod (ringOf R)) {V : TopologicalSpace.Opens X}
    (s : (((tensorBifunctor R).obj M).obj N').val.obj (op V))
    {x : X} (hxV : x ∈ V) (hxU : x ∉ U) :
    ∃ (W : TopologicalSpace.Opens X) (h : W ≤ V), x ∈ W ∧
      mres (((tensorBifunctor R).obj M).obj N') h s = 0 := by
  have hsurj : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf _).map (unitR R (MonoidalCategory.tensorObj
        (C := PresheafOfModulesOfCommRing.{0} R.obj) M.val N'.val))) :=
    (inferInstance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (toSheafify _ (MonoidalCategory.tensorObj
        (C := PresheafOfModulesOfCommRing.{0} R.obj) M.val N'.val).presheaf))
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (unitR R (MonoidalCategory.tensorObj
      (C := PresheafOfModulesOfCommRing.{0} R.obj) M.val N'.val)))
    (U := op V) s
  obtain ⟨W₁, g, ⟨q, hq⟩, hxW₁⟩ := (Opens.mem_grothendieckTopology X).1 hmem x hxV
  have hle : W₁ ≤ V := leOfHom g
  obtain ⟨W₂, h₂, hx₂, hz⟩ := tensor_presheaf_locally_zero R M.val N'.val x
    (fun {W} r hxW => hM r hxW hxU) q hxW₁
  refine ⟨W₂, h₂.trans hle, hx₂, ?_⟩
  have h1 := PresheafOfModules.naturality_apply (unitR R (MonoidalCategory.tensorObj
    (C := PresheafOfModulesOfCommRing.{0} R.obj) M.val N'.val)) (homOfLE h₂).op q
  have e1 : mres (((tensorBifunctor R).obj M).obj N') (h₂.trans hle) s
      = mres (((tensorBifunctor R).obj M).obj N') h₂
        (mres (((tensorBifunctor R).obj M).obj N') hle s) :=
    (mres_mres_aux R _ hle h₂ s).symm
  have e2 : mres (((tensorBifunctor R).obj M).obj N') hle s =
      (unitR R (MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj)
        M.val N'.val)).app (op W₁) q := hq.symm
  rw [e1, e2]
  exact h1.symm.trans ((congrArg
    ((unitR R (MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} R.obj)
      M.val N'.val)).app (op W₂)).hom hz).trans (map_zero _))

/-- If `M|U` is flat, `(M ⊗ -)` preserves monomorphisms after restriction to `U`. -/
private lemma mono_restr_tensor_of_flat (U : TopologicalSpace.Opens X) (M : Mod (ringOf R))
    (hU : IsFlat (R.over U) ((restr (ringOf R) U).obj M))
    {N' N : Mod (ringOf R)} (f : N' ⟶ N) [Mono f] :
    Mono ((Cohesive.restr (ringOf R) U).map (((tensorBifunctor R).obj M).map f)) := by
  have hpf : PreservesFiniteLimits (Cohesive.restr (ringOf R) U) := inferInstance
  have hpc : PreservesLimitsOfShape WalkingCospan (Cohesive.restr (ringOf R) U) := inferInstance
  have hpm : (Cohesive.restr (ringOf R) U).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have hg : Mono ((Cohesive.restr (ringOf R) U).map f) := @hpm.preserves N' N f inferInstance
  have hpmU : ((tensorBifunctor (R.over U)).obj
      ((Cohesive.restr (ringOf R) U).obj M)).PreservesMonomorphisms := hU
  have hW : Mono (((tensorBifunctor (R.over U)).obj
      ((Cohesive.restr (ringOf R) U).obj M)).map ((Cohesive.restr (ringOf R) U).map f)) :=
    @hpmU.preserves _ _ _ hg
  have hnat := restrTensorIso_naturality R U M f
  exact mono_of_conj (restrTensorIso R U _ _).symm (restrTensorIso R U _ _).symm _ hW _
    ((Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2 hnat).trans (Category.assoc _ _ _)))

/-- **S8.b, general form (Z3.l, blueprint §11 v1.20 item 4).** A sheaf of modules `M` on `X` whose
sections vanish near every point outside the open `U`, and whose restriction to `U` is flat, is
flat. The proof of `isFlat_extZero_unit` with `j_! R|U` replaced by `M`: sections of `M ⊗ N'`
vanish near points outside `U` (locally they are sums of pure tensors with a factor in `M`), and
on `U` the kernel vanishes by flatness of `M|U`. -/
theorem isFlat_of_locally_zero (U : TopologicalSpace.Opens X) (M : Mod (ringOf R))
    (hM : ∀ {V : TopologicalSpace.Opens X} (s : M.val.obj (op V)) {x : X}, x ∈ V → x ∉ U →
      ∃ (W : TopologicalSpace.Opens X) (h : W ≤ V), x ∈ W ∧ mres M h s = 0)
    (hU : IsFlat (R.over U) ((restr (ringOf R) U).obj M)) : IsFlat R M := by
  refine ⟨fun {N' N} f hf => ?_⟩
  have := hf
  refine Functor.mono_of_mono_map (SheafOfModules.forget (ringOf R)) ?_
  refine PresheafOfModules.mono_of_injective fun V => ?_
  rw [injective_iff_map_eq_zero]
  intro s hs
  obtain ⟨V⟩ := V
  refine sec_eq_zero_of_locally R (((tensorBifunctor R).obj M).obj N') s fun x hx => ?_
  by_cases hxU : x ∈ U
  · refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
    have hmono := mono_restr_tensor_of_flat R U M hU f
    have hmono' : Mono ((SheafOfModules.forget (ringOf (R.over U))).map
        ((Cohesive.restr (ringOf R) U).map (((tensorBifunctor R).obj M).map f))) :=
      @Functor.map_mono _ _ _ _ (SheafOfModules.forget (ringOf (R.over U))) _ _ _ _ hmono
    have hinj := PresheafOfModules.injective_of_mono
      ((SheafOfModules.forget (ringOf (R.over U))).map
        ((Cohesive.restr (ringOf R) U).map (((tensorBifunctor R).obj M).map f)))
      (op (Over.mk (homOfLE (inf_le_right : V ⊓ U ≤ U))))
    have h0 := (mres_map_aux R (((tensorBifunctor R).obj M).map f)
      (inf_le_left : V ⊓ U ≤ V) s).trans ((congrArg _ hs).trans (map_zero _))
    exact hinj (h0.trans (map_zero _).symm)
  · exact tensor_locally_zero_of R U M hM N' s hx hxU

end Space

end Cohesive
