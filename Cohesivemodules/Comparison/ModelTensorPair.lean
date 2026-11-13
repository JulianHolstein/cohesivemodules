import Cohesivemodules.Comparison.ModelBC

set_option linter.style.header false

/-!
# C7.d (part 1): the pairing `a ⊗ k ↦ a ⊗ η k`

Blueprint item C7.d (§4, v1.11); first of the files `ModelTensor{Pair, Kappa, Coord, Iso}` and
`ModelTensor` (split for size, 27 Oct 2026). The presheaf pairing `φPre : 𝒜^q ⊗ K^p ⟶ T^{q+p}`,
(the dual-basis data for `𝒜^q` are in `ModelDual.lean`). Auxiliary declarations for
`exists_TC_iso_tensorC`, not used elsewhere.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X) (K : CochainComplex (Mod (P.R.over U)) ℤ)

/-! ### The pairing `a ⊗ k ↦ a ⊗ η k` -/

/-- The element `a ⊗ η k` of the total module of `F_K`, for `a ∈ 𝒜^q(V)`, `k ∈ K^p(V)`. -/
def pairElt (q p : ℤ) (V : (Over U)ᵒᵖ) (a : P.PieceO q V.unop.left)
    (k : (K.X p).val.obj V) : P.TTot U (P.FK U K) V :=
  Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) (a.1 : P.D.A V.unop.left)
    (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k))

/-- `a ⊗ η k` has total degree `q + p`. -/
theorem pairElt_mem (q p n : ℤ) (h : q + p = n) (V : (Over U)ᵒᵖ)
    (a : P.PieceO q V.unop.left) (k : (K.X p).val.obj V) :
    P.pairElt U K q p V a k ∈ P.tDeg U (P.FK U K) n V := by
  have := tmul_mem_totDeg (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U (P.FK U K) · V))
    a.2 (P.bcη U K p V k)
  rw [h] at this
  exact this

/-- `a ⊗ η k` is additive in `a`. -/
theorem pairElt_add_left (q p : ℤ) (V : (Over U)ᵒᵖ) (a a' : P.PieceO q V.unop.left)
    (k : (K.X p).val.obj V) :
    P.pairElt U K q p V (a + a') k = P.pairElt U K q p V a k + P.pairElt U K q p V a' k :=
  Tot.add_tmul _ _ _

/-- `a ⊗ η k` is additive in `k`. -/
theorem pairElt_add_right (q p : ℤ) (V : (Over U)ᵒᵖ) (a : P.PieceO q V.unop.left)
    (k k' : (K.X p).val.obj V) :
    P.pairElt U K q p V a (k + k') = P.pairElt U K q p V a k + P.pairElt U K q p V a k' := by
  unfold pairElt
  rw [map_add, map_add, Tot.tmul_add]

/-- `O(V)`-scalars on the left factor of `a ⊗ η k`. -/
theorem pairElt_smul_left (q p : ℤ) (V : (Over U)ᵒᵖ)
    (r : P.O.obj.obj (op V.unop.left)) (a : P.PieceO q V.unop.left) (k : (K.X p).val.obj V) :
    P.pairElt U K q p V (r • a) k = (P.ρ V.unop.left r : P.D.A V.unop.left) •
      P.pairElt U K q p V a k := by
  unfold pairElt
  rw [Tot.smul_tmul]
  rfl

/-- `O(V)`-scalars on the right factor of `a ⊗ η k`. -/
theorem pairElt_smul_right (q p : ℤ) (V : (Over U)ᵒᵖ) (r : (P.R.over U).obj.obj V)
    (a : P.PieceO q V.unop.left) (k : (K.X p).val.obj V) :
    P.pairElt U K q p V a (r • k) =
      (P.ρ V.unop.left (show P.O.obj.obj (op V.unop.left) from r) : P.D.A V.unop.left) •
      P.pairElt U K q p V a k := by
  have h := (((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val.app V).hom.map_smul r k
  have h2 : P.bcη U K p V (r • k) = (P.ρ V.unop.left r : ↥(P.D.𝒜 V.unop.left 0)) •
      P.bcη U K p V k := h
  unfold pairElt
  rw [h2, map_smul, Tot.tmul_smul0, Tot.smul_tmul]
  exact congrArg (fun x => Tot.tmul _ _ x _) (GCDga.central _ (P.ρ V.unop.left r).2 _).symm

/-- `𝒜^q|U`, as a sheaf of `R|U`-modules. -/
abbrev AqU (q : ℤ) : Mod (P.R.over U) := (restr P.R U).obj (P.dgaO q)

/-- The sectionwise tensor presheaf `V ↦ 𝒜^q(V) ⊗_{O(V)} K^p(V)`. -/
abbrev PreT (q p : ℤ) : PresheafOfModules.{0} (ringOf (P.O.over U)).obj :=
  MonoidalCategory.tensorObj (C := PresheafOfModulesOfCommRing.{0} (P.O.over U).obj)
    (P.AqU U q).val (K.X p).val

/-- The pairing `a ⊗ k ↦ a ⊗ η k` on sections over `V`. -/
def φV (q p n : ℤ) (h : q + p = n) (V : (Over U)ᵒᵖ) :
    (P.PreT U K q p).obj V ⟶ (P.TPre U (P.FK U K) n).obj V :=
  ModuleCat.MonoidalCategory.tensorLift
    (fun (a : (P.AqU U q).val.obj V) (k : (K.X p).val.obj V) =>
      (⟨P.pairElt U K q p V a k, P.pairElt_mem U K q p n h V a k⟩ : P.TSec U (P.FK U K) n V))
    (fun a a' k => Subtype.ext (P.pairElt_add_left U K q p V a a' k))
    (fun r a k => Subtype.ext (P.pairElt_smul_left U K q p V r a k))
    (fun a k k' => Subtype.ext (P.pairElt_add_right U K q p V a k k'))
    (fun r a k => Subtype.ext (P.pairElt_smul_right U K q p V r a k))

/-- `φV` on pure tensors. -/
theorem φV_tmul (q p n : ℤ) (h : q + p = n) (V : (Over U)ᵒᵖ)
    (a : (P.AqU U q).val.obj V) (k : (K.X p).val.obj V) :
    ((P.φV U K q p n h V).hom (a ⊗ₜ k)).1 = P.pairElt U K q p V a k := rfl

/-- `pairElt` commutes with restriction. -/
theorem pairElt_res (q p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (a : P.PieceO q V.unop.left) (k : (K.X p).val.obj V) :
    P.pairElt U K q p W (P.resPiece q (leOfHom f.unop.left) a) ((K.X p).val.map f k) =
      P.tRes U (P.FK U K) f (P.pairElt U K q p V a k) := by
  have hn : P.bcη U K p W ((K.X p).val.map f k) = P.fRes U (P.FK U K) p f (P.bcη U K p V k) :=
    (PresheafOfModules.naturality_apply
      ((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val f k)
  unfold pairElt
  show Tot.tmul (P.D.𝒜 W.unop.left) (P.FSec U (P.FK U K) · W) _
      (lof ↥(P.D.𝒜 W.unop.left 0) ℤ (P.FSec U (P.FK U K) · W) p
        (P.bcη U K p W ((K.X p).val.map f k))) =
    totMapAlong (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U (P.FK U K) p f)
      (fun p => P.fRes_smul U (P.FK U K) f p)
      (Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) (a.1 : P.D.A V.unop.left)
        (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k)))
  rw [totMapAlong_tmul, DirectSum.lof_eq_of, DirectSum.lof_eq_of, famMap_of, hn]
  rfl

/-- The pairing as a morphism of presheaves of modules `𝒜^q ⊗ K^p ⟶ T^{q+p}`. -/
def φPre [CompactSpace X] (q p n : ℤ) (h : q + p = n) :
    P.PreT U K q p ⟶ (SheafOfModules.forget _).obj (P.TSh U (P.FK U K) n) where
  app V := P.φV U K q p n h V
  naturality {V W} f := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun a k => ?_
    refine Subtype.ext ?_
    exact P.pairElt_res U K q p f a k

end PreResolvingData

end Cohesive
