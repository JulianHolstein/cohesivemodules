import Cohesivemodules.Comparison.ModelBC

set_option linter.style.header false

/-!
# C7.b: the connection on `𝒜⁰ ⊗_R K`

Blueprint item C7.b (§4, v1.11). Split from `ModelBC.lean` for size. `exists_conn`: the complex
`F_K = 𝒜⁰ ⊗_R K` carries a flat connection with `∇(η k) = 0`.

Proof plan (prover's analysis, 27 Oct 2026):
1. `bcη k` is the image of `1 ⊗ k` under the unit of sheafification (unfold `sheafBCAdj`).
2. The additive map `𝒜⁰(V) ⊗_{R(V)} K^p(V) → T^{p+1}(V)`, `α ⊗ k ↦ dα ⊗ η k`, is balanced
   (`d ∘ ρ = 0`) and natural in `V`.
3. It extends through the sheafification of abelian groups (`T^{p+1}` is a sheaf, C7.a) to
   `∇_V : F^p(V) → T^{p+1}(V)`, additive and natural (`∇` is not `𝒜⁰`-linear, so the module-level
   universal property of `sheafBC` does not apply).
4. Locality: every section of `F^p` is locally of the form `Σ αᵢ η kᵢ`, and `T` is separated;
   hence Leibniz `∇(αf) = dα ⊗ f + α∇f`, `∇ d_F = d_F ∇` and `∇² = 0` (on the presheaf images
   these are computations).
5. `θ_V := ⨁ (∇ + 1 ⊗ d_F)`; `mem`, `flat` (`c = 0`), `eps`, `natural`, `IsBCConn`.

## Deviations
* None beyond those of `ModelDef.lean`.

Part 1 of 2 of the original `Comparison/ModelConn.lean`, split for size; continued in
`Comparison/ModelConn.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum
open scoped ChangeOfRings TensorProduct

variable {X : Type} [TopologicalSpace X]

/-- Additive maps out of the extension of scalars from a balanced bi-additive map. -/
private def liftBC {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) {M : ModuleCat.{0} R}
    {Z : Type} [AddCommGroup Z] (b : S →+ M →+ Z)
    (hb : ∀ (r : R) (s : S) (m : M), b (g r * s) m = b s (r • m)) :
    ((ModuleCat.extendScalars g).obj M) →+ Z :=
  letI : Module R S := Module.compHom S g
  TensorProduct.liftAddHom (R := R) b (fun r s m => hb r s m)

/-- `liftBC` on pure tensors (rfl). -/
private theorem liftBC_tmul {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
    {M : ModuleCat.{0} R} {Z : Type} [AddCommGroup Z] (b : S →+ M →+ Z)
    (hb : ∀ (r : R) (s : S) (m : M), b (g r * s) m = b s (r • m)) (s : S) (m : M) :
    liftBC g b hb ((s ⊗ₜ[R, g] m : (ModuleCat.extendScalars g).obj M)) = b s m := rfl

/-- Induction on elements of the extension of scalars. -/
theorem bc_induction {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
    {M : ModuleCat.{0} R} {C : ((ModuleCat.extendScalars g).obj M) → Prop}
    (z : (ModuleCat.extendScalars g).obj M)
    (ht : ∀ (s : S) (m : M), C (s ⊗ₜ[R, g] m)) (hadd : ∀ x y, C x → C y → C (x + y)) : C z := by
  let _ : Module R S := Module.compHom S g
  exact TensorProduct.inductionOn z ht hadd

/-- `s ⊗ m = s • (1 ⊗ m)` in the extension of scalars. -/
theorem bc_tmul_eq_smul {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
    {M : ModuleCat.{0} R} (s : S) (m : M) :
    (s ⊗ₜ[R, g] m : (ModuleCat.extendScalars g).obj M) =
      s • (show ↑((ModuleCat.extendScalars g).obj M) from (1 : S) ⊗ₜ[R, g] m) := by
  show _ = (s * 1) ⊗ₜ[R, g] m
  rw [mul_one]
  rfl

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X) (K : CochainComplex (Mod (P.R.over U)) ℤ)

/-- `dα ⊗ η k` as an element of the total module. -/
def nbTot (p : ℤ) (V : (Over U)ᵒᵖ) (s : ↥(P.D.𝒜 V.unop.left 0))
    (k : (K.X p).val.obj V) : P.TTot U (P.FK U K) V :=
  Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) (GCDga.d (𝒜 := P.D.𝒜 V.unop.left) s)
    (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k))

/-- `dα ⊗ η k` has total degree `p + 1`. -/
private theorem nbTot_mem (p : ℤ) (V : (Over U)ᵒᵖ) (s : ↥(P.D.𝒜 V.unop.left 0))
    (k : (K.X p).val.obj V) : nbTot P U K p V s k ∈ P.tDeg U (P.FK U K) (p + 1) V := by
  have := tmul_mem_totDeg (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U (P.FK U K) · V))
    (GCDga.d_mem_one (𝒜 := P.D.𝒜 V.unop.left) s.2) (P.bcη U K p V k)
  rwa [add_comm] at this

/-- `nbTot` is additive in `s`. -/
private theorem nbTot_add_left (p : ℤ) (V : (Over U)ᵒᵖ) (s s' : ↥(P.D.𝒜 V.unop.left 0))
    (k : (K.X p).val.obj V) : nbTot P U K p V (s + s') k = nbTot P U K p V s k +
      nbTot P U K p V s' k := by
  unfold nbTot
  rw [Submodule.coe_add, map_add, Tot.add_tmul]

/-- `nbTot` is additive in `k`. -/
private theorem nbTot_add_right (p : ℤ) (V : (Over U)ᵒᵖ) (s : ↥(P.D.𝒜 V.unop.left 0))
    (k k' : (K.X p).val.obj V) : nbTot P U K p V s (k + k') = nbTot P U K p V s k +
      nbTot P U K p V s k' := by
  unfold nbTot
  rw [map_add, map_add, Tot.tmul_add]

/-- `(s, k) ↦ dα ⊗ η k` into `T^{p+1}(V)`, bi-additive. -/
private def nbAdd (p : ℤ) (V : (Over U)ᵒᵖ) :
    ↥(P.D.𝒜 V.unop.left 0) →+ (K.X p).val.obj V →+ P.TSec U (P.FK U K) (p + 1) V :=
  AddMonoidHom.mk' (fun s => AddMonoidHom.mk'
    (fun k => ⟨nbTot P U K p V s k, nbTot_mem P U K p V s k⟩)
    (fun k k' => Subtype.ext (nbTot_add_right P U K p V s k k')))
    (fun s s' => AddMonoidHom.ext fun k => Subtype.ext (nbTot_add_left P U K p V s s' k))

/-- `η(r k) = ρ(r) η k`. -/
private theorem bcη_smul (p : ℤ) (V : (Over U)ᵒᵖ) (r : (P.R.over U).obj.obj V)
    (k : (K.X p).val.obj V) :
    P.bcη U K p V (r • k) = (P.ρ V.unop.left r : ↥(P.D.𝒜 V.unop.left 0)) • P.bcη U K p V k :=
  (((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val.app V).hom.map_smul r k

/-- `nbAdd` is balanced over `R(V)` (`d ∘ ρ = 0`). -/
private theorem nbAdd_balanced (p : ℤ) (V : (Over U)ᵒᵖ) (r : (P.R.over U).obj.obj V)
    (s : ↥(P.D.𝒜 V.unop.left 0)) (k : (K.X p).val.obj V) :
    nbAdd P U K p V (P.ρ V.unop.left r * s) k = nbAdd P U K p V s (r • k) := by
  apply Subtype.ext
  show nbTot P U K p V _ k = nbTot P U K p V s (r • k)
  unfold nbTot
  have e : ((P.ρ V.unop.left r * s : ↥(P.D.𝒜 V.unop.left 0)) : P.D.A V.unop.left) =
      (P.ρ V.unop.left r : P.D.A V.unop.left) * (s : P.D.A V.unop.left) := rfl
  have hd : GCDga.d (𝒜 := P.D.𝒜 V.unop.left) (P.ρ V.unop.left r : P.D.A V.unop.left) = 0 :=
    P.d_ρ _ r
  rw [bcη_smul, map_smul, Tot.tmul_smul0, e,
    GCDga.leibniz_zero _ (P.ρ V.unop.left r).2, hd, zero_mul, zero_add]
  exact congrArg (Tot.tmul _ _ · _) (GCDga.central _ (P.ρ V.unop.left r).2 _)

/-- The presheaf-level tensor product `𝒜⁰ ⊗_R K^p` (before sheafification). -/
abbrev P0 (p : ℤ) := presheafBC (overHom P.ρSheaf U) (K.X p).val

/-- `uApp`: `α ⊗ k ↦ dα ⊗ η k`, on sections over `V`. -/
private def uApp (p : ℤ) (V : (Over U)ᵒᵖ) :
    (P0 P U K p).presheaf.obj V ⟶ (P.TPre U (P.FK U K) (p + 1)).presheaf.obj V :=
  AddCommGrpCat.ofHom (liftBC ((overHom P.ρSheaf U).hom.app V).hom
    (M := secC (R := P.O.over U) (K.X p).val V)
    (nbAdd P U K p V) (fun r s m => nbAdd_balanced P U K p V r s m))

/-- `η` commutes with restriction. -/
private theorem bcη_res (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (k : (K.X p).val.obj V) :
    P.bcη U K p W ((K.X p).val.map f k) = P.fRes U (P.FK U K) p f (P.bcη U K p V k) :=
  PresheafOfModules.naturality_apply
    ((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val f k

/-- `tRes` of `dα ⊗ η k`. -/
private theorem tRes_nbTot (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (s : ↥(P.D.𝒜 V.unop.left 0))
    (k : (K.X p).val.obj V) :
    P.tRes U (P.FK U K) f (nbTot P U K p V s k) =
      nbTot P U K p W ((P.D.res (leOfHom f.unop.left)).f0 s) ((K.X p).val.map f k) := by
  unfold nbTot
  rw [tRes_apply, totMapAlong_tmul, DirectSum.lof_eq_of, DirectSum.lof_eq_of, famMap_of,
    bcη_res]
  exact congrArg (Tot.tmul _ _ · _) ((P.D.res (leOfHom f.unop.left)).map_d s)

/-- `u : 𝒜⁰ ⊗_R K^p → T^{p+1}`, `α ⊗ k ↦ dα ⊗ η k`, as a map of presheaves of abelian groups. -/
private def uNat (p : ℤ) :
    (P0 P U K p).presheaf ⟶ (P.TPre U (P.FK U K) (p + 1)).presheaf where
  app V := uApp P U K p V
  naturality V W f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
    induction z using bc_induction with
    | ht s m =>
      erw [bcMap_tmul]
      exact (Subtype.ext (tRes_nbTot P U K p f s m)).symm
    | hadd x y hx hy =>
      erw [map_add, map_add, map_add, map_add]
      rw [hx, hy]

/-- The unit of sheafification on sections: `𝒜⁰(V) ⊗_{R(V)} K^p(V) → F^p(V)`. -/
def tsf (p : ℤ) (V : (Over U)ᵒᵖ) :
    (P0 P U K p).presheaf.obj V →+ P.FSec U (P.FK U K) p V :=
  ((toSheafify ((Opens.grothendieckTopology X).over U) (P0 P U K p).presheaf).app V).hom

/-- **The additive connection `∇`** as a map of presheaves of abelian groups `F^p → T^{p+1}`:
the sheafification-lift of `u`. -/
private def nabNat [CompactSpace X] (p : ℤ) :
    ((P.FK U K).X p).val.presheaf ⟶ (P.TPre U (P.FK U K) (p + 1)).presheaf :=
  sheafifyLift ((Opens.grothendieckTopology X).over U) (uNat P U K p)
    (P.isSheaf_TPre U (P.FK U K) (p + 1))

/-- `∇` on sections over `V`. -/
def nab [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ) :
    P.FSec U (P.FK U K) p V →+ P.TSec U (P.FK U K) (p + 1) V :=
  ((nabNat P U K p).app V).hom

/-- `∇` is natural. -/
theorem nab_res [CompactSpace X] (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (x : P.FSec U (P.FK U K) p V) :
    P.TRes U (P.FK U K) (p + 1) f (nab P U K p V x) =
      nab P U K p W (P.fRes U (P.FK U K) p f x) :=
  (congrArg (fun φ => φ.hom x) ((nabNat P U K p).naturality f)).symm

/-- `∇ ∘ (unit) = u`. -/
theorem nab_tsf [CompactSpace X] (p : ℤ) (V : (Over U)ᵒᵖ)
    (z : (P0 P U K p).presheaf.obj V) :
    nab P U K p V (tsf P U K p V z) = (uApp P U K p V).hom z :=
  congrArg (fun φ => (φ.app V).hom z) (toSheafify_sheafifyLift _ (uNat P U K p)
    (P.isSheaf_TPre U (P.FK U K) (p + 1)))

/-- The unit of sheafification as a map of presheaves of modules. -/
private def tsfM (p : ℤ) : P0 P U K p ⟶ ((P.FK U K).X p).val :=
  (PresheafOfModules.sheafificationAdjunction.{0} (𝟙 ((ringOf P.A0).over U).obj)).unit.app
    (P0 P U K p)

/-- `tsf` is `𝒜⁰(V)`-linear. -/
theorem tsf_smul (p : ℤ) (V : (Over U)ᵒᵖ)
    (a : ((P.A0.over U).obj ⋙ forget₂ CommRingCat RingCat).obj V) (z : (P0 P U K p).obj V) :
    tsf P U K p V (a • z) = (show ↥(P.D.𝒜 V.unop.left 0) from a) • tsf P U K p V z :=
  ((tsfM P U K p).app V).hom.map_smul a z

/-- Local induction on sections of `F^p`: a property that is local and holds on the image of the
unit of sheafification holds everywhere. -/
theorem fsec_induction (p : ℤ) (Φ : ∀ V : (Over U)ᵒᵖ, P.FSec U (P.FK U K) p V → Prop)
    (hloc : ∀ (V : (Over U)ᵒᵖ) (f : P.FSec U (P.FK U K) p V) (S : Sieve V.unop),
      S ∈ ((Opens.grothendieckTopology X).over U) V.unop →
      (∀ ⦃W : Over U⦄ (g : W ⟶ V.unop), S g → Φ (op W) (P.fRes U (P.FK U K) p g.op f)) →
      Φ V f)
    (hbase : ∀ (V : (Over U)ᵒᵖ) (z : (P0 P U K p).presheaf.obj V), Φ V (tsf P U K p V z)) :
    ∀ (V : (Over U)ᵒᵖ) (f : P.FSec U (P.FK U K) p V), Φ V f := by
  intro V f
  refine hloc V f _ (Presheaf.imageSieve_mem _
    (toSheafify ((Opens.grothendieckTopology X).over U) (P0 P U K p).presheaf) f) ?_
  intro W g hg
  obtain ⟨t, ht⟩ := hg
  have : P.fRes U (P.FK U K) p g.op f = tsf P U K p (op W) t := ht.symm
  rw [this]
  exact hbase _ t

end PreResolvingData
end Cohesive
end
