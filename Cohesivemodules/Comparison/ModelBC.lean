import Cohesivemodules.Comparison.ModelFil
import Cohesivemodules.Sheaf.BaseChange
import Cohesivemodules.Sheaf.Restriction

set_option linter.style.header false

/-!
# C7.b, C7.d: the model `T(K)` of `𝒜^• ⊗_R K`

Blueprint items C7.b and C7.d (§4, v1.11). For a complex `K` of sheaves of `R|U`-modules,
`F_K := 𝒜⁰ ⊗_R K` (S8 `sheafBC` along `ρ|U`), with the unit `η : K → F_K`, `k ↦ 1 ⊗ k`.
* C7.b `exists_conn`: `F_K` carries a flat connection (`Conn`) with `∇(η k) = 0`, i.e.
  `θ(η k) = 1 ⊗ η(d_K k)` (`IsBCConn`); `∇` is the sheafification of `α ⊗ k ↦ dα ⊗ η(1 ⊗ k)`.
* C7.d `ιT`: the map `K → T(K)`, `k ↦ 1 ⊗ η k`; `exists_TC_iso_tensorC`: `T(K)` is isomorphic
  to `tensorC (𝒜^•|U) K` compatibly with `ρ̂ ⊗ K`; `quasiIso_ιT`: for `K` K-flat, `ιT` is a
  quasi-isomorphism (`ρ` is a resolution, C5 step 6 on the over-site).

`ρSheaf` (ρ as a map of sheaves of rings) moved here from `EssSurj.lean` (its proof unchanged).

## Deviations
* Over-site of `U`; `K` is any complex for C7.b, K-flat for `quasiIso_ιT`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X)

/-- **C5, C7.** `ρ : O ⟶ 𝒜⁰` as a map of sheaves of commutative rings (`ρ_U` on sections; natural
by `P.ρ_natural`). -/
def ρSheaf : P.O ⟶ P.A0 :=
  ⟨{ app := fun U ↦ CommRingCat.ofHom (P.ρ U.unop)
     naturality := by
       intro U V f
       refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
       exact Subtype.ext (congrArg Subtype.val (P.ρ_natural (leOfHom f.unop) a).symm) }⟩

variable (U : Opens X) (K : CochainComplex (Mod (P.R.over U)) ℤ)

/-- **C7.b.** `F_K = 𝒜⁰ ⊗_R K`, a complex of sheaves of `𝒜⁰|U`-modules (S8 `sheafBC` along
`ρ|U`). -/
def FK : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ :=
  ((sheafBC (overHom P.ρSheaf U)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- **C7.b.** The unit `η : K^p(V) → F_K^p(V)`, `k ↦ 1 ⊗ k` (unit of `sheafBC ⊣ restriction`). -/
def bcη (p : ℤ) (V : (Over U)ᵒᵖ) : (K.X p).val.obj V →+ P.FSec U (P.FK U K) p V :=
  (((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val.app V).hom.toAddMonoidHom

/-- The differential of `K` on sections over `V`. -/
def kD (p : ℤ) (V : (Over U)ᵒᵖ) : (K.X p).val.obj V →+ (K.X (p + 1)).val.obj V :=
  ((K.d p (p + 1)).val.app V).hom.toAddMonoidHom

/-- **C7.b.** A flat connection on `F_K` with `∇(η k) = 0`: `θ_V(1 ⊗ η k) = 1 ⊗ η(d_K k)`. -/
def IsBCConn (θ : P.Conn U (P.FK U K)) : Prop :=
  ∀ (V : (Over U)ᵒᵖ) (p : ℤ) (k : (K.X p).val.obj V),
    (θ.θ V).θ (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k)) =
      Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
        (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) (p + 1)
          (P.bcη U K (p + 1) V (P.kD U K p V k)))

-- C7.b `exists_conn` is in `ModelConn.lean`; C7.d `exists_TC_iso_tensorC`, `quasiIso_ιT` in
-- `ModelTensor.lean` (split for size, v1.11).

variable {P U K}

/-- `1 ⊗ η k` has total degree `p`. -/
theorem tmul_bcη_mem (p : ℤ) (V : (Over U)ᵒᵖ) (k : (K.X p).val.obj V) :
    Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
        (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k)) ∈
      P.tDeg U (P.FK U K) p V := by
  have := tmul_mem_totDeg (𝒜 := P.D.𝒜 V.unop.left) (Q := (P.FSec U (P.FK U K) · V))
    (SetLike.GradedOne.one_mem (A := P.D.𝒜 V.unop.left)) (P.bcη U K p V k)
  rwa [zero_add] at this

/-- `k ↦ 1 ⊗ η k` as an element of `T^p(V)`. -/
def ιTfun (p : ℤ) (V : (Over U)ᵒᵖ) (k : (K.X p).val.obj V) : P.TSec U (P.FK U K) p V :=
  ⟨_, tmul_bcη_mem p V k⟩

/-- `ιTfun` is additive. -/
theorem ιTfun_add (p : ℤ) (V : (Over U)ᵒᵖ) (k k' : (K.X p).val.obj V) :
    ιTfun p V (k + k') = ιTfun p V k + ιTfun p V k' := by
  apply Subtype.ext
  show Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V (k + k'))) = _
  rw [map_add, map_add, Tot.tmul_add]
  rfl

/-- `ιTfun` is `O(V)`-linear (`η(r k) = ρ(r)·η k`). -/
theorem ιTfun_smul (p : ℤ) (V : (Over U)ᵒᵖ) (r : (P.R.over U).obj.obj V)
    (k : (K.X p).val.obj V) : ιTfun p V (r • k) = r • ιTfun p V k := by
  apply Subtype.ext
  show Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V (r • k))) =
    (P.ρ V.unop.left r : P.D.A V.unop.left) • _
  have h := (((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val.app V).hom.map_smul r k
  have h2 : P.bcη U K p V (r • k) = (P.ρ V.unop.left r : ↥(P.D.𝒜 V.unop.left 0)) •
      P.bcη U K p V k := h
  rw [h2, map_smul, Tot.tmul_smul0, one_mul]
  exact ((Tot.smul_tmul _ _ _).trans (by rw [mul_one])).symm

/-- **C7.d.** `ιT` on sections: `k ↦ 1 ⊗ η k`, an `O(V)`-linear map `K^p(V) → T^p(V)`. -/
def ιTV (p : ℤ) (V : (Over U)ᵒᵖ) :
    (K.X p).val.obj V →ₗ[(P.R.over U).obj.obj V] P.TSec U (P.FK U K) p V where
  toFun := ιTfun p V
  map_add' := ιTfun_add p V
  map_smul' := ιTfun_smul p V

/-- `ιTV` commutes with restriction. -/
theorem ιTV_res [CompactSpace X] (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (k : (K.X p).val.obj V) :
    (ιTV p W ((K.X p).val.map f k)).1 = P.tRes U (P.FK U K) f (ιTV p V k).1 := by
  have hn : P.bcη U K p W ((K.X p).val.map f k) = P.fRes U (P.FK U K) p f (P.bcη U K p V k) :=
    (PresheafOfModules.naturality_apply
      ((sheafBCAdj (overHom P.ρSheaf U)).unit.app (K.X p)).val f k)
  show Tot.tmul (P.D.𝒜 W.unop.left) (P.FSec U (P.FK U K) · W) 1
      (lof ↥(P.D.𝒜 W.unop.left 0) ℤ (P.FSec U (P.FK U K) · W) p
        (P.bcη U K p W ((K.X p).val.map f k))) =
    totMapAlong (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U (P.FK U K) p f)
      (fun p => P.fRes_smul U (P.FK U K) f p)
      (Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
        (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k)))
  rw [totMapAlong_tmul, DirectSum.lof_eq_of, DirectSum.lof_eq_of, famMap_of, hn]
  exact congrArg (Tot.tmul _ _ · _) (map_one (P.D.res (leOfHom f.unop.left)).toAlgHom).symm

/-- **C7.d.** `ιT : K^p → T^p` as a map of sheaves. -/
def ιTn [CompactSpace X] (p : ℤ) : K.X p ⟶ P.TSh U (P.FK U K) p :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (ιTV p V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun k => ?_
       apply Subtype.ext
       exact ιTV_res p f k }⟩

/-- `ιT` commutes with the differentials when `∇(η k) = 0`. -/
theorem ιTn_comm [CompactSpace X] (θ : P.Conn U (P.FK U K)) (hθ : P.IsBCConn U K θ) (p : ℤ) :
    ιTn p ≫ θ.TD p = K.d p (p + 1) ≫ ιTn (p + 1) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun k => ?_
  apply Subtype.ext
  show (θ.N V).X (Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) p (P.bcη U K p V k))) =
    Tot.tmul (P.D.𝒜 V.unop.left) (P.FSec U (P.FK U K) · V) 1
      (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.FK U K) · V) (p + 1)
        (P.bcη U K (p + 1) V (P.kD U K p V k)))
  exact (GenData.extend_tmul_one (θ.θ V) _).trans (hθ V p k)

/-- **C7.d.** The map of complexes `ιT : K → T(K)`, `k ↦ 1 ⊗ η k`, for a connection with
`∇(η k) = 0`. -/
def ιT [CompactSpace X] (θ : P.Conn U (P.FK U K)) (hθ : P.IsBCConn U K θ) : K ⟶ θ.TC where
  f p := ιTn p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e1 : θ.TC.d i (i + 1) = θ.TD i := CochainComplex.of_d _ _ _
    rw [e1]
    exact ιTn_comm θ hθ i

end PreResolvingData

end Cohesive
