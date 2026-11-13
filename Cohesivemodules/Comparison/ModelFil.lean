import Cohesivemodules.Comparison.ModelFilG0

set_option linter.style.header false

/-!
# C7.f: the quasi-isomorphism criterion for `Ξ_e` (part 2 of 2)

Split from `Comparison/ModelFil.lean` for size;
continues `Comparison/ModelFilG0.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace DirectSum
variable {X : Type} [TopologicalSpace X]
namespace PreResolvingData
variable (P : PreResolvingData X) (U : Opens X) (M : CohesiveModule (P.D.𝒜 U))

/-- C7.f: morphisms out of `G0^p` are determined by their values on the global sections
`1 ⊗ q`: the sections of `G0^p` over `V` are generated over `𝒜⁰(V)` by restrictions of those
over `U`. -/
theorem g0Sh_hom_ext (p : ℤ) {N : Mod ((ringOf P.A0).over U)} (h₁ h₂ : P.G0Sh U M p ⟶ N)
    (h : ∀ q : M.Q p,
      (h₁.val.app (topO U)).hom (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q) =
      (h₂.val.app (topO U)).hom (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q)) :
    h₁ = h₂ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  induction x using BCGen.induction_on with
  | ht β q =>
    let y0 : (P.G0Sh U M p).val.obj (topO U) :=
      BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q
    let y1 : (P.G0Sh U M p).val.obj V := P.g0Res U M p (toV V) y0
    let β' : ((ringOf P.A0).over U).obj.obj V := β
    have hv : BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q 1 q = y1 :=
      (congrArg (BCGen.tmul _ M.Q · q) (map_one _)).symm
    have hb : BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q β q = β' • y1 :=
      (BCGen.tmul_eq_smul β q).trans (congrArg (β • ·) hv)
    have n1 : (h₁.val.app V).hom y1 =
        (N.val.map (toV V)).hom ((h₁.val.app (topO U)).hom y0) :=
      PresheafOfModules.naturality_apply h₁.val (toV V) y0
    have n2 : (h₂.val.app V).hom y1 =
        (N.val.map (toV V)).hom ((h₂.val.app (topO U)).hom y0) :=
      PresheafOfModules.naturality_apply h₂.val (toV V) y0
    have e1 := (h₁.val.app V).hom.map_smul β' y1
    have e2 := (h₂.val.app V).hom.map_smul β' y1
    have h0 : (h₁.val.app (topO U)).hom y0 = (h₂.val.app (topO U)).hom y0 := h q
    have h1 : (h₁.val.app V).hom y1 = (h₂.val.app V).hom y1 :=
      (n1.trans (congrArg _ h0)).trans n2.symm
    exact (congrArg (h₁.val.app V).hom hb).trans (e1.trans
      ((congrArg (β' • ·) h1).trans (e2.symm.trans (congrArg (h₂.val.app V).hom hb.symm))))
  | hadd x y hx hy =>
    exact ((h₁.val.app V).hom.map_add x y).trans
      ((congrArg₂ _ hx hy).trans ((h₂.val.app V).hom.map_add x y).symm)

/-- `𝕏⁰` of `M|V` commutes with restriction of generators. -/
theorem X0comp_g0Res (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.G0Sec U M p V) :
    (M.baseChange (P.D.res (leOfHom W.unop.hom))).toQuasiCohesive.X0comp p
        (P.g0Res U M p f x) =
      P.g0Res U M (p + 1) f
        ((M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.X0comp p x) := by
  show bcX0comp (P.D.res (leOfHom W.unop.hom)) M.toQuasiCohesive p (P.g0Res U M p f x) =
    P.g0Res U M (p + 1) f (bcX0comp (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive p x)
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [g0Res_tmul]
    have h1 := X0comp_bc_tmul (P.D.res (leOfHom W.unop.hom)) M.toQuasiCohesive p
      ((P.D.res (leOfHom f.unop.left)).f0 β) q
    have h2 := X0comp_bc_tmul (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive p β q
    refine h1.trans ?_
    refine Eq.trans ?_ (congrArg (P.g0Res U M (p + 1) f) h2).symm
    exact (P.g0Res_tmul U M (p + 1) f β (M.toQuasiCohesive.X0comp p q)).symm
  | hadd x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- **C7.f.** The differential `𝕏⁰ : G0^p → G0^{p+1}` (A11 `X0comp` of `M|V`). -/
def G0D (p : ℤ) : P.G0Sh U M p ⟶ P.G0Sh U M (p + 1) :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom
       ((M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.X0comp p)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact P.X0comp_g0Res U M p f x }⟩

/-- `𝕏⁰ ∘ 𝕏⁰ = 0` on `G0`. -/
theorem G0D_G0D (p : ℤ) : P.G0D U M p ≫ P.G0D U M (p + 1) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  exact bcX0comp_bcX0comp (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive p x

/-- **C7.f.** The form-degree-`0` part `G0 M` of `α_U(M)`, a complex of sheaves of
`𝒜⁰|U`-modules. -/
def G0 : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ :=
  CochainComplex.of (P.G0Sh U M) (P.G0D U M) (P.G0D_G0D U M)

/-! ## The `(0,0)`-component of `Ξ_e` -/

variable {P U M} {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} {θ : P.Conn U F}
  (e : Z0 M.toQuasiCohesive (θ.N (topO U)))

/-- **C7.f.** `gr0Ξ e` on sections over `V`: the `(0,0)`-component of `Ξ_e` on `V` (A12). -/
def gr0ΞV (p : ℤ) (V : (Over U)ᵒᵖ) :
    P.G0Sec U M p V →ₗ[↥(P.D.𝒜 V.unop.left 0)] P.FSec U F p V :=
  comp0L (ΞV_mem e V).1 p

/-- `gr0Ξ e` commutes with restriction (`ΞV_res`). -/
theorem gr0ΞV_res (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.G0Sec U M p V) :
    gr0ΞV e p W (P.g0Res U M p f x) = P.fRes U F p f (gr0ΞV e p V x) := by
  have h1 : P.totRes M (leOfHom V.unop.hom) (leOfHom f.unop.left)
      (Tot.tmul (P.D.𝒜 V.unop.left) (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q) 1
        (lof (P.D.𝒜 V.unop.left 0) ℤ (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q) p x)) =
      Tot.tmul (P.D.𝒜 W.unop.left) (BCGen (P.D.res (leOfHom W.unop.hom)) M.Q) 1
        (lof (P.D.𝒜 W.unop.left 0) ℤ (BCGen (P.D.res (leOfHom W.unop.hom)) M.Q) p
          (P.g0Res U M p f x)) := by
    refine (bcTotRes_tmul (P.D.res (leOfHom f.unop.left)) (P.D.res (leOfHom V.unop.hom))
      (P.D.res (leOfHom W.unop.hom)) (P.D.res_comp _ _) M.Q 1 _).trans ?_
    rw [DgaHom.map_one']
    congr 1
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.map_of]
    rfl
  have h2 : ΞV e W (Tot.tmul (P.D.𝒜 W.unop.left) (BCGen (P.D.res (leOfHom W.unop.hom)) M.Q) 1
        (lof (P.D.𝒜 W.unop.left 0) ℤ (BCGen (P.D.res (leOfHom W.unop.hom)) M.Q) p
          (P.g0Res U M p f x))) =
      P.tRes U F f (ΞV e V (Tot.tmul (P.D.𝒜 V.unop.left)
        (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q) 1
        (lof (P.D.𝒜 V.unop.left 0) ℤ (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q) p x))) := by
    rw [← h1]
    exact ΞV_res e f _
  show Tot.eps (P.D.𝒜 W.unop.left) (P.FSec U F · W) (ΞV e W (Tot.tmul (P.D.𝒜 W.unop.left)
      (BCGen (P.D.res (leOfHom W.unop.hom)) M.Q) 1
      (lof (P.D.𝒜 W.unop.left 0) ℤ (BCGen (P.D.res (leOfHom W.unop.hom)) M.Q) p
        (P.g0Res U M p f x)))) p = _
  rw [h2]
  exact (congrArg (fun y : ⨁ q, P.FSec U F q W => y p)
    (eps_totMapAlong (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
      (fun p => P.fRes_smul U F f p) _)).trans (famMap_apply_mdl _ _ p)

/-- **C7.f.** `gr0Ξ e : G0^p → F^p` as a map of sheaves. -/
def gr0Ξn (p : ℤ) : P.G0Sh U M p ⟶ F.X p :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (gr0ΞV e p V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact gr0ΞV_res e p f x }⟩

/-- `gr0Ξ e` commutes with the differentials (A12 `comp0_sq`). -/
theorem gr0Ξn_comm (p : ℤ) : gr0Ξn e p ≫ F.d p (p + 1) = P.G0D U M p ≫ gr0Ξn e (p + 1) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  have h : ((θ.N V).complex0.d p (p + 1)).hom (comp0L (ΞV_mem e V).1 p x) =
      comp0L (ΞV_mem e V).1 (p + 1)
        (((M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.complex0.d p
          (p + 1)).hom x) :=
    congrArg (fun φ => φ.hom x) (comp0_sq (ΞV_mem e V) p)
  have h1 := ((θ.N V).complex0_d p (comp0L (ΞV_mem e V).1 p x)).symm.trans h
  have h2 : (θ.N V).X0comp p (comp0L (ΞV_mem e V).1 p x) =
      comp0L (ΞV_mem e V).1 (p + 1)
        ((M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.X0comp p x) :=
    h1.trans (congrArg _ ((M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.complex0_d
      p x))
  exact (X0comp_N (θ := θ) V p _).symm.trans h2

/-- **C7.f.** The `(0,0)`-component `gr0Ξ e : G0 M → F` of `Ξ_e`, a map of complexes of sheaves of
`𝒜⁰|U`-modules. -/
def gr0Ξ : P.G0 U M ⟶ F where
  f p := gr0Ξn e p
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e1 : (P.G0 U M).d i (i + 1) = P.G0D U M i := CochainComplex.of_d _ _ _
    rw [e1]
    exact gr0Ξn_comm e i

/-! ## The criterion -/

variable (P U M) in
/-- The form-degree-`0` part of `θ_V = bcθ` is the differential of `G0 M` (`𝕏⁰` of `M|V`). -/
theorem bcConn_eps (V : (Over U)ᵒᵖ) (p : ℤ) (x : P.FSec U (P.G0 U M) p V) :
    Tot.eps (P.D.𝒜 V.unop.left) (P.FSec U (P.G0 U M) · V)
        ((bcGenData (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive).θ
          (lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.G0 U M) · V) p x)) =
      lof ↥(P.D.𝒜 V.unop.left 0) ℤ (P.FSec U (P.G0 U M) · V) (p + 1)
        (P.fD U (P.G0 U M) p V x) := by
  have h : (M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.X0
      (lof (P.D.𝒜 V.unop.left 0) ℤ (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q) p x) =
      lof (P.D.𝒜 V.unop.left 0) ℤ (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q) (p + 1)
        ((M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.X0comp p x) :=
    (M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.X0_lof p x
  have h2 : Tot.eps (P.D.𝒜 V.unop.left) (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q)
      ((bcGenData (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive).θ
        (lof (P.D.𝒜 V.unop.left 0) ℤ (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q) p x)) =
      (M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.X0
      (lof (P.D.𝒜 V.unop.left 0) ℤ (BCGen (P.D.res (leOfHom V.unop.hom)) M.Q) p x) := by
    show _ = Tot.eps _ _ ((bcGenData _ M.toQuasiCohesive).extend (Tot.oneTmul _ _ _))
    rw [Tot.oneTmul_apply, GenData.extend_tmul_one]
  have e1 : (P.G0 U M).d p (p + 1) = P.G0D U M p := CochainComplex.of_d _ _ _
  have h3 : P.fD U (P.G0 U M) p V x =
      (M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive.X0comp p x := by
    unfold fD
    rw [e1]
    rfl
  rw [h3]
  exact h2.trans h

variable (P U M) in
/-- The generator data of `M|V` commute with restriction. -/
theorem bcConn_natural {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : ⨁ p, P.G0Sec U M p V) :
    totMapAlong (P.D.res (leOfHom f.unop.left)) (fun p => (P.g0Res U M p f).toAddMonoidHom)
        (fun p => (P.g0Res U M p f).map_smulₛₗ)
        ((bcGenData (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive).θ x) =
      (bcGenData (P.D.res (leOfHom W.unop.hom)) M.toQuasiCohesive).θ
        (famMap (fun p => (P.g0Res U M p f).toAddMonoidHom) x) :=
  tmA_bcθ (P.D.res (leOfHom f.unop.left)) (P.D.res (leOfHom V.unop.hom))
    (P.D.res (leOfHom W.unop.hom)) (P.D.res_comp _ _) M.toQuasiCohesive x

variable (P U M) in
/-- **C7.f.** `α_U(M)` as a `T`-complex: the flat connection on `G0 M` given on `V` by the
generator data of the base change `M|V` (A9). Then `T(bcConn M)` has the sections of `α_U(M)`. -/
def bcConn : P.Conn U (P.G0 U M) where
  θ V := bcGenData (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive
  mem V := bcθ_mem (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive
  flat V := bc_flat (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive
  eps V := P.bcConn_eps U M V
  natural f := P.bcConn_natural U M f

/-- Restriction of `T(bcConn M)` is the restriction `totRes` of `α_U(M)`. -/
private theorem tRes_G0_eq_totRes {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (x : P.TTot U (P.G0 U M) V) :
    P.tRes U (P.G0 U M) f x = P.totRes M (leOfHom V.unop.hom) (leOfHom f.unop.left) x :=
  totMapAlong_bcGenRes_eq (P.D.res (leOfHom f.unop.left)) (P.D.res (leOfHom V.unop.hom))
    (P.D.res (leOfHom W.unop.hom)) (P.D.res_comp _ _) M.Q x

/-- **C7.f.** `Ξ_e` is the `T`-map of a map of connections `bcConn M → θ` (given on `V` by
`ΞV e V`), up to the identification `α_U(M) ≅ T(bcConn M)` (same sections, differentials and
restrictions); its `(0,0)`-component is `gr0Ξ e`. -/
theorem exists_ΞConnHom [CompactSpace X] :
    ∃ (Φ : ConnHom (P.bcConn U M) θ) (i : P.sheafOfOver U M ≅ (P.bcConn U M).TC),
      Ξ e = i.hom ≫ Φ.TMap ∧ Φ.T0Map = gr0Ξ e := by
  let Φ : ConnHom (P.bcConn U M) θ :=
    ⟨fun V => ΞV e V, fun V => ΞV_mem e V, fun {V W} f x => by
      have h := ΞV_res e f (M := M) x
      rw [tRes_G0_eq_totRes (M := M) f x]
      exact h⟩
  let idL : ∀ (n : ℤ) (V : (Over U)ᵒᵖ), P.sheafOfSec M n (leOfHom V.unop.hom) →ₗ[P.O.obj.obj
      (op V.unop.left)] P.TSec U (P.G0 U M) n V := fun n V =>
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let idL' : ∀ (n : ℤ) (V : (Over U)ᵒᵖ), P.TSec U (P.G0 U M) n V →ₗ[P.O.obj.obj
      (op V.unop.left)] P.sheafOfSec M n (leOfHom V.unop.hom) := fun n V =>
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let hm : ∀ n : ℤ, P.sheafOfOverSh U M n ⟶ P.TSh U (P.G0 U M) n := fun n =>
    ⟨{ app := fun V ↦ ModuleCat.ofHom (idL n V)
       naturality := by
         intro V W f
         apply ModuleCat.hom_ext
         refine DFunLike.ext _ _ fun x => ?_
         apply Subtype.ext
         exact (tRes_G0_eq_totRes f x.1).symm }⟩
  let iv : ∀ n : ℤ, P.TSh U (P.G0 U M) n ⟶ P.sheafOfOverSh U M n := fun n =>
    ⟨{ app := fun V ↦ ModuleCat.ofHom (idL' n V)
       naturality := by
         intro V W f
         apply ModuleCat.hom_ext
         refine DFunLike.ext _ _ fun x => ?_
         apply Subtype.ext
         exact tRes_G0_eq_totRes f x.1 }⟩
  let ee : ∀ n : ℤ, P.sheafOfOverSh U M n ≅ P.TSh U (P.G0 U M) n := fun n =>
    { hom := hm n
      inv := iv n
      hom_inv_id := by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
        apply ModuleCat.hom_ext
        exact DFunLike.ext _ _ fun x => rfl
      inv_hom_id := by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
        apply ModuleCat.hom_ext
        exact DFunLike.ext _ _ fun x => rfl }
  let i : P.sheafOfOver U M ≅ (P.bcConn U M).TC :=
    HomologicalComplex.Hom.isoOfComponents (fun n => ee n) (by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      have e1 : (P.bcConn U M).TC.d i (i + 1) = (P.bcConn U M).TD i :=
        CochainComplex.of_d _ _ _
      have e2 : (P.sheafOfOver U M).d i (i + 1) = P.sheafOfOverD U M i := CochainComplex.of_d _ _ _
      rw [e1, e2]
      refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
      apply ModuleCat.hom_ext
      exact DFunLike.ext _ _ fun x => rfl)
  refine ⟨Φ, i, ?_, ?_⟩
  · refine HomologicalComplex.hom_ext _ _ fun n => ?_
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    exact DFunLike.ext _ _ fun x => rfl
  · refine HomologicalComplex.hom_ext _ _ fun n => ?_
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    exact DFunLike.ext _ _ fun x => rfl

/-- **C7.f. Quasi-isomorphism criterion.** If the `(0,0)`-component `gr0Ξ e : G0 M → F` is a
quasi-isomorphism of complexes of `𝒜⁰|U`-modules, then `Ξ_e : α_U(M) → T` is a
quasi-isomorphism: `Ξ_e` is a map of `T`-complexes (`exists_ΞConnHom`) and the criterion
`ConnHom.quasiIso_TMap` (`ModelCrit.lean`) applies. -/
theorem quasiIso_Ξ [CompactSpace X] (h : QuasiIso (gr0Ξ e)) : QuasiIso (Ξ e) := by
  obtain ⟨Φ, i, h1, h2⟩ := exists_ΞConnHom e
  have h0 : QuasiIso Φ.T0Map := by rw [h2]; exact h
  have hT : QuasiIso Φ.TMap := Φ.quasiIso_TMap h0
  rw [h1]
  infer_instance

end PreResolvingData

end Cohesive
