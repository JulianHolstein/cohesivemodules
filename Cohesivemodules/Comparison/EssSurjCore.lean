import Cohesivemodules.Comparison.EssSurjModel
import Cohesivemodules.Comparison.PerfectAux

set_option linter.style.header false

/-!
# C5 steps 4–5 on the over-site of `⊤` (C5.a–c via C7)

Blueprint item C5 (§4, v1.11). Split from `EssSurjModel.lean` for size.

Proof plan for `exists_cohesive_gr0_quasiIso` (prover's analysis, 27 Oct 2026):
* (A) `Pc := Γ(Pt)` is a bounded complex of finitely generated projective `𝒜⁰(X)`-modules
  (`finite_globalSections`, `projective_globalSections`, S4.c).
* (B) `e⁰ : Pc → N.complex0`, `N := θ.N (topO ⊤)`: `Γ(f⁰)` (a quasi-isomorphism by
  `quasiIso_globalSections`, `𝒜⁰` fine: `isFine0`), evaluation at `topO ⊤` of
  `(overBCComplexIso …).hom`, and the identity-component iso `Γ_⊤ F ≅ N.complex0`
  (`Conn.eps`: `𝕏⁰ = d_F`).
* (C) A11 `lifting` with `flat_piece` gives `M := CohesiveModule.ofGenData …` and closed `e` with
  `(0,0)`-component `e⁰`.
* (D) `gr0ΞV e p V (β ⊗ q) = β · res_V(ε(e(1 ⊗ q)))` (`bcLift` API); the sheaf map
  `ν : G0^p → (Pt|⊤)^p`, `β ⊗ q ↦ β · res q`, and its inverse `ν'` determined by `Γ`
  (`bijective_gammaT_map`, `exists_lift_hom` in PerfectAux); then
  `ν' ≫ gr0Ξ e = f⁰|⊤ ≫ overBCComplexIso.hom` by `Γ`-determination, a quasi-isomorphism
  (restriction is exact).

## Deviations
* None beyond those of C7 (blueprint v1.11).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable {P : PreResolvingData X} {U : Opens X}
  {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ}

/-- The complex `Γ_⊤ F` of sections of `F` over the terminal object is `(N_⊤).complex0`. -/
private def iso0 (θ : P.Conn U F) :
    ((gammaT ((ringOf P.A0).over U) (Over.mk (𝟙 U))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F ≅ (θ.N (topO U)).complex0 :=
  HomologicalComplex.Hom.isoOfComponents (fun p => Iso.refl _) (fun i j hij => by
    obtain rfl : i + 1 = j := hij
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun s => ?_
    exact ((θ.N (topO U)).complex0_d i s).trans (X0comp_N θ (topO U) i s))

/-- `gr0Ξ e` on `1 ⊗ q` over `⊤`: the `p`-component of `ε(e(1 ⊗ q))`. -/
private theorem gr0ΞV_topO {θ : P.Conn U F} {M : CohesiveModule (P.D.𝒜 U)}
    (e : Z0 M.toQuasiCohesive (θ.N (topO U))) (p : ℤ) (q : M.Q p) :
    gr0ΞV e p (topO U) (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q) =
      Tot.eps (P.D.𝒜 (topO U).unop.left) (θ.N (topO U)).Q
        (e.1 (Tot.tmul (P.D.𝒜 U) M.Q 1 (lof (P.D.𝒜 U 0) ℤ M.Q p q))) p := by
  have key : ΞV e (topO U)
      (Tot.tmul (P.D.𝒜 (topO U).unop.left) _ 1
        (lof ↥(P.D.𝒜 (topO U).unop.left 0) ℤ _ p
          (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q))) =
      e.1 (Tot.tmul (P.D.𝒜 U) M.Q 1 (lof (P.D.𝒜 U 0) ℤ M.Q p q)) :=
    ((congrArg (ΞV e (topO U)) (tmul_one_lof_eq_bcF (P.D.res (leOfHom (topO U).unop.hom))
      M.toQuasiCohesive p q)).trans (bcLift_bcF _ _)).trans (P.tRes_id U F (topO U) _)
  unfold gr0ΞV comp0L
  exact congrArg (fun z => Tot.eps (P.D.𝒜 (topO U).unop.left) (θ.N (topO U)).Q z p) key

section Nu

variable (P) (M : CohesiveModule (P.D.𝒜 ⊤))
  (Sc : CochainComplex (Mod ((ringOf P.A0).over ⊤)) ℤ)
  (φ : ∀ p, M.Q p ≃+ P.FSec ⊤ Sc p (topO ⊤))
  (hφ : ∀ p (r : ↥(P.D.𝒜 ⊤ 0)) (q : M.Q p),
    φ p (r • q) = (show ↥(P.D.𝒜 (topO ⊤).unop.left 0) from r) • φ p q)

/-- The bi-additive pairing `(β, q) ↦ β · res_V (φ q)` defining `Θ_V`. -/
private def thetaAux (p : ℤ) (V : (Over ⊤)ᵒᵖ) :
    (P.D.res (leOfHom V.unop.hom)).B0 →+ M.Q p →+ P.FSec ⊤ Sc p V :=
  AddMonoidHom.mk' (fun β => AddMonoidHom.mk'
    (fun q => (show ↥(P.D.𝒜 V.unop.left 0) from β) • P.fRes ⊤ Sc p (toV V) (φ p q))
    (fun q q' => by rw [map_add, map_add, smul_add]))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      exact add_smul (show ↥(P.D.𝒜 V.unop.left 0) from β) (show ↥(P.D.𝒜 V.unop.left 0) from β') _)

include hφ in
/-- `thetaAux` is balanced over `𝒜⁰(⊤)`. -/
private theorem thetaAux_balanced (p : ℤ) (V : (Over ⊤)ᵒᵖ) (r : ↥(P.D.𝒜 ⊤ 0))
    (β : (P.D.res (leOfHom V.unop.hom)).B0) (q : M.Q p) :
    thetaAux P M Sc φ p V (r • β) q = thetaAux P M Sc φ p V β (r • q) := by
  show (show ↥(P.D.𝒜 V.unop.left 0) from (r • β : (P.D.res (leOfHom V.unop.hom)).B0)) •
      P.fRes ⊤ Sc p (toV V) (φ p q) =
    (show ↥(P.D.𝒜 V.unop.left 0) from β) • P.fRes ⊤ Sc p (toV V) (φ p (r • q))
  rw [hφ, P.fRes_smul, smul_smul]
  congr 1
  exact mul_comm _ _

/-- `fRes` is functorial. -/
private theorem fRes_comp' (p : ℤ) {V W Y : (Over ⊤)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Y)
    (s : P.FSec ⊤ Sc p V) :
    P.fRes ⊤ Sc p (f ≫ g) s = P.fRes ⊤ Sc p g (P.fRes ⊤ Sc p f s) := by
  show ((Sc.X p).val.map (f ≫ g)).hom s = ((Sc.X p).val.map g).hom (((Sc.X p).val.map f).hom s)
  rw [(Sc.X p).val.map_comp]
  rfl

/-- `fRes` along the identity is the identity. -/
private theorem fRes_id' (p : ℤ) (V : (Over ⊤)ᵒᵖ) (s : P.FSec ⊤ Sc p V) :
    P.fRes ⊤ Sc p (𝟙 V) s = s := by
  show ((Sc.X p).val.map (𝟙 V)).hom s = s
  rw [(Sc.X p).val.map_id]
  rfl

include hφ in
/-- `Θ_V : 𝒜⁰(V) ⊗_{𝒜⁰(⊤)} Q^p → Sc^p(V)`, `β ⊗ q ↦ β · res_V(φ q)`, additively. -/
private def thetaAdd (p : ℤ) (V : (Over ⊤)ᵒᵖ) : P.G0Sec ⊤ M p V →+ P.FSec ⊤ Sc p V :=
  TensorProduct.liftAddHom (R := ↥(P.D.𝒜 ⊤ 0)) (thetaAux P M Sc φ p V)
    (thetaAux_balanced P M Sc φ hφ p V)

include hφ in
/-- `thetaAdd` on pure tensors. -/
private theorem thetaAdd_tmul (p : ℤ) (V : (Over ⊤)ᵒᵖ) (β : ↥(P.D.𝒜 V.unop.left 0)) (q : M.Q p) :
    thetaAdd P M Sc φ hφ p V (BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q β q) =
      β • P.fRes ⊤ Sc p (toV V) (φ p q) := rfl

include hφ in
/-- `thetaAdd` is `𝒜⁰(V)`-linear. -/
private theorem thetaAdd_smul (p : ℤ) (V : (Over ⊤)ᵒᵖ) (γ : ↥(P.D.𝒜 V.unop.left 0))
    (x : P.G0Sec ⊤ M p V) :
    thetaAdd P M Sc φ hφ p V (γ • x) = γ • thetaAdd P M Sc φ hφ p V x := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [BCGen.smul_tmul, thetaAdd_tmul, thetaAdd_tmul, mul_smul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

include hφ in
/-- `Θ_V` as a linear map. -/
private def thetaLin (p : ℤ) (V : (Over ⊤)ᵒᵖ) :
    P.G0Sec ⊤ M p V →ₗ[↥(P.D.𝒜 V.unop.left 0)] P.FSec ⊤ Sc p V where
  toFun := thetaAdd P M Sc φ hφ p V
  map_add' := map_add _
  map_smul' γ x := thetaAdd_smul P M Sc φ hφ p V γ x

include hφ in
/-- `Θ` commutes with restriction. -/
private theorem thetaLin_res (p : ℤ) {V W : (Over ⊤)ᵒᵖ} (f : V ⟶ W) (x : P.G0Sec ⊤ M p V) :
    thetaLin P M Sc φ hφ p W (P.g0Res ⊤ M p f x) =
      P.fRes ⊤ Sc p f (thetaLin P M Sc φ hφ p V x) := by
  induction x using BCGen.induction_on with
  | ht β q =>
    change thetaAdd P M Sc φ hφ p W (P.g0Res ⊤ M p f
        (BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q β q)) =
      P.fRes ⊤ Sc p f (thetaAdd P M Sc φ hφ p V
        (BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q β q))
    rw [g0Res_tmul, thetaAdd_tmul, thetaAdd_tmul, P.fRes_smul, ← fRes_comp']
    rfl
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

include hφ in
/-- `Θ` as a morphism of sheaves of `𝒜⁰|⊤`-modules. -/
private def thetaHom (p : ℤ) : P.G0Sh ⊤ M p ⟶ Sc.X p :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (thetaLin P M Sc φ hφ p V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact thetaLin_res P M Sc φ hφ p f x }⟩

include hφ in
/-- `φ⁻¹` is semilinear: `φ⁻¹(r s) = r φ⁻¹(s)`. -/
private theorem phi_symm_smul (p : ℤ) (r : ↥(P.D.𝒜 ⊤ 0)) (s : P.FSec ⊤ Sc p (topO ⊤)) :
    (φ p).symm ((show ↥(P.D.𝒜 (topO ⊤).unop.left 0) from r) • s) = r • (φ p).symm s := by
  apply (φ p).injective
  rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

include hφ in
/-- The additive-and-linear map `s ↦ 1 ⊗ φ⁻¹ s` on sections over `⊤`. -/
private def nuLin (p : ℤ) :
    (gammaT ((ringOf P.A0).over ⊤) (Over.mk (𝟙 ⊤))).obj (Sc.X p) ⟶
      (gammaT ((ringOf P.A0).over ⊤) (Over.mk (𝟙 ⊤))).obj (P.G0Sh ⊤ M p) :=
  ConcreteCategory.ofHom
    { toFun := fun s => BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 ((φ p).symm s)
      map_add' := fun s s' =>
        (congrArg (BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 ·)
          (map_add (φ p).symm s s')).trans (BCGen.tmul_add _ _ _)
      map_smul' := fun r s => by
        let r' : ↥(P.D.𝒜 ⊤ 0) := r
        have h1 := phi_symm_smul P M Sc φ hφ p r' s
        have h3 := BCGen.tmul_smul0 (f := P.D.res (leOfHom (topO ⊤).unop.hom))
          (Q := M.Q) r' ((φ p).symm s)
        have h4 : (P.D.res (leOfHom (topO ⊤).unop.hom)).f0 r' = r' :=
          Subtype.ext (P.D.res_id _ _)
        rw [h4] at h3
        exact (congrArg (BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 ·) h1).trans h3 }

include hφ in
/-- `Θ` on `1 ⊗ φ⁻¹ s` over `⊤` is `s`. -/
private theorem thetaHom_nu (p : ℤ) (s : P.FSec ⊤ Sc p (topO ⊤)) :
    ((thetaHom P M Sc φ hφ p).val.app (topO ⊤)).hom
      (BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 ((φ p).symm s)) = s := by
  show thetaAdd P M Sc φ hφ p (topO ⊤)
    (BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 ((φ p).symm s)) = s
  rw [thetaAdd_tmul, one_smul, AddEquiv.apply_symm_apply]
  exact fRes_id' P Sc p (topO ⊤) s

include hφ in
/-- **`G0^p ≅ Sc^p`.** For `Sc^p` a summand of a finite free `𝒜⁰|⊤`-module there is an isomorphism
`ν : Sc^p → G0^p` with `ν(s) = 1 ⊗ φ⁻¹ s` over `⊤`. -/
private theorem exists_nuHom (p : ℤ) (hS : IsFinFreeSummand (Sc.X p)) :
    ∃ ν : Sc.X p ⟶ P.G0Sh ⊤ M p, IsIso ν ∧ ∀ s : P.FSec ⊤ Sc p (topO ⊤),
      (ν.val.app (topO ⊤)).hom s =
        BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 ((φ p).symm s) := by
  obtain ⟨ν, hν⟩ := (bijective_gammaT_map (R := (ringOf P.A0).over ⊤)
    (Over.mkIdTerminal (X := ⊤)) hS (P.G0Sh ⊤ M p)).2 (nuLin P M Sc φ hφ p)
  have hs : ∀ s : P.FSec ⊤ Sc p (topO ⊤), (ν.val.app (topO ⊤)).hom s =
      BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 ((φ p).symm s) :=
    fun s => congrArg (fun f => f.hom s) hν
  refine ⟨ν, ?_, hs⟩
  have F1 : ν ≫ thetaHom P M Sc φ hφ p = 𝟙 _ := by
    refine (bijective_gammaT_map (R := (ringOf P.A0).over ⊤) (Over.mkIdTerminal (X := ⊤)) hS
      (Sc.X p)).1 ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    show ((thetaHom P M Sc φ hφ p).val.app (topO ⊤)).hom ((ν.val.app (topO ⊤)).hom s) = s
    rw [hs s]
    exact thetaHom_nu P M Sc φ hφ p s
  have F2 : thetaHom P M Sc φ hφ p ≫ ν = 𝟙 _ := by
    refine P.g0Sh_hom_ext ⊤ M p _ _ fun q => ?_
    show (ν.val.app (topO ⊤)).hom (((thetaHom P M Sc φ hφ p).val.app (topO ⊤)).hom
      (BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 q)) =
      BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 q
    have h1 : ((thetaHom P M Sc φ hφ p).val.app (topO ⊤)).hom
        (BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 q) = φ p q := by
      have := thetaHom_nu P M Sc φ hφ p (φ p q)
      rw [AddEquiv.symm_apply_apply] at this
      exact this
    rw [h1, hs, AddEquiv.symm_apply_apply]
  exact ⟨⟨thetaHom P M Sc φ hφ p, F1, F2⟩⟩

include hφ in
/-- **Abstract core.** If `Sc^n` are summands of finite free `𝒜⁰|⊤`-modules, `φ` identifies the
generators `Q` of `M` with the sections of `Sc` over `⊤` compatibly with `𝕏⁰` and `d`, and
`gr0Ξ e` is `g` on `1 ⊗ q`, for a quasi-isomorphism `g : Sc → F`, then `gr0Ξ e` is one. -/
private theorem quasiIso_gr0Ξ_abstract (hfin : ∀ n, IsFinFreeSummand (Sc.X n))
    (hX0 : ∀ p (q : M.Q p), φ (p + 1) (M.X0comp p q) = P.fD ⊤ Sc p (topO ⊤) (φ p q))
    {F : CochainComplex (Mod ((ringOf P.A0).over ⊤)) ℤ} {θ : P.Conn ⊤ F}
    (e : Z0 M.toQuasiCohesive (θ.N (topO ⊤))) (g : Sc ⟶ F) [QuasiIso g]
    (hg : ∀ p (q : M.Q p),
      gr0ΞV e p (topO ⊤) (BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 q) =
        ((g.f p).val.app (topO ⊤)).hom (φ p q)) :
    QuasiIso (gr0Ξ e) := by
  choose ν hνiso hνs using fun p => exists_nuHom P M Sc φ hφ p (hfin p)
  have comm : ∀ p, ν p ≫ P.G0D ⊤ M p = Sc.d p (p + 1) ≫ ν (p + 1) := by
    intro p
    refine (bijective_gammaT_map (R := (ringOf P.A0).over ⊤) (Over.mkIdTerminal (X := ⊤))
      (hfin p) (P.G0Sh ⊤ M (p + 1))).1 ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (s : P.FSec ⊤ Sc p (topO ⊤)) => ?_)
    show ((P.G0D ⊤ M p).val.app (topO ⊤)).hom (((ν p).val.app (topO ⊤)).hom s) =
      ((ν (p + 1)).val.app (topO ⊤)).hom (((Sc.d p (p + 1)).val.app (topO ⊤)).hom s)
    rw [hνs, hνs]
    refine (X0comp_bc_tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.toQuasiCohesive p 1
      ((φ p).symm s)).trans ?_
    refine congrArg (BCGen.tmul (P.D.res (leOfHom (topO ⊤).unop.hom)) M.Q 1 ·) ?_
    apply (φ (p + 1)).injective
    rw [AddEquiv.apply_symm_apply, hX0, AddEquiv.apply_symm_apply]
    rfl
  let νc : Sc ⟶ P.G0 ⊤ M :=
    { f := ν
      comm' := fun i j hij => by
        obtain rfl : i + 1 = j := hij
        have e1 : (P.G0 ⊤ M).d i (i + 1) = P.G0D ⊤ M i := CochainComplex.of_d _ _ _
        rw [e1]
        exact comm i }
  have hiso : IsIso νc := by
    haveI : ∀ n, IsIso (νc.f n) := fun n => hνiso n
    exact HomologicalComplex.Hom.isIso_of_components _
  have hcomp : νc ≫ gr0Ξ e = g := by
    refine HomologicalComplex.hom_ext _ _ fun p => ?_
    refine (bijective_gammaT_map (R := (ringOf P.A0).over ⊤) (Over.mkIdTerminal (X := ⊤))
      (hfin p) (F.X p)).1 ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (s : P.FSec ⊤ Sc p (topO ⊤)) => ?_)
    show ((gr0Ξn e p).val.app (topO ⊤)).hom (((ν p).val.app (topO ⊤)).hom s) =
      ((g.f p).val.app (topO ⊤)).hom s
    rw [hνs]
    exact (hg p _).trans (congrArg _ (AddEquiv.apply_symm_apply _ _))
  have h1 : QuasiIso νc := quasiIso_of_isIso _
  have h2 : QuasiIso (νc ≫ gr0Ξ e) := by rw [hcomp]; infer_instance
  exact quasiIso_of_comp_left νc (gr0Ξ e)

end Nu

end PreResolvingData

namespace ResolvingData

variable (D : ResolvingData X)

/-- The complex of global sections `Γ(Pt)` as a complex of `𝒜⁰(X)`-modules. -/
private abbrev PcOf (Pt : CochainComplex (Mod (ringOf D.A0)) ℤ) :
    CochainComplex (ModuleCat.{0} ↥(D.𝒜X 0)) ℤ :=
  ((globalSections (ringOf D.A0)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Pt

/-- The restriction to `⊤` of `f⁰`, followed by `(𝒜⁰ ⊗ K')|⊤ ≅ 𝒜⁰|⊤ ⊗ K'|⊤`. -/
private def gMap (K' : CochainComplex (Mod D.R) ℤ) (Pt : CochainComplex (Mod (ringOf D.A0)) ℤ)
    (f₀ : Pt ⟶ ((sheafBC D.ρSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K') :
    ((restr (ringOf D.A0) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj Pt ⟶
      D.FK ⊤ (((restr D.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K') :=
  ((restr (ringOf D.A0) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map f₀ ≫
    (overBCComplexIso D.ρSheaf ⊤ K').hom

/-- `gMap` is a quasi-isomorphism (restriction is exact). -/
private instance quasiIso_gMap (K' : CochainComplex (Mod D.R) ℤ)
    (Pt : CochainComplex (Mod (ringOf D.A0)) ℤ)
    (f₀ : Pt ⟶ ((sheafBC D.ρSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K')
    [QuasiIso f₀] : QuasiIso (gMap D K' Pt f₀) := by
  unfold gMap
  have : QuasiIso (((restr (ringOf D.A0) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map f₀) :=
    inferInstance
  have h1 : IsIso (overBCComplexIso D.ρSheaf ⊤ K').hom := Iso.isIso_hom _
  have h2 : QuasiIso (overBCComplexIso D.ρSheaf ⊤ K').hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ' := h2)

/-- The quasi-cohesive module `N_⊤` of a connection, over `𝒜(X)` (`⊤` is `(topO ⊤).left`). -/
private abbrev NN {K' : CochainComplex (Mod D.R) ℤ}
    (θ : D.Conn ⊤ (D.FK ⊤ (((restr D.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K'))) :
    QuasiCohesive D.𝒜X := θ.N (PreResolvingData.topO ⊤)

/-- The chain map `e⁰ : Γ(Pt) → N_⊤.complex0`, `Γ_⊤` of `gMap` followed by `iso0`. -/
private def e0Map (K' : CochainComplex (Mod D.R) ℤ) (Pt : CochainComplex (Mod (ringOf D.A0)) ℤ)
    (f₀ : Pt ⟶ ((sheafBC D.ρSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K')
    (θ : D.Conn ⊤ (D.FK ⊤ (((restr D.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K'))) :
    PcOf D Pt ⟶ (NN D θ).complex0 :=
  ((gammaT ((ringOf D.A0).over ⊤) (Over.mk (𝟙 ⊤))).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (gMap D K' Pt f₀) ≫ (PreResolvingData.iso0 θ).hom

/-- `e⁰` is a quasi-isomorphism: `Γ(f⁰)` is one (S3, `𝒜⁰` fine), the rest are isomorphisms. -/
private theorem quasiIso_e0Map [CompactSpace X] (K' : CochainComplex (Mod D.R) ℤ)
    (Pt : CochainComplex (Mod (ringOf D.A0)) ℤ)
    (f₀ : Pt ⟶ ((sheafBC D.ρSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K')
    [QuasiIso f₀]
    (θ : D.Conn ⊤ (D.FK ⊤ (((restr D.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K'))) :
    QuasiIso (e0Map D K' Pt f₀ θ) := by
  have h1 : QuasiIso (((globalSections (ringOf D.A0)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f₀) := quasiIso_globalSections D.isFine0 f₀
  have h2 : IsIso (((gammaT ((ringOf D.A0).over ⊤) (Over.mk (𝟙 ⊤))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (overBCComplexIso D.ρSheaf ⊤ K').hom) :=
    (((gammaT ((ringOf D.A0).over ⊤) (Over.mk (𝟙 ⊤))).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso (overBCComplexIso D.ρSheaf ⊤ K')).isIso_hom
  have h3 : QuasiIso (((gammaT ((ringOf D.A0).over ⊤) (Over.mk (𝟙 ⊤))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (overBCComplexIso D.ρSheaf ⊤ K').hom) := quasiIso_of_isIso _
  have h6 : IsIso (PreResolvingData.iso0 θ).hom := (PreResolvingData.iso0 θ).isIso_hom
  have h4 : QuasiIso (PreResolvingData.iso0 θ).hom := quasiIso_of_isIso _
  have h5 : ((gammaT ((ringOf D.A0).over ⊤) (Over.mk (𝟙 ⊤))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (gMap D K' Pt f₀) =
      ((globalSections (ringOf D.A0)).mapHomologicalComplex (ComplexShape.up ℤ)).map f₀ ≫
      ((gammaT ((ringOf D.A0).over ⊤) (Over.mk (𝟙 ⊤))).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (overBCComplexIso D.ρSheaf ⊤ K').hom := rfl
  unfold e0Map
  rw [h5]
  exact quasiIso_comp _ _ (hφ := quasiIso_comp _ _ (hφ := h1) (hφ' := h3)) (hφ' := h4)

/-- The core: for `M` from A11 and `e` with `(0,0)`-component `e⁰ = Γ_⊤(g)`, `gr0Ξ e` is a
quasi-isomorphism (it is `g` up to the isomorphism `G0 M ≅ Pt|⊤`). -/
private theorem quasiIso_gr0Ξ_core [CompactSpace X] (K' : CochainComplex (Mod D.R) ℤ)
    (Pt : CochainComplex (Mod (ringOf D.A0)) ℤ) (hfree : ∀ n, IsFinFreeSummand (Pt.X n))
    (f₀ : Pt ⟶ ((sheafBC D.ρSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K')
    [QuasiIso f₀]
    (θ : D.Conn ⊤ (D.FK ⊤ (((restr D.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K')))
    (a b₀ : ℤ) [(PcOf D Pt).IsStrictlyGE a] [(PcOf D Pt).IsStrictlyLE b₀]
    [∀ p, Module.Finite ↥(D.𝒜X 0) ((PcOf D Pt).X p)]
    [∀ p, Module.Projective ↥(D.𝒜X 0) ((PcOf D Pt).X p)]
    (θ' : GenData D.𝒜X (Gens (PcOf D Pt)))
    (hθ' : ∀ p (x : Gens (PcOf D Pt) p),
      θ'.θ (lof (D.𝒜X 0) ℤ (Gens (PcOf D Pt)) p x) ∈ totDeg D.𝒜X (Gens (PcOf D Pt)) (p + 1))
    (hflat' : ∀ x, θ'.extend (θ'.θ x) =
      GCDga.c (𝒜 := D.𝒜X) • Tot.tmul D.𝒜X (Gens (PcOf D Pt)) 1 x)
    (hε : ∀ x, Tot.eps D.𝒜X (Gens (PcOf D Pt)) (θ'.θ x) = dGen (PcOf D Pt) x)
    (e : Z0 (CohesiveModule.ofGenData (PcOf D Pt) a b₀ θ' hθ' hflat').toQuasiCohesive
      (NN D θ))
    (hee : ∀ x, Tot.eps D.𝒜X (NN D θ).Q
      (e.1 (Tot.tmul D.𝒜X (Gens (PcOf D Pt)) 1 x)) = e0N (e0Map D K' Pt f₀ θ) x) :
    QuasiIso (PreResolvingData.gr0Ξ e) := by
  have hX : ∀ p (q : (PcOf D Pt).X p),
      (CohesiveModule.ofGenData (PcOf D Pt) a b₀ θ' hθ' hflat').X0comp p q =
        ((PcOf D Pt).d p (p + 1)).hom q := by
    intro p q
    have h : (CohesiveModule.ofGenData (PcOf D Pt) a b₀ θ' hθ' hflat').X0
        (lof (D.𝒜X 0) ℤ (Gens (PcOf D Pt)) p q) =
        lof (D.𝒜X 0) ℤ (Gens (PcOf D Pt)) (p + 1) (((PcOf D Pt).d p (p + 1)).hom q) := by
      show Tot.eps D.𝒜X (Gens (PcOf D Pt))
        (θ'.extend (Tot.tmul D.𝒜X (Gens (PcOf D Pt)) 1 _)) = _
      rw [GenData.extend_tmul_one, hε]
      exact dGen_lof _ p q
    show DirectSum.component (D.𝒜X 0) ℤ (Gens (PcOf D Pt)) (p + 1)
      ((CohesiveModule.ofGenData (PcOf D Pt) a b₀ θ' hθ' hflat').X0
        (lof (D.𝒜X 0) ℤ (Gens (PcOf D Pt)) p q)) = _
    rw [h, DirectSum.component.lof_self]
  refine PreResolvingData.quasiIso_gr0Ξ_abstract D.toPreResolvingData
    (CohesiveModule.ofGenData (PcOf D Pt) a b₀ θ' hθ' hflat')
    (((restr (ringOf D.A0) ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj Pt)
    (fun p => AddEquiv.refl _) (fun _ _ _ => rfl)
    (fun n => IsFinFreeSummand.restr (ringOf D.A0) ⊤ (hfree n))
    (fun p q => (hX p q).symm ▸ rfl) e (gMap D K' Pt f₀) ?_
  intro p q
  rw [PreResolvingData.gr0ΞV_topO]
  have h1 := DFunLike.congr_fun (hee (lof (D.𝒜X 0) ℤ (Gens (PcOf D Pt)) p q)) p
  have h2 := e0N_lof (N := NN D θ) (e0Map D K' Pt f₀ θ) p q
  rw [h2] at h1
  exact h1.trans (DirectSum.of_eq_same p _)

/-- **C5 steps 4–5 on the over-site of `⊤` (C5.a–c, v1.11).** Let `K'` be bounded above with flat
terms, `Pt` strictly perfect over `𝒜⁰`, `f⁰ : Pt → 𝒜⁰ ⊗_O K'` a quasi-isomorphism, and `θ` the
connection of C7.b on `F = 𝒜⁰ ⊗ K'|⊤`. Then there are a cohesive `M` over `𝒜(X)` and a closed
`e : M → N_{K'}(⊤)` with `gr0Ξ e` a quasi-isomorphism. Proof: `P := Γ(Pt)` is a bounded complex
of finitely generated projective `𝒜⁰(X)`-modules (S4.c); `N_{K'}(⊤).complex0 ≅ Γ(𝒜⁰ ⊗ K')`
(`Conn.eps`, `sheafBCOverIso`); `e⁰ := Γ(f⁰)` is a quasi-isomorphism (S3,
`quasiIso_globalSections`: `𝒜⁰` is fine); A11 (`lifting`, with `flat_piece`) gives `M` on
`𝒜(X) ⊗ P` and `e` with `(0,0)`-component `e⁰`; finally `G0 M ≅ Pt|⊤` and `gr0Ξ e` corresponds
to `f⁰|⊤` (both are maps out of summands of finite free modules with the same `Γ`, S4.c). -/
theorem exists_cohesive_gr0_quasiIso [CompactSpace X] [T2Space X]
    {K' : CochainComplex (Mod D.R) ℤ} (b : ℤ) [K'.IsStrictlyLE b]
    (hflat : ∀ n, IsFlat D.O (K'.X n))
    {Pt : CochainComplex (Mod (ringOf D.A0)) ℤ} (hPt : IsStrictlyPerfect Pt)
    (f₀ : Pt ⟶ ((sheafBC D.ρSheaf).mapHomologicalComplex (ComplexShape.up ℤ)).obj K')
    [QuasiIso f₀]
    (θ : D.Conn ⊤ (D.FK ⊤ (((restr D.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K')))
    (hθ : D.IsBCConn ⊤ (((restr D.R ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K') θ) :
    ∃ (M : CohesiveModule D.𝒜X) (e : Z0 M.toQuasiCohesive (θ.N (PreResolvingData.topO ⊤))),
      QuasiIso (PreResolvingData.gr0Ξ e) := by
  classical
  obtain ⟨⟨a, b₀, ha, hb⟩, hfree⟩ := hPt
  haveI : (PcOf D Pt).IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
      Functor.map_isZero (globalSections (ringOf D.A0)) (Pt.isZero_of_isStrictlyGE a i hi)
  haveI : (PcOf D Pt).IsStrictlyLE b₀ :=
    (CochainComplex.isStrictlyLE_iff _ b₀).2 fun i hi =>
      Functor.map_isZero (globalSections (ringOf D.A0)) (Pt.isZero_of_isStrictlyLE b₀ i hi)
  haveI : ∀ p, Module.Finite ↥(D.𝒜X 0) ((PcOf D Pt).X p) :=
    fun p => finite_globalSections (hfree p)
  haveI : ∀ p, Module.Projective ↥(D.𝒜X 0) ((PcOf D Pt).X p) :=
    fun p => projective_globalSections (hfree p)
  haveI : ∀ q, Module.Flat ↥(D.𝒜X 0) (GCDga.piece D.𝒜X q) := fun q => D.flat_piece q
  haveI := quasiIso_e0Map D K' Pt f₀ θ
  obtain ⟨θ', hθ', hflat', hε, e, he, hee⟩ :=
    lifting (NN D θ) a b₀ (e0Map D K' Pt f₀ θ)
  exact ⟨CohesiveModule.ofGenData (PcOf D Pt) a b₀ θ' hθ' hflat', ⟨e, he⟩,
    quasiIso_gr0Ξ_core D K' Pt hfree f₀ θ a b₀ θ' hθ' hflat' hε ⟨e, he⟩ hee⟩

end ResolvingData

end Cohesive
