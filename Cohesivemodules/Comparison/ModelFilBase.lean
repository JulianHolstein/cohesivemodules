import Cohesivemodules.Comparison.EssSurjCore

set_option linter.style.header false

/-!
# Z3.u: C5 step (D) over an arbitrary base `U` (blueprint-tw G′ (k))

Blueprint item Z3.u (`blueprint/blueprint-tw.md` §3 G′ (k)). The private
`quasiIso_gr0Ξ_abstract` of `EssSurjCore.lean` (C5 step (D)) is stated over the base `⊤`. The
twisted theorem needs it over `U = U_α`: for a cohesive module `M` over `𝒜(U)`, a complex `Sc` of
finite free summands over `𝒜⁰|U` and an `𝒜⁰(U)`-linear identification `φ` of the generators
`M.Q p` with the sections `Sc^p(U)`, compatible with `X0comp`, a closed `e : M → θ.N(U)` whose
`gr0Ξ` agrees on `1 ⊗ q` with a quasi-isomorphism `g : Sc → F` has `gr0Ξ e` a quasi-isomorphism.

* `quasiIso_gr0Ξ_of_equiv`: the statement of `quasiIso_gr0Ξ_abstract` with `U` in place of `⊤`.

## Deviations
* None (a generalization of the base of a C5 lemma; same proof, `Over.mk (𝟙 U)` terminal).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) {U : Opens X} (M : CohesiveModule (P.D.𝒜 U))
  (Sc : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
  (φ : ∀ p, M.Q p ≃+ P.FSec U Sc p (topO U))
  (hφ : ∀ p (r : ↥(P.D.𝒜 U 0)) (q : M.Q p),
    φ p (r • q) = (show ↥(P.D.𝒜 (topO U).unop.left 0) from r) • φ p q)

/-- The bi-additive pairing `(β, q) ↦ β · res_V (φ q)` defining `Θ_V`. -/
private def thetaAuxU (p : ℤ) (V : (Over U)ᵒᵖ) :
    (P.D.res (leOfHom V.unop.hom)).B0 →+ M.Q p →+ P.FSec U Sc p V :=
  AddMonoidHom.mk' (fun β => AddMonoidHom.mk'
    (fun q => (show ↥(P.D.𝒜 V.unop.left 0) from β) • P.fRes U Sc p (toV V) (φ p q))
    (fun q q' => by rw [map_add, map_add, smul_add]))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      exact add_smul (show ↥(P.D.𝒜 V.unop.left 0) from β) (show ↥(P.D.𝒜 V.unop.left 0) from β') _)

include hφ in
/-- `thetaAuxU` is balanced over `𝒜⁰(U)`. -/
private theorem thetaAuxU_balanced (p : ℤ) (V : (Over U)ᵒᵖ) (r : ↥(P.D.𝒜 U 0))
    (β : (P.D.res (leOfHom V.unop.hom)).B0) (q : M.Q p) :
    thetaAuxU P M Sc φ p V (r • β) q = thetaAuxU P M Sc φ p V β (r • q) := by
  show (show ↥(P.D.𝒜 V.unop.left 0) from (r • β : (P.D.res (leOfHom V.unop.hom)).B0)) •
      P.fRes U Sc p (toV V) (φ p q) =
    (show ↥(P.D.𝒜 V.unop.left 0) from β) • P.fRes U Sc p (toV V) (φ p (r • q))
  rw [hφ, P.fRes_smul, smul_smul]
  congr 1
  exact mul_comm _ _

/-- `fRes` is functorial. -/
private theorem fResU_comp (p : ℤ) {V W Y : (Over U)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Y)
    (s : P.FSec U Sc p V) :
    P.fRes U Sc p (f ≫ g) s = P.fRes U Sc p g (P.fRes U Sc p f s) := by
  show ((Sc.X p).val.map (f ≫ g)).hom s = ((Sc.X p).val.map g).hom (((Sc.X p).val.map f).hom s)
  rw [(Sc.X p).val.map_comp]
  rfl

/-- `fRes` along the identity is the identity. -/
private theorem fResU_id (p : ℤ) (V : (Over U)ᵒᵖ) (s : P.FSec U Sc p V) :
    P.fRes U Sc p (𝟙 V) s = s := by
  show ((Sc.X p).val.map (𝟙 V)).hom s = s
  rw [(Sc.X p).val.map_id]
  rfl

include hφ in
/-- `Θ_V : 𝒜⁰(V) ⊗_{𝒜⁰(U)} Q^p → Sc^p(V)`, `β ⊗ q ↦ β · res_V(φ q)`, additively. -/
private def thetaAddU (p : ℤ) (V : (Over U)ᵒᵖ) : P.G0Sec U M p V →+ P.FSec U Sc p V :=
  TensorProduct.liftAddHom (R := ↥(P.D.𝒜 U 0)) (thetaAuxU P M Sc φ p V)
    (thetaAuxU_balanced P M Sc φ hφ p V)

include hφ in
/-- `thetaAddU` on pure tensors. -/
private theorem thetaAddU_tmul (p : ℤ) (V : (Over U)ᵒᵖ) (β : ↥(P.D.𝒜 V.unop.left 0))
    (q : M.Q p) :
    thetaAddU P M Sc φ hφ p V (BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q β q) =
      β • P.fRes U Sc p (toV V) (φ p q) := rfl

include hφ in
/-- `thetaAddU` is `𝒜⁰(V)`-linear. -/
private theorem thetaAddU_smul (p : ℤ) (V : (Over U)ᵒᵖ) (γ : ↥(P.D.𝒜 V.unop.left 0))
    (x : P.G0Sec U M p V) :
    thetaAddU P M Sc φ hφ p V (γ • x) = γ • thetaAddU P M Sc φ hφ p V x := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [BCGen.smul_tmul, thetaAddU_tmul, thetaAddU_tmul, mul_smul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

include hφ in
/-- `Θ_V` as a linear map. -/
private def thetaLinU (p : ℤ) (V : (Over U)ᵒᵖ) :
    P.G0Sec U M p V →ₗ[↥(P.D.𝒜 V.unop.left 0)] P.FSec U Sc p V where
  toFun := thetaAddU P M Sc φ hφ p V
  map_add' := map_add _
  map_smul' γ x := thetaAddU_smul P M Sc φ hφ p V γ x

include hφ in
/-- `Θ` commutes with restriction. -/
private theorem thetaLinU_res (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.G0Sec U M p V) :
    thetaLinU P M Sc φ hφ p W (P.g0Res U M p f x) =
      P.fRes U Sc p f (thetaLinU P M Sc φ hφ p V x) := by
  induction x using BCGen.induction_on with
  | ht β q =>
    change thetaAddU P M Sc φ hφ p W (P.g0Res U M p f
        (BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q β q)) =
      P.fRes U Sc p f (thetaAddU P M Sc φ hφ p V
        (BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q β q))
    rw [g0Res_tmul, thetaAddU_tmul, thetaAddU_tmul, P.fRes_smul, ← fResU_comp]
    rfl
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

include hφ in
/-- `Θ` as a morphism of sheaves of `𝒜⁰|U`-modules. -/
private def thetaHomU (p : ℤ) : P.G0Sh U M p ⟶ Sc.X p :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (thetaLinU P M Sc φ hφ p V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact thetaLinU_res P M Sc φ hφ p f x }⟩

include hφ in
/-- `φ⁻¹` is semilinear: `φ⁻¹(r s) = r φ⁻¹(s)`. -/
private theorem phiU_symm_smul (p : ℤ) (r : ↥(P.D.𝒜 U 0)) (s : P.FSec U Sc p (topO U)) :
    (φ p).symm ((show ↥(P.D.𝒜 (topO U).unop.left 0) from r) • s) = r • (φ p).symm s := by
  apply (φ p).injective
  rw [hφ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

include hφ in
/-- The additive-and-linear map `s ↦ 1 ⊗ φ⁻¹ s` on sections over `U`. -/
private def nuLinU (p : ℤ) :
    (gammaT ((ringOf P.A0).over U) (Over.mk (𝟙 U))).obj (Sc.X p) ⟶
      (gammaT ((ringOf P.A0).over U) (Over.mk (𝟙 U))).obj (P.G0Sh U M p) :=
  ConcreteCategory.ofHom
    { toFun := fun s => BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 ((φ p).symm s)
      map_add' := fun s s' =>
        (congrArg (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 ·)
          (map_add (φ p).symm s s')).trans (BCGen.tmul_add _ _ _)
      map_smul' := fun r s => by
        let r' : ↥(P.D.𝒜 U 0) := r
        have h1 := phiU_symm_smul P M Sc φ hφ p r' s
        have h3 := BCGen.tmul_smul0 (f := P.D.res (leOfHom (topO U).unop.hom))
          (Q := M.Q) r' ((φ p).symm s)
        have h4 : (P.D.res (leOfHom (topO U).unop.hom)).f0 r' = r' :=
          Subtype.ext (P.D.res_id _ _)
        rw [h4] at h3
        exact (congrArg (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 ·) h1).trans h3 }

include hφ in
/-- `Θ` on `1 ⊗ φ⁻¹ s` over `U` is `s`. -/
private theorem thetaHomU_nu (p : ℤ) (s : P.FSec U Sc p (topO U)) :
    ((thetaHomU P M Sc φ hφ p).val.app (topO U)).hom
      (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 ((φ p).symm s)) = s := by
  show thetaAddU P M Sc φ hφ p (topO U)
    (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 ((φ p).symm s)) = s
  rw [thetaAddU_tmul, one_smul, AddEquiv.apply_symm_apply]
  exact fResU_id P Sc p (topO U) s

include hφ in
/-- **`G0^p ≅ Sc^p`.** For `Sc^p` a summand of a finite free `𝒜⁰|U`-module there is an
isomorphism `ν : Sc^p → G0^p` with `ν(s) = 1 ⊗ φ⁻¹ s` over `U`. -/
private theorem exists_nuHomU (p : ℤ) (hS : IsFinFreeSummand (Sc.X p)) :
    ∃ ν : Sc.X p ⟶ P.G0Sh U M p, IsIso ν ∧ ∀ s : P.FSec U Sc p (topO U),
      (ν.val.app (topO U)).hom s =
        BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 ((φ p).symm s) := by
  obtain ⟨ν, hν⟩ := (bijective_gammaT_map (R := (ringOf P.A0).over U)
    (Over.mkIdTerminal (X := U)) hS (P.G0Sh U M p)).2 (nuLinU P M Sc φ hφ p)
  have hs : ∀ s : P.FSec U Sc p (topO U), (ν.val.app (topO U)).hom s =
      BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 ((φ p).symm s) :=
    fun s => congrArg (fun f => f.hom s) hν
  refine ⟨ν, ?_, hs⟩
  have F1 : ν ≫ thetaHomU P M Sc φ hφ p = 𝟙 _ := by
    refine (bijective_gammaT_map (R := (ringOf P.A0).over U) (Over.mkIdTerminal (X := U)) hS
      (Sc.X p)).1 ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    show ((thetaHomU P M Sc φ hφ p).val.app (topO U)).hom ((ν.val.app (topO U)).hom s) = s
    rw [hs s]
    exact thetaHomU_nu P M Sc φ hφ p s
  have F2 : thetaHomU P M Sc φ hφ p ≫ ν = 𝟙 _ := by
    refine P.g0Sh_hom_ext U M p _ _ fun q => ?_
    show (ν.val.app (topO U)).hom (((thetaHomU P M Sc φ hφ p).val.app (topO U)).hom
      (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q)) =
      BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q
    have h1 : ((thetaHomU P M Sc φ hφ p).val.app (topO U)).hom
        (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q) = φ p q := by
      have := thetaHomU_nu P M Sc φ hφ p (φ p q)
      rw [AddEquiv.symm_apply_apply] at this
      exact this
    rw [h1, hs, AddEquiv.symm_apply_apply]
  exact ⟨⟨thetaHomU P M Sc φ hφ p, F1, F2⟩⟩

include hφ in
/-- **Z3.u (G′ (k), C5 step (D) over `U`).** [A, Prop 7.2.18], blueprint C5 (D). Let `M` be a
cohesive module over `𝒜(U)`, `Sc` a complex of finite free summands over `𝒜⁰|U`, and
`φ_p : M.Q p ≃ Sc^p(U)` additive equivalences, `𝒜⁰(U)`-linear (`hφ`) and intertwining `X0comp`
with the differential of `Sc` (`hX0`). If `e ∈ Z0(M, θ.N(U))` satisfies
`gr0Ξ e (1 ⊗ q) = g(φ q)` for a quasi-isomorphism `g : Sc → F` (`hg`), then `gr0Ξ e : G0(M) → F` is
a quasi-isomorphism. The private `quasiIso_gr0Ξ_abstract` is the case `U = ⊤`. -/
theorem quasiIso_gr0Ξ_of_equiv (hfin : ∀ n, IsFinFreeSummand (Sc.X n))
    (hX0 : ∀ p (q : M.Q p), φ (p + 1) (M.X0comp p q) = P.fD U Sc p (topO U) (φ p q))
    {F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ} {θ : P.Conn U F}
    (e : Z0 M.toQuasiCohesive (θ.N (topO U))) (g : Sc ⟶ F) [QuasiIso g]
    (hg : ∀ p (q : M.Q p),
      gr0ΞV e p (topO U) (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 q) =
        ((g.f p).val.app (topO U)).hom (φ p q)) :
    QuasiIso (gr0Ξ e) := by
  choose ν hνiso hνs using fun p => exists_nuHomU P M Sc φ hφ p (hfin p)
  have comm : ∀ p, ν p ≫ P.G0D U M p = Sc.d p (p + 1) ≫ ν (p + 1) := by
    intro p
    refine (bijective_gammaT_map (R := (ringOf P.A0).over U) (Over.mkIdTerminal (X := U))
      (hfin p) (P.G0Sh U M (p + 1))).1 ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (s : P.FSec U Sc p (topO U)) => ?_)
    show ((P.G0D U M p).val.app (topO U)).hom (((ν p).val.app (topO U)).hom s) =
      ((ν (p + 1)).val.app (topO U)).hom (((Sc.d p (p + 1)).val.app (topO U)).hom s)
    rw [hνs, hνs]
    refine (X0comp_bc_tmul (P.D.res (leOfHom (topO U).unop.hom)) M.toQuasiCohesive p 1
      ((φ p).symm s)).trans ?_
    refine congrArg (BCGen.tmul (P.D.res (leOfHom (topO U).unop.hom)) M.Q 1 ·) ?_
    apply (φ (p + 1)).injective
    rw [AddEquiv.apply_symm_apply, hX0, AddEquiv.apply_symm_apply]
    rfl
  let νc : Sc ⟶ P.G0 U M :=
    { f := ν
      comm' := fun i j hij => by
        obtain rfl : i + 1 = j := hij
        have e1 : (P.G0 U M).d i (i + 1) = P.G0D U M i := CochainComplex.of_d _ _ _
        rw [e1]
        exact comm i }
  have hiso : IsIso νc := by
    have : ∀ n, IsIso (νc.f n) := fun n => hνiso n
    exact HomologicalComplex.Hom.isIso_of_components _
  have hcomp : νc ≫ gr0Ξ e = g := by
    refine HomologicalComplex.hom_ext _ _ fun p => ?_
    refine (bijective_gammaT_map (R := (ringOf P.A0).over U) (Over.mkIdTerminal (X := U))
      (hfin p) (F.X p)).1 ?_
    refine ModuleCat.hom_ext (LinearMap.ext fun (s : P.FSec U Sc p (topO U)) => ?_)
    show ((gr0Ξn e p).val.app (topO U)).hom (((ν p).val.app (topO U)).hom s) =
      ((g.f p).val.app (topO U)).hom s
    rw [hνs]
    exact (hg p _).trans (congrArg _ (AddEquiv.apply_symm_apply _ _))
  have h1 : QuasiIso νc := quasiIso_of_isIso _
  have h2 : QuasiIso (νc ≫ gr0Ξ e) := by rw [hcomp]; infer_instance
  exact quasiIso_of_comp_left νc (gr0Ξ e)

end PreResolvingData

end Cohesive
