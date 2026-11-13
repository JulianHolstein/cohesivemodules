import Cohesivemodules.Algebra.TotalQuasiIsoGr

set_option linter.style.header false

/-!
# A12: the total quasi-isomorphism (part 3 of 3)

Split from `Algebra/TotalQuasiIso.lean` for size;
continues `Algebra/TotalQuasiIsoGr.lean`.
-/

namespace Cohesive
open CategoryTheory DirectSum TensorProduct
noncomputable section
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
variable {M₁ M₂ : QuasiCohesive 𝒜} {φ : M₁.T →ₗ[k] M₂.T}

namespace QuasiCohesive

variable (M : QuasiCohesive 𝒜)

/-- A12: the identification `F^0 = Tot` in degree `m`. -/
def filZeroEquiv (m : ℤ) : M.filDeg 0 m ≃ₗ[k] totDeg 𝒜 M.Q m :=
  LinearEquiv.ofEq _ _ (M.filDeg_zero m)

/-- A12: `filZeroEquiv` commutes with the differentials. -/
theorem filZeroIso_comm (hc : GCDga.c (𝒜 := 𝒜) = 0) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (M.filZeroEquiv i).toModuleIso.hom ≫ (M.totComplex hc).d i j =
      (M.filComplex hc 0).d i j ≫ (M.filZeroEquiv j).toModuleIso.hom := by
  obtain rfl : j = i + 1 := hij.symm
  ext x
  simp only [ModuleCat.hom_comp, totComplex, filComplex, CochainComplex.of_d,
    ModuleCat.hom_ofHom]
  rfl

/-- A12: the isomorphism of complexes `F^0 ≅ Tot`. -/
def filZeroIso (hc : GCDga.c (𝒜 := 𝒜) = 0) : M.filComplex hc 0 ≅ M.totComplex hc :=
  HomologicalComplex.Hom.isoOfComponents (fun m => (M.filZeroEquiv m).toModuleIso)
    (M.filZeroIso_comm hc)

end QuasiCohesive

/-- A12: the identifications `F^0 ≅ Tot` intertwine `filMap φ 0` and `totMap φ`. -/
theorem filZeroIso_naturality (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) :
    filMap hc hφ 0 ≫ (M₂.filZeroIso hc).hom = (M₁.filZeroIso hc).hom ≫ totMap hc hφ := by
  ext m x
  rfl

/-- A12: `totMap φ` is `filMap φ 0` up to the identification `F^0 = Tot` (`filDeg_zero`). -/
def totArrowIso (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) :
    Arrow.mk (filMap hc hφ 0) ≅ Arrow.mk (totMap hc hφ) :=
  Arrow.isoMk (M₁.filZeroIso hc) (M₂.filZeroIso hc) (filZeroIso_naturality hc hφ)

/-- A12: index bookkeeping `(b : ℤ) + 1 = ((b + 1 : ℕ) : ℤ)` for `filMap`. -/
theorem filMap_arrow_succ (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) (b : ℕ) :
    Arrow.mk (filMap hc hφ ((b : ℤ) + 1)) = Arrow.mk (filMap hc hφ ((b + 1 : ℕ) : ℤ)) := by
  rw [Nat.cast_succ]

/-- A12 (form with an explicit `(0,0)`-component): as `totMap_quasiIso`, with the
`(0,0)`-component given as a chain map `f₀` together with `IsLead0 φ f₀` (`ε(φ(1 ⊗ e)) = f₀ e`).
`f₀` is determined by `φ` (`IsLead0` fixes every component), so this is equivalent to
`totMap_quasiIso`. Proof: A7 (`quasiIso_of_finite_filtration`) with the form-degree filtration
`F^b` (A6), whose graded pieces are `A^b ⊗ (Q, 𝕏⁰)` up to shift. ⚠ Needs `c = 0`. -/
theorem totMap_quasiIso_of_lead (hc : GCDga.c (𝒜 := 𝒜) = 0)
    [∀ b, Module.Flat (𝒜 0) (GCDga.piece 𝒜 b)]
    (hφ : φ ∈ Z0 M₁ M₂) (f₀ : M₁.complex0 ⟶ M₂.complex0) [QuasiIso f₀] (h₀ : IsLead0 φ f₀) :
    QuasiIso (totMap hc hφ) := by
  have key : QuasiIso (filMap hc hφ ((0 : ℕ) : ℤ)) :=
    quasiIso_of_finite_filtration (GCDga.N 𝒜 + 1) (fun b => M₁.filSC hc b)
      (fun b => M₂.filSC hc b) (fun b => M₁.filSC_shortExact hc b)
      (fun b => M₂.filSC_shortExact hc b) (fun b => filSCMap hc hφ f₀ h₀ b)
      (fun b => ⟨_, _, filMap hc hφ b⟩) (fun b => filMap_arrow_succ hc hφ b) (fun b => rfl)
      (fun b _ => grMap_quasiIso (b : ℤ) f₀)
      (filMap_quasiIso_of_gt hc hφ (by push_cast; omega))
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (totArrowIso hc hφ)).1 key

/-! ## The `(0,0)`-component of a closed degree-`0` map -/

/-- A12 helper: `proj0` of an element of `A⁰` is itself. -/
private theorem proj0_coe (f : 𝒜 0) : Tot.proj0 𝒜 (f : A) = f :=
  Subtype.ext ((GCDga.proj_of_mem 𝒜 f.2).trans (by simp))

/-- A12 helper: `ε(φ(1 ⊗ f·e)) = f · ε(φ(1 ⊗ e))` for `φ ∈ Hom⁰`. -/
private theorem eps_hom_tmul_one_smul (hφ : φ ∈ Hom M₁ M₂ 0) (f : 𝒜 0) (e : ⨁ p, M₁.Q p) :
    Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (f • e))) =
      f • Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 e)) := by
  rw [Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul, hφ.2 f.2, mul_zero, Int.negOnePow_zero,
    one_smul, Tot.eps_smul, proj0_coe]

/-- A12: the `(0,0)`-component of a degree-`0` map is `A⁰`-linear. -/
theorem comp0L_smul (hφ : φ ∈ Hom M₁ M₂ 0) (p : ℤ) (f : 𝒜 0) (e : M₁.Q p) :
    Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p (f • e)))) p =
      f • Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p e))) p := by
  rw [map_smul, eps_hom_tmul_one_smul hφ, DirectSum.smul_apply]

/-- A12: the `(0,0)`-component `φ⁰ : Q₁^p → Q₂^p` of a degree-`0` map `φ`: the `A⁰ ⊗ Q₂^p`-part
of `φ(1 ⊗ e)`, i.e. the degree-`p` component of `ε(φ(1 ⊗ e))`. -/
def comp0L (hφ : φ ∈ Hom M₁ M₂ 0) (p : ℤ) : M₁.Q p →ₗ[𝒜 0] M₂.Q p where
  toFun e := Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p e))) p
  map_add' e e' := by
    rw [map_add, Tot.tmul_add, map_add, map_add, DirectSum.add_apply]
  map_smul' f e := comp0L_smul hφ p f e

/-- A12 helper: `ε ∘ φ` factors through `ε`: `ε(φ x) = G(ε x)` with `G e = ε(φ(1 ⊗ e))`. -/
private theorem eps_hom_eq (hφ : φ ∈ Hom M₁ M₂ 0) (x : M₁.T) :
    Tot.eps 𝒜 M₂.Q (φ x) =
      Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (Tot.eps 𝒜 M₁.Q x))) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [homT_tmul (𝒜 := 𝒜) (Q₁ := M₁.Q) (Q₂ := M₂.Q) hφ, GCDga.twist_zero, Tot.eps_smul,
      Tot.eps_tmul, eps_hom_tmul_one_smul hφ]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, Tot.tmul_add, map_add, map_add]

/-- A12 helper: `ε(φ(1 ⊗ e))` is concentrated in degree `p` for `e ∈ Q₁^p`. -/
private theorem eps_hom_eq_lof (hφ : φ ∈ Hom M₁ M₂ 0) (p : ℤ) (e : M₁.Q p) :
    Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p e))) =
      lof (𝒜 0) ℤ M₂.Q p (comp0L hφ p e) := by
  have h1 := hφ.1 (tmul_mem_totDeg (𝒜 := 𝒜) (SetLike.GradedOne.one_mem (A := 𝒜)) e)
  rw [zero_add, add_zero] at h1
  exact eq_lof_of_concAt (Tot.eps_concAt h1)

/-- A12: `φ⁰` commutes with `𝕏⁰` when `φ` is closed. -/
theorem comp0_sq (hφ : φ ∈ Z0 M₁ M₂) (p : ℤ) :
    ModuleCat.ofHom (comp0L hφ.1 p) ≫ M₂.complex0.d p (p + 1) =
      M₁.complex0.d p (p + 1) ≫ ModuleCat.ofHom (comp0L hφ.1 (p + 1)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun e => ?_)
  have hX : ∀ y, M₂.X (φ y) = φ (M₁.X y) := fun y => by
    have h := LinearMap.congr_fun (LinearMap.mem_ker.1 hφ.2) y
    rw [δ_apply, Int.negOnePow_zero, one_smul] at h
    exact sub_eq_zero.1 h
  have h1 := eps_hom_eq hφ.1 (M₁.X (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p e)))
  rw [← hX, M₂.eps_X, M₁.eps_X, ← Tot.oneTmul_apply, Tot.eps_oneTmul, Tot.oneTmul_apply,
    eps_hom_eq_lof hφ.1, QuasiCohesive.X0_lof, QuasiCohesive.X0_lof,
    eps_hom_eq_lof hφ.1] at h1
  have h3 := congrArg (DirectSum.component (𝒜 0) ℤ M₂.Q (p + 1)) h1
  simp only [DirectSum.component.lof_self] at h3
  show (M₂.complex0.d p (p + 1)).hom (comp0L hφ.1 p e) =
    comp0L hφ.1 (p + 1) ((M₁.complex0.d p (p + 1)).hom e)
  rw [QuasiCohesive.complex0_d, QuasiCohesive.complex0_d]
  exact h3

/-- **A12** The `(0,0)`-component of a closed degree-`0` map `φ ∈ Z⁰(M₁, M₂)` as a chain map
`φ⁰ : (Q₁, 𝕏₁⁰) → (Q₂, 𝕏₂⁰)` of complexes of `A⁰`-modules: in degree `p`,
`e ↦ (ε(φ(1 ⊗ e)))_p`, the `A⁰ ⊗ Q₂^p`-part of `φ(1 ⊗ e)`. [B, Prop 2.5.2], [A, Lemma 3.3.5]
(`φ^0` there). A chain map because `δφ = 0` in form degree `0`. -/
def Z0.comp0 (hφ : φ ∈ Z0 M₁ M₂) : M₁.complex0 ⟶ M₂.complex0 :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (comp0L hφ.1 p)) (comp0_sq hφ)

/-- A12: `Z0.comp0 φ` is the `(0,0)`-component of `φ` in the sense of `IsLead0`. -/
theorem isLead0_comp0 (hφ : φ ∈ Z0 M₁ M₂) : IsLead0 φ (Z0.comp0 hφ) :=
  fun p e => eps_hom_eq_lof hφ.1 p e

/-- **A12 (total quasi-isomorphism).** Assume the curvature vanishes and each `A^b` is flat over
`A⁰`. Let `φ : M₁ → M₂` be a closed degree-`0` map of quasi-cohesive modules whose
`(0,0)`-component `φ⁰ = Z0.comp0 φ : (Q₁, 𝕏₁⁰) → (Q₂, 𝕏₂⁰)` is a quasi-isomorphism of
complexes of `A⁰`-modules. Then `φ` is a quasi-isomorphism of total complexes
`(Tot M₁, 𝕏₁) → (Tot M₂, 𝕏₂)` (complexes of `k`-modules graded by total degree).
[A, proof of Prop 7.2.18]; blueprint A12. Proof: `totMap_quasiIso_of_lead` (A7 with the
form-degree filtration) and `isLead0_comp0`.

Deviations: stated for any closed degree-`0` map between quasi-cohesive modules (the blueprint
states it for the map `e` of A11; see `lifting_quasiIso`). ⚠ Needs `c = 0`: the total complex
is only a complex then. -/
theorem totMap_quasiIso (hc : GCDga.c (𝒜 := 𝒜) = 0) [∀ b, Module.Flat (𝒜 0) (GCDga.piece 𝒜 b)]
    (hφ : φ ∈ Z0 M₁ M₂) [QuasiIso (Z0.comp0 hφ)] : QuasiIso (totMap hc hφ) :=
  totMap_quasiIso_of_lead hc hφ (Z0.comp0 hφ) (isLead0_comp0 hφ)

/-! ## A12 for the map of the lifting theorem -/

section Lifting

variable {Pc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ} (a b : ℤ) [Pc.IsStrictlyGE a]
  [Pc.IsStrictlyLE b] [∀ p, Module.Finite (𝒜 0) (Pc.X p)] [∀ p, Module.Projective (𝒜 0) (Pc.X p)]
  (θ : GenData 𝒜 (Gens Pc))
  (hθ : ∀ p (x : Gens Pc p), θ.θ (lof (𝒜 0) ℤ (Gens Pc) p x) ∈ totDeg 𝒜 (Gens Pc) (p + 1))
  (hflat : ∀ x, θ.extend (θ.θ x) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 (Gens Pc) 1 x)

/-- A12: if `ε ∘ θ = ∂`, the identity maps `P^p → P^p` commute with `∂` and `𝔼⁰`. -/
theorem complex0IsoOfGen_comm (hε : ∀ x, Tot.eps 𝒜 (Gens Pc) (θ.θ x) = dGen Pc x) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (Iso.refl (Pc.X i)).hom ≫
        (CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive.complex0.d i j =
      Pc.d i j ≫ (Iso.refl (Pc.X j)).hom := by
  obtain rfl : j = i + 1 := hij.symm
  ext e
  have h2 : (CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive.X0
      (lof (𝒜 0) ℤ (Gens Pc) i e) =
      lof (𝒜 0) ℤ (Gens Pc) (i + 1) ((Pc.d i (i + 1)).hom e) := by
    refine Eq.trans ?_ ((hε (lof (𝒜 0) ℤ (Gens Pc) i e)).trans (dGen_lof Pc i e))
    show Tot.eps 𝒜 (Gens Pc) (θ.extend (Tot.tmul 𝒜 (Gens Pc) 1 (lof (𝒜 0) ℤ (Gens Pc) i e))) = _
    rw [GenData.extend_tmul_one]
  have key : ((CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive.complex0.d i (i + 1)).hom
      e = (Pc.d i (i + 1)).hom e := by
    refine (QuasiCohesive.complex0_d
      (CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive i e).trans ?_
    show DirectSum.component (𝒜 0) ℤ _ (i + 1)
      (QuasiCohesive.X0 (CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive
        (lof (𝒜 0) ℤ (Gens Pc) i e)) = _
    rw [h2]
    exact DirectSum.component.lof_self (R := 𝒜 0) (i + 1) _
  exact key

/-- A12: if `ε ∘ θ = ∂` (`𝔼⁰ = ∂`), the complex `(P, 𝔼⁰)` of the cohesive module `A ⊗ P` built
by the lifting theorem is `(P, ∂)`; the components are identities. -/
def complex0IsoOfGen (hε : ∀ x, Tot.eps 𝒜 (Gens Pc) (θ.θ x) = dGen Pc x) :
    Pc ≅ (CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive.complex0 :=
  HomologicalComplex.Hom.isoOfComponents (fun p => Iso.refl (Pc.X p))
    (complex0IsoOfGen_comm a b θ hθ hflat hε)

end Lifting

/-- **A12 for the lifting theorem.** In the situation of A11 (`lifting`), assume moreover that
the curvature vanishes. Then the lifting theorem's conclusion holds with, in addition, `e` a
quasi-isomorphism of total complexes `(A ⊗ P, 𝔼) → (Tot N, 𝕏)`. Blueprint A12 as stated
([A, proof of Prop 7.2.18]); from `lifting` and `totMap_quasiIso`. ⚠ Needs `c = 0`. -/
theorem lifting_quasiIso {Pc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ}
    (hc : GCDga.c (𝒜 := 𝒜) = 0)
    [∀ b, Module.Flat (𝒜 0) (GCDga.piece 𝒜 b)] (N : QuasiCohesive 𝒜)
    (a b : ℤ) [Pc.IsStrictlyGE a] [Pc.IsStrictlyLE b]
    [∀ p, Module.Finite (𝒜 0) (Pc.X p)] [∀ p, Module.Projective (𝒜 0) (Pc.X p)]
    (e₀ : Pc ⟶ N.complex0) [QuasiIso e₀] :
    ∃ (θ : GenData 𝒜 (Gens Pc))
      (hθ : ∀ p (x : Gens Pc p), θ.θ (lof (𝒜 0) ℤ (Gens Pc) p x) ∈ totDeg 𝒜 (Gens Pc) (p + 1))
      (hflat : ∀ x, θ.extend (θ.θ x) = GCDga.c (𝒜 := 𝒜) • Tot.tmul 𝒜 (Gens Pc) 1 x),
      (∀ x, Tot.eps 𝒜 (Gens Pc) (θ.θ x) = dGen Pc x) ∧
      ∃ e, ∃ he : e ∈ Z0 (CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive N,
        (∀ x, Tot.eps 𝒜 N.Q (e (Tot.tmul 𝒜 (Gens Pc) 1 x)) = e0N e₀ x) ∧
        QuasiIso (totMap hc he) := by
  obtain ⟨θ, hθ, hflat, hε, e, he, hee⟩ := lifting (𝒜 := 𝒜) N a b e₀
  refine ⟨θ, hθ, hflat, hε, e, he, hee, ?_⟩
  let f₀ : (CohesiveModule.ofGenData Pc a b θ hθ hflat).toQuasiCohesive.complex0 ⟶
      N.complex0 := (complex0IsoOfGen a b θ hθ hflat hε).inv ≫ e₀
  have : QuasiIso f₀ := inferInstance
  have h₀ : IsLead0 e f₀ := fun p x =>
    (hee (lof (𝒜 0) ℤ (Gens Pc) p x)).trans (e0N_lof e₀ p x)
  exact totMap_quasiIso_of_lead hc he f₀ h₀

end

end Cohesive
