import Cohesivemodules.Comparison.FullyFaithful
import Cohesivemodules.Sheaf.HomSectionsMap
import Cohesivemodules.Algebra.QuasiIsoElem

set_option linter.style.header false

/-!
# C4 step 5: the `H⁰` dictionary on global sections

Blueprint item C4 (§4), step 5. For a chain map `r : α(M₂) ⟶ I` such that
`Γ(Ψ ≫ r_*) : Γ ℋ(M₁, M₂) → Γ 𝓗om(α(M₁), I)` is a quasi-isomorphism, `H⁰` of this map is a
bijection
`H0(M₁, M₂) → {chain maps α(M₁) → I}/homotopy`, `[φ] ↦ [α(φ) ≫ r]`:
* `Γ ℋ(M₁, M₂)ⁿ ≅ Hom^n(M₁, M₂)` compatibly with `δ` (C3: `homTop_bijective`, `homδV_homTop`);
* `Γ 𝓗om(α(M₁), I)ⁿ ≅ Cochain(α(M₁), I, n)` compatibly with `δ`
  (`homComplexSectionsEquiv`, `exists_cochain_overTop_equiv`), and `Γ(r_*)` is `· ≫ r`
  (`homComplexSectionsEquiv_homComplexMap₂`);
* `Ψ` sends `φ ∈ Z0` to `α(φ)` (`Ψ_top`);
* a degree-`0` cocycle of `Cochain(K, L)` is a chain map, and a coboundary difference is a
  homotopy (`Cochain.equivHomotopy`);
* `H⁰` of a quasi-isomorphism of complexes of modules is bijective, elementwise
  (`exists_cocycle_of_quasiIso`, `exists_eq_d_of_quasiIso`).

Also: `α(M)` is bounded above (needed for `𝓗om(α(M₁), I)` to be bounded below).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X)

/-- Elements of total degree `m > b + N` of `𝒜 ⊗ Q` vanish when `Q^p = 0` for `p > b` and
`𝒜^q = 0` for `q > N`. -/
private theorem eq_zero_of_totDeg_gt {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
    {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    (b N : ℤ) (hQ : ∀ p, b < p → Subsingleton (Q p)) (hA : ∀ q, N < q → ∀ a ∈ 𝒜 q, a = 0)
    {m : ℤ} (hm : b + N < m) {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) : x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, hqp, ha, rfl⟩ := hx
    by_cases hp : b < p
    · have := hQ p hp
      rw [Subsingleton.elim e 0, map_zero, TensorProduct.tmul_zero]
      rfl
    · rw [hA q (by lia) a ha, TensorProduct.zero_tmul]
      rfl
  | zero => rfl
  | add x y _ _ hx hy => rw [hx, hy, add_zero]
  | smul r x _ hx => rw [hx, smul_zero]

/-- `α(M)` is bounded above, for compact `X`. -/
private theorem exists_isStrictlyLE_sheafOf_aux [CompactSpace X] (M : CohesiveModule P.𝒜X) :
    ∃ n : ℤ, (P.sheafOf M).IsStrictlyLE n := by
  obtain ⟨a, b, h⟩ := M.bounded
  refine ⟨b + GCDga.N (𝒜 := P.𝒜X), ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  change Limits.IsZero (P.sheafOfSh M n)
  refine isZero_of_sections_subsingleton fun V => ⟨fun x y => ?_⟩
  have hz : ∀ z : P.sheafOfSec M n (le_top : V.unop ≤ ⊤), z = 0 := fun z =>
    Subtype.ext (eq_zero_of_totDeg_gt (𝒜 := P.D.𝒜 V.unop)
      (Q := (M.baseChange (P.D.res (le_top : V.unop ≤ ⊤))).Q) b (GCDga.N (𝒜 := P.𝒜X))
      (fun p hp => bcGen_subsingleton (P.D.res (le_top : V.unop ≤ ⊤)) (Q := M.Q) p
        (h p (Or.inr hp)))
      (fun q hq a ha => P.zero_above hq V.unop ha) hn z.2)
  exact (hz x).trans (hz y).symm

/-- **C4 step 5.** `α(M)` is bounded above: `α(M)ⁿ = 0` above the top degree of the generators
plus the top form degree `GCDga.N` (elements of `𝒜 ⊗ Q` of total degree `> b + N` vanish).
Assumes `X` compact: the data give a top degree `N(𝒜_V)` for each open `V` separately, and
`𝒜_V^q = 0` for `q > N(𝒜_X)` follows from a finite partition of unity (`zero_above` in
`ModelDual`); the consumer `bijective_J_map_comp` assumes compactness anyway. -/
theorem exists_isStrictlyLE_sheafOf [CompactSpace X] (M : CohesiveModule P.𝒜X) :
    ∃ n : ℤ, (P.sheafOf M).IsStrictlyLE n := by
  exact P.exists_isStrictlyLE_sheafOf_aux M

variable (M₁ M₂ : CohesiveModule P.𝒜X)

/-- A closed section of `ℋ⁰(X)` is `F ∘ φ` for a closed `φ ∈ Z⁰` (C3). -/
private theorem exists_Z0_homTop (y : P.HomSec M₁ M₂ 0 (le_top : (⊤ : Opens X) ≤ ⊤))
    (hy : P.homδV M₁ M₂ 0 le_top y = 0) :
    ∃ φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive, P.homTop M₁ M₂ 0 (P.toHom0 φ) = y := by
  obtain ⟨φ0, rfl⟩ := (P.homTop_bijective M₁ M₂ 0).2 y
  rw [P.homδV_homTop M₁ M₂ 0 φ0, ← map_zero (P.homTop M₁ M₂ (0 + 1))] at hy
  have h1 := (P.homTop_bijective M₁ M₂ (0 + 1)).1 hy
  have h2 : δ M₁.toQuasiCohesive M₂.toQuasiCohesive 0 φ0.1 = 0 := congrArg Subtype.val h1
  exact ⟨⟨φ0.1, Submodule.mem_inf.2 ⟨φ0.2, h2⟩⟩, rfl⟩

/-- Under `homComplexSectionsEquiv`, `Γ(Ψ ≫ r_*)` sends `F ∘ φ` to the cochain of `α(φ) ≫ r`. -/
private theorem equiv_Γ_Ψ_comp {I : CochainComplex (Mod P.R) ℤ} (r : P.sheafOf M₂ ⟶ I)
    (φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive) :
    homComplexSectionsEquiv P.isCommSheaf_R (P.sheafOf M₁) I 0 ⊤
        ((((((globalSections P.R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (P.Ψ M₁ M₂ ≫ homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r)).f 0)).hom
          (P.homTop M₁ M₂ 0 (P.toHom0 φ))) =
      Cochain.ofHom ((overC (⊤ : Opens X)).map (P.sheafOfMap φ ≫ r)) := by
  change homComplexSectionsEquiv P.isCommSheaf_R (P.sheafOf M₁) I 0 ⊤
      ((((homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r).f 0).val.app (op ⊤)).hom
        (((P.Ψ M₁ M₂).f 0).val.app (op ⊤) (P.homTop M₁ M₂ 0 (P.toHom0 φ)))) = _
  rw [homComplexSectionsEquiv_homComplexMap₂, P.Ψ_top M₁ M₂ φ, Functor.map_comp,
    Cochain.ofHom_comp]

/-- **C4 step 5, surjectivity on `H⁰`.** If `Γ(Ψ ≫ r_*)` is a quasi-isomorphism, every chain map
`g : α(M₁) ⟶ I` is homotopic to `α(φ) ≫ r` for a closed degree-`0` map `φ : M₁ → M₂`. -/
theorem exists_homotopy_sheafOfMap_comp {I : CochainComplex (Mod P.R) ℤ} (r : P.sheafOf M₂ ⟶ I)
    (h : QuasiIso (((globalSections P.R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (P.Ψ M₁ M₂ ≫ homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r)))
    (g : P.sheafOf M₁ ⟶ I) :
    ∃ φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive, Nonempty (Homotopy (P.sheafOfMap φ ≫ r) g) := by
  obtain ⟨e, he_δ, he_hom, he_comp⟩ := exists_cochain_overTop_equiv P.R
  have hR := P.isCommSheaf_R
  let E := homComplexSectionsEquiv hR (P.sheafOf M₁) I
  let z := (E 0 ⊤).symm (Cochain.ofHom ((overC (⊤ : Opens X)).map g))
  have hz : (((homSheafComplex hR (P.sheafOf M₁) I).d 0 1).val.app (op ⊤)).hom z = 0 := by
    apply (E 1 ⊤).injective
    refine (homComplexSectionsEquiv_d hR (P.sheafOf M₁) I 0 ⊤ z).trans ?_
    rw [(E 0 ⊤).apply_symm_apply, δ_ofHom, map_zero]
  obtain ⟨y, w, hy, hyw⟩ := exists_cocycle_of_quasiIso
    (((globalSections P.R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (P.Ψ M₁ M₂ ≫ homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r)) z hz
  obtain ⟨φ, hφ⟩ := P.exists_Z0_homTop M₁ M₂ y hy
  refine ⟨φ, ?_⟩
  have h0 := P.equiv_Γ_Ψ_comp M₁ M₂ r φ
  rw [hφ] at h0
  have h1 : Cochain.ofHom ((overC (⊤ : Opens X)).map (P.sheafOfMap φ ≫ r)) =
      Cochain.ofHom ((overC (⊤ : Opens X)).map g) +
        CochainComplex.HomComplex.δ (-1) 0 (E (-1) ⊤ w) := by
    refine h0.symm.trans ((congrArg (E 0 ⊤) hyw).trans ?_)
    refine (E 0 ⊤).map_add z _ |>.trans (congrArg₂ (· + ·) ((E 0 ⊤).apply_symm_apply _) ?_)
    exact homComplexSectionsEquiv_d hR (P.sheafOf M₁) I (-1) ⊤ w
  have hδ := he_δ (P.sheafOf M₁) I (-1) (E (-1) ⊤ w)
  refine ⟨(Cochain.equivHomotopy _ _).symm ⟨e _ _ (-1) (E (-1) ⊤ w), ?_⟩⟩
  refine (he_hom _ _ _).symm.trans ((congrArg (e _ _ 0) h1).trans ?_)
  rw [map_add, he_hom, add_comm]
  exact congrArg (· + _) hδ

/-- **C4 step 5, injectivity on `H⁰`.** If `Γ(Ψ ≫ r_*)` is a quasi-isomorphism and
`α(φ) ≫ r` and `α(φ') ≫ r` are homotopic, then `φ` and `φ'` agree in `H0(M₁, M₂)`. -/
theorem mk_eq_of_homotopy_sheafOfMap_comp {I : CochainComplex (Mod P.R) ℤ} (r : P.sheafOf M₂ ⟶ I)
    (h : QuasiIso (((globalSections P.R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (P.Ψ M₁ M₂ ≫ homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r)))
    (φ φ' : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive)
    (H : Homotopy (P.sheafOfMap φ ≫ r) (P.sheafOfMap φ' ≫ r)) :
    (Submodule.Quotient.mk φ : H0 M₁.toQuasiCohesive M₂.toQuasiCohesive) =
      Submodule.Quotient.mk φ' := by
  obtain ⟨e, he_δ, he_hom, he_comp⟩ := exists_cochain_overTop_equiv P.R
  have hR := P.isCommSheaf_R
  let E := homComplexSectionsEquiv hR (P.sheafOf M₁) I
  obtain ⟨c, hc⟩ := Cochain.equivHomotopy _ _ H
  let y := P.homTop M₁ M₂ 0 (P.toHom0 (φ - φ'))
  have hyd : P.homδV M₁ M₂ 0 le_top y = 0 := by
    have h0 : (⟨δ M₁.toQuasiCohesive M₂.toQuasiCohesive 0 (P.toHom0 (φ - φ')).1,
        δ_mem M₁.toQuasiCohesive M₂.toQuasiCohesive (P.toHom0 (φ - φ')).2⟩ :
        Hom M₁.toQuasiCohesive M₂.toQuasiCohesive (0 + 1)) = 0 :=
      Subtype.ext (Submodule.mem_inf.1 (φ - φ').2).2
    rw [P.homδV_homTop M₁ M₂ 0, h0, map_zero]
  have hyw : (((((globalSections P.R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (P.Ψ M₁ M₂ ≫ homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r)).f 0)).hom y =
      ((((globalSections P.R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (homSheafComplex hR (P.sheafOf M₁) I)).d (-1) 0).hom
        ((E (-1) ⊤).symm ((e _ _ (-1)).symm c)) := by
    apply (E 0 ⊤).injective
    apply (e _ _ 0).injective
    have hy : y = P.homTop M₁ M₂ 0 (P.toHom0 φ) - P.homTop M₁ M₂ 0 (P.toHom0 φ') :=
      (congrArg (P.homTop M₁ M₂ 0) (rfl : P.toHom0 (φ - φ') = P.toHom0 φ - P.toHom0 φ')).trans
        (map_sub (P.homTop M₁ M₂ 0) (P.toHom0 φ) (P.toHom0 φ'))
    have hFy := congrArg (((((globalSections P.R).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (P.Ψ M₁ M₂ ≫ homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r)).f 0)).hom hy
    have hL : e _ _ 0 (E 0 ⊤ ((((((globalSections P.R).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (P.Ψ M₁ M₂ ≫ homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r)).f 0)).hom y)) =
        Cochain.ofHom (P.sheafOfMap φ ≫ r) - Cochain.ofHom (P.sheafOfMap φ' ≫ r) := by
      refine (congrArg (fun t => e _ _ 0 (E 0 ⊤ t)) (hFy.trans (map_sub _ _ _))).trans ?_
      refine ((congrArg (e _ _ 0) ((E 0 ⊤).map_sub _ _)).trans ((e _ _ 0).map_sub _ _)).trans ?_
      rw [P.equiv_Γ_Ψ_comp M₁ M₂ r φ, P.equiv_Γ_Ψ_comp M₁ M₂ r φ', he_hom, he_hom]
    have hR' : e _ _ 0 (E 0 ⊤ (((((globalSections P.R).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (homSheafComplex hR (P.sheafOf M₁) I)).d (-1) 0).hom
        ((E (-1) ⊤).symm ((e _ _ (-1)).symm c)))) =
        CochainComplex.HomComplex.δ (-1) 0 c := by
      refine (congrArg (e _ _ 0) (homComplexSectionsEquiv_d hR (P.sheafOf M₁) I (-1) ⊤ _)).trans ?_
      rw [(E (-1) ⊤).apply_symm_apply]
      exact (he_δ _ _ (-1) _).trans (congrArg _ ((e _ _ (-1)).apply_symm_apply c))
    rw [hL, hR', hc, add_sub_cancel_right]
  obtain ⟨v, hv⟩ := exists_eq_d_of_quasiIso
    (((globalSections P.R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (P.Ψ M₁ M₂ ≫ homComplexMap₂ P.isCommSheaf_R (P.sheafOf M₁) r)) y hyd _ hyw
  obtain ⟨ψ, hψ⟩ := (P.homTop_bijective M₁ M₂ (-1)).2 v
  have h1 : P.homTop M₁ M₂ 0 (P.toHom0 (φ - φ')) =
      P.homTop M₁ M₂ (-1 + 1) ⟨δ M₁.toQuasiCohesive M₂.toQuasiCohesive (-1) ψ.1,
        δ_mem M₁.toQuasiCohesive M₂.toQuasiCohesive ψ.2⟩ := by
    refine hv.trans ?_
    rw [← hψ]
    exact (P.homδV_homTop M₁ M₂ (-1) ψ)
  have h2 := (P.homTop_bijective M₁ M₂ 0).1 h1
  refine (Submodule.Quotient.eq _).2 ?_
  exact ⟨ψ.1, ψ.2, (congrArg Subtype.val h2).symm⟩

end PreResolvingData

end Cohesive
