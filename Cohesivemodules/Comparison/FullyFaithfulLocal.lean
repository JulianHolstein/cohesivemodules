import Cohesivemodules.Comparison.FullyFaithful
import Cohesivemodules.Comparison.FullyFaithfulSquare
import Cohesivemodules.Comparison.FullyFaithfulGlobal
import Cohesivemodules.Comparison.PerfectModel
import Cohesivemodules.Sheaf.HomOver
import Cohesivemodules.Sheaf.Derived

set_option linter.style.header false

/-!
# C4 steps 3 and 5: the local quasi-isomorphism and the `H⁰` dictionary

Blueprint item C4 (§4; v1.11 note in step 3). `quasiIso_Ψ_comp`, `bijective_J_map`, `full_J` and
`faithful_J` moved here from `FullyFaithful.lean` (statements unchanged except that
`quasiIso_Ψ_comp` now assumes `X` compact Hausdorff, which its proof needs through C2's map `u`
(C7); its only consumer `bijective_J_map` already assumes it).

**Step 3 (local).** At `x`, LL gives `U ∋ x` and a homotopy equivalence `φ : 𝒜(U) ⊗ W → M₁|U`;
S4.c gives the strictly perfect lift `L` of `W` and C2 the quasi-isomorphism
`u : L → α_U(𝒜(U) ⊗ W)`. With `ι := u ≫ α_U(φ) ≫ (α(M₁)|U ≅ α_U(M₁|U))⁻¹ : L → α(M₁)|U`:
* `Φ := Ψ|U ≫ (𝓗om restriction iso) ≫ ι^* : ℋ(M₁, M₂)|U → 𝓗om(L, α(M₂)|U)` is a
  quasi-isomorphism sectionwise (`quasiIso_Φ`): over `V ⊆ U` it is `Hom(M₁|V, M₂|V) →φ^*
  Hom(𝒜(V) ⊗ W, M₂|V) ≅ Hom_{O(U)}(W, Tot(M₂|V)) ≅ Hom(L|V, α(M₂)|V)` (homotopy equivalence,
  A10.a, S4.c);
* `r_* : 𝓗om(L, α(M₂)|U) → 𝓗om(L, I|U)` is one (S7.b′, `L` strictly perfect);
* `ι^* : 𝓗om(α(M₁)|U, I|U) → 𝓗om(L, I|U)` is one (S7.c′, `ι` a quasi-isomorphism);
so `(Ψ ≫ r_*)|U` is one (2-out-of-3), and `Ψ ≫ r_*` is one (S6).

**Step 5.** `Γ(Ψ ≫ r_*)` is a quasi-isomorphism (soft, bounded below; S3.b(iv)); `H⁰Γ(ℋ) =
H0(M₁, M₂)` (C3), `H⁰Γ(𝓗om(α M₁, I)) = K(α M₁, I)` (S7), `= D(α M₁, I)` (`I` K-injective);
under these, the composite is `f ↦ J(f) ≫ Q(r)` (`Ψ_top`).
-/

noncomputable section

universe w

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

section Site

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{0}} (hR : IsCommSheaf R)

open CochainComplex.HomComplex in
/-- The two functorialities of `𝓗om` commute (pre- and post-composition). -/
private theorem homComplexMap₂_comp_homComplexMap₁ {K K' : CochainComplex (Mod R) ℤ}
    (f : K' ⟶ K) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') :
    homComplexMap₂ hR K g ≫ homComplexMap₁ hR f L' =
      homComplexMap₁ hR f L ≫ homComplexMap₂ hR K' g := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine Limits.Pi.hom_ext _ _ fun T => ?_
  change (Limits.Pi.map _ ≫ Limits.Pi.map _) ≫ _ = (Limits.Pi.map _ ≫ Limits.Pi.map _) ≫ _
  rw [Category.assoc, Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π, ← Category.assoc,
    ← Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π, Category.assoc, Category.assoc]
  congr 1

end Site

namespace PreResolvingData

variable (P : PreResolvingData X)

section OverHty

variable (U : Opens X) {M N : CohesiveModule (P.D.𝒜 U)}

/-- A homotopy equivalence in `Ho(P_{𝒜(U)})` (`ψ ∘ φ ∼ id`, `φ ∘ ψ ∼ id`) gives a
quasi-isomorphism `α_U(φ)` (the argument of `exists_quasiIso_sheafOfOverMap_of_iso`, for a given
`φ`). -/
private theorem quasiIso_sheafOfOverMap_of_homotopyEquiv {A B : CohesiveModule (P.D.𝒜 U)}
    (φ : Z0 A.toQuasiCohesive B.toQuasiCohesive) (ψ : Z0 B.toQuasiCohesive A.toQuasiCohesive)
    (h1 : (Submodule.Quotient.mk (compZ0 _ _ _ ψ φ) : H0 A.toQuasiCohesive A.toQuasiCohesive) =
      Submodule.Quotient.mk (idZ0 A.toQuasiCohesive))
    (h2 : (Submodule.Quotient.mk (compZ0 _ _ _ φ ψ) : H0 B.toQuasiCohesive B.toQuasiCohesive) =
      Submodule.Quotient.mk (idZ0 B.toQuasiCohesive)) :
    QuasiIso (P.sheafOfOverMap U φ) := by
  have key : ∀ {A B : CohesiveModule (P.D.𝒜 U)} (φ : Z0 A.toQuasiCohesive B.toQuasiCohesive)
      (ψ : Z0 B.toQuasiCohesive A.toQuasiCohesive),
      (Submodule.Quotient.mk (compZ0 _ _ _ ψ φ) : H0 A.toQuasiCohesive A.toQuasiCohesive) =
        Submodule.Quotient.mk (idZ0 A.toQuasiCohesive) →
      Nonempty (Homotopy (P.sheafOfOverMap U φ ≫ P.sheafOfOverMap U ψ)
        (𝟙 (P.sheafOfOver U A))) := by
    intro A B φ ψ hφψ
    have hab := Submodule.Quotient.eq _ |>.1 hφψ
    rw [Submodule.mem_comap] at hab
    obtain ⟨h, hh, hδ⟩ := hab
    obtain ⟨H⟩ := P.sheafOfOverMap_homotopic U (compZ0 _ _ _ ψ φ) (idZ0 A.toQuasiCohesive) ⟨h, hh⟩
      (by
        change δ _ _ (-1) h = _ - _
        exact hδ)
    rw [P.sheafOfOverMap_comp, P.sheafOfOverMap_id] at H
    exact ⟨H⟩
  obtain ⟨H1⟩ := key φ ψ h1
  obtain ⟨H2⟩ := key ψ φ h2
  exact (HomotopyEquiv.mk (P.sheafOfOverMap U φ) (P.sheafOfOverMap U ψ) H1 H2).quasiIso_hom

end OverHty

/-- `α(M)` is bounded below: `α(M)^n = 0` below the lowest degree of the generators (forms have
degree `≥ 0`). -/
theorem exists_isStrictlyGE_sheafOf (M : CohesiveModule P.𝒜X) :
    ∃ n : ℤ, (P.sheafOf M).IsStrictlyGE n := by
  obtain ⟨a₁, b₁, h₁⟩ := M.bounded
  refine ⟨a₁, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  change Limits.IsZero (P.sheafOfSh M n)
  refine isZero_of_sections_subsingleton fun V => ⟨fun x y => ?_⟩
  have hz : ∀ z : P.sheafOfSec M n (le_top : V.unop ≤ ⊤), z = 0 := fun z =>
    Subtype.ext (eq_zero_of_totDeg_lt a₁ (fun p hp => bcGen_subsingleton (P.D.res le_top)
      (Q := M.Q) p (h₁ p (Or.inl hp))) hn z.2)
  exact (hz x).trans (hz y).symm

/-- An isomorphism in `Ho(P_{𝒜(U)})` comes from a homotopy equivalence: closed maps `φ`, `ψ`
with `ψ ∘ φ ∼ id` and `φ ∘ ψ ∼ id`. -/
theorem exists_homotopyEquiv_of_iso (U : Opens X) {M N : CohesiveModule (P.D.𝒜 U)}
    (e : HoP.mk M ≅ HoP.mk N) :
    ∃ (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (ψ : Z0 N.toQuasiCohesive M.toQuasiCohesive),
      (Submodule.Quotient.mk (compZ0 _ _ _ ψ φ) : H0 M.toQuasiCohesive M.toQuasiCohesive) =
        Submodule.Quotient.mk (idZ0 M.toQuasiCohesive) ∧
      (Submodule.Quotient.mk (compZ0 _ _ _ φ ψ) : H0 N.toQuasiCohesive N.toQuasiCohesive) =
        Submodule.Quotient.mk (idZ0 N.toQuasiCohesive) := by
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _ e.hom
  obtain ⟨ψ, hψ⟩ := Submodule.Quotient.mk_surjective _ e.inv
  refine ⟨φ, ψ, ?_, ?_⟩
  · have := e.hom_inv_id
    rw [HoP.comp_def, ← hφ, ← hψ, compH0_mk] at this
    exact this
  · have h : compH0 N.toQuasiCohesive M.toQuasiCohesive N.toQuasiCohesive e.hom e.inv =
        Submodule.Quotient.mk (idZ0 N.toQuasiCohesive) := e.inv_hom_id
    have h2 : compH0 N.toQuasiCohesive M.toQuasiCohesive N.toQuasiCohesive
        (Submodule.Quotient.mk φ) (Submodule.Quotient.mk ψ) =
        compH0 N.toQuasiCohesive M.toQuasiCohesive N.toQuasiCohesive e.hom e.inv :=
      congrArg₂ (fun a b => compH0 N.toQuasiCohesive M.toQuasiCohesive N.toQuasiCohesive a b)
        hφ hψ
    exact h2.trans h

end PreResolvingData

namespace ResolvingData

variable (D : ResolvingData X) (M₁ M₂ : CohesiveModule D.𝒜X)

/-- **C4 step 3, sectionwise part.** With `L`, `u` as in C2 (`Γ u = ε ⋙ (w ↦ 1 ⊗ 1 ⊗ w)`) and a
homotopy equivalence `φ : 𝒜(U) ⊗ W → M₁|U` (inverse `ψ`), the map
`Φ = Ψ|U ≫ (𝓗om restriction iso) ≫ ι^* : ℋ(M₁, M₂)|U → 𝓗om(L, α(M₂)|U)`,
`ι = u ≫ α_U(φ) ≫ (restrSheafOfIso)⁻¹`, is a quasi-isomorphism. Proof: sectionwise
(`quasiIso_of_sectionwise`); over `V ⊆ U` it is, up to the isomorphisms
`ℋ(M₁, M₂)(V) ≅ Hom(M₁|V, M₂|V)` (base change), `Hom(𝒜(V) ⊗ W, M₂|V) ≅ Hom_{O(U)}(W, Tot(M₂|V))`
(A10.a) and `Hom(L|V, α(M₂)|V) ≅ Hom_{O(U)}(W, α(M₂)(V))` (S4.c on the over-site of `V`),
precomposition with `φ|V`, a homotopy equivalence. -/
theorem quasiIso_Φ [CompactSpace X] [T2Space X] (U : Opens X)
    (W : CochainComplex (ModuleCat.{0} (D.O.obj.obj (op U))) ℤ)
    (hW : IsBoundedFGProj (D.O.obj.obj (op U)) W)
    (L : CochainComplex (Mod (D.R.over U)) ℤ) (hL : IsStrictlyPerfect L)
    (ε : ((gammaT (D.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ≅ W)
    (u : L ⟶ D.sheafOfOver U (D.fcMod U W hW))
    (hu : ((gammaT (D.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u = ε.hom ≫ D.unitMap U W hW)
    (φ : Z0 (D.fcMod U W hW).toQuasiCohesive (M₁.baseChange (D.r U)).toQuasiCohesive)
    (ψ : Z0 (M₁.baseChange (D.r U)).toQuasiCohesive (D.fcMod U W hW).toQuasiCohesive)
    (hψφ : (Submodule.Quotient.mk (compZ0 _ _ _ ψ φ) : H0 _ _) =
      Submodule.Quotient.mk (idZ0 (D.fcMod U W hW).toQuasiCohesive))
    (hφψ : (Submodule.Quotient.mk (compZ0 _ _ _ φ ψ) : H0 _ _) =
      Submodule.Quotient.mk (idZ0 (M₁.baseChange (D.r U)).toQuasiCohesive)) :
    QuasiIso ((overC U).map (D.Ψ M₁ M₂) ≫
      (homComplexOverIso D.isCommSheaf_R (D.sheafOf M₁) (D.sheafOf M₂) U).hom ≫
      homComplexMap₁ (D.isCommSheaf_R.over U)
        (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M₁).inv)
        ((overC U).obj (D.sheafOf M₂))) := by
  refine quasiIso_of_sectionwise _ fun V => ?_
  obtain ⟨Y⟩ := V
  refine (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat ↑((D.R.over U).obj.obj (op Y))) AddCommGrpCat)).1 ?_
  have hsq := D.jK_Φ_evL U W hW L ε u M₁ M₂ φ Y hu
  haveI := D.isIso_jK U M₁ M₂ Y
  haveI := D.isIso_evL U W L ε M₂ Y hL
  haveI := isIso_alongEv (D.D.res (leOfHom Y.hom)) W (D.d_ρ U) (D.c_eq_zero U)
    (D.c_eq_zero Y.left) (D.NY U M₂ Y)
  haveI := quasiIso_alongPre (D.D.res (leOfHom Y.hom)) (D.NY U M₂ Y) φ ψ hψφ hφψ
  haveI : QuasiIso (D.jK U M₁ M₂ Y) := quasiIso_of_isIso _
  haveI : QuasiIso (D.evL U W L ε M₂ Y) := quasiIso_of_isIso _
  haveI : QuasiIso (homSectionsIso (D.isCommSheaf_R.over U) L
      ((overC U).obj (D.sheafOf M₂)) Y).hom := quasiIso_of_isIso _
  have hev : QuasiIso (alongEv (D.D.res (leOfHom Y.hom)) W (D.d_ρ U) (D.c_eq_zero U)
      (D.c_eq_zero Y.left) (D.NY U M₂ Y)) := quasiIso_of_isIso _
  have hpre := quasiIso_alongPre (D.D.res (leOfHom Y.hom)) (D.NY U M₂ Y) φ ψ hψφ hφψ
  have h1 : QuasiIso (alongPre (D.D.res (leOfHom Y.hom)) (D.NY U M₂ Y) φ ≫
      alongEv (D.D.res (leOfHom Y.hom)) W (D.d_ρ U) (D.c_eq_zero U) (D.c_eq_zero Y.left)
        (D.NY U M₂ Y)) := quasiIso_comp (hφ := hpre) (hφ' := hev) _ _
  rw [← hsq, quasiIso_iff_comp_left, ← Category.assoc, quasiIso_iff_comp_right,
    quasiIso_iff_comp_right] at h1
  exact h1

/-- **C4 step 3, local.** If `M₁|U ≅ 𝒜(U) ⊗ W` in `Ho(P_{𝒜(U)})` (LL), then for a bounded
below injective resolution `r : α(M₂) → I`, `(Ψ ≫ r_*)|U` is a quasi-isomorphism (see the module
doc: `quasiIso_Φ`, S7.b′, S7.c′, 2-out-of-3). -/
theorem quasiIso_restr_Ψ_comp [CompactSpace X] [T2Space X] {I : CochainComplex (Mod D.R) ℤ}
    (r : D.sheafOf M₂ ⟶ I) [QuasiIso r] (hI : ∀ n, Injective (I.X n)) (a : ℤ) [I.IsStrictlyGE a]
    (U : Opens X) (W : CochainComplex (ModuleCat.{0} (D.O.obj.obj (op U))) ℤ)
    (hW : IsBoundedFGProj (D.O.obj.obj (op U)) W)
    (e : HoP.mk (M₁.baseChange (D.r U)) ≅ HoP.mk (D.fcMod U W hW)) :
    QuasiIso ((overC U).map (D.Ψ M₁ M₂ ≫ homComplexMap₂ D.isCommSheaf_R (D.sheafOf M₁) r)) := by
  obtain ⟨φ, ψ, hψφ, hφψ⟩ := D.exists_homotopyEquiv_of_iso U e.symm
  obtain ⟨b, c, hbc⟩ := hW.bounded
  obtain ⟨L, hL, ⟨ε⟩⟩ := exists_lift_complex (R := D.R.over U) (Over.mkIdTerminal (X := U)) W
    hW.finite hW.projective b c hbc
  obtain ⟨u, hu⟩ := exists_lift_hom (Over.mkIdTerminal (X := U)) hL.2
    (ε.hom ≫ D.unitMap U W hW)
  have hu' : QuasiIso u := D.quasiIso_of_gamma_eq U W hW L hL ε u hu
  have hφ : QuasiIso (D.sheafOfOverMap U φ) :=
    D.quasiIso_sheafOfOverMap_of_homotopyEquiv U φ ψ hψφ hφψ
  have hι : QuasiIso (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M₁).inv) := inferInstance
  have hΦ := D.quasiIso_Φ M₁ M₂ U W hW L hL ε u hu φ ψ hψφ hφψ
  have hr : QuasiIso ((overC U).map r) :=
    inferInstanceAs (QuasiIso (((restr D.R U).mapHomologicalComplex (ComplexShape.up ℤ)).map r))
  have hb := quasiIso_homComplexMap₂_site (D.isCommSheaf_R.over U) hL ((overC U).map r)
  have hIge : ((overC U).obj I).IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ a).2 fun i hi =>
      (restr D.R U).map_isZero (CochainComplex.isZero_of_isStrictlyGE I a i hi)
  have hIinj : ∀ (V : Over U) (i : ℤ),
      Injective ((SheafOfModules.overFunctor.{0} (D.R.over U) V).obj (((overC U).obj I).X i)) :=
    fun V i => by
      have := hI i
      exact injective_overFunctor_restr U (I.X i) V
  have hc := quasiIso_homComplexMap₁_site (D.isCommSheaf_R.over U)
    (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M₁).inv) a hIinj
  have hcomp : QuasiIso (((overC U).map (D.Ψ M₁ M₂) ≫
      (homComplexOverIso D.isCommSheaf_R (D.sheafOf M₁) (D.sheafOf M₂) U).hom ≫
      homComplexMap₁ (D.isCommSheaf_R.over U)
        (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M₁).inv) ((overC U).obj (D.sheafOf M₂))) ≫
      homComplexMap₂ (D.isCommSheaf_R.over U) L ((overC U).map r)) := inferInstance
  have heq : ((overC U).map (D.Ψ M₁ M₂) ≫
      (homComplexOverIso D.isCommSheaf_R (D.sheafOf M₁) (D.sheafOf M₂) U).hom ≫
      homComplexMap₁ (D.isCommSheaf_R.over U)
        (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M₁).inv) ((overC U).obj (D.sheafOf M₂))) ≫
      homComplexMap₂ (D.isCommSheaf_R.over U) L ((overC U).map r) =
      (overC U).map (D.Ψ M₁ M₂ ≫ homComplexMap₂ D.isCommSheaf_R (D.sheafOf M₁) r) ≫
      ((homComplexOverIso D.isCommSheaf_R (D.sheafOf M₁) I U).hom ≫
      homComplexMap₁ (D.isCommSheaf_R.over U)
        (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M₁).inv) ((overC U).obj I)) := by
    rw [Functor.map_comp]
    simp only [Category.assoc]
    congr 1
    rw [← Category.assoc ((overC U).map (homComplexMap₂ D.isCommSheaf_R (D.sheafOf M₁) r)),
      homComplexOverIso_naturality₂ D.isCommSheaf_R (D.sheafOf M₁) r U]
    simp only [Category.assoc]
    congr 1
    exact (homComplexMap₂_comp_homComplexMap₁ (D.isCommSheaf_R.over U)
      (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M₁).inv) ((overC U).map r)).symm
  rw [heq] at hcomp
  have hiso : QuasiIso ((homComplexOverIso D.isCommSheaf_R (D.sheafOf M₁) I U).hom ≫
      homComplexMap₁ (D.isCommSheaf_R.over U)
        (u ≫ D.sheafOfOverMap U φ ≫ (D.restrSheafOfIso U M₁).inv) ((overC U).obj I)) :=
    inferInstance
  exact (quasiIso_iff_comp_right _ _).1 hcomp

/-- **C4 step 3.** For an injective resolution `r : α(M₂) → I` (bounded below), the composite
`ℋ(M₁, M₂) → 𝓗om(α(M₁), α(M₂)) → 𝓗om(α(M₁), I)` is a quasi-isomorphism (locally:
`quasiIso_restr_Ψ_comp` on the opens of LL; then S6). Deviation (v1.11): `X` compact Hausdorff
(C2's map `u` goes through C7). -/
theorem quasiIso_Ψ_comp [CompactSpace X] [T2Space X] {I : CochainComplex (Mod D.R) ℤ}
    (r : D.sheafOf M₂ ⟶ I) [QuasiIso r] (hI : ∀ n, Injective (I.X n)) (a : ℤ) [I.IsStrictlyGE a] :
    QuasiIso (D.Ψ M₁ M₂ ≫ homComplexMap₂ D.isCommSheaf_R (D.sheafOf M₁) r) := by
  refine quasiIso_of_locally _ fun x => ?_
  obtain ⟨U, hx, W, hW, ⟨e⟩⟩ := D.LL M₁ x
  exact ⟨U, hx, D.quasiIso_restr_Ψ_comp M₁ M₂ r hI a U W hW e⟩

/-- Global sections of `Ψ ≫ r_*` form a quasi-isomorphism (soft, bounded below; S3.b(iv)). -/
private theorem quasiIso_Γ_Ψ_comp [CompactSpace X] [T2Space X] {I : CochainComplex (Mod D.R) ℤ}
    (r : D.sheafOf M₂ ⟶ I) [QuasiIso r] (hI : ∀ n, Injective (I.X n)) (a : ℤ) [I.IsStrictlyGE a] :
    QuasiIso (((globalSections D.R).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (D.Ψ M₁ M₂ ≫ homComplexMap₂ D.isCommSheaf_R (D.sheafOf M₁) r)) := by
  have := D.quasiIso_Ψ_comp M₁ M₂ r hI a
  obtain ⟨b, hb⟩ := D.exists_isStrictlyLE_sheafOf M₁
  obtain ⟨c, hc⟩ := D.exists_isStrictlyGE_ℋ M₁ M₂
  haveI := hb
  haveI := hc
  haveI : (homSheafComplex D.isCommSheaf_R (D.sheafOf M₁) I).IsStrictlyGE (a - b) :=
    exists_isStrictlyGE_homSheafComplex D.isCommSheaf_R (D.sheafOf M₁) I a b
  haveI : (D.ℋ M₁ M₂).IsStrictlyGE (min c (a - b)) :=
    (D.ℋ M₁ M₂).isStrictlyGE_of_ge _ c (min_le_left _ _)
  haveI : (homSheafComplex D.isCommSheaf_R (D.sheafOf M₁) I).IsStrictlyGE (min c (a - b)) :=
    (homSheafComplex D.isCommSheaf_R (D.sheafOf M₁) I).isStrictlyGE_of_ge _ (a - b)
      (min_le_right _ _)
  exact quasiIso_globalSections_of_isSoft (min c (a - b))
    (fun i => D.isSoft_homSh M₁ M₂ i) (fun i => D.isSoft_homSheafComplex_sheafOf_X M₁ I i) _

/-- **C4 step 5.** For a bounded below injective resolution `r : α(M₂) → I`,
`f ↦ J(f) ≫ Q(r)` is bijective from `Hom_{Ho(P_A)}(M₁, M₂)` to `D(α(M₁), I)`: `Γ(Ψ ≫ r_*)` is a
quasi-isomorphism (`quasiIso_Ψ_comp`, softness `isSoft_homSh`, `isSoft_homSheafComplex_sheafOf_X`,
boundedness, `quasiIso_globalSections_of_isSoft`), `H⁰Γ(ℋ) = H0(M₁, M₂)` (`homTop_bijective`,
`homδV_homTop`), `H⁰Γ(𝓗om(α(M₁), I))` = homotopy classes of maps `α(M₁) → I`
(`exists_cochain_overTop_equiv`), which are `D(α(M₁), I)` for `I` K-injective; the composite is
`f ↦ J(f) ≫ Q(r)` by `Ψ_top`. -/
theorem bijective_J_map_comp [CompactSpace X] [T2Space X] [HasDerivedCategory.{w} (Mod D.R)]
    (M N : HoP D.𝒜X) {I : CochainComplex (Mod D.R) ℤ} (r : D.sheafOf N.as ⟶ I) [QuasiIso r]
    (hI : ∀ n, Injective (I.X n)) (a : ℤ) [I.IsStrictlyGE a] :
    Function.Bijective (fun f : M ⟶ N ↦ D.J.map f ≫ DerivedCategory.Q.map r) := by
  have hΓ := D.quasiIso_Γ_Ψ_comp M.as N.as r hI a
  haveI := CochainComplex.isKInjective_of_injective I a
  haveI : ∀ n, Injective (I.X n) := hI
  let T := HomotopyCategory.quotient (Mod D.R) (ComplexShape.up ℤ)
  have hQ := CochainComplex.IsKInjective.Qh_map_bijective (C := Mod D.R) (T.obj (D.sheafOf M.as)) I
  have hfac : (fun f : M ⟶ N ↦ D.J.map f ≫ DerivedCategory.Q.map r) =
      DerivedCategory.Qh.map ∘ (fun f : M ⟶ N ↦ D.JK.map f ≫ T.map r) := by
    funext f
    refine Eq.trans ?_ (Functor.map_comp DerivedCategory.Qh (D.JK.map f) (T.map r)).symm
    rfl
  rw [hfac]
  refine hQ.comp ⟨fun f f' h => ?_, fun h => ?_⟩
  · induction f using Submodule.Quotient.induction_on with
    | H φ =>
    induction f' using Submodule.Quotient.induction_on with
    | H φ' =>
    have h1 : T.map (D.sheafOfMap φ ≫ r) = T.map (D.sheafOfMap φ' ≫ r) := h
    exact D.mk_eq_of_homotopy_sheafOfMap_comp M.as N.as r hΓ φ φ'
      (HomotopyCategory.homotopyOfEq _ _ h1)
  · obtain ⟨g, rfl⟩ := T.map_surjective h
    obtain ⟨φ, ⟨H⟩⟩ := D.exists_homotopy_sheafOfMap_comp M.as N.as r hΓ g
    exact ⟨(Submodule.Quotient.mk φ : M ⟶ N), HomotopyCategory.eq_of_homotopy _ _ H⟩

/-- **C4.** `J` is bijective on morphisms. [A, Prop 7.2.19]. -/
theorem bijective_J_map [CompactSpace X] [T2Space X] [HasDerivedCategory.{w} (Mod D.R)]
    (M N : HoP D.𝒜X) : Function.Bijective (fun f : M ⟶ N ↦ D.J.map f) := by
  obtain ⟨n, hn⟩ := D.exists_isStrictlyGE_sheafOf N.as
  obtain ⟨I, r, hIn, hI, hr⟩ := exists_injective_resolution (D.sheafOf N.as) n
  have hb := D.bijective_J_map_comp M N r hI n
  have hiso : IsIso (DerivedCategory.Q.map r) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hr
  refine ⟨fun f g h => hb.1 ?_, fun g => ?_⟩
  · change D.J.map f = D.J.map g at h
    change D.J.map f ≫ DerivedCategory.Q.map r = D.J.map g ≫ DerivedCategory.Q.map r
    rw [h]
  · obtain ⟨f, hf⟩ := hb.2 (g ≫ DerivedCategory.Q.map r)
    refine ⟨f, ?_⟩
    change D.J.map f ≫ DerivedCategory.Q.map r = g ≫ DerivedCategory.Q.map r at hf
    exact (cancel_mono (f := DerivedCategory.Q.map r)).1 hf

/-- **C4.** `J` is full. -/
theorem full_J [CompactSpace X] [T2Space X] [HasDerivedCategory.{w} (Mod D.R)] : D.J.Full :=
  ⟨fun {M N} => (D.bijective_J_map M N).2⟩

/-- **C4.** `J` is faithful. -/
theorem faithful_J [CompactSpace X] [T2Space X] [HasDerivedCategory.{w} (Mod D.R)] :
    D.J.Faithful :=
  ⟨fun {M N} => (D.bijective_J_map M N).1⟩

end ResolvingData

end Cohesive
