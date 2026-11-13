import Cohesivemodules.Comparison.PerfectLoc
import Cohesivemodules.Comparison.HomSheaf
import Cohesivemodules.Comparison.FullyFaithfulAux
import Cohesivemodules.Algebra.HomAlongT
import Cohesivemodules.Sheaf.RestrEval
import Cohesivemodules.Sheaf.HomOverSections

set_option linter.style.header false

/-!
# C4 step 3: the sections of `Φ` over a fixed `Y`

Blueprint item C4 (§4), step 3 (`quasiIso_Φ` in `Comparison/FullyFaithfulLocal.lean`). Fix
`Y : Over U` and write `V = Y.left ≤ U`, `N_Y = M₂|V` (`NY`), `ρ_Y = res ∘ ρ_U : O(U) → 𝒜⁰(V)`
(`ρY`). The sections over `Y` of the source and target of `Φ` are compared with complexes of
abelian groups built in `Algebra/HomAlongT.lean`:
* `jK`: `Hom^•_{along res}(M₁|U, N_Y) ⟶ ℋ(M₁, M₂)(V)`, `χ' ↦ χ' ∘ F` (`F = bcF` along
  `r_U`), an isomorphism (`isIso_jK`; inverse `χ ↦ extAlong χ ∘ totRes`);
* `evL`: `Cochain(L|Y, α(M₂)|Y) ⟶ Hom^•_{O(U)}(W, N_Y)` (families for `ρ_Y`),
  `c ↦ (w ↦ c_{p,p+n}((ε⁻¹ w)|Y))`, an isomorphism for strictly perfect `L` (`isIso_evL`, S4.c
  with restriction, `Sheaf/RestrEval.lean`);
* `ι_app_res`: the value of `ι = u ≫ α_U(φ) ≫ (restrSheafOfIso)⁻¹` on `(ε⁻¹ w)|Y` is
  `(φ(1 ⊗ 1 ⊗ w))|V` (from `hu`; `cmpTotInv_bcF` collapses the comparison of base changes).

Part 1 of 2 of the original `Comparison/FullyFaithfulPhi.lean`, split for size; continued in
`Comparison/FullyFaithfulPhi.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex

section Generic

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

/-- A9's comparison map `F = bcF : Tot(M) → Tot(f^*M)` as a `k`-linear map. -/
def bcFLin (f : DgaHom 𝒜 ℬ) (M : QuasiCohesive 𝒜) : M.T →ₗ[k] (M.baseChange f).T where
  toFun := bcF f M.Q
  map_add' := map_add _
  map_smul' := bcF_smul_k f M.Q

/-- `bcFLin` on an element (rfl). -/
theorem bcFLin_apply (f : DgaHom 𝒜 ℬ) (M : QuasiCohesive 𝒜) (x : M.T) :
    bcFLin f M x = bcF f M.Q x := rfl

variable {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]

/-- A9.a: the inverse comparison `g^*(f^*M) → (g ∘ f)^*M` on `F_g(y)` is the restriction
`bcTotRes`: both sides are semilinear along `g` and agree on `F_g(F_f(x)) ↦ F_{gf}(x)`. -/
theorem cmpTotInv_bcF (f : DgaHom 𝒜 ℬ) (g : DgaHom ℬ 𝒞) (f₂ : DgaHom 𝒜 𝒞)
    (hf : g.comp f = f₂) (M : QuasiCohesive 𝒜) (y : (M.baseChange f).T) :
    cmpTotInv f g f₂ hf M (bcF g (M.baseChange f).Q y) =
      bcTotRes g f f₂ (fun a => by rw [← hf]; rfl) M.Q y := by
  have key := bc_ext_semilinear (g := g) (f := f) (Q := M.Q) (n := 0)
    ((cmpTotInv f g f₂ hf M).comp (bcF g (BCGen f M.Q)))
    (bcTotRes g f f₂ (fun a => by rw [← hf]; rfl) M.Q)
    (fun {p b} _ y => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, zero_mul, Int.negOnePow_zero,
        one_smul]
      rw [bcF_smul, cmpTotInv_smul])
    (fun {p b} _ y => by
      simp only [zero_mul, Int.negOnePow_zero, one_smul]
      exact bcTotRes_smul g f f₂ _ M.Q b y)
    (fun x => by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply]
      rw [bcTotRes_bcF, ← bcCompTot_bcF]
      subst hf
      rw [← cmpTot_rfl, cmpTotInv_cmpTot])
  exact congrArg (fun ψ => ψ y) key

end Generic

/-- Sections over `V` of a complex of sheaves of modules, as a complex of abelian groups. -/
abbrev secAb {C : Type} [SmallCategory C] {J : GrothendieckTopology C} (S : Sheaf J RingCat.{0})
    (V : Cᵒᵖ) : CochainComplex (Mod S) ℤ ⥤ CochainComplex AddCommGrpCat.{0} ℤ :=
  (SheafOfModules.evaluation.{0} S V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    (forget₂ (ModuleCat ↑(S.obj.obj V)) AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℤ)

section RestrEvalLemmas

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}} {T : C}

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- `restrEval` is additive in the morphism. -/
lemma restrEval_hom_add (hT : Limits.IsTerminal T) {M N : Mod R} (Y : C)
    (g g' : M.over Y ⟶ N.over Y) (m : M.val.obj (op T)) :
    restrEval hT Y (g + g') m = restrEval hT Y g m + restrEval hT Y g' m := rfl

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- `restrEval` commutes with the action of a unit `±1` on morphisms. -/
lemma restrEval_hom_units (hT : Limits.IsTerminal T) {M N : Mod R} (Y : C) (z : ℤˣ)
    (g : M.over Y ⟶ N.over Y) (m : M.val.obj (op T)) :
    restrEval hT Y (z • g) m = z • restrEval hT Y g m := by
  have h : (SheafOfModules.evaluation.{0} (R.over Y) (op (Over.mk (𝟙 Y)))).map
      ((z : ℤ) • g) = (z : ℤ) • (SheafOfModules.evaluation.{0} (R.over Y)
        (op (Over.mk (𝟙 Y)))).map g := Functor.map_zsmul _
  rw [Units.smul_def, Units.smul_def]
  exact congrArg (fun q : M.val.obj (op Y) ⟶ N.val.obj (op Y) =>
    q.hom ((M.val.map (hT.from Y).op).hom m)) h

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- `restrEval` of a restricted morphism followed by `g` is `restrEval g` of the image. -/
lemma restrEval_over_comp (hT : Limits.IsTerminal T) {M' M N : Mod R} (Y : C) (a : M' ⟶ M)
    (g : M.over Y ⟶ N.over Y) (m : M'.val.obj (op T)) :
    restrEval hT Y ((SheafOfModules.overFunctor.{0} R Y).map a ≫ g) m =
      restrEval hT Y g ((a.val.app (op T)).hom m) := by
  unfold restrEval
  have := PresheafOfModules.naturality_apply a.val (hT.from Y).op m
  refine congrArg (fun x => (g.val.app (op (Over.mk (𝟙 Y)))).hom x) ?_
  exact this

end RestrEvalLemmas

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X)

/-- `ρ_Y = res_{V ≤ U} ∘ ρ_U : O(U) → 𝒜⁰(V)` for `Y : Over U`, `V = Y.left`. -/
def ρY (Y : Over U) : P.O.obj.obj (op U) →+* (P.D.𝒜 Y.left) 0 :=
  (P.D.res (leOfHom Y.hom)).f0.comp (P.ρ U)

/-- `M₂|V` (base change along `r_V`) for `Y : Over U`, `V = Y.left`, as a quasi-cohesive
module over `𝒜(V)`. Its total module is `α(M₂)(V)` in all degrees. -/
abbrev NY (M₂ : CohesiveModule P.𝒜X) (Y : Over U) : QuasiCohesive (P.D.𝒜 Y.left) :=
  (M₂.baseChange (P.r Y.left)).toQuasiCohesive

/-! ### The `ℋ` side -/

section HSide

variable (M₁ M₂ : CohesiveModule P.𝒜X) (Y : Over U)

/-- `χ' ∘ F` lies in `ℋ^n(V)` for `χ'` along `res_{V ≤ U}` out of `M₁|U` (`res ∘ r_U = r_V`). -/
theorem jK_mem {n : ℤ}
    (χ' : HomAlongT (P.D.res (leOfHom Y.hom)) (M₁.baseChange (P.r U)).toQuasiCohesive
      (P.NY U M₂ Y) n) :
    χ'.1 ∘ₗ bcFLin (P.r U) M₁.toQuasiCohesive ∈
      P.homAlong M₁ M₂ n (le_top : Y.left ≤ ⊤) := by
  refine ⟨fun {m x} hx => χ'.2.1 (bcF_mem_totDeg (P.r U) M₁.Q hx), fun {p a} ha x => ?_⟩
  change χ'.1 (bcF (P.r U) M₁.Q (a • x)) = _
  rw [bcF_smul]
  refine (χ'.2.2 ((P.r U).map_mem ha) (bcF (P.r U) M₁.Q x)).trans ?_
  rw [P.D.res_comp]
  rfl

/-- `jK` in degree `n`: `χ' ↦ χ' ∘ F`. -/
def jKf (n : ℤ) :
    (alongComplex (P.D.res (leOfHom Y.hom)) (M₁.baseChange (P.r U)).toQuasiCohesive
      (P.NY U M₂ Y)).X n ⟶ ((secAb (P.R.over U) (op Y)).obj ((overC U).obj (P.ℋ M₁ M₂))).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun χ' => (⟨χ'.1 ∘ₗ bcFLin (P.r U) M₁.toQuasiCohesive, P.jK_mem U M₁ M₂ Y χ'⟩ :
        P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤))
      map_zero' := Subtype.ext (LinearMap.zero_comp _)
      map_add' := fun _ _ => Subtype.ext (LinearMap.add_comp _ _ _) }

/-- `jKf` on an element (rfl). -/
theorem jKf_apply (n : ℤ)
    (χ' : HomAlongT (P.D.res (leOfHom Y.hom)) (M₁.baseChange (P.r U)).toQuasiCohesive
      (P.NY U M₂ Y) n) :
    ((P.jKf U M₁ M₂ Y n).hom χ' : P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤)).1 =
      χ'.1 ∘ₗ bcFLin (P.r U) M₁.toQuasiCohesive := rfl

/-- `jKf` commutes with the differentials (`𝕏` of `M₁|U` on `F(x)` is `F(𝕏 x)`,
`bc_extend_bcF`; the differential of `ℋ` is `homδV`). -/
theorem jKf_comm (n : ℤ) :
    P.jKf U M₁ M₂ Y n ≫ ((secAb (P.R.over U) (op Y)).obj ((overC U).obj (P.ℋ M₁ M₂))).d n (n + 1) =
      (alongComplex (P.D.res (leOfHom Y.hom)) (M₁.baseChange (P.r U)).toQuasiCohesive
        (P.NY U M₂ Y)).d n (n + 1) ≫ P.jKf U M₁ M₂ Y (n + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro χ'
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have hd : (P.ℋ M₁ M₂).d n (n + 1) = P.homD M₁ M₂ n := by
    simp only [PreResolvingData.ℋ, CochainComplex.of_d]
  simp only [alongComplex, CochainComplex.of_d, secAb, overC, Functor.comp_obj,
    Functor.mapHomologicalComplex_obj_d, hd]
  change ((P.homδV M₁ M₂ n (le_top : Y.left ≤ ⊤)) (P.jKf U M₁ M₂ Y n χ')).1 x =
    ((P.jKf U M₁ M₂ Y (n + 1)).hom ((alongD _ _ _ n) χ')).1 x
  change (M₂.baseChange (P.D.res (le_top : Y.left ≤ ⊤))).X (χ'.1 (bcF (P.r U) M₁.Q x)) -
      n.negOnePow • χ'.1 (bcF (P.r U) M₁.Q (M₁.X x)) =
    (P.NY U M₂ Y).X (χ'.1 (bcF (P.r U) M₁.Q x)) -
      n.negOnePow • χ'.1 ((M₁.baseChange (P.r U)).X (bcF (P.r U) M₁.Q x))
  rw [← bc_extend_bcF]
  rfl

/-- **C4 step 3.** The chain map `Hom^•_{along res}(M₁|U, M₂|V) ⟶ ℋ(M₁, M₂)(V)`,
`χ' ↦ χ' ∘ F`, on sections over `Y`. -/
def jK : alongComplex (P.D.res (leOfHom Y.hom)) (M₁.baseChange (P.r U)).toQuasiCohesive
      (P.NY U M₂ Y) ⟶ (secAb (P.R.over U) (op Y)).obj ((overC U).obj (P.ℋ M₁ M₂)) where
  f n := P.jKf U M₁ M₂ Y n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact P.jKf_comm U M₁ M₂ Y i

/-- `jKf` is injective (uniqueness of semilinear extensions along a base change). -/
private theorem jKf_injective (n : ℤ) : Function.Injective (P.jKf U M₁ M₂ Y n).hom := by
  intro χ₁ χ₂ h
  have h' : ∀ x : M₁.T, χ₁.1 (bcF (P.r U) M₁.Q x) = χ₂.1 (bcF (P.r U) M₁.Q x) := fun x =>
    LinearMap.congr_fun (congrArg Subtype.val h) x
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  have key := bc_ext_semilinear (g := P.D.res (leOfHom Y.hom)) (f := P.r U) (Q := M₁.Q) n
    χ₁.1.toAddMonoidHom χ₂.1.toAddMonoidHom
    (fun {p b} hb y => χ₁.2.2 hb y) (fun {p b} hb y => χ₂.2.2 hb y) h'
  exact congrArg (fun ψ => ψ y) key

/-- The preimage of `χ ∈ ℋ^n(V)`: `extAlong χ ∘ totRes_{V ≤ U}`, as an element of
`Hom^n_{along res}(M₁|U, M₂|V)`. -/
private def jKpre (n : ℤ) (χ : P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤)) :
    HomAlongT (P.D.res (leOfHom Y.hom)) (M₁.baseChange (P.r U)).toQuasiCohesive
      (P.NY U M₂ Y) n :=
  ⟨(extAlong (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n) ⟨χ.1, χ.2⟩) ∘ₗ
      (P.totResL M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom)),
    fun {m x} hx => by
      have h1 : P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) x ∈
          totDeg (P.D.𝒜 Y.left) (M₁.baseChange (P.D.res (le_top : Y.left ≤ ⊤))).Q m :=
        P.totRes_mem M₁ _ _ hx
      exact (extAlong_mem (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n) ⟨χ.1, χ.2⟩).1 h1,
    fun {p a} ha x => by
      have hs : P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (a • x) =
          P.D.res (leOfHom Y.hom) a • P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) x :=
        bcTotRes_smul (P.D.res (leOfHom Y.hom)) (P.D.res (le_top : U ≤ ⊤))
          (P.D.res (le_top : Y.left ≤ ⊤)) _ M₁.Q a x
      change extAlong (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n) ⟨χ.1, χ.2⟩
        (P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (a • x)) = _
      rw [hs]
      exact (extAlong_mem (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n) ⟨χ.1, χ.2⟩).2
        ((P.D.res (leOfHom Y.hom)).map_mem ha) _⟩

/-- `jKpre` is a preimage of `χ` under `jKf`. -/
private theorem jKpre_spec (n : ℤ) (χ : P.HomSec M₁ M₂ n (le_top : Y.left ≤ ⊤)) :
    (P.jKf U M₁ M₂ Y n).hom (P.jKpre U M₁ M₂ Y n χ) = χ := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  change extAlong (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n) ⟨χ.1, χ.2⟩
      (P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (bcF (P.r U) M₁.Q x)) = χ.1 x
  rw [show P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (bcF (P.r U) M₁.Q x) =
    bcF (P.D.res (le_top : Y.left ≤ ⊤)) M₁.Q x from
    bcTotRes_bcF (P.D.res (leOfHom Y.hom)) (P.D.res (le_top : U ≤ ⊤))
      (P.D.res (le_top : Y.left ≤ ⊤)) _ M₁.Q x]
  exact extAlong_bcF (f := P.D.res (le_top : Y.left ≤ ⊤)) (n := n) ⟨χ.1, χ.2⟩ x

/-- **C4 step 3.** `jK` is an isomorphism: injective by uniqueness of extensions along a base
change (`bc_ext_semilinear`), surjective with preimage `extAlong χ ∘ totRes_{V ≤ U}`
(`extAlong_bcF`, `bcTotRes_bcF`). -/
theorem isIso_jK : IsIso (P.jK U M₁ M₂ Y) := by
  have : ∀ n, IsIso ((P.jK U M₁ M₂ Y).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective (P.jKf U M₁ M₂ Y n)).2
      ⟨P.jKf_injective U M₁ M₂ Y n, fun χ =>
        ⟨P.jKpre U M₁ M₂ Y n χ, P.jKpre_spec U M₁ M₂ Y n χ⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end HSide

end PreResolvingData
end Cohesive
end
