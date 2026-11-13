import Cohesivemodules.Comparison.FunctorDef
import Cohesivemodules.Sheaf.Restriction
import Cohesivemodules.Comparison.AlphaOverAux
import Cohesivemodules.Algebra.BaseChangeResAPI

set_option linter.style.header false

/-!
# C1.c: `α` on the over-site of an open `U`

Blueprint item C1.c (§4), audit G11. For an open `U` and a cohesive module `M` over `𝒜(U)`,
`P.sheafOfOver U M` is the complex of sheaves of `O|U`-modules on the over-site of `U` with
`α_U(M)^n(V) = Tot(M|V)` in degree `n` (the same section data as `α`, `Comparison/AlphaDef.lean`,
with base `U₀ = U`). C2 and C4 compare `α(M)|U′` with `α_{U′}` of the restriction `M|U′`.

Not part of the main statement (J uses only `α` on `X`); not frozen.

* `sheafOfOverPre`, `isSheaf_sheafOfOverPre`, `sheafOfOverSh`, `sheafOfOverD`, `sheafOfOver`,
  `sheafOfOverMap`.
* **C1.c** `restrSheafOfIso`: `α(M)|U ≅ α_U(M|U)` (`restr` termwise; `M|U` the base change along
  `res : 𝒜(X) → 𝒜(U)`).
* `exists_quasiIso_sheafOfOverMap_of_iso`: an isomorphism `M ≅ N` in `Ho(P_{𝒜(U)})` gives a homotopy
  equivalence `α_U(M) ≃ α_U(N)`, hence a quasi-isomorphism (audit G5, second half).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X)

section Complex

variable (M : CohesiveModule (P.D.𝒜 U))

/-- **C1.c.** `α_U(M)^n` as a presheaf of `O|U`-modules on the over-site of `U`. -/
def sheafOfOverPre (n : ℤ) : PresheafOfModules.{0} (P.R.over U).obj where
  obj V := ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.sheafOfSec M n (leOfHom V.unop.hom))
  map {V W} f := ModuleCat.semilinearMapAddEquiv ((P.R.over U).obj.map f).hom
      (ModuleCat.of (P.O.obj.obj (op V.unop.left)) (P.sheafOfSec M n (leOfHom V.unop.hom)))
      (ModuleCat.of (P.O.obj.obj (op W.unop.left)) (P.sheafOfSec M n (leOfHom W.unop.hom)))
      (P.sheafOfRes M n (leOfHom V.unop.hom) (leOfHom f.unop.left))
  map_id V := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact P.totRes_id M _ x.1
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact (P.totRes_comp M _ _ _ x.1).symm

/-- **C1.c (C1.a on `U`).** `α_U(M)^n` is a sheaf. -/
theorem isSheaf_sheafOfOverPre (n : ℤ) :
    Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U) (P.sheafOfOverPre U M n).presheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat), isSheaf_iff_isSheaf_of_type]
  exact P.isSheaf_sheafOfOverTy M n

/-- The sheaf `α_U(M)^n` of `O|U`-modules. -/
def sheafOfOverSh (n : ℤ) : Mod (P.R.over U) :=
  ⟨P.sheafOfOverPre U M n, P.isSheaf_sheafOfOverPre U M n⟩

/-- The differential of `α_U(M)`. -/
def sheafOfOverD (n : ℤ) : P.sheafOfOverSh U M n ⟶ P.sheafOfOverSh U M (n + 1) :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (P.sheafOfDV M n (leOfHom V.unop.hom))
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact P.X_totRes M (leOfHom V.unop.hom) (leOfHom f.unop.left) x.1 }⟩

/-- `d² = 0` on `α_U(M)`. -/
theorem sheafOfOverD_sheafOfOverD (n : ℤ) :
    P.sheafOfOverD U M n ≫ P.sheafOfOverD U M (n + 1) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  have h := (M.baseChange (P.D.res (leOfHom V.unop.hom))).flat x.1
  rw [P.c_eq_zero, zero_smul] at h
  exact h

/-- **C1.c.** The complex `α_U(M)` of sheaves of `O|U`-modules on the over-site of `U`. -/
def sheafOfOver : CochainComplex (Mod (P.R.over U)) ℤ :=
  CochainComplex.of (P.sheafOfOverSh U M) (P.sheafOfOverD U M) (P.sheafOfOverD_sheafOfOverD U M)

end Complex

/-- `α_U(φ)` for a closed degree-`0` map `φ` of cohesive modules over `𝒜(U)`. -/
def sheafOfOverMap {M N : CohesiveModule (P.D.𝒜 U)} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) :
    P.sheafOfOver U M ⟶ P.sheafOfOver U N where
  f n := ⟨{ app := fun V ↦ ModuleCat.ofHom (P.sheafOfMapV φ n (leOfHom V.unop.hom))
            naturality := by
              intro V W f
              apply ModuleCat.hom_ext
              refine DFunLike.ext _ _ fun x => ?_
              apply Subtype.ext
              exact bcHomL_bcTotRes (P.D.res (leOfHom f.unop.left))
                (P.D.res (leOfHom V.unop.hom)) (P.D.res ((leOfHom f.unop.left).trans
                  (leOfHom V.unop.hom))) (P.D.res_comp _ _) 0 (P.toHom0 φ) x.1 }⟩
  comm' := by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    have e1 : (P.sheafOfOver U N).d i (i + 1) = P.sheafOfOverD U N i := CochainComplex.of_d _ _ _
    have e2 : (P.sheafOfOver U M).d i (i + 1) = P.sheafOfOverD U M i := CochainComplex.of_d _ _ _
    rw [e1, e2]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    exact (P.bcHomL_X φ (leOfHom V.unop.hom) x.1).symm

section Morphisms

variable {M N : CohesiveModule (P.D.𝒜 U)}

/-- C1.c: `α_U` preserves identities. -/
theorem sheafOfOverMap_id (M : CohesiveModule (P.D.𝒜 U)) :
    P.sheafOfOverMap U (idZ0 M.toQuasiCohesive) = 𝟙 (P.sheafOfOver U M) := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact DFunLike.congr_fun (bcHomL_id (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive) x.1

/-- C1.c: `α_U` preserves composition. -/
theorem sheafOfOverMap_comp {L : CohesiveModule (P.D.𝒜 U)}
    (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (ψ : Z0 N.toQuasiCohesive L.toQuasiCohesive) :
    P.sheafOfOverMap U (compZ0 _ _ _ ψ φ) = P.sheafOfOverMap U φ ≫ P.sheafOfOverMap U ψ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact DFunLike.congr_fun (bcHomL_comp (P.D.res (leOfHom V.unop.hom)) 0 0
    (P.toHom0 ψ) (P.toHom0 φ)) x.1

/-- C1.c: the homotopy component `α_U(M)^i ⟶ α_U(N)^j` (`i + -1 = j`) given by
`h ∈ Hom^{-1}`. -/
def hOverMap (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ)
    (hij : i + -1 = j) : P.sheafOfOverSh U M i ⟶ P.sheafOfOverSh U N j :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (P.hMapV h i j hij (leOfHom V.unop.hom))
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact bcHomL_bcTotRes (P.D.res (leOfHom f.unop.left))
         (P.D.res (leOfHom V.unop.hom)) (P.D.res ((leOfHom f.unop.left).trans
           (leOfHom V.unop.hom))) (P.D.res_comp _ _) (-1) h x.1 }⟩

/-- C1.c: the homotopy `α_U(M) ⟶ α_U(N)` of degree `-1` given by `h ∈ Hom^{-1}` (`0` off the
degree `-1` diagonal). -/
def hOverHom (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (i j : ℤ) :
    (P.sheafOfOver U M).X i ⟶ (P.sheafOfOver U N).X j :=
  if hij : i + -1 = j then P.hOverMap U h i j hij else 0

/-- C1.c: if `φ - ψ = δh` for `h ∈ Hom^{-1}` then `α_U(φ)` and `α_U(ψ)` are homotopic. -/
theorem sheafOfOverMap_homotopic (a b : Z0 M.toQuasiCohesive N.toQuasiCohesive)
    (h : Hom M.toQuasiCohesive N.toQuasiCohesive (-1)) (hab : δ _ _ (-1) h.1 = a.1 - b.1) :
    Nonempty (Homotopy (P.sheafOfOverMap U a) (P.sheafOfOverMap U b)) := by
  refine ⟨{ hom := P.hOverHom U h, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    have : ¬ (i + -1 = j) := by
      intro h'
      apply hij
      change j + 1 = i
      omega
    simp only [hOverHom, this, ↓reduceDIte]
  · intro i'
    obtain ⟨i, rfl⟩ : ∃ i, i' = i + 1 := ⟨i' - 1, by omega⟩
    have e1 : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    have e2 : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    rw [dNext_eq _ e1, prevD_eq _ e2]
    have h1 : i + 1 + -1 = i := by omega
    have h2 : i + 1 + 1 + -1 = i + 1 := by omega
    have d1 : (P.sheafOfOver U M).d (i + 1) (i + 1 + 1) = P.sheafOfOverD U M (i + 1) :=
      CochainComplex.of_d _ _ _
    have d2 : (P.sheafOfOver U N).d i (i + 1) = P.sheafOfOverD U N i := CochainComplex.of_d _ _ _
    rw [d1, d2]
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    apply Subtype.ext
    have k1 : P.hOverHom U h (i + 1 + 1) (i + 1) = P.hOverMap U h _ _ h2 := by
      simp only [hOverHom, h2, ↓reduceDIte]
      rfl
    have k2 : P.hOverHom U h (i + 1) i = P.hOverMap U h _ _ h1 := by
      simp only [hOverHom, h1, ↓reduceDIte]
      rfl
    rw [k1, k2]
    exact hty_formula (M₁ := M.toQuasiCohesive.baseChange (P.D.res (leOfHom V.unop.hom)))
      (M₂ := N.toQuasiCohesive.baseChange (P.D.res (leOfHom V.unop.hom)))
      (bcHomL (P.D.res (leOfHom V.unop.hom)) (-1) h) _ _
      (P.bcHomL_homotopy a b h hab (leOfHom V.unop.hom)) x.1

end Morphisms

section RestrIso

variable (M : CohesiveModule P.𝒜X)

/-- `res_V = res_{V ≤ U} ∘ res_U` as an equality of dga maps (`V ≤ U`). -/
private theorem res_comp_eq {V : Opens X} (h : V ≤ U) :
    (P.D.res h).comp (P.r U) = P.r V :=
  dgaHom_ext' fun a => P.D.res_comp le_top h a

/-- Sectionwise comparison `α(M)^n(V) ≃ α_U(M|U)^n(V)` for `V ≤ U` (A9's `bcCompTot`, transported
along `res_comp_eq`). -/
private def restrEquiv (n : ℤ) {V : Opens X} (h : V ≤ U) :
    P.sheafOfSec M n (le_top : V ≤ ⊤) ≃ₗ[P.O.obj.obj (op V)]
      P.sheafOfSec (M.baseChange (P.r U)) n h where
  toFun x := ⟨cmpTot (P.r U) (P.D.res h) (P.r V) (P.res_comp_eq U h) M.toQuasiCohesive x.1,
    cmpTot_mem _ _ _ _ _ x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' f x := Subtype.ext (cmpTot_smul _ _ _ _ _ (P.ρ V f : P.D.A V) x.1)
  invFun y := ⟨cmpTotInv (P.r U) (P.D.res h) (P.r V) (P.res_comp_eq U h) M.toQuasiCohesive y.1,
    cmpTotInv_mem _ _ _ _ _ y.2⟩
  left_inv x := Subtype.ext (cmpTotInv_cmpTot _ _ _ _ _ x.1)
  right_inv y := Subtype.ext (cmpTot_cmpTotInv _ _ _ _ _ y.1)

/-- The comparison `α(M)^n|U ≅ α_U(M|U)^n`, termwise. -/
private def restrIsoSh (n : ℤ) :
    (restr P.R U).obj (P.sheafOfSh M n) ≅ P.sheafOfOverSh U (M.baseChange (P.r U)) n :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun V => (P.restrEquiv U M n (leOfHom V.unop.hom)).toModuleIso) (by
        intro V W f
        apply ModuleCat.hom_ext
        refine DFunLike.ext _ _ fun x => ?_
        apply Subtype.ext
        exact cmpTot_bcTotRes (P.r U) (P.D.res (leOfHom V.unop.hom)) (P.r V.unop.left)
          (P.res_comp_eq U _) M.toQuasiCohesive (P.D.res (leOfHom f.unop.left))
          (P.D.res ((leOfHom f.unop.left).trans (leOfHom V.unop.hom))) (P.r W.unop.left)
          (P.res_comp_eq U _) (P.D.res_comp _ _) (P.D.res_comp _ _) x.1))

end RestrIso

/-- **C1.c.** `α(M)|U ≅ α_U(M|U)`, with `M|U` the base change of `M` along
`res : 𝒜(X) → 𝒜(U)` (A9). -/
def restrSheafOfIso (M : CohesiveModule P.𝒜X) :
    ((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P.sheafOf M) ≅
      P.sheafOfOver U (M.baseChange (P.r U)) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => P.restrIsoSh U M n) ?_
  intro i j hij
  obtain rfl : i + 1 = j := hij
  have e1 : (P.sheafOfOver U (M.baseChange (P.r U))).d i (i + 1) =
      P.sheafOfOverD U (M.baseChange (P.r U)) i := CochainComplex.of_d _ _ _
  have e2 : (P.sheafOf M).d i (i + 1) = P.sheafOfD M i := CochainComplex.of_d _ _ _
  have e3 : (((restr P.R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P.sheafOf M)).d i
      (i + 1) = (restr P.R U).map (P.sheafOfD M i) := by
    change (restr P.R U).map ((P.sheafOf M).d i (i + 1)) = _
    rw [e2]
    rfl
  rw [e1, e3]
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact cmpTot_X (P.r U) (P.D.res (leOfHom V.unop.hom)) (P.r V.unop.left)
    (P.res_comp_eq U _) M.toQuasiCohesive x.1

/-- An isomorphism in `Ho(P_{𝒜(U)})` is represented by a closed map whose image under `α_U` is a
quasi-isomorphism (it is a homotopy equivalence). -/
theorem exists_quasiIso_sheafOfOverMap_of_iso {M N : CohesiveModule (P.D.𝒜 U)}
    (e : HoP.mk M ≅ HoP.mk N) :
    ∃ φ : Z0 M.toQuasiCohesive N.toQuasiCohesive, QuasiIso (P.sheafOfOverMap U φ) := by
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
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _ e.hom
  obtain ⟨ψ, hψ⟩ := Submodule.Quotient.mk_surjective _ e.inv
  have h1 := key φ ψ (by
    have := e.hom_inv_id
    rw [HoP.comp_def, ← hφ, ← hψ, compH0_mk] at this
    exact this)
  have h2 := key ψ φ (by
    have := e.inv_hom_id
    change compH0 N.toQuasiCohesive M.toQuasiCohesive N.toQuasiCohesive e.hom e.inv =
      Submodule.Quotient.mk (idZ0 N.toQuasiCohesive) at this
    rw [← hφ, ← hψ, compH0_mk] at this
    exact this)
  obtain ⟨H1⟩ := h1
  obtain ⟨H2⟩ := h2
  refine ⟨φ, ?_⟩
  exact (HomotopyEquiv.mk (P.sheafOfOverMap U φ) (P.sheafOfOverMap U ψ) H1 H2).quasiIso_hom

end PreResolvingData

end Cohesive
