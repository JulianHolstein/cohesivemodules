import Cohesivemodules.Comparison.FullyFaithfulPhiH

set_option linter.style.header false

/-!
# C4 step 3: the sections of `Φ` over a fixed `Y` (part 2 of 2)

Split from `Comparison/FullyFaithfulPhi.lean` for size;
continues `Comparison/FullyFaithfulPhiH.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace CochainComplex.HomComplex
variable {X : Type} [TopologicalSpace X]
namespace PreResolvingData
variable (P : PreResolvingData X) (U : Opens X)

/-! ### The `L` side -/

section LSide

variable (W : CochainComplex (ModuleCat.{0} (P.O.obj.obj (op U))) ℤ)
  (L : CochainComplex (Mod (P.R.over U)) ℤ)
  (ε : ((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ≅ W)
  (M₂ : CohesiveModule P.𝒜X) (Y : Over U)

/-- The value `c_{p,p+n}((ε⁻¹ w)|Y) ∈ α(M₂)^{p+n}(V)`, as an element of `Tot(M₂|V)`. -/
def evLVal {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n) (p : ℤ)
    (w : W.X p) : (P.NY U M₂ Y).T :=
  (show P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤) from
    restrEval (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) rfl) ((ε.inv.f p).hom w)).1

/-- `evLVal` is additive in `w`. -/
theorem evLVal_add {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n) (p : ℤ)
    (w w' : W.X p) :
    P.evLVal U W L ε M₂ Y c p (w + w') =
      P.evLVal U W L ε M₂ Y c p w + P.evLVal U W L ε M₂ Y c p w' := by
  have e := restrEval_add (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) rfl)
    ((ε.inv.f p).hom w) ((ε.inv.f p).hom w')
  exact congrArg Subtype.val
    ((congrArg (restrEval (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) rfl))
      ((ε.inv.f p).hom.map_add w w')).trans e)

/-- `evLVal` is `ρ_Y`-semilinear in `w`. -/
theorem evLVal_smul {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n) (p : ℤ)
    (r : P.O.obj.obj (op U)) (w : W.X p) :
    P.evLVal U W L ε M₂ Y c p (r • w) = P.ρY U Y r • P.evLVal U W L ε M₂ Y c p w := by
  have h1 := (ε.inv.f p).hom.map_smul r w
  have e := restrEval_smul (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) rfl) r
    ((ε.inv.f p).hom w)
  refine (congrArg Subtype.val
    ((congrArg (restrEval (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) rfl)) h1).trans
      e)).trans ?_
  change P.ρ Y.left (P.O.obj.map (homOfLE (leOfHom Y.hom)).op r) • _ = _
  rw [← P.ρ_natural]
  rfl

/-- `evLVal` as a `ρ_Y`-semilinear map. -/
def evLV {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n) (p : ℤ) :
    W.X p →ₛₗ[P.ρY U Y] (P.NY U M₂ Y).T where
  toFun := P.evLVal U W L ε M₂ Y c p
  map_add' := P.evLVal_add U W L ε M₂ Y c p
  map_smul' := P.evLVal_smul U W L ε M₂ Y c p

/-- `evLV` lands in `Hom^n_{O(U)}(W, M₂|V)` (degree `p + n`). -/
theorem evLV_mem {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n) :
    P.evLV U W L ε M₂ Y c ∈ HomR (P.ρY U Y) W (P.NY U M₂ Y) n := by
  intro p w
  exact (restrEval (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) rfl)
    ((ε.inv.f p).hom w) : P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)).2

/-- `evLV` of the zero cochain is zero. -/
theorem evLV_zero (n : ℤ) :
    P.evLV U W L ε M₂ Y
      (0 : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n) = 0 := by
  funext p
  refine LinearMap.ext fun w => ?_
  change (restrEval (Over.mkIdTerminal (X := U)) Y
    ((0 : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n).v p (p + n)
      rfl)
    ((ε.inv.f p).hom w) : P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)).1 = 0
  rw [Cochain.zero_v]
  rfl

/-- `evLV` is additive in the cochain. -/
theorem evLV_add {n : ℤ}
    (c c' : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n) :
    P.evLV U W L ε M₂ Y (c + c') = P.evLV U W L ε M₂ Y c + P.evLV U W L ε M₂ Y c' := by
  funext p
  refine LinearMap.ext fun w => ?_
  change (restrEval (Over.mkIdTerminal (X := U)) Y ((c + c').v p (p + n) rfl)
    ((ε.inv.f p).hom w) : P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)).1 =
    (restrEval (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) rfl)
      ((ε.inv.f p).hom w) : P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)).1 +
    (restrEval (Over.mkIdTerminal (X := U)) Y (c'.v p (p + n) rfl)
      ((ε.inv.f p).hom w) : P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)).1
  rw [Cochain.add_v]
  rfl

/-- `evL` in degree `n`. -/
def evLf (n : ℤ) :
    (CochainComplex.HomComplex ((overC Y).obj L)
      ((overC Y).obj ((overC U).obj (P.sheafOf M₂)))).X n ⟶
      (famComplex W (d_f0_comp (P.D.res (leOfHom Y.hom)) (P.d_ρ U)) (P.c_eq_zero Y.left)
        (P.NY U M₂ Y)).X n :=
  AddCommGrpCat.ofHom
    { toFun := fun c => ⟨P.evLV U W L ε M₂ Y c, P.evLV_mem U W L ε M₂ Y c⟩
      map_zero' := Subtype.ext (P.evLV_zero U W L ε M₂ Y n)
      map_add' := fun c c' => Subtype.ext (P.evLV_add U W L ε M₂ Y c c') }

/-- `evLf` on an element (rfl). -/
theorem evLf_apply (n : ℤ)
    (c : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n) (p : ℤ)
    (w : W.X p) :
    (show HomR (P.ρY U Y) W (P.NY U M₂ Y) n from (P.evLf U W L ε M₂ Y n).hom c).1 p w =
      P.evLVal U W L ε M₂ Y c p w := rfl

/-- The differential of `α(M)` on sections over `V` is `𝕏` of `M|V`, for any `j = i + 1`. -/
private lemma sheafOf_d_val (M : CohesiveModule P.𝒜X) (i j : ℤ) (h : i + 1 = j) (V : Opens X)
    (x : P.sheafOfSec M i (le_top : V ≤ ⊤)) :
    ((((P.sheafOf M).d i j).val.app (op V)).hom x : P.sheafOfSec M j (le_top : V ≤ ⊤)).1 =
      (M.baseChange (P.D.res (le_top : V ≤ ⊤))).X x.1 := by
  subst h
  have e : (P.sheafOf M).d i (i + 1) = P.sheafOfD M i := CochainComplex.of_d _ _ _
  rw [e]
  rfl

/-- The value of `evLVal` does not depend on the target index. -/
private lemma evVal_congr {n : ℤ}
    (c : Cochain ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) n)
    (p q q' : ℤ) (h : p + n = q) (h' : p + n = q') (m : (L.X p).val.obj (op (Over.mk (𝟙 U)))) :
    (restrEval (Over.mkIdTerminal (X := U)) Y (c.v p q h) m :
      P.sheafOfSec M₂ q (le_top : Y.left ≤ ⊤)).1 =
    (restrEval (Over.mkIdTerminal (X := U)) Y (c.v p q' h') m :
      P.sheafOfSec M₂ q' (le_top : Y.left ≤ ⊤)).1 := by
  subst h
  subst h'
  rfl

/-- `evLf` commutes with the differentials: Mathlib's `δ` on cochains (`δ_v`), `ε⁻¹` a chain
map, restriction commuting with the differential of `L`, and the differential of `α(M₂)` over
`V` being `𝕏` of `M₂|V` give A10.a's `homRδ`. -/
theorem evLf_comm (n : ℤ) :
    P.evLf U W L ε M₂ Y n ≫ (famComplex W (d_f0_comp (P.D.res (leOfHom Y.hom)) (P.d_ρ U))
        (P.c_eq_zero Y.left) (P.NY U M₂ Y)).d n (n + 1) =
      (CochainComplex.HomComplex ((overC Y).obj L)
        ((overC Y).obj ((overC U).obj (P.sheafOf M₂)))).d n (n + 1) ≫
        P.evLf U W L ε M₂ Y (n + 1) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  funext p
  apply LinearMap.ext
  intro w
  simp only [famComplex, CochainComplex.of_d]
  change (P.NY U M₂ Y).X (P.evLVal U W L ε M₂ Y c p w) -
      n.negOnePow • P.evLVal U W L ε M₂ Y c (p + 1) (dW W p w) =
    P.evLVal U W L ε M₂ Y (CochainComplex.HomComplex.δ n (n + 1) c) p w
  have hv := CochainComplex.HomComplex.δ_v n (n + 1) rfl c p (p + (n + 1)) rfl (p + n) (p + 1)
    (by omega) rfl
  have hε : ((L.d p (p + 1)).val.app (op (Over.mk (𝟙 U)))).hom ((ε.inv.f p).hom w) =
      (ε.inv.f (p + 1)).hom (dW W p w) :=
    congrArg (fun q => q.hom w) (ε.inv.comm p (p + 1))
  have e1 : restrEval (Over.mkIdTerminal (X := U)) Y
      ((CochainComplex.HomComplex.δ n (n + 1) c).v p (p + (n + 1)) rfl) ((ε.inv.f p).hom w) =
    restrEval (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) (by omega) ≫
        ((overC Y).obj ((overC U).obj (P.sheafOf M₂))).d (p + n) (p + (n + 1)))
        ((ε.inv.f p).hom w) +
      (n + 1).negOnePow • restrEval (Over.mkIdTerminal (X := U)) Y
        (((overC Y).obj L).d p (p + 1) ≫ c.v (p + 1) (p + (n + 1)) (by omega))
        ((ε.inv.f p).hom w) := by
    rw [hv]
    exact (restrEval_hom_add _ Y _ _ _).trans
      (congrArg (HAdd.hAdd _) (restrEval_hom_units _ Y _ _ _))
  have e2 : restrEval (Over.mkIdTerminal (X := U)) Y
      (((overC Y).obj L).d p (p + 1) ≫ c.v (p + 1) (p + (n + 1)) (by omega))
        ((ε.inv.f p).hom w) =
      restrEval (Over.mkIdTerminal (X := U)) Y (c.v (p + 1) (p + (n + 1)) (by omega))
        ((ε.inv.f (p + 1)).hom (dW W p w)) :=
    (restrEval_over_comp (Over.mkIdTerminal (X := U)) Y (L.d p (p + 1)) _ _).trans
      (congrArg _ hε)
  have t1 : (restrEval (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) (by omega) ≫
        ((overC Y).obj ((overC U).obj (P.sheafOf M₂))).d (p + n) (p + (n + 1)))
        ((ε.inv.f p).hom w) : P.sheafOfSec M₂ (p + (n + 1)) (le_top : Y.left ≤ ⊤)).1 =
      (P.NY U M₂ Y).X (P.evLVal U W L ε M₂ Y c p w) :=
    P.sheafOf_d_val M₂ (p + n) (p + (n + 1)) (by omega) Y.left
      (restrEval (Over.mkIdTerminal (X := U)) Y (c.v p (p + n) rfl) ((ε.inv.f p).hom w))
  have t2 : (restrEval (Over.mkIdTerminal (X := U)) Y (c.v (p + 1) (p + (n + 1)) (by omega))
        ((ε.inv.f (p + 1)).hom (dW W p w)) :
          P.sheafOfSec M₂ (p + (n + 1)) (le_top : Y.left ≤ ⊤)).1 =
      P.evLVal U W L ε M₂ Y c (p + 1) (dW W p w) :=
    P.evVal_congr U L M₂ Y c (p + 1) _ _ _ _ _
  have t3 := congrArg Subtype.val e1
  rw [e2] at t3
  change _ = _ + _ at t3
  rw [t1] at t3
  have h4 : ∀ (z : ℤˣ) (x : P.sheafOfSec M₂ (p + (n + 1)) (le_top : Y.left ≤ ⊤)),
      (z • x : P.sheafOfSec M₂ (p + (n + 1)) (le_top : Y.left ≤ ⊤)).1 = z • x.1 := fun z x => rfl
  have h5 := (h4 (n + 1).negOnePow (restrEval (Over.mkIdTerminal (X := U)) Y
    (c.v (p + 1) (p + (n + 1)) (by omega)) ((ε.inv.f (p + 1)).hom (dW W p w)))).trans
    (congrArg (HSMul.hSMul (n + 1).negOnePow) t2)
  have hfin : (P.NY U M₂ Y).X (P.evLVal U W L ε M₂ Y c p w) -
      n.negOnePow • P.evLVal U W L ε M₂ Y c (p + 1) (dW W p w) =
      (P.NY U M₂ Y).X (P.evLVal U W L ε M₂ Y c p w) +
      (n + 1).negOnePow • P.evLVal U W L ε M₂ Y c (p + 1) (dW W p w) := by
    generalize P.evLVal U W L ε M₂ Y c (p + 1) (dW W p w) = B
    generalize (P.NY U M₂ Y).X (P.evLVal U W L ε M₂ Y c p w) = A
    simp only [Int.negOnePow_succ, Units.smul_def, Units.val_neg, neg_smul, sub_eq_add_neg]
  exact hfin.trans
    ((congrArg (fun x => (P.NY U M₂ Y).X (P.evLVal U W L ε M₂ Y c p w) + x) h5.symm).trans
      t3.symm)

/-- **C4 step 3.** Evaluation on `Γ_U(L) ≅ W`, restricted to `Y`:
`Cochain(L|Y, α(M₂)|Y) ⟶ Hom^•_{O(U)}(W, M₂|V)`, `c ↦ (w ↦ c_{p,p+n}((ε⁻¹ w)|Y))`. -/
def evL :
    CochainComplex.HomComplex ((overC Y).obj L) ((overC Y).obj ((overC U).obj (P.sheafOf M₂))) ⟶
    famComplex W (d_f0_comp (P.D.res (leOfHom Y.hom)) (P.d_ρ U)) (P.c_eq_zero Y.left)
      (P.NY U M₂ Y) where
  f n := P.evLf U W L ε M₂ Y n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact P.evLf_comm U W L ε M₂ Y i

/-- `evLf` is injective for `L` with terms direct summands of finite free modules. -/
private theorem evLf_injective (hL : IsStrictlyPerfect L) (n : ℤ) :
    Function.Injective (P.evLf U W L ε M₂ Y n).hom := by
  intro c c' h
  have hh : ∀ p (w : W.X p), P.evLVal U W L ε M₂ Y c p w = P.evLVal U W L ε M₂ Y c' p w :=
    fun p w => congrArg (fun χ : HomR (P.ρY U Y) W (P.NY U M₂ Y) n => χ.1 p w) h
  refine Cochain.ext _ _ fun p q hpq => ?_
  subst hpq
  refine restrEval_injective (Over.mkIdTerminal (X := U)) (hL.2 p) _ Y ?_
  funext m
  have hm : (ε.inv.f p).hom ((ε.hom.f p).hom m) = m :=
    congrArg (fun φ => (φ.f p).hom m) ε.hom_inv_id
  have := hh p ((ε.hom.f p).hom m)
  rw [← hm]
  exact Subtype.ext this

/-- `evLf` is surjective for `L` with terms direct summands of finite free modules. -/
private theorem evLf_surjective (hL : IsStrictlyPerfect L) (n : ℤ) :
    Function.Surjective (P.evLf U W L ε M₂ Y n).hom := by
  intro (g : HomR (P.ρY U Y) W (P.NY U M₂ Y) n)
  have key : ∀ p : ℤ, ∃ G : ((overC Y).obj L).X p ⟶
      ((overC Y).obj ((overC U).obj (P.sheafOf M₂))).X (p + n),
      restrEval (Over.mkIdTerminal (X := U)) Y G = fun m =>
        (⟨(g.1 p) ((ε.hom.f p).hom m), g.2 p _⟩ :
          P.sheafOfSec M₂ (p + n) (le_top : Y.left ≤ ⊤)) := by
    intro p
    refine restrEval_surjective (Over.mkIdTerminal (X := U)) (hL.2 p) _ Y _ ?_ ?_
    · intro m m'
      exact Subtype.ext
        ((congrArg (g.1 p) ((ε.hom.f p).hom.map_add m m')).trans ((g.1 p).map_add _ _))
    · intro r m
      refine Subtype.ext ?_
      exact ((congrArg (g.1 p) ((ε.hom.f p).hom.map_smul r m)).trans
        (map_smulₛₗ (g.1 p) r _)).trans
        (congrArg (fun a : ↥(P.D.𝒜 Y.left 0) => (a : P.D.A Y.left) • (g.1 p)
          ((ε.hom.f p).hom m)) (P.ρ_natural (leOfHom Y.hom) r))
  choose G hG using key
  refine ⟨Cochain.mk fun p q hpq => hpq ▸ G p, Subtype.ext (funext fun p => ?_)⟩
  refine LinearMap.ext fun w => ?_
  have hm : (ε.hom.f p).hom ((ε.inv.f p).hom w) = w :=
    congrArg (fun φ => (φ.f p).hom w) ε.inv_hom_id
  have := congrArg (fun F => (F ((ε.inv.f p).hom w)).1) (hG p)
  change _ = (g.1 p) ((ε.hom.f p).hom ((ε.inv.f p).hom w)) at this
  rw [hm] at this
  exact this

/-- **C4 step 3.** For `L` strictly perfect, `evL` is an isomorphism: in each degree it is the
product over `p` of the bijections of S4.c with restriction (`restrEval_injective`,
`restrEval_surjective`) composed with `ε⁻¹`, read in total degree `p + n` (`sheafOfSec`). -/
theorem isIso_evL (hL : IsStrictlyPerfect L) : IsIso (P.evL U W L ε M₂ Y) := by
  have : ∀ n, IsIso ((P.evL U W L ε M₂ Y).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective (P.evLf U W L ε M₂ Y n)).2
      ⟨P.evLf_injective U W L ε M₂ Y hL n, P.evLf_surjective U W L ε M₂ Y hL n⟩
  exact HomologicalComplex.Hom.isIso_of_components _

end LSide

/-! ### The value of `ι` -/

section Iota

variable (W : CochainComplex (ModuleCat.{0} (P.O.obj.obj (op U))) ℤ)
  (hW : IsBoundedFGProj (P.O.obj.obj (op U)) W)
  (L : CochainComplex (Mod (P.R.over U)) ℤ)
  (ε : ((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex (ComplexShape.up ℤ)).obj L
      ≅ W)
  (u : L ⟶ P.sheafOfOver U (P.fcMod U W hW))
  (M₁ : CohesiveModule P.𝒜X)
  (φ : Z0 (P.fcMod U W hW).toQuasiCohesive (M₁.baseChange (P.r U)).toQuasiCohesive)
  (Y : Over U)

/-- **C4 step 3.** If `Γ_U(u) = ε ≫ unitMap` (C2's `u`), then
`ι = u ≫ α_U(φ) ≫ (restrSheafOfIso)⁻¹ : L ⟶ α(M₁)|U` sends `(ε⁻¹ w)|Y` to `(φ(1 ⊗ 1 ⊗ w))|V`:
naturality of `ι` along `Y ⟶ U`, `hu`, the formula for `α_U(φ)` (`bcHomL_bcF`) and
`cmpTotInv_bcF`. -/
theorem ι_app_res
    (hu : ((gammaT (P.R.over U) (Over.mk (𝟙 U))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map u = ε.hom ≫ P.unitMap U W hW) (p : ℤ) (w : W.X p) :
    (show P.sheafOfSec M₁ p (le_top : Y.left ≤ ⊤) from
      (((u ≫ P.sheafOfOverMap U φ ≫ (P.restrSheafOfIso U M₁).inv).f p).val.app (op Y)).hom
        (((L.X p).val.map ((Over.mkIdTerminal (X := U)).from Y).op).hom
          ((ε.inv.f p).hom w))).1 =
      P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) (φ.1 (fcι (P.ρ U) W w)) := by
  have hm : (ε.hom.f p).hom ((ε.inv.f p).hom w) = w :=
    congrArg (fun φ => (φ.f p).hom w) ε.inv_hom_id
  have hu' : ((u.f p).val.app (op (Over.mk (𝟙 U)))).hom ((ε.inv.f p).hom w) =
      P.unitElt U W hW p w :=
    (congrArg (fun φ => (φ.f p).hom ((ε.inv.f p).hom w)) hu).trans
      (congrArg (fun x => (P.unitHom U W hW p).hom x) hm)
  have hnat := PresheafOfModules.naturality_apply
    ((u ≫ P.sheafOfOverMap U φ ≫ (P.restrSheafOfIso U M₁).inv).f p).val
    ((Over.mkIdTerminal (X := U)).from Y).op ((ε.inv.f p).hom w)
  have e0 := congrArg Subtype.val hu'
  have hz : ((((u ≫ P.sheafOfOverMap U φ ≫ (P.restrSheafOfIso U M₁).inv).f p).val.app
      (op (Over.mk (𝟙 U)))).hom ((ε.inv.f p).hom w) :
        P.sheafOfSec M₁ p (le_top : U ≤ ⊤)).1 = φ.1 (fcι (P.ρ U) W w) := by
    change cmpTotInv (P.r U) (P.D.res (le_refl U)) (P.r U) _ M₁.toQuasiCohesive
      (bcHomL (P.D.res (le_refl U)) 0 (P.toHom0 φ)
        (((u.f p).val.app (op (Over.mk (𝟙 U)))).hom ((ε.inv.f p).hom w)).1) = _
    have e1 : (P.unitElt U W hW p w).1 =
        bcF (P.D.res (le_refl U)) (FCGen (P.ρ U) W) (fcι (P.ρ U) W w) := rfl
    have e2 : bcHomL (P.D.res (le_refl U)) 0 (P.toHom0 φ)
        (bcF (P.D.res (le_refl U)) (FCGen (P.ρ U) W) (fcι (P.ρ U) W w)) =
        bcF (P.D.res (le_refl U)) (M₁.baseChange (P.r U)).toQuasiCohesive.Q
          (φ.1 (fcι (P.ρ U) W w)) :=
      bcHomL_bcF (P.D.res (le_refl U)) 0 (P.toHom0 φ) (fcι (P.ρ U) W w)
    rw [e0, e1]
    refine (congrArg (fun y => cmpTotInv (P.r U) (P.D.res (le_refl U)) (P.r U) _
      M₁.toQuasiCohesive y) e2).trans ?_
    refine (cmpTotInv_bcF (P.r U) (P.D.res (le_refl U)) (P.r U) _ M₁.toQuasiCohesive _).trans ?_
    exact P.totRes_id M₁ _ _
  refine Eq.trans (congrArg Subtype.val hnat) ?_
  change P.totRes M₁ (le_top : U ≤ ⊤) (leOfHom Y.hom) _ = _
  rw [hz]

end Iota

end PreResolvingData

end Cohesive
