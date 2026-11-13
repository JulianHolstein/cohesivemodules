import Cohesivemodules.Sheaf.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

set_option linter.style.header false

/-!
# S4.c with restriction: maps out of a free summand restricted to `Y`

Blueprint item S4.c (§4), in the form used by C4 step 3 (`quasiIso_Φ`). On a small site with a
terminal object `T`, let `M` be a direct summand of a finite free module. A morphism
`g : M|Y ⟶ N|Y` on the over-site of `Y` is determined by the map
`M(T) → N(Y)`, `m ↦ g_Y(m|Y)` (`restrEval`), and every additive map `M(T) → N(Y)` that is
semilinear along the restriction `R(T) → R(Y)` arises this way. For `Y = T` this is the
Hom bijection `bijective_gammaT_map` (`Comparison/PerfectAux.lean`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}} {T : C}

/-- Restriction to `Y`, then evaluation: `restrEval g m = g_Y(m|Y)` for `g : M|Y ⟶ N|Y` and
`m ∈ M(T)` (`T` terminal; `M|Y` evaluated at `Y → Y` is `M(Y)`). -/
def restrEval (hT : IsTerminal T) {M N : Mod R} (Y : C) (g : M.over Y ⟶ N.over Y)
    (m : M.val.obj (op T)) : N.val.obj (op Y) :=
  (g.val.app (op (Over.mk (𝟙 Y)))).hom ((M.val.map (hT.from Y).op).hom m)

/-- `restrEval g` is additive. -/
theorem restrEval_add (hT : IsTerminal T) {M N : Mod R} (Y : C) (g : M.over Y ⟶ N.over Y)
    (m m' : M.val.obj (op T)) :
    restrEval hT Y g (m + m') = restrEval hT Y g m + restrEval hT Y g m' := by
  unfold restrEval
  rw [map_add (ModuleCat.Hom.hom (M.val.map (hT.from Y).op)) m m']
  exact map_add (ModuleCat.Hom.hom (g.val.app (op (Over.mk (𝟙 Y))))) _ _

/-- `restrEval g` is semilinear along the restriction `R(T) → R(Y)`. -/
theorem restrEval_smul (hT : IsTerminal T) {M N : Mod R} (Y : C) (g : M.over Y ⟶ N.over Y)
    (r : R.obj.obj (op T)) (m : M.val.obj (op T)) :
    restrEval hT Y g (r • m) = (R.obj.map (hT.from Y).op).hom r • restrEval hT Y g m := by
  unfold restrEval
  rw [PresheafOfModules.map_smul]
  exact (g.val.app (op (Over.mk (𝟙 Y)))).hom.map_smul _ _

private instance overFunctorAdditive (Y : C) :
    (SheafOfModules.overFunctor.{0} R Y).Additive where
  map_add := rfl

private instance evaluationAdditive (X : Cᵒᵖ) :
    (SheafOfModules.evaluation.{0} R X).Additive where
  map_add := rfl

/-- The target module `N(Y)` as an `R(T)`-module. -/
private abbrev resE (hT : IsTerminal T) (N : Mod R) (Y : C) : ModuleCat.{0} (R.obj.obj (op T)) :=
  (ModuleCat.restrictScalars (R.obj.map (hT.from Y).op).hom).obj (N.val.obj (op Y))

/-- `restrEval` as a linear map. -/
private def phi (hT : IsTerminal T) {M N : Mod R} (Y : C) (g : M.over Y ⟶ N.over Y) :
    (SheafOfModules.evaluation.{0} R (op T)).obj M ⟶ resE hT N Y :=
  ModuleCat.ofHom (X := (SheafOfModules.evaluation.{0} R (op T)).obj M) (Y := resE hT N Y)
    { toFun := restrEval hT Y g
      map_add' := restrEval_add hT Y g
      map_smul' := fun r m => restrEval_smul hT Y g r m }

/-- Naturality of `phi` in the source module. -/
private lemma phi_nat (hT : IsTerminal T) {M' M N : Mod R} (Y : C) (a : M' ⟶ M)
    (g : M.over Y ⟶ N.over Y) :
    phi hT Y ((SheafOfModules.overFunctor.{0} R Y).map a ≫ g) =
      (SheafOfModules.evaluation.{0} R (op T)).map a ≫ phi hT Y g := by
  ext m
  show restrEval hT Y ((SheafOfModules.overFunctor.{0} R Y).map a ≫ g) m =
    restrEval hT Y g ((a.val.app (op T)).hom m)
  unfold restrEval
  have := PresheafOfModules.naturality_apply a.val (hT.from Y).op m
  refine congrArg (fun x => (g.val.app (op (Over.mk (𝟙 Y)))).hom x) ?_
  exact this

omit [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A section of a sheaf on the over-site is determined by its value at the terminal object. -/
private lemma sections_eq_of_terminal_over {V : C} {M : Mod (R.over V)} (s t : M.sections)
    (h : s.1 (op (Over.mk (𝟙 V))) = t.1 (op (Over.mk (𝟙 V)))) : s = t := by
  apply PresheafOfModules.sections_ext
  intro Z
  obtain ⟨Z⟩ := Z
  let u : Z ⟶ Over.mk (𝟙 V) := Over.homMk Z.hom (by simp)
  have h1 := PresheafOfModules.sections_property s u.op
  have h2 := PresheafOfModules.sections_property t u.op
  rw [← h1, ← h2, h]

/-- Evaluation at the unit section. -/
private def epsF (N : Mod R) (V : C) (φ : (SheafOfModules.unit R).over V ⟶ N.over V) :
    N.val.obj (op V) :=
  (φ.val.app (op (Over.mk (𝟙 V)))).hom (1 : R.obj.obj (op V))

/-- `epsF` is bijective. -/
private lemma epsF_bijective (N : Mod R) (V : C) : Function.Bijective (epsF N V) := by
  constructor
  · intro φ ψ hφψ
    have := sections_eq_of_terminal_over (M := N.over V)
      ((N.over V).unitHomEquiv (show SheafOfModules.unit (R.over V) ⟶ N.over V from φ))
      ((N.over V).unitHomEquiv (show SheafOfModules.unit (R.over V) ⟶ N.over V from ψ)) hφψ
    exact (N.over V).unitHomEquiv.injective this
  · intro s0
    let sec : (N.over V).sections := PresheafOfModules.sectionsMk
      (fun Z ↦ N.val.map Z.unop.hom.op s0) (by
        intro Z Z' g
        have hw : g.unop.left ≫ Z.unop.hom = Z'.unop.hom := Over.w g.unop
        show (N.val.map g.unop.left.op).hom (N.val.map Z.unop.hom.op s0) = _
        rw [← PresheafOfModules.map_comp_apply]
        rw [← hw]
        rfl)
    refine ⟨(N.over V).unitHomEquiv.symm sec, ?_⟩
    show ((N.over V).unitHomEquiv ((N.over V).unitHomEquiv.symm sec)).val
      (op (Over.mk (𝟙 V))) = s0
    rw [Equiv.apply_symm_apply]
    show (N.val.map (𝟙 (op V))).hom s0 = s0
    simp only [PresheafOfModules.map_id]
    rfl

/-- On the unit, `restrEval g r = res r • g_Y(1)`. -/
private lemma restrEval_unit (hT : IsTerminal T) (N : Mod R) (Y : C)
    (g : (SheafOfModules.unit R).over Y ⟶ N.over Y) (r : R.obj.obj (op T)) :
    restrEval hT Y g r = (R.obj.map (hT.from Y).op).hom r • epsF N Y g := by
  have h := (g.val.app (op (Over.mk (𝟙 Y)))).hom.map_smul
    ((R.obj.map (hT.from Y).op).hom r) (1 : R.obj.obj (op Y))
  have e : ((SheafOfModules.unit R).val.map (hT.from Y).op).hom r =
      (R.obj.map (hT.from Y).op).hom r • (1 : R.obj.obj (op Y)) := by
    show (R.obj.map (hT.from Y).op).hom r = _
    rw [smul_eq_mul, mul_one]
  unfold restrEval
  rw [e]
  exact h

/-- On the unit, `phi` is bijective. -/
private lemma phi_unit_bijective (hT : IsTerminal T) (N : Mod R) (Y : C) :
    Function.Bijective (phi hT (M := SheafOfModules.unit R) (N := N) Y) := by
  constructor
  · intro g g' h
    apply (epsF_bijective N Y).1
    have := congrArg (fun k => (ModuleCat.Hom.hom k) (1 : R.obj.obj (op T))) h
    change restrEval hT Y g (1 : R.obj.obj (op T)) =
      restrEval hT Y g' (1 : R.obj.obj (op T)) at this
    simp only [restrEval_unit, map_one, one_smul] at this
    exact this
  · intro k
    obtain ⟨g, hg⟩ := (epsF_bijective N Y).2 ((ModuleCat.Hom.hom k) (1 : R.obj.obj (op T)))
    refine ⟨g, ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (r : R.obj.obj (op T))
    refine (restrEval_unit hT N Y g r).trans ?_
    rw [hg]
    have := (ModuleCat.Hom.hom k).map_smul r (1 : R.obj.obj (op T))
    have e : @HSMul.hSMul (R.obj.obj (op T))
        ((SheafOfModules.evaluation.{0} R (op T)).obj (SheafOfModules.unit R)) _ _ r
        (1 : R.obj.obj (op T)) = (r : R.obj.obj (op T)) := by
      show r * 1 = r
      exact mul_one r
    rw [e] at this
    exact this.symm

/-- Abstract coproduct step: a natural comparison `Φ` between `Hom(H M, X)` and `Hom(G M, E)`
that is bijective on the summands is bijective on the coproduct. -/
private theorem bij_sigma_gen {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
    (H : C₁ ⥤ C₂) (G : C₁ ⥤ D) {ι : Type} (M : ι → C₁) [HasCoproduct M]
    [PreservesColimit (Discrete.functor M) H] [PreservesColimit (Discrete.functor M) G]
    (X : C₂) (E : D) (Φ : ∀ P : C₁, (H.obj P ⟶ X) → (G.obj P ⟶ E))
    (nat : ∀ {P P' : C₁} (a : P' ⟶ P) (g : H.obj P ⟶ X), Φ P' (H.map a ≫ g) = G.map a ≫ Φ P g)
    (h : ∀ i, Function.Bijective (Φ (M i))) : Function.Bijective (Φ (∐ M)) := by
  constructor
  · intro g g' hg
    refine (isColimitOfPreserves H (coproductIsCoproduct M)).hom_ext fun j => ?_
    simp only [Functor.mapCocone_ι_app]
    apply (h j.as).1
    show Φ _ (H.map (Sigma.ι M j.as) ≫ g) = Φ _ (H.map (Sigma.ι M j.as) ≫ g')
    rw [nat, nat, hg]
  · intro k
    have := fun i => (h i).2 (G.map (Sigma.ι M i) ≫ k)
    choose g hg using this
    let c : Cocone (Discrete.functor M ⋙ H) :=
      { pt := X, ι := Discrete.natTrans fun j => g j.as }
    refine ⟨(isColimitOfPreserves H (coproductIsCoproduct M)).desc c, ?_⟩
    refine (isColimitOfPreserves G (coproductIsCoproduct M)).hom_ext fun j => ?_
    simp only [Functor.mapCocone_ι_app]
    show G.map (Sigma.ι M j.as) ≫ _ = G.map (Sigma.ι M j.as) ≫ k
    rw [← nat]
    have hc : H.map (Sigma.ι M j.as) ≫
        (isColimitOfPreserves H (coproductIsCoproduct M)).desc c = g j.as :=
      (isColimitOfPreserves H (coproductIsCoproduct M)).fac c ⟨j.as⟩
    rw [hc]
    exact hg j.as

/-- Abstract retract step: bijectivity of a natural comparison passes to retracts. -/
private theorem bij_retract_gen {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
    (H : C₁ ⥤ C₂) (G : C₁ ⥤ D) (X : C₂) (E : D) (Φ : ∀ P : C₁, (H.obj P ⟶ X) → (G.obj P ⟶ E))
    (nat : ∀ {P P' : C₁} (a : P' ⟶ P) (g : H.obj P ⟶ X), Φ P' (H.map a ≫ g) = G.map a ≫ Φ P g)
    {M P : C₁} (i : M ⟶ P) (p : P ⟶ M) (hip : i ≫ p = 𝟙 M)
    (h : Function.Bijective (Φ P)) : Function.Bijective (Φ M) := by
  constructor
  · intro g g' hg
    have := h.1 (a₁ := H.map p ≫ g) (a₂ := H.map p ≫ g') (by rw [nat, nat, hg])
    simpa [← Functor.map_comp_assoc, hip] using congrArg (fun x => H.map i ≫ x) this
  · intro k
    obtain ⟨g, hg⟩ := h.2 (G.map p ≫ k)
    refine ⟨H.map i ≫ g, ?_⟩
    rw [nat, hg, ← Category.assoc, ← G.map_comp, hip, G.map_id, Category.id_comp]

/-- `phi` is bijective for a direct summand of a finite free module. -/
private theorem phi_bijective (hT : IsTerminal T) {M : Mod R} (hM : IsFinFreeSummand M)
    (N : Mod R) (Y : C) : Function.Bijective (phi hT (M := M) (N := N) Y) := by
  obtain ⟨m, i, p, hip⟩ := hM
  have hfree : Function.Bijective
      (phi hT (M := SheafOfModules.free (R := R) (Fin m)) (N := N) Y) :=
    bij_sigma_gen (SheafOfModules.overFunctor.{0} R Y) (SheafOfModules.evaluation.{0} R (op T))
      (fun _ : Fin m => SheafOfModules.unit R) (N.over Y) (resE hT N Y)
      (fun P g => phi hT Y g) (fun a g => phi_nat hT Y a g)
      (fun _ => phi_unit_bijective hT N Y)
  exact bij_retract_gen (SheafOfModules.overFunctor.{0} R Y)
    (SheafOfModules.evaluation.{0} R (op T)) (N.over Y) (resE hT N Y)
    (fun P g => phi hT Y g) (fun a g => phi_nat hT Y a g) i p hip hfree

/-- **S4.c with restriction, injectivity.** For `M` a direct summand of a finite free module, a
morphism `M|Y ⟶ N|Y` is determined by `restrEval`. -/
theorem restrEval_injective (hT : IsTerminal T) {M : Mod R} (hM : IsFinFreeSummand M)
    (N : Mod R) (Y : C) : Function.Injective (restrEval hT (M := M) (N := N) Y) := by
  intro g g' h
  apply (phi_bijective hT hM N Y).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact congrFun h m

/-- **S4.c with restriction, surjectivity.** For `M` a direct summand of a finite free module,
every additive map `s : M(T) → N(Y)`, semilinear along `R(T) → R(Y)`, is `restrEval g` for a
morphism `g : M|Y ⟶ N|Y`. -/
theorem restrEval_surjective (hT : IsTerminal T) {M : Mod R} (hM : IsFinFreeSummand M)
    (N : Mod R) (Y : C) (s : M.val.obj (op T) → N.val.obj (op Y))
    (hadd : ∀ m m', s (m + m') = s m + s m')
    (hsmul : ∀ (r : R.obj.obj (op T)) m, s (r • m) = (R.obj.map (hT.from Y).op).hom r • s m) :
    ∃ g : M.over Y ⟶ N.over Y, restrEval hT Y g = s := by
  let k : (SheafOfModules.evaluation.{0} R (op T)).obj M ⟶ resE hT N Y :=
    ModuleCat.ofHom (X := (SheafOfModules.evaluation.{0} R (op T)).obj M) (Y := resE hT N Y)
      { toFun := s
        map_add' := hadd
        map_smul' := fun r m => hsmul r m }
  obtain ⟨g, hg⟩ := (phi_bijective hT hM N Y).2 k
  refine ⟨g, funext fun m => ?_⟩
  exact congrArg (fun q => (ModuleCat.Hom.hom q) m) hg

end Cohesive
