import Cohesivemodules.Forms.PullbackDef
import Cohesivemodules.Forms.Dbar
import Cohesivemodules.Forms.Product

set_option linter.style.header false

/-!
# F7: holomorphic pullback

Blueprint item F7 (conventions §6). For `G : E → E` holomorphic (near the points considered),
`G^*α(x) = α(G x) ∘ DG(x)` (`compContinuousLinearMap`), with the `ℂ`-linear `DG(x)` regarded as a
`ℂ`-linear map of `Ē` (`Conj.map`).
The definitions (and their basic API) are in `Cohesivemodules/Forms/PullbackDef.lean`.

* F7.a `∂̄ G^* = G^* ∂̄` (`dbar_pullback`), proof as Mathlib's `extDeriv_pullback` with `D″`: the
  second-derivative term is antilinear in the new slot, so `D″` keeps it, and alternation kills it.
* F7.b on fibres `G^*` is multiplicative (`TotFibre.pull_mul`) and respects multiplication by
  functions (`pullback_smul`).
* F7.c `(G ∘ H)^* = H^* G^*`, `id^* = id`.

## Junk values
`fderiv ℂ G x` is `0` where `G` is not complex-differentiable: every statement carries the
differentiability it needs.

## Deviations
* `G` is a function `E → E` with local hypotheses at the points considered, instead of a map
  between open subsets `V → V′`; by locality (F3.b) this is the same.
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap Conj

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {q : ℕ}

/-- F7: `DolbeaultFibre.pull` is additive. -/
private theorem DolbeaultFibre.pull_add (T : E →L[ℂ] E) (α β : DolbeaultFibre E q F) :
    DolbeaultFibre.pull T (α + β) = DolbeaultFibre.pull T α + DolbeaultFibre.pull T β := rfl

/-- F7: `DolbeaultFibre.pull` commutes with scalars. -/
private theorem DolbeaultFibre.pull_smul (T : E →L[ℂ] E) (c : ℂ) (α : DolbeaultFibre E q F) :
    DolbeaultFibre.pull T (c • α) = c • DolbeaultFibre.pull T α := rfl

/-- **F7.** The holomorphic pullback `G^*α(x) = α(G x) ∘ DG(x)`, with `DG(x) = fderiv ℂ G x`
acting on `Ē`. Junk where `G` is not complex-differentiable. -/
def pullback (G : E → E) (α : E → DolbeaultFibre E q F) : E → DolbeaultFibre E q F :=
  fun x => DolbeaultFibre.pull (fderiv ℂ G x) (α (G x))

/-- F7: formula for `pullback`. -/
theorem pullback_apply (G : E → E) (α : E → DolbeaultFibre E q F) (x : E) :
    pullback G α x = DolbeaultFibre.pull (fderiv ℂ G x) (α (G x)) := rfl

/-- F7.a helper: `Conj.map` is a continuous `ℝ`-linear map `(E →L[ℂ] E) → (Ē →L[ℂ] Ē)`. -/
private theorem exists_conjMap_clm :
    ∃ Cm : (E →L[ℂ] E) →L[ℝ] (Conj E →L[ℂ] Conj E), ∀ T, Cm T = Conj.map T := by
  refine ⟨LinearMap.mkContinuous
    { toFun := Conj.map
      map_add' := fun S T => by ext v; rfl
      map_smul' := fun r T => by
        ext v
        simp only [Conj.map_apply, _root_.smul_apply, RingHom.id_apply]
        rw [← Complex.coe_smul, ← Complex.coe_smul, toConj_smul, Complex.conj_ofReal] }
    1 (fun T => ?_), fun T => rfl⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  show ‖toConj (T (ofConj v))‖ ≤ 1 * ‖T‖ * ‖v‖
  have := T.le_opNorm (ofConj v)
  rw [one_mul]
  exact this

/-- F7.a helper: `antiPart` of `L ∘ S`, `S` complex linear, is `antiPart L ∘ Conj.map S`. -/
private theorem antiPart_comp_complex {Γ : Type} [NormedAddCommGroup Γ] [NormedSpace ℂ Γ]
    (L : E →L[ℝ] Γ) (S : E →L[ℂ] E) :
    antiPart (L ∘L S.restrictScalars ℝ) = antiPart L ∘L Conj.map S := by
  ext v
  simp only [antiPart_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', Conj.map_apply, ofConj_toConj, map_smul]

/-- F7.a helper: `alternatizeUncurryFin` of the pulled-back `D″` is the pullback. -/
private theorem alternatizeUncurryFin_pull (f : Conj E →L[ℂ] DolbeaultFibre E q F)
    (T : Conj E →L[ℂ] Conj E) :
    alternatizeUncurryFin
      (ContinuousAlternatingMap.compContinuousLinearMapCLM T ∘L f ∘L T) =
      (alternatizeUncurryFin f).compContinuousLinearMap T := by
  ext v
  simp +unfoldPartialApp [alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]

/-- F7.a helper: the antilinear part of `v ↦ Conj.map (D2 v)` is `u ↦ Conj.map (D2 (ofConj u))`. -/
private theorem antiPart_conjMap_apply (Cm : (E →L[ℂ] E) →L[ℝ] (Conj E →L[ℂ] Conj E))
    (hCm : ∀ T, Cm T = Conj.map T) (D2 : E →L[ℂ] E →L[ℂ] E) (u w : Conj E) :
    antiPart (Cm ∘L D2.restrictScalars ℝ) u w = toConj (D2 (ofConj u) (ofConj w)) := by
  have h1 : Cm (D2 (Complex.I • ofConj u)) = (-Complex.I) • Cm (D2 (ofConj u)) := by
    rw [map_smul, hCm, hCm]
    ext v
    simp only [Conj.map_apply, _root_.smul_apply]
    rw [smul_def]
    simp only [ofConj_toConj, map_neg, Complex.conj_I, neg_neg]
  simp only [antiPart_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', _root_.add_apply, _root_.smul_apply, h1]
  rw [hCm]
  simp only [Conj.map_apply]
  rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul, ← two_smul ℂ, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

/-- F7.a helper: the second-derivative term is killed by alternation (symmetry of `D²G`). -/
private theorem alt_second_term (Cm : (E →L[ℂ] E) →L[ℝ] (Conj E →L[ℂ] Conj E))
    (hCm : ∀ T, Cm T = Conj.map T) (a : DolbeaultFibre E q F) (T : Conj E →L[ℂ] Conj E)
    {D2 : E →L[ℂ] E →L[ℂ] E} (hs : ∀ u w, D2 u w = D2 w u) :
    alternatizeUncurryFin (antiPart (((a.fderivCompContinuousLinearMap T).restrictScalars ℝ) ∘L
      (Cm ∘L D2.restrictScalars ℝ))) = 0 := by
  rw [antiPart_comp]
  exact alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero a T (fun u w => by
    rw [antiPart_conjMap_apply Cm hCm, antiPart_conjMap_apply Cm hCm, hs])

/-- F7.a helper: the real derivative of `y ↦ G^*α(y)`, as a sum of two terms. -/
private theorem fderiv_pullback_eq (Cm : (E →L[ℂ] E) →L[ℝ] (Conj E →L[ℂ] Conj E))
    (hCm : ∀ T, Cm T = Conj.map T) {α : E → DolbeaultFibre E q F} {G : E → E} {x : E}
    (hα : DifferentiableAt ℝ α (G x)) (hG : ContDiffAt ℂ 2 G x) :
    fderiv ℝ (pullback G α) x =
      (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (Conj.map (fderiv ℂ G x))).restrictScalars ℝ
        ∘L (fderiv ℝ α (G x) ∘L (fderiv ℂ G x).restrictScalars ℝ) +
      ((α (G x)).fderivCompContinuousLinearMap (Conj.map (fderiv ℂ G x))).restrictScalars ℝ
        ∘L (Cm ∘L (fderiv ℂ (fderiv ℂ G) x).restrictScalars ℝ) := by
  have hGd : DifferentiableAt ℂ G x := hG.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℂ (fderiv ℂ G) x :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (𝕜 := ℝ) (fun y => α (G y))
      (fderiv ℝ α (G x) ∘L (fderiv ℂ G x).restrictScalars ℝ) x :=
    hα.hasFDerivAt.comp x (hGd.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (𝕜 := ℝ) (fun y => Cm (fderiv ℂ G y))
      (Cm ∘L (fderiv ℂ (fderiv ℂ G) x).restrictScalars ℝ) x :=
    Cm.hasFDerivAt.comp x (hD.hasFDerivAt.restrictScalars ℝ)
  have h3 := (ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap
      (α (G x), Cm (fderiv ℂ G x))).hasFDerivAt.restrictScalars ℝ
  have h4 := h3.comp x (h1.prodMk h2)
  have h5 : pullback G α = fun y => (fun fg : DolbeaultFibre E q F × (Conj E →L[ℂ] Conj E) =>
      fg.1.compContinuousLinearMap fg.2) (α (G y), Cm (fderiv ℂ G y)) := by
    funext y
    simp only [pullback_apply, DolbeaultFibre.pull, hCm]
  rw [h5]
  refine Eq.trans h4.fderiv ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [hCm]
  rfl

/-- **F7.a.** `∂̄` commutes with holomorphic pullback: `∂̄(G^*α)(x) = G^*(∂̄α)(x)`, for `α`
differentiable at `G x` and `G` complex `C²` at `x`. Proof as Mathlib's `extDeriv_pullback`. -/
theorem dbar_pullback {α : E → DolbeaultFibre E q F} {G : E → E} {x : E}
    (hα : DifferentiableAt ℝ α (G x)) (hG : ContDiffAt ℂ 2 G x) :
    dbar (pullback G α) x = pullback G (dbar α) x := by
  obtain ⟨Cm, hCm⟩ := exists_conjMap_clm (E := E)
  have hs : IsSymmSndFDerivAt ℂ G x :=
    hG.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact le_rfl)
  rw [dbar, dbarPart, fderiv_pullback_eq Cm hCm hα hG, antiPart_add, alternatizeUncurryFin_add,
    antiPart_comp, antiPart_comp_complex, alt_second_term Cm hCm _ _ hs, add_zero]
  exact alternatizeUncurryFin_pull _ _

/-- **F7.b.** Pullback respects multiplication by functions: `G^*(f α) = (f ∘ G) G^*α`. -/
theorem pullback_smul (G : E → E) (f : E → ℂ) (α : E → DolbeaultFibre E q F) (x : E) :
    pullback G (fun y => f y • α y) x = f (G x) • pullback G α x := by
  ext v
  simp only [pullback_apply, DolbeaultFibre.pull_apply, ContinuousAlternatingMap.smul_apply]

/-- **F7.c.** `(G ∘ H)^* = H^* G^*` at points where `H` is complex-differentiable at `x` and `G`
at `H x` (chain rule). -/
theorem pullback_comp {G H : E → E} {α : E → DolbeaultFibre E q F} {x : E}
    (hG : DifferentiableAt ℂ G (H x)) (hH : DifferentiableAt ℂ H x) :
    pullback (G ∘ H) α x = pullback H (pullback G α) x := by
  ext v
  simp only [pullback_apply, DolbeaultFibre.pull_apply, Function.comp_apply]
  rw [fderiv_comp x hG hH]
  rfl

/-- **F7.c.** `id^* = id`. -/
theorem pullback_id (α : E → DolbeaultFibre E q F) : pullback id α = α := by
  funext x
  ext v
  simp only [pullback_apply, DolbeaultFibre.pull_apply, id_eq, fderiv_id]
  rfl

/-! ## F7.b: on fibres, pullback is an algebra map -/

variable [FiniteDimensional ℂ E]

/-- F7.b helper: `Φ_q` intertwines `DolbeaultFibre.pull T` with the exterior power of the dual of
`Conj.map T`.
-/
private theorem pull_extToFibre (T : E →L[ℂ] E) (q : ℕ) (x : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    DolbeaultFibre.pull T (extToFibre E q x) =
      extToFibre E q (exteriorPower.map q (Conj.map T : Conj E →ₗ[ℂ] Conj E).dualMap x) := by
  have hx : x ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ q)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  refine Submodule.span_induction
    (p := fun x _ => DolbeaultFibre.pull T (extToFibre E q x) =
      extToFibre E q (exteriorPower.map q (Conj.map T : Conj E →ₗ[ℂ] Conj E).dualMap x))
    ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨φ, rfl⟩
    ext v
    rw [DolbeaultFibre.pull_apply, extToFibre_ιMulti, exteriorPower.map_apply_ιMulti,
      extToFibre_ιMulti]
    rfl
  · rw [_root_.map_zero, _root_.map_zero, _root_.map_zero]
    rfl
  · intro x y _ _ hx hy
    rw [map_add, DolbeaultFibre.pull_add, hx, hy, map_add, map_add]
  · intro c x _ hx
    rw [map_smul, DolbeaultFibre.pull_smul, hx, map_smul, map_smul]

namespace TotFibre

/-- F7.b: `pull` on a homogeneous element. -/
theorem pull_ofDeg (T : E →L[ℂ] E) {p : ℕ} (α : DolbeaultFibre E p ℂ) :
    pull T (ofDeg p α : TotFibre E) = ofDeg p (DolbeaultFibre.pull T α) := by
  funext i
  show DolbeaultFibre.pull T (if h : p = (i : ℕ) then DolbeaultFibre.cast h α else 0) =
    (if h : p = (i : ℕ) then DolbeaultFibre.cast h (DolbeaultFibre.pull T α) else 0)
  by_cases h : p = (i : ℕ)
  · subst h
    simp only [DolbeaultFibre.cast_rfl, dite_true]
  · simp only [h, dite_false]
    rfl

/-- F7.b helper: `pull T` is `Φ_tot` of the algebra map induced by the dual of `Conj.map T`. -/
private theorem pull_extEquivTotFibre (T : E →L[ℂ] E)
    (a : ExteriorAlgebra ℂ (Module.Dual ℂ (Conj E))) :
    pull T (extEquivTotFibre E a) =
      extEquivTotFibre E (ExteriorAlgebra.map (Conj.map T : Conj E →ₗ[ℂ] Conj E).dualMap a) := by
  induction a using DirectSum.Decomposition.inductionOn
    (fun q => ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) with
  | zero => simp only [_root_.map_zero]
  | homogeneous m =>
    rename_i q
    rw [extEquivTotFibre_of_mem, pull_ofDeg, pull_extToFibre, ← exteriorPower.coe_map,
      extEquivTotFibre_of_mem]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **F7.b.** On fibres, pullback is multiplicative: it is the algebra map induced by the dual
of `T` on the exterior algebra (`ExteriorAlgebra.map`). -/
theorem pull_mul (T : E →L[ℂ] E) (x y : TotFibre E) : pull T (x * y) = pull T x * pull T y := by
  obtain ⟨a, rfl⟩ := (extEquivTotFibre E).surjective x
  obtain ⟨b, rfl⟩ := (extEquivTotFibre E).surjective y
  rw [← extEquivTotFibre_mul, pull_extEquivTotFibre, pull_extEquivTotFibre,
    pull_extEquivTotFibre, map_mul, extEquivTotFibre_mul]

/-- **F7.b.** On fibres, pullback preserves the unit. -/
theorem pull_one (T : E →L[ℂ] E) : pull T (1 : TotFibre E) = 1 := by
  have h : (1 : TotFibre E) = extEquivTotFibre E 1 := rfl
  rw [h, pull_extEquivTotFibre, map_one]

end TotFibre

end Cohesive
