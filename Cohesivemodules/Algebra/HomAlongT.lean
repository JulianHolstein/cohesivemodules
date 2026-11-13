import Cohesivemodules.Algebra.HomAlongTBasic

set_option linter.style.header false

/-!
# Hom complexes along a map of (possibly curved) dgas, and A10.a (part 2 of 2)

Split from `Algebra/HomAlongT.lean` for size;
continues `Algebra/HomAlongTBasic.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory TensorProduct DirectSum
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
variable (f : DgaHom 𝒜 ℬ)
variable {f}
variable (f)
variable {f}
variable (f)

/-! ### A10.a along `f` -/

section FromComplex

variable {R : Type} [CommRing R] (W : CochainComplex (ModuleCat.{0} R) ℤ)

/-- `d ∘ f₀ ∘ ρ = 0` when `d ∘ ρ = 0`. -/
theorem d_f0_comp {ρ : R →+* 𝒜 0} (hρ : ∀ r, GCDga.d (𝒜 := 𝒜) (ρ r : A) = 0) (r : R) :
    GCDga.d (𝒜 := ℬ) ((f.f0.comp ρ r : ℬ 0) : B) = 0 := by
  rw [show ((f.f0.comp ρ r : ℬ 0) : B) = f (ρ r : A) from rfl, ← f.map_d, hρ, f.map_zero']

/-- `homRδ` is additive in the family. -/
theorem homRδ_add {ρ : R →+* ℬ 0} (hρ : ∀ r, GCDga.d (𝒜 := ℬ) (ρ r : B) = 0)
    (N : QuasiCohesive ℬ) (n : ℤ) (g g' : ∀ p, W.X p →ₛₗ[ρ] N.T) :
    homRδ W hρ N n (g + g') = homRδ W hρ N n g + homRδ W hρ N n g' := by
  funext p
  ext w
  show N.X ((g + g') p w) - n.negOnePow • (g + g') (p + 1) (dW W p w) = _
  simp only [Pi.add_apply, LinearMap.add_apply, map_add, smul_add]
  show _ = (N.X (g p w) - n.negOnePow • g (p + 1) (dW W p w)) +
    (N.X (g' p w) - n.negOnePow • g' (p + 1) (dW W p w))
  abel

/-- `homRδ ∘ homRδ = 0` on families (`𝕏_N² = c = 0`, `d_W² = 0`). -/
theorem homRδ_homRδ {ρ : R →+* ℬ 0} (hρ : ∀ r, GCDga.d (𝒜 := ℬ) (ρ r : B) = 0)
    (hc : GCDga.c (𝒜 := ℬ) = 0) (N : QuasiCohesive ℬ) (n : ℤ) (g : ∀ p, W.X p →ₛₗ[ρ] N.T) :
    homRδ W hρ N (n + 1) (homRδ W hρ N n g) = 0 := by
  funext p
  ext w
  show N.X (N.X (g p w) - n.negOnePow • g (p + 1) (dW W p w)) -
    (n + 1).negOnePow • (N.X (g (p + 1) (dW W p w)) -
      n.negOnePow • g (p + 1 + 1) (dW W (p + 1) (dW W p w))) = 0
  simp only [dW_dW, map_zero, smul_zero, sub_zero, map_sub, N.flat, hc, zero_smul,
    Units.smul_def, map_zsmul, Int.negOnePow_succ, Units.val_neg, neg_smul]
  abel

/-- **A10.a** The complex `Hom^•_R(W, N)` of families `(f_p : W^p → N)_p` (`HomR`), with
differential `homRδ`, as a complex of abelian groups. (`hc` is needed for `d² = 0`.) -/
def famComplex {ρ : R →+* ℬ 0} (hρ : ∀ r, GCDga.d (𝒜 := ℬ) (ρ r : B) = 0)
    (hc : GCDga.c (𝒜 := ℬ) = 0) (N : QuasiCohesive ℬ) : CochainComplex AddCommGrpCat.{0} ℤ :=
  CochainComplex.of (fun n => AddCommGrpCat.of (HomR ρ W N n))
    (fun n => AddCommGrpCat.ofHom
      { toFun := fun g => ⟨homRδ W hρ N n g.1, homRδ_mem W hρ N g.2⟩
        map_zero' := Subtype.ext (by
          simpa using (homRδ_add W hρ N n 0 0))
        map_add' := fun g g' => Subtype.ext (homRδ_add W hρ N n g.1 g'.1) })
    (fun n => by
      ext g p w
      exact LinearMap.congr_fun (congr_fun (homRδ_homRδ W hρ hc N n g.1) p) w)

/-- `famComplex` in degree `n` (rfl). -/
theorem famComplex_X {ρ : R →+* ℬ 0} (hρ : ∀ r, GCDga.d (𝒜 := ℬ) (ρ r : B) = 0)
    (hc : GCDga.c (𝒜 := ℬ) = 0) (N : QuasiCohesive ℬ) (n : ℤ) :
    (famComplex W hρ hc N).X n = AddCommGrpCat.of (HomR ρ W N n) := rfl

variable {ρ : R →+* 𝒜 0} (hρ : ∀ r, GCDga.d (𝒜 := 𝒜) (ρ r : A) = 0)
  (hc : GCDga.c (𝒜 := 𝒜) = 0) (hc' : GCDga.c (𝒜 := ℬ) = 0) (N : QuasiCohesive ℬ)

/-- A map along `f` out of `A ⊗_R W` is `f₀ ∘ ρ`-semilinear on the generators
`1 ⊗ (1 ⊗ w)` (`fcι_smulR` and degree-`0` semilinearity). -/
theorem along_fcι_smulR {n : ℤ} (χ : HomAlongT f (QuasiCohesive.fromComplex W hρ hc) N n)
    {p : ℤ} (r : R) (w : W.X p) :
    χ.1 (fcι ρ W (r • w)) = (f.f0.comp ρ r : ℬ 0) • χ.1 (fcι ρ W w) := by
  have h := χ.2.2 (ρ r).2 (fcι ρ W w)
  rw [mul_zero, Int.negOnePow_zero, one_smul] at h
  rw [fcι_smulR]
  refine h.trans ?_
  exact (Tot.smul0_eq ((f.f0.comp ρ) r) (χ.1 (fcι ρ W w))).symm

/-- Evaluating a map along `f` on the generators gives a family: `w ↦ χ(1 ⊗ (1 ⊗ w))` is
`f₀ ∘ ρ`-semilinear of degree `p + n`. -/
def alongEvP {n : ℤ} (χ : HomAlongT f (QuasiCohesive.fromComplex W hρ hc) N n) (p : ℤ) :
    W.X p →ₛₗ[f.f0.comp ρ] N.T where
  toFun w := χ.1 (fcι ρ W w)
  map_add' w w' :=
    (congrArg χ.1 (fcι_add (𝒜 := 𝒜) (ρ := ρ) (W := W) w w')).trans (χ.1.map_add _ _)
  map_smul' r w := along_fcι_smulR f W hρ hc N χ r w

/-- `alongEvP` lands in `HomR`. -/
theorem alongEvP_mem {n : ℤ} (χ : HomAlongT f (QuasiCohesive.fromComplex W hρ hc) N n) :
    alongEvP f W hρ hc N χ ∈ HomR (f.f0.comp ρ) W N n := by
  intro p w
  exact χ.2.1 (fcι_mem ρ W w)

/-- Evaluation on the generators commutes with the differentials:
`ev(δAl χ) = homRδ (ev χ)` (`fromComplex.X (1 ⊗ (1 ⊗ w)) = 1 ⊗ (1 ⊗ d_W w)`). -/
theorem alongEvP_δAl {n : ℤ} (χ : HomAlongT f (QuasiCohesive.fromComplex W hρ hc) N n) :
    alongEvP f W hρ hc N (n := n + 1) ⟨δAl _ N n χ.1, δAl_mem χ.2⟩ =
      homRδ W (d_f0_comp f hρ) N n (alongEvP f W hρ hc N χ) := by
  funext p
  ext w
  show N.X (χ.1 (fcι ρ W w)) - n.negOnePow • χ.1 ((fcGenData W hρ).extend (fcι ρ W w)) = _
  rw [fc_extend_fcι]
  rfl

/-- **A10.a along `f`.** Evaluation on the generators `1 ⊗ (1 ⊗ w)`:
`Hom^•_{along f}(A ⊗_R W, N) ⟶ Hom^•_R(W, N)` (families for `f₀ ∘ ρ`), a chain map. -/
def alongEv : alongComplex f (QuasiCohesive.fromComplex W hρ hc) N ⟶
    famComplex W (d_f0_comp f hρ) hc' N :=
  CochainComplex.ofHom
    (fun n => AddCommGrpCat.ofHom
      { toFun := fun χ => ⟨alongEvP f W hρ hc N χ, alongEvP_mem f W hρ hc N χ⟩
        map_zero' := Subtype.ext (funext fun _ => LinearMap.ext fun _ => rfl)
        map_add' := fun _ _ => Subtype.ext (funext fun _ => LinearMap.ext fun _ => rfl) })
    (fun n => by
      simp only [alongComplex, famComplex, CochainComplex.of_d]
      ext χ p w
      exact (LinearMap.congr_fun (congr_fun (alongEvP_δAl f W hρ hc N χ) p) w).symm)

/-- `alongEv` on an element (rfl). -/
theorem alongEv_f_apply (n : ℤ) (χ : HomAlongT f (QuasiCohesive.fromComplex W hρ hc) N n)
    (p : ℤ) (w : W.X p) :
    (((alongEv f W hρ hc hc' N).f n).hom χ).1 p w = χ.1 (fcι ρ W w) := rfl

/-- `f₀ : A⁰ → B⁰` as an `R`-linear map `RA0 ρ → RA0 (f₀ ∘ ρ)`. -/
private def fcF0 : RA0 ρ →ₗ[R] RA0 (f.f0.comp ρ) where
  toFun α := RA0.of (f.f0.comp ρ) (f.f0 (RA0.un ρ α))
  map_add' α β := congrArg (RA0.of (f.f0.comp ρ)) (map_add f.f0 (RA0.un ρ α) (RA0.un ρ β))
  map_smul' r α := by
    show RA0.of (f.f0.comp ρ) (f.f0 (ρ r * RA0.un ρ α)) =
      RA0.of (f.f0.comp ρ) ((f.f0.comp ρ) r * f.f0 (RA0.un ρ α))
    rw [map_mul]
    rfl

/-- The generator map `A⁰ ⊗_R W^p → B⁰ ⊗_R W^p`, `α ⊗ w ↦ f₀(α) ⊗ w`. -/
private def fcGenMap (p : ℤ) : FCGen ρ W p →+ FCGen (f.f0.comp ρ) W p :=
  (TensorProduct.map (fcF0 f) (LinearMap.id : W.X p →ₗ[R] W.X p)).toAddMonoidHom

/-- `fcGenMap` on pure tensors (rfl). -/
private theorem fcGenMap_tmul (p : ℤ) (α : 𝒜 0) (w : W.X p) :
    fcGenMap f W (ρ := ρ) p (FCGen.tmul ρ W α w) = FCGen.tmul (f.f0.comp ρ) W (f.f0 α) w := rfl

/-- `fcGenMap` is `f₀`-semilinear. -/
private theorem fcGenMap_smul (p : ℤ) (γ : 𝒜 0) (x : FCGen ρ W p) :
    fcGenMap f W (ρ := ρ) p (γ • x) = f.f0 γ • fcGenMap f W (ρ := ρ) p x := by
  induction x using FCGen.induction_on with
  | ht α w =>
    rw [FCGen.smul_tmul, fcGenMap_tmul, fcGenMap_tmul, FCGen.smul_tmul, map_mul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `⨁ fcGenMap` is `f₀`-semilinear. -/
private theorem map_fcGenMap_smul (γ : 𝒜 0) (e : ⨁ p, FCGen ρ W p) :
    DirectSum.map (fcGenMap f W (ρ := ρ)) (γ • e) =
      f.f0 γ • DirectSum.map (fcGenMap f W (ρ := ρ)) e := by
  ext i
  simp only [DirectSum.map_apply, DirectSum.smul_apply]
  exact fcGenMap_smul f W i γ (e i)

/-- The bi-additive map `(a, e) ↦ f(a) ⊗ (⨁ fcGenMap) e`. -/
private def fcTotAux : A →+ (⨁ p, FCGen ρ W p) →+ Tot ℬ (FCGen (f.f0.comp ρ) W) :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun e => Tot.tmul ℬ _ (f a) (DirectSum.map (fcGenMap f W (ρ := ρ)) e))
      (fun e e' => by rw [map_add, Tot.tmul_add]))
    (fun a b => AddMonoidHom.ext fun e => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, f.map_add', Tot.add_tmul])

/-- `fcTotAux` is `A⁰`-balanced. -/
private theorem fcTotAux_balanced (r : 𝒜 0) (a : A) (e : ⨁ p, FCGen ρ W p) :
    fcTotAux f W (ρ := ρ) (r • a) e = fcTotAux f W (ρ := ρ) a (r • e) := by
  show Tot.tmul ℬ _ (f (r • a)) (DirectSum.map (fcGenMap f W (ρ := ρ)) e) =
    Tot.tmul ℬ _ (f a) (DirectSum.map (fcGenMap f W (ρ := ρ)) (r • e))
  rw [map_fcGenMap_smul, Tot.tmul_smul0, GCDga.smul0_def, f.map_mul', DgaHom.coe_f0]
  exact congrArg (Tot.tmul ℬ _ · _) (GCDga.central ℬ (f.map_mem r.2) _)

/-- The map `A ⊗_{A⁰} ⨁(A⁰ ⊗_R W) → B ⊗_{B⁰} ⨁(B⁰ ⊗_R W)`, `a ⊗ e ↦ f(a) ⊗ (⨁ fcGenMap) e`. -/
private def fcTot : Tot 𝒜 (FCGen ρ W) →+ Tot ℬ (FCGen (f.f0.comp ρ) W) :=
  TensorProduct.liftAddHom (R := 𝒜 0) (fcTotAux f W (ρ := ρ)) (fcTotAux_balanced f W)

/-- `fcTot` on pure tensors (rfl). -/
private theorem fcTot_tmul (a : A) (e : ⨁ p, FCGen ρ W p) :
    fcTot f W (ρ := ρ) (Tot.tmul 𝒜 _ a e) =
      Tot.tmul ℬ _ (f a) (DirectSum.map (fcGenMap f W (ρ := ρ)) e) := rfl

/-- `fcTot` is `f`-semilinear. -/
private theorem fcTot_smul (a : A) (x : Tot 𝒜 (FCGen ρ W)) :
    fcTot f W (ρ := ρ) (a • x) = f a • fcTot f W (ρ := ρ) x := by
  induction x using Tot.induction_on with
  | ht b e => rw [Tot.smul_tmul, fcTot_tmul, fcTot_tmul, Tot.smul_tmul, f.map_mul']
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `fcTot` is `k`-linear. -/
private theorem fcTot_smul_k (r : k) (x : Tot 𝒜 (FCGen ρ W)) :
    fcTot f W (ρ := ρ) (r • x) = r • fcTot f W (ρ := ρ) x := by
  rw [← algebraMap_smul A r x, fcTot_smul, ← algebraMap_smul B r (fcTot f W (ρ := ρ) x),
    show f (algebraMap k A r) = algebraMap k B r from f.toAlgHom.commutes r]

/-- `fcTot` preserves the total degree. -/
private theorem fcTot_mem {m : ℤ} {x : Tot 𝒜 (FCGen ρ W)} (hx : x ∈ totDeg 𝒜 (FCGen ρ W) m) :
    fcTot f W (ρ := ρ) x ∈ totDeg ℬ (FCGen (f.f0.comp ρ) W) m := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, rfl, ha, rfl⟩ := hx
    change fcTot f W (ρ := ρ) (Tot.tmul 𝒜 _ a (DirectSum.of _ p e)) ∈ _
    rw [fcTot_tmul, DirectSum.map_of]
    exact tmul_mem_totDeg (f.map_mem ha) _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [fcTot_smul_k]; exact Submodule.smul_mem _ r hx

/-- `fcTot` maps the generator `1 ⊗ (1 ⊗ w)` to the generator over `B`. -/
private theorem fcTot_fcι {p : ℤ} (w : W.X p) :
    fcTot f W (ρ := ρ) (fcι ρ W w) = fcι (f.f0.comp ρ) W w := by
  rw [fcι, fcι, fcTot_tmul, f.map_one']
  congr 1
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of, DirectSum.map_of, fcGenMap_tmul, map_one]

/-- A map along `f` out of `A ⊗_R W` vanishing on the generators `1 ⊗ (1 ⊗ w)` is zero. -/
private theorem along_eq_zero' {n : ℤ} (D : Tot 𝒜 (FCGen ρ W) →ₗ[k] N.T)
    (hs : ∀ {q : ℤ} {a : A}, a ∈ 𝒜 q → ∀ x, D (a • x) = (n * q).negOnePow • f a • D x)
    (h : ∀ (p : ℤ) (w : W.X p), D (fcι ρ W w) = 0) : D = 0 := by
  have s₁ : ∀ (α : 𝒜 0) (y : Tot 𝒜 (FCGen ρ W)), D ((α : A) • y) = (f α : B) • D y := by
    intro α y
    have := hs α.2 y
    rwa [mul_zero, Int.negOnePow_zero, one_smul] at this
  have hgen : ∀ e : ⨁ p, FCGen ρ W p, D (Tot.tmul 𝒜 _ 1 e) = 0 := by
    intro e
    induction e using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero]
    | of p x =>
      induction x using FCGen.induction_on with
      | ht α w =>
        change D (Tot.tmul 𝒜 _ 1 (DirectSum.of _ p (FCGen.tmul ρ W (RA0.un ρ α) w))) = 0
        rw [fc_of_tmul, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul, s₁]
        have := h p w
        change D (Tot.tmul 𝒜 _ 1 (lof (𝒜 0) ℤ (FCGen ρ W) p (FCGen.tmul ρ W 1 w))) = 0 at this
        rw [this, smul_zero]
      | hadd x y hx hy =>
        rw [(DirectSum.of (FCGen ρ W) p).map_add, Tot.tmul_add, map_add, hx, hy, add_zero]
    | add x y hx hy => rw [Tot.tmul_add, map_add, hx, hy, add_zero]
  have hall : ∀ x : Tot 𝒜 (FCGen ρ W), D x = 0 := by
    intro x
    induction x using Tot.induction_on with
    | ht a e =>
      induction a using DirectSum.Decomposition.inductionOn 𝒜 with
      | zero => rw [Tot.zero_tmul, map_zero]
      | add x y hx hy => rw [Tot.add_tmul, map_add, hx, hy, add_zero]
      | @homogeneous q y =>
        rw [Tot.tmul_eq_smul (y : A) e, hs y.2, hgen, smul_zero, smul_zero]
    | hadd x y hx hy => rw [map_add, hx, hy, add_zero]
  exact LinearMap.ext hall

/-- **A10.a along `f`.** `alongEv` is an isomorphism: a map along `f` out of `A ⊗_R W` is
determined by its values on the generators (injectivity, as `fc_hom_ext`), and every family
extends (surjectivity: `fcExt` over `B` composed with `A ⊗_R W → B ⊗_R W`,
`a ⊗ (α ⊗ w) ↦ f(a) ⊗ (f₀(α) ⊗ w)`). -/
theorem isIso_alongEv : IsIso (alongEv f W hρ hc hc' N) := by
  have : ∀ n, IsIso ((alongEv f W hρ hc hc' N).f n) := fun n => by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun (χ χ' : HomAlongT f (QuasiCohesive.fromComplex W hρ hc) N n) hχ => ?_,
      fun g => ?_⟩
    · have key : (χ - χ' : HomAlongT f (QuasiCohesive.fromComplex W hρ hc) N n) = 0 := by
        apply Subtype.ext
        refine along_eq_zero' (f := f) (W := W) (N := N) (n := n) (χ - χ').1
          (fun {q a} ha x => (χ - χ').2.2 ha x) ?_
        intro p w
        have := congrArg (fun z => z.1 p w) hχ
        exact sub_eq_zero.2 this
      exact sub_eq_zero.1 key
    · let E := fcExt W (d_f0_comp f hρ) hc' N n g
      let Tk : Tot 𝒜 (FCGen ρ W) →ₗ[k] Tot ℬ (FCGen (f.f0.comp ρ) W) :=
        ⟨⟨fcTot f W (ρ := ρ), map_add _⟩, fcTot_smul_k f W⟩
      let χ : (QuasiCohesive.fromComplex W hρ hc).T →ₗ[k] N.T := E.1 ∘ₗ Tk
      have hmem : χ ∈ HomAlongT f (QuasiCohesive.fromComplex W hρ hc) N n := by
        refine ⟨fun {m x} hx => E.2.1 (fcTot_mem f W hx), fun {p a} ha x => ?_⟩
        show E.1 (fcTot f W (a • x)) = _
        exact (congrArg E.1 (fcTot_smul f W a x)).trans (E.2.2 (f.map_mem ha) _)
      refine ⟨⟨χ, hmem⟩, ?_⟩
      apply Subtype.ext
      funext p
      ext w
      have h1 := LinearMap.congr_fun
        (congrFun (fcResP_fcExt W (d_f0_comp f hρ) hc' N n g) p) w
      refine Eq.trans ?_ h1
      show E.1 (fcTot f W (fcι ρ W w)) = E.1 (fcι (f.f0.comp ρ) W w)
      rw [fcTot_fcι]
  exact HomologicalComplex.Hom.isIso_of_components _

end FromComplex

end Cohesive
