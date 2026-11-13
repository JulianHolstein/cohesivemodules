import Cohesivemodules.Algebra.TotalQuasiIsoFil

set_option linter.style.header false

/-!
# A12: the total quasi-isomorphism (part 2 of 3)

Split from `Algebra/TotalQuasiIso.lean` for size;
continues `Algebra/TotalQuasiIsoFil.lean`.
-/

namespace Cohesive
open CategoryTheory DirectSum TensorProduct
noncomputable section
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
variable {M₁ M₂ : QuasiCohesive 𝒜} {φ : M₁.T →ₗ[k] M₂.T}

/-! ## The graded pieces `gr^b` -/

variable (𝒜) in
/-- A12: the structure map `k → A⁰`, `r ↦ r·1`. -/
def kToA0 : k →+* 𝒜 0 where
  toFun r := ⟨algebraMap k A r, SetLike.algebraMap_mem_graded 𝒜 r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable (𝒜) in
/-- A12: restriction of scalars from `A⁰` to `k`. -/
abbrev resK : ModuleCat.{0} (𝒜 0) ⥤ ModuleCat.{0} k := ModuleCat.restrictScalars (kToA0 𝒜)

namespace QuasiCohesive

variable (M : QuasiCohesive 𝒜)

/-- A12: `gr^b`: the complex `A^b ⊗_{A⁰} (Q, 𝕏⁰)` (`tensC`), restricted to `k` and shifted by
`-b`, so that degree `m` is `A^b ⊗ Q^{m-b}` and the differential is `(-1)^b (1 ⊗ 𝕏⁰)`. -/
def grComplex (b : ℤ) : CochainComplex (ModuleCat.{0} k) ℤ :=
  (shiftFunctor (CochainComplex (ModuleCat.{0} k) ℤ) (-b)).obj
    (((resK 𝒜).mapHomologicalComplex _).obj (tensC M.complex0 b))

/-- A12: the extraction `extr` of the form-degree-`b` part as a `k`-linear map. -/
theorem extr_smul_k (b j : ℤ) (r : k) (x : Tot 𝒜 (Gens M.complex0)) :
    extr M.complex0 b j (r • x) = kToA0 𝒜 r • extr M.complex0 b j x := by
  rw [Tot.smul_k_eq_smul0, map_smul]
  rfl

/-- A12: the projection `F^b → gr^b` in degree `m`: `x ↦` its component in `A^b ⊗ Q^{m-b}`. -/
def grProjL (b m : ℤ) : M.filDeg b m →ₗ[k] (M.grComplex b).X m where
  toFun x := extr M.complex0 b (m + -b) (x : M.T)
  map_add' x y := map_add (extr M.complex0 b (m + -b)) (x : M.T) y
  map_smul' r x := M.extr_smul_k b (m + -b) r (x : M.T)

/-- A12 helper: `extr_b ∘ π_b = extr_b`. -/
private theorem extr_projF (Xc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ) (b j : ℤ)
    (y : Tot 𝒜 (Gens Xc)) : extr Xc b j (Tot.projF 𝒜 (Gens Xc) b y) = extr Xc b j y := by
  induction y using Tot.induction_on with
  | ht a e =>
    rw [Tot.projF_tmul, extr_tmul, extr_tmul]
    have : projPiece 𝒜 b (GCDga.proj 𝒜 b a) = projPiece 𝒜 b a := by
      apply Subtype.ext
      show GCDga.proj 𝒜 b (GCDga.proj 𝒜 b a) = GCDga.proj 𝒜 b a
      rw [GCDga.proj_of_mem 𝒜 (GCDga.proj_mem 𝒜 b a)]
      simp only [↓reduceIte]
    rw [this]
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- A12 helper: `extr_b` kills `F^{b+1}`. -/
private theorem extr_eq_zero_of_mem (Xc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ) (b j : ℤ)
    {y : Tot 𝒜 (Gens Xc)} (hy : y ∈ filTot 𝒜 (Gens Xc) (b + 1)) : extr Xc b j y = 0 := by
  rw [← extr_projF, projF_eq_zero_of_mem hy, map_zero]

/-- A12 helper: on `F^b`, `extr_b ∘ 𝕏 = (-1)^b (1 ⊗ 𝕏⁰) ∘ extr_b`. -/
private theorem extr_X_of_mem (M : QuasiCohesive 𝒜) (b j₀ j₁ : ℤ) (h : j₀ + 1 = j₁) {x : M.T}
    (hx : x ∈ filTot 𝒜 M.Q b) :
    extr M.complex0 b j₁ (M.X x) =
      b.negOnePow • ((tensC M.complex0 b).d j₀ j₁).hom (extr M.complex0 b j₀ x) := by
  subst h
  have h1 : M.X x - hatGen 1 M.X0 x ∈ filTot 𝒜 M.Q (b + 1) := X_lead M b x hx
  have h2 : extr M.complex0 b (j₀ + 1) (M.X x) = extr M.complex0 b (j₀ + 1) (hatGen 1 M.X0 x) :=
    sub_eq_zero.1 ((map_sub (extr M.complex0 b (j₀ + 1)) _ _).symm.trans
      (extr_eq_zero_of_mem M.complex0 b (j₀ + 1) h1))
  rw [h2]
  have := extr_hatGen_d (Xc := M.complex0) b j₀ x
  rw [dGen_complex0] at this
  exact this

/-- A12: `grProjL` commutes with the differentials. -/
theorem grProj_comm (hc : GCDga.c (𝒜 := 𝒜) = 0) (b i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    ModuleCat.ofHom (M.grProjL b i) ≫ (M.grComplex b).d i j =
      (M.filComplex hc b).d i j ≫ ModuleCat.ofHom (M.grProjL b j) := by
  obtain rfl : j = i + 1 := hij.symm
  ext x
  have h1 := extr_X_of_mem M b (i + -b) (i + 1 + -b) (by omega) x.2.2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, QuasiCohesive.filComplex,
    CochainComplex.of_d, ModuleCat.hom_ofHom]
  change (((M.grComplex b).d i (i + 1)).hom (extr M.complex0 b (i + -b) (x : M.T))) =
    extr M.complex0 b (i + 1 + -b) (M.X x)
  rw [h1]
  simp only [grComplex, CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg]
  rfl

/-- A12: the projection of complexes `F^b → gr^b`. -/
def grProj (hc : GCDga.c (𝒜 := 𝒜) = 0) (b : ℤ) : M.filComplex hc b ⟶ M.grComplex b where
  f m := (ModuleCat.ofHom (M.grProjL b m) :
    ModuleCat.of k (M.filDeg b m) ⟶ ModuleCat.of k ((M.grComplex b).X m))
  comm' i j hij := M.grProj_comm hc b i j hij

/-- A12: `F^{b+1} → F^b → gr^b` composes to zero. -/
theorem filIncl_grProj (hc : GCDga.c (𝒜 := 𝒜) = 0) (b : ℤ) :
    M.filIncl hc b ≫ M.grProj hc b = 0 := by
  ext m x
  exact extr_eq_zero_of_mem M.complex0 b (m + -b) x.2.2

/-- A12: the short complex `F^{b+1} → F^b → gr^b`. -/
def filSC (hc : GCDga.c (𝒜 := 𝒜) = 0) (b : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{0} k) ℤ) :=
  ShortComplex.mk (M.filIncl hc b) (M.grProj hc b) (M.filIncl_grProj hc b)

/-- A12: `0 → F^{b+1} → F^b → gr^b → 0` is short exact (degreewise: `F^{b+1}` is the kernel of
the extraction of the form-degree-`b` part, which is onto `A^b ⊗ Q^{m-b}`). -/
theorem filSC_shortExact (hc : GCDga.c (𝒜 := 𝒜) = 0) (b : ℤ) : (M.filSC hc b).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun m => ?_
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    intro (y : M.filDeg b m)
    constructor
    · intro hy
      have hy' : extr M.complex0 b (m + -b) (y : M.T) = 0 := hy
      have hz := y.2.1
      have h1 : Tot.projF 𝒜 M.Q b (y : M.T) = 0 := by
        have e := pieceTot_extr (Xc := M.complex0) (b := b) (j := m + -b) (by omega)
          (y := (y.1 : Tot 𝒜 (Gens M.complex0))) hz
        have e2 : extr M.complex0 b (m + -b)
            (Tot.projF 𝒜 (Gens M.complex0) b (y.1 : Tot 𝒜 (Gens M.complex0))) = 0 :=
          (extr_projF M.complex0 b (m + -b) _).trans hy'
        exact e.symm.trans ((congrArg (pieceTot M.complex0 b (m + -b)) e2).trans (map_zero _))
      have h2 := sub_projF_mem_filTot (𝒜 := 𝒜) y.2.2
      rw [h1, sub_zero] at h2
      exact ⟨⟨(y : M.T), hz, h2⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact extr_eq_zero_of_mem M.complex0 b (m + -b) x.2.2
  · rw [ModuleCat.mono_iff_injective]
    intro (x : M.filDeg (b + 1) m) (y : M.filDeg (b + 1) m) h
    have h' : M.filInclD b m x = M.filInclD b m y := h
    exact Subtype.ext (congrArg (fun z : M.filDeg b m => (z : M.T)) h')
  · rw [ModuleCat.epi_iff_surjective]
    intro t
    let t' : GCDga.piece 𝒜 b ⊗[𝒜 0] M.complex0.X (m + -b) := t
    have hm : pieceTot M.complex0 b (m + -b) t' ∈ totDeg 𝒜 M.Q m := by
      have := pieceTot_mem (Xc := M.complex0) b (m + -b) t'
      rwa [show b + (m + -b) = m by omega] at this
    have hf : pieceTot M.complex0 b (m + -b) t' ∈ filTot 𝒜 M.Q b := by
      have h3 : Tot.projF 𝒜 (Gens M.complex0) b (pieceTot M.complex0 b (m + -b) t') ∈
          filTot 𝒜 (Gens M.complex0) b := projF_mem_filTot b _
      rw [projF_pieceTot] at h3
      exact h3
    exact ⟨⟨_, hm, hf⟩, extr_pieceTot b (m + -b) t'⟩

end QuasiCohesive

/-- A12: the map `gr^b M₁ → gr^b M₂` induced by a chain map `f₀ : (Q₁, 𝕏₁⁰) → (Q₂, 𝕏₂⁰)`. -/
def grMap (b : ℤ) (f₀ : M₁.complex0 ⟶ M₂.complex0) : M₁.grComplex b ⟶ M₂.grComplex b :=
  (shiftFunctor (CochainComplex (ModuleCat.{0} k) ℤ) (-b)).map
    (((resK 𝒜).mapHomologicalComplex _).map (tensMap b f₀))

/-- A12: `gr^b f₀` is a quasi-isomorphism if `f₀` is one and `A^b` is flat over `A⁰`. -/
theorem grMap_quasiIso (b : ℤ) [Module.Flat (𝒜 0) (GCDga.piece 𝒜 b)]
    (f₀ : M₁.complex0 ⟶ M₂.complex0) [QuasiIso f₀] : QuasiIso (grMap b f₀) := by
  refine (CochainComplex.quasiIso_shift_iff _ (-b)).2 ?_
  have : QuasiIso (tensMap b f₀) := inferInstance
  infer_instance

/-- A12: the hypothesis "the `(0,0)`-component of `φ` is `f₀`": `ε(φ(1 ⊗ e)) = f₀ e` for
`e ∈ Q₁^p`. -/
def IsLead0 (φ : M₁.T →ₗ[k] M₂.T) (f₀ : M₁.complex0 ⟶ M₂.complex0) : Prop :=
  ∀ p (e : M₁.Q p), Tot.eps 𝒜 M₂.Q (φ (Tot.tmul 𝒜 M₁.Q 1 (lof (𝒜 0) ℤ M₁.Q p e))) =
    lof (𝒜 0) ℤ M₂.Q p ((f₀.f p).hom e)

/-- A12 helper: `φ - ĝ` raises the form-degree filtration by one, when `φ` has leading
component `f₀`. -/
private theorem sub_hatGen_mem_filTot' {Xc Yc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ}
    {ψ : Tot 𝒜 (Gens Xc) →ₗ[k] Tot 𝒜 (Gens Yc)} (hψ : ψ ∈ HomT 𝒜 (Gens Xc) (Gens Yc) 0)
    (f₀ : Xc ⟶ Yc)
    (h₀ : ∀ p (e : Xc.X p), Tot.eps 𝒜 (Gens Yc)
      (ψ (Tot.tmul 𝒜 (Gens Xc) 1 (lof (𝒜 0) ℤ (Gens Xc) p e))) =
        lof (𝒜 0) ℤ (Gens Yc) p ((f₀.f p).hom e))
    {b : ℤ} {x : Tot 𝒜 (Gens Xc)} (hx : x ∈ filTot 𝒜 (Gens Xc) b) :
    ψ x - hatGen 0 (genMap f₀) x ∈ filTot 𝒜 (Gens Yc) (b + 1) := by
  have heps : ∀ e : ⨁ p, Gens Xc p,
      Tot.eps 𝒜 (Gens Yc) (ψ (Tot.tmul 𝒜 (Gens Xc) 1 e)) = genMap f₀ e := by
    intro e
    induction e using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero, map_zero, map_zero]
    | of p e' =>
      show Tot.eps 𝒜 (Gens Yc) (ψ (Tot.tmul 𝒜 (Gens Xc) 1 (lof (𝒜 0) ℤ (Gens Xc) p e'))) =
        genMap f₀ (lof (𝒜 0) ℤ (Gens Xc) p e')
      rw [genMap_lof]
      exact h₀ p e'
    | add x y hx hy => rw [Tot.tmul_add, map_add, map_add, map_add, hx, hy]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, a, e, hbq, ha, rfl⟩ := hx
    rw [homT_tmul hψ, GCDga.twist_zero, hatGen_tmul,
      GCDga.twist_zero, Tot.tmul_eq_smul a (genMap f₀ e), ← smul_sub]
    have h1 : ψ (Tot.tmul 𝒜 (Gens Xc) 1 e) - Tot.tmul 𝒜 (Gens Yc) 1 (genMap f₀ e) ∈
        filTot 𝒜 (Gens Yc) 1 := by
      rw [← heps e]
      exact sub_tmul_eps_mem _
    exact filTot_anti (by omega) (smul_mem_filTot ha h1)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, add_sub_add_comm]
    exact add_mem hx hy
  | smul r x _ hx =>
    rw [map_smul, map_smul, ← smul_sub]
    exact Submodule.smul_mem _ r hx

/-- A12: the square `F^b → gr^b` commutes with `φ` and `gr^b f₀`. -/
theorem grProj_grMap (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂)
    (f₀ : M₁.complex0 ⟶ M₂.complex0) (h₀ : IsLead0 φ f₀) (b : ℤ) :
    filMap hc hφ b ≫ M₂.grProj hc b = M₁.grProj hc b ≫ grMap b f₀ := by
  refine HomologicalComplex.hom_ext _ _ fun m => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : M₁.filDeg b m) => ?_)
  have h1 := sub_hatGen_mem_filTot' (Xc := M₁.complex0) (Yc := M₂.complex0) (ψ := φ)
    hφ.1 f₀ (fun p e => h₀ p e) (x := (x : M₁.T)) x.2.2
  have h2 : extr M₂.complex0 b (m + -b) (φ x) =
      extr M₂.complex0 b (m + -b) (hatGen 0 (genMap f₀) (x : M₁.T)) :=
    sub_eq_zero.1 ((map_sub (extr M₂.complex0 b (m + -b)) _ _).symm.trans
      (QuasiCohesive.extr_eq_zero_of_mem M₂.complex0 b (m + -b) h1))
  exact h2.trans (extr_hatGen_map f₀ b (m + -b) _)

/-- A12: the inclusions `F^{b+1} → F^b` commute with `φ`. -/
theorem filIncl_filMap (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) (b : ℤ) :
    filMap hc hφ (b + 1) ≫ M₂.filIncl hc b = M₁.filIncl hc b ≫ filMap hc hφ b := by
  ext m x
  rfl

/-- A12: the map of short exact sequences `(F^{b+1} → F^b → gr^b)` induced by `φ`. -/
def filSCMap (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂)
    (f₀ : M₁.complex0 ⟶ M₂.complex0) (h₀ : IsLead0 φ f₀) (b : ℤ) :
    M₁.filSC hc b ⟶ M₂.filSC hc b where
  τ₁ := filMap hc hφ (b + 1)
  τ₂ := filMap hc hφ b
  τ₃ := grMap b f₀
  comm₁₂ := filIncl_filMap hc hφ b
  comm₂₃ := grProj_grMap hc hφ f₀ h₀ b

/-- A12 helper: for `b > N` every term of `F^b` is zero. -/
private theorem filComplex_isZero (M : QuasiCohesive 𝒜) (hc : GCDga.c (𝒜 := 𝒜) = 0) {b : ℤ}
    (hb : (GCDga.N 𝒜 : ℤ) < b) (i : ℤ) : Limits.IsZero ((M.filComplex hc b).X i) := by
  have : Subsingleton (M.filDeg b i) := by
    rw [M.filDeg_eq_bot hb i]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of k (M.filDeg b i))

/-- A12: `F^b → F^b` is a quasi-isomorphism for `b > N` (both sides are zero). -/
theorem filMap_quasiIso_of_gt (hc : GCDga.c (𝒜 := 𝒜) = 0) (hφ : φ ∈ Z0 M₁ M₂) {b : ℤ}
    (hb : (GCDga.N 𝒜 : ℤ) < b) : QuasiIso (filMap hc hφ b) := by
  rw [quasiIso_iff]
  intro i
  have hK : (M₁.filComplex hc b).ExactAt i :=
    HomologicalComplex.ExactAt.of_isZero (filComplex_isZero M₁ hc hb i)
  have hL : (M₂.filComplex hc b).ExactAt i :=
    HomologicalComplex.ExactAt.of_isZero (filComplex_isZero M₂ hc hb i)
  exact (quasiIsoAt_iff_exactAt _ i hK).2 hL

end
end Cohesive
