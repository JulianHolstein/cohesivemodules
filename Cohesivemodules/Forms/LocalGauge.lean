import Cohesivemodules.Forms.ChartTransport
import Cohesivemodules.Forms.GaugeMatrix
import Cohesivemodules.Forms.LocalFree
import Cohesivemodules.Algebra.FrameIso
import Cohesivemodules.Hypotheses

set_option linter.style.header false

/-!
# Z5.i: the local gauge lemma (H2)

Blueprint item Z5.i, E.3–E.4 and F (`blueprint/blueprint-ll.md` §4 E–F; §11 v1.15).
* `exists_iso_of_gauge` (E.3–E.4): on an open `U ∋ x` inside the chart source, let `N` be cohesive
  over `𝒜_X(U)` with a graded frame, `𝒜 = frameOp` its frame model (Z5.h) and `g` a gauge such
  that `B = g·𝒜` (`gaugeOp`) is flat, has `aᵢ = 0` and is holomorphic on `frameDom U x`. Then
  `N ≅ 𝒜_X(U) ⊗_{O(U)} W` in `Ho(P)` with `W = matComplex` of the holomorphic matrix of `B`.
  Proof: the matrix of `B` has form degree `0` (B.7) and is holomorphic, hence `ρ(f)` for
  `f` over `O(U)` (`exists_hol_of_chartExpr`); the matrices of `g` and `g⁻¹` are chart
  expressions of forms `G`, `H` (`exists_form_of_chartExpr`); the operator identity
  `g𝒜 = Bg + Σₖ εₖ∂ₖg` gives the gauge identity of `exists_iso_fromComplex_of_frame` through
  `chartExpr_d`, `chartExpr_sigma` and `eq_of_chartExpr_eq_frameDom`.
* `localGaugeLemma` (F): H2 holds on every complex manifold. Local freeness (Z5.g) on `U′`, a
  frame (`exists_gradedFrame_bcGen`), the frame model (Z5.h), the gauge induction (Z5.f) on
  `W₀ ⊆ frameDom U′ x`, then `exists_iso_of_gauge` on `U″ = chartOpen x W₀` with the restricted
  frame (`exists_frame_baseChange`, `frameOp_baseChange`) and `bcCompIso`.

The statement of `localGaugeLemma` is exactly the frozen `LocalGaugeLemma E X` (`Hypotheses.lean`).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold Opposite CategoryTheory
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X] {r : ℕ}

/-! ## Fibre-level matrix identities -/

/-- Helper: `σ` fixes elements of form degree `0`. -/
private theorem sgnTot_of_deg0 {t : TotFibre E}
    (h : ∀ q : Fin (Module.finrank ℂ E + 1), (q : ℕ) ≠ 0 → t q = 0) : sgnTot E t = t := by
  funext q
  show ((-1 : ℂ) ^ (q : ℕ)) • t q = t q
  by_cases hq : (q : ℕ) = 0
  · have h1 : ((-1 : ℂ) ^ (q : ℕ)) = 1 := by rw [hq]; exact pow_zero _
    rw [h1, one_smul]
  · rw [h q hq, smul_zero]

/-- Helper: `σ 1 = 1`. -/
private theorem sgnTot_one' : sgnTot E (1 : TotFibre E) = 1 :=
  sgnTot_of_deg0 fun q hq => by
    rw [TotFibre.one_eq]
    exact ofDeg_apply_ne _ q (by omega)

/-- Helper: the matrix of `matOp Ω` is `Ω`. -/
private theorem opMat_matOp (Ω : Fin r → Fin r → TotFibre E) (l j : Fin r) :
    opMat (matOp Ω) l j = Ω l j := by
  show matOp Ω (Pi.single j 1) l = Ω l j
  rw [matOp_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, sgnTot_one', one_mul]
  · intro i _ hij
    rw [Pi.single_eq_of_ne hij, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Helper: an odd operator `T` applied to a vector, in terms of its matrix. -/
private theorem odd_apply {T : FibOp E r} (h : ∀ j, epsOp j * T = -(T * epsOp j)) (t : Fib E r)
    (i : Fin r) : T t i = ∑ l, sgnTot E (t l) * opMat T i l := by
  conv_lhs => rw [eq_matOp_of_odd h]
  rw [matOp_apply]

/-- Helper: for an odd `B` with matrix of form degree `0` and `B² = 0`, the matrix squares to
zero (in the reversed order, which is the one that appears when applying `B` twice). -/
private theorem opMat_sq_of_odd {T : FibOp E r} (hodd : ∀ j, epsOp j * T = -(T * epsOp j))
    (h0 : ∀ i k (q : Fin (Module.finrank ℂ E + 1)), (q : ℕ) ≠ 0 → opMat T i k q = 0)
    (hsq : T * T = 0) (i k : Fin r) : ∑ l, opMat T l k * opMat T i l = 0 := by
  have h1 : (T * T) (Pi.single k 1) i = 0 := by rw [hsq]; rfl
  rw [mul_apply_eq_comp, odd_apply hodd] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show T (Pi.single k 1) l = opMat T l k from rfl, sgnTot_of_deg0 (h0 l k)]

/-- Helper: `B g = g 𝒜 − Σₖ εₖ ∂ₖ g` at `z` when `B = g·𝒜` there. -/
private theorem gauge_op_identity {deg : Fin r → ℤ} {g 𝒜 : E → FibOp E r} {B : FibOp E r} {z : E}
    (hg : IsGauge deg g) (hB : gaugeOp g 𝒜 z = B) :
    g z * 𝒜 z = B * g z + ∑ k, epsOp k * pdbar (Module.finBasis ℂ E k) g z := by
  have h1 := Ring.inverse_mul_cancel _ (hg.unit z)
  rw [← hB]
  unfold gaugeOp
  rw [sub_mul, mul_assoc (g z * 𝒜 z), mul_assoc (∑ k, epsOp k * pdbar (Module.finBasis ℂ E k) g z),
    h1, mul_one, mul_one]
  abel

/-- Helper: the gauge identity on matrix entries: `(g𝒜)ᵢⱼ = (Bg)ᵢⱼ + ∂̄gᵢⱼ`. -/
private theorem gauge_entries {deg : Fin r → ℤ} {g 𝒜 : E → FibOp E r} {B : FibOp E r} {z : E}
    (hg : IsGauge deg g) (hB : gaugeOp g 𝒜 z = B) (hodd : ∀ j, epsOp j * B = -(B * epsOp j))
    (i j : Fin r) :
    ∑ l, opMat (𝒜 z) l j * opMat (g z) i l =
      ∑ k, sgnTot E (opMat (g z) k j) * opMat B i k +
        dbarTot E (fun w => opMat (g w) i j) z := by
  have hd : DifferentiableAt ℝ g z := (hg.smooth.differentiable (by simp)) z
  have h1 := congrArg (fun T : FibOp E r => opMat T i j) (gauge_op_identity hg hB)
  rw [opMat_mul_of_comm (hg.comm z)] at h1
  rw [h1, dbarTot_opMat hd]
  exact congrArg₂ (· + ·) (odd_apply hodd (g z (Pi.single j 1)) i) rfl

/-! ## Forms from matrices on the frame domain -/

/-- Helper: the matrix of a degree-`1` superconnection with all `aᵢ = 0` vanishes off the
degrees `deg k = deg i + 1`. -/
private theorem opMat_eq_zero_of_ne {deg : Fin r → ℤ} {B : E → FibOp E r} {z : E}
    (hdeg : IsOfTotDeg deg 1 (B z)) (ha : ∀ i, aCoef i B z = 0) {k i : Fin r}
    (h : deg k ≠ deg i + 1) : opMat (B z) k i = 0 := by
  funext q
  by_cases hq : (q : ℕ) = 0
  · exact opMat_hasDeg hdeg k i q (by omega)
  · exact opMat_deg_zero ha k i q hq

/-- Helper: the matrices `G` of a gauge, as Dolbeault forms with prescribed chart expression. -/
private theorem exists_forms_of_gauge {U : Opens X} {x : X}
    (hUs : (U : Set X) ⊆ (chartAt E x).source) {deg : Fin r → ℤ} {g : E → FibOp E r}
    (hg : IsGauge deg g) :
    ∃ G : Fin r → Fin r → DolbeaultAlg E U,
      (∀ i j, G i j ∈ dolbeaultGrade E U (deg j - deg i)) ∧
      ∀ i j, ∀ z ∈ frameDom E U x,
        chartExpr E (G i j : U → TotFibre E) (chartAt E x) z = opMat (g z) i j := by
  have h : ∀ i j : Fin r, ∃ α : DolbeaultAlg E U, α ∈ dolbeaultGrade E U (deg j - deg i) ∧
      ∀ z ∈ frameDom E U x,
        chartExpr E (α : U → TotFibre E) (chartAt E x) z = opMat (g z) i j := fun i j =>
    exists_form_of_chartExpr hUs (η := fun z => opMat (g z) i j)
      (contDiffOn_opMat hg.smooth.contDiffOn i j)
      (fun z q hq => opMat_hasDeg (hg.deg_zero z) i j q (by rw [add_zero]; exact hq))
  choose G hG1 hG2 using h
  exact ⟨G, hG1, hG2⟩

open Classical in
/-- Helper: the extension by `0` of the matrix entries of `B` has `∂̄ = 0` on the frame domain. -/
private theorem dbarTot_extend_zero {V : Set E} (hV : IsOpen V) {B : E → FibOp E r}
    (hs : ContDiffOn ℝ ∞ B V) (hhol : ∀ z ∈ V, ∀ i, pdbar (Module.finBasis ℂ E i) B z = 0)
    (k i : Fin r) {z : E} (hz : z ∈ V) :
    dbarTot E (fun w => if w ∈ V then opMat (B w) k i else 0) z = 0 := by
  have hd : DifferentiableAt ℝ B z :=
    ((hs.contDiffAt (hV.mem_nhds hz)).differentiableAt (by simp))
  rw [dbarTot_congr (g := fun w => opMat (B w) k i)
    (Filter.eventually_of_mem (hV.mem_nhds hz) fun w hw => by simp only [hw, ite_true]),
    dbarTot_opMat hd]
  simp only [hhol z hz, mul_zero, Finset.sum_const_zero]
  rfl

open Classical in
/-- Helper: the matrix of the holomorphic flat superconnection consists of `ρ(f)`'s. -/
private theorem exists_hol_matrix {U : Opens X} {x : X} (hx : x ∈ U)
    (hUs : (U : Set X) ⊆ (chartAt E x).source) {deg : Fin r → ℤ} {B : E → FibOp E r}
    (hflat : IsFlatSuperconn deg (frameDom E U x) B)
    (ha : ∀ z ∈ frameDom E U x, ∀ i, aCoef i B z = 0)
    (hhol : ∀ z ∈ frameDom E U x, ∀ i, pdbar (Module.finBasis ℂ E i) B z = 0) :
    ∃ f : Fin r → Fin r → (holSheaf E X).obj.obj (op U),
      (∀ k i, deg k ≠ deg i + 1 → f k i = 0) ∧
      ∀ k i, ∀ z ∈ frameDom E U x,
        chartExpr E (((dolbeaultRhoU E U (f k i) : dolbeaultGrade E U 0) : DolbeaultAlg E U) :
          U → TotFibre E) (chartAt E x) z = opMat (B z) k i := by
  have h : ∀ k i : Fin r, ∃ f : (holSheaf E X).obj.obj (op U), ∀ z ∈ frameDom E U x,
      chartExpr E (((dolbeaultRhoU E U f : dolbeaultGrade E U 0) : DolbeaultAlg E U) :
        U → TotFibre E) (chartAt E x) z = opMat (B z) k i := fun k i => by
    obtain ⟨f, hf⟩ := exists_hol_of_chartExpr hx hUs
      (η := fun w => if w ∈ frameDom E U x then opMat (B w) k i else 0)
      ((contDiffOn_opMat hflat.smooth k i).congr fun w hw => by simp only [hw, ite_true])
      (fun w q hq => by
        by_cases hw : w ∈ frameDom E U x
        · simp only [hw, ite_true]
          exact opMat_deg_zero (ha w hw) k i q hq
        · simp only [hw, ite_false]
          rfl)
      (fun z hz => dbarTot_extend_zero (isOpen_frameDom E U x) hflat.smooth hhol k i hz)
    exact ⟨f, fun z hz => by rw [hf z hz]; simp only [hz, ite_true]⟩
  choose f0 hf0 using h
  refine ⟨fun k i => if deg k = deg i + 1 then f0 k i else 0,
    fun k i hne => by simp only [hne, ite_false], fun k i z hz => ?_⟩
  by_cases hd : deg k = deg i + 1
  · simp only [hd, ite_true]
    exact hf0 k i z hz
  · simp only [hd, ite_false, map_zero]
    rw [opMat_eq_zero_of_ne (hflat.deg_one z hz) (ha z hz) hd]
    exact chartExpr_alg_zero (U := U) _ _

/-- Helper: `B² = 0` where `B` is flat with `∂̄B = 0`. -/
private theorem sq_eq_zero_of_flat {deg : Fin r → ℤ} {V : Set E} {B : E → FibOp E r}
    (hflat : IsFlatSuperconn deg V B)
    (hhol : ∀ z ∈ V, ∀ i, pdbar (Module.finBasis ℂ E i) B z = 0) {z : E} (hz : z ∈ V) :
    B z * B z = 0 := by
  have h := hflat.flat z hz
  unfold mcOp at h
  simpa only [hhol z hz, mul_zero, Finset.sum_const_zero, zero_add] using h

/-- Helper: a ring hom commutes with finite sums (stated for abstract rings to avoid slow
instance search on `O_X(U)`). -/
private theorem ringHom_sum {R S : Type} [Semiring R] [Semiring S] (φ : R →+* S) {ι : Type}
    (s : Finset ι) (f : ι → R) : φ (∑ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := map_sum φ f s

/-- Helper: `f² = 0` for the holomorphic matrix `f` of `B` (`ρ` is injective). -/
private theorem matrix_sq {U : Opens X} {x : X} (hUs : (U : Set X) ⊆ (chartAt E x).source)
    {B : E → FibOp E r} {f : Fin r → Fin r → (holSheaf E X).obj.obj (op U)}
    (hf : ∀ k i, ∀ z ∈ frameDom E U x,
      chartExpr E (((dolbeaultRhoU E U (f k i) : dolbeaultGrade E U 0) : DolbeaultAlg E U) :
        U → TotFibre E) (chartAt E x) z = opMat (B z) k i)
    (hB2 : ∀ z ∈ frameDom E U x, ∀ k i, ∑ l, opMat (B z) l i * opMat (B z) k l = 0)
    (k i : Fin r) : ∑ l, f k l * f l i = 0 := by
  rw [show ∑ l, f k l * f l i = ∑ l, f l i * f k l from
    Finset.sum_congr rfl fun l _ => mul_comm _ _]
  refine dolbeaultRhoU_injective E U (Subtype.ext (eq_of_chartExpr_eq_frameDom hUs fun z hz => ?_))
  rw [ringHom_sum, RingHom.map_zero]
  have e1 : (((∑ l, dolbeaultRhoU E U (f l i * f k l) : dolbeaultGrade E U 0)) :
      DolbeaultAlg E U) = ∑ l, ((dolbeaultRhoU E U (f l i) : dolbeaultGrade E U 0) :
        DolbeaultAlg E U) * ((dolbeaultRhoU E U (f k l) : dolbeaultGrade E U 0) :
        DolbeaultAlg E U) := by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun l _ => by rw [RingHom.map_mul]; rfl
  rw [e1, chartExpr_alg_sum]
  refine (Finset.sum_congr rfl fun l _ => ?_).trans ((hB2 z hz k i).trans
    (chartExpr_alg_zero (U := U) _ _).symm)
  rw [chartExpr_alg_mul, hf _ _ z hz, hf _ _ z hz]

/-- Helper: the forms `G`, `H` of a gauge and its inverse are mutually inverse matrices. -/
private theorem inverse_relations {U : Opens X} {x : X}
    (hUs : (U : Set X) ⊆ (chartAt E x).source) {deg : Fin r → ℤ} {g : E → FibOp E r}
    (hg : IsGauge deg g) {G H : Fin r → Fin r → DolbeaultAlg E U}
    (hGc : ∀ i j, ∀ z ∈ frameDom E U x,
      chartExpr E (G i j : U → TotFibre E) (chartAt E x) z = opMat (g z) i j)
    (hHc : ∀ i j, ∀ z ∈ frameDom E U x,
      chartExpr E (H i j : U → TotFibre E) (chartAt E x) z = opMat (Ring.inverse (g z)) i j) :
    (∀ l j, ∑ i, G i j * H l i = if l = j then 1 else 0) ∧
      ∀ k i, ∑ j, H j i * G k j = if k = i then 1 else 0 := by
  constructor
  · intro l j
    refine eq_of_chartExpr_eq_frameDom hUs fun z hz => ?_
    rw [chartExpr_alg_sum]
    simp only [chartExpr_alg_mul, hGc _ _ z hz, hHc _ _ z hz]
    rw [← opMat_mul_of_comm ((IsGauge.inverse hg).comm z) (g z) l j,
      Ring.inverse_mul_cancel _ (hg.unit z), opMat_one]
    by_cases hlj : l = j
    · simp only [hlj, ite_true]
      exact (chartExpr_alg_one hz).symm
    · simp only [hlj, ite_false]
      exact (chartExpr_alg_zero (U := U) _ _).symm
  · intro k i
    refine eq_of_chartExpr_eq_frameDom hUs fun z hz => ?_
    rw [chartExpr_alg_sum]
    simp only [chartExpr_alg_mul, hGc _ _ z hz, hHc _ _ z hz]
    rw [← opMat_mul_of_comm (hg.comm z) (Ring.inverse (g z)) k i,
      Ring.mul_inverse_cancel _ (hg.unit z), opMat_one]
    by_cases hki : k = i
    · simp only [hki, ite_true]
      exact (chartExpr_alg_one hz).symm
    · simp only [hki, ite_false]
      exact (chartExpr_alg_zero (U := U) _ _).symm

/-- Helper: the chart expression of the connection matrix entry is the matrix entry of
`frameOp`. -/
private theorem opMat_frameOp {U : Opens X} {x : X} {N : QuasiCohesive (dolbeaultGrade E U)}
    (F : GradedFrame (dolbeaultGrade E U) N.Q r) (z : E) (l j : Fin r) :
    opMat (frameOp F x z) l j =
      chartExpr E ((F.mat l j : DolbeaultAlg E U) : U → TotFibre E) (chartAt E x) z :=
  opMat_matOp _ l j

/-- Helper: the gauge identity of `exists_iso_fromComplex_of_frame` for the forms `G`, `f`. -/
private theorem gauge_forms {U : Opens X} {x : X} (hx : x ∈ U)
    (hUs : (U : Set X) ⊆ (chartAt E x).source) {N : QuasiCohesive (dolbeaultGrade E U)}
    (F : GradedFrame (dolbeaultGrade E U) N.Q r) {g B : E → FibOp E r} (hg : IsGauge F.deg g)
    (hB : ∀ z ∈ frameDom E U x, gaugeOp g (frameOp F x) z = B z)
    (hflat : IsFlatSuperconn F.deg (frameDom E U x) B)
    {G : Fin r → Fin r → DolbeaultAlg E U}
    (hGc : ∀ i j, ∀ z ∈ frameDom E U x,
      chartExpr E (G i j : U → TotFibre E) (chartAt E x) z = opMat (g z) i j)
    {f : Fin r → Fin r → (holSheaf E X).obj.obj (op U)}
    (hf : ∀ k i, ∀ z ∈ frameDom E U x,
      chartExpr E (((dolbeaultRhoU E U (f k i) : dolbeaultGrade E U 0) : DolbeaultAlg E U) :
        U → TotFibre E) (chartAt E x) z = opMat (B z) k i) (i j : Fin r) :
    GCDga.d (𝒜 := dolbeaultGrade E U) (G i j) +
        ∑ k, GCDga.sigma (dolbeaultGrade E U) (G k j) *
          ((dolbeaultRhoU E U (f i k) : dolbeaultGrade E U 0) : DolbeaultAlg E U) =
      ∑ l, (F.mat l j : DolbeaultAlg E U) * G i l := by
  refine eq_of_chartExpr_eq_frameDom hUs fun z hz => ?_
  rw [chartExpr_alg_add, chartExpr_alg_sum, chartExpr_alg_sum, chartExpr_d hx _ hz]
  simp only [chartExpr_alg_mul, chartExpr_sigma, hGc _ _ z hz, hf _ _ z hz]
  have hnhds : frameDom E U x ∈ nhds z := (isOpen_frameDom E U x).mem_nhds hz
  rw [dbarTot_congr (g := fun w => opMat (g w) i j)
    (Filter.eventually_of_mem hnhds fun w hw => hGc i j w hw)]
  simp only [← opMat_frameOp F z]
  rw [gauge_entries hg (hB z hz) (hflat.odd z hz) i j, add_comm]

/-- **Z5.i (E.3–E.4).** Let `x ∈ U ⊆ (chartAt x).source`, `N` cohesive over `𝒜_X(U)` with a graded
frame `F`, `g` a gauge, and `B` a flat superconnection on `frameDom U x` that equals `g·𝒜` there
(`𝒜 = frameOp F x`, `gaugeOp`), with all `aᵢ(B) = 0` and `∂ᵢB = 0` there. Then `N` is isomorphic in
`Ho(P_{𝒜_X(U)})` to `𝒜_X(U) ⊗_{O_X(U)} W` for a bounded complex `W` of finitely generated
projective `O_X(U)`-modules. [B, proof of Lemma 4.1.5]. -/
theorem exists_iso_of_gauge {U : Opens X} {x : X} (hx : x ∈ U)
    (hUs : (U : Set X) ⊆ (chartAt E x).source) (N : CohesiveModule (dolbeaultGrade E U))
    (F : GradedFrame (dolbeaultGrade E U) N.Q r) {g B : E → FibOp E r} (hg : IsGauge F.deg g)
    (hB : ∀ z ∈ frameDom E U x, gaugeOp g (frameOp F x) z = B z)
    (hflat : IsFlatSuperconn F.deg (frameDom E U x) B)
    (ha : ∀ z ∈ frameDom E U x, ∀ i, aCoef i B z = 0)
    (hhol : ∀ z ∈ frameDom E U x, ∀ i, pdbar (Module.finBasis ℂ E i) B z = 0) :
    ∃ (W : CochainComplex (ModuleCat.{0} ((holSheaf E X).obj.obj (op U))) ℤ)
      (hW : IsBoundedFGProj ((holSheaf E X).obj.obj (op U)) W),
      Nonempty (HoP.mk N ≅ HoP.mk (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E U) W
        (dbar_dolbeaultRhoU E U) rfl hW)) := by
  obtain ⟨f, hfdeg, hf⟩ := exists_hol_matrix hx hUs hflat ha hhol
  obtain ⟨G, hG, hGc⟩ := exists_forms_of_gauge hUs hg
  obtain ⟨H, hH, hHc⟩ := exists_forms_of_gauge hUs (IsGauge.inverse hg)
  obtain ⟨hGH, hHG⟩ := inverse_relations hUs hg hGc hHc
  have hB2 : ∀ z ∈ frameDom E U x, ∀ k i,
      ∑ l, opMat (B z) l i * opMat (B z) k l = 0 := fun z hz k i =>
    opMat_sq_of_odd (hflat.odd z hz) (fun i k q hq => opMat_deg_zero (ha z hz) i k q hq)
      (sq_eq_zero_of_flat hflat hhol hz) k i
  have hsq := matrix_sq hUs hf hB2
  have hgauge := gauge_forms hx hUs F hg hB hflat hGc hf
  obtain ⟨hh⟩ := exists_iso_fromComplex_of_frame (ρ := dolbeaultRhoU E U)
    (dbar_dolbeaultRhoU E U) rfl hfdeg hsq N F rfl G H hG hH hGH hHG hgauge
  exact ⟨_, isBoundedFGProj_matComplex hfdeg hsq, ⟨hh⟩⟩

/-- Helper: the gauge action on the restricted frame model is the restriction of the gauge
action on the frame model. -/
private theorem gaugeOp_baseChange_eq {U' V : Opens X} (hle : V ≤ U') {x : X} {z : E}
    (hz : z ∈ frameDom E V x) (N' : CohesiveModule (dolbeaultGrade E U'))
    (F : GradedFrame (dolbeaultGrade E U') N'.Q r)
    (F' : GradedFrame (dolbeaultGrade E V) (BCGen (dolbeaultRes E hle) N'.Q) r)
    (hF' : ∀ i, F'.basis i = bcι (dolbeaultRes E hle) N'.Q (F.basis i)) (g : E → FibOp E r) :
    gaugeOp g (frameOp (N := (N'.baseChange (dolbeaultRes E hle)).toQuasiCohesive) F' x) z =
      gaugeOp g (frameOp F x) z := by
  have hop : frameOp (N := (N'.baseChange (dolbeaultRes E hle)).toQuasiCohesive) F' x z =
      frameOp F x z := frameOp_baseChange (N := N'.toQuasiCohesive) hle hF' x hz
  unfold gaugeOp
  rw [hop]

/-- Helper: `exists_iso_of_gauge` applied to the restriction `N′|V` in the restricted frame. -/
private theorem iso_of_restriction {U' V : Opens X} (hle : V ≤ U') {x : X} (hxV : x ∈ V)
    (hVs : (V : Set X) ⊆ (chartAt E x).source) (N' : CohesiveModule (dolbeaultGrade E U'))
    (F : GradedFrame (dolbeaultGrade E U') N'.Q r) {g : E → FibOp E r} (hg : IsGauge F.deg g)
    (hflat : IsFlatSuperconn F.deg (frameDom E V x) (gaugeOp g (frameOp F x)))
    (ha : ∀ z ∈ frameDom E V x, ∀ i, aCoef i (gaugeOp g (frameOp F x)) z = 0)
    (hhol : ∀ z ∈ frameDom E V x, ∀ i,
      pdbar (Module.finBasis ℂ E i) (gaugeOp g (frameOp F x)) z = 0) :
    ∃ (W : CochainComplex (ModuleCat.{0} ((holSheaf E X).obj.obj (op V))) ℤ)
      (hW : IsBoundedFGProj ((holSheaf E X).obj.obj (op V)) W),
      Nonempty (HoP.mk (N'.baseChange (dolbeaultRes E hle)) ≅
        HoP.mk (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E V) W
          (dbar_dolbeaultRhoU E V) rfl hW)) := by
  obtain ⟨F', hF'deg, hF'⟩ := exists_frame_baseChange (dolbeaultRes E hle) F
  have hg' : IsGauge F'.deg g := by rw [hF'deg]; exact hg
  have hflat' : IsFlatSuperconn F'.deg (frameDom E V x) (gaugeOp g (frameOp F x)) := by
    rw [hF'deg]; exact hflat
  exact exists_iso_of_gauge hxV hVs (N'.baseChange (dolbeaultRes E hle)) F' hg'
    (B := gaugeOp g (frameOp F x)) (fun z hz => gaugeOp_baseChange_eq hle hz N' F F' hF' g)
    hflat' ha hhol

/-- Helper: the restriction of a frame-model gauge datum on `W₀ ⊆ frameDom U′ x` to
`U″ = chartOpen x W₀` and `exists_iso_of_gauge` there. -/
private theorem iso_of_restricted_gauge {U' : Opens X} {x : X}
    (N' : CohesiveModule (dolbeaultGrade E U')) (F : GradedFrame (dolbeaultGrade E U') N'.Q r)
    {W₀ : Set E} (hW₀ : IsOpen W₀) (hxW₀ : chartAt E x x ∈ W₀)
    (hW₀V : W₀ ⊆ frameDom E U' x) {g : E → FibOp E r} (hg : IsGauge F.deg g)
    (hflat : IsFlatSuperconn F.deg W₀ (gaugeOp g (frameOp F x)))
    (ha : ∀ z ∈ W₀, ∀ i, aCoef i (gaugeOp g (frameOp F x)) z = 0)
    (hhol : ∀ z ∈ W₀, ∀ i, pdbar (Module.finBasis ℂ E i) (gaugeOp g (frameOp F x)) z = 0) :
    ∃ (hle : chartOpen E x hW₀ ≤ U') (_ : x ∈ chartOpen E x hW₀)
      (W : CochainComplex (ModuleCat.{0} ((holSheaf E X).obj.obj (op (chartOpen E x hW₀)))) ℤ)
      (hW : IsBoundedFGProj ((holSheaf E X).obj.obj (op (chartOpen E x hW₀))) W),
      Nonempty (HoP.mk (N'.baseChange (dolbeaultRes E hle)) ≅
        HoP.mk (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E (chartOpen E x hW₀)) W
          (dbar_dolbeaultRhoU E (chartOpen E x hW₀)) rfl hW)) := by
  have hle : chartOpen E x hW₀ ≤ U' := chartOpen_le hW₀ hW₀V
  have hdom : frameDom E (chartOpen E x hW₀) x = W₀ :=
    frameDom_chartOpen x hW₀ fun z hz => (hW₀V hz).1
  have hxU : x ∈ chartOpen E x hW₀ := ⟨mem_chart_source E x, hxW₀⟩
  rw [← hdom] at hflat ha hhol
  obtain ⟨W, hW, hiso⟩ := iso_of_restriction hle hxU (fun y hy => hy.1) N' F hg hflat ha hhol
  exact ⟨hle, hxU, W, hW, hiso⟩

/-- Z5.i: a cohesive module with a graded frame is, near each `x ∈ U′`, isomorphic to
`𝒜 ⊗ W` (frame model, gauge induction Z5.f, then `iso_of_restricted_gauge`). Public since Z3.e
(H2 on opens, `localGaugeLemmaOpen`). -/
theorem exists_local_iso {U' : Opens X} {x : X} (hxU' : x ∈ U')
    (N' : CohesiveModule (dolbeaultGrade E U')) (F : GradedFrame (dolbeaultGrade E U') N'.Q r) :
    ∃ (U'' : Opens X) (hle : U'' ≤ U') (_ : x ∈ U'')
      (W : CochainComplex (ModuleCat.{0} ((holSheaf E X).obj.obj (op U''))) ℤ)
      (hW : IsBoundedFGProj ((holSheaf E X).obj.obj (op U'')) W),
      Nonempty (HoP.mk (N'.baseChange (dolbeaultRes E hle)) ≅
        HoP.mk (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E U'') W
          (dbar_dolbeaultRhoU E U'') rfl hW)) := by
  obtain ⟨W₀, hW₀, hxW₀, hW₀V, g, hg, hflatB, hfin⟩ := exists_gauge_holomorphic F.deg
    (isOpen_frameDom E U' x) (mem_frameDom E hxU') (isFlatSuperconn_frameOp F hxU')
  obtain ⟨hle, hxU, W, hW, hiso⟩ := iso_of_restricted_gauge N' F hW₀ hxW₀ hW₀V hg hflatB
    (fun z hz i => (hfin z hz).1 i) (fun z hz i => (hfin z hz).2 i)
  exact ⟨_, hle, hxU, W, hW, hiso⟩

/-- Helper: a graded frame of the base change of `M` to a small enough neighbourhood of `x`
(Z5.g local freeness, Z5.h frames). -/
private theorem exists_frame_top (M : CohesiveModule (dolbeault E X)) (x : X) :
    ∃ (U' : Opens X) (_ : x ∈ U') (r : ℕ), Nonempty (GradedFrame (dolbeaultGrade E U')
      (M.baseChange (dolbeaultRes E (le_top : U' ≤ ⊤))).Q r) := by
  obtain ⟨U', hxU', hU's, hfree⟩ := exists_free_baseChange E M x
  obtain ⟨r, ⟨F⟩⟩ := exists_gradedFrame_bcGen (dolbeaultRes E (le_top : U' ≤ ⊤)) M hfree
  exact ⟨U', hxU', r, ⟨F⟩⟩

/-- Helper: `(M|U′)|U″ ≅ M|U″` in `Ho(P)` (`dolbeaultRes_comp`, `bcCompIso`). -/
private theorem iso_top_comp {U' U'' : Opens X} (M : CohesiveModule (dolbeault E X))
    (hle : U'' ≤ U') :
    Nonempty (HoP.mk (M.baseChange (dolbeaultRes E (le_top : U'' ≤ ⊤))) ≅
      HoP.mk ((M.baseChange (dolbeaultRes E (le_top : U' ≤ ⊤))).baseChange
        (dolbeaultRes E hle))) := by
  have e : dolbeaultRes E (le_top : U'' ≤ ⊤) =
      (dolbeaultRes E hle).comp (dolbeaultRes E (le_top : U' ≤ ⊤)) :=
    (dolbeaultRes_comp E (le_top : U' ≤ ⊤) hle).symm
  rw [e]
  exact ⟨bcCompIso (dolbeaultRes E (le_top : U' ≤ ⊤)) (dolbeaultRes E hle) (HoP.mk M)⟩

variable (E X) in
/-- **Z5.i. H2, the local gauge lemma** (weak form, as frozen in `Hypotheses.lean`), proved on
every complex manifold `X` modelled on `E`. [B, Lemma 4.1.5], following [DK §2.2.2],
[BSW Thm 5.3] (blueprint-ll §1). Every cohesive module over `𝒜_X(X)` is, near each point `x`,
isomorphic in `Ho(P_{𝒜_X(U′)})` to `𝒜_X(U′) ⊗_{O_X(U′)} W` for a bounded complex `W` of finitely
generated projective `O_X(U′)`-modules. -/
theorem localGaugeLemma : LocalGaugeLemma E X := by
  intro M x
  obtain ⟨U', hxU', r, ⟨F⟩⟩ := exists_frame_top M x
  obtain ⟨U'', hle, hxU'', W, hW, ⟨hiso⟩⟩ := exists_local_iso hxU'
    (M.baseChange (dolbeaultRes E (le_top : U' ≤ ⊤))) F
  obtain ⟨e⟩ := iso_top_comp M hle
  exact ⟨U'', hxU'', W, hW, ⟨e ≪≫ hiso⟩⟩

end Cohesive
