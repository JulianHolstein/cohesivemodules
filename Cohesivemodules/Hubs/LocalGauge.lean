import Cohesivemodules.Forms.LocalGaugeOpen
import Cohesivemodules.MainH2

set_option linter.style.header false

/-!
# The local gauge lemma H2 and its proof

This page is an overview of the local gauge lemma (blueprint item H2) and its proof (items
Z5.a–Z5.j, `blueprint/blueprint-ll.md`). It contains no declarations; the links below point to
the files where the definitions and theorems live.

## Overview

H2 is the local input of the comparison functor `J` (*Block's theorem* hub): it shows that `J`
lands in perfect complexes (C2), and it is used locally in the proof of full faithfulness (C4).
It says that every cohesive module over the Dolbeault algebra `A = 𝒜_X(X)` looks, near each
point, like a complex of holomorphic vector bundles.
In the project this is the `Prop` `Cohesive.LocalGaugeLemma` (H2, frozen in
`Hypotheses.lean` at gate 3), the field LL of the resolving data C0:
```
def LocalGaugeLemma : Prop :=
  ∀ (M : CohesiveModule (dolbeault E X)) (x : X),
    ∃ (U' : Opens X) (_ : x ∈ U')
      (W : CochainComplex (ModuleCat.{0} ((holSheaf E X).obj.obj (op U'))) ℤ)
      (hW : IsBoundedFGProj ((holSheaf E X).obj.obj (op U')) W),
      Nonempty (HoP.mk (M.baseChange (dolbeaultRes E (le_top : U' ≤ ⊤))) ≅
        HoP.mk (CohesiveModule.fromComplex (ρ := dolbeaultRhoU E U') W
          (dbar_dolbeaultRhoU E U') rfl hW))
```
In words: for every cohesive module `M` over `𝒜_X(X)` and every `x ∈ X` there are an open
`U′ ∋ x`, a bounded complex `W` of finitely generated projective `O_X(U′)`-modules, and an
isomorphism in `Ho(P_{𝒜_X(U′)})` between the restriction `M|U′` (base change along
`dolbeaultRes`, A9) and `𝒜_X(U′) ⊗_{O_X(U′)} W` (A10, along `ρ_{U′} = dolbeaultRhoU`).

⚠ **Weak form.** [[B][Block], Lemma 4.1.5] states full faithfulness of `α` (Block's name for
`J`); the
gauge equivalence is in its *proof*, which gives, on a small polydisc, an actual isomorphism of
cohesive modules with a complex of trivial holomorphic bundles, for restrictions of global
cohesive modules. Compared with Block's proof, H2 asks for less: an isomorphism in the homotopy
category (a homotopy equivalence) instead of an isomorphism of cohesive modules, and `W` finitely
generated projective rather than free. Compared with [[A][Antweiler]]'s local lifting assumption
(item 6 of
Assumptions 7.2), a sheaf version for cohesive modules on every open set, H2 is sectionwise and
only for restrictions of global modules; this suffices because the comparison theorem applies it
only to such restrictions. The proof below establishes the strong form in substance (mutually
inverse closed maps, `W` free) and concludes H2.

**Status.** H2 is a theorem, `Cohesive.localGaugeLemma` (Z5.i), on every complex manifold `X`
modelled on a finite-dimensional `E`; no compactness is needed. The module docstring of the
frozen `Hypotheses.lean` still says "their proofs are LATER"; this is known and accepted
(blueprint §11 v1.18). With H1 (*Dolbeault–Grothendieck lemma* hub) it gives the main
theorem without hypotheses, `main_theorem` (root namespace; Z5.j, `MainH2.lean`; the statement
is the subject of the *Block's theorem* hub).

**Proof in brief** (blueprint-ll §4). Near `x`, in a chart and a frame of the generators, the
superconnection `𝕏` of `M` is `∂̄ + 𝒜` with `𝒜` a smooth function with values in fibre
operators, and flatness is the Maurer–Cartan equation `Σⱼ εⱼ ∂ⱼ𝒜 + 𝒜² = 0` (`εⱼ = dz̄ⱼ ∧ ·`,
`∂ⱼ = ∂̄` along `e_j`; see Conventions). A gauge transformation, built one coordinate `z_k` at a
time ([[DK][DonaldsonKronheimer], §2.2.2], [[BSW][BismutShenWei], Thm 5.3]; each step removes
`dz̄_k`), removes every `dz̄ᵢ` from `𝒜` and
makes it holomorphic; what is left is a complex of trivial holomorphic bundles. Each step solves
the *linear* equation `∂̄_k g = g a` with parameters, by a Neumann series built on the Cauchy
solver of Z4. The proof does not use H1 itself, only the Z4 analytic toolkit
(`Cohesive.cauchySolve`, the slab-cutoff construction of Z4.e, redone with radius control as
`Cohesive.exists_cutoff_radius`, and chart transport).

## Main definitions

* `Cohesive.LocalGaugeLemma`: the statement H2 (frozen, `Hypotheses.lean`).
* `Cohesive.pdbar`: `∂̄` along a vector, for functions with values in any complex normed space
  (Z5.b).
* `Cohesive.neumannTerm`, `Cohesive.gaugeSeries`: the Neumann series `g = Σᵢ uᵢ` of iterated
  Cauchy solves, solving `∂̄_k g = g b` for the cut-off coefficient `b` (Z5.c).
* `Cohesive.Fib`, `Cohesive.FibOp`, `Cohesive.epsOp`, `Cohesive.iotaOp`, `Cohesive.IsOfTotDeg`:
  the fibre `Λ ⊗ ℂ^r`, its operator algebra, `dz̄ⱼ ∧ ·`, the contractions, total degree (Z5.d).
* `Cohesive.dbarFib`, `Cohesive.mcOp`, `Cohesive.gaugeOp`, `Cohesive.aCoef`: `∂̄` of sections,
  the Maurer–Cartan expression, the gauge action, the `dz̄ᵢ`-coefficient (Z5.e).
* `Cohesive.IsFlatSuperconn`, `Cohesive.IsGauge`, `Cohesive.gaugeSubalg`: the hypotheses kept
  along the induction, the gauges, the gauge algebra of step `k` (Z5.f).
* `Cohesive.GradedFrame`, `Cohesive.GradedFrame.coefTot`, `Cohesive.GradedFrame.mat`: frames of
  the generators, coefficients, the connection matrix (Z5.h, generic dga).
* `Cohesive.frameDom`, `Cohesive.chartCoef`, `Cohesive.frameOp`, `Cohesive.matOp`: the frame
  model of a cohesive module in a chart (Z5.h).
* `Cohesive.opMat`: the matrix of a fibre operator (Z5.i).
* `Cohesive.matComplex`: the complex `W` of a square-zero matrix over a commutative ring (Z5.i).

## Main results

* `Cohesive.norm_cauchySolve_le` (Z5.a): if `ℓ v = 1` and `G` vanishes outside
  `{w | ‖ℓ w − c‖ ≤ ρ}`, then `‖cauchySolve v G z‖ ≤ 3ρ·sup‖G‖`.
* `Cohesive.iteratedFDeriv_cauchySolve`, `Cohesive.pdbar_cauchySolve`,
  `Cohesive.pdbar_cauchySolve_comm` (Z5.b): the solver commutes with all derivatives, is a right
  inverse of `∂̄_v` (for `v ≠ 0`, `F` compactly supported), and commutes with `∂̄_w`.
* `Cohesive.exists_gauge_solution` (Z5.c): for a finite-dimensional complex Banach algebra `𝔄`
  with `‖1‖ = 1`, a subalgebra `S`, and `a` smooth on an open `U ∋ x` with values in `S` there,
  holomorphic in the directions `e_j`, `j ∈ J ∌ k`: there are an open `W` with `x ∈ W ⊆ U` and
  `g : E → 𝔄`, `C^∞` on `E`, pointwise invertible, with values in `S`, such that
  `∂̄_{e_k} g = g a` and `∂̄_{e_j} g = 0` (`j ∈ J`) on `W`.
* `Cohesive.dbarFib_eq_sum` (B.1), `Cohesive.dbarFib_add_sq` (curvature, B.2),
  `Cohesive.gauge_conj`, `Cohesive.mcOp_gaugeOp`, `Cohesive.gaugeOp_mul` (gauge action, B.3),
  `Cohesive.iota_mcOp` (contracted Maurer–Cartan, B.4), `Cohesive.aCoef_gaugeOp` (B.5),
  `Cohesive.aCoef_comm` (B.6), `Cohesive.preserves_deg_zero` (B.7) (Z5.e).
* `Cohesive.exists_gauge_holomorphic` (Z5.f): a flat ∂̄-superconnection on an open `U ⊆ E` is,
  near each point, gauge equivalent to one with all `dz̄ᵢ`-coefficients zero and holomorphic.
  One step is `Cohesive.exists_gauge_step`; the downward induction is
  `Cohesive.exists_gauge_of_aCoef`.
* `Cohesive.exists_free_baseChange` (Z5.g): near `x`, inside the chart at `x`, every
  `𝒜⁰(U′) ⊗_{𝒜⁰(X)} Q^p` is free.
* `Cohesive.exists_gradedFrame_bcGen`, `Cohesive.GradedFrame.coefTot_X`,
  `Cohesive.chartCoef_X`, `Cohesive.isFlatSuperconn_frameOp` (Z5.h): frames exist once the
  generators are free, and in a chart `𝕏 = ∂̄ + 𝒜` with `𝒜 = frameOp` a flat
  ∂̄-superconnection.
* `Cohesive.exists_iso_fromComplex_of_frame` (Z5.i, algebraic E.4): a frame and mutually
  inverse matrices `G, H` of forms satisfying the gauge identity give `N ≅ A ⊗_R W` in `Ho(P_A)`,
  through `Cohesive.hoPIsoOfInverse`.
* `Cohesive.exists_iso_of_gauge`, `Cohesive.exists_local_iso`, `Cohesive.localGaugeLemma`
  (Z5.i): the assembly, and H2.
* Open-set versions (Z3.e, used for the curved local lifting `Forms/CurvedLL.lean`; see the
  *Twisted theorem* hub): `Cohesive.exists_free_baseChange_open`, `Cohesive.localGaugeLemmaOpen`
  (H2 for cohesive modules over `𝒜_X(U₀)`, `x ∈ U₀`, with `U′ ≤ U₀`).
* `Cohesive.localGaugeLemma_of_finrank_eq_zero`: H2 in dimension `0`, the check K1.

## Conventions and signs

Coordinates are indexed by `Fin (finrank ℂ E)`, from `0` ([[B][Block]],
[[DK][DonaldsonKronheimer]] count from `1`); the
induction hypothesis at step `k` is "`aᵢ = 0` for `i < k`" rather than a list of the `dz̄ᵢ` that
still occur. `e = Module.finBasis ℂ E`, `b_j` is `e_j` read in `Ē = Conj E`, and `dz̄ⱼ` is the
dual basis.

**Derivatives.** `pdbar v f z = ½ (Df(z) v + i Df(z)(i v))`, the antilinear part of the
derivative (F3 normalization; on `E = ℂ`, `pdbar 1 f = ∂f/∂z̄`), and `∂ⱼ := pdbar (e j)`. For a
section `s : E → Fib E r`, `∂̄s = Σⱼ εⱼ ∂ⱼ s` (`Cohesive.dbarFib_eq_sum`, B.1).

**Fibre operators** (Z5.d).
* `Fib E r = Fin r → TotFibre E` is `Λ ⊗ ℂ^r`, `Λ = Λ^{0,•}(E)`, with generator degrees
  `deg : Fin r → ℤ`; `t ∈ Λ^q` in component `i` has total degree `q + deg i`.
* `εⱼ = epsOp j` is left multiplication by `dz̄ⱼ` in each component; `ιⱼ = iotaOp j` is
  contraction with `b_j` (Mathlib's `CliffordAlgebra.contractLeft`).
* Relations: `εᵢεⱼ = −εⱼεᵢ`, `ιᵢιⱼ = −ιⱼιᵢ`, `ιᵢεⱼ + εⱼιᵢ = δᵢⱼ`.
* `T` is *even* if `εⱼT = Tεⱼ` for all `j` (Λ-linear), *odd* if `εⱼT = −Tεⱼ` (Λ-linear in the
  graded sense). A
  superconnection coefficient `𝒜` is odd of total degree `1`; a gauge `g` is even, of total
  degree `0`, smooth and pointwise invertible.

**Flatness and gauges** (Z5.e).
* `mcOp 𝒜 = Σⱼ εⱼ ∂ⱼ𝒜 + 𝒜²`, and `(∂̄ + 𝒜)² s = mcOp 𝒜 · s`; flat means `mcOp 𝒜 = 0`.
* `g·𝒜 := gaugeOp g 𝒜 = g𝒜g⁻¹ − (Σⱼ εⱼ ∂ⱼg) g⁻¹` (`g⁻¹ = Ring.inverse g`); `·` is used only for
  this gauge action, products are written by juxtaposition. Then
  `g ∘ (∂̄ + 𝒜) ∘ g⁻¹ = ∂̄ + g·𝒜`; `mcOp (g·𝒜) = g (mcOp 𝒜) g⁻¹`; `(hg)·𝒜 = h·(g·𝒜)`.
* `aCoef i 𝒜 = ιᵢ𝒜 + 𝒜ιᵢ` is the `dz̄ᵢ`-coefficient, and
  `ιᵢ mcOp − mcOp ιᵢ = ∂ᵢ𝒜 − Σⱼ εⱼ ∂ⱼaᵢ + aᵢ𝒜 − 𝒜aᵢ`. So once all `aᵢ` vanish, flatness gives
  `∂ᵢ𝒜 = 0`: holomorphy needs no separate argument.

**Frames and matrices of forms** (Z5.h, Z5.i).
* A graded frame is one basis `ẽ₁ … ẽ_r` of `⨁_p Q^p` by homogeneous elements of degrees
  `deg i`; every `x ∈ Tot Q` is `Σᵢ xᵢ · (1 ⊗ ẽᵢ)` with `xᵢ = coefTot x i ∈ A`.
* The connection matrix `ωⱼᵢ = mat j i` is the `j`-th coefficient of `𝕏(1 ⊗ ẽᵢ)`, of degree
  `deg i + 1 − deg j`, and `(𝕏x)ⱼ = d xⱼ + Σᵢ σ(xᵢ) ωⱼᵢ` with `σ` the parity involution
  `Cohesive.GCDga.sigma`: the coefficient stands on the left, as for left modules
  (*Cohesive modules* hub).
* In the chart `φ = chartAt x₀`, for `x₀ ∈ U` and on `frameDom U x₀ = φ(U ∩ φ.source)`:
  `frameOp z (t)ⱼ = Σᵢ σ(tᵢ) Ωⱼᵢ(z)` with `Ωⱼᵢ = chartExpr ωⱼᵢ` (`matOp Ω`), and
  `chartCoef (𝕏x) = ∂̄ (chartCoef x) + frameOp (chartCoef x)`.
* `opMat T i j = T(eⱼ)ᵢ`. Even `T`: `T(t)ᵢ = Σⱼ tⱼ Tᵢⱼ`, and `(TS)ᵢⱼ = Σₖ Sₖⱼ Tᵢₖ`
  (`Cohesive.opMat_mul_of_comm`; note the order of the factors, the entries lie in the
  noncommutative `Λ`). Odd `T`: `T = matOp (opMat T)`.
* `matComplex R deg f`: `W^p = R^{{i | deg i = p}}`, `d(w)ₖ = Σᵢ fₖᵢ wᵢ`, where `fₖᵢ = 0` unless
  `deg k = deg i + 1`, and `Σₗ fₖₗ fₗᵢ = 0` (`f² = 0`).
* The isomorphism is `Ψ(1 ⊗ ẽⱼ) = Σᵢ Gᵢⱼ ⊗ wᵢ` with inverse `Φ(1 ⊗ wᵢ) = Σⱼ Hⱼᵢ ⊗ ẽⱼ`, under the
  gauge identity `dGᵢⱼ + Σₖ σ(Gₖⱼ) ρ(fᵢₖ) = Σₗ ωₗⱼ Gᵢₗ`, where `G` and `H` are the matrices of the
  gauge `g` and of `g⁻¹` read back as forms (mutually inverse), and `ρ(f)` is the matrix of the
  holomorphic, form-degree-`0` operator `g·𝒜`.

## Implementation notes

* **Operators, not matrices of forms.** The local analysis works with fibre operators, where
  all signs sit in `εⱼ` and `ιⱼ` (blueprint-ll §3, decision L1); matrices appear only at the end,
  through `Cohesive.opMat`. Block's p-degree separation is replaced by the contracted
  Maurer–Cartan equation (blueprint-ll §1, audit row a4).
* **Smoothness without elliptic regularity.** `g = Σᵢ uᵢ` is `C^∞` by summable bounds
  `‖D^m uᵢ‖ ≤ C_m (i+1)^m θ^i` with constants `C_m` and a ratio `θ < 1` controlled by the cutoff
  radius (`contDiff_tsum`); constraints (degree `0`, even, commuting with `ιᵢ`, `i ≤ k`) are kept
  by solving in the subalgebra `Cohesive.gaugeSubalg`. This closes the smoothness gap of the
  sources (blueprint-ll §1, audit row a5). ⚠ The integral of the kernel `|t|⁻¹` over a disc of
  radius `ρ` is bounded by `3πρ` (`Cohesive.integral_inv_norm_ball_le`) instead of
  [[DK][DonaldsonKronheimer]]'s `2πρ`,
  because the disc is not centred at the pole; with the factor `π⁻¹` in `cauchySolve` this gives
  the `3ρ` of Z5.a.
* ⚠ **Local freeness by localization** (blueprint §11 v1.17), not by idempotent matrices and
  Cramer's rule: localize at `ker (ev_x)`, spread freeness to `{r_p ≠ 0}`, where `r_p` is a unit.
* ⚠ **Maurer–Cartan from the frame vectors** (blueprint §11 v1.18): `mcOp frameOp = 0` follows
  from `𝕏² = 0` on the frame vectors and the Λ-linearity of `mcOp`, not from all sections via
  `chartForm`.
* ⚠ **`W` from `ρ`-preimages** (blueprint §11 v1.18): the holomorphic degree-`0` entries of `g·𝒜`
  are chart expressions of `ρ(fᵢⱼ)` with `fᵢⱼ ∈ O(U″)` (F12), and `W = matComplex` of `f` is free.
* **Generic algebra.** Graded frames and their base change (`Algebra/Frame.lean`,
  `Algebra/FrameBaseChange.lean`) are stated for any map of (possibly curved) dgas; `matComplex`
  for any commutative ring `R`; the isomorphism `Cohesive.exists_iso_fromComplex_of_frame` for any
  dga with `c = 0` and any `ρ : R →+* A⁰` with `d ∘ ρ = 0` (the hypotheses of A10). Reason:
  `Module.Free` goals on Dolbeault base changes time out in `isDefEq`. ⚠ One frame of `⨁_p Q^p`
  indexed by `Fin r`, not one frame per `Q^p`.
* **Assembly.** `M|U′` gets a frame on `U′` (Z5.g, Z5.h); the gauge induction on
  `frameDom U′ x` gives a gauge on a smaller `W₀ ∋ φ(x)`;
  the isomorphism is built on `U″ = chartOpen x W₀` for the restricted frame
  and composed with `(M|U′)|U″ ≅ M|U″` (`Cohesive.bcCompIso`).

## Files

* `Analysis/KernelEstimate.lean` (Z5.a), `Analysis/CauchySolveDeriv.lean` (Z5.b).
* `Forms/GaugeSolve.lean` (Z5.c; in `Forms/` because it uses the Z4.e cutoff).
* `Forms/FibreOps.lean` (Z5.d), `Forms/Superconnection.lean` (Z5.e),
  `Forms/GaugeInduction.lean` (Z5.f).
* `Forms/LocalFree.lean` (Z5.g).
* `Algebra/Frame.lean`, `Forms/FrameModel.lean` (Z5.h).
* `Algebra/FrameIso.lean`, `Algebra/FrameBaseChange.lean`, `Forms/GaugeMatrix.lean`,
  `Forms/ChartTransport.lean`, `Forms/LocalGauge.lean` (Z5.i).
* `MainH2.lean` (Z5.j), `Hypotheses.lean` (H2 statement, frozen).
* `Forms/LocalFreeOpen.lean`, `Forms/LocalGaugeOpen.lean` (Z3.e, open-set versions;
  `Forms/CurvedLL.lean`, the curved version, is documented in the *Twisted theorem* hub).

## References

* [[B][Block]] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2, proof of Lemma 4.1.5 (the published version: Lemma 4.5).
* [[A][Antweiler]] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1, Assumptions 7.2 (item 6, local lifting; cited in §7.4 as
  "Assumption 7").
* [[DK][DonaldsonKronheimer]] S. Donaldson, P. Kronheimer, *The geometry of four-manifolds*,
  §2.2.2, pp. 50–53.
* [[BSW][BismutShenWei]] J.-M. Bismut, S. Shen, Z. Wei, *Coherent sheaves, superconnections and
  RRG*,
  arXiv 2102.08129, §5.2, Thm 5.3.
* Blueprint: `blueprint/blueprint.md` (H2; §11 v1.15–v1.18), `blueprint/blueprint-ll.md` (Z5);
  conventions: `blueprint/conventions.md` §6.
-/
