# Conventions

**Version 1.10 (26 Oct 2026, approved by the human)**, companion to `blueprint.md` v1.10 (§2
tensor order with 𝒜^•, §9 `ringOf` spelling; v1.9: §2 shift remark, §5 carrier of A⁰, §9
statement shape). Changes from v1.0 are listed
in blueprint §11. Later notes (blueprint §11 v1.18, 2 Nov 2026, audit follow-up): §6 charts,
§8 D_perf vs D^b_coh, §9 freeze rule and imports of frozen statement files.

Every choice where this project, Mathlib and the three sources differ. `blueprint.md` says
what is proved; this file says how it is spelled. Section numbers are cited from the blueprint.

## 1. General
- Scalars: ℂ for everything geometric. Layer A works over an arbitrary commutative ring k.
- Grading: cohomological throughout; differentials raise degree by 1.
- Two degrees: the **internal degree** p ∈ ℤ of a cohesive module and the **form degree**
  q ∈ ℤ of the algebra, with A^q = 0 for q < 0 (one index type for all degrees; v1.2). The **total degree** of a ⊗ e with a ∈ A^q, e ∈ Q^p is p + q.
- Cohesive modules are bounded in p; algebras are bounded in q (A^q = 0 for q > N).
- Curvature c is carried in Layer A and set to 0 everywhere else (Z3 uses c ≠ 0).
- **Naming (4 Nov 2026).** "Dga" in Lean names (`GCDga`, `DgaHom`, `DgaPresheaf`,
  `DgaSheafData`, `dgaHom_ext'`) means a bounded graded-commutative **possibly curved** dga: the
  class `GCDga` carries the curvature `c`, `DgaHom` preserves it. Flatness is imposed separately
  (`PreResolvingData.c_eq_zero`, hypotheses `c = 0`). Docstrings of declarations that allow
  `c ≠ 0` say "(possibly curved)"; the names are not changed (decided by the human: no rename).

## 2. Signs
- Koszul rule: moving x past y costs (−1)^{|x||y|}.
- Graded commutativity of A: ab = (−1)^{pq} ba for a ∈ A^p, b ∈ A^q.
- Leibniz rule for d on A: d(ab) = da·b + (−1)^p a·db.
- ℤ-connection on a left module: 𝕏(a·m) = da·m + (−1)^{|a|} a·𝕏m.
- Hom^n: φ(a·m) = (−1)^{n|a|} a·φ(m).
- Hom differential: δφ = 𝕏₂ ∘ φ − (−1)^n φ ∘ 𝕏₁. This is Mathlib's
  `CochainComplex.HomComplex.δ` (δz = z ≫ d + (−1)^{n+1} d ≫ z; Mathlib writes composition
  in diagrammatic order).
- Composition of generator maps: for φ of degree n and ψ of degree m, ψ is extended to the
  total module by ψ̂(a ⊗ e) = (−1)^{m|a|} a·ψ(e), and ψ ∘ φ := ψ̂ ∘ φ.
- Shift: M[1] has Q[1]^p = Q^{p+1} and, on generators, components
  𝕏[1]^j = (−1)^{j+1} 𝕏^j : Q[1]^p → A^j ⊗ Q[1]^{p+1−j}. So 𝕏[1]^0 = −𝕏^0, matching Mathlib's
  shift on cochain complexes (differential multiplied by `n.negOnePow`), and 𝕏[1]^1 = +𝕏^1, so the
  connection stays a connection. Equivalently: A ⊗ Q[1] ≅ (A ⊗ Q)[1] via a ⊗ e ↦ (−1)^{|a|} a ⊗ e,
  and 𝕏[1] = −𝕏 transported along this map. ⚠ The naive rule 𝕏[1] = −𝕏 on A ⊗ Q[1] violates the
  Leibniz rule (−∇ is not a connection) whenever A ≠ A^0 — in the left convention; Block's
  𝔼[1] = −𝔼 [B, §2.4] is correct for his right modules (v1.9). For M[k]: 𝕏[k]^j = (−1)^{k(j+1)} 𝕏^j.
- Total complex of α(E): degree n is ⊕_{p+q=n} 𝒜^q ⊗_{𝒜^0} Q^p, differential 𝔼.
- (v1.10) Sheaf tensor products with the Dolbeault complex put 𝒜^• **first**:
  `tensorC R 𝒜^• K`. Its differential db ⊗ k + (−1)^{|b|} b ⊗ dk is a left-module connection
  (Mathlib's `mapBifunctor` puts (−1)^p on the second factor). With 𝒜^• second the sign lands
  on d_𝒜 and the result is not a connection. A closed degree-0 map of cohesive modules extends
  from generators with no sign: e(a ⊗ p) = a·e(1 ⊗ p).

## 3. Left modules, and translation to the sources
This project uses **left** modules A ⊗_{A^0} Q, as Antweiler does and as Mathlib's `Module`
does.

| | Block [B] | Antweiler [A] | This project |
| --- | --- | --- | --- |
| Module | right, Q ⊗_{A^0} A | left, A ⊗_{A^0} Q | left |
| 𝔼^1 on Q^p | a connection up to (−1)^p | the connection ∇ (object data) | a connection, no sign |
| Flatness | 𝔼 ∘ 𝔼 + e·c = 0 | 𝔼² = h | 𝔼 ∘ 𝔼 = c·(−) |
| Curvature | c | h | c_here = −c_Block, c_here = h_Antweiler |

For graded-commutative A, Block's right module Q ⊗ A becomes a left module through
e ⊗ a ↦ (−1)^{|e||a|} a ⊗ e; under this the operator 𝔼 is unchanged and its square changes from
−e·c to −c·e. Blueprint A13 proves the translation. At c = 0 the difference is invisible.
Lean (A13): Block's side in `Algebra/BlockDef.lean` (`TotR = (⨁ Q) ⊗_{A⁰} A`, right action
`TotR.rAct`, `BlockQuasiCohesive 𝒜 cB` with explicit Block curvature `cB`, `BlockCohesive`,
`BlockHom`, `blockδ`); the translation in `Algebra/BlockBridge.lean` (`blockSwap` = the map
above read as e ⊗ a ↦ (−1)^{|e||a|} a ⊗ e, `toLeft`/`toBlock` under `h : c = -cB`,
`blockHomEquiv`, `blockConj_δ`, `blockConj_comp`).

## 4. Encoding cohesive modules (decided after P1: encoding 1)
Three equivalent encodings:
1. **Operator on the total module.** A ⊗_{A^0} Q as a graded left A-module, 𝕏 an operator.
   Closest to Block; needs graded A-modules.
2. **Generator maps (A4.c form).** Morphisms given by A^0-linear maps
   Q^p → T(Q)^{p+n} (⚠ 𝕏 is not: its component 𝕏^1 is a connection, only k-linear), T(Q)^m = ⊕_{q+p′=m} A^q ⊗ Q^{p′}; composition by the extension rule of §2.
   Index bookkeeping in the style of `CochainComplex.HomComplex.Cochain.v p q (h : p + n = q)`.
3. **Antweiler's twisted complexes over the cdg-category of modules with connections**
   [A, Def 3.1.12, Rem 4.0.4], with components in Hom^{a,b} = ⊕_p Hom^b(E^p, F^{p+a}) and the
   composition sign (−1)^{a′b}.

**Decision (v1.2, approved by the human after P1): encoding 1** is the definition.
- The total module is built from the generators, not given as free data:
  T = A ⊗[𝒜 0] (⨁ p, Q p), graded by total degree (a ⊗ e with a ∈ A^q, e ∈ Q^p has degree
  p + q). Mathlib provides `Module A`, `Module k`, `IsScalarTower k A` on it.
- 𝕏 : T →ₗ[k] T with Leibniz 𝕏(a·x) = da·x + (−1)^{|a|} a·𝕏x and flatness 𝕏∘𝕏 = c·(−).
  Building 𝕏 from generator data (A3.a) needs `TensorProduct.liftAddHom` (the map
  (a, e) ↦ da ⊗ e + (−1)^{|a|} a·𝕏e is A^0-balanced, not A^0-bilinear); this is done once.
- Lean: `Tot 𝒜 Q` is a `def` (not an `abbrev`) with its instances (`AddCommGroup`, `Module A`,
  `Module k`, `Module A⁰`, `IsScalarTower k A`) declared once in `Algebra/CohesiveDef.lean`. With
  an `abbrev`, instance search cannot find quotients of submodules of `Tot →ₗ[k] Tot` (needed
  for H⁰). `Ho(P_A)` is a one-field structure `HoP.as : CohesiveModule 𝒜`, so the category
  structure is not an instance on `CohesiveModule`.
- Hom^n(M₁, M₂): `k`-linear maps T₁ → T₂ of degree n with φ(a·x) = (−1)^{n|a|} a·φ(x), a
  `k`-submodule of `T₁ →ₗ[k] T₂` (blueprint A4 verbatim). Composition is composition of linear
  maps; δφ = 𝕏₂ ∘ φ − (−1)^n φ ∘ 𝕏₁. Prototype: `Scratch/P1_Encodings.lean`, Part C.
- Encoding 2 is the theorem A4.c (needed for A6, A11, C3). Encoding 3 appears only when
  transcribing [A, Prop 3.3.4] for A11, through a sign-dictionary lemma proved first.
- Reason: composition and δ in encoding 2 are defined through the extensions ψ̂, 𝕏̂, i.e.
  through encoding 1, so every proof would pass to encoding 1 anyway, with dependent-index
  bookkeeping on top.

## 5. Encoding graded algebras (decided in P1: internal ℤ-grading)
- **Decided:** internal grading, indexed by **ℤ**. A total k-algebra with
  `𝒜 : ℤ → Submodule k A` and `[GradedAlgebra 𝒜]` ✓, zero in negative degrees; equalities
  across degrees are checked in the total algebra, so no casts between `𝒜 (m + n + p)` and
  `𝒜 (m + (n + p))`. Signs are `Int.negOnePow`, as in `CochainComplex.HomComplex`.
- Lean: `class Cohesive.GCDga 𝒜` (A1, `Algebra/Dga.lean`); fields `N`, `zero_of_neg`,
  `zero_of_gt`, `gcomm`, `d`, `d_mem`, `leibniz`, `d_d`, `c`, `c_mem`, `d_c`.
- A^0 := ↥(𝒜 0), a commutative ring: `GCDga.commRing0`, built from graded commutativity
  (Mathlib's `SetLike.GradeZero.instCommRing` needs `A` commutative; when it is, the two agree
  at instance transparency). `A` is an `A^0`-algebra by `GCDga.algebra0` (A^0 is central).
  (v1.9) The sheaf 𝒜^0 of a presheaf of dgas has sections `CommRingCat.of ↥(𝒜_U 0)` and is
  a `RingSheaf` through `ringOf`; its global sections *are* A^0 (same type, same ring structure
  at instance transparency; prototype P7). Never introduce a second ring isomorphic to A^0.
  Tensor products over A^0 use Mathlib's `TensorProduct` (commutative base ✓); `A ⊗[𝒜 0] Q`
  gets `Module A`, `Module k`, `IsScalarTower k A` by instance search (checked in P1).
- Graded commutativity and boundedness are fields of the structure (no Mathlib class ✗).
- d: a k-linear map of the total algebra with d(𝒜 q) ⊆ 𝒜 (q+1), the graded Leibniz rule on
  homogeneous elements, and d ∘ d = 0.
- The Dolbeault algebra (F10) needs no direct-sum construction: it is the algebra of sections
  of one sheaf with the total fibre Λ^{0,•}(E) = Π_{q ≤ n} Λ^{0,q}(E; ℂ), product pointwise, and
  its grading is by components.

## 6. Forms
- E: finite-dimensional complex normed space, `E : Type`, n = dim_ℂ E. Its real structure is
  the instance `NormedSpace.complexToReal` ✓. J := multiplication by i, as an ℝ-linear map.
- Conjugate space: Ē = `Conj E`, a `def` type synonym of E with c • v := c̄ • v and the same
  norm. Antilinear maps on E are ℂ-linear maps on Ē; ℂ-linear maps of E are ℂ-linear on Ē too.
- Fibre: Λ^{0,q}(E; F) = `Conj E [⋀^Fin q]→L[ℂ] F`, Lean name `DolbeaultFibre E q F`
  (`Forms/Fibre.lean`); the bridge Φ_q from the exterior algebra is `extToFibre`/`extEquivFibre`,
  Φ_tot is `extEquivTotFibre`. Coordinate-free. **Decided in P2: keep
  `Conj E`; no fallback.** `Conj E` is a `def` with `Module.compHom E (starRingEnd ℂ)` and the
  norm of E. On Λ the ℝ-structure found by instance search equals `NormedSpace.complexToReal` at
  instance transparency (no diamond). The ℝ-structures of E and `Conj E` agree only
  propositionally; nothing takes `fderiv` on `Conj E` (D″ is built pointwise).
- Antilinear part of an ℝ-linear L : E → F: L″ = ½ (L + i·L ∘ J). On E = ℂ, D″f(1) = ∂f/∂z̄.
- D″ω(x) is regarded as a ℂ-linear map on Ē, and ∂̄ω(x) = `alternatizeUncurryFin` (D″ω(x)) over
  ℂ. No factorials, the same normalization as
  Mathlib's `extDeriv` ✓: dω(x; v₀, …, v_q) = Σ_i (−1)^i D_{v_i}ω(x; …, v̂_i, …).
- Product: transported from `ExteriorAlgebra ℂ (Dual_ℂ Ē)` along Φ, φ₁ ∧ ⋯ ∧ φ_q ↦
  (v ↦ det(φ_i(v_j))) (`exteriorPower.pairingDual`). This is the shuffle-sum product without
  factorials, and the Laplace formula φ ∧ ω = `alternatizeUncurryFin` (φ ⊗ ω) for a 1-form φ
  matches ∂̄'s normalization, so ∂̄ is a derivation of degree +1.
- dz̄ on E = ℂ is v ↦ v̄. Checks K2: ∂̄z̄ = dz̄, ∂̄z = 0, ∂̄|z|² = z·dz̄.
- Values: ℂ for the algebra. F-valued forms (later only) are a module over it via
  Λ^{0,q}(E; F) ≅ Λ^{0,q}(E; ℂ) ⊗ F.
- Charts: a section ω of 𝒜^{0,q}_M has ω(x) written in `chartAt x`. Changing to the chart φ
  uses ω(y) ∘ D(`chartAt y` ∘ φ⁻¹)(φ y). ∂̄ is computed in `chartAt x` and evaluated at x.
  (v1.18, audit F4) So the carrier `DolbeaultAlg E U` depends on the `chartAt` function of the
  `ChartedSpace` instance, not only on the maximal atlas (as Mathlib's `smoothSheaf` does); the
  theorem is quantified over the given instance. `chartExpr α e z` is meaningful only on
  `e.target ∩ e.symm ⁻¹' U` (`e.symm` is total, so elsewhere it is a junk value);
  `IsDolbeault` and `dbarSec` only read the germ at `e x ∈ e.target`.
- Holomorphic functions: complex `ContMDiff ∞` via `smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ, ℂ)` ✓.
  Cauchy–Riemann (F8) identifies them with real-smooth ∂̄-closed functions without
  several-variable Cauchy theory.

## 7. Sheaves, manifolds, universes
- **Smoothness exponents.** `⊤ : ℕ∞ω` is ω (analytic); C^∞ is `∞`. Complex manifolds are
  `IsManifold 𝓘(ℂ, E) ∞ X`; forms, smooth functions and partitions of unity are real `∞`.
  Never write `⊤` for smoothness.
- `X : Type` and `E : Type`. Reason: `smoothSheaf` ✓ needs the manifold and the value type in
  the same universe, and ℂ : Type.
- Cohesive and quasi-cohesive modules: each graded piece `Q p : Type` (so P_A, Ho(P_A) and the
  quantifier in H2 range over a fixed universe).
- Sheaves of modules: always write `SheafOfModules.{0} R` with `R : Sheaf _ RingCat.{0}`. A bare
  `SheafOfModules R` leaves the module universe free, and then the `IsGrothendieckAbelian` and
  `EnoughInjectives` instances are not found.
- **Abbreviation rule.** Every Mathlib constant that carries the module universe as an
  undetermined parameter (`SheafOfModules`, `overFunctor`, `pushforward`, `pullback`, `free`,
  `unit`, …) is used in project code only through a project `abbrev` that fixes it to `0`,
  e.g. `abbrev Mod R := SheafOfModules.{0} R` and
  `abbrev restr R U : Mod R ⥤ Mod (R.over U) := SheafOfModules.overFunctor.{0} R U`. Reason: an
  unfixed universe is generalized to a fresh parameter `u_1`; the needed instances (Grothendieck
  abelian, enough injectives, K-injective resolutions) exist only at level 0; error messages
  hide universes (use `set_option pp.universes true` when types look identical but do not match).
- Real-smooth ℂ-valued functions: `smoothSheafCommRing 𝓘(ℝ, E) 𝓘(ℝ, ℂ) M ℂ` needs the local
  instance `ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ` (absent from Mathlib; provided in F1) besides the
  realification of F1.
- Sheaves on `Opens X` with `Opens.grothendieckTopology X`. Rings for `SheafOfModules` are
  `RingCat`-valued; convert from `CommRingCat` with `forget₂`.
- Realification `IsManifold 𝓘(ℝ, E) ∞ X` is a theorem used as a local instance, never a global
  instance, to avoid search loops; the `ChartedSpace E X` instance is shared.
- **Restriction to opens (decided in P3):** `restr R U := SheafOfModules.overFunctor.{0} R U`,
  sheaves of modules over `R.over U` on the over-site `Over U`; use only this API (`Hom.over`,
  `overMap`, `overFunctorMap`; `SheafOfModules.IsLocallyFree` is also defined via over-sites).
  Pass to modules over `R|_U` on the space `U` only when needed, through
  `TopologicalSpace.Opens.sheafOfModulesEquivOver`. Restriction is exact because it has adjoints
  on both sides; `j_!` is its left adjoint.
  Lean traps: Mathlib's adjoint instances are stated for `pushforward (𝟙 _)` and `overFunctor`
  is a `def`. The left-adjoint instance transfers with `inferInstanceAs`; for the right-adjoint
  instance pass `PresheafOfModules.instIsRightAdjointPushforward (F := Over.forget U) …`
  explicitly (instance search does not unfold `(R.over U).obj`). Both become named instances in
  `Sheaf/Restriction.lean` (prototype: `Scratch/P3_Restriction.lean`).
- Derived categories: `DerivedCategory (SheafOfModules R)` ✓ with
  `attribute [local instance] HasDerivedCategory.standard` ✓; morphisms then live in a larger
  universe. Do not fight this; state results up to isomorphism.

## 8. Derived categories and perfect complexes
- D(R) = `DerivedCategory (SheafOfModules R)`, Q its localization functor.
- Strictly perfect: bounded, each term a direct summand of `SheafOfModules.free (Fin m)` ✓.
- Perfect: locally connected to a strictly perfect complex by a roof of quasi-isomorphisms
  K|U ← L → P. No derived category over U is needed.
- D_perf(X, R): full subcategory of D(R) on objects isomorphic to Q(K) with K perfect (an
  `ObjectProperty`).
- (v1.18, audit F3) The headline is Block's theorem in the *perfect* form. [B, Thm 4.1.3] states
  D^b_coh; [A, Thm 7.4.3] states D_perf, with D_perf ⊆ D^b_coh an embedding. Equality on a
  complex manifold (coherence of O_X) is Z1, not formalized.
- Homs into D: compute with a bounded-below injective resolution, `IsKInjective` ✓.

## 9. Statement-freezing policy
- (v1.22, 6 Nov 2026) Names: `MainStatement` (`Statements.lean`) is the canonical statement
  without hypotheses (formerly `MainStatementUnconditional`); `MainStatementConditional`
  (`StatementsConditional.lean`) is the original statement with H1, H2 as hypotheses (formerly
  `MainStatement`); `MainStatementTwisted` (`StatementsTwisted.lean`). Each statement file
  contains only its `def … : Prop` and imports frozen definitions. The bullets below predate the
  rename: in them `MainStatement` with hypotheses means `MainStatementConditional`.
- Freezes happen at the gates of blueprint §8: A3–A5, then S9.c, then F10, F12, H1, H2, then
  C1. After a freeze, changing a definition needs human approval.
- `MainStatement := ∀ E X [instances], DolbeaultGrothendieck E X → LocalGaugeLemma E X →
  (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
  (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X))`, with
  `blockFunctor E X : HoP (dolbeault E X) ⥤ DerivedCategory (Mod (ringOf (holSheaf E X)))`
  defined without H1, H2 (blueprint §1, C0.a).
- H1 and H2 are `Prop`-valued definitions passed as hypotheses. Never `axiom`.
- (v1.9) Spelling: `DolbeaultGrothendieck E X`, `LocalGaugeLemma E X` (`E` explicit: the
  model of `ChartedSpace` is not an `outParam`), `Perf (ringOf (holSheaf E X))`,
  `Mod (ringOf (holSheaf E X))` (v1.10: `ringOf`, since `holSheaf` is a `CommRingCat` sheaf).
  `Statements.lean` fixes `HasDerivedCategory.standard` once, for both `blockFunctor` and `Perf`.
- (v1.18, audit F1) **What is frozen:** exactly the term-dependency closure of the main
  statements (`MainStatement`, `MainStatementConditional`, `MainStatementTwisted`): the
  constants reached by unfolding them and their types (`scripts/statement_defs.py`). Instances
  on reached types (e.g. `HasShift (HoP 𝒜) ℤ`, `Pretriangulated`) are listed for information
  and not frozen. `MainStatement` (`Statements.lean`) is the canonical statement;
  `MainStatementConditional` is its corollary with H1, H2 as (now proved) hypotheses.
- (v1.18, audit F10) Frozen statement files may import theorem files, but use only
  `Prop`-valued terms from them (e.g. `dbar_dolbeaultRhoU` as the argument `hρ` of
  `fromComplex` in `Hypotheses.lean`): a rename breaks the build, never the meaning.

## 10. Notation dictionary
| Concept | [B] | [A] | [CHL] | Here (Lean, proposed) |
| --- | --- | --- | --- | --- |
| Cohesive modules | 𝒫_A | (A^∗, h)-Mod^coh | 𝒫_A ≃ Tw_perf(A) | `CohesiveModule 𝒜` |
| Homotopy category | Ho 𝒫_A | H^0(…) | H^0(…) | `HoP 𝒜` |
| Components of 𝔼 | 𝔼^k | 𝔼_k (plus ∇) | — | `E.comp k` |
| Quasi-cohesive | quasi-cohesive | quasi-cohesive | — | `QuasiCohesive 𝒜` |
| Sheafification functor | α | J | F = J ∘ p^∗ | `blockFunctor` (F15); `PreResolvingData.J` |
| The complex α(M) of sheaves | α(M) | J(M) | — | `P.sheafOf M`; sections `sheafOfSec`, map `sheafOfMap`, over `U` `sheafOfOver` (renamed from `α…`, 28 Oct 2026) |
| Ring of the comparison | 𝒪_X | R | ℛ | `holSheaf X` |
| Resolving algebra | 𝒜_X^{0,•} | A^∗ | 𝒜 | `dolbeault X` |
| Local lifting | proof of Lemma 4.1.5 | Assumption 6 | condition (\*) | `LocalLifting`, `LocalGaugeLemma X` |
| Perfect complexes | D_perf | D^B_perf | D^B_perf | `Perf X` |

## 11. Prototypes for phase 0
- **P1 Encodings.** A toy dga, e.g. A = k[ε]/(ε²) with |ε| = 1 and d = 0, and a two-term
  cohesive module. Implement §4 encoding 2 and §5 internal grading; prove δ² = 0 and
  associativity of composition on it. Decide §4 and §5 from how this goes.
  Second toy, to test the signs with d ≠ 0: A = k[t, ε]/(t², ε², tε), |t| = 0, |ε| = 1, dt = ε
  (Leibniz holds in every characteristic).
- **P2 Fibres.** Define `Conj E` with its normed ℂ-structure, Λ^{0,q}(E; F) and D″; check that
  `fderiv ℝ` of a Λ-valued map, the ℝ-structure of Λ and `alternatizeUncurryFin` over ℂ on Ē
  elaborate without instance diamonds; define Φ₁ and prove K2. If `Conj E` fights the instance
  system, switch to the subtype fallback of §6.
- **P3 Restriction.** Restrict a `SheafOfModules` to an open, prove exactness of restriction
  and restrict a complex; decide §7's API.

## 12. Sign acceptance tests
- δ² = 0 on P1's toy module; composition sign on two explicit degree-1 maps.
- Shift: Hom(M, N[1]) ≅ Hom(M, N)[1] with Mathlib's sign, using the shift rule of §2; check
  that 𝕏[1] satisfies Leibniz on the second P1 toy.
- K2–K4 of blueprint §9.
