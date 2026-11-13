import Cohesivemodules.ChecksMain

set_option linter.style.header false

/-!
# The functor `J` and Block's theorem

This page is an overview of the comparison layer and the assembly of the main theorem
(blueprint items C0–C7, F14–F15, the main statements M and Z5.j, and the intermediate corollary
Z4.h). It contains no declarations; the links below point to the files where the definitions
and theorems live.

## Overview

The main theorem of the project is Block's theorem in its perfect form ([[B][Block], Thm 4.1.3],
[[A][Antweiler], Thm 7.2.20 / 7.4.3 at `h = 0`]): for a compact complex manifold `X` with
Dolbeault algebra
`A = 𝒜_X(X)`, the functor `J : Ho(P_A) ⥤ D_perf(X, O_X)`, `M ↦ α(M)`, is an equivalence of
categories. It is the proposition `Cohesive.MainStatement`, proved as `main_theorem`:

```lean
def MainStatement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X],
      letI := HasDerivedCategory.standard (Mod (ringOf (holSheaf E X)))
      (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
        (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X))
```

Reading it part by part:
* `E` is a finite-dimensional complex normed space, the model of the charts. It is explicit
  everywhere because the model of `ChartedSpace` is not an `outParam`.
* `X` is a compact Hausdorff complex manifold modelled on `E`: `IsManifold 𝓘(ℂ, E) ∞ X` asks for
  complex `C^∞`, i.e. holomorphic, transition maps. The exponent is `∞`, not `⊤` (which is `ω`).
  `X : Type` and `E : Type` (conventions §7).
* `Cohesive.holSheaf` `E X` is `O_X`, the sheaf of complex-`C^∞` (holomorphic) functions, a
  sheaf of commutative rings; `Cohesive.ringOf` turns it into a `RingSheaf`, and `Cohesive.Mod` is
  `SheafOfModules.{0}` over it (see the *Dolbeault algebra* hub for `O_X` and the *Sheaves and
  perfect complexes* hub for `Mod`).
* `HasDerivedCategory.standard` fixes one model of the derived category
  `D(O_X) = DerivedCategory (Mod (ringOf (holSheaf E X)))`, the same one for the functor and for
  `Perf`.
* `Cohesive.blockFunctor` `E X : HoP (dolbeault E X) ⥤ D(O_X)` is the functor `J`: it sends a
  cohesive module `M` over the Dolbeault algebra `Cohesive.dolbeault` `E X` (see the
  *Cohesive modules* hub for `Cohesive.HoP` and the *Dolbeault algebra* hub for the algebra) to
  the complex of sheaves `α(M)`.
* `Cohesive.Perf` `R` is `D_perf(X, R)`: the objects of `D(R)` isomorphic to `Q K` for a perfect
  complex `K` (`Cohesive.IsPerfect`, locally quasi-isomorphic to a strictly perfect complex;
  *Sheaves and perfect complexes* hub).
* "Equivalence onto `D_perf`" is written as `Full ∧ Faithful ∧ essImage = Perf`, with Mathlib's
  `CategoryTheory.Functor.Full`, `CategoryTheory.Functor.Faithful` and
  `CategoryTheory.Functor.essImage`. ⚠ `J` lands in the whole derived category: that it lands in
  `D_perf` is C2, which needs the local lifting property, so a functor into `D_perf` cannot be
  defined without H2, whereas the statement (and its conditional form, where H2 is a hypothesis)
  must name `J` beforehand. The corestriction form is equivalent (K6, below).

`Cohesive.MainStatementConditional` is the same statement with the hypotheses
`Cohesive.DolbeaultGrothendieck` `E X` (H1) and `Cohesive.LocalGaugeLemma` `E X` (H2), added as
implications `DolbeaultGrothendieck E X → LocalGaugeLemma E X →` after the manifold binders and
before the `letI`; everything else is verbatim.
It was the project's first formalized main statement (frozen at gate 5), used
while H1 and H2 were unproved, and is proved as `main_theorem_conditional`. Both hypotheses are
now theorems (`Cohesive.dolbeaultGrothendieck`, see the *Dolbeault–Grothendieck lemma* hub;
`Cohesive.localGaugeLemma`, see the *Local gauge lemma* hub), so the conditional statement is a
corollary.

**Names (v1.22).** Until 6 Nov 2026 the names were swapped: the conditional statement was
`MainStatement` (theorem `main_theorem`, file `Statements.lean`) and the canonical one
`MainStatementUnconditional`
(theorem `main_theorem_unconditional`, file `StatementsUnconditional.lean`). The `def` bodies are
unchanged; older gate sheets, blueprint history entries and dated PROGRESS entries use the old
names.

**Strategy.** The proof is abstract. *Resolving data* (C0) axiomatize what is used of the
Dolbeault resolution `O_X → 𝒜^{0,•}`: a presheaf of bounded dgas `𝒜(U)` with fine `𝒜⁰` and
locally free `𝒜^q`, a sheaf of commutative rings `O` (as a `RingSheaf`, `R = ringOf O`) with
`ρ : O → 𝒜⁰`, `d ∘ ρ = 0`, such that `O → 𝒜⁰ → 𝒜¹ → ⋯` is a resolution, and local lifting (LL).
For such data
the comparison theorem `Cohesive.ResolvingData.comparison` (C6,
[[A][Antweiler], Thm 7.2.20 at `h = 0`], [[CHL][ChuangHolsteinLazarev], Thm 7.10]) proves `J`
full, faithful, with essential image `Perf`. F14 shows that the
Dolbeault data are resolving data given H1 (exactness in degrees `≥ 1`) and H2 (LL), and F15
applies C6.

## Main definitions

* `Cohesive.DgaPresheaf`, `Cohesive.DgaPresheaf.pre0`: presheaves of bounded graded-commutative,
  possibly curved `ℂ`-dgas on `Opens X`, and the presheaf of commutative rings `U ↦ 𝒜⁰(U)` of
  their degree-`0` parts (the only spelling of `𝒜⁰`, so `Γ(X, 𝒜⁰)` and `A⁰` are the same type)
  (C0).
* `Cohesive.PreResolvingData` (C0.a): a dga presheaf whose sections glue and whose degree is
  local, with `𝒜⁰` a sheaf of commutative rings, curvature `c = 0`, a sheaf of commutative rings
  `O` with natural ring maps `ρ_U : O(U) →+* 𝒜⁰(U)` and `d ∘ ρ = 0`, `𝒜⁰` fine, and each `𝒜^q`
  locally free of finite rank over `𝒜⁰`. `Cohesive.PreResolvingData.R` is `ringOf O` (written
  `R` below), and `Cohesive.PreResolvingData.𝒜X` is the global dga `𝒜(X)`.
* `Cohesive.ResolvingData` (C0.b): in addition `O → 𝒜⁰ → 𝒜¹ → ⋯` exact and the local lifting
  property `Cohesive.ResolvingData.LL`.
* `Cohesive.PreResolvingData.sheafOf` (C1): the complex of sheaves `α(M)`; terms
  `Cohesive.PreResolvingData.sheafOfSh` (sheaf condition C1.a,
  `Cohesive.PreResolvingData.isSheaf_sheafOfPre`), differential
  `Cohesive.PreResolvingData.sheafOfD`, maps `Cohesive.PreResolvingData.sheafOfMap`.
* `Cohesive.PreResolvingData.JK`, `Cohesive.PreResolvingData.J` (C1.b): `J` into the homotopy
  category and into the derived category, `J = JK ⋙ DerivedCategory.Qh`.
* `Cohesive.PreResolvingData.sheafOfOver`, `Cohesive.PreResolvingData.restrSheafOfIso` (C1.c):
  `α` on the over-site of an open `U`, and `α(M)|U ≅ α_U(M|U)`.
* `Cohesive.PreResolvingData.ℋ` (C3): the Hom complex of sheaves `V ↦ Hom^•(M₁|V, M₂|V)`,
  spelled as degree-`n` maps `Tot(M₁) → Tot(M₂|V)` semilinear along `res_V` (canonically the
  same). ⚠ Its terms are `𝒜⁰`-modules, but its differential is not `𝒜⁰`-linear.
* `Cohesive.PreResolvingData.Conn`, `Cohesive.PreResolvingData.Conn.TC`,
  `Cohesive.PreResolvingData.Ξ` (C7). For a complex `K` of `R|U`-modules and `F = 𝒜⁰ ⊗_R K`:
  `Conn` is a flat `𝒜`-connection on `F`, `Conn.TC` the complex `T(K)` it defines (the explicit
  model of `𝒜 ⊗_R K`, built from plain tensor products of sections), and `Ξ` the comparison map
  `Ξ_e : α_U(M) → T(K)`.
* `Cohesive.dolbeaultPresheaf`, `Cohesive.dolbeaultPreData` (F14, C0.a): the Dolbeault data,
  without hypotheses; `Cohesive.dolbeaultData` (F14, C0.b) completes them given H1 and H2.
* `Cohesive.blockFunctor` (F15): `J` for the Dolbeault data (`Cohesive.blockFunctor_eq`).
* `Cohesive.MainStatement`, `Cohesive.MainStatementConditional` (Z5.j, M).

## Main results

All results of C2–C7 assume `X` compact Hausdorff (⚠ blueprint §11 v1.11: C2 and step 3 of C4 use
it through the explicit model C7), and so do `Cohesive.dolbeaultPreData` and
`Cohesive.blockFunctor` (fineness of `𝒜⁰` is a field of C0.a).

* `Cohesive.ResolvingData.isPerfect_sheafOf`, `Cohesive.ResolvingData.perf_J_obj` (C2,
  [[A][Antweiler], Lemma
  7.2.17]): `α(M)` is perfect, so `J M ∈ D_perf`.
* `Cohesive.ResolvingData.full_J`, `Cohesive.ResolvingData.faithful_J` (C4,
  [[A][Antweiler], Prop 7.2.19]):
  through `Cohesive.PreResolvingData.Ψ : ℋ(M₁, M₂) ⟶ 𝓗om(α M₁, α M₂)`, a quasi-isomorphism after
  composing with an injective resolution (`Cohesive.ResolvingData.quasiIso_Ψ_comp`), and
  `Cohesive.ResolvingData.bijective_J_map`.
* `Cohesive.ResolvingData.exists_J_obj_iso` (C5, [[A][Antweiler], Prop 7.2.18], ⚠ K-flat
  variant): every
  perfect complex is isomorphic in `D(R)` to some `J M`; steps
  `Cohesive.ResolvingData.exists_flat_model` (bounded above, flat terms) and
  `Cohesive.ResolvingData.exists_sheafOfMap_quasiIso` (via the lifting theorem A11 of the
  *Cohesive modules* hub).
* `Cohesive.PreResolvingData.quasiIso_Ξ`, `Cohesive.PreResolvingData.exists_TC_iso_tensorC`,
  `Cohesive.ResolvingData.quasiIso_ιT` (C7.f, C7.d): `Ξ_e` is a quasi-isomorphism when its
  form-degree-`0` part is, `T(K) ≅ 𝒜 ⊗_R K`, and `K → T(K)` is a quasi-isomorphism for `K`
  K-flat.
* `Cohesive.ResolvingData.comparison` (C6): for resolving data on a compact Hausdorff space,
  `D.J.Full ∧ D.J.Faithful ∧ D.J.essImage = Perf D.R`, for any `HasDerivedCategory` instance.
* `Cohesive.blockPerf` (F15): the conclusion for `blockFunctor E X` given H1 and H2, any
  `HasDerivedCategory` instance; `main_theorem_conditional : MainStatementConditional`.
* `Cohesive.blockPerf_of_localGaugeLemma`, `main_theorem_of_localGaugeLemma` (Z4.h): H1 removed.
* `Cohesive.blockPerf_unconditional`, `main_theorem : MainStatement` (Z5.j): no hypotheses.
* K6 (`ChecksMain.lean`): `Cohesive.Checks.full_faithful_essImage_iff` (for a property closed
  under isomorphism, full + faithful + essential image `P` iff `F` lands in `P` and the
  corestriction is an equivalence); `Cohesive.Checks.blockFunctor_iff` (without hypotheses: the
  conclusion of `MainStatement` for `blockFunctor E X` is equivalent to the corestriction form);
  and `Cohesive.Checks.isEquivalence_blockFunctor_lift` (given H1 and H2: `blockFunctor E X`
  lands in `D_perf` and its corestriction `Ho(P_A) ⥤ D_perf(X, O_X)` is an equivalence).
  K1: `Cohesive.Checks.blockPerf_dim_zero`.

## Conventions and signs

**What `α(M)` is.** For pre-resolving data `P` and a cohesive module `M = (Q, 𝕏)` over
`A = 𝒜(X)`, `α(M)^n(V)` is the degree-`n` part of the total module `Tot(M|V)` of the base change
of `M` along `res : 𝒜(X) → 𝒜(V)` (A9; `Cohesive.PreResolvingData.TotSec`,
`Cohesive.PreResolvingData.sheafOfSec`). ⚠ This is
`𝒜(V) ⊗_{𝒜⁰(V)} ⨁_p (𝒜⁰(V) ⊗_{𝒜⁰(X)} Q^p)` in degree `n`, canonically isomorphic to the
blueprint's `⊕_{p+q=n} 𝒜^q(V) ⊗_{𝒜⁰(X)} Q^p`; the spelling reuses A9's differential and its
functoriality `bcHomL`. `O(V)` acts through `ρ_V`. The restriction maps are `Cohesive.bcTotRes`,
`b ⊗ (β ⊗ q) ↦ res(b) ⊗ (res(β) ⊗ q)`. The differential is the operator `𝕏` of `M|V`; it is
`O`-linear because `d ∘ ρ = 0`, and squares to zero because `c = 0` (a field of C0.a).
* On morphisms: a closed degree-`0` map `φ` goes to `α(φ)`, on `α(M)^n(V)` the base change
  `bcHomL (res) 0 φ`, i.e. `a ⊗ e ↦ a·φ(1 ⊗ e)` with no sign. A coboundary `δh`,
  `h ∈ Hom^{-1}`, goes to a null-homotopic map with homotopy `bcHomL (res) (-1) h`
  (`Cohesive.PreResolvingData.sheafOfMap_homotopic`), so `J` is well defined on `H⁰`.
* Hom differential and degree conventions are those of the *Cohesive modules* hub
  (`δφ = 𝕏₂ ∘ φ − (−1)^n φ ∘ 𝕏₁`,
  Mathlib's `CochainComplex.HomComplex.δ`).
* Sheaf tensor products with `𝒜^•` put `𝒜^•` **first** (`tensorC R 𝒜^• K`), so that
  `db ⊗ k + (−1)^{|b|} b ⊗ dk` is a left-module connection (C5.a, C7.c; conventions §2).

**Derived category and universes.**
* `D(R) = DerivedCategory (Mod R)` with `Mod R = SheafOfModules.{0} R` (module universe fixed to
  `0`, conventions §7). `J`, `Perf`, `comparison` and `blockPerf` take a
  `HasDerivedCategory.{w}` instance as an argument; the frozen statements fix
  `HasDerivedCategory.standard` once, by `letI`, for both `blockFunctor` and `Perf`. Its
  morphisms live in a larger universe than those of `Mod R` (universe `1`); this is why
  `Cohesive.perf_Q_obj_iff'` is stated for every universe `w`.
* `blockFunctor` passes the instance to `Cohesive.PreResolvingData.J` explicitly: instance search
  does not unfold `(dolbeaultPreData E X).R` to `ringOf (holSheaf E X)`, though the two are equal
  by `rfl` (`Cohesive.dolbeaultPreData_R`).

**`O_X` and the Dolbeault data.** `O_X = holSheaf E X` (complex-`C^∞` functions, a `CommRingCat`
sheaf), used as `ringOf (holSheaf E X)`; `ρ_U` is the inclusion of holomorphic functions into
`𝒜^{0,0}(U)`. In the Dolbeault data `c = 0` holds by definition (F10).

**Axioms.** `#print axioms` of `main_theorem`, `main_theorem_conditional`, `Cohesive.blockPerf`,
`Cohesive.blockPerf_unconditional` and the Z4.h corollaries list only `propext`,
`Classical.choice`, `Quot.sound` (checked with `#guard_msgs` in `ChecksMain.lean`). In
`MainStatementConditional`, H1 and H2 are hypotheses, never axioms.

## Implementation notes

* **Pre-resolving vs resolving.** C0 is split so that `J` (C1) needs only C0.a: `blockFunctor` is
  defined without H1 and H2, and the frozen statement can quantify over all `X`.
* **Deviations from [[A][Antweiler]], ⚠.** LL is required only for global cohesive modules
  restricted to opens (sectionwise form of [[A][Antweiler], Assumption 6], also the form of
  Block's gauge step); the first half of [[A][Antweiler], Assumption 5] (`𝒜` K-flat over `R`,
  Malgrange) is not assumed: C5 uses K-flat
  resolutions (S8). D_perf replaces D^b_coh of [[B][Block]]; their equality is Z1 (LATER).
* **C7 replaces sheafified tensor products**, whose sections are not computable, by the explicit
  model `T(K)` with plain tensor products of sections (v1.11); C2, C4 step 3 and C5.a–c go
  through it.
* **Global names.** `main_theorem`, `main_theorem_conditional` and
  `main_theorem_of_localGaugeLemma` are in the root namespace, not in `Cohesive`.
* **Frozen files.** `Comparison/SetupDef.lean` (C0), `Algebra/BaseChangeResDef.lean`,
  `Algebra/BaseChangeHomDef.lean`, `Algebra/GenHomDef.lean`, `Comparison/AlphaDef.lean`,
  `Comparison/FunctorDef.lean` (C1), `BlockFunctorDef.lean` (F14–F15), `Hypotheses.lean` (H1,
  H2), `Statements.lean` and `StatementsConditional.lean` are in the term-dependency closure of
  the statements and frozen; theorems about them are in separate files. The full list, for all
  layers, is `review/statement-defs.md`.

## Files

* `Comparison/SetupDef.lean`, `Comparison/Setup*.lean` (C0).
* `Algebra/BaseChangeRes*.lean`, `Comparison/AlphaDef.lean`, `Comparison/AlphaSheaf*.lean`,
  `Comparison/FunctorDef.lean`, `Comparison/AlphaOver*.lean` (C1).
* `Comparison/Perfect*.lean` (C2), `Comparison/HomSheaf*.lean` (C3),
  `Comparison/FullyFaithful*.lean` (C4), `Comparison/EssSurj*.lean` (C5),
  `Comparison/Equivalence.lean` (C6), `Comparison/Model*.lean` (C7).
* `BlockFunctorDef.lean` (F14 C0.a, F15), `Main.lean` (F14 C0.b, F15, M), `MainH1.lean` (Z4.h),
  `MainH2.lean` (Z5.j).
* `Statements.lean`, `StatementsConditional.lean` (the frozen statements); `Hypotheses.lean`
  (H1, H2; see the *Dolbeault–Grothendieck lemma* and *Local gauge lemma* hubs);
  `ChecksComparison.lean`, `ChecksMain.lean` (§9 checks).
* The `Twisted*`, `TwistDatum*`, `Curved*`, `SheafData*` and `Gauge*` files of `Comparison/`
  belong to the *Twisted theorem* hub.

## References

* [[B][Block]] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2, §4.1, Thm 4.1.3, Lemma 4.1.5.
* [[A][Antweiler]] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1, §7.2 (Assumptions 7.2, Def 7.2.3, Lemma 7.2.17,
  Props 7.2.18–7.2.19, Thm 7.2.20) and Thm 7.4.3 at `h = 0`.
* [[CHL][ChuangHolsteinLazarev]] J. Chuang, J. Holstein, A. Lazarev, *Maurer–Cartan moduli and
  theorems of
  Riemann–Hilbert type*, Appl. Categ. Struct. 29 (2021); numbering of arXiv 1802.02549v3:
  Thm 7.10, Prop 7.4.
* Blueprint: `blueprint/blueprint.md` §1 (M), §4 (C0–C7), §5 (F14–F15), §9 (K1, K6), §11 (v1.11,
  v1.15, v1.18, v1.22); conventions: `blueprint/conventions.md` §2, §7–§9.
-/
