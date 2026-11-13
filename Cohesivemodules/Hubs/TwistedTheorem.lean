import Cohesivemodules.MainTwisted
import Cohesivemodules.ChecksTwistedK8
import Cohesivemodules.ChecksCurvedZero
import Cohesivemodules.Forms.TwistExists
import Cohesivemodules.Forms.CurvedLL

set_option linter.style.header false

/-!
# The twisted theorem: curved cohesive modules and twisted perfect complexes

This page is an overview of the twisted form of Block's theorem (blueprint item Z3, Z3.a–Z3.v,
`blueprint/blueprint-tw.md`). It contains no declarations; the links below point to the files
where the definitions and theorems live.

## Overview

For a `∂̄`-closed form `h ∈ 𝒜^{0,2}(X)` the Dolbeault algebra becomes a *curved* algebra
`(𝒜_X(X), ∂̄, h)`, and cohesive modules over it satisfy `𝕏 ∘ 𝕏 = h·(−)`. The sheaves `α(M)`
attached to them are no longer complexes, but on each open `U_α` of a cover with
`h|U_α = ∂̄h⁰_α` the gauge change `𝕏 ↦ 𝕏 − h⁰_α` makes them flat. These local complexes glue,
by units `u_αβ`, up to a Čech 2-cocycle `ȟ` of units of `O_X`: they form a complex of
`ȟ`-twisted sheaves. The theorem says that this construction identifies `Ho(P_A)` with the twisted
perfect complexes ([[A][Antweiler], Thm 7.4.3]; stated without proof in [[B][Block], Thm 4.2.1]).

The pieces:
* **Curved algebras** (Z3.a). `Cohesive.GCDga.withC` replaces the curvature of a gc dga by a
  closed `c' ∈ A²`, on the same carrier; `Cohesive.DgaPresheaf.withCurvature` does this for a
  presheaf of dgas (curvature `h|U` on `U`). `Cohesive.DgaSheafData` is
  `Cohesive.PreResolvingData` (*Block's theorem* hub) without its field `c = 0`, so curved data
  can carry the sheaf structure (`Cohesive.PreResolvingData.toSheafData`,
  `Cohesive.DgaSheafData.withCurvature`).
* **Gauge** (Z3.b). `Cohesive.CohesiveModule.gauge` turns a module over `(𝒜, c + dβ)` into one
  over `(𝒜, c)` with operator `𝕏 − β·`; the Hom complexes agree (`Hom^n` by `rfl`,
  `Cohesive.gauge_hom`; `δ` on `Hom^n`, `Cohesive.gauge_δ`), whence an equivalence
  `Cohesive.gaugeHoP`.
* **Curved Dolbeault algebra and twist data** (Z3.c–d). `Cohesive.DolbeaultClosed2`,
  `Cohesive.curvedDolbeault`; `Cohesive.TwistCocycle`, `Cohesive.TwistDatum`,
  `Cohesive.TwistData`, and the existence theorem `Cohesive.exists_twistData`.
* **Twisted sheaves** (Z3.f–l′, Z3.r).
  The abelian category `Cohesive.TwMod` of `ȟ`-twisted sheaves of
  modules, with enough injectives, gluing for `ȟ = 1`, rescaling, extension by zero, base change
  and twisted Hom sheaves; twisted perfect complexes `Cohesive.TwPerf`.
* **The functor** `J_T` (Z3.m–o) and the theorem (Z3.p–v): `Cohesive.twistedBlockFunctor`,
  `Cohesive.MainStatementTwisted`, `Cohesive.main_theorem_twisted`.

## The statement

`Cohesive.MainStatementTwisted` (`StatementsTwisted.lean`, frozen at gate 12) reads:
```
def MainStatementTwisted : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X] (h : DolbeaultClosed2 E X) (T : TwistData E X h),
      letI := HasDerivedCategory.standard (TwMod (dolbeaultPreData E X).toSheafData.O T.U T.ch)
      (twistedBlockFunctor h T).Full ∧ (twistedBlockFunctor h T).Faithful ∧
        (twistedBlockFunctor h T).essImage = TwPerf (dolbeaultPreData E X).toSheafData.O T.U T.ch
```
* `X` is a compact Hausdorff complex manifold modelled on `E` (smoothness `∞`, not `ω`), as in
  `Cohesive.MainStatement` (*Block's theorem* hub).
* `h : DolbeaultClosed2 E X` is a global Dolbeault form of form degree `2` (bidegree `(0,2)`)
  with `∂̄h = 0`. The source category is `Ho(P_A)` (`Cohesive.HoP`, *Cohesive modules* hub)
  for the curved Dolbeault algebra `A = Cohesive.curvedDolbeault h = (𝒜_X(X), ∂̄, h)`, whose
  curvature is `h` (`Cohesive.curvedDolbeault_c`).
* `T : TwistData E X h` is a twist datum (`Cohesive.TwistDatum` over the Dolbeault data): a
  finite open cover `T.U`, primitives `h⁰_α ∈ 𝒜^{0,1}(U_α)` with `∂̄h⁰_α = h|U_α`, units
  `u_αβ ∈ 𝒜⁰(U_α ∩ U_β)ˣ` with `∂̄u_αβ = (h⁰_β − h⁰_α)u_αβ`, `u_αα = 1`, `u_βα = u_αβ⁻¹`, and a
  normalized Čech 2-cocycle `T.ch = ȟ` of units of `O_X` with `ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹`,
  where `ρ : O_X → 𝒜⁰` is the inclusion. ⚠ The normalization and the cocycle condition of `ȟ`
  are fields, although they follow from the other data and the injectivity of `ρ`. Every `h` has
  a twist datum (`Cohesive.exists_twistData`), so the statement is not vacuous.
* `TwMod O_X T.U T.ch` (`Cohesive.TwMod`) is the abelian category of `ȟ`-twisted sheaves of
  `O_X`-modules; `O_X` is spelled `(dolbeaultPreData E X).toSheafData.O`, which is
  `holSheaf E X` by `rfl` (`Cohesive.dolbeaultPreData_toSheafData_O`). The derived category is
  Mathlib's `HasDerivedCategory.standard`, the same for the functor and for `TwPerf`.
* `TwPerf` (`Cohesive.TwPerf`) is the class of objects isomorphic to `Q K` with `K` twisted
  perfect: each component complex `K_α` on the over-site `Over U_α` is perfect
  (`Cohesive.TwIsPerfect`, `Cohesive.IsPerfectOver`). ⚠ The condition is componentwise (the
  gluing maps play no role), and it uses local roofs of quasi-isomorphisms instead of
  isomorphisms in `D(O|W)` (equivalent).
* `twistedBlockFunctor h T` (`Cohesive.twistedBlockFunctor`, which is
  `Cohesive.TwistDatum.twistedJ` of the Dolbeault data) sends `M` to the complex of twisted
  sheaves whose components are the sheaves `α(M)^n` of the *Block's theorem* hub (in a copy for
  curved data) restricted to `U_α`, with differential `𝕏 − h⁰_α` and gluing `u_αβ·`
  (`Cohesive.TwistDatum.twistedSheafOf`).
* The conclusion "equivalence onto `TwPerf`" is stated as full, faithful, and essential image
  equal to `TwPerf`.

⚠ **Deviations from the sources** (repeated from the docstrings of `StatementsTwisted.lean` and
`TwistedBlockFunctorDef.lean`; blueprint-tw §2.4):
* The statement is per twist datum `T` (finite cover, normalized `ȟ`, antisymmetric `u`,
  multiplicative data `(h⁰, u, ȟ)` instead of [[A][Antweiler]]'s `(h⁰, h¹, h², exp_ℛ)`); a datum
  exists for
  every `h`; **independence of `T` is LATER**.
* Twisted `O_X`-modules only, with no intermediate category of cdg-modules; left modules, with
  curvature `c = h_[A] = −B_[B]`, and no factor `2πi`.
* `D_perf` (`TwPerf`) instead of [[A][Antweiler]]/[[B][Block]]'s `D^b_coh` (the comparison needs
  Oka; that is Z1).
* The generic gauge assumes `IsUnit (2 : k)` (true for `k = ℂ`).
* Gluing by the units `u_αβ·`, where [[A][Antweiler]]'s definition of `J` glues by `exp(h¹_αβ)`. The
  differential `𝕏 − h⁰_α` is [[A][Antweiler]]'s `d_α = d|U_α − h⁰_α` (same sign;
  [[A][Antweiler]]'s `+ h⁰_α` belongs to the
  inverse, untwisting construction).
* Twisted sheaves glue by maps `φ_αβ` on sections over every open `W ≤ U_α ∩ U_β`, not by
  isomorphisms of sheaves `M_α|U_α ∩ U_β → M_β|U_α ∩ U_β` as in [[A][Antweiler], Def 7.1.2] and
  [[Căldăraru][Caldararu2000]].

## Main definitions

* `Cohesive.GCDga.withC`, `Cohesive.DgaPresheaf.withCurvature`, `Cohesive.DgaSheafData` (Z3.a).
* `Cohesive.QuasiCohesive.gauge`, `Cohesive.CohesiveModule.gauge`, `Cohesive.gaugeHoP` (Z3.b).
* `Cohesive.DolbeaultClosed2`, `Cohesive.curvedDolbeaultPresheaf`, `Cohesive.curvedDolbeault`;
  `Cohesive.TwistCocycle`, `Cohesive.TwistDatum`, `Cohesive.TwistData`; the special data
  `Cohesive.trivialTwistDatum` (`h = 0`) and `Cohesive.exactTwistDatum` (`h = ∂̄β`) (Z3.c).
* `Cohesive.restrOver` (restriction between over-sites, Z3.f); `Cohesive.TwMod`,
  `Cohesive.TwMod.Hom`, `Cohesive.TwMod.comp` (Z3.g), with its `Abelian` instance (Z3.h).
* `Cohesive.push` (Toda's twisted pushforward, Z3.i); `Cohesive.IsPerfectOver`,
  `Cohesive.TwIsPerfect`, `Cohesive.TwPerf` (Z3.j); `Cohesive.glue`, `Cohesive.glueEquiv`,
  `Cohesive.rescale` (Z3.k); `Cohesive.extTw` (Z3.l); `Cohesive.twBC` (base change, Z3.l′).
* `Cohesive.homTw`, `Cohesive.twHomComplex` (twisted Hom sheaves, Z3.r);
  `Cohesive.DgaSheafData.ℋ` (curved C3, Z3.q).
* `Cohesive.TwistDatum.twTerm`, `Cohesive.TwistDatum.twDiff`, `Cohesive.TwistDatum.twistedSheafOf`,
  `Cohesive.TwistDatum.twistedJK`, `Cohesive.TwistDatum.twistedJ` (Z3.n);
  `Cohesive.twistedBlockFunctor`, `Cohesive.MainStatementTwisted` (Z3.v).

## Main results

* `Cohesive.main_theorem_twisted : MainStatementTwisted` (Z3.v), assembled from
  `Cohesive.full_twistedJ_dolbeault`, `Cohesive.faithful_twistedJ_dolbeault` (Z3.s) and
  `Cohesive.essImage_twistedBlockFunctor`, which combines `Cohesive.twIsPerfect_twistedSheafOf`
  (Z3.p) with `Cohesive.exists_twistedJ_obj_iso` (Z3.u).
* `Cohesive.exists_twistData` (Z3.d): every closed `h ∈ 𝒜^{0,2}(X)` on a compact Hausdorff `X`
  has a twist datum (`Cohesive.exists_cover_primitives`, `Cohesive.twistData_of_primitives`,
  with `Cohesive.expUnit`). It uses only local H1, no Leray cover.
* `Cohesive.gaugeHoP` (Z3.b): `Ho(P_{(𝒜, c + dβ)}) ≌ Ho(P_{(𝒜, c)})`, identity on morphisms.
* `Cohesive.curvedLL`, `Cohesive.localGaugeLemmaOpen` (Z3.e): H2 over opens, applied to
  `gauge_{h⁰_α}(M|U_α)` (⚠ [[A][Antweiler]] states it for the curved `M|U′`; equivalent by the
  gauge).
* `Cohesive.enoughInjectives` (with `Cohesive.pushAdj`), `Cohesive.extTwAdj`,
  `Cohesive.glueEquiv` (for a cover, `⨆ U_α = ⊤`: `TwMod R U 1 ≌ Mod R`) (Z3.i–l).
* `Cohesive.twLocalIso` (Z3.o): `J_T(M)_α ≅ α_{U_α}(gauge_{h⁰_α}(M|U_α))`, the bridge to the
  flat theory of the *Block's theorem* hub on each `U_α`.
* `Cohesive.bijective_twistedJ_map` (Z3.s): for resolving data on a compact Hausdorff `X`
  satisfying H2 over opens (`Cohesive.LLOpen`), and any twist datum, `J_T` is bijective on
  morphisms; `Cohesive.llOpen_dolbeault` discharges
  `LLOpen` for the Dolbeault data.
* Checks: `Cohesive.K14_exact_iff` (at `h = ∂̄β` and `exactTwistDatum β`, the twisted conclusion
  is equivalent to the untwisted one) and `Cohesive.K8_twisted_implies_unconditional`
  (`MainStatementTwisted → MainStatement`). K12 (`ChecksCurved.lean`) is a curved toy dga with
  `c ≠ 0` and a cohesive module; K12b `Cohesive.Checks.isZero_czHoP`: for `k[c]/(c²)` with curvature
  `c`, every object of `Ho(P)` is zero.

**Proof in brief** (blueprint-tw §3 A–H). Twisted sheaves have no global sections, so every
global step (softness, globalization, lifting) acts on untwisted objects; every local step is the
flat theory of the *Block's theorem* hub on `U_α`, after the gauge by `h⁰_α`. Full faithfulness
uses an injective resolution in `TwMod`, the curved Hom sheaf `ℋ^h` and the twisted Hom sheaf.
Essential surjectivity base-changes a flat model to `𝒜⁰`, untwists it by `u⁻¹` and glues it into
a perfect complex of `𝒜⁰`-modules on `X`, glues the local connections plus `h⁰_α` to a curved
connection, and lifts by A11, which holds for any
curvature (*Cohesive modules* hub).

## Conventions and signs

**Curvature.** Left modules: `𝕏 ∘ 𝕏 = c·(−)` with `c = h`. This is `h` of
[[A][Antweiler], Rem 4.0.4] and
`−B` for Block's `B` ([[B][Block], §4.2], right modules; A13). There is no factor `2πi` anywhere.

**Cocycle orientation.** For `φ_αβ : M_α → M_β` on `U_α ∩ U_β`, the twisted cocycle is
`φ_βγ ∘ φ_αβ = ȟ_αβγ · φ_αγ` on every `W ≤ U_α ∩ U_β ∩ U_γ` (field `cocycle` of `TwMod`). This
corrects [[A][Antweiler], Def 7.1.1], whose `φ_αβ ∘ φ_βγ = ȟ φ_αγ` does not typecheck (audit
a1). It matches
`ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹` in `TwistDatum`. The gluing maps of
[[Căldăraru][Caldararu2000], Def 1.2.1] run the other way, `φ_ij : F_j → F_i` on `U_ij`; read
his `φ_ij` as our `φ_ji`. The Čech condition in `TwistCocycle` is
`ȟ_βγδ ȟ_αγδ⁻¹ ȟ_αβδ ȟ_αβγ⁻¹ = 1`, again on every open inside the four members.

**Normalization.** `ȟ_αβγ = 1` whenever two indices coincide (field `normalized`), and
`φ_αα = id` is a field of `TwMod` (`φ_self`). ⚠ Without that field `φ = 0` satisfies all other
axioms; [[A][Antweiler]] only gets `φ_αα` idempotent. With it and `ȟ_αβα = 1`,
`φ_βα ∘ φ_αβ = id`, so the
`φ_αβ` are bijective. The units satisfy `u_αα = 1`, `u_βα = u_αβ⁻¹`.

**Gauge.** For `c' = c + dβ`, `β ∈ A¹`: `gauge M β = (M.Q, 𝕏 − β·)`, with
`(𝕏 − β)² = c' − dβ + β² = c` (Leibniz `𝕏(βx) = dβ·x − β𝕏x`; `β² = 0` because `β² = −β²` and
`2` is a unit). The inverse is `𝕏 + β·`. Hom complexes and `δ` agree (the `β`-terms cancel since
`φ(βx) = (−1)^n βφ(x)`). In `J_T` the gauge is `𝕏 ↦ 𝕏 − h⁰_α` on `U_α`, so
`(𝕏 − h⁰_α)² = h − ∂̄h⁰_α = 0`, and `u_αβ(𝕏 − h⁰_α)u_αβ⁻¹ = 𝕏 − h⁰_β` follows from
`∂̄u_αβ = (h⁰_β − h⁰_α)u_αβ`. The units `u` and `ȟ` are the data, where
[[A][Antweiler], Def 7.2.2] has
`u = exp h¹`, `ȟ = exp_ℛ h²` (deviation recorded in `Comparison/TwistDatumDef.lean`).
Dictionary with [[B][Block], §2.7]: `(f, ω) = (id, β)`, sign reversed for left modules.

**`h = 0`.** The curved instance at `h = 0` is *definitionally* the frozen flat one:
`Cohesive.curvedDolbeault_zero_inst` and `Cohesive.hoP_curvedDolbeault_zero` (`HoP` of the
curved algebra at `0` is `HoP (dolbeault E X)`) are `rfl`, and `GCDga.withC i i.c … = i` is
`rfl` (`Cohesive.GCDga.withC_self`). So at `h = 0` the source categories of the untwisted and
twisted theorems agree by `rfl`, with no cast along `c = 0`. In Lean, K8 is K14 at `β = 0`
(`exactTwistDatum 0` is `trivialTwistDatum`), with the sources matched by the gauge equivalence
`Cohesive.gaugeHoP` for the gauge `0`.

## Implementation notes

* **Same carrier.** `GCDga.withC` is `@[reducible]` and never an instance. In the generic gauge
  (Z3.b) two instances live on the same term `𝒜`, so projections of modules over the curved one
  are written with `@` (dot notation re-synthesizes the flat instance; prototype P15). At the
  Dolbeault level the curved algebra is a different term, `(curvedDolbeaultPresheaf h).𝒜 ⊤`.
* **Section-level gluing.** `TwMod` components are sheaves of modules on the over-sites
  `Over U_α`; `φ α β` acts on sections over every `W ≤ U_α ∩ U_β`, `R(W)`-linear and natural in
  `W` (decision D4). `R(W)` acts on `Cohesive.sec` only through the coercion `Cohesive.toSec`.
* **Copies over `DgaSheafData`.** The C1/C3/C7 constructions of the *Block's theorem* hub assume
  `c = 0` through `PreResolvingData`; Z3.m/q/t copy the needed terms over
  `DgaSheafData` (decision D11).
* **Frozen surface.** The term-dependency closure of `MainStatementTwisted` is frozen (gate 12):
  besides the frozen files of `MainStatement`, `Algebra/CurvedDga`, `Comparison/CurvedPresheaf`,
  `Forms/CurvedDolbeault`, `Sheaf/Twisted/{CocycleDef, Def, SecHom, Preadditive, Abelian,
  PerfectDef}`, `Sheaf/RestrOverDef`, `Comparison/{TwistDatumDef, TwistedFunctorAux,
  TwistedFunctorDef}`, the Z3.m copies `Comparison/SheafData{AlphaDef, Alpha, Map}`,
  `TwistedBlockFunctorDef` and `StatementsTwisted` (full list: `review/statement-defs.md`). The
  `Abelian` instance is frozen with the statement, since the derived category depends on it
  (D13).
* **Not done (LATER).** Independence of `T`; `J_T` as a triangulated functor; the twisted
  `D^b_coh` version (Z1); non-compact `X`; AB5 and a separator for `TwMod`.

## Files

* `Algebra/CurvedDga.lean`, `Comparison/CurvedPresheaf.lean` (Z3.a); `Algebra/Gauge.lean` (Z3.b).
* `Forms/CurvedDolbeault.lean`, `Sheaf/Twisted/CocycleDef.lean`, `Comparison/TwistDatum*.lean`
  (Z3.c); `Forms/ExpForm.lean`, `Forms/TwistCover.lean`, `Forms/TwistFromPrimitives.lean`,
  `Forms/TwistExists.lean` (Z3.d); `Forms/LocalFreeOpen.lean`, `Forms/LocalGaugeOpen.lean`,
  `Forms/CurvedLL.lean` (Z3.e).
* `Sheaf/RestrOver*.lean` (Z3.f); `Sheaf/Twisted/*.lean` (Z3.g–l′, Z3.r).
* `Comparison/SheafData*.lean` (Z3.m); `Comparison/TwistedFunctor*.lean` (Z3.n);
  `Comparison/TwistedLocal.lean` (Z3.o); `Comparison/AlphaOverRestr.lean`,
  `Comparison/TwistedPerfect.lean` (Z3.p); `Comparison/CurvedHom*.lean` (Z3.q);
  `Comparison/TwistedFF*.lean`, `Comparison/TwistedFullyFaithful*.lean`, `Comparison/TwistedPsi*`
  (Z3.s); `Comparison/TwistedModel.lean`, `Comparison/TwistedCurved*.lean`,
  `Comparison/TwistedUntwist.lean` (Z3.t); `Comparison/TwistedEssSurj*.lean`,
  `Comparison/TwistedLift*.lean`, `Comparison/TwistedXi.lean` (Z3.u).
* `Forms/CurvedRestrictDef.lean` (the gauged restriction `gauge_{h⁰_α}(M|U_α)`, Z3.e),
  `Comparison/GaugeSheaf.lean`, `Comparison/GaugeExactIso.lean` (K14).
* `TwistedBlockFunctorDef.lean`, `StatementsTwisted.lean`, `MainTwisted.lean` (Z3.v).
* `ChecksTwisted.lean`, `ChecksTwistedFF.lean`, `ChecksTwistedK8.lean` (K8, K14),
  `ChecksCurved.lean` (K12), `ChecksCurvedZero.lean` (K12b).

## References

* [[A][Antweiler]] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1, §7.1–7.4; Thm 7.4.3.
* [[B][Block]] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2, §2.7 (gauge) and §4.2 (Thm 4.2.1, stated without proof).
* [[Căldăraru][Caldararu2000]] A. Căldăraru, *Derived categories of twisted sheaves on
  Calabi–Yau manifolds*,
  thesis, Def 1.2.1 (twisted sheaves).
* [[Toda][Toda2009]] Y. Toda, *Deformations and Fourier–Mukai transforms*, J. Differential
  Geom. 81, Lemma 4.3
  (cited in [[A][Antweiler], Lemma 7.1.6]): the twisted pushforward used for enough injectives.
* Blueprint: `blueprint/blueprint-tw.md` (audit of [[A][Antweiler]]/[[B][Block]] in §1.1;
  statement in §2.4; proof in
  §3); `blueprint/blueprint.md` §11 v1.19; conventions: `blueprint/conventions.md`.
-/
