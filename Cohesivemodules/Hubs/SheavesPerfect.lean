import Cohesivemodules.Sheaf.Acyclic
import Cohesivemodules.Sheaf.TensorSections
import Cohesivemodules.Sheaf.HomAction
import Cohesivemodules.Sheaf.HomOver
import Cohesivemodules.Sheaf.BaseChange
import Cohesivemodules.Sheaf.Globalize

set_option linter.style.header false

/-!
# Sheaves of modules and perfect complexes

This page is an overview of the sheaf layer of the project (blueprint items S1–S11). It contains
no declarations; the links below point to the files where the definitions and theorems live.

## Overview

On the geometric side of Block's theorem the category is `D_perf(X, O_X)`, the perfect complexes
in the derived category of sheaves of `O_X`-modules. This layer builds, for a sheaf of rings `R`
on a topological space `X` (compact Hausdorff where needed), the vocabulary in which that
category is defined, and the toolkit the comparison theorem (*Block's theorem* hub) needs about
sheaves over a *fine* sheaf of rings such as the sheaf `𝒜⁰` of smooth functions. The rings `O_X`
and `𝒜⁰` only enter in the *Dolbeault algebra* hub; everything here is for a general sheaf of
rings, commutative where stated: Hom sheaves, tensor products, base change, S4.b and S10 need
`R` commutative.

* **Modules.** Sheaves of rings on `Opens X` are `Cohesive.RingSheaf X`; modules over any sheaf
  of rings `R` are `Cohesive.Mod R`, Mathlib's `SheafOfModules` with the module universe fixed
  to `0`. Restriction `M ↦ M|U` is `Cohesive.restr`, global sections `Cohesive.globalSections`.
* **Perfect complexes** (S9). A complex is *strictly perfect* (`Cohesive.IsStrictlyPerfect`) if
  it is bounded and every term is a direct summand of a finite free module
  (`Cohesive.IsFinFreeSummand`), and *perfect* (`Cohesive.IsPerfect`) if it is locally connected
  to a strictly perfect complex by a roof of quasi-isomorphisms. `Cohesive.Perf R` is the full
  subcategory of `D(R)` on the objects isomorphic to `Q K` with `K` perfect. These three
  definitions enter the main statement and are frozen.
* **Fine sheaves** (S1–S4, S10). Over a fine sheaf of rings (`Cohesive.IsFine`: partitions of
  unity for finite covers) on a compact space, `Γ(X, -)` is exact on modules (S2–S3), finitely
  generated projective modules are `Γ` of direct summands of finite free modules (S4), and, for
  `R` also commutative, every perfect complex is quasi-isomorphic to a strictly perfect one
  (S10). No sheaf cohomology is
  used anywhere.
* **Soft sheaves** (S3.b, `Cohesive.IsSoft`) give `Γ`-acyclicity for complexes whose terms are
  modules over a fine sheaf but whose differentials are not linear, as for Hom sheaves of
  cohesive modules.
* **Hom sheaves** (S7, `Cohesive.homSheafComplex`) and **tensor products** with K-flat
  resolutions (S8, `Cohesive.tensorC`, `Cohesive.IsKFlat`); S8 replaces Malgrange's flatness
  theorem (blueprint §0 decision 5).
* **Derived-category wiring** (S11): injective resolutions, and morphisms in `D` as homotopy
  classes, from Mathlib.

## Main definitions

* `Cohesive.RingSheaf`, `Cohesive.Mod`, `Cohesive.restr`, `Cohesive.globalSections`,
  `Cohesive.ringOf`: the shared vocabulary (frozen, `Sheaf/Basic.lean`, `Sheaf/RingOfDef.lean`).
* `Cohesive.SupportedIn` (`SupportedIn ρ U`: the global section `ρ` is supported in `U`),
  `Cohesive.IsFine`: fine sheaves of rings (S1);
  `Cohesive.IsComm`, `Cohesive.IsCommSheaf`: commutativity of a sheaf of rings.
* `Cohesive.IsSoft`: soft sheaves of modules (S3.b).
* `Cohesive.IsFinFreeSummand`, `Cohesive.IsLocallyFinFreeSummand`: (local) direct summands of
  finite free modules (S4).
* `Cohesive.extZero`: extension by zero `j_!`, the left adjoint of `Cohesive.restr` (S5.b).
* `Cohesive.homSheaf`, `Cohesive.homSheafComplex`: the Hom sheaf `𝓗om(M, N)` and the Hom complex
  `𝓗om(K, L)` (S7); `Cohesive.homComplexSourceAction`: the termwise source action (S7.a′).
* `Cohesive.tensorBifunctor`, `Cohesive.tensorC`: tensor products of sheaves of modules and of
  complexes; `Cohesive.IsFlat` (S8.b), `Cohesive.IsKFlat` (S8); `Cohesive.sheafBC`: base change
  `S ⊗_R -` along a map of sheaves of commutative rings (S8.a).
* `Cohesive.IsStrictlyPerfect`, `Cohesive.IsPerfect`, `Cohesive.Perf` (S9.a–c, frozen);
  `Cohesive.IsPerfectIn`: perfect with all local models in a fixed degree range (S9.d).

## Main results

* `Cohesive.existsUnique_extend` (S1.a): `ρ • t` extends by zero for `ρ` supported in `U`.
* `Cohesive.surjective_globalSections_of_epi` (S2): over a fine `R` on compact `X`, `Γ` maps
  epimorphisms to surjections. `Cohesive.acyclic_globalSections` (S3): `Γ` preserves acyclic
  complexes of `R`-modules.
* `Cohesive.IsSoft.of_action`, `Cohesive.isSoft_of_isFine` (S3.b(i)): a sheaf of modules on which
  the global sections of a fine sheaf of rings act unitally and locally is soft; in particular
  every module over a fine commutative `R` is soft; `Cohesive.acyclic_globalSections_of_isSoft`
  (S3.b(iv)): on compact Hausdorff `X`, `Γ` of a bounded-below acyclic complex with soft terms
  is acyclic.
* `Cohesive.projective_of_isFinFreeSummand` (S4.a), `Cohesive.isFinFreeSummand_of_locally`
  (S4.b), `Cohesive.exists_globalSections_iso` and `Cohesive.bijective_globalSections_map`
  (S4.c), `Cohesive.isIso_tensorSectionsMap` (S4.d, on any site, no fineness).
* `Cohesive.extZeroAdj`, `Cohesive.restr_injective` (S5); `Cohesive.quasiIso_of_locally` (S6):
  quasi-isomorphisms are local; `Cohesive.quasiIso_of_sectionwise` (S6, any site): a sectionwise
  quasi-isomorphism is a quasi-isomorphism.
* `Cohesive.quasiIso_homComplexMap₂` (S7.b): `𝓗om(P, -)` preserves quasi-isomorphisms for `P`
  strictly perfect; `Cohesive.acyclic_homComplex` (S7.c): `𝓗om(C, I)` is acyclic for `C` acyclic
  and `I` bounded below with injective terms; `Cohesive.isSoft_homSheafComplex_X` (S7.a′): if the
  global sections of a fine sheaf of rings act on the terms of `K` (additively, unitally and
  locally; the action need not commute with `d`), the terms of `𝓗om(K, L)` are soft. Site
  versions: `Cohesive.quasiIso_homComplexMap₂_site` (S7.b′) and
  `Cohesive.quasiIso_homComplexMap₁_site` (S7.c′; ⚠ the injectivity of the restrictions `Iⁱ|V`
  to every object is a hypothesis, automatic on a space by S5.c).
* `Cohesive.exists_quasiIso_flat` (S8.d): flat resolutions of bounded-above complexes;
  `Cohesive.isKFlat_of_isFlat` (S8.d): bounded-above complexes of flats are K-flat;
  `Cohesive.acyclic_tensorC_of_isKFlat` (S8.e); `Cohesive.quasiIso_sheafBC_of_isKFlat` (S8.g):
  base change preserves quasi-isomorphisms between K-flat complexes.
* `Cohesive.perf_Q_obj_iff` (S9.c): `Q K ∈ Perf R ↔ IsPerfect K`, stated for a
  `HasDerivedCategory` instance in universe `0`; for an instance in any universe, including the
  universe-`1` instance `HasDerivedCategory.standard` of the main statement, use
  `Cohesive.perf_Q_obj_iff'` (`Comparison/Perfect.lean`);
  `Cohesive.IsPerfect.exists_isPerfectIn` (S9.d): on compact `X` perfect complexes are globally
  bounded.
* `Cohesive.exists_strictlyPerfect_quasiIso` (S10): for `R` fine and commutative on compact `X`,
  every perfect complex receives a quasi-isomorphism from a strictly perfect complex. Local
  steps: `Cohesive.nullHomotopic_locally`, `Cohesive.lift_locally`, `Cohesive.split_locally`,
  `Cohesive.homology_finGen_locally` (S10.a–d), global generation
  `Cohesive.exists_epi_free_of_locally` (S10.e).
* `Cohesive.exists_injective_resolution`, `Cohesive.Q_map_surjective_of_isKInjective`,
  `Cohesive.exists_lift_of_isKProjective` (S11).

## Conventions and signs

Binding for the whole project (`blueprint/conventions.md` §7–§8).

**Sites and rings.**
* Sheaves on a space live on `Opens X` with `Opens.grothendieckTopology X`, and
  `X : Type`. Rings for `SheafOfModules` are `RingCat.{0}`-valued; a sheaf of commutative rings
  `R : Sheaf J CommRingCat` is converted with `Cohesive.ringOf R` (`forget₂`). Commutativity of a
  `RingCat`-valued sheaf is a hypothesis (`Cohesive.IsComm`, `Cohesive.IsCommSheaf`), not a type
  class.
* Results that must also hold on the over-site of an open (S7.b′–c′, S8, S10.a–d, S4.d) are
  stated on an arbitrary small site `C` with topology `J` (for S8 and S4.d, for a sheaf of
  commutative rings). There **"locally"** at an object `V` means: the arrows `Y ⟶ V` over which
  the property holds generate a covering sieve of `V` (`Sieve.generate … ∈ J V`). On `Opens X`
  this says that every point of `V` has an open neighbourhood `W ⊆ V` on which the property
  holds.
* **Universes.** Always `Cohesive.Mod R = SheafOfModules.{0} R`; every Mathlib constant with a
  free module universe (`SheafOfModules.overFunctor`, `SheafOfModules.free`, …) is used with the
  module universe fixed to `0` (through a project abbreviation such as `Mod` or `restr`, or an
  explicit `.{0}`), since the Grothendieck-abelian and enough-injectives
  instances exist only there. The derived category is `DerivedCategory (Mod R)` with
  `HasDerivedCategory.standard` as a local instance, so its morphisms live in universe `1`;
  `Cohesive.Perf` takes the `HasDerivedCategory` instance as an argument, and the main statement
  uses `HasDerivedCategory.standard` for both the functor and `Perf`.

**Restriction.** `Cohesive.restr R U M = M|U` is Mathlib's `SheafOfModules.overFunctor`: a sheaf
of modules over `R.over U` on the over-site `Over U`, not a module over a ring on the space `U`
(decided in prototype P3). Restriction has adjoints on both sides, so it is exact; its left
adjoint is `Cohesive.extZero`. Strictly perfect complexes on `U` live over `R.over U`.

**Stalk-free definitions.** No stalks of sheaves of modules are used.
* Support: `ρ ∈ R(X)` is supported in `U` (`Cohesive.SupportedIn ρ U`) if there is an open `V`
  with `U ∪ V = X` and `ρ|V = 0`; for a sheaf this is `supp ρ ⊆ U`.
* Fine: for every *finite* open cover `(Uᵢ)` there are `ρᵢ ∈ R(X)` with `∑ ρᵢ = 1`
  and `ρᵢ` supported in `Uᵢ`. ⚠ Finite covers only, with compactness where needed, replace the
  softness and arbitrary covers of [[A][Antweiler]] (blueprint §9 deviation 2).
* Soft: for every closed `K`, open `U ⊇ K` and `s ∈ M(U)` there are `t ∈ M(X)` and an open
  `V` with `K ⊆ V ⊆ U` and `t|V = s|V`. On compact Hausdorff `X` this is the usual notion.
* `j_!`: the stalk formula is replaced by `(j_! M)|U ≅ M` and "sections of `j_! M` vanish near
  points outside `U`" (`Cohesive.extZero_locally_zero`).

**Hom and tensor.**
* `𝓗om(M, N)(V) = Hom(M|V, N|V)`, with `R(V)` acting through the target (`R` commutative).
  `𝓗om(K, L)ⁿ = ∏_{p + n = q} 𝓗om(Kᵖ, L^q)`, with Mathlib's differential
  `CochainComplex.HomComplex.δ`, `δz = z ≫ d + (−1)^{n+1} d ≫ z` (the sign of the *Cohesive
  modules* hub); its sections are cochains (`Cohesive.homComplexSectionsEquiv`).
* `M ⊗ N` is the sheafification of the sectionwise tensor product `U ↦ M(U) ⊗_{R(U)} N(U)`
  (Mathlib's monoidal structure on presheaves of modules over commutative rings; there is no
  monoidal structure on `SheafOfModules`). `K ⊗ L` is the total complex
  `HomologicalComplex.mapBifunctor` with Mathlib's Koszul sign on the second differential.
* Flat: `M ⊗ -` preserves monomorphisms. K-flat: `K ⊗ L` is acyclic for every acyclic `L`.

**Perfect complexes.**
* Strictly perfect: there are `a, b` with `P` strictly zero outside `[a, b]`
  (`CochainComplex.IsStrictlyGE`, `CochainComplex.IsStrictlyLE`), and each `Pⁿ` has maps
  `i : Pⁿ ⟶ Rᵐ`, `p : Rᵐ ⟶ Pⁿ` with `i ≫ p = 𝟙`, where `Rᵐ` is
  `SheafOfModules.free (Fin m)`.
* Perfect: every `x` has an open `U ∋ x`, complexes `L`, `P` over `R.over U` with `P` strictly
  perfect, and quasi-isomorphisms `K|U ← L → P`. ⚠ A roof instead of an isomorphism
  `Q(K|U) ≅ Q(P)` in `D(R|U)`: equivalent, and it avoids a derived category for every open.
* `D_perf(X, R)` (`Cohesive.Perf R`): an `ObjectProperty` of `DerivedCategory (Mod R)`, closed
  under isomorphism by construction.
* Globally bounded (S9.d, `Cohesive.IsPerfectIn K a b`): all local models in degrees `[a, b]`.
  ⚠ No uniform bound on the number of generators ([[A][Antweiler], Def 7.2.11 (3)]); on compact
  `X` a finite
  subcover gives it.

## Implementation notes

* **Frozen files.** `Sheaf/Basic.lean`, `Sheaf/FineDef.lean`, `Sheaf/RingOfDef.lean` and
  `Sheaf/PerfectDef.lean` enter the main statement and are frozen; they hold only definitions.
  `Sheaf/RestrOverDef.lean` (restriction between over-sites) is frozen as part of the twisted
  statement and is described in the *Twisted theorem* hub.
* **Replacements for the sources.** Exactness of `Γ` over a fine sheaf (S3) and softness (S3.b)
  replace sheaf-cohomological acyclicity ([[A][Antweiler], Lemma 7.2.8]). S10 replaces
  [[A][Antweiler], Lemma 7.2.10] on
  small opens, which needs free modules over `R|U` to be projective, by local lifting and
  splitting (S10.a–c) and S4.b (⚠ blueprint §9 deviation 3); compactness replaces finite covering
  dimension ([[A][Antweiler], Lemma 7.2.12]) (⚠ blueprint §9 deviation 2).
* **S7.a′.** The old S7.a ("a complex of modules over a fine `S` via the source") is false when
  the differentials are not `S`-linear, and is not formalized; S7.a′ (blueprint v1.9) gives only a
  termwise action, which is what softness needs.
* **Restricted generality.** S8.e is stated for bounded-above `L`, S8.f for flat modules, and
  S8.g for a single quasi-isomorphism between K-flat complexes (the roof form follows by
  resolving the middle term); S4.b and S10 need `R` commutative. S4.d holds on any site and
  object, without fineness. S4.c needs neither fineness nor compactness, and does not construct
  the inverse `P ↦ P̃` explicitly; S4.a holds for free modules on any index type.

## Files

* `Sheaf/Basic.lean`, `Sheaf/RingOfDef.lean`, `Sheaf/FineDef.lean`, `Sheaf/Fine.lean` (S1–S2),
  `Sheaf/Acyclic.lean` (S3), `Sheaf/SoftBasic.lean`, `Sheaf/Soft.lean` (S3.b).
* `Sheaf/ProjectiveBasic.lean`, `Sheaf/Projective.lean`, `Sheaf/RestrEval.lean` (S4),
  `Sheaf/TensorSections.lean` (S4.d).
* `Sheaf/RestrictionBasic.lean`, `Sheaf/Restriction.lean` (S5–S6); `Sheaf/RestrOver*.lean`
  (*Twisted theorem* hub).
* `Sheaf/Hom/Basic.lean`, `Sheaf/HomSheafComplex.lean`, `Sheaf/Hom.lean`,
  `Sheaf/HomAcyclic.lean`, `Sheaf/HomAcyclic/*.lean`, `Sheaf/HomOver*.lean`,
  `Sheaf/HomSectionsMap.lean`, `Sheaf/HomAction.lean` (S7).
* `Sheaf/Flat/*.lean`, `Sheaf/FlatBasic.lean`, `Sheaf/Flat.lean`, `Sheaf/Resolution.lean`,
  `Sheaf/FlatResolution.lean`, `Sheaf/BaseChangeBasic.lean`, `Sheaf/BaseChange.lean` (S8);
  `Sheaf/BaseChangeRestrOver.lean` (*Twisted theorem* hub).
* `Sheaf/PerfectDef.lean`, `Sheaf/Perfect.lean` (S9).
* `Sheaf/GlobalizeEpi.lean`, `Sheaf/Globalize.lean`, `Sheaf/Globalize/*.lean` (S10).
* `Sheaf/Derived.lean` (S11).

## References

* [[A][Antweiler]] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1, §7.2 (Def 7.2.11, Lemmas 7.2.7–7.2.16).
* [TT] R. Thomason, T. Trobaugh, *Higher algebraic K-theory of schemes and of derived
  categories*, §1–§2 (Lemma 1.9.5 for S10).
* [Stacks] The Stacks Project, chapter *Cohomology of Sheaves*, K-flat complexes (S8).
* Blueprint: `blueprint/blueprint.md` §3 (items S1–S11); conventions: `blueprint/conventions.md`
  §7–§8.
-/
