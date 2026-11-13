# Blueprint: twisted sheaves and the curved Dolbeault algebra (Z3)

*Approved as blueprint §11 v1.19 (2 Nov 2026). Assembled from the Claude Fable 5.1 replies
`audit/out/report-TWISTED_PROMPT_A.md` (design) and `…_B.md` (proof, Lean items, decisions; both
gitignored), with B's corrections applied, the Mathlib/TauCeti reuse search, and the prototypes
P15–P17 (`Scratch/P15_Curved.lean`, `P16_TwMod.lean`, `P17_RestrOver.lean`). Names marked (u) are
not yet compiled. `ȟ` is written `ch` in Lean (not an identifier character).*

## Overview

**Target.** For a compact Hausdorff complex manifold `X`, a `∂̄`-closed `h ∈ 𝒜^{0,2}(X)` and a
twist datum `T` for `h`, the functor

  `J_T : Ho(P_{(𝒜_X(X), ∂̄, h)}) ⥤ D(TwMod O 𝒰 ȟ)`, `M ↦ ((α^h(M)|U_α, 𝕏 − h⁰_α), u_αβ·)_α`

is full and faithful with essential image the twisted perfect complexes `TwPerf`; and every closed
`h` has a twist datum. Closest sources: [A, Thm 7.4.3] (first equivalence, compact `X`),
[B, Thm 4.2.1] (stated without proof; `D^b_coh` replaced by `D_perf`, which is Z1).

**Shape of the proof.** On each `U_α` the curved algebra is gauge-equivalent to the flat one
(`𝕏 ↦ 𝕏 − h⁰_α`), so every over-site lemma of C1/C2/C4/C7 and H2 on opens is reused on the cover
pieces. Twisted sheaves have no global sections, so every global step (softness S3.b,
globalization S10, lifting A11) acts on untwisted objects: Hom sheaves, a glued `𝒜⁰`-complex,
global sections of a strictly perfect complex. New global work: the abelian category `TwMod` and
its homological algebra, gluing of sheaves of modules (S12), twisted Hom sheaves, the glued curved
model, A11 over the curved algebra (already general, §1.1).

**Size.** ≈ 12–21k lines (H2 was ≈ 6k); checked statement (statement closure, `exists_twistData`,
K8) ≈ 5–8k. Three stages, gates G1–G5, phases 8–10 (§5).

## 1. Sources, audit, verified facts

### 1.1 Audit of [A, §7.1–7.4] and [B, §4.2]
| # | Place | Finding | Here |
| --- | --- | --- | --- |
| a1 | [A] Def 7.1.1 | cocycle `φ_αβ ∘ φ_βγ = ȟ φ_αγ` does not typecheck for `φ_αβ : M_α → M_β` | `φ_βγ ∘ φ_αβ = ȟ_αβγ φ_αγ` |
| a2 | [A] Def 7.1.1 | `φ_αα` only idempotent | normalized `ȟ` ⇒ `φ_αα = 1`, `φ_βα = φ_αβ⁻¹` |
| a4 | [A] Lemma 7.1.6 | enough injectives via [Toda 4.3] | Toda's twisted pushforward (C.4) |
| a6 | [A] Def 7.2.2 | `h¹` with `dh¹ = ďh⁰` on the given cover needs a Leray cover (implicit) | refinement argument (B.3), local H1 only |
| a7 | [A] Def 7.2.3 | `d_α = d − h⁰_α`, gluing `exp h¹` | verified; same signs |
| a9 | [A] Assumptions 7.2 | (5) K-flatness of `𝒜` over `ℛ` (Malgrange) | not assumed; componentwise flat resolutions (C.8) |
| a12 | [A] Prop 7.2.18 | "`exp(−h⁰_αβ)`" is a typo for `exp(−h¹_αβ)` | untwisting by `u⁻¹` (G.2) |
| a14 | [A] §7.4 | curved local lifting attributed to [Blo09, 4.1.5] (flat only) | gauge by `h⁰_α`, then flat H2 on opens (E.1) |
| a15 | [A] Thm 7.4.3 | embedding into `D^b_coh` uses Oka | not needed (Z1) |
| b1 | [B] Thm 4.2.1 | statement only; right modules, `B = c_Block = −c_here`; "weight one" orientation unspecified | proof spine is [A]; orientation fixed by D.3 |

### 1.2 Verified against the repo and the prototypes (2 Nov 2026)
- **A11 general:** `lifting` (`Algebra/LiftingCone.lean:418`) has no `c = 0` hypothesis (its
  flatness field is `θ² = c·`). B's V1 fallback is void.
- **Resolution lemma general:** `exists_quasiIso_of_enough` (`Sheaf/Resolution.lean:212`) is for
  any abelian `C`.
- **`PreResolvingData.c_eq_zero`** is used in `Comparison/FunctorDef.lean:71`, `ModelDef.lean:65`:
  the C1/C3/C7 terms need copies over `DgaSheafData` (Z3.m/q/t).
- **P15 (curved instance):** `withC` must be `@[reducible]`. Statements relating two instances
  on the *same* term `𝒜` (the generic gauge) need fully explicit `@QuasiCohesive.Q … inst M`
  projections: dot notation re-synthesizes the instance from context and fails. At the Dolbeault
  level the curved algebra is the different term `(curvedDolbeaultPresheaf E X h).𝒜 U`, so
  instance search separates the two. `Hom (gauge M₁) (gauge M₂) n = Hom M₁ M₂ n` is `rfl`.
  **At `h = 0` the curved instance is definitionally the frozen one**:
  `HoP ((withCurvature (dolbeaultPresheaf E X) 0 …).𝒜 ⊤) = HoP (dolbeault E X)` is `rfl`
  (the partial first attempt was right; A/B's "only propositional" is corrected).
- **P16 (`TwMod`):** structure with section-level `φ`, morphisms, `Category`, `comp α`
  compile; `R(W)` acts on sections only through the explicit definitional coercion
  `toSec : R.obj.obj (op W) → ((ringOf R).over U).obj.obj (ovr h)`; `SheafOfModules.evaluation`
  preserves finite limits (instance).
- **P17 (`restrOver`):** `SheafOfModules.overMap R (homOfLE h)` with right adjoint
  `overPullback` (`overMapPushforwardAdj`), left adjoint by passing
  `PresheafOfModules.instIsRightAdjointPushforward (F := Over.map _)` explicitly (as P3 for
  `restr`), hence exact; `restr R U ⋙ restrOver h ≅ restr R V` (`overFunctorMap`);
  `IsGrothendieckAbelian`/`EnoughInjectives (Mod (R.over U))`; the right adjoint preserves
  injectives (`preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`).

## 2. Definitions and target

### 2.1 Curved algebra (Z3.a–b)
- `withC (i : GCDga 𝒜) (c') (hc : c' ∈ 𝒜 2) (hd : i.d c' = 0) : GCDga 𝒜 := { i with c := c', … }`,
  `@[reducible]`, never an instance. `d`, `N`, `commRing0`, `Tot`, `Hom` agree by `rfl` (P15).
- `DgaPresheaf.withCurvature D h hh hd`: same `A`, `𝒜`, grading; `dga U := withC (D.dga U)
  (D.res le_top h) …`; `res` the same algebra maps with `map_c` from `res_comp` (built with
  explicit `@DgaHom.mk`, P15).
- `DgaSheafData X` (u): `PreResolvingData` without `c_eq_zero`; `PreResolvingData.toSheafData`,
  `DgaSheafData.withCurvature`.
- **Gauge** (A.2–A.4). For `M` over `withC i c'` and `β ∈ 𝒜¹` with `c' = c + dβ`:
  `gauge M β := (M.Q, 𝕏 − β·)` over `i`. `(𝕏 − β)² = c' − dβ + β² = c` by Leibniz
  `𝕏(βx) = dβ·x − β𝕏x`, and `β² = 0` since `β² = −β²` (graded commutativity).
  ⚠ Generic `k` needs no 2-torsion: hypothesis `IsUnit (2 : k)` in the generic gauge lemma (true
  for ℂ); deviation from A/B, which wrote "2 ≠ 0". Same `Hom^n`, same `δ` (the `β`-terms cancel
  since `φ(βx) = (−1)^n βφ(x)`), so `gaugeHoP : HoP (withC i c') ≌ HoP i`, identity on `H0`.
  `(gauge M β).baseChange f = gauge (M.baseChange f) (f β)` on generators. Dictionary: [B, §2.7]
  `(id, ω = β)`, sign reversed for left modules.
- `DolbeaultClosed2 E X := {h : DolbeaultAlg E ⊤ // h ∈ dolbeaultGrade E ⊤ 2 ∧ ∂̄h = 0}`;
  `curvedDolbeaultPresheaf E X h := (dolbeaultPresheaf E X).withCurvature h.1 …`;
  `curvedDolbeault E X h := (curvedDolbeaultPresheaf E X h).𝒜 ⊤`.

### 2.2 Twist data (Z3.c)
`TwistCocycle R` (u): `ι : Type`, `[Fintype ι]`, `U : ι → Opens X`, `⨆ U = ⊤`,
`ch α β γ : (R(U_αβγ))ˣ`, normalized, Čech cocycle on quadruple intersections.
`TwistDatum S h extends TwistCocycle S.O` (u): `h0 α ∈ 𝒜¹(U_α)` with `d h0_α = h|U_α`;
`u α β : 𝒜⁰(U_αβ)ˣ` with `d u_αβ = (h0_β − h0_α) u_αβ`, `u_αα = 1`, `u_βα = u_αβ⁻¹`;
`ρ(ch_αβγ) = u_βγ u_αβ u_αγ⁻¹` on `U_αβγ`. `TwistData E X h := TwistDatum (dolbeaultPreData E X)
.toSheafData h.1`. Normalization and cocycle of `ch` follow from (4), (3) and injectivity of `ρ`
(B correction 8). Special data: `trivialTwistDatum` (`h = 0`: `ι = Unit`, `h0 = 0`, `u = 1`,
`ch = 1`), `exactTwistDatum h β` (`h = dβ`: `h0 = β`, `u = 1`, `ch = 1`).

### 2.3 Twisted sheaves (Z3.f–l)
For `R : Sheaf _ CommRingCat.{0}`, `U : ι → Opens X`, `ch` (P16 spelling):
- `sec M h := M.val.obj (op (Over.mk (homOfLE h)))` for `M : Mod ((ringOf R).over U)`, `h : W ≤ U`;
  `toSec`, `secRes`, `resUnit`.
- `TwMod R U ch`: `M α : Mod ((ringOf R).over (U α))`; `φ α β (hα : W ≤ U α) (hβ : W ≤ U β) :
  sec (M α) hα →+ sec (M β) hβ`, `R(W)`-linear, natural in `W`; cocycle
  `φ β γ (φ α β x) = toSec (resUnit (ch α β γ)) • φ α γ x`. Morphisms commute with `φ`.
  ⚠ Correction (3 Nov 2026, for review at G2): `φ_self : φ α α = id` must be a field, not API
  (without it `φ = 0` satisfies the other axioms; the cocycle only makes `φ_αα` idempotent).
  `φ_symm` (`φ_βα φ_αβ = id`) then follows from the normalized cocycle.
- `restrOver R h := SheafOfModules.overMap R (homOfLE h)` (P17).
- `IsPerfectOver K` on `Over U` (S9.a shape, roofs after `restrOver`); `TwIsPerfect K := ∀ α,
  IsPerfectOver ((comp α).mapHomologicalComplex _ |>.obj K)`; `TwPerf : ObjectProperty
  (DerivedCategory (TwMod R U ch))`, objects `≅ Q K` with `TwIsPerfect K`.

### 2.4 The functor and the statement (Z3.m–v)
- `J_T(M)_α^n := restr_{U_α}(sheafOfSh M n)` (curved `DgaSheafData` copy of C1.a), the same
  sheaf for every `α`; differential `𝕏 − h0_α·`; gluing `φ_αβ := u_αβ·` (B correction 2).
- `twistedBlockFunctor E X h T : HoP (curvedDolbeault E X h) ⥤ DerivedCategory (TwMod (holSheaf
  E X) T.U T.ch)`.
```lean
def MainStatementTwisted : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace E X]
    [IsManifold 𝓘(ℂ, E) ∞ X] (h : DolbeaultClosed2 E X) (T : TwistData E X h),
    letI := HasDerivedCategory.standard (TwMod (holSheaf E X) T.U T.ch)
    (twistedBlockFunctor E X h T).Full ∧ (twistedBlockFunctor E X h T).Faithful ∧
      (twistedBlockFunctor E X h T).essImage = TwPerf (holSheaf E X) T.U T.ch
theorem exists_twistData [T2Space X] [CompactSpace X] (h : DolbeaultClosed2 E X) :
    Nonempty (TwistData E X h)
theorem main_theorem_twisted : MainStatementTwisted
theorem K8_twisted_implies_unconditional : MainStatementTwisted → MainStatement
-- (`MainStatementUnconditional` until 6 Nov 2026, blueprint §11 v1.22)
```
Deviations (⚠, repeat in docstrings): statement per twist datum (independence LATER); finite
cover, normalized `ch`, antisymmetric `u`, multiplicative zigzag `(h⁰, u, ch)` instead of
[A]'s `(h⁰, h¹, h², exp_ℛ)`; cocycle order corrected (a1); twisted `O`-modules only, no
intermediate cdg-module category; left modules, `c = h_[A] = −B_[B]`, no `2πi`; `D_perf`
instead of `D^b_coh`; generic gauge assumes `IsUnit (2 : k)`.

## 3. Proof (B §1, condensed; every step names what it reuses)

**A.** Curved algebra. **A.1** `withC`, `withCurvature` (§2.1). **A.2** gauge curvature. **A.3** gauge on
Hom: identity on `Hom^n`, `δ`, `Z0`, `B0`, composition. **A.4** gauge commutes with base change.
**A.5** gluing identity: `u(𝕏 − h0_α)u⁻¹ = 𝕏 − h0_β` from `du = (h0_β − h0_α)u`.

**B.** Twist data exist (H1 = `dolbeaultGrothendieck`, F12, compactness).
**B.1** H1 (`q = 1`) + finite subcover: `U_α`, `h0_α`. **B.2** `ω_αβ := h0_β − h0_α` closed, antisymmetric.
**B.3** refinement: shrink (`exists_iUnion_eq_closure_subset`), at each `x` intersect H1 (`q = 0`)
neighbourhoods in `U_αβ` or complements of `cl U'_α ∩ cl U'_β`; finitely many `W_i`; cover
`U'_α ⊓ W_i` (index `ι × Fin m`): `ω` exact on all double intersections; symmetrized primitives
`η'`. **B.4** `u := exp ∘ η'` (`HasFDerivAt.cexp`, `ContDiff.cexp`; `∂̄` passes the holomorphic
factor through, Z4.d `dbarPart_comp_clm`). **B.5** `ζ = u_bc u_ab u_ac⁻¹` is `∂̄`-closed, so `ζ = ρ(ch)`
(F12, `ρ` injective). **B.6** cocycle, normalization, cyclic symmetry `ch_bca = ch_abc` (used in C.4).

**C.** `TwMod` (section-level). **C.1** category, `comp α` jointly faithful and conservative
(`JointlyReflectIsomorphisms`). **C.2** `Abelian`: componentwise kernels/cokernels (sections commute
with finite limits; `restrOver` exact), `Abelian.ofCoimageImageComparisonIsIso` with
`PreservesCoimageImageComparison.iso`; quasi-isomorphisms componentwise. **C.2′** (refinement, 3 Nov 2026, P19): sections do not commute with cokernels (sheafification), so
`φ` on a cokernel is not defined section by section. Bridge: a family `φ α β` over all
`W ≤ U_α ∩ U_β`, `R(W)`-linear and natural, is the same as a morphism of sheaves
`glueHom α β : restrOver inf_le_left (M α) ⟶ restrOver inf_le_right (M β)` on `Over (U_α ∩ U_β)`
(sections of `restrOver` are the original sections by `rfl`, P19). Kernels: componentwise,
`φ` restricted (sections commute with kernels). Cokernels: componentwise; `glueHom` is the map
induced on cokernels (`restrOver` preserves cokernels); `φ_self` and the cocycle are equalities of
sheaf morphisms on `Over W`-type over-sites, checked after precomposing with the epimorphism
`restrOver (coker.π)`; then read on sections. Implementation (3 Nov 2026): `homOfSec` turns a
linear natural section family on `W' ≤ W` into a sheaf morphism on `Over W`; `sec_eq_of_epi`
cancels `restrOver p` (cocycle of a quotient, with the scalar `ȟ` as a section family, so no
scalar endomorphism of sheaves is needed); sub-objects use injectivity of monos on sections;
`TwMod.ofMono`/`ofEpi` package this once for kernels and cokernels; biproducts use joint
injectivity of `fst, snd` on sections. **C.3** products,
coproducts componentwise. **C.4** enough injectives: `push_α N` (`β`-component `W ↦ N(W ⊓ U_α)`,
gluing `ch_αβγ·`), `comp_α ⊣ push_α` (uses B.6), `push_α` preserves injectives, `M ↪ ∏_α push_α
I_α` (components have enough injectives: `IsGrothendieckAbelian`).
**C.4′** (detail, 3 Nov 2026, P20). Fix a twist cocycle `T` (normalized, Čech cocycle). **(a)** Cyclic
symmetry: the cocycle at `(α, β, γ, α)` with `ȟ_αγα = ȟ_αβα = 1` gives `ȟ_βγα = ȟ_αβγ` on every
`W` in the three opens. **(b)** `j_α N := overPullback (U_α ≤ ⊤) N` on `X`; sections over `W` are
`N(P_α W)`, `P_α W := pullback (W ≤ ⊤) (U_α ≤ ⊤)` (a chosen pullback in `Opens X`, equal to
`W ⊓ U_α` but not definitionally; `P_α W ≤ W`, `P_α W ≤ U_α`, `W ⊓ U_α ≤ P_α W`); restriction is
restriction in `N` and `r ∈ R(W)` acts by `r|P_α W` (P20, all `rfl`). **(c)** `push_α N`: components
`(push_α N)_β := restrOver (U_β ≤ ⊤) (j_α N)`, so sections over `W ≤ U_β` are `N(P_α W)` for every
`β` (definitionally, independent of `β`: this is why one pushes to `X` first); gluing
`φ_βγ x := ȟ_αβγ|P_α W · x`. Linear (commutativity of `R`), natural (restriction of units),
`φ_ββ = id` (`ȟ_αββ = 1`), cocycle `ȟ_αγδ ȟ_αβγ = ȟ_βγδ ȟ_αβδ` (Čech cocycle at `(α, β, γ, δ)`).
On morphisms `push_α k` has components `restrOver (j_α k)` (commutes with scalars).
**(d)** Counit `ε_N : (push_α N)_α ⟶ N`, restriction along `W ≤ P_α W` (`W ≤ U_α`); an iso.
**(e)** `Hom(M, push_α N) ≃ Hom(M_α, N)`: `F ↦ F_α ≫ ε_N`; inverse `g ↦ G`,
`G_β(x) := g(φ_βα(x|P_α W))` for `x ∈ M_β(W)`. `G` commutes with the gluing:
`G_γ(φ_βγ x) = g(φ_γα φ_βγ (x|P)) = g(ȟ_βγα φ_βα(x|P)) = ȟ_αβγ G_β(x)` by (a). Left inverse:
`F.comm` at `(β, α)` and `ȟ_αβα = 1` give `F_α(φ_βα y) = F_β(y)`, so `G_β x = ε(F_β(x)|P)` and
`P_α(P_α W) = P_α W` up to restrictions (functoriality of restriction). Right inverse:
`ε(G_α x) = g(x)` by `φ_αα = id` and naturality of `g`. Naturality in `M` is associativity, in `N`
naturality of `ε`. Hence `comp_α ⊣ push_α` (`Adjunction.mkOfHomEquiv`).
**(f)** `comp_α` preserves monomorphisms (it preserves kernels), so `push_α` preserves injectives
(`Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`). **(g)** Given `M`,
choose monos `ι_α : M_α ↪ I_α`, `I_α` injective; `g := Pi.lift (fun α => (homEquiv)⁻¹ ι_α) :
M ⟶ ∏_α push_α I_α` (finite product, injective). `g` is mono because each component `g.f β` is:
`(g ≫ π_β).f β ≫ ε = ι_β` is mono. (A morphism of twisted sheaves with mono components is mono,
by `hom_ext`.) So `EnoughInjectives (TwMod R T.U T.ch)` for finite covers.
**C.5** restriction preserves
injectives (exact left adjoints). (3 Nov 2026: for `comp_α` the left adjoint is `extTw α`, built
in Z3.l, so the `comp_α` part of C.5 moves to Z3.l; `restrOver` part done in Z3.f.) **C.6** `TwIsPerfect`, invariance, twisted S9.d (compactness).
Detail of C.6 (3 Nov 2026, Z3.j). Restrictions compose definitionally: `restrOver h' ∘ restrOver h =
restrOver (h'.trans h)` and `restrOver (le_refl V) = 𝟭`, also on complexes (`Iso.refl` checks).
**(a)** `restrOver` preserves summands of finite free modules (it commutes with `free`, as `restr` in
S5.a) and strict bounds (additive), hence strict perfectness; it is exact, so preserves
quasi-isomorphisms. **(b)** Over-site S9.c: `IsPerfectOver` is invariant under quasi-isomorphism
(compose roofs; homotopy pullback of roofs through `D(R|W)`), verbatim as S9.c. **(c)**
`IsPerfectOverIn K a b`: models in `[a, b]`. Restriction: a roof on `W ∋ x` restricts to `W ⊓ V'`
by (a). Locality: if every `x ∈ V` has `V' ∋ x` with `IsPerfectOverIn (K|V') a b`, then
`IsPerfectOverIn K a b` (models of `K|V'` are models of `K`, since `K|V'|W = K|W`). A single roof
on `V` gives `IsPerfectOverIn K a b` (take `W = V`). **(d)** Homology of `K` with
`IsPerfectOverIn K a b` vanishes outside `[a, b]`: verbatim S9.d, with locality of zero sheaves on
`Over V` (sections over `W ≤ V` are determined on a cover of `W`). **(e)** `comp_α` is exact (C.2),
so it preserves quasi-isomorphisms and homology; a twisted sheaf with all components zero is zero.
Hence `TwIsPerfect` is invariant under quasi-isomorphism and `TwPerf (Q K) ↔ TwIsPerfect K` (as
S9.c), and `K.ExactAt i ↔ ∀ α, K_α.ExactAt i`. **(f)** For a normalized `ch`, the gluing maps give an
isomorphism of functors `comp_α ⋙ resL α β ≅ comp_β ⋙ resR α β` (`glueHom` is natural in `M` and
has inverse built from `φ_βα`, `φ_symm`); so `K_α|W ≅ K_β|W` for every `W ≤ U_α ⊓ U_β`, as
complexes. **(g)** Twisted S9.d: let `X` be compact, the cover cover `X`, `K` twisted perfect. For
each `x` choose `β(x)` with `x ∈ U_β(x)` and a roof for `K_β(x)` on `W_x ∋ x`, models in
`[a_x, b_x]`; a finite subcover `W_{x_1}, …` gives one range `[a, b]`. For any `α` and `y ∈ U_α`,
`y ∈ W_{x_i}`; with `W' = W_{x_i} ⊓ U_α`, the roof restricted to `W'` (c) and transported along
`K_β|W' ≅ K_α|W'` (f) gives `IsPerfectOverIn (K_α|W') a b`; locality (c) gives
`IsPerfectOverIn K_α a b`. So `TwIsPerfectIn K a b`, and by (d), (e) the homology of `K` vanishes
outside `[a, b]`. **(h)** Sanity: `IsPerfectOver (K|⊤) ↔ IsPerfect K` (`restr_restrOver`).
**C.7** S12 gluing for `ch = 1`: `glue(N)(W) = {(s_α) : ψ_αβ s_α = s_β}`, `glue|U_α ≅ N_α` (cocycle
only), `glueEquiv : TwMod R U 1 ≌ Mod R` (sheaf condition, `TopCat.Sheaf.existsUnique_gluing`);
`rescale g : TwMod R U ch ≌ TwMod R U (ch·ďg)`; tensor with summands of finite free `𝒜⁰`-modules
commutes with `glue`.
Detail of C.7 (3 Nov 2026, Z3.k; prototype P21). **(a)** Sections of a sheaf on `Over U` glue uniquely along
open covers of `W ≤ U` (sheaf condition for the sieve generated by the cover, pullbacks are `⊓`).
**(b)** For `M : TwMod R U 1`, `glue M (W) := {(s_α) ∈ ∏_α M_α(W ⊓ U_α) : φ_αβ(s_α|W') = s_β|W' for
all W' ≤ W ⊓ U_α ⊓ U_β}`, an `R(W)`-module via `R(W) → R(W ⊓ U_α)`; restriction componentwise.
(The condition is quantified over all `W'`, so no intersections are rewritten; by `φ_res` it is
the usual one.) Sheaf: given compatible families on a cover `W_i` of `W`, for each `α` the
components `s^i_α` on `W_i ⊓ U_α` agree on overlaps, so glue (a) to `s_α` on `W ⊓ U_α`; the
compatibility of `(s_α)` holds locally on `W' ∩ W_i`, hence by separatedness. **(c)**
`ofSheaf (glue M) ≅ M`, no cover needed: on `W ≤ U_γ`, `(s_α) ↦ s_γ|W` (`W ≤ W ⊓ U_γ`), inverse
`t ↦ (φ_γα(t|W ⊓ U_α))_α`, compatible by the cocycle with `ȟ = 1` and `φ_res`; inverse laws by
`φ_γγ = id` and compatibility of `(s_α)` at `W' = W ⊓ U_α`; it commutes with the gluing maps
(cocycle again); natural in `M`. **(d)** For `⨆ U_α = ⊤`, `glue (ofSheaf N) ≅ N`: `t ↦ (t|W ⊓ U_α)_α`,
bijective by the sheaf condition of `N` for the cover `W ⊓ U_α` of `W`; natural in `N`. **(e)**
`glueEquiv : TwMod R U 1 ≌ Mod R` from (c), (d) (`Equivalence.mk`). **(f)** `rescale g`: for units
`g_αβ ∈ R(U_αβ)ˣ` with `g_αα = 1` and `ȟ'_αβγ g_αγ = g_βγ g_αβ ȟ_αβγ` on every `W ≤ U_αβγ`,
`φ' := g_αβ φ` defines `TwMod R U ȟ ⥤ TwMod R U ȟ'` (identity on components and morphisms);
`g⁻¹` gives the inverse, unit and counit have identity components. With `g = 1` this is transport
along `ȟ = ȟ'`. **(g)** "Tensor with summands of finite free `𝒜⁰`-modules commutes with `glue`"
needs the twisted base change (Z3.l `BaseChange.lean`): moved to Z3.l.
**C.7′** (Z3.l′ detail, 5 Nov 2026, for review at G5; prototype P24). Fix a map of sheaves of
commutative rings `ψ : R ⟶ S` on `X`; `S ⊗ −` is S8.a's `sheafBC` on an over-site, `η` the unit
of `sheafBC ⊣ restrictScalars` (`η(m) = 1 ⊗ m`, as C7.b's `bcη`).
**(a)** *Base change commutes with restriction between over-sites*: for `V ≤ U` and `M` on
`Over U`, `(S|U ⊗ M)|V ≅ S|V ⊗ M|V` (`restrOver`), natural in `M`, and on sections over `W ≤ V` it
sends `η(m)` to `η(m)`. Proof: S8.a's `sheafBCOverIso` with `Over.map (V ≤ U)` in place of
`Over.forget` (sectionwise the same presheaf; Mathlib's compatibility of pushforward along a
continuous functor with sheafification, which applies to `Over.map` by P24).
**(b)** *Uniqueness*: two `S(W′)`-linear families on sections of `S|U ⊗ M` over `W′ ≤ W ≤ U`,
natural in `W′`, with values in a sheaf of `S`-modules, are equal as soon as they agree on all
`η(m)`, `m ∈ M(W′)`. Proof: as morphisms on `Over W` (`homOfSec`), transported by (a), they
correspond under `sheafBC ⊣ restrictScalars` to their composites with `η`.
**(c)** *`twBC ψ : TwMod R U ȟ ⥤ TwMod S U ψ(ȟ)`*: components `S|U_α ⊗ M_α`; gluing over
`W ≤ U_α ∩ U_β` given by the sections of `(a)⁻¹ ∘ (S ⊗ g_αβ) ∘ (a)`, where `g_αβ` is `φ_αβ` as a
morphism on `Over (U_α ∩ U_β)` (`homOfSec`, C.2′). Linearity and naturality hold because this is
a morphism of sheaves. Key formula: `φ′_αβ(η m) = η(φ_αβ m)` (from (a) and naturality of `η`).
`φ′_αα = id` and the cocycle `φ′_βγ φ′_αβ = ψ(ȟ_αβγ)·φ′_αγ` hold by (b): on `η(m)` both sides
are `η(φ_βγ φ_αβ m) = η(ȟ_αβγ·φ_αγ m) = ψ(ȟ_αβγ)·η(φ_αγ m)` (`η` is `R`-linear into the
restriction of scalars). On morphisms `S ⊗ f_α` componentwise, which commutes with the gluing by
(b). Functorial and additive (`sheafBC` is), and `comp_α ∘ twBC = sheafBC ∘ comp_α` by `rfl`.
**(d)** *Scope change*: the statement "tensor with summands of finite free `𝒜⁰`-modules commutes
with `glue`" (C.7 (g)) follows from C7.a (`T` is a sheaf for every `F`) and C.7 (c). It is proved
where it is used (Z3.t, G.5: assembling the global curved connection from local ones), not as a
separate file of Z3.l′.
**C.8** generators `extTw α (extZero_V R)` with `Hom(G, M) ≅ M_α(V)`;
bounded-above resolutions by finite sums of them (`exists_quasiIso_of_enough`), components flat.
(v1.20, blueprint §11, approved 3 Nov 2026: explicit extension by zero `extX V F` on `X`,
`extTw α N` with components `restr (U β) (extX (U α) N)` and gluing `ȟ_αβγ ·`, `extTw α ⊣ comp_α`,
flatness by the S8.b argument, resolutions by `⊕_α extTw α F_α`; base change and C.7 (g) split off
as Z3.l′.)

**D.** `J_T`. **D.1** terms (curved C1.a copy). **D.2** `d_α = 𝕏 − h0_α`, `d_α² = h − dh0_α = 0`.
**D.3** gluing `u_αβ·`, chain map by A.5, cocycle by (4). **D.4** morphisms and homotopies (C1, `k`
commutes with `u`). **D.5** trivial datum. **D.6** local identification `(J_T M)_α|W' ≅
sheafOfOver_{W'}(gauge_{h0_α}(M|U_α)|W')` (C1.c, A.2/A.4).

**E.** `J_T M ∈ TwPerf`. **E.1** LL^h = H2 on opens (Z3.e) for `gauge_{h0_α}(M|U_α)`. **E.2** C2's over-site
core (base generalized `⊤ → U₀`, V3) + D.6.

**F.** Full faithfulness. **F.1** injective resolution `r : J_T M₂ → I` (C.4). **F.2** curved ℋ^h (C3 over
`DgaSheafData`); `𝓗om^tw(K, I)` = glued over-site Hom sheaves (conjugation, `ch` cancels);
sections = `HomComplex` cochains of `TwMod`; `Ψ^tw = r_α ∘ sheafOfMapV`. **F.3** locally `Ψ^tw` is
C4's `Ψ_{U'}` for the gauged flat modules (A.3, C.7, D.6), quasi-iso by C4 step 3 + LL^h;
globalize (S6). **F.4** softness (S7.a′, S3.b). **F.5** `H⁰` dictionary (`Qh_map_bijective_of_isKInjective`,
`isKInjective_of_injective`).
**F′** (detail, 4 Nov 2026, approved at G4 5 Nov 2026; refines F.1–F.5, no decision changed). Fix sheaf data,
`h`, a twist datum `T` (normalized `ȟ`), `S_h` the curved data, `M₁, M₂` cohesive over `(𝒜(X), h)`.
**(a)** *Curved C3* (Z3.q): C3's section data over `S : DgaSheafData` word for word (`HomSec`,
`homRes`, `homδV`, `ℋ`, `homTop`). Only `δ² = 0` changes: `δ²χ = 𝕏₂²χ − χ𝕏₁² = c·χ − χ(c·) = 0`
(`c` of degree 2, so `χ(c·y) = c·χ(y)`). `ℋ^h(M₁, M₂)(X) ≅ Hom^•(M₁, M₂)` as in C3. Softness as
C3.a(ii).
**(b)** *Hom sections on over-sites.* For `P, Q` on `Over U` and `W ≤ U`, morphisms
`P.over (W → U) ⟶ Q.over (W → U)` (sections of `homSheaf P Q` over `W`) are the same as
`R(W′)`-linear natural section families on `W′ ≤ W` (`homOfSec₀`-type bridge, P19 rfl sections).
**(c)** *`homTw K L`* (Z3.r), for `K, L : TwMod R U ȟ`: the untwisted (`ȟ = 1`) twisted sheaf with
components `homSheaf (K_α) (L_α)` on `Over U_α` and gluing by conjugation on sections over
`W ≤ U_α ∩ U_β`: `s ↦ φ^L_αβ ∘ s ∘ φ^K_βα` (by (b), on `W′ ≤ W`). Linear (target action commutes
with `φ^L`), natural, `φ_self` from `φ^K_αα = φ^L_αα = id`; cocycle: `φ^K_βα φ^K_γβ = ȟ_αβγ⁻¹ φ^K_γα`
(inverse of the cocycle, `φ_symm`) and `φ^L_βγ φ^L_αβ = ȟ_αβγ φ^L_αγ`, so the scalars cancel (`s` is
`R`-linear). Functorial: `homTwPost g`, `homTwPre f` (componentwise `homPost`, `homPre`).
**(d)** *`𝓗om^tw(K, L)`* for complexes of `TwMod R U ȟ`: degree `n` is `∏_{p + n = q} glue(homTw(Kᵖ,
L^q))` in `Mod R` (`glue`, C.7 (b); `⨆ U = ⊤`), differential with Mathlib's sign as S7
(`homComplexD`), `δ² = 0` formally from functoriality of `homTwPost`/`homTwPre`; functorial in both
variables (`twHomMap₂`, `twHomMap₁`).
**(e)** *Global sections*: `Γ(𝓗om^tw(K, L))ⁿ ≅ Cochain_{TwMod}(K, L, n)` compatibly with `δ` and with
`twHomMap₂` (post-composition): a global section of `glue(homTw(Kᵖ, L^q))` is a family of
morphisms `Kᵖ_α → L^q_α` compatible with conjugation, i.e. a morphism of twisted sheaves.
**(f)** *Restriction*: for `V ≤ U_α`, `𝓗om^tw(K, L)|V ≅ 𝓗om_{Over V}(K_α|V, L_α|V)` as complexes
(`glue(N)|U_α ≅ N_α`, C.7 (c); restriction preserves products; `restrOver` commutes with
`homSheaf`), natural in `L` (and in `K`).
**(g)** *Twisted S5.c*: for `I` injective in `TwMod`, every restriction `(I_α)|V` is injective (`I` is a
summand of `∏_β push_β J_β`, C.4 (g); the components of `push_β J` are restrictions of the
injective `j_β J` on `X`, `overPullback` preserves injectives; `restr_restrOver`; S5.c).
**(h)** *Softness, bounds*: `𝒜⁰(X)` acts on each `J_T(M₁)^p` by morphisms of twisted sheaves
(multiplication commutes with `u_αβ·`), hence on the terms of `𝓗om^tw(J_T M₁, I)` by
precomposition, unitally and vanishing over `V` where `a|V = 0` (S3.b(i)); bounded below for `I`
bounded below (`J_T M₁` is bounded above).
**(i)** *`Ψ^tw : ℋ^h(M₁, M₂) ⟶ 𝓗om^tw(J_T M₁, J_T M₂)`*: `χ ∈ ℋ^{h,n}(V)` goes, in component `α`, over
`W ≤ V ⊓ U_α`, degree `p`, to C4's `extAlong (χ|W)`. It commutes with the gluing (`u_αβ` has degree
`0`) and with `δ` (`h⁰_α` has degree 1: `χ(h⁰_α y) = (−1)ⁿ h⁰_α χ(y)`, so the `h⁰_α`-terms cancel).
**(j)** *Local* (F.3): `x ∈ U_α`; LL over opens (Z3.e) for `gM₁ := gauge_{h⁰_α}(M₁|U_α)` gives
`U′ ∋ x`, `U′ ≤ U_α`, `W` and a homotopy equivalence `φ : 𝒜(U′) ⊗ W → gM₁|U′`; with C2's `L, ε, u`
(C4 step 3), `ι := u ≫ α_{U′}(φ) ≫ (α_{U_α}(gM₁)|U′ ≅ α_{U′}(gM₁|U′))⁻¹ ≫ (twLocalIso|U′)⁻¹ :
L → (J_T M₁)_α|U′`. `Φ^tw := Ψ^tw|U′ ≫ (f) ≫ ι^*` is a sectionwise quasi-isomorphism: over `V ≤ U′`
it is `ℋ^h(V) ≅ Hom_along(gM₁|U′, gM₂|V)` (gauge is the identity on `Hom`, A.3; base change, as
C4's `jK`) `→φ^*→ Hom_along(𝒜(U′) ⊗ W, gM₂|V) ≅ Hom_{O(U′)}(W, Tot(gM₂|V))` (A10.a)
`≅ Cochain(L|V, α_{U_α}(gM₂)|V)` (S4.c, C4's `evL` with base `U_α`) `≅ Cochain(L|V, (J_T M₂)_α|V)`
(D.6). Then `r_*` (S7.b′; `r_α|U′` a quasi-iso, `comp_α`, `restrOver` exact) and `ι^*` (S7.c′, (g)):
`(Ψ^tw ≫ r_*)|U′` is a quasi-isomorphism; S6.
**(k)** *Global* (F.4–F.5): `Γ(Ψ^tw ≫ r_*)` is a quasi-isomorphism (S3.b(iv), (h)); `H⁰Γ ℋ^h =
Hom_{Ho(P)}(M₁, M₂)` ((a)), `H⁰Γ 𝓗om^tw(J_T M₁, I) = K(TwMod)(J_T M₁, I) = D(TwMod)(J_T M₁, I)`
((e); `I` K-injective); the composite is `f ↦ J_T(f) ≫ Q(r)`. Stated for resolving data `D`
(compact Hausdorff `X`) with LL over opens as a hypothesis (`LLOpen`); for the Dolbeault data it is proved
(`llOpen_dolbeault`, from Z3.e), so the Dolbeault theorems carry no such hypothesis.

**G.** Essential surjectivity. **G.1** `D ≅ Q K`, bounded (C.6), `K' → K` componentwise flat (C.8).
**G.2** `F := glue(𝒜⁰ ⊗ K'_α, u⁻¹(1 ⊗ φ))` ([A, Rem 7.2.4]). **G.3** `F` globally bounded perfect on `X`.
**G.4** S10: `P̃ → F`, `P := Γ(P̃)`. **G.5** curved model: `∇^h_α := ∇_α + h0_α ⊗ −` glue to `∇^h` with
`(∇^h)² = h`; `N := (Γ(F^•), 𝕏^h)` quasi-cohesive over `(𝒜(X), h)` (curved C7.c copy). **G.6** A11
(general `c`, §1.2): `M`, `e ∈ Z0(M, N)`. **G.7** `e_α ∈ Z0(gauge(M|U_α), N_α)`. **G.8** `Ξ` glued, componentwise
quasi-iso by C7.f. **G.9** `ιT : K' → T^tw(K')` (C7.d). **G.10** `Q(J_T M) ≅ D`.
**G′** (detail, 5 Nov 2026, for review at G5; refines G.1–G.10, no decision changed). Fix flat
resolving data `P`, `h` closed of degree 2, a twist datum `T` (`h⁰_α`, `u_αβ`, `ȟ`), and `K` twisted
perfect in `TwMod O U ȟ` with `D ≅ Q K`. `B_α := 𝒜⁰|U_α ⊗ −`, `η(k) = 1 ⊗ k` as in C.7′.
**(a)** *Flat model* (G.1): `K` has homology in `[a, b]` (C.6 (g)); `K' → K` a quasi-isomorphism
from a bounded above complex with flat components (Z3.l, applied to `truncLE b`). `K'` is twisted
perfect (C.6 (e)) and each `K'_α` is K-flat on `Over U_α` (S8.e).
**(b)** *Base change, untwisting* (G.2): `B := twBC ρ K'` (C.7′, cocycle `ρ(ȟ)`, components
`B_α(K'_α) = F_{K'_α}` of C7.b by `rfl`). By B.5, `ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹`, so `g_αβ := u_αβ⁻¹`
is a rescaling `ρ(ȟ) → 1` (`IsRescale`: `g_αγ = g_βγ g_αβ ρ(ȟ_αβγ)` ✓). `F := glue(rescale_g B)`,
a complex of `𝒜⁰`-modules on `X`, with gluing `φ^F_αβ = u_αβ⁻¹·φ^B_αβ` and `φ^B(η k) = η(φ k)`
(`bcφ_bcUnit`). `F|U_α ≅ F_{K'_α}` (C.7 (c)), compatible with the differentials.
**(c)** *Perfectness* (G.3): `F_{K'_α}` is perfect on `Over U_α`: S8.g's `exists_roof_sheafBC` on
over-sites, with C.7′ (a) in place of `sheafBCOverIso`. Hence `F` is perfect on `X` (local roofs
through `F|U_α ≅ F_{K'_α}` and `restr_restrOver`), globally bounded (S9.d, `X` compact).
**(d)** *S10* (G.4): `Pt` strictly perfect over `𝒜⁰`, `f⁰ : Pt → F` a quasi-isomorphism;
`P := Γ(Pt)` is a bounded complex of finitely generated projective `𝒜⁰(X)`-modules (S4.c) and
`Γ(f⁰)` is a quasi-isomorphism (S3, `𝒜⁰` fine).
**(e)** *Local connections*: `θ_α` the C7.b connection on `F_{K'_α}` over `Over U_α`
(`exists_conn`; `θ_α(η k) = 1 ⊗ η(d k)`), `T_α := θ_α.TC`, `ιT_α : K'_α → T_α` a
quasi-isomorphism (C7.d, `quasiIso_ιT`, K-flat).
**(f)** *Twisted model* (G.9): `T^tw ∈ TwMod O U ȟ` (complexes) with components `T_α` and gluing
`a ⊗ s ↦ a ⊗ φ^B_αβ(s)` on `Tot(𝒜(W), F_{K'_α}(W))` (`totMapAlong` with the identity of `𝒜(W)`;
`φ^B` is `𝒜⁰(W)`-linear). Cocycle `ȟ` (acting through `ρ`). Chain maps: `θ_β φ^B` and `φ^B θ_α`
are both `𝒜⁰`-connections, so their difference is `𝒜⁰`-linear out of `F_{K'_α}`, and it vanishes
on `η k` (`d_{K'}` commutes with `φ`), hence everywhere (C.7′ (b)). `ιT^tw : K' → T^tw` has
components `ιT_α` (commutes with the gluing: `φ^B η = η φ`) and is a quasi-isomorphism
componentwise (C.6 (e)).
**(g)** *Sections of the model of `F`* (C.7 (g)): for `V` open, the map `Tot(𝒜(V), F(V)) →
∏_α Tot(𝒜(V ⊓ U_α), F_{K'_α}(V ⊓ U_α))`, restriction followed by the component `α` of
`F|U_α ≅ F_{K'_α}` (`π_α`), is injective, and its image consists of the families with
`y_β = u_αβ⁻¹·φ^T_αβ(y_α)` on the overlaps. Proof: `V ↦ Tot(𝒜(V), F(V))` is a sheaf (C7.a, for
any `F`), and (b).
**(h)** *Curved connection* (G.5): for `s ∈ F^p(X)`, `θ^h(s)` is the element of (g) with
components `θ_α(s_α) + h⁰_α·s_α`. Compatibility on `W ≤ U_α ∩ U_β`: on `s_α = η k`,
`θ_β(u⁻¹η(φk)) + h⁰_β u⁻¹η(φk) = u⁻¹(η(φ dk) + h⁰_α η(φk))`, since `d(u_αβ⁻¹) =
−u_αβ⁻¹(h⁰_β − h⁰_α)` (from `d u_αβ = (h⁰_β − h⁰_α)u_αβ`); in general both sides are connections
(C.7′ (b)). `θ^h` is generator data over `(𝒜(X), h)` (A3.a): degree 1; flat, since in each
component `(θ_α + h⁰_α)² = θ_α² + d h⁰_α = h|U_α` (`h⁰_α` odd); its form-degree-0 part is `d_F`
(`h⁰_α` has form degree 1). `N^h := (F^•(X), θ^h)` is quasi-cohesive over `(𝒜(X), h)` with
`(0,0)`-complex `Γ(F)`. Only `V = X` is needed: no curved copy of C7's `Conn` for all `V`.
**(i)** *Lifting* (G.6): A11 (general `c`) with `e⁰ := Γ(f⁰)` gives `M` cohesive over
`(𝒜(X), h)` on `𝒜(X) ⊗ P` and `e ∈ Z0(M, N^h)` with `(0,0)`-component `e⁰` (curved copy of
`exists_cohesive_gr0_quasiIso`, steps (A)–(C)).
**(j)** *Localization* (G.7): `e_α ∈ Z0(gauge_{h⁰_α}(M|U_α), N_α)`, `N_α := θ_α.N(U_α)`,
`x ↦ π_α(extAlong(res) e (x))`. Closed: `π_α ∘ res ∘ θ^h = (θ_α + h⁰_α) ∘ π_α ∘ res` by (h), and
the gauged differential is `𝕏 − h⁰_α` (A.2).
**(k)** *Comparison* (G.8): `Ξ^tw : J_T(M) → T^tw` with components `twLocalIso` (D.6, `W′ = U_α`)
followed by `Ξ_{e_α}` (C7.e). It commutes with the gluing: `J_T`'s gluing is `u_αβ·`, and
`φ^T(π_α y) = u_αβ·π_β(y)` by (g). Quasi-isomorphism componentwise by C7.f: `gr0Ξ_{e_α}`
corresponds to `f⁰|U_α` under `G0(gauge(M|U_α)) ≅ Pt|U_α` and `F|U_α ≅ F_{K'_α}` (gauging changes
only the form-degree-1 component), as in C5's step (D) with base `U_α` in place of `⊤`. In detail:
the generators of `gauge(M|U_α)` are `𝒜⁰(U_α) ⊗_{𝒜⁰(X)} Γ(Pt^p)`, and `φ_p : β ⊗ q ↦ β·q|U_α`
onto `Pt^p(U_α)` is bijective because `Pt^p` is a summand of a finite free `𝒜⁰`-module (true for
`𝒜⁰^m`, and preserved by retracts); `φ` intertwines `X0comp` with the differential of `Pt|U_α`
(gauging does not change `X0comp`). Then C5 (D) with base `U_α` (`quasiIso_gr0Ξ_of_equiv`,
`Sc := Pt|U_α`, `g := f⁰|U_α` followed by `F|U_α ≅ F_{K'_α}`) gives `gr0Ξ_{e_α}` a
quasi-isomorphism; `hg` is `ε ∘ π_α = π_α ∘ ε` on `e(1 ⊗ q)` and the `(0,0)`-component `Γ(f⁰)` of
`e` from (i).
**(l)** *Assembly* (G.10): `Q(J_T M) ≅ Q(T^tw) ≅ Q(K') ≅ Q(K) ≅ D`.
**(m)** *Split and risks*: Z3.t = (b), (e)–(h), (j); Z3.u = (a), (c), (d), (i), (k), (l). Risks:
(k) generalizing C5's step (D) (`quasiIso_gr0Ξ_abstract`, private, at `⊤`) to base `U_α`; (g) the
transport of `T(F)` sections along `F|U_α ≅ F_{K'_α}`; curved/flat instance traps between
`(𝒜(X), h)` and the flat `𝒜(U_α)` in (h)–(j) (P15 notes; `cmpTot` as in `twCmp`).

**H.** Assembly. **H.1** `twistedComparison` for `CurvedResolvingData` (u). **H.2** Dolbeault instance,
`main_theorem_twisted`. **H.3** K8: at `(0, trivialTwistDatum)` the source `HoP` is literally
`HoP (dolbeault E X)` (P15); `glueEquiv : TwMod O {⊤} 1 ≌ Mod O`, `twistedBlockFunctor E X 0 T₀ ≅
blockFunctor ⋙ glue.mapDerivedCategory`-type isomorphism (`Equivalence.mapDerivedCategory` ≈ 40
lines from `mapDerivedCategoryCompIso`/`IdIso`/`NatTrans.mapDerivedCategory`), `TwPerf ↔ Perf`.

## 4. Items, files, estimates (new files only; no FROZEN changes)

| Item | File(s) | Content | Est. lines |
| --- | --- | --- | --- |
| **Stage 1 (phase 8)** | | | |
| Z3.a curved dga/presheaf | `Algebra/CurvedDga.lean`, `Comparison/CurvedPresheaf.lean` | `withC` (+ rfl API), `withCurvature`, `DgaSheafData`, `toSheafData`, bridges | 250–400 |
| Z3.b gauge | `Algebra/Gauge.lean`, `Algebra/GaugeBaseChange.lean` | A.2–A.4, `gaugeHoP` (explicit `@`-projections, P15) | 400–700 |
| Z3.c curved Dolbeault, twist data | `Forms/CurvedDolbeault.lean`, `Sheaf/Twisted/CocycleDef.lean`, `Comparison/TwistDatumDef.lean` | §2.1–2.2, `trivialTwistDatum`, `exactTwistDatum` | 300–500 |
| Z3.d exp, existence | `Forms/ExpForm.lean`, `Forms/TwistExists.lean` | B.1–B.6 | 500–900 |
| Z3.e H2 on opens, LL^h | `Forms/LocalFreeOpen.lean`, `Forms/LocalGaugeOpen.lean`, `Forms/CurvedLL.lean` | Z5.g–i with base `U₀`; `localGaugeLemma` re-derived at `⊤`; `curvedLL` | 400–800 |
| **Stage 2 (phase 9)** | | | |
| Z3.f `restrOver` | `Sheaf/RestrOver.lean` | P17 promoted: adjoints, exactness, `restr_restrOver`, injectives | 150–300 |
| Z3.g `TwMod` | `Sheaf/Twisted/Def.lean` | P16 promoted: `sec`, `toSec`, `secRes`, structure, `Hom`, `Category`, `comp`, `φ_self`, `φ_symm` | 400–600 |
| Z3.h abelian | `Sheaf/Twisted/SecHom.lean`, `SubQuot.lean`, `Preadditive.lean`, `Kernels.lean`, `Cokernels.lean`, `Biprod.lean`, `Abelian.lean` | C.2–C.3 | 900–1500 |
| Z3.i injectives | `Sheaf/Twisted/Pushforward.lean`, `Injective.lean` | C.4–C.5 | 400–700 |
| Z3.j perfectness | `Sheaf/Twisted/PerfectDef.lean`, `PerfectOver.lean`, `Perfect.lean` | C.6 | 400–700 |
| Z3.k gluing | `Sheaf/Twisted/GlueSec.lean`, `Glue.lean`, `GlueEquiv.lean`, `Rescale.lean` | C.7 (a)–(f) | 700–1200 |
| Z3.l generators (v1.20) | `Sheaf/Twisted/ExtZero.lean`, `ExtTw.lean`, `ExtTwAdj.lean`, `FlatResolution.lean`; `isFlat_of_locally_zero` in `Sheaf/Flat.lean` | C.5 (`comp_α`), C.8 | 1200–2000 |
| **Stage 3 (phase 10)** | | | |
| Z3.l′ base change (v1.20) | `Sheaf/Twisted/BaseChange.lean`, `GlueTensor.lean` | C.7 (g), componentwise `sheafBC`; before Z3.u | 600–1200 |
| Z3.m C1 over `DgaSheafData` | `Comparison/SheafDataAlphaDef.lean`, `SheafDataAlpha.lean`, `SheafDataMap.lean` | copies + rfl bridges (done 3 Nov 2026: AlphaDef, C1.a, C1.b section and degree maps; no complex/`J`, they need `c = 0`; `AlphaOver` not copied, D.6 applies it to the flat gauged module) | 600–1000 |
| Z3.n `J_T` | `Comparison/TwistedFunctorDef.lean`, `TwistedFunctor.lean` | D.1–D.4 | 600–1000 |
| Z3.o local identification | `Comparison/TwistedLocal.lean`; `Scratch/P23_TwLocal.lean` | D.6 (generic `P : PreResolvingData`; `gaugedRes`, `twCmp`) | 400–700 |
| Z3.p C2^tw | `Comparison/AlphaOverRestr.lean` (C1.c between opens), `Comparison/TwistedPerfect.lean` | E.1–E.2 (H2 over opens for any `N` over `𝒜(U)`, so no `curvedLL` bridge is needed) | 300–600 |
| Z3.q C3 curved | `Comparison/CurvedHomSheaf*.lean`, `CurvedHomGauge.lean` | F.2 (ℋ^h) | 800–1300 |
| Z3.r `𝓗om^tw` | `Sheaf/Twisted/HomSheaf.lean`, `HomSections.lean` | F.2 | 800–1200 |
| Z3.s C4^tw | `Comparison/TwistedFullyFaithful*.lean` | F.1–F.5 | 1000–1600 |
| Z3.t curved model | `Comparison/CurvedConn.lean`, `TwistedModel.lean` | G.5, G.7 | 900–1500 |
| Z3.u C5^tw | `Comparison/TwistedEssSurj*.lean` | G.1–G.4, G.6, G.8–G.10 | 1200–2000 |
| Z3.v assembly | `Comparison/TwistedEquivalence.lean`, `TwistedBlockFunctorDef.lean`, `StatementsTwisted.lean`, `MainTwisted.lean`, `ChecksTwisted.lean` | H.1–H.3 | 500–900 |

Totals: stage 1 ≈ 1.9–3.3k, stage 2 ≈ 3.7–6.2k, stage 3 ≈ 7.1–11.8k; **≈ 12.7–21.3k**.

## 5. Order, gates, checks
Dependencies as B §2.3: {Z3.a, b, e} ∥ {Z3.c, d} ∥ {Z3.f, g, h}; Z3.m after Z3.a; stage 3 after
both. Gates: **G1** after Z3.a–e; **G2** after Z3.f–l (freeze candidates `restrOver`, `TwMod`,
`AbelianDef`, `TwPerf`); **G3** after Z3.p; **G4** after Z3.s; **G5** after Z3.v (freeze
`StatementsTwisted.lean` and its term-dependency closure, v1.18 rule; `scripts/statement_defs.py`
with root `MainStatementTwisted`).
Checks (`ChecksTwisted.lean`, `ChecksAlgebra.lean`):
- **K8**: `MainStatementTwisted → MainStatement` (formerly `MainStatementUnconditional`).
- **K9**: a non-identity coboundary cocycle `ch = ďg` on two opens; nonzero `extTw` objects;
  `rescale g ⋙ glueEquiv`.
- **K12**: curved toy dga with a cohesive module, and its gauge to `c = 0`: signs of A.2,
  non-vacuity of `c ≠ 0`. Toy (approved at G1, 3 Nov 2026): the square-zero `k ⊕ kβ ⊕ kc`,
  `|β| = 1`, `|c| = 2`, `dβ = c` (`ChecksCurved.lean`); the earlier `k[t]/t² ⊗ Λ(ε₁, ε₂)`,
  `dt = ε₁` has no well-defined `d` (`d(t²) = 2tε₁ ≠ 0`).
- **K12b** (added by the human at G1, 3 Nov 2026): `k[c]/(c²)`, `|c| = 2`, `d = 0`, curvature `c`:
  every object of `Ho(P_A)` is zero (`ChecksCurvedZero.lean`; contraction `𝕏₂`,
  `isZero_of_contraction`). Bounded counterpart of the requested `k[t, t⁻¹]`, `|t| = 0`, curvature
  `t`, which is outside `GCDga` (curvature in degree 2, bounded algebra).
- **K14**: `exactTwistDatum (dβ) β` for any `X`: the twisted theorem at exact `h` ↔ the untwisted.
- `#print axioms main_theorem_twisted`.
A concrete compact `X` with `H^{0,2} ≠ 0` (complex torus) is out of scope: neither Mathlib nor
TauCeti has a 2-dimensional torus.

## 6. Frozen surface (G5)
Term-dependency closure of `MainStatementTwisted`: `withC`, `withCurvature`, `DolbeaultClosed2`,
`curvedDolbeault*`; `TwistCocycle`, `TwistDatum`, `TwistData`, `DgaSheafData`, `toSheafData`;
`restrOver`; `TwMod` with `Category` **and `Abelian`** (the derived category takes it as an
argument; definitions-only files `Sheaf/Twisted/Def.lean`, `AbelianDef.lean`); `comp`,
`IsPerfectOver`, `TwIsPerfect`, `TwPerf`; the Z3.m copies used by `twistedSheafOf`;
`twistedSheafOf`, `twistedJ`, `twistedBlockFunctor`; `MainStatementTwisted`.

## 7. Risks (ranked) and open checks
1. `Abelian (TwMod)` (Z3.h): componentwise kernels with section-level `φ`; mitigated by P16 and
   Mathlib's constructor.
2. Re-parametrization over `DgaSheafData` (Z3.m/q/t): ≈ 2–3k lines of copies; semantic risk nil.
3. Curved/flat instance traps (P15): reducible `withC`, explicit projections in Z3.b, distinct
   terms at the Dolbeault level; `toSec` for ring actions (P16).
4. `extTw` coherence (Z3.l).
5. Base generalization (V3): list the C2/C4/C7 and Z5.g–i statements that use `⊤`/`le_top` before
   Z3.e/Z3.p; expected statement-level only.
6. Universes (V5): `TwMod : Type 1`, `Category.{0}`; `HasDerivedCategory.standard` as for `Mod R`.
7. `exists_twistData` bookkeeping (product index).

## 8. Decisions (B §3, approved with v1.19)
D1 same carrier (`withC` reducible, P15); D2 multiplicative `(h⁰, u, ch)`; D3 finite `[Fintype ι]`;
D4 components on over-sites, section-level `φ`, restriction = `SheafOfModules.overMap` (P17);
D5 Toda's pushforward; D6 per datum + `exists_twistData`; D7 Z5.g–i re-stated over `U₀`; D8
componentwise flat resolutions, no Malgrange; D9 triangulated `J_T`/`TwPerf` LATER; D10
`glueEquiv` + `rescale`; D11 `DgaSheafData` with copies; D12 `TwIsPerfect := ∀ α, IsPerfectOver`;
D13 `Abelian` instance frozen with the statement; D14 K8 as an implication; D15 `TwMod` over a
`CommRingCat` sheaf; D16 three stages, gates G1–G5, phases 8–10; D17 K12; D18 K14 now, torus out of
scope; D19 void (A11 general).

## 9. LATER (Z3+)
Independence of the datum (gauge by `ξ`, `rescale`, refinement; TauCeti's Čech/Leray toolkit and
`additiveUnitsFunctor` may help for the class in `Ȟ²(O*)`); `J_T` triangulated (with Z2.d–g,
which apply to the curved `HoP` unchanged since they are generic in `GCDga`); twisted Z1
(`D^b_coh`); non-compact `X`; AB5/separator for `TwMod`.
