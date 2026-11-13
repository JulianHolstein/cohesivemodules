# Blueprint: Block's theorem, perfect form

Ho(P_A) ≃ D_perf(X) for a compact complex manifold X and its Dolbeault algebra A.

**Version 1.12 (29 Oct 2026, gate 4: file layout and Lean names; approved by the human).** Changes after this point go in §11 and need human approval (latest: v1.18, 2 Nov 2026).

Companion files: `blueprint/conventions.md` (signs, encodings, universes, notation) and
the feasibility report (design rationale). This file is definitive for *what* is proved;
`conventions.md` is definitive for *how* it is spelled.

## 0. How to read this file

**Status tags.** Every item carries one tag.

| Tag | Meaning |
| --- | --- |
| BUILD | Formalize now, no `sorry` in the end. |
| HYP | Deep input, stated as a `Prop` and carried as an explicit hypothesis of the main theorem. Never an `axiom`. |
| LATER | Deliberately deferred. Do not start. Listed in §6 so nothing is lost. |

**Sizes** (rough, for planning only): S = days, M = 1–3 weeks, L = 1–2 months.

**Sources.**
- [B] J. Block, *Duality and equivalence of module categories in noncommutative geometry*, arXiv math/0509284v2.
  Numbering is that of arXiv v2 (`references/arXiv-math0509284v2`); the published version
  (CRM Proc. Lecture Notes 50, 2010; `references/Block.pdf`) numbers differently.
- [A] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert correspondence*, arXiv 2411.19595v1. §3.1 and §7 are the spine of this blueprint.
- [CHL] J. Chuang, J. Holstein, A. Lazarev, *Maurer–Cartan moduli and theorems of Riemann–Hilbert type*, Appl. Categ. Struct. 29 (2021).
  Numbering is that of arXiv 1802.02549v3 (`references/CHL.pdf`); the journal numbering was not
  checked.
- [TT] R. Thomason, T. Trobaugh, *Higher algebraic K-theory of schemes and of derived categories*, §1.
- [Stacks] The Stacks Project.

**Mathlib marks.** ✓ = declaration found in Mathlib master at commit `80dabc7`
(21 Oct 2026, Lean `v4.36.0-rc1`) and re-checked with `#check` against the pinned stable release
`v4.35.0` (commit `56a0058`, Lean `v4.35.0`) in phase 0. ✗ = searched for and absent. (?) = not
checked.

**Deviations from the sources** are flagged with ⚠ and collected in §9.

**Fixed decisions.** Do not revisit these without asking.
1. Headline: Ho(P_A) ≃ D_perf(X). D^b_coh(X) is later (Z1).
2. Standalone repository on stable Mathlib; Tau Ceti roadmaps are design references only.
3. Proof spine: [A] §7.2 at h = 0, with Block's §§2–3 for the algebra. Gaps in [B] are filled
   from [CHL] and [A].
4. Hypotheses H1 and H2 are stated on X; H2 is the weak (homotopy-equivalence) form of
   Block's gauge lemma.
5. Malgrange's flatness theorem is not used: K-flat resolutions instead (S8, C5.0).
6. Forms: one sheaf of chart-expressed sections (F9); fibre = ℂ-alternating maps on the
   conjugate space; product from Mathlib's exterior algebra (F2, F5).
7. Left modules, as in [A] and Mathlib (conventions §3).
8. LATER (§6): G9 = Z1 (D^b_coh), G10 = Z2 (triangulated structure), and the twisted extension
   Z3, together with Z4–Z8.

## 1. Scope and the main theorem

### M — Main theorem (BUILD, assembled in §5)

For a finite-dimensional complex normed space E and a compact Hausdorff complex manifold X
modelled on E, let A = 𝒜_X(X) be the Dolbeault algebra (F10) and O_X the sheaf of
holomorphic functions (F12). Assume the two analytic hypotheses H1 (Dolbeault–Grothendieck)
and H2 (local gauge lemma, weak form) on X. Then the functor

  J : Ho(P_A) ⥤ D_perf(X, O_X),  M ↦ α(M)

of C1 is an equivalence of categories.

Lean shape (names indicative, fixed in M0):

```lean
theorem blockPerf
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
    (h₁ : DolbeaultGrothendieck E X) (h₂ : LocalGaugeLemma E X) :
    (blockFunctor E X).Full ∧ (blockFunctor E X).Faithful ∧
      (blockFunctor E X).essImage = Perf (ringOf (holSheaf E X))
```

Here `blockFunctor E X : HoP (dolbeault E X) ⥤ DerivedCategory (Mod (ringOf (holSheaf E X)))` is
J with values in the whole derived category, and `Perf (ringOf (holSheaf E X))` is the
`ObjectProperty` of S9.c (v1.9: `Perf` takes the ring sheaf; v1.10: `Perf` and `Mod` take a
`RingSheaf X`, while `holSheaf E X` is a sheaf of `CommRingCat`, hence `ringOf`; `E` is explicit everywhere because the model space of
`ChartedSpace` is not an `outParam`). `blockFunctor` and `Perf` use the same derived-category
instance, `HasDerivedCategory.standard`, fixed once in `Statements.lean`.
⚠ **Why not `IsEquivalence` onto D_perf.** That J lands in D_perf is C2, which uses LL = H2, so a
functor `Ho(P_A) ⥤ D_perf(X)` cannot be defined before H2 is assumed. Fully faithful with
essential image exactly D_perf is equivalent to "the corestriction is an equivalence"; that
corollary is proved in `Checks.lean` (K6).

⚠ **Smoothness exponents.** In Mathlib `⊤ : ℕ∞ω` is ω (analytic) and `∞` is C^∞. Complex
manifolds use `∞` (complex C^∞ transition maps, i.e. holomorphic); all forms and partitions of
unity are real `∞`. Never write `⊤` for smoothness in this project.

**Relation to the sources.** This is [B, Thm 4.1.3] with D^b_coh replaced by D_perf, and
[A, Thm 7.4.3] at h = 0 for compact X. The step D_perf(X) = D^b_coh(X) is Z1 (LATER).

**What is deliberately not here** (all in §6): D^b_coh (Z1), triangulated structure (Z2),
twisted sheaves and curvature (Z3), proofs of H1 and H2 (Z4, Z5), the dg-level
quasi-equivalence (Z6), open manifolds (Z7), comparison with intrinsic forms (Z8).

### Dependency overview

```
A (algebra of cohesive modules) ─────────────┐
S (sheaf toolkit on compact spaces) ──────────┼──> C (comparison theorem) ──> M
F (Dolbeault sheaf) + H1 + H2 ────────────────┘
```

A and F1–F8 are independent of everything else and can run in parallel.

## 2. Layer A — cohesive modules over a dga (milestone M1)

**Setting for all of §2.** k a commutative ring. A a ℤ-graded k-algebra with A^q = 0 for
q < 0 and q > N, graded-commutative (ab = (−1)^{pq} ba for a ∈ A^p, b ∈ A^q), with a degree-one
k-linear derivation d satisfying the graded Leibniz rule and d² = 0. Write A^0 for the
(commutative) degree-0 part. Curvature c ∈ A^2 with dc = 0 is carried in the definitions
because it costs nothing; **this project only ever uses c = 0** (c ≠ 0 is Z3).

### A1 — Bounded graded-commutative dga (BUILD, S)
Definition of the setting above. Encoding: internal ℤ-grading, see conventions §5.
Lean: `GradedAlgebra` ✓; no graded-commutativity class in Mathlib (✗ as a class), so
state it as a field. `class GCDga` in `Algebra/Dga.lean`, with A^0 a commutative ring and A an
A^0-algebra built from graded commutativity. ⚠ ℤ-indexed (zero in negative degrees) rather than
ℕ-indexed.

### A2 — Connections (BUILD, S)
A connection on an A^0-module P is a k-linear ∇ : P → A^1 ⊗_{A^0} P with
∇(fe) = df ⊗ e + f∇e. Extension to A ⊗_{A^0} P by ∇(a ⊗ e) = da ⊗ e + (−1)^{|a|} a·∇e.
- **A2.a** Every finitely generated projective A^0-module has a connection.
  Proof: P ⊕ P' ≅ (A^0)^m; take ∇ = (1 ⊗ π) ∘ d^{⊕m} ∘ ι. [B, proof of Lemma 3.2.8].
- **A2.b** The difference of two connections is A^0-linear.

### A3 — Cohesive and quasi-cohesive modules (BUILD, M)
A *quasi-cohesive module* is a ℤ-graded A^0-module Q together with a k-linear operator 𝕏
of total degree 1 on A ⊗_{A^0} Q (left A-module, A acting on the left factor) such that
- Leibniz: 𝕏(a·m) = da·m + (−1)^{|a|} a·𝕏m, and
- flatness: 𝕏 ∘ 𝕏 = c·(−) (left multiplication; c = 0 here).

It is *cohesive* if moreover Q^p ≠ 0 for only finitely many p and each Q^p is finitely
generated projective. P_A denotes the cohesive ones. [B, Def 2.3.2] ⚠ left modules, see
conventions §3 for the translation to Block's right modules.
- **A3.a Components.** Restriction to Q determines 𝕏, with components
  𝕏^j : Q^p → A^j ⊗ Q^{p+1−j}; 𝕏^0 is an A^0-linear differential, 𝕏^1 is a connection
  on each Q^p (no sign in the left convention), 𝕏^j (j ≥ 2) are A^0-linear.
  [B, after Def 2.3.1], [A, eq. (2)].
- **A3.b** Flatness unfolds degree by degree into the equations of [A, eq. (2)].

### A4 — Hom complexes (BUILD, M)
For M₁ cohesive and M₂ quasi-cohesive: Hom^n(M₁, M₂) = k-linear maps φ of degree n with
φ(a·m) = (−1)^{n|a|} a·φ(m); differential δφ = 𝕏₂∘φ − (−1)^n φ∘𝕏₁.
- **A4.a** δ∘δ = 0, including with curvature (|c| even). [B, Lemma 2.3.4]
- **A4.b** Composition is associative, unital and satisfies the Leibniz rule for δ.
- **A4.c** Restriction to generators gives Hom^n(M₁, M₂) ≅ ⊕_p Hom_{A^0}(Q₁^p, (A ⊗ Q₂)^{p+n}).
- **A4.d** The sign convention agrees with Mathlib's `CochainComplex.HomComplex.δ` ✓
  (δz = z ≫ d + (−1)^{n+1} d ≫ z), conventions §2.

### A5 — Homotopy category Ho(P_A) (BUILD, S)
Objects: cohesive modules. Morphisms: H^0 of the Hom complex. A category (from A4.b),
k-linear. Homotopy equivalences = isomorphisms in Ho(P_A). [B, §2.4]

### A6 — Form-degree filtration (BUILD, S)
F^b Hom^n = maps whose components into A^{b'} ⊗ − vanish for b' < b. δ preserves it,
the filtration is finite (0 ≤ b ≤ N), and gr^b ≅ Hom_{A^0}(Q₁, A^b ⊗ Q₂) with differential
induced by 𝕏₁^0, 𝕏₂^0. [B, Prop 2.5.1], [A, Def 3.3.2]

### A7 — Finite filtration comparison (BUILD, S)
A map of finitely filtered complexes inducing quasi-isomorphisms on all gr^b is a
quasi-isomorphism. Proof: induction on the filtration length with the long exact sequence.
Replaces the spectral sequences in [B] and [A]. Lean: homology long exact sequence ✓
(`HomologicalComplex.HomologySequence`).

### A8 — Homotopy criterion (BUILD, M; not used by M)
Not on the critical path: no step of C or F uses it. Schedule it after F15, or with Z2.
A closed degree-0 φ : M₁ → M₂ between cohesive modules is an isomorphism in Ho(P_A)
iff φ^0 : (Q₁, 𝕏₁^0) → (Q₂, 𝕏₂^0) is a homotopy equivalence of complexes of
A^0-modules. [A, Lemma 3.3.5], [B, Prop 2.5.2]
- Proof (⇐): for every cohesive M, φ_* : Hom(M, M₁) → Hom(M, M₂) induces on gr^b the map
  Hom_{A^0}(Q, A^b ⊗ φ^0), a homotopy equivalence (any additive functor preserves them);
  by A7 φ_* is a quasi-isomorphism; Yoneda as in [A, Lemma 3.3.5].
- Proof (⇒): take the (0,0)-components of the homotopies.
- **A8.a** For bounded complexes of projective A^0-modules, homotopy equivalence ⇔
  quasi-isomorphism ([B]'s form). Lean: `CochainComplex.isKProjective_of_projective` ✓.

### A9 — Base change along dga maps (BUILD, S)
For a dga map f : A → B, M = (Q, 𝕏) ↦ f^*M with generators B^0 ⊗_{A^0} Q^p (Block's
E^• ⊗_{𝒜_1} 𝒜_2, [B, §2.7]) and 𝕏_B(b ⊗ m) = db ⊗ m + (−1)^{|b|} b·𝕏m; its total module
B ⊗_{B^0} ⨁_p (B^0 ⊗_{A^0} Q^p) is canonically B ⊗_A M.
Cohesive goes to cohesive (B^0 ⊗_{A^0} Q^p is finitely generated projective); a dg functor;
preserves homotopy equivalences. Used for restriction of cohesive modules to open subsets.
[B, §2.7 with ω = 0]
- **A9.a** Base change along a composite B → C is naturally isomorphic to the composite of
  base changes, compatibly with Hom complexes (used when restricting from X to U′ to V ⊆ U′).

### A10 — Cohesive modules from complexes (BUILD, S)
Let ρ : R → A^0 be a map of commutative rings with d∘ρ = 0, and (W, d_W) a bounded complex of
finitely generated projective R-modules. Then A ⊗_R W with 𝕏 = d ⊗ 1 + 1 ⊗ d_W is cohesive.
(v1.10) With the Koszul sign of conventions §2: 𝕏(a ⊗ w) = da ⊗ w + (−1)^{|a|} a ⊗ d_W w; on
generators 1 ⊗ w no sign appears, and this is what `fromComplex` implements.
- **A10.a Adjunction.** Hom^•_{P_A}(A ⊗_R W, M) ≅ Hom^•_R(W, M) as complexes, via
  precomposition with w ↦ 1 ⊗ w. Used in C4.

### A11 — Lifting theorem (BUILD, L)
Assume each A^b is flat over A^0. Let N = (Q, 𝕏) be quasi-cohesive, (P, ∂) a bounded complex of
finitely generated projective A^0-modules, and e^0 : (P, ∂) → (Q, 𝕏^0) a quasi-isomorphism.
Then there are a cohesive structure 𝔼 on A ⊗ P with 𝔼^0 = ∂ and a closed degree-0
e : (A ⊗ P, 𝔼) → N with e^0 as (0,0)-component.
[B, Thm 3.2.7(2) and Lemma 3.2.8], [A, Prop 3.3.4, case 2]
- Proof: choose connections on each P^p (A2.a). Construct 𝔼^b and e^b by induction on b.
  At each step the defect pair (P_b, Q_b) of [A, (10)–(12)] is a cycle in the cone of the
  map of A11.a, which is acyclic; a preimage gives (𝔼^{b+1}, e^{b+1}). Stop at
  b = N.
- ⚠ Re-derive every sign of [A, (10)–(12)] in the left convention before coding (Antweiler
  composes with a Koszul sign (−1)^{a'b}, conventions §4).
- **A11.a Internal hypothesis.** The proof only uses that, for every b, the map
  Hom_{A^0}(P, A^b ⊗ P) → Hom_{A^0}(P, A^b ⊗ Q) induced by e^0 is a quasi-isomorphism
  ([A]'s form). This follows from the assumptions: A^b ⊗ − preserves quasi-isomorphisms, and so
  does Hom out of a bounded complex of projectives.

### A12 — Total quasi-isomorphism (BUILD, S)
In A11, e is a quasi-isomorphism of total complexes. Proof: A7 with the form-degree filtration.
[A, proof of Prop 7.2.18]

### A13 — Bridge to Block's definition (BUILD, S; sanity)
The left-module definition is dg-equivalent to [B, Def 2.3.2] (right modules) for
graded-commutative A, with curvature c ↔ −c. Not on the critical path; proves the
conventions are faithful.

### A14 — Pretriangulated structure (LATER, = Z2)
Shifts, cones, triangulated Ho(P_A) [B, Prop 2.4.1]. Not needed for M.

## 3. Layer S — sheaf toolkit on a compact space (milestone M2a)

**Setting for all of §3.** X a compact Hausdorff space, `X : Type` (conventions §7).
Sheaves on `Opens X` with the standard topology. R a sheaf of commutative rings, modules are
Mathlib `SheafOfModules` ✓ (abelian ✓ `SheafOfModules.instAbelian`, Grothendieck abelian ✓,
hence enough injectives ✓ `IsGrothendieckAbelian.enoughInjectives`).

### S1 — Fine sheaves of rings (BUILD, S)
S is *fine* if for every finite open cover (U_i) of X there are ρ_i ∈ S(X) with Σρ_i = 1 and
supp ρ_i ⊆ U_i (support = closed set of points where the germ is nonzero). ✗ in Mathlib.
- **S1.a Extension by zero of sections.** If supp ρ ⊆ U and t ∈ M(U) for an S-module M,
  then ρt extends uniquely to a global section vanishing off supp ρ.
- Finite covers suffice because X is compact; ⚠ [A] uses softness and arbitrary covers.

### S2 — Γ is exact on modules over a fine sheaf (BUILD, S)
For S fine, M ↠ N an epimorphism of S-modules, Γ(X, M) → Γ(X, N) is surjective.
Proof: lift locally on a finite cover, glue with a partition of unity via S1.a.
Lean: epi ⇔ locally surjective (?) (`Sheaf.isLocallySurjective_iff_epi'` ✓ for sheaves of
types/abelian groups; check the module version).

### S3 — Acyclic complexes of S-modules (BUILD, S)
For S fine, an acyclic complex of S-modules has acyclic complex of global sections.
Proof: split into short exact sequences of cycles; apply S2. No sheaf cohomology needed.
Degreewise form: exactness of K at n gives exactness of Γ(K) at n (used in S10).
Replaces [A, Lemma 7.2.8] for complexes *of* S-modules (S-linear differentials); for complexes
whose terms are S-modules but whose differentials are not S-linear (C4), use S3.b.

### S3.b — Soft sheaves (BUILD, M; added v1.7)
X compact Hausdorff. Stalk-free softness: a sheaf F of abelian groups is *soft* if every section
over an open neighbourhood of a closed K agrees near K with a global section.
- **S3.b(i)** A sheaf of abelian groups on which the global sections of a fine sheaf of rings S
  act (by sheaf endomorphisms, additively, unitally, with ρ· = 0 on opens where ρ vanishes) is
  soft. In particular every S-module is soft.
- **S3.b(ii)** If 0 → A → B → C → 0 is exact and A is soft, Γ(B) → Γ(C) is surjective. Proof:
  finite cover with local lifts, shrink to closed sets (normality), glue inductively, correcting
  by global sections of A (softness).
- **S3.b(iii)** If A and B are soft, so is C.
- **S3.b(iv)** A bounded-below acyclic complex of sheaves (of R-modules) with soft terms has
  acyclic complex of global sections: the cycle sheaves are soft by induction from the bottom
  ((iii)), and (ii) lifts global cycles.
Replaces [A, Lemma 7.2.8] (Γ-acyclic terms, Stacks 015E) in C4 without sheaf cohomology.

### S4 — Projective modules over a fine sheaf (BUILD, M)
For S fine:
- **S4.a** Finite free S-modules are projective (Hom(S, M) = M(X) and S2).
- **S4.b** A locally finitely generated, locally projective S-module is a direct summand of
  a finite free module (finite cover, partition of unity). [A, Lemma 7.2.15, Cor 7.2.13]
- **S4.c** Γ is an equivalence between direct summands of finite free S-modules and finitely
  generated projective S(X)-modules; inverse P ↦ P̃, P̃(U) = S(U) ⊗_{S(X)} P.
  Moreover Hom_S(P̃, N) = Hom_{S(X)}(P, N(X)) for every S-module N. [A, remark after Def 7.2.5,
  and proof of Lemma 7.2.7]
- **S4.d** For such P̃, Γ(P̃ ⊗_S N) = P ⊗_{S(X)} Γ(N). (v1.9: proved in the stronger form
  "the sectionwise tensor product P̃ ⊗^{pre} N is already a sheaf", on any site and any object,
  for S a sheaf of commutative rings; needs no fineness.)
- Lean: `SheafOfModules.free` ✓, `IsLocallyFree` ✓.

### S5 — Restriction and extension by zero (BUILD, M)
- **S5.a** Restriction M ↦ M|U to an open U, exact. Lean: `overFunctor.{0}` ✓ through the
  project abbreviation `restr` (conventions §7, decided in P3); exact because it has adjoints on
  both sides.
- **S5.b** Extension by zero j_! for an open j : U → X: left adjoint to restriction, exact,
  stalks (j_!M)_x = M_x for x ∈ U and 0 otherwise. ✗ as such in Mathlib, but
  `SheafOfModules.pullback` ✓ (left adjoint of `pushforward` along a continuous functor) applied
  to the inclusion of opens may already be j_! (?); exactness still needs a stalk argument.
- **S5.c** Restriction preserves injective objects (it has the exact left adjoint j_!).

### S6 — Locality (BUILD, S)
A map of complexes of R-modules is a quasi-isomorphism iff its restrictions to the members of
some open cover are; a complex is acyclic iff locally acyclic. Also: a sectionwise homotopy
equivalence of presheaves of complexes induces a quasi-isomorphism of the associated sheaf
complexes.

### S7 — Hom sheaves (BUILD, M)
For complexes M, N of R-modules, 𝓗om(M, N) is the complex of sheaves of R-modules with
𝓗om(M, N)(V) = Hom^•(M|V, N|V). ✗ for `SheafOfModules` (Mathlib has `presheafHom` ✓ for
type-valued Homs only).
- **S7.a′** (v1.9, replaces S7.a) *Termwise source action.* Let a ring T act on each term M^i
  of a complex of R-modules by R-linear sheaf endomorphisms (additively, unitally; not
  necessarily commuting with the differential). Precomposition gives an action of T on each
  term 𝓗om(M, N)^n by R-linear sheaf endomorphisms, additive and unital, and vanishing on V
  whenever the action on every M^i vanishes on V. It is not a chain map. With T = S(X) for a
  fine S this is the input of S3.b(i) (`IsSoft.of_action`), used in C4 step 2. (The old S7.a,
  "a complex of S-modules via the source", is false as stated when the differentials of M are
  not S-linear, which is exactly the case in C3/C4.)
- **S7.b** If W is strictly perfect (S9), 𝓗om(W, −) preserves quasi-isomorphisms.
- **S7.c** If I is a bounded-below complex of injectives, then 𝓗om(C, I) is acyclic for every
  acyclic C (sections over V use S5.c and `CochainComplex.isKInjective_of_injective` ✓).

### S8 — Tensor products and K-flat resolutions (BUILD, L)
This package replaces Malgrange's flatness theorem (feasibility report, G6).
- **S8.a** Tensor product and base change of sheaves of modules along R → S. Lean:
  `PresheafOfModules` monoidal ✓ plus sheafification ✓; no monoidal structure on
  `SheafOfModules` ✗.
- **S8.b** Flat R-modules; j_! R|_U is flat (stalks, S5.b).
- **S8.c** Every R-module is a quotient of a direct sum of modules j_! R|_U.
- **S8.d** Every bounded-above complex has a quasi-isomorphism from a bounded-above complex
  of flat modules; bounded-above complexes of flats are K-flat. [Stacks, chapter *Cohomology of
  Sheaves*, section on K-flat complexes; look up the exact tags in phase 2].
- **S8.e** If K is K-flat and acyclic then K ⊗ L is acyclic for every L (resolve L by S8.d).
- **S8.f** Restriction to opens preserves K-flatness (use j_!).
- **S8.g** If K, K′ are K-flat and connected by a roof of quasi-isomorphisms, so are
  S ⊗_R K and S ⊗_R K′ (resolve the middle term by S8.d). (v1.9) Lean form: for a single
  quasi-isomorphism K → K′ between K-flat complexes. For a roof K ← L → K′ with K′ bounded
  (e.g. strictly perfect) and L arbitrary, as in `IsPerfect`: first replace L by τ_{≤b}L
  (`CochainComplex.truncLE`; L → K′ a quasi-isomorphism with K′ in degrees ≤ b makes
  τ_{≤b}L → L one), then resolve τ_{≤b}L by S8.d and apply S8.g to both legs.

### S9 — Perfect complexes (BUILD, S)
- **S9.a** A complex of R-modules is *strictly perfect* if it is bounded and each term is a
  direct summand of a finite free module. [A, Def 7.2.11]
- **S9.b** A complex K is *perfect* if every point has an open neighbourhood U, a strictly
  perfect P on U and quasi-isomorphisms K|U ← L → P (`QuasiIso` ✓). Equivalent to Q(K|U) ≅ Q(P)
  in D(R|U), but avoids a derived category for every open set.
  Lean: with `overFunctor` (chosen in P3), "strictly perfect on U" lives over `R.over U` on
  the over-site `Over U`, not over a ring on `Opens U`; S9.d and S10 must use the same API.
- **S9.c** D_perf(X, R) is the full subcategory of `DerivedCategory (SheafOfModules R)` ✓ on
  objects isomorphic to Q(K) with K perfect (perfectness is invariant under
  quasi-isomorphism).
- **S9.d** On compact X every perfect complex is globally bounded (uniform degree range and
  number of generators), by a finite cover.

### S10 — Globalization over a fine sheaf (BUILD, L)
For S fine, every globally bounded perfect complex of S-modules is quasi-isomorphic to a
strictly perfect complex of S-modules. [A, Lemma 7.2.16, with Lemmas 7.2.9, 7.2.10]
- Sub-lemmas (v1.8), on any space Y and sheaf of rings R on Y (applied on opens U through
  Mathlib's `Opens.sheafOfModulesEquivOver`):
  - **S10.a Local null-homotopy.** A chain map from a strictly perfect complex to an acyclic
    complex is locally null-homotopic (finitely many sections, degree by degree, by local
    surjectivity of epis, S2 local part).
  - **S10.b Local lifting.** For E strictly perfect and a quasi-isomorphism s : L → K, every
    chain map E → K lifts locally through s up to homotopy (S10.a on the cone of s).
  - **S10.c Local splitting.** An epimorphism onto a direct summand of a finite free module
    splits locally. Hence, for a bounded acyclic complex C in degrees [m, n] whose terms are
    summands of finite free modules except possibly C^{m+1}: splitting from the top, the cycle
    sheaves Z^i (i ≥ m + 2) are locally such summands, and C^{m+1} ≅ C^m ⊕ Z^{m+2} locally,
    so C^{m+1} is locally a summand of a finite free module too.
  - **S10.d** The top homology sheaf of a strictly perfect complex is locally finitely
    generated (S10.c on the part above it).
  - **S10.e Global generation.** For R fine on compact X, a locally finitely generated
    R-module is a quotient of a finite free module (finite cover, S1.a).
- Proof outline (v1.8): by S9.d, K has local strictly perfect models in [a, b] and homology in
  [a, b]. (1) Downward induction from b to a − 1 builds finite free S-modules Fⁿ and F → K,
  iso on homology above the current degree, as in [TT, Lemma 1.9.5]: the next homology sheaf
  of the cone is locally the top homology of the cone of a local lift F|U → P_U (S10.b), a
  strictly perfect complex, so locally finitely generated (S10.d), hence a quotient of a
  finite free module (S10.e); lift to global cycles (S4.a). (2) B = coker(F^{a−1} → F^a) and
  P = (B → F^{a+1} → ⋯ → F^b), with P → τ_{≥a}K ≃ K a quasi-isomorphism. Locally the model
  P_U lifts to a quasi-isomorphism P_U → P|U (S10.b); its cone is bounded and acyclic in degrees
  [a − 1, b] with terms summands of finite free modules except cone^a = P_U^{a+1} ⊕ B;
  S10.c makes B locally a summand of a finite free module, and S4.b globally. So P is strictly
  perfect, hence K-projective (S4.a, S11), and P → τ_{≥a}K lifts to P → K (S11).
- ⚠ The proof of [A, Lemma 7.2.16] applies [A, Lemma 7.2.10] on small opens U, which needs free
  S|U-modules to be projective (true for soft S on paracompact U, not given by S1 on compact
  X); replaced by local lifting and local splitting (S10.a–c) and S4.b (v1.8).
- ⚠ Compactness replaces [A, Lemma 7.2.12] (finite covering dimension).

### S11 — Derived-category facts from Mathlib (BUILD, S: wiring only)
- Bounded-below injective resolutions: `exists_quasiIso_injective` ✓
  (`DerivabilityStructureInjectives`).
- Hom in D into a K-injective complex equals homotopy classes:
  `CochainComplex.IsKInjective` ✓, `Qh_map_bijective_of_isKInjective` ✓.
- Bounded complexes of projectives are K-projective: `isKProjective_of_projective` ✓.
- Universes: `HasDerivedCategory.standard` ✓ as a local instance (conventions §7).

## 4. Layer C — the comparison theorem (milestone M2b)

### C0 — Resolving data (BUILD, S: a structure)
The abstract input, Antweiler's Assumptions 7.2 at h = 0 in the form used here. It is split in
two structures: **C0.a `PreResolvingData`** has every field below except the resolution
condition and LL; **C0.b `ResolvingData`** extends it by those two. C1 (the functor J) uses only
C0.a, so J can be defined for X without H1 and H2 (see §1).
- X compact Hausdorff, `X : Type`; R a sheaf of commutative ℂ-algebras on X.
- For each open U a bounded graded-commutative dga 𝒜(U) (A1, degrees ≤ N), restriction maps
  that are dga maps and functorial; each 𝒜^q a sheaf of ℂ-modules.
- 𝒜^0 a fine sheaf of commutative rings (S1); each 𝒜^q a locally free 𝒜^0-module of finite
  rank.
- (v1.9, audit F1) **One carrier for A⁰.** The sheaves are not separate data: they are derived
  from the presheaf of dgas U ↦ (A_U, 𝒜_U). 𝒜^0 is the `Sheaf _ CommRingCat` with
  𝒜^0(U) = `CommRingCat.of ↥(𝒜_U 0)` and the restriction maps of the dgas; it is used as a
  `RingSheaf` through `ringOf` (S8). 𝒜^q(U) = ↥(𝒜_U q) as an 𝒜^0(U)-module (`GCDga.piece`).
  The sheaf conditions are fields. So Γ(X, 𝒜^0) and A⁰ = ↥(𝒜_X 0) are the same type with the
  same ring structure (prototype P7: `rfl` at instance transparency), modules over Γ(X, 𝒜^0)
  are `𝒜 0`-modules (A11 applies to P = Γ(P̃) without transport), and ρ_U : R(U) →+* ↥(𝒜_U 0)
  is the ring map A10 takes.
- ρ : R → 𝒜^0 a map of sheaves of rings with d∘ρ = 0 such that
  0 → R → 𝒜^0 → 𝒜^1 → ⋯ is exact (a resolution).
- (v1.10) **Flat curvature: c = 0** in every 𝒜(U) (a field of C0.a). Needed for α(M) to be a
  complex (𝕏² = c·(−)) and for `fromComplex` in LL (A10 takes `hc : c = 0`). It holds for the
  Dolbeault dga by definition (F10), so F14 fills it; it is not an analytic hypothesis.
  Curved data (c ≠ 0) is the twisted case Z3 (LATER).
- **LL (local lifting).** For every cohesive module M over 𝒜(X) and x ∈ X, there are an open
  x ∈ U′, a bounded complex W of finitely generated projective R(U′)-modules and a homotopy
  equivalence in P_{𝒜(U′)} between M|U′ (A9) and 𝒜(U′) ⊗_{R(U′)} W (A10).
- ⚠ [A] Assumption 6 is a sheaf version for modules on every open set. C2 and C4 only ever
  apply LL to restrictions of global modules, so this weaker, sectionwise form suffices; it is
  also the form of the gauge step in Block's proof of [B, Lemma 4.1.5].
- ⚠ The first half of [A] Assumption 5 (𝒜 K-flat over R) is **not** assumed: C5 uses S8
  instead. (Its second half, each 𝒜^q flat over 𝒜^0, follows from local freeness above.)

### C1 — The functor J (BUILD, M)
Input: pre-resolving data (C0.a) only; J : Ho(P_A) ⥤ D(R), into the whole derived category.
For a cohesive module M = (Q, 𝔼) over A = 𝒜(X), α(M) is the complex of sheaves of R-modules
α(M)^n(V) = ⊕_{p+q=n} 𝒜^q(V) ⊗_{𝒜^0(X)} Q^p with the differential of the base change M|V (A9).
- **C1.a** It is a sheaf (Q^p is finitely generated projective; S4.c). R acts through ρ, and
  the differential is R-linear because d∘ρ = 0.
- **C1.b** Closed degree-0 maps go to chain maps, homotopies to homotopies, so
  J : Ho(P_A) ⥤ K(R) ⥤ D(R). [B, §4.1, the sheaves ℰ_X]
- **C1.c** α(M)|U ≅ α_U(M|U), naturally (sheaf on U from the cohesive module over 𝒜(U)).

### C2 — J lands in perfect complexes (BUILD, S)
For every cohesive M, α(M) is perfect (S9.b). [A, Lemma 7.2.17]
Proof: by LL and C1.c, α(M)|U′ is homotopy equivalent to 𝒜|U′ ⊗_R W̃, W̃(V) = R(V) ⊗ W
strictly perfect; W̃ → 𝒜 ⊗_R W̃ is a quasi-isomorphism because ρ is a resolution and each
W̃^p is a direct summand of a finite free module.
- (v1.11) **Proof via C7** (the identification above was not itemized). X compact Hausdorff.
  e : Tot(𝒜(U′) ⊗ W) → Tot(N_{W̃}(U′)), a ⊗ (α ⊗ w) ↦ aα ⊗ η(1 ⊗ w̃) with w̃ ∈ Γ(W̃) the section
  corresponding to w. gr^0 Ξ_e is an isomorphism (both sides summands of finite free
  𝒜⁰|U′-modules with the same global sections, S4.c on the over-site), so Ξ_e is a
  quasi-isomorphism (C7.f). u ≫ Ξ_e = (W̃ → T(W̃)) (both determined by Γ, S4.c), a
  quasi-isomorphism by C7.d; so u is one (2-out-of-3).
- (v1.9, audit F5) **The roof.** `IsPerfect` wants α(M)|U′ ← L → P. Take L := W̃, P := W̃,
  g := id and f := α(h) ∘ u : W̃ → 𝒜|U′ ⊗_R W̃ → α(M)|U′, where h : 𝒜(U′) ⊗ W → M|U′ is the
  direction of the LL homotopy equivalence pointing into M|U′ (a homotopy equivalence, so
  α(h) is a quasi-isomorphism).
- (v1.9) **W̃ without fineness.** R|U′ is not fine. W̃ is built on the over-site of U′ from
  S4.c, whose parts used here (`exists_globalSections_iso`, the Hom bijection) need neither
  fineness nor compactness; transfer to the over-site through
  `TopologicalSpace.Opens.sheafOfModulesEquivOver`, or restate S4.c on any site. The
  differentials of W lift uniquely by the Hom bijection.

### C3 — Hom sheaves of cohesive modules (BUILD, S)
For cohesive M₁, M₂ over A, ℋ(M₁, M₂)(V) = Hom^•_{P_{𝒜(V)}}(M₁|V, M₂|V). It is a complex of
sheaves of R-modules whose terms are 𝒜^0-modules (A4.c and S4.c); ⚠ the differential is not
𝒜^0-linear (δ(fφ) = df·φ + f·δφ). ℋ(M₁, M₂)(X) = Hom^•_{P_A}(M₁, M₂).
- **C3.a** (v1.9, audit F3) *The actions needed for softness.* (i) 𝒜^0(X) acts on each term
  α(M₁)^i by R-linear sheaf endomorphisms (multiplication; R-linear because R → 𝒜^0 is a map
  of commutative rings), additively, unitally, vanishing on V where f|V = 0; by S7.a′ it acts
  on each term of 𝓗om_R(α(M₁), N) for every N. (ii) 𝒜^0(X) acts on each term of ℋ(M₁, M₂)
  (by restriction and multiplication in 𝒜(V)), with the same three properties. Both actions
  are termwise, not chain maps; these are the inputs of S3.b(i) in C4 step 2.

### C4 — Full faithfulness (BUILD, L)
J is fully faithful. [A, Prop 7.2.19]
1. Choose a bounded-below injective resolution r : α(M₂) → I (S11).
2. Ψ : ℋ(M₁, M₂) → 𝓗om_R(α(M₁), I), φ ↦ r ∘ α(φ), is a map of complexes of sheaves of
   R-modules; 𝒜^0(X) acts on the terms of both sides (C3.a, S7.a′), hence they are soft
   (S3.b(i)), but the differentials are not 𝒜^0-linear (v1.7). The terms of cone(Ψ) are
   biproducts of terms of both sides, soft by the closure lemmas of S3.b.
3. Ψ is a quasi-isomorphism of sheaf complexes. Locally (S6), at x take U′ and the homotopy
   equivalence h : 𝒜(U′) ⊗ W → M₁|U′ from LL. In the square
   ```
   ℋ(M₁,M₂)|U′ ───Ψ───> 𝓗om_R(α(M₁), I)|U′
       │ h^*                  │ α(h)^*
   ℋ(𝒜⊗W, M₂) ───Ψ───> 𝓗om_R(𝒜 ⊗_R W̃, I)
       │ ≅ (A10.a)            │ u^*,  u : W̃ → 𝒜 ⊗_R W̃
   𝓗om_R(W̃, α(M₂)) ──r_*──> 𝓗om_R(W̃, I)
   ```
   both upper vertical maps are sectionwise homotopy equivalences, u^* is a
   quasi-isomorphism by S7.c (cone(u) is acyclic), and r_* is one by S7.b.
   (v1.11) Lean: the square lives on the over-site of U′, so it needs ℋ_{U′} (C3's section data
   with base U′) with ℋ(M₁, M₂)|U′ ≅ ℋ_{U′}(M₁|U′, M₂|U′), and Ψ_{U′} compatible with Ψ under
   this iso, `restrSheafOfIso` and `homComplexOverIso`; u is C2's map.
4. Γ(X, Ψ) is a quasi-isomorphism: S3.b(iv) applied to cone(Ψ), bounded below (α(M₁) and
   ℋ bounded, I bounded below) with soft terms (v1.7; S3 does not apply, see C3).
5. Take H^0: Hom_{Ho(P_A)}(M₁, M₂) ≅ H^0 Hom(α(M₁), I) ≅ Hom_{D(R)}(α(M₁), α(M₂)) (S11),
   and check that the composite is J on morphisms.

### C5 — Essential surjectivity (BUILD, L)
Every object of D_perf(X, R) is isomorphic to some J(M). [A, Prop 7.2.18], ⚠ K-flat variant.
- **C5.0 Tensor input** (the only place where flatness enters). For every perfect K there is a
  K′ connected to K by quasi-isomorphisms such that (i) K′ → 𝒜 ⊗_R K′ is a quasi-isomorphism and
  (ii) 𝒜^0 ⊗_R K′ is a globally bounded perfect complex of 𝒜^0-modules. Steps 1, 2 and 6 below
  prove C5.0 with S8; steps 3–5 and 7 use only C5.0. Keeping this interface lets C5 be written
  before S8 is finished, and keeps open the alternative proof by Malgrange flatness (K′ = K).
1. Let K be perfect. It is globally bounded (S9.d); replace it by a bounded complex
   (truncations `CochainComplex.truncGE` ✓, `truncLE`) and then by a K-flat
   resolution K′ → K (S8.d).
2. 𝒜^0 ⊗_R K′ is a globally bounded perfect complex of 𝒜^0-modules (S8.f, S8.g). (v1.9,
   audit F4) The middle term of each local roof K′|U ← L → P_U is unbounded; truncate it to
   τ_{≤b}L and resolve by S8.d before applying S8.g, as in S8.g's v1.9 note.
3. By S10 there is a strictly perfect complex P̃ of 𝒜^0-modules quasi-isomorphic to it; P̃ is
   K-projective (S4.a, S11), so the quasi-isomorphism is an honest map f^0 : P̃ → 𝒜^0 ⊗_R K′.
4. Pass to global sections: P = Γ(P̃) is a bounded complex of finitely generated projective
   𝒜^0(X)-modules (S4.c); Γ(f^0) is a quasi-isomorphism (S3); N := the quasi-cohesive module
   of C5.a. Each 𝒜^q(X) is projective, hence flat, over 𝒜^0(X) (S4.b, S4.c), so A11 gives a
   cohesive M on 𝒜(X) ⊗ P and a closed e : M → N extending Γ(f^0).
5. Localize e to a map of complexes of sheaves α(M) → 𝒜 ⊗_R K′ (C5.b); it is a
   quasi-isomorphism (C5.c).

(v1.11) **C5.a–c are proved via C7** with U = X and K = K′, which replaces the sheaf-tensor
arguments below (they relied on a base-change associativity that S8.a does not contain, and on
an 𝒜(V)-action on sections of a sheafified tensor product): N := N_{K′}(X) (C7.c); A11 with
e⁰ = Γ(f⁰) (a quasi-isomorphism by S3: 𝒜⁰ is fine, no boundedness needed); C5.b := Ξ_e (C7.e);
C5.c := C7.f, with gr^0 Ξ_e ≅ f⁰ via Γ (S4.c); step 7 goes through T(K′) and C7.d. The text
below is kept as the informal picture.

Sub-items (v1.9, audit F2):
- **C5.a Quasi-cohesive structure on Γ(𝒜 ⊗_R K′).** Q^p := Γ(𝒜^0 ⊗_R K′^p) (an
  𝒜^0(X)-module). This is *not* A10 (K′ is not finitely generated projective, and
  Γ(𝒜 ⊗_R K′) ≠ 𝒜(X) ⊗_{R(X)} Γ(K′)). Instead: 𝒜^q ⊗_R K′^p ≅ 𝒜^q ⊗_{𝒜^0} (𝒜^0 ⊗_R K′^p)
  (base-change associativity, S8.a), and Γ of the right side is 𝒜^q(X) ⊗_{𝒜^0(X)} Q^p by S4.d
  (𝒜^q is a summand of a finite free 𝒜^0-module, F11 and S4.b). 𝕏 is Γ of the sheaf operator
  𝕏(b ⊗ k) = db ⊗ k + (−1)^{|b|} b ⊗ d_{K′}k (well defined because d∘ρ = 0), transported along
  these isomorphisms; Leibniz and 𝕏² = 0 hold sectionwise, hence after transport.
  (v1.10, sign fix) The Koszul sign is essential: without it Leibniz fails whenever 𝒜 ≠ 𝒜^0
  (𝕏(a·(b⊗k)) = da·(b⊗k) + (−1)^{|a|} a·𝕏(b⊗k) needs (−1)^{|a|+|b|} on ab ⊗ dk). This operator
  is the differential of `tensorC R 𝒜^• K′` with 𝒜^• as the **first** factor (Mathlib puts
  the sign on the second factor), as fixed in conventions §2. Its (0,0)-component is
  Γ(𝒜^0 ⊗_R d_{K′}), so A11's target complex (Q, 𝕏^0) is Γ(𝒜^0 ⊗_R K′).
- **C5.b The sheaf map.** On V, e_V : 𝒜(V) ⊗_{𝒜^0(X)} P → Γ(V, 𝒜 ⊗_R K′),
  a ⊗ p ↦ a·res_V(e(1 ⊗ p)). (v1.10) No sign: e is closed of degree 0, and a degree-0 map
  satisfies φ(a·m) = a·φ(m) (conventions §2, Hom^n with n = 0). For a map of degree n the
  generator extension carries (−1)^{n|a|}. N|V is *not* the base change of N, so A9 does
  not supply the map; α(M)(V) is A9's base change of M, and e_V is defined on generators. It
  is a chain map because res_V is a dga map and e is closed; it is compatible with
  restriction, so it defines α(M) → 𝒜 ⊗_R K′ (S4.c Hom property on each α(M)^n, which is a
  finite sum of summands of finite free 𝒜^0-modules).
- **C5.c Quasi-isomorphism.** Form-degree filtration on both sides as complexes of sheaves of
  abelian groups; A7 applies as stated (`quasiIso_of_finite_filtration` is proved in any
  abelian category). On gr^b the map is 𝒜^b ⊗_{𝒜^0} f^0 (up to the shift sign of A12), a
  quasi-isomorphism because 𝒜^b is a summand of a finite free 𝒜^0-module (tensoring with it
  preserves quasi-isomorphisms; flat by S8.b, or directly).
6. K′ → 𝒜 ⊗_R K′ is a quasi-isomorphism (𝒜^• first, as in C5.a): its cone is cone(ρ) ⊗_R K′, acyclic because ρ is a
   resolution and K′ is K-flat.
7. Hence α(M) ≅ 𝒜 ⊗_R K′ ≅ K′ ≅ K in D(R).

### C6 — Comparison theorem (BUILD, S)
For resolving data, J : Ho(P_{𝒜(X)}) ⥤ D(R) is full and faithful (C4) with essential image
exactly D_perf(X, R) (C2, C5); equivalently its corestriction to D_perf is an equivalence.
[A, Thm 7.2.20 at h = 0], [CHL, Thm 7.10] (full faithfulness: [CHL, Prop 7.4]).

### C7 — The explicit model T(K) of 𝒜 ⊗_R K (BUILD, L) (v1.11)
Used by C2, C4 step 3 and C5.a–c in place of the sheafified tensor product, whose sections are
not computable. Setting: resolving data, X compact Hausdorff, an open U, the over-site of U.
For a complex K of R|U-modules let F := 𝒜⁰ ⊗_R K (S8 `sheafBC` along ρ), a complex of
𝒜⁰|U-modules, and
  T(K)^n(V) := degree-n part of 𝒜(V) ⊗_{𝒜⁰(V)} ⊕_p F^p(V) = ⊕_q 𝒜^q(V) ⊗_{𝒜⁰(V)} F^{n−q}(V),
with plain tensor products of sections (A3's `Tot` over 𝒜(V), generators F^p(V)).
- **C7.a Sheaf.** T(K)^n is a sheaf of R|U-modules: 𝒜^q|U is a summand of a finite free
  𝒜⁰|U-module (S4.b on X, restricted), so T(K)^n is sectionwise a retract of a finite power of
  ⊕_q F^{n−q}, compatibly with restriction.
- **C7.b Connection.** ∇ : F^p → 𝒜¹ ⊗_{𝒜⁰} F^p (target a sheaf by C7.a) is the sheafification
  of α ⊗ k ↦ dα ⊗ η(1 ⊗ k) on the presheaf tensor 𝒜⁰(V) ⊗_{R(V)} K^p(V), η the unit of
  sheafification (R-linear, well defined since d∘ρ = 0). ∇(αf) = dα ⊗ f + α∇f, ∇ commutes with
  d_F, and ∇² = 0 (in 𝒜² ⊗ F): checked where f comes from the presheaf, then everywhere (η is
  locally surjective; the target is separated).
- **C7.c Differential.** 𝕏_V(a ⊗ f) = da ⊗ f + (−1)^{|a|}(a·∇f + a ⊗ d_F f) (Koszul sign of
  v1.10; ∇ extended to 𝒜 ⊗ F by Leibniz). Leibniz holds by construction, 𝕏² = 0 from C7.b and
  c = 0, and 𝕏 commutes with restriction. Hence (F^•(V), 𝕏_V) is a quasi-cohesive module N_K(V)
  over 𝒜(V) (A3; generators not finitely generated), the restrictions are closed degree-0 maps
  semilinear along res, and T(K) is a complex of sheaves of R|U-modules.
- **C7.d Comparison with tensorC.** The presheaf map 𝒜^q(V) ⊗_{R(V)} K^p(V) → T(K)(V),
  a ⊗ k ↦ a ⊗ η(1 ⊗ k), is locally bijective (a retract of a finite power of η), so it induces
  an isomorphism tensorC(𝒜^•|U, K) ≅ T(K) of complexes (differentials compared on a ⊗ k).
  With C5 step 6 on any site: for K bounded above with flat terms, the map K → T(K),
  k ↦ 1 ⊗ η(1 ⊗ k), is a quasi-isomorphism.
- **C7.e Comparison map.** For M cohesive over 𝒜(U) and e : Tot(M) → Tot(N_K(U)) closed of
  degree 0, Ξ_e : α_U(M) → T(K) is on V the A9 extension (`extAlong`) of res_V ∘ e; it is a map
  of complexes of sheaves (closedness, C7.c).
- **C7.f Quasi-isomorphism criterion.** Filter α_U(M) and T(K) by form degree (A6 `filTot`,
  sectionwise; subsheaves by C7.a and `degree_local`), with short exact sequences sectionwise
  (A12 `filSC_shortExact`) and A7 in sheaves. gr^b Ξ_e is a retract of a finite power of
  gr^0 Ξ_e (the splitting of 𝒜^b over 𝒜⁰), so Ξ_e is a quasi-isomorphism as soon as
  gr^0 Ξ_e : (V ↦ 𝒜⁰(V) ⊗_{𝒜⁰(U)} Q^•) → F is one.

## 5. Layer F — the Dolbeault sheaf (milestone M3)

**Setting.** E a finite-dimensional complex normed space, n = dim_ℂ E, `E : Type`. F a
finite-dimensional complex normed space of values (F = ℂ for the main theorem; general F is
for Z3 and Z8). M a complex manifold modelled on E (`ChartedSpace E M`,
`IsManifold 𝓘(ℂ, E) ∞ M`), not necessarily compact. Only F = ℂ is needed on the critical path;
F2–F4 and F7 are stated for general F because it is free there. Conventions §6 fixes all normalizations.

### F1 — Realification (BUILD, S)
`IsManifold 𝓘(ℝ, E) ∞ M` from `IsManifold 𝓘(ℂ, E) ∞ M`, same charts. Proof: transition
maps are `ContDiffOn ℂ ∞`, hence `ContDiffOn ℝ ∞` (`ContDiffOn.restrict_scalars` ✓).
`NormedSpace ℝ E` comes from the instance `NormedSpace.complexToReal` ✓. The realification
lemma itself is ✗ in Mathlib. Provide it as a theorem plus local instance; avoid a global
instance (conventions §7).

### F2 — The fibre Λ^{0,q}(E; F) (BUILD, S)
Ē = `Conj E`: E with the conjugate ℂ-action, a type synonym declared with `def` (not `abbrev`),
normed like E. ✗ in Mathlib. A ℂ-linear map on Ē is an antilinear map on E, and a ℂ-linear map
of E (for example DG(x) for holomorphic G) is also ℂ-linear on Ē.

Λ^{0,q}(E; F) := `Conj E [⋀^Fin q]→L[ℂ] F`, a ℂ-normed space (`instNormedAddCommGroup`,
`instNormedSpace` ✓). ⚠ This replaces the earlier subtype of ℝ-alternating maps antilinear in
each slot: the same maps, without membership side conditions, and Mathlib's exterior-power API
applies to Ē directly. P2 confirmed `Conj E` works without instance diamonds; no fallback.
- **F2.a** Λ^{0,0}(E; F) ≅ F (`constOfIsEmpty` ✓).
- **F2.b Exterior-algebra bridge.** Φ_q : ⋀^q_ℂ(Dual_ℂ Ē) ≃ Λ^{0,q}(E; ℂ),
  φ₁ ∧ ⋯ ∧ φ_q ↦ (v ↦ det(φ_i(v_j))), from `exteriorPower.pairingDual` ✓
  (`pairingDual_ιMulti_ιMulti` ✓) and `exteriorPower.alternatingMapLinearEquiv` ✓, plus
  continuity in finite dimension. Bijective via the basis lemmas `ιMultiDual_apply_diag`,
  `ιMultiDual_apply_nondiag` ✓ and `Module.Basis.exteriorPower` ✓; packaging it as an
  equivalence is ✗.
- **F2.c** Λ^{0,q} = 0 for q > n; dim = C(n, q)·dim F; a basis of E gives the basis dz̄_I.

### F3 — The ∂̄-operator on open subsets of E (BUILD, S)
For ω : E → Λ^{0,q}(E; F), smooth near x: D″ω(x) = ½ (Dω(x) + i·Dω(x) ∘ J), the antilinear part
of the real derivative (J = multiplication by i), regarded as an element of
`Conj E →L[ℂ] Λ^{0,q}(E; F)`; and ∂̄ω(x) = `alternatizeUncurryFin` (D″ω(x)) ✓, over ℂ on Ē.
- **F3.a** D″ω(x) is ℂ-linear on Ē (the defining computation).
- **F3.b** ℂ-linear in ω, local (depends on the germ), smooth in, smooth out.
- **F3.c** (sanity) ∂̄ω is the (0, q+1)-part of `extDeriv` ✓ ω.

### F4 — ∂̄∂̄ = 0 (BUILD, S)
For ω C² near x, ∂̄(∂̄ω)(x) = 0. Proof: copy `extDerivWithin_extDerivWithin_apply` ✓ with D″ in
place of D, over ℂ on Ē. The ℂ-bilinear map (u, v) ↦ D″D″ω(x)(u, v) on Ē is symmetric (from
`ContDiffAt.isSymmSndFDerivAt` ✓ over ℝ); conclude with
`alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric` ✓.

### F5 — Product on the total fibre (BUILD, M)
The total fibre is Λ^{0,•}(E) := Π_{q ≤ n} Λ^{0,q}(E; ℂ), a finite product of normed spaces.
Its multiplication is transported along Φ = (Φ_q)_q from `ExteriorAlgebra ℂ (Dual_ℂ Ē)`, which
is graded (`ExteriorAlgebra.gradedAlgebra` ✓) and graded-commutative on generators
(`ιMulti_mul_ιMulti_anticomm` ✓). Associativity, unit and graded commutativity come for free;
continuity by finite dimension. ⚠ This replaces a hand-built shuffle product, whose
associativity is not in Mathlib (only `AlternatingMap.domCoprod` ✓ and its alternatization
lemmas are).
- **F5.a Laplace formula.** For a 1-form φ and a q-form ω, φ ∧ ω = `alternatizeUncurryFin`
  (v ↦ φ(v) • ω), i.e. (φ ∧ ω)(v₀, …, v_q) = Σ_i (−1)^i φ(v_i) ω(…, v̂_i, …). From expansion of
  the determinant along the first row (`Matrix.det_succ_row_zero` ✓). This is the only link
  between the product and the analysis.
- **F5.b** F-valued forms are a module over Λ^{0,•}(E) via Λ^{0,q}(E; F) ≅ Λ^{0,q}(E; ℂ) ⊗ F
  (later only).

### F6 — Leibniz rule (BUILD, S)
∂̄(α ∧ β) = ∂̄α ∧ β + (−1)^p α ∧ ∂̄β. Proof: (i) ∂̄(f·η) = ∂̄f ∧ η + f·∂̄η for a function f, by
the product rule and F5.a; (ii) constant forms are ∂̄-closed; (iii) locally every form is
Σ_I f_I dz̄_I (F2.c); expand and use graded commutativity. No general alternation identity is
needed.

### F7 — Holomorphic pullback (BUILD, M)
For G : V → V′ holomorphic between open subsets of E, G^*ω(x) = ω(G x) ∘ DG(x)
(`compContinuousLinearMap` ✓), with DG(x) regarded as a ℂ-linear map of Ē.
- **F7.a** G^* ∂̄ = ∂̄ G^*. Proof: copy `extDerivWithin_pullback` ✓ with D″. The
  second-derivative term is antilinear in the new slot, so D″ keeps it, and alternation kills
  it (`alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero` ✓).
- **F7.b** On fibres G^* is the algebra map induced by the dual of DG(x) on the exterior algebra
  (`ExteriorAlgebra.map`), so it respects products; it respects multiplication by functions.
- **F7.c** (G ∘ H)^* = H^* G^*, id^* = id.

### F8 — Cauchy–Riemann (BUILD, S)
For f : E → F real C^∞ on an open V: ∂̄f = 0 on V ⇔ f is `ContDiffOn ℂ ∞` on V.
Proof (⇒): ∂̄f = 0 means Df(x) is ℂ-linear (`differentiableAt_iff_restrictScalars` ✓). A
symmetric ℝ-bilinear map that is ℂ-linear in one slot is ℂ-linear in both, so the derivative of
fderiv ℂ f is again ℂ-linear; induct. ⚠ This avoids several-variable Cauchy or Osgood theory,
which Mathlib does not have (✗ "Osgood", "Hartogs").

### F9 — The sheaves 𝒜^{0,q}_M(F) and 𝒜^{0,•}_M (BUILD, L)
Sections over an open U are functions ω : U → Λ^{0,q}(E; F) (or into the total fibre
Λ^{0,•}(E)), ω(x) read in the chart `chartAt x`, satisfying the local predicate: for each x ∈ U, with φ = `chartAt x`, the chart
expression z ↦ ω(y) ∘ D(`chartAt y` ∘ φ⁻¹)(z) at z = φ(y) is smooth near φ(x).
Built with `TopCat.LocalPredicate` ✓ and `TopCat.subsheafToTypes` ✓, as Mathlib builds
`smoothSheaf` ✓; the ring structure on 𝒜^{0,•} follows `smoothSheafCommRing` ✓. Making each
𝒜^{0,q} a `SheafOfModules` over 𝒜^0 has no Mathlib precedent and is part of F9's size.
- **F9.a** The predicate is independent of the chart choices (F7). The transition factor is
  the coordinate change of `tangentBundleCore` ✓ (`tangentBundleCore_coordChange` ✓), so its
  cocycle lemmas apply.
- **F9.b** ∂̄ chartwise: (∂̄ω)(x) = (∂̄ω_φ)(φ(x)), φ = `chartAt x`; well defined by F7.a.
- **F9.c** ∧ and the module structure over smooth functions are pointwise.
- **F9.d** 𝒜^{0,0}_M(ℂ) ≅ C^∞_M(ℂ) := `smoothSheafCommRing 𝓘(ℝ, E) 𝓘(ℝ, ℂ) M ℂ` ✓.
- **F9.e** (sanity) For an open V ⊆ E with its induced structure
  (`TopologicalSpace.Opens.instChartedSpace` ✓), sections over V are just smooth functions
  V → Λ^{0,q}(E; F).

### F10 — The Dolbeault dga (BUILD, S)
𝒜_M(U) := sections over U of the total-fibre sheaf 𝒜^{0,•}_M (F9), with pointwise product (F5)
and ∂̄ (F9.b); internally graded by the components q, and 𝒜^{0,q}_M is the q-th component sheaf.
A bounded graded-commutative dga (A1) for every open U, with restrictions dga maps.
(v1.9) The component sheaves are *defined* as the subtypes 𝒜^{0,q}_M(U) := ↥(𝒜_M(U) q) of
the total section algebra, so that the 𝒜^0 of C0 is the dga's own `𝒜 0` (C0, one carrier
for A⁰).
**The Dolbeault algebra of X is A = 𝒜_X(X).** ⚠ The total fibre removes the direct-sum
construction of conventions §5: the ring axioms hold pointwise.

### F11 — Fineness and local freeness (BUILD, S)
For compact X: 𝒜^0 is fine (`SmoothPartitionOfUnity.exists_isSubordinate` ✓ for 𝓘(ℝ, E); needs
T2 and σ-compact); 𝒜^{0,q} is locally free of rank C(n, q) over 𝒜^0 (F2.c in charts);
𝒜^{0,q} = 0 for q > n. (v1.9) `IsFine` asks for the stalk-free `SupportedIn`
(∃ V, U ⊔ V = ⊤ ∧ ρ|V = 0): take V := (tsupport ρ_i)ᶜ; the real-valued ρ_i become sections
of 𝒜^0 through ℝ → ℂ.

### F12 — Holomorphic functions (BUILD, S)
O_M := `smoothSheafCommRing 𝓘(ℂ, E) 𝓘(ℂ, ℂ) M ℂ` ✓ (complex C^∞ = holomorphic).
ρ : O_M → C^∞_M(ℂ) is the inclusion (F1 and restriction of scalars); it is injective with
image ker(∂̄ : 𝒜^0 → 𝒜^1) by F8. So 0 → O → 𝒜^0 → 𝒜^1 is exact.

### F13 — Chart transport (LATER; needed only for Z4 and Z5)
For a chart φ : U ≅ φ(U) ⊆ E, an isomorphism of presheaves of dgas 𝒜_M|U ≅ φ^*𝒜_{φ(U)},
compatible with ρ and O. From F7 and F9.e. Not on the critical path, because H1 and H2 are
stated on X.

### H1 — Dolbeault–Grothendieck lemma (HYP)
`DolbeaultGrothendieck E X : Prop`: for every open U ⊆ X, q ∈ ℕ, x ∈ U and
ω ∈ Γ(U, 𝒜^{0,q+1}_X) with ∂̄ω = 0, there are an open x ∈ U′ ⊆ U and η ∈ Γ(U′, 𝒜^{0,q}_X) with
∂̄η = ω|U′. Together with F12 this says exactly that ρ : O_X → 𝒜^•_X is a resolution.
- True on every complex manifold (Dolbeault–Grothendieck lemma). Proof is Z4.
- Trivial cases to prove as lemmas: q + 1 > n; n = 0.
- ⚠ Stated on X, not on open subsets of E: this keeps chart transport (F13) off the critical
  path, and it is the standard sheaf-theoretic form of the lemma.

### H2 — Local gauge lemma, weak form (HYP)
`LocalGaugeLemma E X : Prop`: for every cohesive module M over A = 𝒜_X(X) and x ∈ X, there are an
open x ∈ U′, a bounded complex W of finitely generated projective O_X(U′)-modules, and a homotopy
equivalence in P_{𝒜_X(U′)} between M|U′ (A9) and 𝒜_X(U′) ⊗_{O_X(U′)} W (A10).
- True: the proof of [B, Lemma 4.1.5] (whose statement is full faithfulness of α) gives a gauge
  equivalence on a smaller polydisc with W free; this is its weak
  form, and [A, Assumption 6] at the level of sections. It is field LL of C0 verbatim. Proof is
  Z5.
- Trivial case to prove: n = 0.
- (v1.9, audit F9) Lean form, to be reviewed at gate 3: `LocalGaugeLemma E X` says: for every
  `M : CohesiveModule (dolbeault E X)` and x, there are an open U′ ∋ x, a complex
  `W : CochainComplex (ModuleCat.{0} (O(U′))) ℤ` with `IsBoundedFGProj`, and an isomorphism in
  `HoP` of the U′-dga between `M.baseChange (res_{U′})` (A9) and
  `CohesiveModule.fromComplex ρ_{U′} … W` (A10, with `hc : c = 0` and `d ∘ ρ_{U′} = 0`, both
  facts about the Dolbeault dga). ρ_{U′} : O(U′) →+* ↥(𝒜_{U′} 0) (C0, one carrier).

### F14 — The fields of C0 (BUILD, S)
F10, F11 and F12 give the pre-resolving data C0.a for X, unconditionally. Given H1 and H2,
F12 and H1 give the resolution field and H2 is the field LL, completing C0.b.

### F15 — Main theorem (BUILD, S)
`blockFunctor E X := J` for the C0.a data of F14 (no hypotheses). Assemble C0.b from H1, H2
(F14) and apply C6. This proves M.

## 6. LATER — deferred on purpose (do not start)

Each item names what it needs and what in this blueprint already prepares it.

### Z1 — D_perf(X) = D^b_coh(X)  (feasibility report G9)
Corollary: Ho(P_A) ≃ D^b_coh(X), Block's original form [B, Thm 4.1.3].
Needs: coherent O_X-modules (✗), Oka's coherence of O_X, Noetherian regular local rings O_{X,x},
coherent sheaves have local finite free resolutions [Griffiths–Harris, p. 696], coherent sheaves
form an abelian subcategory, truncation triangles. Then [A, Lemma 7.4.1, Cor 7.4.2].
Prepared by: S9 (perfect complexes). Design references: Tau Ceti RealAnalyticGeometry and
ComplexComparisonPartII roadmaps (Oka statements).

### Z2 — Triangulated structure  (feasibility report G10)
Shifts and cones in P_A, pretriangulated in the sense of Bondal–Kapranov, Ho(P_A) triangulated,
J a triangulated functor; idempotent completeness. [B, Prop 2.4.1], [CHL, Prop 3.1, Lemma 3.3].
Prepared by: A4 (sign conventions match Mathlib's shift and Hom complex), A14.

### Z3 — Twisted sheaves (curvature h ≠ 0)
For a ∂̄-closed h ∈ 𝒜^{0,2}(X): cohesive modules over (A, h) model h-twisted perfect complexes.
[A, §7.1–7.2, Thm 7.4.3], [B, §4.2].
Needs: twisted sheaves for a cover and cocycle [A, Def 7.1.1]; the Čech–Dolbeault zigzag
producing the cocycle from h [A, Def 7.2.2] (uses H1 in degrees 1 and 2); exponentiation on 𝒜^0;
the twisted functor [A, Def 7.2.3]; enough injectives for twisted modules [A, Lemma 7.1.6];
K-flat resolutions for twisted sheaves (open: not in [A]; plausible with twisted
extension-by-zero generators).
Prepared by: curvature carried in A3–A4; F-valued forms (F2–F10); S-lemmas stated for
arbitrary opens and ringed spaces, so they apply on each cover member where the twist is
trivial.
Beyond Z3: topologically nontrivial gerbes need End(E)-valued forms and a noncommutative A^0
[Block–Daenzer]; Mathlib's `TensorProduct` needs a commutative base, so this is out of reach of
the present encoding.

### Z4 — Prove H1 (Dolbeault–Grothendieck)
One-variable inhomogeneous ∂̄ via the Cauchy transform with smooth parameters
(Cauchy–Pompeiu), then induction on variables on polydiscs with shrinking (Hörmander;
Griffiths–Harris, p. 25). Prepared by: F3, F4 on open subsets of E. Needs F13 to move between
polydiscs in E and X. **Started (v1.14, approved 1 Nov 2026): phase 6, items Z4.a–Z4.h in §11;
F13 is not needed.** No longer LATER.

### Z5 — Prove H2 (local gauge lemma)
Block's proof of [B, Lemma 4.1.5] following Donaldson–Kronheimer §2.2.2: solve the nonlinear
equation φ⁻¹∂̄₁φ = J′ in one variable with parameters, iterate over the variables, conclude a
gauge equivalence with a holomorphic complex on a polydisc, then trivialize the projective
modules on a ball. Needs F13. Contains Koszul–Malgrange integrability as the one-term case. Needs Z4-type
estimates and a fixed-point argument. (v1.15 DRAFT, §11: detailed, audited plan in
`blueprint/blueprint-ll.md`; the equation is linear, ∂̄_k g = g·a; F13 not needed; proposed as
phase 7.)

### Z6 — Dg-level quasi-equivalence
Upgrade the equivalence of homotopy categories to a quasi-equivalence of dg-categories
[CHL, Cor 7.7, Rem 7.4]. Needs DG-category infrastructure (Tau Ceti DGAInfinity roadmap as a
design reference) and either flatness of 𝒜 over O (Malgrange) or a K-flat substitute.

### Z7 — Open manifolds
Replace D_perf by globally bounded perfect complexes D^B_perf and compactness by finite
covering dimension [A, Lemma 7.2.12]; partitions of unity for arbitrary covers.

### Z8 — Bridge to intrinsic forms
Identify 𝒜^{0,q}_X with smooth sections of Λ^{0,q}T*X ⊂ Λ^q T*X ⊗ ℂ and ∂̄ with the (0, q+1)-part
of d, once manifold differential forms exist (Mathlib's `extDeriv` currently lives on normed
spaces only). F3.c is the pointwise seed of this.

### K7 — Our ∂̄ against TauCeti's `delBar` (LATER; human, 1 Nov 2026)
Sanity check of the normalization of F3. TauCeti (not a dependency) defines
`delBar φ = Σ_{p+q=k} π^{p,q+1}(d(π^{p,q}φ))`, type (p,q) as the eigenvalue (p−q)i of the
J-derivation, `typeProjection` as a polynomial in it (`typePolynomial`). Transcribe these
definitions pointwise on the model space E with J = i· and `extDeriv` for `mextDeriv` (TauCeti's
`inChartAt_mextDeriv_eq`), then prove: (i) `DolbeaultFibre.toReal` maps onto the forms of type
(0,q); (ii) for a (0,q)-form all terms but π^{0,q+1}(dφ) vanish; (iii) with F3.c
`dbar_eq_extDeriv`, the transcribed `delBar` of `toReal ∘ α` is `toReal (dbar α)`; (iv) an
explicit example as in K2/K3. Est. 200–400 lines, in a checks file outside the statement. The
transcription's faithfulness needs human review. Sources (fetch from TauCeti `main` with `curl`
from raw.githubusercontent.com, not with web-fetch, which mangles brackets):
`TauCeti/Analysis/Normed/Module/Alternating/Uncurry/AlmostComplexType.lean`,
`TauCeti/Geometry/Manifold/DifferentialForm/{AlmostComplexType, Dolbeault/Basic}.lean`.
Repository: `TauCetiProject/TauCeti`. The pointwise definitions are in
`TauCeti/Topology/Algebra/Module/Alternating/AlmostComplexType.lean`.

**K7′ detail (6 Nov 2026; approved at gate 13, §11 v1.21; K7 promoted from LATER by the human 6 Nov 2026).**
File `Cohesivemodules/ChecksK7.lean`, outside the statement. Real forms `ω : E [⋀^Fin k]→L[ℝ] F`
(`F` a complex normed space), `J := I • · : E →L[ℝ] E`.
- (a) **Transcription** (verbatim up to names; review item):
  - `tcDeriv J ω v = Σ_i ω (update v i (J (v i)))` (TauCeti `alternatingDerivation`);
  - `tcIsOfType ω p q := p + q = k ∧ tcDeriv J ω = ((p − q) i) • ω`;
  - `tcEig (p, q) := (p − q) i`, `tcTypePolynomial k p q := Lagrange.basis (antidiagonal k) tcEig (p, q)`,
    `tcTypeProjection p q := aeval (tcDeriv J) (tcTypePolynomial k p q)`;
  - `tcDelBar φ x := Σ_{(p,q) ∈ antidiagonal k} π^{p,q+1}(extDeriv (π^{p,q} ∘ φ) x)` for
    `φ : E → E [⋀^Fin k]→L[ℝ] F` (TauCeti `delBar`, with `extDeriv` for `mextDerivₗ` on the model
    space, and the type projections applied pointwise).
- (b) **Eigenvector lemma.** If `tcIsOfType ω p q`, then `aeval (tcDeriv J) g ω = g(tcEig(p,q)) • ω`.
  Hence `π^{p',q'} ω = ω` if `(p', q') = (p, q)`, and `0` otherwise, for `p' + q' = k`
  (Lagrange basis values). No polynomial identity needed.
- (c) **(i)** `toReal α` is of type `(0,q)`: `toReal α (update v i (I v_i)) = −I · toReal α v`
  (antilinear slots), so `tcDeriv` acts by `−q i`.
- (d) **(ii)** For `φ` with each `φ y` of type `(0,q)`, `π^{p,q}(φ y)` is `φ y` for `(p,q) = (0,q)`
  and `0` otherwise (b), so `tcDelBar φ x = π^{0,q+1}(extDeriv φ x)`.
- (e) **Slot decomposition.** For any `ω` of degree `n`, set `ω_T(v) := 2^{-n} Σ_{S} c_{T,S} ω(J_S v)`
  with the slotwise projections `P^± f(v) = ½ (f(v) ∓ i f(J v))` (`P^+` on the slots in `T`,
  `P^-` elsewhere). Then `ω = Σ_T ω_T`, the groups `ω^{p} := Σ_{|T| = p} ω_T` are alternating, and
  each is of type `(p, n − p)` (eigenvalue `(p − (n − p)) i`). By (b),
  `π^{0,n} ω = ω^{0} = 2^{-n} Σ_S i^{|S|} ω(J_S v)`.
- (f) **(iii)** With (d), (e) for `n = q + 1` and F3.c `dbar_eq_extDeriv`:
  `tcDelBar (toReal ∘ α) x = toReal (dbar α x)` for `α` differentiable at `x`.
- (g) **(iv)** Example: `E = ℂ`, `q = 0`, `α = z̄` (a function), both sides equal the `(0,1)`-form
  `v ↦ v̄` up to `toReal` (as K2/K3).
Estimate: 300–500 lines. Only (e) is substantial linear algebra; (a) needs human review.

## 7. File layout

```
Cohesivemodules/
  Algebra/   Dga.lean (A1, FROZEN)  Connection.lean (A2)  CohesiveDef.lean (A3–A5 defs, FROZEN)
             GeneratorsDef.lean (generator data, FROZEN)  Cohesive.lean (A3.a, A4.c)
             Filtration.lean (A6–A8)  BaseChangeDef.lean (A9 defs, FROZEN)
             FromComplexDef.lean (A10 defs, FROZEN)  BaseChange.lean (A9–A10 theorems)
             DegreeZero.lean (A10 in degree 0, for K1)
             Lifting.lean, LiftingCone.lean (A11)  TotalQuasiIso.lean (A12)
             BlockDef.lean, BlockBridge.lean (A13)
             GenHomDef.lean (A4.c defs), BaseChangeHomDef.lean, BaseChangeResDef.lean (A9 defs)
             (FROZEN at gate 4)  BaseChangeResAPI.lean (A9 API)  BaseChangeExt.lean (C3)
             BaseChangeLift.lean, TotMap.lean (C7)  HomAlongT.lean, QuasiIsoElem.lean (C4)
  Sheaf/     Basic.lean (vocabulary, FROZEN)  Fine.lean (S1–S2)  Acyclic.lean (S3)
             Soft.lean (S3.b)  Projective.lean (S4.a–c)  TensorSections.lean (S4.d)
             Restriction.lean (S5–S6)  Hom/Basic.lean, Hom.lean (S7)
             HomAcyclic.lean + HomAcyclic/ (S7.b–c)  Flat.lean + Flat/ (S8.a–f)
             Resolution.lean, FlatResolution.lean (S8.d–e)  BaseChange.lean (S8.a, S8.g)
             PerfectDef.lean (S9.a–c defs, FROZEN)  Perfect.lean (S9.c–d)
             Globalize.lean + Globalize/ (S10)  Derived.lean (S11)
             FineDef.lean (S1 defs), RingOfDef.lean (S8 `ringOf`) (FROZEN at gate 4)
             HomAction.lean (S7.a′)  HomOver.lean, HomOverSections.lean, HomSectionsMap.lean,
             RestrEval.lean (S7.b′–c′, C4)
  Forms/     Realify.lean (F1)  FibreDef.lean, Fibre.lean (F2)  DbarDef.lean, Dbar.lean (F3–F4)
             ProductDef.lean, Product.lean (F5)  Leibniz.lean (F6)
             PullbackDef.lean, Pullback.lean (F7)  CauchyRiemann.lean (F8)
             SheafPred.lean (F9 defs)  ChartAux.lean (chart helpers)  Sheaf.lean (F9–F10 theorems)
             SheafDef.lean (F10 defs)  Holomorphic.lean (F12 defs)
             Dolbeault.lean (F10–F12 theorems)  Transport.lean (F13, LATER)
             (FROZEN at gate 3: every *Def.lean here, SheafPred, Holomorphic)
  Comparison/ SetupDef.lean (C0 defs)  Setup.lean, SetupAux.lean (C0 API)
             AlphaDef.lean (C1 α)  FunctorDef.lean (C1 J)  AlphaSheaf(Aux).lean (C1.a)
             AlphaOver(Aux).lean (C1.c)
             Perfect.lean, PerfectAux.lean, PerfectLoc.lean, PerfectModel.lean (C2)
             HomSheaf.lean, HomSheafAux.lean, HomSheafRetract.lean (C3)
             FullyFaithful.lean, FullyFaithful{Aux, Top, Phi, Square, Global, Local}.lean (C4)
             EssSurj.lean, EssSurj{Aux, Core, Model}.lean (C5)  Equivalence.lean (C6)
             ModelDual.lean, ModelTSheaf.lean, ModelDef.lean (C7.a, c, e)
             ModelConnNab.lean, ModelConn.lean (C7.b)  ModelBC.lean (C7.b, d: ιT)
             ModelTensor{Pair, Kappa, Coord, Iso}.lean, ModelTensor.lean (C7.d)
             ModelFilG0.lean, ModelFil.lean, ModelCrit{Site, Coord, Fil}.lean, ModelCrit.lean
             (C7.f)
             (FROZEN at gate 4: SetupDef, AlphaDef, FunctorDef)
  Hypotheses.lean   H1, H2 statements and their trivial cases (FROZEN)
  BlockFunctorDef.lean  F14 (C0.a: dolbeaultPresheaf, dolbeaultPreData), F15 blockFunctor
                    (FROZEN at gate 5)
  StatementsConditional.lean  def MainStatementConditional : Prop (FROZEN at gate 5; named
                    MainStatement in Statements.lean until v1.22)
  Statements.lean   def MainStatement : Prop, without H1, H2 (FROZEN at gate 7; named
                    MainStatementUnconditional in StatementsUnconditional.lean until v1.22)
  Main.lean         F14 (C0.b: dolbeaultData), theorem blockPerf, theorem main_theorem_conditional
  MainH2.lean       theorem main_theorem : MainStatement
  Checks.lean       §9 checks; ChecksMain.lean: K1 corollary, K6, #print axioms blockPerf,
                    main_theorem_conditional and main_theorem
  ChecksSheaf.lean  non-vacuity of the layer-S definitions
  ChecksForms.lean  K1, K5 and non-vacuity of the layer-F definitions
  ChecksAlgebra.lean, ChecksComparison.lean  layer-A checks; C0 non-vacuity
Scratch/            experiments, never imported
```
Files over ~500 lines are split for size into pieces next to the original name (e.g.
`Algebra/BaseChange{Functor, Comp}.lean` before `BaseChange.lean`, `Sheaf/SoftBasic.lean` before
`Soft.lean`); the pieces belong to the item of the file listed here.

## 8. Order of work

Each phase ends with a human review gate before the next phase starts: every new definition and
statement is listed on a generated review sheet, and the human checks them in excerpts. Definitions used in `MainStatement` are frozen in stages, because they are built
in different layers.

| Phase | Items | Gate (human review) |
| --- | --- | --- |
| 0 Setup | Pin Mathlib; re-check every ✓ in §10; prototypes P1–P3 (conventions §11); draft `PROGRESS.md` | Conventions §4–§7 decisions from P1–P3 |
| 1a Algebra | A1–A12, then A13 | Freeze A3–A5 (cohesive modules, Ho) |
| 1b Local analysis (parallel with 1a) | F1–F8 | Normalization checks K2, K3 pass |
| 2 Sheaf toolkit | S1–S11 | Freeze S9.c (D_perf) |
| 3 Dolbeault sheaf | F9–F12, then H1, H2 stated | Freeze F10, F12, H1, H2 |
| 4 Comparison | C0–C6 | Freeze C1 (J) |
| 5 Assembly | F14–F15; write and freeze `Statements.lean`; §9 checks; then A8 | `#print axioms` shows only the standard three |

Inside each phase, follow the item order; items marked BUILD-S are good single tasks for one
session.

## 9. Sanity checks, non-vacuity, deviations

### Checks (all go in `Checks.lean`)
- **K1 Dimension zero.** For E = (Fin 0 → ℂ) and every X prove H1 X and H2 X outright (Λ^{0,q} = 0 for q ≥ 1;
  𝒜 = 𝒜^0 = C^∞ = O, so W is the cohesive module's own complex). Get the unconditional
  corollary for finite discrete X. This shows the hypothesis bundle is satisfiable.
  Lean: the `ChartedSpace (Fin 0 → ℂ) X` instance for a discrete X may have to be built.
- **K2 Normalization on E = ℂ.** ∂̄(z ↦ z̄) = dz̄ with dz̄ = (v ↦ v̄); ∂̄(z ↦ z) = 0;
  ∂̄(z ↦ |z|²) = z·dz̄.
- **K3 ∂̄∂̄ = 0 and Leibniz** on explicit polynomial forms on ℂ², including the sign on
  dz̄₁ ∧ dz̄₂.
- **K4 Dolbeault cohomology.** For M = 𝒜 (Q = 𝒜^0 in degree 0, 𝔼 = ∂̄), Hom^k(M, M) ≅ 𝒜^{0,k}(X)
  with δ = ∂̄, so Hom_{Ho}(M, M[k]) = H^{0,k}_∂̄(X).
- **K5 Trivial cases of the hypotheses.** H1 for q + 1 > n.
- **K6 Statement review.** The docstring of `blockPerf` matches §1; every hypothesis is listed;
  `#print axioms blockPerf` and `#print axioms main_theorem_conditional` (v1.22 name) show only `propext`,
  `Classical.choice`, `Quot.sound`. Corollary: the corestriction of `blockFunctor E X` to D_perf
  is an equivalence. (v1.9, audit F12) Also the converse: if the corestriction is an
  equivalence, then J is full, faithful, with essential image `Perf` (both `essImage` and
  `Perf` are closed under isomorphism), so the shape of M is equivalent to the source form.

### Non-vacuity of definitions
For every new structure (cohesive module, resolving data, fine sheaf, strictly perfect complex,
LocalPredicate sheaf), give an example: the zero module and 𝒜 itself; the data of F14 for a
single point; the constant sheaf on a point.

### Deviations from the sources (⚠ in the text)
1. Left modules instead of Block's right modules; curvature c ↔ −c (conventions §3).
2. Finite covers and compactness replace softness and finite covering dimension (S1, S10).
3. Exactness of Γ on modules over a fine sheaf (S3) and softness (S3.b) replace
   sheaf-cohomological acyclicity ([A, Lemma 7.2.8]); S10's step (2) uses a global Ext
   argument instead of [A, Lemma 7.2.10] on small opens (v1.7), then by local lifting and
   splitting (S10.a–c) with S4.b (v1.8).
4. K-flat resolutions replace the first half of [A]'s Assumption 5 (𝒜 K-flat over R), i.e.
   Malgrange's theorem (C5).
5. Local lifting is stated sectionwise and only for restrictions of global cohesive modules
   (C0, H2); H1 and H2 are stated on X, not on open subsets of E.
6. (0,q)-forms are ℂ-alternating maps on the conjugate space Ē; the product is transported
   from the exterior algebra of the antilinear dual (F2, F5; conventions §6).
7. Errata in [A]: "Assumption 7" means item 6; item 6's target is A^∗ ⊗_R W, not R ⊗_k V;
   Prop 7.2.18 forms A^0 ⊗_R M underived (fixed by 4).
8. [B, proof of Lemma 3.2.8] has typos ((j ⊗ 1)θ̃ − θ; θ for μ); A11 follows [A, Prop 3.3.4].

## 10. Mathlib status (pinned `v4.35.0`, re-checked 21 Oct 2026)

### Found (✓) — re-checked against `v4.35.0`
Full names where the table abbreviates: the `alternatizeUncurryFin…` lemmas are in
`ContinuousAlternatingMap`; `CochainComplex.Plus.exists_quasiIso_injective` (input
`CochainComplex.Plus C`, output in `InjectiveObject C`); `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective`
(on `HomotopyCategory.Plus`); `IsGrothendieckAbelian.enoughInjectives`; `SheafOfModules.instAbelian`
and the presheaf monoidal structure are unnamed instances; `tangentBundleCore_coordChange` is
generated by `@[simps]`. Hypotheses to remember: `isKInjective_of_injective` /
`isKProjective_of_projective` need `IsStrictlyGE` / `IsStrictlyLE`; `truncGE`/`truncLE` need
`HasHomology` in every degree; `SheafOfModules.pullback` needs `(pushforward φ).IsRightAdjoint`;
`ContinuousAlternatingMap.instNormedSpace` needs `SMulCommClass 𝕜 𝕜' F`; `pairingDual_ιMulti_ιMulti`
gives `det (of fun i j ↦ f j (v i))`, the transpose of det(φ_i(v_j)) (same value).

| Use | Declaration | File |
| --- | --- | --- |
| d on forms, d² = 0 | `extDeriv`, `extDeriv_extDeriv`, `extDerivWithin_extDerivWithin_apply` | `Analysis/Calculus/DifferentialForm/Basic.lean` |
| Pullback | `extDeriv_pullback`, `extDerivWithin_pullback` | same |
| Alternation | `ContinuousAlternatingMap.alternatizeUncurryFin`, `alternatizeUncurryFinCLM`, `alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric`, `alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero` | `Analysis/Normed/Module/Alternating/Uncurry/Fin.lean` |
| Normed fibres | `ContinuousAlternatingMap.instNormedSpace` (extra scalars 𝕜′) | `Analysis/Normed/Module/Alternating/Basic.lean` |
| Exterior algebra bridge | `exteriorPower.pairingDual`, `pairingDual_ιMulti_ιMulti`, `exteriorPower.alternatingMapLinearEquiv`, `ιMultiDual_apply_diag`, `ιMultiDual_apply_nondiag`, `Module.Basis.exteriorPower` | `LinearAlgebra/ExteriorPower/{Pairing,Basis,Basic}.lean` |
| Exterior algebra | `ExteriorAlgebra.gradedAlgebra`, `ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm`, `ExteriorAlgebra.liftAlternating`, `ExteriorAlgebra.map` | `LinearAlgebra/ExteriorAlgebra/*` |
| Laplace expansion | `Matrix.det_succ_row_zero` | `LinearAlgebra/Matrix/Determinant/Basic.lean` |
| Tangent coordinate changes | `tangentBundleCore`, `tangentBundleCore_coordChange` | `Geometry/Manifold/VectorBundle/Tangent.lean` |
| Pullback of sheaves of modules | `SheafOfModules.pullback`, `pullbackPushforwardAdjunction` | `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` |
| Wedge (algebraic, not used) | `AlternatingMap.domCoprod` | `LinearAlgebra/Alternating/DomCoprod.lean` |
| Restriction of scalars | `ContDiff.restrict_scalars`, `ContDiffOn.restrict_scalars`, `ContDiffAt.restrict_scalars`, `differentiableAt_iff_restrictScalars` | `Analysis/Calculus/ContDiff/Operations.lean`, `Analysis/Calculus/FDeriv/RestrictScalars.lean` |
| Smooth sheaves | `smoothSheaf`, `smoothSheafCommRing` | `Geometry/Manifold/Sheaf/Smooth.lean` |
| Local predicates | `TopCat.LocalPredicate`, `TopCat.subsheafToTypes` | `Topology/Sheaves/LocalPredicate.lean` |
| Partitions of unity | `SmoothPartitionOfUnity`, `SmoothPartitionOfUnity.exists_isSubordinate` | `Geometry/Manifold/PartitionOfUnity.lean` |
| Open submanifolds | `TopologicalSpace.Opens.instChartedSpace`, `IsManifold I n s` instance | `Geometry/Manifold/HasGroupoid.lean`, `IsManifold/Basic.lean` |
| Compact complex manifolds | `MDifferentiable.exists_eq_const_of_compactSpace` | `Geometry/Manifold/Complex.lean` |
| Sheaves of modules | `SheafOfModules.instAbelian`, `IsGrothendieckAbelian` instance, `SheafOfModules.free`, `SheafOfModules.IsLocallyFree`, `SheafOfModules.pushforward`, `overFunctor` | `Algebra/Category/ModuleCat/Sheaf/*`, `CategoryTheory/Abelian/GrothendieckAxioms/SheafOfModules.lean` |
| Enough injectives | `enoughInjectives` for Grothendieck abelian | `CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean` |
| Presheaf tensor | monoidal structure on `PresheafOfModules` | `Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` |
| Type-valued Hom sheaf | `presheafHom` | `CategoryTheory/Sites/SheafHom.lean` |
| Derived categories | `DerivedCategory`, `HasDerivedCategory.standard`, `Functor.mapDerivedCategory` | `Algebra/Homology/DerivedCategory/*` |
| K-injective, K-projective | `CochainComplex.IsKInjective`, `isKInjective_of_injective`, `Qh_map_bijective_of_isKInjective`, `IsKProjective`, `isKProjective_of_projective` | `Algebra/Homology/HomotopyCategory/K*.lean`, `DerivedCategory/Plus.lean` |
| Injective resolutions | `exists_quasiIso_injective` | `Algebra/Homology/DerivedCategory/DerivabilityStructureInjectives.lean` |
| Hom complexes, shifts | `CochainComplex.HomComplex.δ`, shift with `n.negOnePow • d` | `Algebra/Homology/HomotopyCategory/HomComplex.lean`, `Shift.lean` |
| Truncations | `CochainComplex.truncGE` (and `truncLE`) | `Algebra/Homology/Embedding/CochainComplex.lean` |

### Absent (✗) — to be built here
Conjugate-space type synonym; `pairingDual` packaged as an equivalence; manifold differential
forms; realification lemma; the instance `ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ` (so
`smoothSheafCommRing 𝓘(ℝ, E) 𝓘(ℝ, ℂ) M ℂ` does not elaborate without it, F1);
graded-commutativity class; continuity of algebraic multilinear or alternating maps in finite
dimension as a ready-made declaration (only `MultilinearMap.continuous_of_bound` /
`mkContinuous`, which need a bound; F2.b); curved dgas, cohesive modules, dg-categories; fine or soft sheaves;
monoidal structure and internal Hom on `SheafOfModules`; extension by zero; flat sheaves and
K-flat complexes; perfect complexes of sheaves; coherent analytic sheaves; several-variable
Cauchy, Osgood or Hartogs theory.

### Not checked (?)
The module version of "epi ⇔ locally surjective" for `SheafOfModules`; whether
`SheafOfModules.pullback` along the inclusion of an open is extension by zero.

## 11. Version history

**v1.0 (21 Oct 2026), final.** Hypotheses on X confirmed. Changes from the first draft, after
expert review:

1. **Smoothness exponent (bug fix).** `⊤` in Mathlib's `ℕ∞ω` means analytic. Every C^∞
   statement now uses `∞`; complex manifolds are `IsManifold 𝓘(ℂ, E) ∞ X`.
2. **Hypotheses on X.** H1 and H2 are stated on X; H2 only for restrictions of global cohesive
   modules, which is all C2 and C4 use and is Block's own Lemma 4.1.5. Chart transport (F13)
   moves to LATER; F14–F15 become one-line assemblies.
3. **Fibre and product.** Forms are ℂ-alternating maps on the conjugate space Ē; the product on
   the total fibre is transported from `ExteriorAlgebra ℂ (Dual Ē)` via Mathlib's
   `exteriorPower.pairingDual`. Associativity and graded commutativity become free, and the
   Leibniz rule reduces to the Laplace formula F5.a. F6 drops from M to S; F10 from M to S.
4. **A8 off the critical path.** The homotopy criterion is not used by the main theorem.
5. **A11 simplified** to the hypotheses actually available (quasi-isomorphism plus flatness).
6. **Perfect complexes via roofs** (S9.b): no derived category of R|U is needed.
7. **C5.0 interface** isolates the one place flatness enters, so C5 can be written before S8.
8. **Possible shortcut for j_!**: `SheafOfModules.pullback` may already provide it (S5.b).

**v1.0.1 (21 Oct 2026), layout only (approved by the human in phase 0).** No mathematical
change.
1. The files of §7 live under `Cohesivemodules/` (the existing lean_lib; `lakefile.toml` is not
   edited). The Lean namespace stays `Cohesive`.
2. `Comparison/Main.lean` (C6) is renamed `Comparison/Equivalence.lean`, so there is only one
   `Main.lean`.
3. `blueprint.md` and `conventions.md` moved into `blueprint/`, as referenced throughout.

**v1.1 (21 Oct 2026), approved by the human after the phase-0 review.**
1. **Main statement shape.** `blockFunctor E X` goes into the whole derived category and is
   defined from the hypothesis-free pre-resolving data C0.a. M states full, faithful, essential
   image = `Perf X` (§1). Reason: a functor into D_perf needs C2, hence H2.
2. **Shift rule** (conventions §2) corrected to 𝕏[1]^j = (−1)^{j+1} 𝕏^j on generators; the
   naive 𝕏[1] = −𝕏 breaks Leibniz for A ≠ A^0.
3. **Universes.** Graded pieces of cohesive modules are `Q p : Type`; sheaves of modules are
   written `SheafOfModules.{0}` (conventions §7).
4. **Mathlib re-pinned** to the stable release `v4.35.0` (Lean `v4.35.0`); §10 re-checked
   against it.
5. Small fixes: phase-0 gate covers conventions §4–§7; `#print axioms` for both `blockPerf` and
   `main_theorem`; F9 size note; S9.b over-site note; K1 chart-instance note; second P1 toy.

**v1.2 (21 Oct 2026), approved by the human (P1 decision, part 1).**
1. **Grading by ℤ.** The algebra is ℤ-graded with A^q = 0 for q < 0 (§2 setting, A1,
   conventions §1, §5); signs are `Int.negOnePow`.
2. **A^0 structures** (commutative ring, A^0-algebra structure on A) are built from graded
   commutativity (conventions §5).
3. **Encoding of cohesive modules: encoding 1** (conventions §4). The total module
   A ⊗_{A^0} (⨁ Q^p) is built from the generators; Hom^n is the k-submodule of degree-n maps
   with φ(a·x) = (−1)^{n|a|} a·φ(x) (A4 verbatim); the generator form is the theorem A4.c.

**v1.3 (21 Oct 2026), citation audit against the sources, approved by the human.**
1. H2 and C0: the gauge equivalence is in the *proof* of [B, Lemma 4.1.5]; the lemma itself
   states full faithfulness of α ([A] makes the same slip when it cites [Blo09, Lemma 4.1.5]).
2. C6: [CHL, Thm 7.10] (there is no Thm 7.9); full faithfulness is [CHL, Prop 7.4].
3. S4.c: the cited facts are in the remark after [A, Def 7.2.5] and the proof of
   [A, Lemma 7.2.7], not in the statement of Lemma 7.2.7.
4. [A] has no "Assumption 5a": it is the first half of Assumption 5.
5. Sources: [B] uses arXiv v2 numbering (the published version differs); [CHL] uses arXiv v3
   numbering. All other [A], [B], [CHL] citations were checked and match.

**v1.4 (21 Oct 2026), P2 decisions, approved by the human.**
1. Forms: keep `Conj E` (conventions §6); the subtype fallback is dropped.
2. §10: continuity of algebraic alternating maps in finite dimension is ✗ (F2.b needs a bound).

**v1.5 (22 Oct 2026), P3 decision, approved by the human; phase 0 closed.**
1. Restriction of sheaves of modules: `overFunctor.{0}` on the over-site (conventions §7, S5.a).
2. Abbreviation rule for Mathlib constants with an undetermined module universe (conventions §7).

**v1.6 (22 Oct 2026), approved by the human.** A9: base change is defined on generators,
B^0 ⊗_{A^0} Q^p, exactly as [B, §2.7] (E^• ⊗_{𝒜_1} 𝒜_2) at ω = 0; "B ⊗_A M" is its total module
up to canonical isomorphism.

**v1.7 (23 Oct 2026), approved by the human (phase 2).**
1. S3.b (new, soft sheaves): C4 step 4 applies Γ to cone(Ψ), whose differentials are not
   𝒜^0-linear (δ(fφ) = df·φ + f·δφ), so S3 does not apply; S3.b(iv) does. C3 and C4 step 2
   corrected accordingly; S7.a is not used. Deviation 3 amended.
2. S10 proof route: step (2) proves the bottom term projective by a global Ext¹ argument (S3
   degreewise, S7.b, S7.c, S5.c, S6, S4.a, S11) instead of [A, Lemma 7.2.10] on small opens,
   which needs projectivity of free S|U-modules not provided by S1. Statement unchanged.

**v1.8 (23 Oct 2026), approved by the human (phase 2).** S10 step (2) by local splitting instead
of the global Ext¹ route of v1.7: locally the model lifts to a quasi-isomorphism P_U → P|U
(S10.b), whose cone splits locally (S10.c), so B is locally a summand of a finite free module
and S4.b applies. Sub-lemmas S10.a–e made explicit (S10.a, S10.b are needed by step (1) on
either route). S10 no longer uses S7.b, S7.c or derived Homs; statement unchanged.

**v1.9 (24 Oct 2026), approved by the human with gate 2 (external audit, `audit/out/report.md`).**
No change to any frozen file, to the statement M, or to the fixed decisions of §0.
1. **One carrier for A⁰** (audit F1; C0, F10, conventions §5, §7): the sheaves 𝒜^q are derived
   from the presheaf of dgas, 𝒜^0(U) = `CommRingCat.of ↥(𝒜_U 0)`, 𝒜^{0,q}(U) = ↥(𝒜_U q).
   Prototype P7 (`Scratch/P7_Carrier.lean`) checks that modules, complexes, finiteness and
   projectivity over Γ(𝒜^0) are those over `𝒜 0` with no cast.
2. **C5.a–c** (audit F2): quasi-cohesive structure on Γ(𝒜 ⊗_R K′) from the sheaf operator via
   S4.d (not A10); the sheaf map α(M) → 𝒜 ⊗_R K′ on generators (not A9); A7 in sheaves (already
   proved for any abelian category).
3. **S7.a′ and C3.a** (audit F3): termwise source action on 𝓗om and on ℋ(M₁, M₂), the input of
   S3.b(i) in C4 step 2; the old S7.a is replaced (false as stated for non-linear differentials).
4. **S8.g / C5 step 2** (audit F4): truncate the roof's middle term before resolving.
5. **C2** (audit F5 and own check): the roof written out; W̃ built over the non-fine O|U′ from the
   fineness-free part of S4.c.
6. **Spelling** (audit F6, F9, F12): `Perf (holSheaf E X)`, `DolbeaultGrothendieck E X`,
   `LocalGaugeLemma E X`; one `HasDerivedCategory` instance; H2 in Lean terms; K6 both directions.
7. **S4.d** proved in the stronger presheaf form (it had been left open in phase 2).
8. Small: F11 support line (audit F10); §7 file layout refreshed (audit F7, layout only).

**v1.10 (26 Oct 2026), approved by the human with gate 3 (phase-4 prep audit,
`review/phase4-prep.md`, and prototype P8, `Scratch/P8_Functor.lean`).** No change to any frozen
file or to the fixed decisions of §0; the statement M changes only in spelling.
1. **C5.a sign fix.** The operator d ⊗_R 1 + 1 ⊗ d_{K′} is not a connection; the correct
   operator carries the Koszul sign, db ⊗ k + (−1)^{|b|} b ⊗ dk, i.e. `tensorC R 𝒜^• K′` with
   𝒜^• first (conventions §2). C5 step 6 uses the same order. A10 clarified (its code already
   has the sign; no change).
2. **C5.b: no sign** (e has degree 0); the open "to be fixed" note is closed.
3. **C0.a: field c = 0** (flat curvature), needed for α(M) to be a complex and for A10 in LL.
   True for the Dolbeault dga; not an analytic hypothesis.
4. **Spelling of M** (§1, conventions §9): `Perf (ringOf (holSheaf E X))` and
   `Mod (ringOf (holSheaf E X))`; `Perf`/`Mod` take a `RingSheaf`, `holSheaf` is a
   `CommRingCat` sheaf. (v1.9 item 6 wrote `Perf (holSheaf E X)`.)
5. **§7 file layout** refreshed after the gate-3 definitions/theorems split (layout only), with
   the planned `Comparison/` files.

**v1.11 (26 Oct 2026), approved by the human (phase 4, provers' BLOCKED reports), including
the compactness hypotheses on C2's Lean statements.** Item C7 added to §4; pointers in C2, C4
step 3, C5.
No change to any frozen file, to the statement M, or to §0. Three gaps found while proving C2,
C4 and C5; all three need the same missing object, so one new item C7 is proposed.
- **Gaps.** (i) C2: "α(M)|U′ ≃ 𝒜|U′ ⊗_R W̃" and "W̃ → 𝒜 ⊗_R W̃ is a quasi-isomorphism" are
  asserted, but α_{U′}(𝒜(U′) ⊗ W) (sections 𝒜(V) ⊗_{𝒜(U′)} Tot, A9) is never identified with
  the sheaf tensor product 𝒜 ⊗_R W̃ (a sheafification). (ii) C5.a cites "base-change
  associativity, S8.a", which S8.a does not contain and which is not in Lean. (iii) C5.b needs
  an 𝒜(V)-action on sections of the sheafified 𝒜 ⊗_R K′, which does not exist. C4 step 3 uses
  (i) (the map u) and in addition a version of ℋ on over-sites.
- **C7 (new, BUILD, L): the explicit model T(K).** On the over-site of any open U, for a complex
  K of R|U-modules put F := 𝒜⁰ ⊗_R K (S8 `sheafBC` along ρ, a complex of 𝒜⁰-modules) and
  T(K)^n(V) := degree-n part of 𝒜(V) ⊗_{𝒜⁰(V)} ⊕_p F^p(V), i.e. ⊕_q 𝒜^q(V) ⊗_{𝒜⁰(V)} F^{n−q}(V),
  with *plain* tensor products of sections (Tot of A3 over 𝒜(V)).
  - C7.a T(K)^n is a sheaf: each 𝒜^q|U is a summand of a finite free 𝒜⁰|U-module (S4.b
    restricted; needs X compact), so T(K)^n(V) is sectionwise a retract of F(V)^m.
  - C7.b Connection: ∇ : F^p → 𝒜¹ ⊗_{𝒜⁰} F^p, α ⊗ k ↦ dα ⊗ k on the presheaf tensor
    (well defined since d∘ρ = 0), extended through sheafification (target is a sheaf by C7.a).
    Leibniz ∇(αf) = dα ⊗ f + α∇f and ∇² = 0 hold where f comes from the presheaf, hence
    everywhere (local surjectivity of the unit, separatedness).
  - C7.c Differential 𝕏_V(a ⊗ f) = da ⊗ f + (−1)^{|a|}(a·∇f + a ⊗ d_F f) (the v1.10 Koszul
    sign); Leibniz is built in, 𝕏² = 0 by C7.b and c = 0; compatible with restriction. So
    (F^•(U), 𝕏_U) is a quasi-cohesive module N_K over 𝒜(U) (A3; generators not finitely
    generated), and T(K) is a complex of sheaves of R|U-modules.
  - C7.d T(K) ≅ tensorC(𝒜^•|U, K) termwise, compatibly with differentials: the presheaf map
    a ⊗ k ↦ a ⊗ η(1 ⊗ k) is locally bijective (a retract of a power of the unit η of
    sheafification). With C5 step 6 (on any site): K → T(K) is a quasi-isomorphism for K
    bounded above with flat terms. This replaces the missing associativity (gap ii).
  - C7.e Comparison map. For M cohesive over 𝒜(U) and a closed degree-0 e : Tot(M) → Tot(N_K),
    Ξ_e : α_U(M) → T(K) is on V the A9 extension of res_V ∘ e (`extAlong`, already proved for
    C4); a chain map. (Gap iii: the action is the plain one on 𝒜(V) ⊗ F(V).)
  - C7.f Quasi-isomorphism criterion. Filter both sides by form degree (A6 `filTot`,
    sectionwise; subsheaves by C7.a), short exact sequences sectionwise (A12 `filSC_shortExact`),
    A7 in sheaves. gr^b Ξ_e is a retract of (gr^0 Ξ_e)^m (the splitting of 𝒜^b over 𝒜⁰), so
    Ξ_e is a quasi-isomorphism if gr^0 Ξ_e : (𝒜⁰ ⊗ Q^•, 𝔼⁰)~ → F is one.
- **C2 (proof replaced).** U, W from LL; e : 𝒜(U) ⊗ W → N_{W̃}, a ⊗ w ↦ a ⊗ η(1 ⊗ w). gr^0 Ξ_e
  is an isomorphism (both sides summands of finite free 𝒜⁰|U-modules with the same global
  sections, S4.c on the over-site). So u ≫ Ξ_e = (W̃ → T(W̃)) (both determined by Γ, S4.c),
  and u is a quasi-isomorphism by 2-out-of-3. ⚠ Uses X compact (C7.a): C2's Lean statements
  get `[CompactSpace X] [T2Space X]` (as C6 already has).
- **C5.a–c (proof replaced).** N := N_{K′} on U = X (C7.c); A11 gives M and e with
  (0,0)-component Γ(f⁰) (a quasi-isomorphism by S3, 𝒜⁰ fine, no boundedness needed); C5.b :=
  Ξ_e (C7.e); C5.c := C7.f, gr^0 Ξ_e ≅ f⁰ via Γ (S4.c). Step 7 uses C7.d instead of tensorC.
  Lean: `exists_αMap_quasiIso` keeps its statement (compose Ξ_e with C7.d).
- **C4 step 3 (made explicit).** New: ℋ_U on the over-site (same section-level data as C3, base
  U) with ℋ(M₁, M₂)|U ≅ ℋ_U(M₁|U, M₂|U), and Ψ_U compatible with Ψ. The square of step 3 is
  unchanged; u is C2's map. Step 5 (H⁰ dictionary) is unchanged, only spelled out: H⁰Γ(ℋ) =
  H0(M₁, M₂) (C3), H⁰Γ(𝓗om(αM₁, I)) = K(R)(αM₁, I) (S7), = D(R)(αM₁, αM₂) for I K-injective.

**v1.12 (27–28 Oct 2026), approved by the human with gate 4 (29 Oct 2026); applied to §7 and the
C4 Lean note (`restrSheafOfIso`). Layout and Lean names only, no mathematical change.**
§7 file layout to be refreshed to the files that exist after phase 4. On approval, replace the
`Comparison/ (planned, phase 4)` block of §7 by:
```
  Comparison/ SetupDef.lean (C0 defs)  Setup.lean, SetupAux.lean (C0 API)
             AlphaDef.lean (C1 α)  FunctorDef.lean (C1 J)  AlphaSheaf(Aux).lean (C1.a)
             AlphaOver(Aux).lean (C1.c)
             Perfect.lean, PerfectAux.lean, PerfectLoc.lean, PerfectModel.lean (C2)
             HomSheaf.lean, HomSheafAux.lean, HomSheafRetract.lean (C3)
             FullyFaithful.lean, FullyFaithful{Aux, Top, Phi, Square, Global, Local}.lean (C4)
             EssSurj.lean, EssSurj{Aux, Core, Model}.lean (C5)  Equivalence.lean (C6)
             ModelDual.lean, ModelTSheaf.lean, ModelDef.lean (C7.a, c, e)
             ModelConnNab.lean, ModelConn.lean (C7.b)  ModelBC.lean (C7.b, d: ιT)
             ModelTensor{Pair, Kappa, Coord, Iso}.lean, ModelTensor.lean (C7.d)
             ModelFilG0.lean, ModelFil.lean, ModelCrit{Site, Coord, Fil}.lean, ModelCrit.lean
             (C7.f)
             (FROZEN at gate 4: SetupDef, AlphaDef, FunctorDef and the definitions they use)
```
and add to `Algebra/`: GenHomDef.lean, BaseChangeHomDef.lean, BaseChangeResDef.lean (C1 defs,
FROZEN at gate 4), BaseChangeExt.lean (C3), BaseChangeLift.lean, TotMap.lean (C7),
HomAlongT.lean, QuasiIsoElem.lean (C4); to `Sheaf/`: FineDef.lean, RingOfDef.lean (defs, FROZEN
at gate 4), HomAction.lean (S7.a′), HomOver.lean, HomOverSections.lean, HomSectionsMap.lean,
RestrEval.lean (S7.b′–c′, C4); to the top level: ChecksComparison.lean (C0 non-vacuity).
Files over ~500 lines were split for size (28 Oct 2026, pure moves); the earlier pieces sit next
to the original name, e.g. `Algebra/BaseChange{Functor, Comp}.lean` before `BaseChange.lean`,
`Sheaf/{Soft, Projective, Restriction, Flat, BaseChange}Basic.lean`, `ChecksAlgebra.lean` before
`Checks.lean`; §7 lists the item files, the pieces inherit their item.
Lean names (human, 28 Oct 2026, "option A"): the complex α(M) of [B] is `P.sheafOf M` (was
`P.α M`), with `sheafOfSec`, `sheafOfMap`, `sheafOfOver`, `restrSheafOfIso`, … and
`TotSec`/`TSec`/`G0Sec` (were `Car`/`TCar`/`G0Car`); conventions §10. On approval, update the
Lean notes that name them (C1, C2, C5: e.g. `exists_αMap_quasiIso` → `exists_sheafOfMap_quasiIso`).

**v1.13 (30 Oct 2026, phase 5). Item 1 approved by the human with gate 5 (1 Nov 2026) and
applied to §7; item 2 (K4) still open.**
1. **F14/F15 layout.** `Statements.lean` may import only frozen files, so the hypothesis-free
   definitions it names cannot live in `Main.lean`. New file `BlockFunctorDef.lean` (frozen at
   gate 5): `dolbeaultPresheaf`, `dolbeaultPreData` (F14, C0.a), `blockFunctor E X :=
   (dolbeaultPreData E X).J` (F15). `Main.lean`: `dolbeaultData h₁ h₂` (F14, C0.b),
   `blockPerf` (for any `HasDerivedCategory` instance), `main_theorem : MainStatement`.
   `ChecksMain.lean`: K1 corollary, K6. On approval, §7 gains these files.
2. **K4 (open).** "Hom_Ho(M, M[k]) = H^{0,k}(X)" needs the shift on cohesive modules, part of Z2
   (LATER). Proposed replacement: for the unit module 𝒜 (Q = 𝒜⁰ in degree 0, 𝕏 = ∂̄), an
   isomorphism of complexes `homComplex 𝒜 𝒜 ≅ (𝒜^{0,•}(X), ∂̄)`, hence H^k(Hom^•(𝒜, 𝒜)) ≅
   H^{0,k}_∂̄(X), and for k = 0: Hom_Ho(𝒜, 𝒜) ≅ ker ∂̄ on 𝒜^{0,0}(X) = O(X). Needs the human's
   decision.

**v1.14 (30 Oct 2026), approved by the human 1 Nov 2026, with Z4.b as a port of TauCeti
`Pompeiu.lean` (attribution paragraph in the module docstring). Z4 is phase 6.**
Source: `blueprint/blueprint-dg.md` (written for TauCeti) and its audit section "Audit
(30 Oct 2026)". Nothing below changes a frozen file or the main statement; H1 stays a `def`, the
new result is a theorem about it. To be applied only after gate 5 and the human's approval.
1. **Z4 leaves §6 (LATER) and becomes phase 6** (after gate 5). Z4's text "Needs F13" is
   replaced by: needs only a chart-form constructor (Z4.f) built from F7, F9.a and the transition
   lemmas of F11; F13 stays LATER.
2. **Items Z4.a–Z4.h** (new files only; informal proofs as in blueprint-dg §§A–D with the audit's
   corrections B.1–B.4 and simplifications S1–S3):
   - **Z4.a Cauchy kernel** (`Analysis/CauchyKernel.lean`): `LocallyIntegrable (fun t : ℂ ↦ t⁻¹)`,
     from Mathlib's `locallyIntegrable_of_norm_le_rpow` (α = 1 < 2 = dim_ℝ ℂ).
   - **Z4.b One-variable ∂̄ (Cauchy–Pompeiu)** (`Analysis/Pompeiu.lean`): for `h : ℂ → Λ` (Λ a
     complex Banach space), `ContDiff ℝ 1 h`, compact support, `u w = π⁻¹ ∫ t⁻¹ • h (w − t)`
     satisfies `antiPart (fderiv ℝ u w) (toConj 1) = h w`. Proof: `Du = π⁻¹(t⁻¹ ⋆ Dh)`
     (Mathlib convolution derivative); polar coordinates around w: the angular term integrates
     to 0 over each circle, the radial term to −h(w) along each ray, so
     ∫ ζ⁻¹ ∂̄h(w+ζ) dA = −π h(w). Proposed: port TauCeti `Pompeiu.lean` (Apache 2.0, with
     attribution in the module docstring) — needs the human's decision.
   - **Z4.c Parametric solver** (`Analysis/CauchySolve.lean`): `cauchySolve v F z :=
     (π⁻¹ : ℂ) • ∫ t : ℂ, t⁻¹ • F (z − t • v)` for `F : E → Λ` C^∞ with compact support:
     (i) C^∞ on E with `fderiv (cauchySolve v F) = cauchySolve v (fderiv ℝ F)` (parametric
     convolution lemmas, g(z,ζ) = F(z + (ζ − ℓ z)•v), ℓ v = 1); (ii) `L (cauchySolve v F z) =
     cauchySolve v (L ∘ F) z` for ℂ-linear CLMs L; (iii) for v ≠ 0,
     `dbarPart (cauchySolve v F) z (toConj v) = F z` (slice through z, then Z4.b).
   - **Z4.d Contraction** (`Forms/Contraction.lean`): contraction = `curryLeft`; anticommutation,
     `curryLeft a (toConj v) = 0` on a basis ⇒ `a = 0`; `dbarPart` commutes with CLMs; B4
     `curryLeft (dbar ω z) v = dbarPart ω z v − dbar (fun y ↦ curryLeft (ω y) v) z` (degree
     q + 1) and `curryLeft (dbar ω z) v = dbarPart ω z v` (degree 0); `InvolvesOnly b k a`
     (contractions with `b j`, j ≥ k, vanish); B5.
   - **Z4.e Flat lemma** (`Forms/FlatGrothendieck.lean`): cutoff ψ (S2), induction step (split
     on q = 0 / q + 1), `exists_dbar_eq` on open subsets of E with η globally C^∞.
   - **Z4.f Chart forms** (`Forms/ChartForm.lean`): from a flat form η on W ⊆ (chartAt x).target,
     a Dolbeault form on `(chartAt x).source ∩ (chartAt x)⁻¹' W` whose expression in `chartAt x`
     is η; injectivity of `chartExpr` at points of the chart. Needed private lemmas of
     `Forms/SheafBasic.lean`, `Forms/DolbeaultFree.lean` become public (visibility only).
   - **Z4.g H1** (`Forms/DolbeaultGrothendieck.lean`): `theorem dolbeaultGrothendieck
     [IsManifold 𝓘(ℂ, E) ∞ X] : DolbeaultGrothendieck E X`.
   - **Z4.h Corollary** (`MainH1.lean`): `MainStatement` without H1, as a theorem only (no new
     statement to freeze; a new main statement follows after Z5). `#print axioms` checks.
3. **Conventions** (on approval): ∂̄ along v is `dbarPart ω z v` = ½(D_v + i D_{iv}); the
   one-variable solver is π⁻¹ ∫ t⁻¹ h(w − t) dA (= 2T in TauCeti's normalization).

**v1.15 (1 Nov 2026), approved by the human 1 Nov 2026: Z5 (proof of H2) is phase 7.**
Decisions with the approval: Z5.j adds a new main statement without hypotheses, to be frozen at
the phase-7 gate; K4 is to be done including the triangulated structure on `Ho(P_A)` (Z2 leaves
LATER), in parallel with Z5 where possible, otherwise after it (separate blueprint for Z2/K4,
needs approval).
Source: `blueprint/blueprint-ll.md` (audit of [B, Lemma 4.1.5] against [DK §2.2.2], [BSW Thm 5.3],
[DP Prop 16], [BR Lemma 3.9]; Lean target signatures checked in `Scratch/P12_LL.lean`).
1. Z5 leaves §6 (LATER) and becomes phase 7, split into Z5.a–Z5.j (blueprint-ll §5). "Needs
   F13" is replaced by the Z4.f chart transport.
2. Route: Block/DK/BSW gauge induction in operator form (flatness = Maurer–Cartan equation for a
   fibre-operator-valued `𝒜`), one-variable solver by an elementary Neumann series with
   derivative bounds (`contDiff_tsum`), strong form (isomorphism, `W` free).
3. Decided (human, 1 Nov 2026): Z5.j adds a new frozen main statement without H1 and H2.

**v1.16 (1 Nov 2026), approved by the human 1 Nov 2026 — Z2 and K4.** `blueprint/blueprint-tr.md`:
triangulated structure on `HoP 𝒜` by direct construction (shift via the sign isomorphism
`ι_a`, cone `inr 𝕏_N snd + inr φ fst − inl 𝕏_M fst`, axioms following Mathlib's
`HomotopyCategory`), K4 in its original form `Hom(𝒜, 𝒜⟦k⟧) ≅ H^{0,k}_∂̄(X)`; items Z2.a–g,
K4.a–b. Block's `𝔼[1] = −𝔼` holds only for right modules (audit).

**v1.17 (2 Nov 2026), approved by the human 2 Nov 2026 — Z5.g proof route.** The statement of
`exists_free_baseChange` (blueprint-ll §5) is unchanged; only the proof of A.1–A.3 changes. It
uses localization instead of idempotents, minors and Cramer's rule:
1. `m := ker (ev_x : A⁰(X) → ℂ)` is prime; `Q^p` (f.g. projective) has a free localization at
   some `r_p ∉ m` (`Module.FinitePresentation.exists_free_localizedModule_powers`).
2. If `r_p` becomes a unit in `A⁰(U′)`, then `A⁰(U′) ⊗ Q^p` is free (base change of the
   localization, `IsLocalizedModule.isBaseChange`).
3. `U′ := (chartAt x).source ∩ {y | r_p(y) ≠ 0 for a ≤ p ≤ b}` (finitely many `p` by
   boundedness); nonvanishing degree-0 forms are units. Outside `[a, b]`, `Q^p = 0`.
The open question "Mathlib name for the idempotent presentation" (blueprint-ll §7) is void.

**v1.18 (2 Nov 2026), approved by the human 2 Nov 2026 — follow-up of the external audit.**
Audit by Claude Fable 5.1 of the finished state (`audit/AUDIT_PROMPT.md`, tier `sources`, reply
`audit/out/report.md`, not committed). Verdict: no blocker, no major finding; both frozen main
statements faithful. The audit did not see the `Checks*` files, most theorem files, or any
proofs. Decisions:
1. **Freeze rule (F1).** Freeze exactly the term-dependency closure of the main statements
   (`MainStatement`, `MainStatementUnconditional`): the constants reached by unfolding them and
   their types. Instances on the reached types (e.g. `HasShift (HoP 𝒜) ℤ`, later
   `Pretriangulated`) are not frozen; `scripts/statement_defs.py` lists them in a separate,
   informational section. Consequences: `Algebra/Shift.lean` and `Algebra/ShiftHoP.lean`, frozen
   at gate 7 only through the `HasShift` instance, are unfrozen (the human removes the marker
   line; the hook blocks the agent); the Z2.c–g files will not be frozen. Replaces the rule of
   23 Oct 2026 ("every file the sheet lists").
2. **Z2 before the cone (F6, F7), added to `blueprint-tr.md`.** (a) Before Z2.d, `#check`/
   `#print` the pinned `CochainComplex.mappingCone.triangle`, `triangleδ`, `inr_triangleδ` and
   `Pretriangulated.Triangle.rotate`, and state the cone triangle of `HoP` with exactly those
   signs: a sign change of the third map alone is not an isomorphism of triangles, so a mismatch
   would make a later `J.IsTriangulated` (Z2.h) false while `Pretriangulated (HoP 𝒜)` holds.
   (b) New first step of Z2.c: `Tot.prodEquiv : Tot 𝒜 (fun p ↦ Q₁ p × Q₂ p) ≃ Tot 𝒜 Q₁ × Tot 𝒜 Q₂`
   with `rfl`/`simp` lemmas on pure tensors; the cone's `inl/inr/fst/snd` are then
   `LinearMap.inl/inr/fst/snd` through it, `𝕏_C` a 2×2 matrix, and the five identities and the
   `δ` formulas follow by `LinearMap.ext` + `simp` instead of generator inductions. (c) Optional
   sanity for Z2.h: `J(cone φ) ≅ mappingCone (J φ)` for closed `φ`.
3. **H2 route in `blueprint-ll.md` (F11).** The three deviations recorded so far only in PROGRESS
   and module docstrings go into blueprint-ll: A.1–A.3 by localization (v1.17); E.2 Maurer–Cartan
   from `𝕏² = 0` on the frame vectors and Λ-linearity of `mcOp`; E.3 first option of §7
   (`W` over `O(U″)` from `ρ`-preimages of the holomorphic degree-0 entries).
4. **Conventions (F3, F4, F10).** Notes in `conventions.md`: D_perf vs D^b_coh (equality is Z1;
   [A] has D_perf ⊆ D^b_coh); the carrier `DolbeaultAlg E U` depends on the `chartAt` of the
   `ChartedSpace` instance (as Mathlib's `smoothSheaf` does) and `chartExpr` is meaningful only on
   `e.target ∩ e.symm ⁻¹' U`; frozen statement files may import theorem files but use only
   `Prop`-valued terms from them (a rename breaks the build, never the meaning).
5. **Out-of-date text (F2, F8).** Known out of date and frozen, left unchanged: the module
   docstrings of `Hypotheses.lean` ("their proofs are LATER (Z4, Z5)") and `Statements.lean`
   ("H1 and H2 … not proved"); both are proved (Z4.g, Z5.i). The canonical statement is now
   `MainStatementUnconditional`, the theorem `main_theorem_unconditional` (CLAUDE.md goal and
   definition of done updated). Frozen declarations without docstrings (structure fields,
   instances; review sheet "(no docstring)") are accepted exceptions.
6. **Clean-ups (F12)** as already planned (PROGRESS): splits of files over 500 lines as pure
   moves, shared private helpers, `Scratch/` leftovers.
7. **K4.b (record).** Split of the blueprint's single file into `Algebra/UnitModule.lean`,
   `Algebra/UnitCohomology.lean` (generic dga, zero curvature) and
   `Forms/DolbeaultCohomology.lean`; `Bⁿ = d(𝒜ⁿ⁻¹)` with ℤ subtraction as in K4.a's `HomB`;
   the sanity check `H^{0,0}_∂̄(X) ≅ O(X)` is a bijection of sets (`K4_zero`), not additive
   (the additive version through `dolbeaultRhoU` times out in elaboration).

**v1.19 (2 Nov 2026), approved by the human 2 Nov 2026 — Z3 (twisted sheaves, curved Dolbeault
algebra).** Z3 leaves LATER and becomes phases 8–10 (stages 1–3). Blueprint:
`blueprint/blueprint-tw.md`; prototypes P15–P17 in `Scratch/`. Prototype results: P15 settles
item 5 for the partial attempt (at `h = 0` the curved instance is definitionally the frozen one;
`withC` must be reducible; the generic gauge needs explicit projections and, for general `k`,
`IsUnit (2 : k)`); P16 compiles `TwMod` with section-level gluing (`R(W)` acts through an explicit
coercion `toSec`); P17 compiles `restrOver = SheafOfModules.overMap` with both adjoints, exactness
and injectives. Decided with the approval (human, 2 Nov 2026): **Z2.d–g (cone, pretriangulated,
octahedron) are deferred**, to be done with or after Z3; K4 (the check of the shift) is done.
Z2.d–g are generic in `GCDga`, so they will apply to the curved `HoP` unchanged; reuse search:
no shortcut in Mathlib or TauCeti (no generic "pretriangulated dg ⇒ triangulated H⁰"; ports
10–28k lines), direct route kept, TauCeti `CategoryTheory/DG/Twisted/{Cone,Triangle,
Pretriangulated,Triangulated}.lean` as proof template, Mathlib `IsTriangulated.mk'` for the
octahedron. Original draft text:
Sources: Claude Fable 5.1 blueprint requests (`audit/TWISTED_PROMPT_A.md`, `_B.md`, tier
`sources`), replies `audit/out/report-TWISTED_PROMPT_A.md` (design), `…_B.md` (proof, Lean items,
decisions D1–D19), and the cut-off first attempt `…-partial-1.md`; `audit/out/` is gitignored, so
on approval the agent assembles `blueprint/blueprint-tw.md` (tracked) from parts A + B with the
changes below. Search for reusable material in the pinned Mathlib and in TauCeti: PROGRESS
handoff of 2 Nov 2026.
1. **Target.** `MainStatementTwisted`: for compact Hausdorff `X`, a `∂̄`-closed `h ∈ 𝒜^{0,2}(X)`
   and a twist datum `T = (finite cover, h⁰_α, u_αβ ∈ 𝒜⁰ˣ, ȟ ∈ Oˣ)` for `h`, the functor
   `twistedBlockFunctor : HoP (curvedDolbeault E X h) ⥤ DerivedCategory (TwMod O 𝒰 ȟ)` is full,
   faithful, with essential image `TwPerf`; plus `exists_twistData` (every closed `h` has a
   datum; uses H1 in degrees 1 and 2, F12, compactness, a refinement argument that replaces the
   Leray cover implicitly assumed in [A, Def 7.2.2]). Check K8:
   `MainStatementTwisted → MainStatementUnconditional`.
2. **Model** (B, decisions D1–D19, recommendations accepted unless noted): curvature as the
   `GCDga` field `c` on the same carrier (`GCDga.withC`, `DgaPresheaf.withCurvature`); gauge
   `𝕏 ↦ 𝕏 − β` (identity on `Hom`, `δ`) gives `HoP` equivalences; `TwMod` = families on the
   over-sites `Over U_α` with section-level gluing `φ_βγ φ_αβ = ȟ_αβγ φ_αγ`; `Abelian` built by
   hand and frozen with the statement (D13); injectives by Toda's twisted pushforward (D5);
   `TwIsPerfect := ∀ α, IsPerfectOver (K α)` (D12); new `DgaSheafData` (`PreResolvingData`
   without `c_eq_zero`) with copies of the C1/C3/C7 terms over it (D11); three stages, gates
   G1–G5, phases 8–10 (D16).
3. **Changed by the Mathlib search** (pin `56a0058`): `restrOver` is Mathlib's
   `SheafOfModules.overMap` with `overFunctorMap`, `overMapPushforwardAdj` (right adjoint) and
   `pullbackPushforwardAdjunction` (left adjoint), not B's `overFunctor` + `overOverEquiv` route
   (B correction 9); `Abelian (TwMod)` through `Abelian.ofCoimageImageComparisonIsIso`,
   `PreservesCoimageImageComparison.iso` and `JointlyReflectIsomorphisms`; injectives of the
   components from `IsGrothendieckAbelian (SheafOfModules R)`; transport of injectives by
   `preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`; `exp` by
   `HasFDerivAt.cexp`/`ContDiff.cexp`; shrinking lemma `exists_iUnion_eq_closure_subset`. Not
   in Mathlib: twisted sheaves, gerbes, 2-cocycles, effective descent for sheaves of modules,
   `Equivalence.mapDerivedCategory` (≈ 40 lines). TauCeti: nothing for twisted sheaves; its curved
   dg modules (right modules, `w = −h`) are a design reference only.
4. **Verified against the repo:** A11 `lifting` holds for any curvature (its flatness field is
   `θ² = c·`), so B's V1 fallback is void; `exists_quasiIso_of_enough` is stated for any abelian
   category (V2 closed); `PreResolvingData.c_eq_zero` is used in `FunctorDef`, `ModelDef` (B
   correction 1 confirmed).
5. **Discrepancy, to settle by prototype P15:** the partial first attempt claims the twisted
   statement at `h = 0` specializes literally (curved instance definitionally the frozen one);
   A/B obtain `c = res 0`, equal to `0` only propositionally, so K8 is a transport theorem. A/B is
   assumed. The partial attempt's other model (components as sheaves on `X` living on `U_i`,
   Grothendieck abelian) is not taken.
6. **Size** (revised after item 3): full theorem ≈ 12–21k lines; checked statement (statement
   closure, `exists_twistData`, K8) ≈ 5–8k lines. First steps after approval: `blueprint-tw.md`;
   prototypes P15 (curved/flat defeq), P16 (`TwMod` on `Fin 2`, `Abelian`), P17 (`overMap` API) in
   `Scratch/`; then stage 1 (Z3.a–e), gate G1.

**v1.20 (3 Nov 2026), approved by the human 3 Nov 2026 — Z3.l design (option A, chosen by the human 3 Nov 2026;
prototype `Scratch/P22_ExtZero.lean`).** blueprint-tw C.8 named `extTw α` without a construction.
Mathlib's extension by zero (left adjoint of `restrOver`) has no explicit sections, which the
section-level gluing of `TwMod` needs. Option B (abstract adjoints with base-change isomorphisms and
their coherence on triple overlaps) is not taken.
1. **Explicit extension by zero.** For `V : Opens X` and `F` on `Over V`, `extX V F : Mod R` on `X`:
   sections over `W` are the `s ∈ F(W ⊓ V)` with "support closed in `W`", i.e. some open `W' ≤ W`
   with `W ≤ (W ⊓ V) ⊔ W'` and `s|(W' ⊓ V) = 0` (stalk-free). A sheaf on `X` by unique gluing (the
   template of `glue`, Z3.k). On `Over U` it is used through `restr U` (sections, restriction and
   scalars are `rfl`, P22), so no sheaf condition on an over-site is needed.
2. **`extTw α N`** (twist cocycle `T`): components `restr (U β) (extX (U α) N)`. Sections over
   `W ≤ U_β` are a subtype of `N(W ⊓ U_α)`, independent of `β` (as in Toda's pushforward), so the
   gluing is `ȟ_αβγ|(W ⊓ U_α) ·`. `φ_self` by normalization, cocycle by `unitRes_cocycle` at
   `(α, β, γ, δ)` on `W ⊓ U_α`.
3. **`extTw α ⊣ comp_α`.** Unit `N → (extTw α N)_α`, `s ↦ s|(W ⊓ U_α)`. For `f : N → M_α`, the
   component `β` sends `s` (witness `W'`) to the unique `t ∈ M_β(W)` with `t|(W ⊓ U_α) =
   φ_αβ(f s)` and `t|W' = 0` (`sec_existsUnique_gluing`; independent of `W'`). `extTw α`
   preserves monomorphisms (injective on sections), so `comp_α` preserves injectives (C.5).
4. **Flatness.** The proof of `isFlat_extZero_unit` (S8.b) uses only two facts: sections vanish
   near every point outside `V`, and the restriction to `V` is flat. Stated as a lemma for any
   such sheaf, it applies to `extX V F` for flat `F` (`(extX V F)|V ≅ F`). Components of
   `extTw α F` are then flat by `IsFlat.restr`.
5. **Componentwise flat resolutions.** For `M`, S8.c on `Over U_α` gives a flat epi `F_α ↠ M_α`
   (`ringOf (R.over U) = (ringOf R).over U` by `rfl`, P22). Then `⊕_α extTw α F_α ↠ M` is a finite
   biproduct, and its `β` component contains `F_β ↠ M_β` through the unit isomorphism.
   `exists_quasiIso_of_enough` with P = "componentwise flat" gives bounded-above componentwise flat
   resolutions (G.1).
6. **Item split.** Z3.l: `ExtZero.lean`, `ExtTw.lean`, `ExtTwAdj.lean`, `FlatResolution.lean`
   (1–4, 5, C.5; ≈ 1.2–2k lines). New Z3.l′: twisted base change along a map of ring sheaves (the
   gluing maps through `sheafBC` and restriction isomorphisms, since sections of `sheafBC` are not
   explicit), and tensor commutes with `glue` (C.7 (g)) (`BaseChange.lean`, `GlueTensor.lean`;
   ≈ 0.6–1.2k). Z3.l′ is used only in Z3.u (G.2), so it moves to stage 3 before Z3.u, and gate G2
   follows Z3.l.
7. **Risks and size.** Risk 4 (`extTw` coherence) is replaced by two risks: the S8.b
   generalization (low; the existing proof already allows a general `M`), and Z3.l′ (sections of
   `sheafBC` are not explicit). Stage 2 grows by ≈ 1–1.5k lines.

**v1.21 (6 Nov 2026), approved by the human 6 Nov 2026 (gates 13 and 14) — K7 and Z2.d–g.**
1. **K7′ detail** (§6): the transcription of TauCeti's `delBar` and its comparison with our ∂̄
   (`ChecksK7.lean`), as drafted 6 Nov 2026.
2. **blueprint-tr §3c–§3d**: cone triangle, rotation, shift of cones and the `Pretriangulated`
   instance (Z2.f1–f4); cone of a composite and the octahedron (Z2.g1–g2), as drafted 6 Nov 2026.
   All proved: `instance : IsTriangulated (HoP 𝒜)`, generic in `GCDga`.

**v1.22 (6 Nov 2026), requested by the human 6 Nov 2026 — names of the main statements.**
Renamed, with content unchanged (the `def` bodies are identical; `scripts/statement_defs.py` lists
the same 276 declarations): `MainStatement` → `MainStatementConditional` (file `Statements.lean` →
`StatementsConditional.lean`, `main_theorem` → `main_theorem_conditional`), and
`MainStatementUnconditional` → `MainStatement` (file `StatementsUnconditional.lean` →
`Statements.lean`, `main_theorem_unconditional` → `main_theorem`). So `MainStatement` and
`main_theorem` now name the canonical statement without hypotheses. The two statement files were
unfrozen by the human for the rename and refrozen. Earlier entries of this history, old gate
sheets and dated PROGRESS entries keep the old names.
