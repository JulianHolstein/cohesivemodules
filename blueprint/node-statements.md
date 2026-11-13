# Readable node statements (documentation plan B14)

Read by `scripts/blueprint_gen.py`. One `## ID` section per blueprint node; its text is the
statement shown on the node (the statement panel of the dependency graph and the chapter page).
The text of the Markdown blueprints stays authoritative and is printed below it as "Blueprint
notes"; the dependency edges are still read from that text and from Lean. `check` reports nodes
without a section here (`NO-TEXT`). Text before the first `## ` is ignored.

Rules for the statements (human, 10 Nov 2026: "a precise, readable statement"):
- **Faithful to Lean.** The statement describes what the Lean declarations of the node (column
  "Lean" of `lean-map.md`) actually say: same hypotheses, same generality, same conclusion. Where
  Lean is more general than the sources, say the Lean version; where it deviates from the
  sources, add one short sentence "Deviation: …".
- **Self-contained and precise.** State the setting ("Let A be a bounded graded-commutative
  dga …"), all hypotheses (finiteness, boundedness, compactness, smoothness) and the
  conclusion. A definition says what the defined object is; a theorem says what is proved.
  Several sub-results: a short bulleted list.
- **Readable.** Ordinary mathematical prose. Unicode mathematics with `^`/`_` (braces for more
  than one character: `A^{p+1}`, `D_{perf}`). No history (v1.x, "replaces"), no Lean
  implementation details, no file names, no "✓/✗". Lean names in backticks only where they
  help the reader (the Lean links are shown on the node anyway).
- **Short.** Usually 2–8 lines; proofs belong in the proof part, not here.

## M — Main theorem conditional
Let E be a finite-dimensional complex normed space and X a compact Hausdorff complex manifold
modelled on E. Let A = 𝒜_X(X) be the Dolbeault algebra of X and O_X its sheaf of holomorphic
functions. Assume that X satisfies the Dolbeault–Grothendieck lemma (H1) and the local gauge
lemma in its weak form (H2). Then the functor J : Ho(P_A) ⥤ D(O_X), M ↦ α(M), into the derived
category of sheaves of O_X-modules is full and faithful, and its essential image is exactly
D_{perf}(X, O_X). Equivalently, J corestricts to an equivalence Ho(P_A) ≃ D_{perf}(X, O_X).
Both hypotheses are theorems (H1, H2), so this form is a corollary of Z5.j.

Deviation: D_{perf}(X, O_X) instead of Block's D^b_{coh}(X); the equivalence is stated as full,
faithful and essential image D_{perf}.

## A1 — Bounded graded-commutative dga
Let k be a commutative ring. A *bounded graded-commutative curved dga* over k is a ℤ-graded
k-algebra A = ⨁_q A^q together with
- a top degree N with A^q = 0 for q < 0 and for q > N;
- graded commutativity: ab = (−1)^{pq} ba for a ∈ A^p, b ∈ A^q;
- a k-linear differential d of degree +1 with d(ab) = da·b + (−1)^p a·db for a ∈ A^p, and
  d ∘ d = 0;
- a curvature c ∈ A^2 with dc = 0.

Deviation: Block allows non-commutative A with d² = [c, −]; for graded-commutative A this
is d² = 0. Boundedness is added (it holds for the Dolbeault algebra).

## A2 — Connections
Let A be a bounded graded-commutative curved dga over a commutative ring k, and P an
A^0-module. A *connection* on P is an additive map ∇ : P → A^1 ⊗_{A^0} P with
∇(fe) = df ⊗ e + f·∇e for f ∈ A^0 (it is then automatically k-linear).
- Every finitely generated projective A^0-module has a connection.
- The difference ∇₁ − ∇₂ of two connections on P is A^0-linear.

Deviation: additivity is assumed and k-linearity derived; left modules.

## A3 — Cohesive and quasi-cohesive modules
Let A be a bounded graded-commutative curved dga over k with curvature c. A *quasi-cohesive
module* M = (Q, 𝕏) is a family of A^0-modules Q^p (p ∈ ℤ) together with a k-linear operator 𝕏
of total degree 1 on the total module Tot Q = A ⊗_{A^0} ⨁_p Q^p (A acting on the left factor)
such that 𝕏(a·x) = da·x + (−1)^{|a|} a·𝕏x for homogeneous a, and 𝕏 ∘ 𝕏 = c·(−). It is
*cohesive* if Q^p = 0 outside a bounded range of p and every Q^p is finitely generated
projective over A^0; P_A denotes the cohesive modules.
- 𝕏 is determined by its values on the generators 1 ⊗ e, and conversely an additive map θ on
  the generators of total degree 1 with θ(fe) = df ⊗ e + f·θ(e) that is flat on generators
  extends to a quasi-cohesive module with 𝕏(a ⊗ e) = da ⊗ e + (−1)^{|a|} a·θ(e).
- Writing 𝕏^j for the form-degree-j part of 𝕏 on generators: 𝕏^1(fe) = df ⊗ e + f·𝕏^1(e)
  (a connection, no sign); 𝕏^0 is an A^0-linear map of degree +1 on ⨁_p Q^p with 𝕏^0 ∘ 𝕏^0 = 0.

Deviation: left modules; the curvature is c = −c_Block.

## A3.b′ — Flatness in all degrees
Let M = (Q, 𝕏) be a quasi-cohesive module over a bounded graded-commutative curved dga A with
curvature c ∈ A^2, and 𝕏^j : Q^p → A^j ⊗_{A^0} Q^{p+1−j} the components of 𝕏 on generators,
extended to Tot Q by the Leibniz rule. Then flatness 𝕏 ∘ 𝕏 = c·(−) is equivalent to the
equations Σ_{i+j=n} 𝕏^i ∘ 𝕏^j = δ_{n,2}·c·(−) for all n ≥ 0, one in each form degree n
(in degree 0: 𝕏^0 ∘ 𝕏^0 = 0). Not formalized; not used by any other item.

## A4 — Hom complexes
Let A be a bounded graded-commutative curved dga over k and M₁ = (Q₁, 𝕏₁), M₂ = (Q₂, 𝕏₂)
quasi-cohesive modules. Hom^n(M₁, M₂) is the k-module of k-linear maps φ : Tot Q₁ → Tot Q₂
raising total degree by n with φ(a·x) = (−1)^{n|a|} a·φ(x) for homogeneous a, with
differential δφ = 𝕏₂ ∘ φ − (−1)^n φ ∘ 𝕏₁.
- δ maps Hom^n to Hom^{n+1} and δ ∘ δ = 0 (also with curvature, since |c| = 2).
- Composition maps Hom^m × Hom^n to Hom^{m+n}, and δ(ψ ∘ φ) = δψ ∘ φ + (−1)^m ψ ∘ δφ for
  ψ of degree m; the identity lies in Hom^0 and is closed.
- δ agrees with Mathlib's `CochainComplex.HomComplex.δ`: δφ = 𝕏₂ ∘ φ + (−1)^{n+1} φ ∘ 𝕏₁.
- Restriction to generators is a k-linear isomorphism from Hom^n(M₁, M₂) to the A^0-linear maps
  ψ : ⨁_p Q₁^p → Tot Q₂ with ψ(Q₁^p) in total degree p + n; the inverse is
  ψ̂(a ⊗ e) = (−1)^{n|a|} a·ψ(e).

Deviation: M₁ may be any quasi-cohesive module (the sources take M₁ cohesive).

## A5 — Homotopy category Ho
Let A be a bounded graded-commutative curved dga over k. The homotopy category Ho(P_A) has
the cohesive modules as objects and, as morphisms M → N, the degree-0 cohomology
H^0 = Z^0/B^0 of the Hom complex, where Z^0 = {φ ∈ Hom^0(M, N) : δφ = 0} and
B^0 = δ(Hom^{−1}(M, N)); composition is induced by composition of maps. Ho(P_A) is a
preadditive, k-linear category.

## A6 — Form-degree filtration
Let A be a bounded graded-commutative curved dga over k with top degree N, and M₁, M₂
quasi-cohesive modules. F^b Tot Q is the k-span of the a ⊗ e with a ∈ A^q, q ≥ b, and
F^b Hom^n(M₁, M₂) consists of the φ ∈ Hom^n with φ(F^c Tot Q₁) ⊆ F^{c+b} Tot Q₂ for all c.
- φ ∈ Hom^n lies in F^b iff φ(1 ⊗ e) ∈ F^b Tot Q₂ for every generator e, i.e. the components
  of φ into A^{b′} ⊗ Q₂ vanish for b′ < b.
- δ maps F^b Hom^n into F^b Hom^{n+1}.
- The filtration is finite: F^0 Hom^n = Hom^n and F^b Hom^n = 0 for b > N.

## A7 — Finite filtration comparison
Let C be an abelian category and N ∈ ℕ. Suppose given, for b = 0, …, N, maps
f_b : F^b K → F^b L of ℤ-indexed cochain complexes in C, and for b < N maps of short exact
sequences 0 → F^{b+1} → F^b → gr^b → 0 (of the K-side into the L-side) whose first two
components are f_{b+1} and f_b. If every induced map gr^b K → gr^b L (b < N) is a
quasi-isomorphism and f_N is a quasi-isomorphism (e.g. F^N = 0), then f_0 is a
quasi-isomorphism.

Deviation: replaces the spectral sequences of the sources by the homology long exact sequence.

## A8 — Homotopy criterion
Let A be a bounded graded-commutative dga over k and φ : M₁ → M₂ a closed degree-0 map of
cohesive modules. Then φ is an isomorphism in Ho(P_A) iff its (0,0)-component
φ^0 : (Q₁, 𝕏₁^0) → (Q₂, 𝕏₂^0) is a homotopy equivalence of complexes of A^0-modules
(equivalently, since these are bounded complexes of projectives, a quasi-isomorphism).
Not formalized; not used by any other item.

## A9 — Base change along dga maps
Let A, B be bounded graded-commutative curved dgas over k. A *dga map* f : A → B is a
k-algebra map preserving degrees, the differential and the curvature (f(c_A) = c_B). For a
quasi-cohesive A-module M = (Q, 𝕏), the base change f^*M is the quasi-cohesive B-module with
generators B^0 ⊗_{A^0} Q^p and 𝕏_B(b ⊗ m) = db ⊗ m + (−1)^{|b|} b·𝕏m.
- If M is cohesive, so is f^*M.
- φ ∈ Hom^n(M₁, M₂) gives f^*φ ∈ Hom^n(f^*M₁, f^*M₂), (f^*φ)(b ⊗ m) = (−1)^{n|b|} b·φ(m),
  with f^*(δφ) = δ(f^*φ); this gives a functor Ho(P_A) ⥤ Ho(P_B).
- Maps of degree n out of f^*M₁ are determined by their values on the image of
  Tot Q₁ → Tot(f^*Q₁), a ⊗ e ↦ f(a) ⊗ (1 ⊗ e).
- For a second dga map g : B → C, γ ⊗ q ↦ γ ⊗ (1 ⊗ q) is a closed degree-0 isomorphism
  (g ∘ f)^*M ≅ g^*(f^*M), natural on Hom complexes in every degree; it gives a natural
  isomorphism of functors (g ∘ f)^* ≅ g^* ∘ f^* on Ho(P_A).

Deviation: left modules; Block's ω is 0.

## A10 — Cohesive modules from complexes
Let A be a bounded graded-commutative dga over k with curvature c = 0, ρ : R → A^0 a map of
commutative rings with d ∘ ρ = 0, and (W, d_W) a cochain complex of R-modules. Then A ⊗_R W,
with generators A^0 ⊗_R W^p and 𝕏(a ⊗ w) = da ⊗ w + (−1)^{|a|} a ⊗ d_W w, is a quasi-cohesive
module; it is cohesive if W is bounded with finitely generated projective terms.
For every quasi-cohesive N, restriction along w ↦ 1 ⊗ w is an additive bijection from
Hom^n(A ⊗_R W, N) to the families of ρ-semilinear maps f_p : W^p → Tot N landing in total degree
p + n; it carries δ to (δf)_p = 𝕏_N ∘ f_p − (−1)^n f_{p+1} ∘ d_W.

Deviation: requires c = 0 (otherwise 𝕏 ∘ 𝕏 = 0 ≠ c·(−)).

## A11 — Lifting theorem
Let A be a bounded graded-commutative curved dga over k (curvature c arbitrary) such that every
A^b is flat over A^0. Let N = (Q, 𝕏) be a quasi-cohesive module, (P, ∂) a bounded cochain
complex of finitely generated projective A^0-modules, and e^0 : (P, ∂) → (Q, 𝕏^0) a
quasi-isomorphism. Then there are a cohesive module (A ⊗_{A^0} P, 𝔼) with generators P^p and
𝔼^0 = ∂, and a closed degree-0 map e : (A ⊗ P, 𝔼) → N whose (0,0)-component is e^0
(ε(e(1 ⊗ x)) = e^0(x), ε the form-degree-0 part).
The proof constructs 𝔼 and e form degree by form degree; at each step it only needs that the
cone of e^0 ∘ − : gr^b Hom(P, P) → gr^b Hom(P, Q) has no cohomology in degree 1.

## A12 — Total quasi-isomorphism
Let A be a bounded graded-commutative dga over k with curvature c = 0 such that every A^b is
flat over A^0. Let φ : M₁ → M₂ be a closed degree-0 map of quasi-cohesive modules whose
(0,0)-component φ^0 : (Q₁, 𝕏₁^0) → (Q₂, 𝕏₂^0) is a quasi-isomorphism of complexes of
A^0-modules. Then φ is a quasi-isomorphism of total complexes (Tot Q₁, 𝕏₁) → (Tot Q₂, 𝕏₂)
(complexes of k-modules graded by total degree). In particular, in the lifting theorem (A11)
with c = 0, the map e is a quasi-isomorphism of total complexes.

Deviation: stated for any such φ (the sources state it for the map e of A11).

## A13 — Bridge to Block's definition
Let A be a bounded graded-commutative curved dga over k with curvature c, and c_B ∈ A with
c = −c_B. A quasi-cohesive module in Block's convention is a family of A^0-modules Q^p with a
k-linear operator 𝔼 of total degree 1 on the right module (⨁_p Q^p) ⊗_{A^0} A satisfying
𝔼(eω) = 𝔼(e ⊗ 1)·ω + (−1)^{|e|} e ⊗ dω for e ∈ Q^p, and 𝔼 ∘ 𝔼 + (−)·c_B = 0; its morphisms of
degree n are the right A-linear maps of degree n, with dφ = 𝔼₂ ∘ φ − (−1)^n φ ∘ 𝔼₁.
Transport along σ : e ⊗ a ↦ (−1)^{|e||a|} a ⊗ e gives
- mutually inverse bijections between Block's (cohesive, quasi-cohesive) modules and those of A3;
- for each n a k-linear isomorphism from Block's Hom^n to Hom^n of A4, φ ↦ σ ∘ φ ∘ σ^{−1},
  compatible with the differentials, composition and identities.

## Z2.a — Shift
Let A be a bounded graded-commutative curved dga over k and M = (Q, 𝕏) a cohesive module, a ∈ ℤ.
The shifted generators are Q[a]^p = Q^{p+a}, and ι_a : Tot Q[a] → Tot Q,
α ⊗ e ↦ (−1)^{a|α|} α ⊗ e, is a k-linear bijection taking total degree m to m + a with
ι_a(βx) = (−1)^{a|β|} β ι_a(x).
- Generally, if u : Tot Q′ → Tot Q is such a bijection of degree m, then (−1)^m u^{−1} 𝕏 u is a
  quasi-cohesive structure on Q′.
- The shift M[a] = (Q[a], (−1)^a ι_a^{−1} 𝕏 ι_a) is a cohesive module, and ι_a ∈ Hom^a(M[a], M)
  is closed.

Deviation: Block's 𝔼[1] = −𝔼 fails the Leibniz rule for left modules; the shift is transported
along ι_a instead.

## Z2.b — Shift functor on Ho(P_A)
Let A be a bounded graded-commutative curved dga over k. A *shift datum* of degree m from M′ to
M is a k-linear bijection v : Tot M′ → Tot M taking total degree n onto n + m, with
v(βx) = (−1)^{m|β|} β v(x) and 𝕏′ = (−1)^m v^{−1} 𝕏 v; shift data compose (degrees add), and
two shift data v₁, v₂ of the same degree onto M give an isomorphism v₂^{−1} ∘ v₁ in Ho(P_A).
- Ho(P_A) has a shift by ℤ: M⟦a⟧ = M[a] on objects, [φ]⟦a⟧ = [ι_a^{−1} ∘ φ ∘ ι_a] on morphisms,
  with M[0] ≅ M and M[a+b] ≅ M[a][b] the comparisons of the shift data ι_0, id and ι_{a+b},
  ι_a ∘ ι_b.
- Each shift functor is additive and k-linear.

## Z2.c — Zero object
Let A be a bounded graded-commutative curved dga over k.
- For families Q₁, Q₂ of A^0-modules, with (Q₁ × Q₂)^p = Q₁^p × Q₂^p, the map
  α ⊗ (e₁, e₂) ↦ (α ⊗ e₁, α ⊗ e₂) is an A-linear isomorphism
  Tot(Q₁ × Q₂) ≅ Tot Q₁ × Tot Q₂ preserving total degree componentwise.
- The module with all Q^p = 0 and 𝕏 = 0 is cohesive and is a zero object of Ho(P_A); in
  particular Ho(P_A) has a zero object.

## Z2.d — Cone
Let A be a bounded graded-commutative curved dga over k, M, N cohesive modules and
φ ∈ Z^0(M, N) a closed degree-0 map. The cone C(φ) has generators Q_N^p × Q_M^{p+1}; through
Z2.c and ι_1, Tot C(φ) ≅ Tot M × Tot N, giving inl ∈ Hom^{−1}(M, C), inr ∈ Hom^0(N, C),
fst ∈ Hom^1(C, M), snd ∈ Hom^0(C, N) with fst∘inl = id, snd∘inr = id, fst∘inr = 0,
snd∘inl = 0, inl∘fst + inr∘snd = id. The operator is
𝕏_C = inr 𝕏_N snd + inr φ fst − inl 𝕏_M fst, and C(φ) is a cohesive module with
δ inl = inr ∘ φ, δ inr = 0, δ fst = 0, δ snd = −φ ∘ fst (Mathlib's mapping-cone signs).

## Z2.e — Maps of cones
In the setting of Z2.d (φ ∈ Z^0(M, N)), with T a cohesive module:
- inr : N → C(φ) is closed of degree 0;
- (desc) for α ∈ Hom^{−1}(M, T) and closed β : N → T of degree 0 with δα = β ∘ φ,
  α ∘ fst + β ∘ snd : C(φ) → T is closed of degree 0;
- (lift) for closed α ∈ Hom^1(T, M) and β ∈ Hom^0(T, N) with δβ = −φ ∘ α,
  inl ∘ α + inr ∘ β : T → C(φ) is closed of degree 0;
- (map of cones) for φ_i ∈ Z^0(M_i, N_i), closed a : M₁ → M₂, b : N₁ → N₂ of degree 0 and
  h ∈ Hom^{−1}(M₁, N₂) with δh = b ∘ φ₁ − φ₂ ∘ a, desc(inl₂ ∘ a + inr₂ ∘ h, inr₂ ∘ b) is a
  closed degree-0 map C(φ₁) → C(φ₂).

## Z2.f — Ho(P_A) pretriangulated
Let A be a bounded graded-commutative curved dga over k (no further hypotheses). For
φ ∈ Z^0(M, N) the *cone triangle* is M →[φ] N →[inr] C(φ) →[w_φ] M⟦1⟧ with
w_φ = −ι_1^{−1} ∘ fst, and a triangle in Ho(P_A) is *distinguished* if it is isomorphic to a
cone triangle. With the shift of Z2.b, this makes Ho(P_A) a pretriangulated category:
- X →[id] X → 0 → X⟦1⟧ is distinguished, and every morphism is the first map of a
  distinguished triangle;
- a commutative square between the first maps of two distinguished triangles extends to a
  morphism of triangles (for cone triangles, by a map of cones, Z2.e);
- (cone triangle of φ).rotate ≅ cone triangle of inr_φ, with components id, id and a homotopy
  equivalence M⟦1⟧ ≅ C(inr_φ); distinguished triangles are closed under rotation.

## Z2.g — Octahedron axiom
Let A be a bounded graded-commutative curved dga over k. For closed degree-0 maps u : X₁ → X₂,
v : X₂ → X₃, the triangle C(u) →[m₁] C(v ∘ u) →[m₂] C(v) →[w_v ≫ inr_u⟦1⟧] C(u)⟦1⟧, with m₁, m₂
the maps of cones of the squares (id, v) and (u, id) with zero homotopy, is distinguished.
Hence the pretriangulated category Ho(P_A) satisfies the octahedron axiom: Ho(P_A) is
triangulated, for every curvature c.

## S1 — Fine sheaves of rings
Let X be a topological space and R a sheaf of rings on X. A global section ρ ∈ R(X) is
*supported in* an open U if there is an open V with U ∪ V = X and ρ|_V = 0 (equivalently
supp ρ ⊆ U). R is *fine* if for every finite open cover (U_i) of X there are ρ_i ∈ R(X) with
Σ_i ρ_i = 1 and each ρ_i supported in U_i.
- **Extension by zero.** If ρ is supported in U, M is a sheaf of R-modules and t ∈ M(U), there is
  a unique s ∈ M(X) with s|_U = ρ|_U · t and s|_V = 0 on every open V where ρ|_V = 0.
- **For morphisms.** If R is commutative and ρ is supported in U, every morphism φ : M|_U → N|_U
  gives a morphism ψ : M → N with ψ = ρ·φ over opens V ⊆ U and ψ = 0 over opens where ρ vanishes.

Deviation: only finite covers are required (the usual notion on compact spaces).

## S2 — Γ is exact on modules over a fine sheaf
Let R be a sheaf of rings on a topological space X and f : M → N an epimorphism of sheaves of
R-modules.
- f is locally surjective: for every s ∈ N(U) and x ∈ U there are an open x ∈ V ⊆ U and
  t ∈ M(V) with f(t) = s|_V.
- If X is compact and R is fine, then Γ(X, f) : M(X) → N(X) is surjective.

## S3 — Acyclic complexes of S-modules
Let X be compact and R a fine sheaf of rings on X. For ℤ-indexed cochain complexes of sheaves of
R-modules (with R-linear differentials):
- if K is acyclic, the complex of global sections Γ(X, K) is acyclic;
- degreewise: if K is exact at n, then Γ(X, K) is exact at n;
- if f : K → L is a quasi-isomorphism, so is Γ(X, f).

No boundedness is assumed.

## S3.b — Soft sheaves
Let R be a sheaf of rings on a topological space X. A sheaf M of R-modules is *soft* if for every
closed K ⊆ X, open U ⊇ K and s ∈ M(U) there are t ∈ M(X) and an open V with K ⊆ V ⊆ U and
t|_V = s|_V.
- (i) Let S be a fine sheaf of rings on X acting on M through an additive map
  S(X) → End(M) with 1 acting as the identity and ρ acting as 0 over every open where ρ vanishes.
  Then M is soft. In particular every module over a fine commutative sheaf of rings is soft.
- Let X be compact Hausdorff and 0 → A → B → C → 0 a short exact sequence of R-modules with A
  soft. (ii) Γ(X, B) → Γ(X, C) is surjective. (iii) If B is also soft, so is C.
- (iv) On compact Hausdorff X, a bounded-below acyclic complex of R-modules with soft terms has
  acyclic complex of global sections.

Deviation: softness is defined through open neighbourhoods of closed sets rather than stalks or
sections over closed sets; on compact Hausdorff spaces this is the usual notion.

## S4 — Projective modules over a fine sheaf
Let R be a sheaf of rings on a topological space X. A sheaf of R-modules is a *finite free
summand* if it is a retract of R^m for some m ∈ ℕ.
- If X is compact and R is fine, every free R-module R^{(I)} (any index type I) is projective;
  hence every finite free summand is projective.
- If X is compact and R is fine and commutative, a module that is locally a finite free summand
  (each point has an open U with M|_U a finite free summand) is globally one.
- For any R and any finite free summand M: Γ(X, M) is a finitely generated projective
  R(X)-module, and Γ : Hom_R(M, N) → Hom_{R(X)}(Γ(X, M), Γ(X, N)) is bijective for every
  R-module N.

## S5 — Restriction and extension by zero
Let R be a sheaf of rings on a topological space X and U ⊆ X open. Restriction M ↦ M|_U sends
sheaves of R-modules to sheaves of R|_U-modules on U; it is exact.
- R^{(I)}|_U ≅ (R|_U)^{(I)}, and the restriction of a finite free summand is a finite free
  summand.
- Extension by zero j_! is the left adjoint of restriction. The unit M → (j_! M)|_U is an
  isomorphism; every section of j_! M vanishes near each point outside U; and j_! is exact.
- Consequently restriction preserves injective objects.

## S6 — Locality
Let R be a sheaf of rings on a topological space X.
- A short complex M₁ → M₂ → M₃ of R-modules is exact iff every section of M₂ over U killed by
  the second map comes, near every point of U, from a section of M₁.
- A complex K of R-modules is acyclic if every point has an open neighbourhood U with K|_U
  acyclic; a map f of complexes is a quasi-isomorphism if every point has an open neighbourhood
  U with f|_U a quasi-isomorphism.
- On any site, a map of complexes of sheaves of modules that is a quasi-isomorphism on sections
  over every object is a quasi-isomorphism.

## S7 — Hom sheaves
Let R be a sheaf of commutative rings on a site C (in particular on X or on the over-site of an
open U). For R-modules M, N the *Hom sheaf* 𝓗om(M, N) is the sheaf of R-modules with
𝓗om(M, N)(V) = Hom(M|_V, N|_V), R acting through the target, functorial in both variables
(pre- and post-composition). For ℤ-indexed complexes K, L, the *Hom complex* 𝓗om(K, L) is the
complex of sheaves of R-modules with 𝓗om(K, L)^n = ∏_{p+n=q} 𝓗om(K^p, L^q) and differential
δz = z ∘ d + (−1)^{n+1} d ∘ z. Its sections over V are the degree-n cochains K|_V → L|_V, and
𝓗om(M, N)|_V ≅ 𝓗om(M|_V, N|_V).

## S8 — Tensor products and K-flat resolutions
Let R be a sheaf of commutative rings on a site.
- The *tensor product* M ⊗ N of sheaves of R-modules is the sheafification of the presheaf
  V ↦ M(V) ⊗_{R(V)} N(V).
- The *tensor product of complexes* K ⊗ L is the total complex of the double complex K^p ⊗ L^q
  (Koszul sign on the differential of the second factor); it is functorial in both variables.
- M is *flat* if M ⊗ − preserves monomorphisms; a complex K is *K-flat* if K ⊗ L is acyclic for
  every acyclic complex L.
- On a space X, tensor products commute with restriction to an open U:
  (M ⊗ N)|_U ≅ M|_U ⊗ N|_U.

## S9 — Perfect complexes
Let R be a sheaf of rings on a topological space X; complexes are ℤ-indexed cochain complexes of
sheaves of R-modules.
- K is *strictly perfect* if K^n = 0 outside some interval [a, b] and every K^n is a finite free
  summand (on any site).
- K is *perfect* if every point has an open neighbourhood U, a strictly perfect complex P of
  R|_U-modules and quasi-isomorphisms K|_U ← L → P.
- D_{perf}(X, R) is the full subcategory of the derived category D(R) on the objects isomorphic
  to Q(K) for some perfect K; Q(K) lies in D_{perf}(X, R) iff K is perfect.
- If X is compact, every perfect K has local models as above all concentrated in one interval
  [a, b], and then the homology sheaves of K vanish outside [a, b].

Deviation: perfectness is a roof of quasi-isomorphisms on each U instead of an isomorphism in
D(R|_U); the two are equivalent.

## S10 — Globalization over a fine sheaf
Let X be compact and R a fine sheaf of commutative rings on X. Every perfect complex K of
R-modules receives a quasi-isomorphism P → K from a strictly perfect complex P.

Supporting lemmas, for a sheaf of rings R on any site:
- a chain map from a strictly perfect complex to an acyclic complex is locally null-homotopic;
- for E strictly perfect and a quasi-isomorphism s : L → K, every chain map E → K lifts locally
  through s up to homotopy;
- an epimorphism onto a finite free summand splits locally; in a bounded acyclic complex in
  degrees [m, n] whose terms other than the (m+1)-st are finite free summands, that term is
  locally a finite free summand;
- if P is strictly perfect and exact in all degrees ≥ k, then H^{k−1}(P) is locally a quotient of a
  finite free module.

And on X with R fine: a module that is locally a quotient of a finite free module is a quotient of
a finite free module.

## S11 — Derived-category facts from Mathlib
Let C be an abelian category.
- If C has enough injectives, every complex K with K^i = 0 for i < n has a quasi-isomorphism
  K → I to a complex I of injective objects with I^i = 0 for i < n (so I is K-injective).
- If P is K-projective and s : L → K is a quasi-isomorphism, every chain map g : P → K lifts
  through s up to homotopy: there is f : P → L with s ∘ f homotopic to g.

Morphisms in D(C) into a K-injective complex, or out of a K-projective one, are homotopy classes
of chain maps; bounded complexes of projectives are K-projective.

## C0 — Resolving data
Let X be a topological space. *Pre-resolving data* on X consist of:
- for every open U a bounded graded-commutative ℂ-dga 𝒜(U) (A1), with restriction maps of dgas
  for V ⊆ U that are functorial; sections glue uniquely, being of degree q is a local property,
  and 𝒜^0 : U ↦ 𝒜^0(U) is a sheaf of commutative rings;
- curvature c = 0 in every 𝒜(U);
- a sheaf of commutative rings O and ring maps ρ_U : O(U) → 𝒜^0(U), natural in U, with
  d ∘ ρ_U = 0;
- 𝒜^0 is fine (S1), and every 𝒜^q is locally free of finite rank over 𝒜^0: each point has an
  open U and finitely many e_i ∈ 𝒜^q(U) such that, over every V ⊆ U, each β ∈ 𝒜^q(V) is uniquely
  Σ_i f_i·e_i|_V with f_i ∈ 𝒜^0(V).

From these, each 𝒜^q is a sheaf of 𝒜^0-modules. *Resolving data* add:
- O → 𝒜^0 → 𝒜^1 → ⋯ is a resolution: each ρ_U is injective, every closed section of 𝒜^0(U) lies
  in the image of ρ_U, and in degrees q + 1 ≥ 1 every closed form is locally exact;
- local lifting (LL): for every cohesive module M over 𝒜(X) and x ∈ X there are an open x ∈ U′, a
  bounded complex W of finitely generated projective O(U′)-modules and an isomorphism in
  Ho(P_{𝒜(U′)}) between M|_{U′} and 𝒜(U′) ⊗_{O(U′)} W.

Deviation: LL is required only for restrictions of global cohesive modules, and K-flatness of 𝒜
over O is not assumed. No compactness or Hausdorff condition is part of the data.

## C1 — The functor J
Let pre-resolving data on X be given (C0), A = 𝒜(X) and R = O. For a cohesive module M = (Q, 𝕏)
over A, α(M) is the complex of sheaves of O-modules with α(M)^n(V) the degree-n part of the base
change M|_V (A9), i.e. of 𝒜(V) ⊗_{𝒜^0(V)} ⨁_p (𝒜^0(V) ⊗_{A^0} Q^p) ≅ ⨁_{p+q=n} 𝒜^q(V) ⊗_{A^0} Q^p,
O acting through ρ, with differential 𝕏 of M|_V (d² = 0 because c = 0).
- Closed degree-0 maps give chain maps and coboundaries give null-homotopic maps, so M ↦ α(M)
  defines J_K : Ho(P_A) ⥤ K(O) and J : Ho(P_A) ⥤ D(O), the composite with the localization.
- For an open U and a cohesive module M over 𝒜(U), α_U(M) is the same construction on the
  over-site of U, and α(M)|_U ≅ α_U(M|_U).

J lands in the whole derived category D(O); that it lands in D_{perf} is C2.

## C2 — J lands in perfect complexes
Let resolving data be given on a compact Hausdorff space X.
- For an open U and a bounded complex W of finitely generated projective O(U)-modules there are
  a strictly perfect complex L of O|_U-modules and a quasi-isomorphism
  L → α_U(𝒜(U) ⊗_{O(U)} W) (A10).
- For every cohesive module M over 𝒜(X), α(M) is a perfect complex; hence J(M) ∈ D_{perf}(X, O).

Deviation: X is assumed compact Hausdorff, which the proof uses through the explicit model C7.

## C3 — Hom sheaves of cohesive modules
Let pre-resolving data be given on X and M₁, M₂ cohesive modules over 𝒜(U₀). For V ⊆ U₀ let
ℋ^n(M₁, M₂)(V) be the ℂ-linear maps χ : Tot(M₁) → Tot(M₂|_V) of degree n with
χ(a·x) = (−1)^{n|a|} a|_V·χ(x); by base change these are the degree-n maps M₁|_V → M₂|_V.
- For U₀ = X these form a complex ℋ(M₁, M₂) of sheaves of O-modules with
  δχ = 𝕏₂ ∘ χ − (−1)^n χ ∘ 𝕏₁, and ℋ(M₁, M₂)(X) ≅ Hom^•_{P_A}(M₁, M₂) in each degree.
- If X is compact Hausdorff, every term ℋ^n(M₁, M₂) is soft (S3.b): 𝒜^0(X) acts by
  multiplication. The differential is not 𝒜^0-linear.

## C4 — Full faithfulness
Let resolving data be given on a compact Hausdorff space X. Then for all M, N in Ho(P_A),
J : Hom(M, N) → Hom_{D(O)}(J M, J N) is bijective. Main steps:
- Ψ : ℋ(M₁, M₂) → 𝓗om(α(M₁), α(M₂)), χ ↦ α(χ), is a map of complexes, and ℋ(M₁, M₂) is bounded
  below; at X it sends a closed degree-0 map φ to α(φ).
- For a quasi-isomorphism r : α(M₂) → I to a bounded-below complex of injectives,
  r_* ∘ Ψ : ℋ(M₁, M₂) → 𝓗om(α(M₁), I) is a quasi-isomorphism (locally via LL, then S6).
- Hence f ↦ J(f) ∘ Q(r) is a bijection Hom_{Ho(P_A)}(M, N) → Hom_{D(O)}(α(M), I).

## C5 — Essential surjectivity
Let resolving data be given on a compact Hausdorff space X. Every object of D_{perf}(X, O) is
isomorphic to J(M) for some cohesive module M over 𝒜(X). Main steps:
- a perfect K receives a quasi-isomorphism from a bounded-above complex K′ of flat O-modules;
- for such K′ (perfect), the base change 𝒜^0 ⊗_O K′ along ρ : O → 𝒜^0 is perfect;
- given a strictly perfect complex P̃ of 𝒜^0-modules and a quasi-isomorphism P̃ → 𝒜^0 ⊗_O K′,
  there are a cohesive M and a quasi-isomorphism α(M) → 𝒜^• ⊗_O K′ (𝒜^• the first factor);
- for bounded-above, termwise flat K′ (no compactness needed), ρ̂ ⊗ K′ : O[0] ⊗ K′ → 𝒜^• ⊗ K′
  is a quasi-isomorphism, and O[0] ⊗ K′ ≅ K′.

Deviation: K-flat resolutions replace Malgrange's flatness theorem.

## C6 — Comparison theorem for resolving data
Let resolving data be given on a compact Hausdorff space X, with A = 𝒜(X). Then the functor
J : Ho(P_A) ⥤ D(O) is full and faithful, and its essential image is exactly D_{perf}(X, O).

This is the abstract comparison theorem, for any resolving data (C0). Its application to the
Dolbeault data is F15 (`blockPerf`), which is the proof of M.

## C7 — The explicit model T(K) of 𝒜 ⊗_R K
Let pre-resolving data be given on a compact space X, U ⊆ X open, and F a complex of
𝒜^0|_U-modules on the over-site of U. A *flat connection* on F is, for every V, generator data
θ_V on the 𝒜^0(V)-modules F^p(V) of total degree 1, flat (𝕏_V² = c = 0), with form-degree-0 part d_F, and
compatible with restriction. Given one:
- N(V) = (⨁_p F^p(V), 𝕏_V) is a quasi-cohesive module over 𝒜(V);
- T(F)^n(V) = (𝒜(V) ⊗_{𝒜^0(V)} ⨁_p F^p(V))^n is a sheaf of O|_U-modules, and with 𝕏 a complex T;
- a closed degree-0 map e : M → N(U) from a cohesive module over 𝒜(U) induces a map of complexes
  Ξ_e : α_U(M) → T.
- For K a complex of O|_U-modules and F = 𝒜^0 ⊗_O K, with a connection satisfying ∇(1 ⊗ k) = 0
  (which exists), T ≅ 𝒜^•|_U ⊗ K, and under this and K ≅ O|_U[0] ⊗ K the map K → T,
  k ↦ 1 ⊗ (1 ⊗ k), is ρ̂|_U ⊗ K.

## F1 — Realification
Let E be a complex normed space and M a complex C^∞ manifold modelled on E (charts with complex
C^∞, i.e. holomorphic, transition maps). Then M, with the same charts, is a real C^∞ manifold
modelled on E (E regarded as a real normed space). Moreover ℂ, as a real manifold, is a smooth
ring: multiplication ℂ × ℂ → ℂ is real C^∞. Hence the real-smooth ℂ-valued functions on M form a
sheaf of commutative rings C^∞_M(ℂ).

## F2 — The fibre Λ^{0,q}
Let E and F be complex normed spaces. The conjugate space Ē is E with the same norm and the
scalar action c · v := c̄ v. For q ∈ ℕ, the fibre Λ^{0,q}(E; F) is the normed space of continuous
ℂ-multilinear alternating maps Ē^q → F (equivalently: real alternating maps on E that are
antilinear in each slot).
- A continuous ℂ-linear map T : E → E′ is also a continuous ℂ-linear map Ē → Ē′.
- Λ^{0,0}(E; F) ≅ F, isometrically: a 0-form at a point is a value.
- If E is finite-dimensional, Φ_q : ⋀^q_ℂ (Ē)^* → Λ^{0,q}(E; ℂ),
  φ_1 ∧ ⋯ ∧ φ_q ↦ (v ↦ det(φ_j(v_i))), is a linear isomorphism.
- For a basis b of E indexed by a finite linearly ordered set ι, the forms
  dz̄_I = Φ_q(dz̄_{i_1} ∧ ⋯ ∧ dz̄_{i_q}) (dz̄_i the dual basis of b in Ē), I running over the
  q-element subsets of ι, form a basis of Λ^{0,q}(E; ℂ). So dim Λ^{0,q}(E; ℂ) = C(n, q),
  n = dim_ℂ E, and Λ^{0,q} = 0 for q > n.

## F3 — The ∂̄-operator on open subsets of E
Let E, F be complex normed spaces and q ∈ ℕ. The antilinear part of a real-linear map L : E → G
is L″(v) = ½(L v + i·L(i v)), a ℂ-linear map Ē → G. For α : E → Λ^{0,q}(E; F) and x ∈ E let
D″α(x) be the antilinear part of the real derivative Dα(x), and
∂̄α(x)(v_0, …, v_q) = Σ_i (−1)^i D″α(x)(v_i)(v_0, …, v̂_i, …, v_q) ∈ Λ^{0,q+1}(E; F)
(Mathlib's normalization of the exterior derivative). Properties:
- ∂̄(α + β)(x) = ∂̄α(x) + ∂̄β(x) and ∂̄(cα)(x) = c ∂̄α(x) (c ∈ ℂ) if α, β are real-differentiable
  at x;
- ∂̄α(x) depends only on the germ of α at x.

Deviation: ∂̄ is defined for every function on E (with value 0 where α is not differentiable);
by locality this gives ∂̄ on open subsets of E.

## F4 — ∂̄∂̄ = 0
Let E, F be complex normed spaces and α : E → Λ^{0,q}(E; F). If α is real C² at x, then
∂̄(∂̄α)(x) = 0.

## F5 — Product on the total fibre
Let E be a finite-dimensional complex normed space, n = dim_ℂ E. The total fibre is the normed
space Λ^{0,•}(E) = ∏_{q=0}^{n} Λ^{0,q}(E; ℂ). It is a ℂ-algebra, with the product transported
from the exterior algebra ⋀_ℂ (Ē)^* along Φ = (Φ_q)_q of F2, so that Φ is an isomorphism of
ℂ-algebras. Viewing a q-form as an element of Λ^{0,•}(E) in degree q (zero if q > n):
- the product of a p-form and a q-form is a (p+q)-form;
- graded commutativity: α ∧ β = (−1)^{pq} β ∧ α for a p-form α and a q-form β;
- Laplace formula: for a 1-form φ and a q-form β,
  (φ ∧ β)(v_0, …, v_q) = Σ_i (−1)^i φ(v_i) β(v_0, …, v̂_i, …, v_q);
- the product is a continuous bilinear map.

## F6 — Leibniz rule
Let E be a finite-dimensional complex normed space. For a p-form α and a q-form β at a point,
α ∧ β ∈ Λ^{0,p+q}(E; ℂ) is the degree-(p+q) part of their product in Λ^{0,•}(E). If
α : E → Λ^{0,p}(E; ℂ) and β : E → Λ^{0,q}(E; ℂ) are real-differentiable at x, then in Λ^{0,•}(E)
∂̄(α ∧ β)(x) = ∂̄α(x) ∧ β(x) + (−1)^p α(x) ∧ ∂̄β(x).

## F7 — Holomorphic pullback
Let E, F be complex normed spaces. For G : E → E and α : E → Λ^{0,q}(E; F) the pullback is
G^*α(x) = α(G x) ∘ DG(x), with the complex derivative DG(x) acting on Ē (junk where G is not
complex-differentiable).
- If α is real-differentiable at G x and G is complex C² at x, then ∂̄(G^*α)(x) = G^*(∂̄α)(x).
- G^*(f α)(x) = f(G x) · G^*α(x) for f : E → ℂ.
- (G ∘ H)^* α (x) = H^*(G^*α)(x) if H is complex-differentiable at x and G at H x.
- If E is finite-dimensional, the pullback T^* along a continuous ℂ-linear T : E → E, applied
  degreewise on Λ^{0,•}(E), is a unital ring homomorphism.

Deviation: G is a map E → E rather than a holomorphic map between open subsets; since all
hypotheses are local at x, this covers the latter.

## F8 — Cauchy–Riemann
Let E, F be complex normed spaces, V ⊆ E open and f : E → F real C^∞ on V. Then ∂̄f = 0 at every
point of V (f regarded as a 0-form) if and only if f is complex C^∞ (holomorphic) on V.

## F9 — The sheaves 𝒜^{0,q}_M(F) and 𝒜^{0,•}_M
Let E be a finite-dimensional complex normed space and X a complex manifold modelled on E. A form
on an open U ⊆ X is a function α : U → Λ^{0,•}(E), the value α(y) being written in the chart at
y. Its expression in a chart e is z ↦ T^*α(y), y = e^{−1}(z), T the complex derivative at z of the
transition map chartAt(y) ∘ e^{−1}. α is a *Dolbeault form* if, for every x ∈ U, its expression in
φ = chartAt(x) is real C^∞ at φ(x); its ∂̄ is (∂̄α)(x) = ∂̄(expression of α in φ)(φ(x)), degree
by degree. A form has degree q if all its other components vanish.
- Restrictions of Dolbeault forms are Dolbeault forms, and being Dolbeault is local, so
  Dolbeault forms are a sheaf of sets on X.
- The expression of a Dolbeault form in any atlas chart e is real C^∞ at e(x) for x ∈ U ∩ e.source.
- ∂̄ of a Dolbeault form is a Dolbeault form, and ∂̄ maps forms of degree q to degree q + 1.

Deviation: forms take values in the total fibre, and only ℂ-valued forms are treated; 𝒜^{0,q}
is the degree-q part (equivalent, since the direct sum is finite).

## F10 — The Dolbeault dga
Let E be a finite-dimensional complex normed space, n = dim_ℂ E, and X a complex manifold modelled
on E. For an open U ⊆ X, 𝒜_X(U) is the ℂ-algebra of Dolbeault forms on U (F9) with pointwise
operations, graded by 𝒜^{0,q}_X(U) = the forms of degree q (zero for q < 0 and q > n).
- 𝒜_X(U) with d = ∂̄ is a bounded graded-commutative dga (A1) with top degree n and curvature 0.
- Restriction along V ⊆ U is a map of dgas 𝒜_X(U) → 𝒜_X(V).
- Sheaf conditions: Dolbeault forms on opens U_i that agree on overlaps glue to a unique
  Dolbeault form on ⋃ U_i; having degree q is a local property.
- U ↦ 𝒜^{0,0}_X(U) is a sheaf 𝒜^0 of commutative rings on X.

The Dolbeault algebra of X is A = 𝒜_X(X).

## F11 — Fineness and local freeness
Let E be a finite-dimensional complex normed space, n = dim_ℂ E, and X a complex manifold modelled
on E.
- If X is compact Hausdorff, 𝒜^0 is fine: for every finite open cover (U_i) of X there are global
  sections ρ_i ∈ 𝒜^{0,0}_X(X) with Σ_i ρ_i = 1, each ρ_i supported in U_i (it vanishes on an open
  V_i with U_i ∪ V_i = X).
- 𝒜^{0,q} is locally free of rank C(n, q) over 𝒜^0: every x ∈ X has an open neighbourhood U with
  forms e_I ∈ 𝒜^{0,q}_X(U), I running over the q-element subsets of {0, …, n−1}, such that on
  every open V ⊆ U each β ∈ 𝒜^{0,q}_X(V) is uniquely Σ_I f_I · e_I|_V with f_I ∈ 𝒜^{0,0}_X(V).

## F12 — Holomorphic functions
Let E be a finite-dimensional complex normed space and X a complex manifold modelled on E. O_X is
the sheaf of commutative rings of complex C^∞ (holomorphic) functions on X. ρ : O_X → 𝒜^0 is the
morphism of sheaves of rings that sends a holomorphic function f on U to f as a form of degree 0.
For every open U ⊆ X:
- ρ_U is injective;
- ∂̄ ρ_U(f) = 0 for every f ∈ O_X(U);
- every α ∈ 𝒜^{0,0}_X(U) with ∂̄α = 0 is ρ_U(f) for some f ∈ O_X(U).

So 0 → O_X(U) → 𝒜^{0,0}_X(U) → 𝒜^{0,1}_X(U) is exact.

## H1 — Dolbeault–Grothendieck lemma
Let E be a finite-dimensional complex normed space and X a complex manifold modelled on E. X
satisfies the *Dolbeault–Grothendieck lemma* if for every open U ⊆ X, every q ∈ ℕ, every x ∈ U and
every α ∈ 𝒜^{0,q+1}_X(U) with ∂̄α = 0, there are an open U′ with x ∈ U′ ⊆ U and
η ∈ 𝒜^{0,q}_X(U′) with ∂̄η = α|_{U′}. Theorem: this holds for every such X (no compactness or
Hausdorff assumption). With F12 it says that ρ : O_X → 𝒜^{0,•}_X is a resolution.

Deviation: stated on the manifold X in sheaf form, not on polydiscs in ℂ^n.

## H2 — Local gauge lemma, weak form
Let E be a finite-dimensional complex normed space and X a complex manifold modelled on E. X
satisfies the *local gauge lemma* (weak form) if for every cohesive module M over A = 𝒜_X(X) and
every x ∈ X there are an open U′ ∋ x, a bounded complex W of finitely generated projective
O_X(U′)-modules, and an isomorphism in Ho(P_{𝒜_X(U′)}) between the restriction M|_{U′} (base
change along 𝒜_X(X) → 𝒜_X(U′), A9) and 𝒜_X(U′) ⊗_{O_X(U′)} W (A10, along ρ_{U′}). Theorem: this
holds for every such X.

Deviation: the weak, sectionwise form of [B, Lemma 4.1.5]: only restrictions of global cohesive
modules, a homotopy equivalence instead of a gauge equivalence, and W need not be free.

## F14 — The fields of C0
Let E be a finite-dimensional complex normed space and X a complex manifold modelled on E.
- U ↦ 𝒜_X(U) with restriction of forms is a presheaf of dgas on X.
- If X is compact Hausdorff, the Dolbeault data form pre-resolving data (C0.a): the dgas
  𝒜_X(U), which glue and have curvature 0; O = O_X with ρ_U : O_X(U) → 𝒜^{0,0}_X(U) and
  ∂̄ ∘ ρ = 0 (F12); 𝒜^0 a fine sheaf and each 𝒜^{0,q} locally free over it (F11). No analytic
  hypothesis is used.
- If moreover X satisfies H1 and H2, they form resolving data (C0.b): ρ is injective,
  O_X → 𝒜^0 → 𝒜^1 is exact (F12), the Dolbeault complex is locally exact in degrees ≥ 1 (H1),
  and the local lifting field LL is H2.

## F15 — Main theorem conditional: proof
The proof of M, as the Lean theorem `blockPerf`. Let E be a finite-dimensional complex normed
space and X a compact Hausdorff complex manifold modelled on E, A = 𝒜_X(X). The Dolbeault data
of X are pre-resolving data (F14) without any analytic hypothesis, so C1 gives the functor
J : Ho(P_A) ⥤ D(O_X). If X satisfies H1 and H2, the Dolbeault data are resolving data (F14), and
the comparison theorem C6 specialized to them says that J is full and faithful with essential
image D_{perf}(X, O_X).

This is the only node that applies the abstract theorem C6 to the Dolbeault data; M is the
statement itself (`MainStatementConditional`), and Z5.j is its form without H1 and H2.

Deviation: proved for any model of the derived category (any `HasDerivedCategory` instance), not
only the standard one.

## Z4.a — Cauchy kernel
The Cauchy kernel t ↦ t^{−1} is locally integrable on ℂ with respect to Lebesgue measure.

## Z4.b — One-variable ∂̄ (Cauchy–Pompeiu)
Let F be a complex Banach space and h : ℂ → F real C¹ with compact support. Let
u(w) = π^{−1} ∫_ℂ t^{−1} h(w − t) dA(t). Then for every w ∈ ℂ,
½ (Du(w)(1) + i·Du(w)(i)) = h(w),
i.e. ∂u/∂w̄ = h in the normalization of F3.

## Z4.c — Parametric solver
Let E be a complex normed space and Λ a complex Banach space. For v ∈ E and F : E → Λ let
u(z) = cauchySolve v F (z) = π^{−1} ∫_ℂ t^{−1} F(z − t v) dA(t). Let v ≠ 0 and F have compact
support.
- If F is real C^∞, then u is real C^∞ on E.
- If F is real C¹, then Du(z) = cauchySolve v (DF)(z) for every z.
- If F is continuous and L : Λ → Λ′ is continuous ℂ-linear (Λ′ Banach), then
  L(u(z)) = cauchySolve v (L ∘ F)(z).
- If F is real C¹, then ½ (Du(z)(v) + i·Du(z)(i v)) = F(z) for every z (∂̄ along v solves the
  equation).

## Z4.d — Contraction
Let E, F be complex normed spaces. For v ∈ Ē, the contraction ι_v : Λ^{0,q+1}(E; F) →
Λ^{0,q}(E; F) is (ι_v a)(w_1, …, w_q) = a(v, w_1, …, w_q).
- If ι_{b_i} a = 0 for every vector of a basis b of Ē, then a = 0.
- D″(L ∘ ω)(z) = L ∘ D″ω(z) for continuous ℂ-linear maps L between fibres, ω real-differentiable
  at z.
- For ω of degree q + 1, real-differentiable at z: ι_v ∂̄ω(z) = D″ω(z)(v) − ∂̄(ι_v ω)(z). For ω of
  degree 0: ι_v ∂̄ω(z) = D″ω(z)(v).
- Say a involves only dz̄_0, …, dz̄_{k−1} (for a basis b of Ē indexed by {0, …, n−1}) if
  ι_{b_j} a = 0 for all j ≥ k. If U ⊆ E is open, ω (degree q + 1) is real-differentiable on U,
  involves only dz̄_0, …, dz̄_{k−1} at every point of U and ∂̄ω = 0 on U, then D″ω(z)(b_j) = 0 for
  all z ∈ U and j ≥ k.

## Z4.e — Flat lemma
Let E be a finite-dimensional complex normed space with a fixed basis e_0, …, e_{n−1} (also a basis
of Ē). Flat Dolbeault–Grothendieck lemma: let U ⊆ E be open, x ∈ U, and β : E → Λ^{0,q+1}(E; ℂ)
real C^∞ on U with ∂̄β = 0 on U. Then there are an open U′ with x ∈ U′ ⊆ U and
η : E → Λ^{0,q}(E; ℂ), real C^∞ on all of E, with ∂̄η = β on U′. Ingredients:
- for v ≠ 0 and F : E → Λ^{0,q}(E; ℂ) real C¹ with compact support,
  D″(cauchySolve v F)(z)(v) = F(z) and D″(cauchySolve v F)(z)(w) = cauchySolve v (D″F(·)(w))(z);
- if every value of F involves only dz̄_0, …, dz̄_{k−1}, so does every value of cauchySolve v F;
- cutoff: for x ∈ U and an index k there are a real C^∞ ψ with compact support in U, ψ = 1 on an
  open W ∋ x, and an open slab S ⊇ W, stable under z ↦ z − t e_k (t ∈ ℂ), on which the
  derivatives of ψ in the directions e_j, i e_j (j ≠ k) vanish; ψα is C^∞ with compact support
  for every α that is C^∞ on U.

## Z4.f — Chart forms
Let E be a finite-dimensional complex normed space and X a complex manifold modelled on E. For
x ∈ X, φ = chartAt(x), an open W ⊆ E and η : E → Λ^{0,q}(E; ℂ), the chart form of η is the form on
U′ = φ.source ∩ φ^{−1}(W) whose value at y is η(φ(y)), placed in degree q and pulled back along the
derivative of φ ∘ chartAt(y)^{−1} at chartAt(y)(y).
- If W ⊆ φ.target, the expression of the chart form in φ is η on W.
- (Converse of F9.a.) If U ⊆ e.source for an atlas chart e and the expression of a form α on U in
  e is real C^∞ at e(y) for all y ∈ U, then α is a Dolbeault form.
- The chart form has degree q; if W ⊆ φ.target and η is real C^∞ on W, it is a Dolbeault form.

## Z4.g — H1: Dolbeault–Grothendieck lemma
Let E be a finite-dimensional complex normed space and X a complex manifold modelled on E (no
compactness or Hausdorff assumption). Then X satisfies the Dolbeault–Grothendieck lemma H1. Proof
outline: the flat expression of degree r of a form α in chartAt(x) (the degree-r component of its
chart expression) is C^∞ and ∂̄-closed near chartAt(x)(x); the flat lemma (Z4.e) solves ∂̄η = it,
and the chart form of η (Z4.f) is the required local primitive.

## Z4.h — Corollary
Let E be a finite-dimensional complex normed space and X a compact Hausdorff complex manifold
modelled on E, satisfying the local gauge lemma H2. Then J : Ho(P_A) ⥤ D(O_X), A = 𝒜_X(X), is full
and faithful with essential image D_{perf}(X, O_X), for the standard derived category and for any
other `HasDerivedCategory` instance. (H1 holds by Z4.g.)

## Z5.a — Kernel estimate
- For ρ ≥ 0: ∫_{B(0,ρ)} |t|^{−1} dA(t) = 2πρ.
- For every c ∈ ℂ, t ↦ |t|^{−1} is integrable on B(c, ρ), and ∫_{B(c,ρ)} |t|^{−1} dA(t) ≤ 3πρ for
  ρ ≥ 0.
- Let E, Λ be complex normed spaces, v ∈ E, ℓ : E → ℂ continuous ℂ-linear with ℓ(v) = 1, and
  G : E → Λ with ‖G‖ ≤ C and G(w) ≠ 0 only where |ℓ(w) − c| ≤ ρ (ρ ≥ 0). Then
  ‖cauchySolve v G (z)‖ ≤ 3ρC for every z ∈ E.

## Z5.b — Derivatives of the solver
For complex normed spaces E, Λ, v ∈ E and f : E → Λ let ∂̄_v f(z) = ½ (Df(z)(v) + i·Df(z)(i v))
(junk where f is not differentiable). Let E be finite-dimensional, Λ a Banach space, v ≠ 0 and
F : E → Λ with compact support.
- If F is real C^∞: D^m(cauchySolve v F)(z) = cauchySolve v (D^m F)(z) for all m ∈ ℕ, z ∈ E.
- If F is real C¹: ∂̄_v(cauchySolve v F) = F, and ∂̄_w(cauchySolve v F) = cauchySolve v (∂̄_w F) for
  every w ∈ E.

## Z5.c — One-variable gauge solver
Let E be a finite-dimensional complex normed space with a fixed basis e_0, …, e_{n−1} and
coordinate functionals c_k, and 𝔄 a complex Banach algebra with ‖1‖ = 1.
- Cutoff: for a neighbourhood K of x and an index k, for all small r > 0 there is ψ as in Z4.e
  (with compact support in K), with 0 ≤ ψ ≤ 1 and |c_k(w) − c_k(x)| ≤ 2r wherever ψ(w) ≠ 0.
- Neumann series: u_0 = 1, u_{i+1} = cauchySolve v (u_i · b), g = Σ_i u_i. If v ≠ 0, b is C^∞ with
  compact support, ℓ(v) = 1, b vanishes outside {|ℓ(w) − c| ≤ ρ}, ‖b‖ ≤ B and θ = 3ρB < 1, then
  ‖D^m u_i(z)‖ ≤ C_m (i+1)^m θ^i for all m, i, z, and g is C^∞ on E.
- Main result (𝔄 finite-dimensional): let U ⊆ E be open, x ∈ U, a : E → 𝔄 real C^∞ on U with
  values in a subalgebra S on U, and J a set of indices with k ∉ J and ∂̄_{e_j} a = 0 on U for
  j ∈ J. Then there are an open W with x ∈ W ⊆ U and g : E → 𝔄, real C^∞, with values in S and
  pointwise invertible, such that ∂̄_{e_k} g = g·a and ∂̄_{e_j} g = 0 (j ∈ J) on W.

## Z5.d — Fibre operators
Let E be a finite-dimensional complex normed space with a fixed basis e_0, …, e_{n−1}, and r ∈ ℕ.
The fibre of the local model is Fib = Λ^{0,•}(E)^r; fibre operators are the continuous ℂ-linear
endomorphisms of Fib (a finite-dimensional Banach algebra). Define: dz̄_j ∈ Λ^{0,•}(E), the 1-forms
dual to the basis; the contraction ι_j of Λ^{0,•}(E) with e_j; the grade involution σ = (−1)^q on
Λ^{0,q}; and on Fib, componentwise, ε_j = left multiplication by dz̄_j, ι_j, σ. Results:
- ε_iε_j = −ε_jε_i, ι_iι_j = −ι_jι_i, ι_jι_j = 0, ι_iε_j + ε_jι_i = δ_{ij};
- an operator commuting with every ε_j commutes with multiplication by every t ∈ Λ^{0,•}(E); one
  anticommuting with every ε_j satisfies T(t·s) = σ(t)·T(s);
- an element of Λ^{0,•}(E) killed by every ι_j has form degree 0.

For deg : {0, …, r−1} → ℤ, an element of Fib has total degree m if its i-th component has form
degree m − deg(i); an operator has total degree d if it raises total degree by d.

## Z5.e — Flat superconnections and gauges
Let E be a finite-dimensional complex normed space, ∂̄_j = ∂̄_{e_j} (Z5.b), and 𝒜, g : E → FibOp
(Z5.d). For s : E → Fib, ∂̄s is taken componentwise (F9). Let mc(𝒜) = Σ_j ε_j ∂̄_j𝒜 + 𝒜² and
g·𝒜 = g𝒜g^{−1} − (Σ_j ε_j ∂̄_j g) g^{−1}. Call 𝒜 odd at z if ε_j 𝒜(z) = −𝒜(z) ε_j for all j.
- ∂̄s(z) = Σ_j ε_j ∂̄_j s(z) if s is real-differentiable at z.
- If 𝒜 is C¹ at z and odd at z, and s is C² at z: (∂̄ + 𝒜)((∂̄ + 𝒜)s)(z) = mc(𝒜)(z) s(z).
- Let g be pointwise invertible and commute with every ε_j. If g is C¹ at z and s differentiable
  at z: g(∂̄ + 𝒜)(g^{−1}s) = (∂̄ + g·𝒜)s at z. If 𝒜 is odd at z, so is g·𝒜. On an open U where
  g and 𝒜 are C^∞ and 𝒜 is odd: mc(g·𝒜) = g mc(𝒜) g^{−1} on U.

## Z5.f — Gauge induction
Notation of Z5.d–Z5.e, with degrees deg : {0, …, r−1} → ℤ. A *flat superconnection* on an open
U ⊆ E is 𝒜 : E → FibOp, C^∞ on U, of total degree 1, odd and with mc(𝒜) = 0 on U. A *gauge* is
g : E → FibOp, C^∞ on E, pointwise invertible, of total degree 0, commuting with every ε_j. Let
a_i(𝒜) = ι_i𝒜 + 𝒜ι_i (the dz̄_i-coefficient). Main result: if 𝒜 is a flat superconnection on U and
x ∈ U, there are an open W with x ∈ W ⊆ U and a gauge g such that g·𝒜 is a flat superconnection on
W with a_i(g·𝒜) = 0 and ∂̄_{e_i}(g·𝒜) = 0 on W for every i. It follows by induction on k from:
- step: if a_i(𝒜) = 0 on U for i < k, then near x there is a gauge g with a_i(g·𝒜) = 0 for i ≤ k
  (g solves ∂̄_k g = g·a_k with values in the subalgebra of operators of total degree 0 commuting
  with every ε_j and with ι_i for i ≤ k; Z5.c).

## Z5.g — Local freeness
- Ring theory: a finitely generated projective module Q over a commutative ring R is free over a
  basic open containing a given prime 𝔪: Q[r^{−1}] is free over R[r^{−1}] for some r ∉ 𝔪. If
  Q[r^{−1}] is free and r becomes a unit in the R-algebra S, then S ⊗_R Q is free over S.
- Let E be a finite-dimensional complex normed space and X a complex manifold modelled on E.
  Evaluation at y ∈ U is a ring homomorphism 𝒜^{0,0}_X(U) → ℂ; a degree-0 form is a continuous
  function on U, and a nowhere-vanishing one is a unit of 𝒜^{0,0}_X(U).
- Main result: for a cohesive module M over 𝒜_X(X) with generators Q^p and x ∈ X, there is an open
  U′ ∋ x inside the source of chartAt(x) such that 𝒜^{0,0}_X(U′) ⊗_{𝒜^{0,0}_X(X)} Q^p is a free
  𝒜^{0,0}_X(U′)-module for every p.

## Z5.h — Frame model
Let A be a bounded graded-commutative dga (A1) over k and Q a graded A^0-module. A *graded frame*
of rank r is a degree function deg : {0, …, r−1} → ℤ and an A^0-basis (ẽ_i) of ⨁_p Q^p with
ẽ_i ∈ Q^{deg i} (coordinates of elements of Q^p vanish at frame vectors of other degrees).
- Every x ∈ A ⊗_{A^0} ⨁_p Q^p is uniquely Σ_i x_i (1 ⊗ ẽ_i) with x_i ∈ A; if x has total degree m,
  then x_i ∈ A^{m − deg i}.
- For a quasi-cohesive module N with a graded frame, the connection matrix ω_{ji} ∈ A^{deg i + 1 − deg j}
  is the j-th coefficient of 𝕏(1 ⊗ ẽ_i), and (𝕏x)_j = d x_j + Σ_i σ(x_i) ω_{ji}.
- Frame model: for N cohesive over 𝒜_X(U) with a graded frame, x_0 ∈ U and φ = chartAt(x_0), on
  V = φ(U ∩ φ.source) the chart expressions of the coefficients satisfy 𝕏 = ∂̄ + 𝒜 with
  𝒜(z)(t)_j = Σ_i σ(t_i) Ω_{ji}(z) (Ω the chart expression of ω), and 𝒜 is a flat superconnection
  on V (Z5.f).

## Z5.i — The local gauge lemma
- For a commutative ring R, deg : {0, …, r−1} → ℤ and an r×r matrix f over R with f_{ki} = 0 unless
  deg k = deg i + 1, and f² = 0: the complex W^p = R^{{i : deg i = p}}, d(w)_k = Σ_i f_{ki} w_i,
  a bounded complex of finitely generated projective R-modules.
- Algebraic form: let A be a dga with curvature 0, ρ : R → A^0 with d ∘ ρ = 0, N a cohesive module
  with graded frame of degrees deg and connection matrix ω, and G, H mutually inverse matrices over
  A with G_{ij}, H_{ij} ∈ A^{deg j − deg i} and dG_{ij} + Σ_k σ(G_{kj}) ρ(f_{ik}) = Σ_l ω_{lj} G_{il}.
  Then N ≅ A ⊗_R W in Ho(P_A).
- Geometric form: let X be a complex manifold modelled on a finite-dimensional E, x ∈ U ⊆ source
  of chartAt(x), N cohesive over 𝒜_X(U) with a graded frame, g a gauge and B a flat superconnection
  on V = φ(U) with B = g·𝒜 (𝒜 the frame model), a_i(B) = 0 and ∂̄_{e_i}B = 0 on V. Then
  N ≅ 𝒜_X(U) ⊗_{O_X(U)} W in Ho(P_{𝒜_X(U)}), W a bounded complex of finitely generated projective
  O_X(U)-modules.
- Hence every cohesive module over 𝒜_X(U′) with a graded frame is, near each x ∈ U′, isomorphic in
  Ho(P) to 𝒜_X(U″) ⊗_{O_X(U″)} W after restriction to an open U″ ∋ x; with Z5.g this proves H2.

## Z5.j — Main theorem
Let E be a finite-dimensional complex normed space and X a compact Hausdorff complex manifold
modelled on E. Let A = 𝒜_X(X) be the Dolbeault algebra of X and O_X its sheaf of holomorphic
functions. Then the functor J : Ho(P_A) ⥤ D(O_X), M ↦ α(M), into the (standard) derived category of
sheaves of O_X-modules is full and faithful, and its essential image is exactly D_{perf}(X, O_X).
The same holds for any other `HasDerivedCategory` instance.

Deviation: D_{perf} instead of D^b_{coh}; the equivalence is stated as full, faithful and essential
image D_{perf}.

## Z3.a — Curved dga/presheaf
Let A be a bounded graded-commutative curved dga (A1) with curvature c. For a closed element
c′ ∈ A^2 (dc′ = 0), A with curvature c′ is the curved dga with the same algebra, grading and
differential and curvature c′. For a presheaf of dgas D on X and a closed h ∈ A(X)^2, the
*curved presheaf* D_h has the same algebras, gradings and restriction maps, with curvature h|U on
each open U. *Sheaf data* on X are the fields of pre-resolving data (C0) except c = 0: a presheaf
of possibly curved dgas with gluing and degree-locality of sections, 𝒜^0 a fine sheaf of
commutative rings, a structure sheaf O with ρ : O → 𝒜^0 and d ∘ ρ = 0, and every 𝒜^q locally free
over 𝒜^0. Every pre-resolving data are sheaf data, and sheaf data with D replaced by D_h are
again sheaf data.

## Z3.b — Gauge
Let k be a commutative ring in which 2 is a unit, A a bounded graded-commutative curved dga over
k with curvature c, β ∈ A^1, and c′ = c + dβ. For a (quasi-)cohesive module (Q, 𝕏) over
(A, c′), its *gauge* (Q, 𝕏 − β·) is a (quasi-)cohesive module over (A, c), with
(𝕏 − β)^2 = c′ − dβ + β^2 = c; the inverse is 𝕏 ↦ 𝕏 + β·. The gauge does not change the Hom
complexes: Hom^n(M₁, M₂) is the same submodule, δ agrees on it, hence so do the closed and exact
degree-0 maps. Consequently the gauge is an equivalence Ho(P_{(A, c + dβ)}) ≌ Ho(P_{(A, c)}),
the identity on morphisms.

Deviation: the sources write "2 ≠ 0"; Lean assumes 2 is a unit in k (true for k = ℂ).

## Z3.c — Curved Dolbeault, twist data
Let X be a complex manifold modelled on a finite-dimensional complex normed space E.
- A *closed (0,2)-form* is a global Dolbeault form h ∈ 𝒜_X(X) of form degree 2 with ∂̄h = 0. The
  curved Dolbeault presheaf is U ↦ (𝒜_X(U), ∂̄, h|U), and the curved Dolbeault algebra is
  (𝒜_X(X), ∂̄, h), whose curvature is h.
- A *twist cocycle* for a sheaf of commutative rings R is a finite open cover (U_α) of X with
  units ȟ_αβγ ∈ R(U_α ∩ U_β ∩ U_γ)^×, equal to 1 when two indices coincide, satisfying
  ȟ_βγδ ȟ_αγδ^{−1} ȟ_αβδ ȟ_αβγ^{−1} = 1 on every open contained in U_α, U_β, U_γ, U_δ. The
  trivial cocycle is the cover {X} with ȟ = 1.
- A *twist datum* for a closed h ∈ 𝒜(X)^2 over sheaf data S is a twist cocycle ȟ of S.O together
  with primitives h^{0}_α ∈ 𝒜^1(U_α), dh^{0}_α = h|U_α, and units u_αβ ∈ 𝒜^0(U_α ∩ U_β)^× with
  du_αβ = (h^{0}_β − h^{0}_α) u_αβ, u_αα = 1, u_βα = u_αβ^{−1}, and
  ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ^{−1}. For h = dβ with β ∈ 𝒜^1(X) there is a twist datum on the
  cover {X} with h^{0} = β, u = 1, ȟ = 1 (for β = 0: the trivial datum for h = 0).

Deviation: multiplicative data (h^{0}, u, ȟ) on a finite cover instead of Antweiler's
(h^{0}, h^{1}, h^{2}, exp); the normalization and cocycle condition of ȟ are imposed as fields.

## Z3.d — Exp, existence
Let X be a compact Hausdorff complex manifold modelled on a finite-dimensional complex normed
space E, and h ∈ 𝒜^{0,2}(X) with ∂̄h = 0. Then h has a twist datum. More precisely:
- there are a finite open cover (U_α) of X, primitives h^{0}_α ∈ 𝒜^1(U_α) of h|U_α, and
  functions η_αβ ∈ 𝒜^0(U_α ∩ U_β) with ∂̄η_αβ = h^{0}_β − h^{0}_α, η_αα = 0 and η_βα = −η_αβ;
- for any such data, u_αβ = exp(η_αβ) (a unit of 𝒜^0 with ∂̄ exp(η) = exp(η)·∂̄η) and the
  holomorphic units ȟ_αβγ with ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ^{−1} form a twist datum for h.

## Z3.e — H2 on opens, LL^h
Let X be a complex manifold modelled on a finite-dimensional complex normed space E.
- (H2 over an open.) For an open U₀ ⊆ X, a cohesive module N over 𝒜_X(U₀) and x ∈ U₀, there are an
  open U′ ⊆ U₀ containing x, a bounded complex W of finitely generated projective
  O_X(U′)-modules and an isomorphism N|U′ ≅ 𝒜_X(U′) ⊗_{O_X(U′)} W in Ho(P_{𝒜_X(U′)}).
- (Curved local lifting.) Let X moreover be compact Hausdorff, h ∈ 𝒜^{0,2}(X) closed, T a twist
  datum for h and M a cohesive module over (𝒜_X(X), ∂̄, h). For x ∈ U_α the same conclusion holds
  for the gauged restriction gauge_{h^{0}_α}(M|U_α), a cohesive module over the flat algebra
  𝒜_X(U_α) with operator 𝕏 − h^{0}_α.

Deviation: Antweiler states the curved lemma for M|U′ itself; it is stated after the gauge by
h^{0}_α, which is an equivalence of homotopy categories (Z3.b).

## Z3.f — `restrOver`
Let R be a sheaf of rings on X and V ⊆ U opens. Restriction M ↦ M|V from sheaves of R|U-modules
on the over-site of U to sheaves of R|V-modules on the over-site of V is Mathlib's pushforward
along Over V → Over U. It is left adjoint to the pushforward along the other direction (which
therefore preserves injective objects), it also has a left adjoint, so it is exact, and
restricting to U and then to V is isomorphic to restricting to V.

## Z3.g — `TwMod`
Let R be a sheaf of commutative rings on X, (U_α)_{α∈ι} a family of opens and
ȟ_αβγ ∈ R(U_α ∩ U_β ∩ U_γ)^×. An *ȟ-twisted sheaf of R-modules* consists of sheaves of modules
M_α on the over-sites of U_α, and for every open W ⊆ U_α ∩ U_β an additive map
φ_αβ : M_α(W) → M_β(W), R(W)-linear and compatible with restriction, with φ_αα = id and
φ_βγ ∘ φ_αβ = ȟ_αβγ|W · φ_αγ on every W ⊆ U_α ∩ U_β ∩ U_γ. Morphisms are families of morphisms
M_α → N_α commuting with the gluing maps; composition is componentwise, and M ↦ M_α is the
component functor.

Deviation: the gluing is given on sections over every W ⊆ U_α ∩ U_β instead of as isomorphisms
of restricted sheaves; φ_αα = id is a field.

## Z3.h — Abelian
For every sheaf of commutative rings R on X, family of opens (U_α) and family of units ȟ_αβγ
(no cocycle condition needed), the category of ȟ-twisted sheaves of R-modules is abelian.
Kernels and cokernels are computed componentwise, with gluing maps induced from those of the
source and target, and the component functors M ↦ M_α preserve them. Supporting facts: a
compatible family of R(W)-linear section maps over all W ⊆ V defines a morphism of restricted
sheaves on V, and a monomorphism of sheaves of modules is injective on sections.

## Z3.i — Existence of injectives
Let R be a sheaf of commutative rings on X and ȟ a twist cocycle of R on a finite cover (U_α).
- For each α, Toda's twisted pushforward N ↦ push_α(N), from sheaves of R|U_α-modules to
  ȟ-twisted sheaves (sections over W ⊆ U_β are N(W ∩ U_α), gluing by ȟ_αβγ), is right adjoint
  to the component functor M ↦ M_α.
- The component functors preserve monomorphisms, and a morphism with mono components is mono;
  hence push_α preserves injective objects.
- Consequently the category of ȟ-twisted sheaves has enough injectives.
- The cocycle satisfies the cyclic symmetry ȟ_βγα = ȟ_αβγ.

## Z3.j — Perfectness
Let R be a sheaf of commutative rings on X.
- A complex K of sheaves of R|V-modules on the over-site of an open V is *perfect* if every
  x ∈ V has an open neighbourhood W ⊆ V with quasi-isomorphisms K|W ← L → P, P strictly perfect.
  If moreover all such P can be chosen concentrated in degrees [a, b], then the homology sheaves
  of K vanish outside [a, b]; restrictions of strictly perfect complexes are strictly perfect.
- A complex K of ȟ-twisted sheaves is *twisted perfect* if each component complex K_α is perfect
  on the over-site of U_α. D_{perf}(X, ȟ) is the class of objects of the derived category of
  ȟ-twisted sheaves isomorphic to Q(K) for a twisted perfect K.
- If ȟ_αβα = 1 for all α, β, the gluing maps assemble into a natural isomorphism
  M_α|U_α ∩ U_β ≅ M_β|U_α ∩ U_β.

Deviation: twisted perfectness is componentwise (the gluing maps play no role), and local roofs
of quasi-isomorphisms replace isomorphisms in the derived category.

## Z3.k — Gluing
Let R be a sheaf of commutative rings on X and (U_α) a family of opens.
- For a twisted sheaf M with trivial cocycle, the compatible families
  (s_α) ∈ ∏_α M_α(W ∩ U_α) form a sheaf glue(M) of R-modules on X, and M is isomorphic to the
  twisted sheaf of restrictions of glue(M) (no cover hypothesis).
- If ⋃_α U_α = X, gluing is an equivalence between twisted sheaves with trivial cocycle and
  sheaves of R-modules on X, with inverse N ↦ (N|U_α, identity gluing).
- (Rescaling.) For units g_αβ ∈ R(U_α ∩ U_β)^× with g_αα = 1 and families ȟ, ȟ′ with
  ȟ′_αβγ g_αγ = g_βγ g_αβ ȟ_αβγ, replacing φ_αβ by g_αβ φ_αβ is an equivalence between
  ȟ-twisted and ȟ′-twisted sheaves, the identity on components and morphisms.

## Z3.l — Generators
Let R be a sheaf of commutative rings on X and ȟ a twist cocycle of R on a finite cover (U_α).
- For a sheaf F of R|V-modules, its extension by zero j_!F is a sheaf of R-modules on X with
  (j_!F)|V ≅ F, whose sections vanish near every point outside V; if F is flat, so is j_!F.
- The twisted extension by zero N ↦ ext_α(N) (components (j_!N)|U_β, gluing by ȟ_αβγ) is left
  adjoint to the component functor M ↦ M_α.
- Every twisted sheaf is a quotient of one with flat components, and every complex of twisted
  sheaves strictly zero above degree b receives a quasi-isomorphism from such a complex with
  componentwise flat terms.

## Z3.l′ — Base change
Let ψ : R → S be a morphism of sheaves of commutative rings on X.
- For V ⊆ U and a sheaf M of R|U-modules, base change commutes with restriction:
  (S|U ⊗ M)|V ≅ S|V ⊗ M|V.
- Section maps out of S ⊗ M that are linear and natural are determined by their values on the
  elements 1 ⊗ m.
- Componentwise base change is a functor from ȟ-twisted R-modules to ψ(ȟ)-twisted S-modules,
  whose gluing maps satisfy φ′_αβ(1 ⊗ m) = 1 ⊗ φ_αβ(m).

## Z3.m — C1 over `DgaSheafData`
Let S be sheaf data on X (possibly curved), U₀ an open and M a cohesive module over 𝒜(U₀). The
constructions of C1 are defined over S word for word: the sheaf of rings 𝒜^0, the global algebra
𝒜(X) (with the curvature of S), the restrictions r_V, the ring sheaf O, the total module
Tot(M|V) for V ⊆ U₀, and its elements of total degree n, an O(V)-module α(M)^n(V). These form a
sheaf α(M)^n of O-modules with the operator 𝕏 : α(M)^n → α(M)^{n+1}, and α acts on closed
degree-0 maps and homotopies. For pre-resolving data these agree definitionally with C1.

Deviation: no complex α(M) and no functor are built here, since 𝕏^2 = c· need not vanish.

## Z3.n — `J_T`
Let S be sheaf data on X, h ∈ 𝒜(X)^2 closed, T a twist datum for h over S, and let M be a
cohesive module over the curved algebra (𝒜(X), h).
- For any sheaf data, β ∈ 𝒜^1(V) and M over 𝒜(U₀), V ⊆ U₀, the gauged operator 𝕏 − β· on
  α(M)(V) satisfies (𝕏 − β)^2 = 0 if dβ is the curvature over V (h|V for the curved data);
  if du = (β′ − β)u for u ∈ 𝒜^0(V), then (𝕏 − β′)(u·x) = u·(𝕏 − β)x; and homotopies of maps
  give homotopies for the gauged operators.
- J_T(M) is the complex of ȟ-twisted O-modules with components J_T(M)^n_α = α(M)^n|U_α,
  gluing maps u_αβ· and differential 𝕏 − h^{0}_α on U_α.
- M ↦ J_T(M) defines functors J_T : Ho(P_{(𝒜(X), h)}) ⥤ K(TwMod(O, U, ȟ)) and, for any
  derived category structure, Ho(P_{(𝒜(X), h)}) ⥤ D(TwMod(O, U, ȟ)).

Deviation: the gluing is by the units u_αβ instead of Antweiler's exp(h^{1}_αβ).

## Z3.o — Local identification
Let P be pre-resolving data on X, h ∈ 𝒜(X)^2 closed, T a twist datum for h over P and M a cohesive
module over (𝒜(X), h). For each α, the restriction M|U_α is a cohesive module over
(𝒜(U_α), h|U_α), and its gauge gauge_{h^{0}_α}(M|U_α) (Z3.b, h|U_α = dh^{0}_α) is a cohesive
module over the flat algebra 𝒜(U_α). The comparison Tot(M|V) → Tot(gauge_{h^{0}_α}(M|U_α)|V),
V ⊆ U_α, intertwines 𝕏 − h^{0}_α with the operator of the gauged module, and the component
complex J_T(M)_α on the over-site of U_α is isomorphic to α_{U_α}(gauge_{h^{0}_α}(M|U_α)) (C1).

## Z3.p — Image of J
Let X be a compact Hausdorff complex manifold modelled on a finite-dimensional complex normed
space E.
- For pre-resolving data, opens U′ ⊆ U and a cohesive module N over 𝒜(U), α_U(N)|U′ ≅
  α_{U′}(N|U′) as complexes on the over-site of U′.
- For every open U and every cohesive module N over 𝒜_X(U), α_U(N) is perfect on U.
- For a closed h ∈ 𝒜^{0,2}(X), a twist datum T for h and a cohesive module M over
  (𝒜_X(X), ∂̄, h), the complex J_T(M) is twisted perfect.

## Z3.q — C3 curved
Let S be sheaf data on X (possibly curved, curvature c) and M₁, M₂ cohesive modules over 𝒜(X).
The *Hom complex of sheaves* ℋ(M₁, M₂) is the complex of sheaves of O-modules whose degree-n
sections over V are the degree-n maps χ : Tot(M₁) → Tot(M₂|V) with
χ(a·x) = (−1)^{n|a|} a|V·χ(x), with differential δχ = 𝕏₂ ∘ χ − (−1)^n χ ∘ 𝕏₁; δ^2 = 0 because
𝕏₁^2 and 𝕏₂^2 are both multiplication by c. Its global sections are Hom^•_{P_A}(M₁, M₂) (a
bijection compatible with δ), and if X is compact Hausdorff its terms are soft.

## Z3.r — `𝓗om^tw`
Let R be a sheaf of commutative rings on X, (U_α) a cover of X, ȟ a family of units with
ȟ_αβα = 1, and K, L complexes of ȟ-twisted sheaves.
- For twisted sheaves K, L, the Hom sheaves Hom(K_α, L_α) with gluing s ↦ φ^L_αβ ∘ s ∘ φ^K_βα
  form a twisted sheaf with trivial cocycle; its gluing has global sections Hom(K, L).
- 𝓗om^tw(K, L) is the complex of sheaves of R-modules on X with
  𝓗om^tw(K, L)^n = ∏_{p+n=q} glue(Hom(K^p, L^q)), Mathlib's sign for the differential.
- For V ⊆ U_α, 𝓗om^tw(K, L)|V ≅ 𝓗om(K_α|V, L_α|V) as complexes on the over-site of V, and
  morphisms of sheaves on X agreeing on every U_α agree.

## Z3.s — Full faithfulness
Let D be resolving data (C0) on a compact Hausdorff space X satisfying the local gauge lemma over
every open (LL_open: each cohesive module over 𝒜(U₀) is near each x ∈ U₀ isomorphic to
𝒜(U′) ⊗_{O(U′)} W, W bounded finitely generated projective). Let h ∈ 𝒜(X)^2 be closed and T a
twist datum for h. Then:
- there is a morphism of complexes Ψ^tw : ℋ^h(M₁, M₂) → 𝓗om^tw(J_T M₁, J_T M₂), which on global
  sections sends a closed degree-0 map φ to J_T(φ), and becomes a quasi-isomorphism after
  composing with a bounded below injective resolution of J_T(M₂);
- J_T : Ho(P_{(𝒜(X), h)}) ⥤ D(TwMod(O, U, ȟ)) is bijective on morphisms.
For the Dolbeault data of a compact Hausdorff complex manifold LL_open holds, so J_T is full and
faithful for every closed h ∈ 𝒜^{0,2}(X) and every twist datum T.

## Z3.t — Curved model
Let P be pre-resolving data on X, h ∈ 𝒜(X)^2 closed, T a twist datum for h and K′ a complex of
ȟ-twisted O-modules.
- The cocycle ρ(ȟ) of 𝒜^0-units, rescaled by u^{−1}, is trivial; hence
  untwist(M) = glue(rescale_{u^{−1}}(𝒜^0 ⊗ M)) is a sheaf of 𝒜^0-modules on X with
  untwist(M)|U_α ≅ 𝒜^0|U_α ⊗ M_α, whose sections are determined by their components, which
  satisfy s_β = u_αβ^{−1}·φ_αβ(s_α).
- For X compact and connections θ_α on 𝒜^0|U_α ⊗ K′_α (C7), the differentials of the local models
  commute with the gluing, giving a twisted model complex of K′.
- For F = untwist(K′), the maps Tot(𝒜(X), F(X)) → Tot(𝒜(U_α), F_α(U_α)) jointly determine
  elements, and there is a curved operator θ^h with (θ^h)^2 = h restricting to θ_α + h^{0}_α.

## Z3.u — Essential surjectivity
Let D be resolving data on a compact space X, h ∈ 𝒜(X)^2 closed and T a twist datum for h. Then
every object K of D(TwMod(O, U, ȟ)) in D_{perf}(X, ȟ) is isomorphic to J_T(M) for some M in
Ho(P_{(𝒜(X), h)}). Steps proved on the way:
- every twisted perfect complex receives a quasi-isomorphism from a strictly bounded above
  complex K′ with componentwise flat terms, whose components K′_α are then K-flat;
- for such K′ (over pre-resolving data), F = untwist(K′) satisfies F|U_α ≅ 𝒜^0|U_α ⊗ K′_α and is
  a perfect complex of 𝒜^0-modules on X;
- base change along R → S of a bounded above flat complex preserves the existence of local roofs
  to strictly perfect complexes.

Deviation: K-flat variant (no flatness of 𝒜 over O assumed); X is not assumed Hausdorff here.

## Z3.v — Main theorem twisted
Let E be a finite-dimensional complex normed space and X a compact Hausdorff complex manifold
modelled on E. Let h ∈ 𝒜^{0,2}(X) be ∂̄-closed, A = (𝒜_X(X), ∂̄, h) the curved Dolbeault algebra
and T a twist datum for h with cover (U_α) and cocycle ȟ. Then the functor
J_T : Ho(P_A) ⥤ D(TwMod(O_X, U, ȟ)), M ↦ J_T(M), into the derived category of ȟ-twisted sheaves
of O_X-modules is full and faithful, and its essential image is exactly D_{perf}(X, ȟ) (the
essential image statement holds for any choice of derived category).

Deviation: stated for each twist datum T (independence of T is not proved); D_{perf} instead of
D^b_{coh}; twisted O_X-modules only, curvature c = h for left modules, no factor 2πi.
