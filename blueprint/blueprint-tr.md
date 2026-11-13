# Blueprint: triangulated structure on Ho(P_A) (Z2) and the Dolbeault check K4

*As of 2026-11-01. DRAFT; needs approval (blueprint.md §11, v1.16 DRAFT).*

## Overview

**Targets.**
- **Z2.** For every bounded graded-commutative curved dga `𝒜` (the project's `GCDga`, curvature
  `c` allowed), `HoP 𝒜` gets:
  - a shift `HasShift (HoP 𝒜) ℤ`;
  - a zero object;
  - `Pretriangulated (HoP 𝒜)`, with distinguished triangles those isomorphic to cone triangles;
  - `IsTriangulated (HoP 𝒜)` (octahedron).

  This is [B, Prop 2.4.1]: "P_A is pretriangulated in the sense of Bondal–Kapranov, so Ho P_A is
  triangulated". Block's proof is the single line "same as Prop 1 and Prop 2 of [BK]".
- **K4** (blueprint §9, original form). For the unit module `𝒜` over the Dolbeault algebra
  (`Q = 𝒜⁰` in degree 0, `𝕏 = ∂̄`): `Hom_{HoP}(𝒜, 𝒜⟦k⟧) ≅ H^{0,k}_∂̄(X)` as ℂ-vector spaces,
  for every `k : ℤ`. Both sides vanish for `k < 0` and `k > dim X`.

**Route** (research of 1 Nov 2026). Direct construction on `HoP`, imitating Mathlib's
`HomotopyCategory` files: `Shift` (320 lines), `MappingCone` (671), `Pretriangulated` (534) and
`Triangulated` (229). The other options fail:
- Mathlib has no dg-categories or dg-modules.
- The total-complex functor is not full, and curvature rules out ordinary complexes.
- Transport along `J : HoP ≅ D_perf` only works for the Dolbeault algebra, needs the main
  theorem, and gives a non-canonical shift. K4 would then not be a check of the shift.

## 1. Sources and audit
- **[B] §2.4** (`references/arXiv-math0509284v2`, l. 386–409):
  - `E[1]^• = E^{•+1}` with `𝔼[1] = −𝔼`, "easy to verify";
  - the cone `Cone(φ)^• = F^• ⊕ E[1]^•` with `ℂ_φ = [[𝔽, φ],[0, 𝔼[1]]]`;
  - the triangle `E → F → Cone(φ) → E[1]`, with the last two maps not written out.
- **Audit.**
  - **Shift sign.** `𝔼[1] = −𝔼` is for Block's *right* modules. In our left-module encoding,
    `−𝕏` breaks the Leibniz rule (already noted in conventions §2, v1.9). The correct shift is
    transported along the sign isomorphism below.
  - **Missing data.** Block gives no third map of the triangle and none of the homotopies needed
    for the axioms. We take them from Mathlib's `MappingCone`/`Pretriangulated`, translated into
    our Hom calculus. The signs below are checked against Mathlib's `δ_inl`, `δ_snd`.
- **[BK]** Bondal–Kapranov, *Enhanced triangulated categories* (1990), Props 1–2. These are
  standard; the formal proof follows Mathlib, not [BK].

## 2. Definitions and signs (left modules, `Tot = A ⊗_{A⁰} ⊕_p Q^p`)

Membership in `Hom^n`: `φ(α·x) = (−1)^{n|α|} α·φ(x)`. Differential:
`δφ = 𝕏 ∘ φ − (−1)^n φ ∘ 𝕏` (A4, equal to Mathlib's `HomComplex.δ` by A4.d).

- **Shift.**
  - `Q[a]^p := Q^{p+a}`.
  - `ι_a : Tot(Q[a]) → Tot(Q)`, `α ⊗ e ↦ (−1)^{a|α|} α ⊗ e` (`GCDga.twist a` ⊗ reindexing by
    `Equiv.addRight a`). It is bijective and lies in `Hom^{a}`: an element of degree `m` goes to
    degree `m + a`, and `ι_a(β x) = (−1)^{a|β|} β ι_a(x)`.
  - `𝕏[a] := (−1)^a ι_a⁻¹ ∘ 𝕏 ∘ ι_a`. Checks:
    - Leibniz: `ι_a⁻¹(dβ · y) = (−1)^{a(|β|+1)} dβ ι_a⁻¹ y`; the signs cancel to
      `𝕏[a](βx) = dβ·x + (−1)^{|β|} β 𝕏[a]x`.
    - Flatness: `𝕏[a]² = ι⁻¹ c ι = c`, since `c` has even degree.
    - On generators: `𝕏[a]^j = (−1)^{a(j+1)} 𝕏^j`, consistent with Mathlib's `n.negOnePow` on
      differentials.
  - Generic lemma (Z2.a): if `u : Tot' → Tot` is bijective, `u ∈ Hom^m` (semilinear of degree
    `m`), and `𝕏` is a cohesive operator, then `(−1)^m u⁻¹ 𝕏 u` is one. This is cleaner than going
    through `GenData`.
  - Morphisms: `φ ↦ ι_a⁻¹ φ ι_a`, with `δ(ι⁻¹hι) = (−1)^a ι⁻¹(δh)ι`, so boundaries go to
    boundaries.
  - `M[a][b] ≅ M[a+b]` is the identity on generators up to reindexing; the signs agree
    (`(−1)^{(a+b)(j+1)}`).
- **Cone of `φ ∈ Z0(M, N)`.**
  - `Q_C^p := Q_N^p × Q_M^{p+1}`.
  - Structure maps, all A-semilinear and defined on generators via `homEquivGen` (A4.c):
    `inl ∈ Hom^{−1}(M, C)`, `inr ∈ Hom^0(N, C)`, `fst ∈ Hom^1(C, M)`, `snd ∈ Hom^0(C, N)`.
  - Identities: `fst∘inl = id`, `snd∘inr = id`, `fst∘inr = 0`, `snd∘inl = 0`,
    `inl∘fst + inr∘snd = id`.
  - Operator: `𝕏_C := inr 𝕏_N snd + inr φ fst − inl 𝕏_M fst`. On `inr f + inl e` this is Block's
    matrix. Flatness from those of `M`, `N` and `δφ = 0`.
  - Then `δ(inl) = inr ∘ φ`, `δ(inr) = 0`, `δ(fst) = 0`, `δ(snd) = −φ ∘ fst` (Mathlib's
    `δ_inl`, `δ_snd`).
- **Triangle.** `M →φ N →inr C(φ) →(−ι₁⁻¹∘fst) M⟦1⟧`, where `ι₁⁻¹ ∘ fst ∈ Z0(C, M[1])`. This is
  Mathlib's `Cocycle.homOf ((-fst φ).rightShift 1 0 _)`.

## 3. Proof plan (following Mathlib)
- **Pretriangulated** (fields of `CategoryTheory.Pretriangulated`):
  - `isomorphic_distinguished`: by definition.
  - `contractible_distinguished`: `C(id_M)` is contractible, with homotopy `inl ∘ snd`
    (Mathlib `homotopyToZeroOfId`).
  - `distinguished_cocone_triangle`: the cone triangle.
  - `rotate_distinguished_triangle`: `C(inr) ≃ M[1]` (homotopy equivalence; Mathlib
    `rotateHomotopyEquiv`). The inverse rotation follows generically
    (`invRotateIsoRotateRotateShiftFunctorNegOne`). Needs `C(φ)⟦n⟧ ≅ C(φ⟦n⟧)` (Mathlib
    `shiftTrianglehIso`).
  - `complete_distinguished_triangle_morphism`: map of cones from a homotopy-commutative square
    (Mathlib `mapOfHomotopy`).
- **Octahedron:** `C(g) ≃ C(C(f) → C(gf))` (Mathlib `mappingConeCompHomotopyEquiv`), then
  `IsTriangulated` as in Mathlib `Triangulated.lean`.
- **Advantage of our encoding.** Identities between maps are `LinearMap` equalities, proved on
  generators with `simp [comp_add, add_comp, comp_assoc, …]`. There is no degreewise `ext` as in
  Mathlib's cochains.

### 3a. Additions from the external audit (blueprint §11 v1.18, approved 2 Nov 2026)
- **Signs pinned to Mathlib before Z2.d.** `#check`/`#print` the pinned
  `CochainComplex.mappingCone.triangle`, `triangleδ`, `inr_triangleδ` and
  `Pretriangulated.Triangle.rotate` (Mathlib names unverified here), and state the cone triangle
  of `HoP` with exactly those signs. Changing the sign of the third map alone is not an
  isomorphism of triangles (no `(a, b, c) ∈ {±1}³` fixes `u`, `v` and flips `w`), so a mismatch
  would make a later `J.IsTriangulated` (Z2.h) false while `Pretriangulated (HoP 𝒜)` still holds.
  Record the checked signs in `Scratch/P14_TR.lean` (§7) before the skeleton.
- **`Tot.prodEquiv` first (Z2.c).** A `k`-linear (in fact `A`-linear) isomorphism
  `Tot 𝒜 (fun p ↦ Q₁ p × Q₂ p) ≃ Tot 𝒜 Q₁ × Tot 𝒜 Q₂` (direct sum of a product family is the
  product of the direct sums; the tensor product distributes), with `rfl`/`simp` lemmas on pure
  tensors and on `totDeg`. Then the cone's `inl`, `inr`, `fst`, `snd` (§2) are
  `LinearMap.inl/inr/fst/snd` transported along it, `𝕏_C` is a 2×2 matrix of operators, and the
  five identities, flatness and the `δ` formulas are `LinearMap.ext` + `simp` instead of
  generator-level inductions. The same isomorphism gives the zero object and biproducts. This
  replaces the risk "Cone generators" of §6.
- **Optional sanity for Z2.h.** `J(cone φ) ≅ mappingCone (J φ)` in `K(Mod O_X)` for closed `φ`,
  on sections; cheap once `Tot.prodEquiv` exists; the only real risk to `J.IsTriangulated`.

### 3b. Templates for Z2.d–g (reuse search 2 Nov 2026; Z2.d–g deferred with v1.19)
No generic "dg category with shifts and cones ⇒ triangulated H⁰" exists in Mathlib or TauCeti;
TauCeti's routes (Bondal–Kapranov envelope, Frobenius/Happel) would be 10–28k-line ports. Direct
route kept, with these templates:
- **TauCeti** (Apache-2.0, copy with attribution; Lean 4.36-rc2, module system, so back-port):
  `CategoryTheory/DG/Twisted/Cone.lean` (537 lines), `Triangle.lean` (837),
  `Pretriangulated.lean` (226), `Triangulated.lean` (712). They prove the axioms in an
  elementwise dg-Hom calculus (`dgComp`, `dgDifferential`, no degreewise `ext`), close to our
  `LinearMap` encoding. Names to follow: `coneTriangle` (Triangle.lean:116),
  `coneHomOfHomotopy` (:169), `exists_coneTriangle_hom` (:433),
  `coneRotateHom`/`coneRotateInv`/`coneRotateIso` (:464–702), `coneTriangleShiftIso`,
  `coneCompHom`/`coneCompInv`/`coneCompTriangle`. Small helpers worth copying:
  `isoNegThird` (`CategoryTheory/Triangulated/Signs.lean:27`), `distinguished_mk_of_iso`,
  `distinguished_mk_of_iso₁` (`Triangulated/TriangleIso.lean:39, 48`).
- **Mathlib (pin)**: `IsTriangulated.mk'` (`CategoryTheory/Triangulated/Triangulated.lean:371`,
  octahedron up to isomorphic diagrams; the tool for Z2.g, as TauCeti uses it);
  `invRotateIsoRotateRotateShiftFunctorNegOne` (`TriangleShift.lean:139`),
  `distinguished_iff_of_iso` (`Pretriangulated.lean:98`); the copied `HomotopyCategory` files
  (`MappingCone` 671, `Pretriangulated` 534, `Triangulated` 229 lines; `mappingConeCompTriangle`
  :38, `mappingConeCompHomotopyEquiv` :137).
- Z2.d–g must stay generic in `GCDga` (no `c_eq_zero`), so they apply to the curved `HoP` of Z3.

### 3c. Z2.f detail (6 Nov 2026; approved at gate 14, blueprint §11 v1.21)
Notation: `ι_a : Tot(M[a]) → Tot(M)` (Z2.a, `Hom^a`, closed), `w_φ := −ι₁⁻¹ ∘ fst ∈ Z⁰(C(φ), M[1])`
(P14: Mathlib's `triangle φ`.mor₃ with no extra sign on generators), `f[a] := ι_a⁻¹ f ι_a`
(`conjZ0`, the shift on morphisms, Z2.b). Primes denote the structure maps of `C(inr_φ)`.
Mathlib's `leftShift` signs (`(a n' + a(a−1)/2)`) are absorbed into these formulas.
- **Triangle and set** (`Algebra/ConeTriangle.lean`, Z2.f1). `coneTriangle φ := (M →[φ] N →[inr] C(φ) →[w_φ] M⟦1⟧)`;
  distinguished = isomorphic to some `coneTriangle φ` (`φ ∈ Z⁰`, representatives in `HoP`).
  - contractible: `C(id_M)` is zero: `δ(inl ∘ snd) = id` (`δ inl ∘ snd − inl ∘ δ snd = inr snd + inl fst`),
    `isZero_of_contraction`;
  - cocone: choose a representative of `f`;
  - morphisms: a square commuting in `HoP` gives `h ∈ Hom^{−1}` with `δh = bφ₁ − φ₂a` (`B⁰`); `coneMap`
    (Z2.e); `a[1] ∘ w₁ = w₂ ∘ coneMap` exactly (`fst₂ ∘ coneMap = a ∘ fst₁`).
- **Rotation** (`Algebra/ConeRotate.lean`, Z2.f2; Mathlib `rotateHomotopyEquiv`).
  `hom := coneLift inr_φ (φ ∘ ι₁) (−inl ∘ ι₁) : M[1] → C(inr_φ)` (`δ(−inl ι₁) = −inr φ ι₁`),
  `inv := coneDesc inr_φ 0 w_φ : C(inr_φ) → M[1]`; `inv ∘ hom = id` exactly, `hom ∘ inv − id = δ H` with
  `H := −inl' ∘ snd_φ ∘ snd'`. Triangle iso `(coneTriangle φ).rotate ≅ coneTriangle inr_φ` with
  components `(id, id, [hom])`: `w' ∘ hom = −φ[1]` exactly (`fst' ∘ hom = φ ι₁`), and
  `hom ∘ w_φ − inr' = δ H₂`, `H₂ := −inl' ∘ snd_φ`.
- **Shift** (`Algebra/ConeShift.lean`, Z2.f3; Mathlib `shiftIso`, `shiftTriangleIso`).
  `C(φ)[n] ≅ C(φ[n])`: `hom := coneLift φ[n] ((−1)^n ι_n⁻¹ fst ι_n) (ι_n⁻¹ snd ι_n)`,
  `inv := coneDesc φ[n] ((−1)^n ι_n⁻¹ inl ι_n) (ι_n⁻¹ inr ι_n)`, inverse exactly; triangle iso
  `(Triangle.shiftFunctor n).obj (coneTriangle φ) ≅ coneTriangle φ[n]` with components
  `(id, (−1)^n, shiftIso)`; the third square involves `shiftFunctorComm` of `HoP` (Z2.b's
  `shiftFunctorAdd`), the main risk.
- **Instance** (`Algebra/Pretriangulated.lean`): as Mathlib, `invRotate` via
  `invRotateIsoRotateRotateShiftFunctorNegOne` and shift-closure.

### 3d. Z2.g detail (6 Nov 2026; approved at gate 14, blueprint §11 v1.21)
Mathlib `HomotopyCategory/Triangulated.lean` (`mappingConeCompTriangle`,
`mappingConeCompHomotopyEquiv`, `IsTriangulated.mk'`). For `u ∈ Z⁰(X₁, X₂)`, `v ∈ Z⁰(X₂, X₃)`,
`uv := v ∘ u`. Conventions as in §3c (`δ inl = inr φ`, `δ snd = −φ fst`, `δ fst = δ inr = 0`,
`δ(f∘g) = δf∘g + (−1)^{|f|} f∘δg`).
- **Comparison maps** (`Algebra/ConeComp.lean`). `m₁ := coneMap u uv id v 0 : C(u) → C(uv)`,
  `m₂ := coneMap uv v u id 0 : C(uv) → C(v)` (homotopy `0`: `v∘u − uv∘id = 0`, `id∘uv − v∘u = 0`).
  Triangle `C(u) →[m₁] C(uv) →[m₂] C(v) →[w_v ≫ inr_u⟦1⟧] C(u)⟦1⟧`.
- **Homotopy equivalence** `C(v) ≃ C(m₁) =: D`.
  `hom := coneLift m₁ (inr_u ∘ fst_v) (inr_{uv} ∘ snd_v)`
  (`δ(inr_{uv} snd_v) = −inr_{uv} v fst_v = −m₁ inr_u fst_v` by `m₁ inr_u = inr_{uv} v`);
  `inv := coneDesc m₁ (inl_v ∘ snd_u) m₂`
  (`δ(inl_v snd_u) = inr_v v snd_u + inl_v u fst_u = m₂ ∘ m₁`, using `m₁ = inl_{uv} fst_u + inr_{uv} v snd_u`).
  `inv ∘ hom = id` exactly (`fst_v inl_v = id`, `snd_v m₂ = snd_{uv}`); `hom ∘ inv − id = δH` with
  `H := −inl_D ∘ inl_u ∘ fst_{uv} ∘ snd_D` (checked by hand: with `K = inl_u fst_{uv} snd_D`,
  `δ(inl_D K) = inr_D inl_{uv} fst_{uv} snd_D − inl_D inr_u u fst_{uv} snd_D + inl_D inl_u fst_u fst_D`,
  which is `−(hom ∘ inv − id)` after expanding `id_D`, `id_{C(u)}`, `id_{C(uv)}`).
- **Distinguished.** Triangle iso `(id, id, [hom])` to `coneTriangle m₁`: `inv ∘ inr_D = m₂` exactly
  (so `m₂ ≫ [hom] = [inr_D]` in `HoP`), and `w_D ∘ hom = −ι₁⁻¹ inr_u fst_v = inr_u[1] ∘ w_v` exactly.
- **Octahedron** (`Algebra/Triangulated.lean`). `IsTriangulated.mk'` with the three cone triangles
  of `u`, `v`, `uv`, `Iso.refl`s, and `Octahedron.mk [m₁] [m₂]`: `m₁ inr_u = inr_{uv} v`,
  `w_{uv} m₁ = w_u` (`fst m₁ = fst`), `m₂ inr_{uv} = inr_v`, `u[1] w_{uv} = w_v m₂`
  (`fst_v m₂ = u fst_{uv}`), all exact; the last field is the distinguished triangle above.

## 4. K4
- **(i) Generic** (model: Mathlib `HomComplexCohomology.homAddEquiv`).
  `Hom_{HoP}(M, N⟦k⟧) ≅ H^k(Hom^•(M,N))` via `φ ↦ ι_k ∘ φ`, since `δ(ι_k ∘ φ) = ± ι_k ∘ δφ`.
  The cohomology is the quotient `(Hom^k ⊓ ker δ) ⧸ δ(Hom^{k−1})` (like `H0`), or the homology
  of A6's `homComplex`.
- **(ii) Unit module.** `Hom^k(U, U) ≅ 𝒜^k` by evaluation at `1 ⊗ gen` (`homEquivGen`,
  `hom_tmul`), with `δ ↔ d` and no sign (`θ(gen) = 0`). `unitCohesive` exists in
  `ChecksAlgebra.lean:338`; move it to a library file (it is not frozen).
- **(iii) Dolbeault.** Define `H^k(𝒜, d) := (𝒜^k ⊓ ker d) ⧸ d(𝒜^m)` with `m + 1 = k` (ℤ-indexed,
  no ℕ subtraction) and `H^{0,k}_∂̄(X) :=` that for `dolbeault E X` (`d = dbarL`).
  `K4 : ((⟨unitCohesive (dolbeault E X) rfl⟩ : HoP _) ⟶ (⟨…⟩ : HoP _)⟦k⟧) ≃ₗ[ℂ] H^{0,k}_∂̄(X)`.
  Sanity: both sides are `0` for `k < 0` and `k > n`. For `k = 0` it is `O(X)` (F12).

## 5. Items, files, estimates (new files only; no FROZEN changes)

| Item | File | Content | Est. lines |
| --- | --- | --- | --- |
| Z2.a | `Algebra/Shift.lean` | `ι_a`, generic transport lemma, `CohesiveModule.shift` | 250–350 |
| Z2.b | `Algebra/ShiftHoP.lean` | shift on `Hom`/`Z0`/`H0`, `HasShift (HoP 𝒜) ℤ` (`hasShiftMk`), additivity, `k`-linearity | 300–450 |
| K4.a | `Algebra/HomShift.lean` | `Hom_{HoP}(M, N⟦k⟧) ≃ₗ H^k(Hom^•(M,N))` | 100–150 |
| K4.b | `Algebra/UnitModule.lean`, `ChecksMain`/`ChecksForms` | unit module, `Hom^•(U,U) ≅ (𝒜, d)`, Dolbeault cohomology, K4 | 200–350 |
| Z2.c | `Algebra/TotProd.lean`, `Algebra/HoPZero.lean` | `Tot.prodEquiv` (v1.18, below), zero object | 100–200 |
| Z2.d | `Algebra/Cone.lean` | cone, structure maps, identities, `δ` formulas | 350–500 |
| Z2.e | `Algebra/ConeMaps.lean` | `lift`/`desc`, maps of cones from homotopies | 200–300 |
| Z2.f | `Algebra/Pretriangulated.lean` | the pretriangulated axioms, shift of cones | 400–600 |
| Z2.g | `Algebra/Triangulated.lean` | octahedron, `IsTriangulated` | 250–400 |

Total: Z2 core ≈ 1,800–2,700 lines, K4 ≈ 300–500 lines. Order: Z2.a → Z2.b → K4, which needs no
cones, then Z2.c–g. This can run in parallel with Z5 (disjoint files: Algebra layer vs Analysis
and Forms).

Optional, not proposed now: Z2.h, `J.CommShift` and `J.IsTriangulated`. With them `Perf = J.essImage`
is triangulated by Mathlib's `essImage` instance (+400–700 lines).

## 6. Risks
- **Coherence of `HasShift`** (`M[a][b] ≅ M[a+b]`, `zero_add`, `assoc`). This is dependent-type
  reindexing of `Q (p + a + b)` vs `Q (p + (a + b))`. Use a `reindex (h : f = g)` family with
  `subst`, as Mathlib's `XIsoOfEq`.
- **Cone generators.** `⨁ (Q_N × Q_M[1])` is not a type-level biproduct of the `Tot`s, so the five
  identities need generator-level proofs (`homEquivGen`).
- **Base-change elaboration traps** (PROGRESS) do not arise here; `HoP` is over a fixed `𝒜`.

## 7. Lean targets (to be compiled in `Scratch/P14_TR.lean` before skeletons)
```lean
def CohesiveModule.shift (M : CohesiveModule 𝒜) (a : ℤ) : CohesiveModule 𝒜
instance : HasShift (HoP 𝒜) ℤ
instance : HasZeroObject (HoP 𝒜)
instance (n : ℤ) : (shiftFunctor (HoP 𝒜) n).Additive
instance : Pretriangulated (HoP 𝒜)
instance : IsTriangulated (HoP 𝒜)
def homShiftEquiv (M N : HoP 𝒜) (k : ℤ) : (M ⟶ N⟦k⟧) ≃ₗ[k] HomCohomology M.as N.as k
def dolbeaultCohomology (k : ℤ) : Type
theorem K4 (k : ℤ) : Nonempty ((unitHoP (dolbeault E X) ⟶ (unitHoP (dolbeault E X))⟦k⟧) ≃ₗ[ℂ]
    dolbeaultCohomology E X k)
```
