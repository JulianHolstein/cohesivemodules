import Cohesivemodules.Algebra.Triangulated
import Cohesivemodules.Forms.DolbeaultCohomology

set_option linter.style.header false

/-!
# The triangulated structure on `Ho(P_A)`

This page is an overview of the triangulated structure on the homotopy category of cohesive
modules (blueprint item Z2, sub-items Z2.a–g) and of the check K4. It contains no declarations;
the links below point to the files where the definitions and theorems live.

## Overview

[[B][Block], Prop 2.4.1] says that `P_A` is pretriangulated in the sense of Bondal–Kapranov, so that
`Ho(P_A)` is triangulated. Block's proof is one line ("The proof of this is the same as that of
Proposition 1 and Proposition 2 of [[BK][BondalKapranov]]"). It gives only the shift `E[1]` and
the cone
`C(φ) = F ⊕ E[1]`, leaves the last two maps of the cone triangle unspecified, and omits the
homotopies needed for the axioms. This project builds the structure directly on
`Cohesive.HoP`, imitating Mathlib's `HomotopyCategory` files (`Shift`, `MappingCone`,
`Pretriangulated`, `Triangulated`) and translating their cochain formulas into the Hom calculus
of cohesive modules (*Cohesive modules* hub).

**Not needed for the main results.** Neither the statements nor the proofs of Block's theorem,
its conditional form or the twisted theorem use anything on this page: none of the files listed
under "Files" is imported by `main_theorem`, `main_theorem_conditional` or
`Cohesive.main_theorem_twisted`. The main theorems are equivalences of categories, and `J` is not
shown to be a triangulated functor (see "Not done" below). The structure is built because
[[B][Block], Prop 2.4.1] states it, and K4 checks the shift against Dolbeault cohomology.

Everything here works over an arbitrary bounded graded-commutative **curved** dga `𝒜`
(`Cohesive.GCDga`, curvature `c` allowed), so the same instances also apply to the curved `HoP`
of the twisted theorem (*Twisted theorem* hub); the twisted theorem itself does not use them.
Only K4 needs `c = 0`, because it uses the unit module.

* **Shift** (Z2.a–b). `M[a]` has generators `Q^{p+a}` and the operator transported along a sign
  isomorphism `ι_a`. This gives `HasShift (HoP 𝒜) ℤ`, with additive and `k`-linear shift
  functors.
* **Zero object** (Z2.c). The module with all `Q^p = 0` gives `HasZeroObject (HoP 𝒜)`.
* **Cone** (Z2.d–e). For a closed degree-`0` map `φ : M → N`, the cone `C(φ)` has generators
  `Q_N^p × Q_M^{p+1}`, structure maps `inl`, `inr`, `fst`, `snd`, and maps into, out of and
  between cones.
* **Pretriangulated** (Z2.f). The distinguished triangles are those isomorphic to a cone
  triangle `M → N → C(φ) → M⟦1⟧`.
* **Triangulated** (Z2.g). The octahedron axiom holds, via the cone of a composite.
* **K4** (blueprint §9). `Hom_{Ho(P_A)}(M, N⟦n⟧)` is the `n`-th cohomology of the Hom complex.
  For the unit module of the Dolbeault algebra this is `H^{0,n}_∂̄(X)`. This checks the shift of
  Z2.b: with it, `Hom(U, U⟦n⟧)` is the expected Dolbeault cohomology in every degree.

## Main definitions

* `Cohesive.shiftIota`: the sign isomorphism `ι_a : Tot(Q[a]) ≃ Tot(Q)` (Z2.a).
* `Cohesive.CohesiveModule.shift`: the shift `M[a]` of a cohesive module (Z2.a), built with the
  generic transport `Cohesive.QuasiCohesive.transport`.
* `Cohesive.shiftFunctorHoP`, `Cohesive.shiftMkCoreHoP`: the shift functors on `Ho(P_A)` and the
  data of `instance : HasShift (HoP 𝒜) ℤ` (Z2.b).
* `Cohesive.Tot.prodEquiv`: `Tot(Q₁ × Q₂) ≃ₗ[A] Tot Q₁ × Tot Q₂` (Z2.c); `Cohesive.zeroHoP`: the
  zero object (Z2.c).
* `Cohesive.cone`: the cone `C(φ)` (Z2.d), with `Cohesive.coneInl`, `Cohesive.coneInr`,
  `Cohesive.coneFst`, `Cohesive.coneSnd` and operator `Cohesive.coneX`.
* `Cohesive.coneDesc`, `Cohesive.coneLift`, `Cohesive.coneMap`: maps out of, into and between
  cones (Z2.e).
* `Cohesive.coneW`, `Cohesive.coneTriangle`, `Cohesive.distinguishedTriangles`: the third map,
  the cone triangle and the class of distinguished triangles (Z2.f).
* `Cohesive.HomCohomology`: the cohomology `Zⁿ / Bⁿ` of the Hom complex (K4.a).
* `Cohesive.unitCohesive`, `Cohesive.unitHoP`: the unit module `U = 𝒜` (`Q⁰ = A⁰`, `𝕏 = d`;
  needs `c = 0`); `Cohesive.DgaCohomology`: the cohomology of `(𝒜, d)` (K4.b).
* `Cohesive.dolbeaultCohomology`: `H^{0,n}_∂̄(X)`; `Cohesive.dolbeaultUnit`: the unit module of
  the Dolbeault algebra in `Ho(P_A)` (K4.b).

## Main results

* `instance : Pretriangulated (HoP 𝒜)` (`Algebra/Pretriangulated.lean`, Z2.f4) and
  **`instance : IsTriangulated (HoP 𝒜)`** (`Algebra/Triangulated.lean`, Z2.g2). They hold for
  every `𝒜` with `[GradedAlgebra 𝒜] [GCDga 𝒜]` over a commutative ring `k`; there are no further
  hypotheses (in particular, the curvature `c` is arbitrary).
  `Cohesive.mem_distTriang_iff`: the distinguished
  triangles are exactly `Cohesive.distinguishedTriangles` (`Iff.rfl`).
* `Cohesive.rotateTriangleIso`: `(coneTriangle φ).rotate ≅ coneTriangle inr_φ` (Z2.f2).
* `Cohesive.shiftTriangleIso`: the `n`-th shift of `coneTriangle φ` is isomorphic to
  `coneTriangle φ[n]` (Z2.f3).
* `Cohesive.compTriangle_distinguished`: for closed `u : X₁ → X₂`, `v : X₂ → X₃`, the triangle
  `C(u) → C(v ∘ u) → C(v) → C(u)⟦1⟧` is distinguished (Z2.g1).
* `Cohesive.homShiftEquiv`: `(M ⟶ N⟦n⟧) ≃ₗ[k] HomCohomology M N n`, `[φ] ↦ [ι_n ∘ φ]` (K4.a;
  Mathlib's analogue is `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`).
* `Cohesive.unitShiftEquiv`: for `c = 0`, `(U ⟶ U⟦n⟧) ≃ₗ[k] DgaCohomology 𝒜 n`,
  `[φ] ↦ [(ι_n ∘ φ)(1 ⊗ gen)]` (K4.b).
* **K4**, `Cohesive.k4Equiv`: for any complex manifold `X` (no compactness or Hausdorff
  assumption; the statement is about global forms) and every `n : ℤ`,
  `(dolbeaultUnit E X ⟶ (dolbeaultUnit E X)⟦n⟧) ≃ₗ[ℂ] H^{0,n}_∂̄(X)`. Both sides vanish for
  `n < 0` and `n > dim_ℂ X` (cohomology side:
  `Cohesive.subsingleton_dolbeaultCohomology_of_neg`,
  `Cohesive.subsingleton_dolbeaultCohomology_of_gt`; Hom side: `Cohesive.Checks.K4_of_neg`,
  `Cohesive.Checks.K4_of_gt`). For `n = 0`, `Cohesive.k4ZeroEquiv` is a bijection with `O(X)`
  (F12); it is a bijection of sets only (blueprint §11 v1.18, item 7). The checks
  `Cohesive.Checks.K4` and `Cohesive.Checks.K4_zero` are in `ChecksForms.lean`.

## Conventions and signs

The signs are fixed so that every formula matches Mathlib's `CochainComplex` conventions
(`blueprint/conventions.md` §2, `blueprint/blueprint-tr.md` §2, §3c–§3d; the Mathlib signs were
pinned in `Scratch/P14_TR.lean`). The Hom calculus is that of the *Cohesive modules* hub:
`φ ∈ Hom^n` means that `φ` raises total degree by `n` and `φ(α·x) = (−1)^{n|α|} α·φ(x)`,
and `δφ = 𝕏 ∘ φ − (−1)^n φ ∘ 𝕏`, so that
`δ(f ∘ g) = δf ∘ g + (−1)^{|f|} f ∘ δg`.

**Shift of a cohesive module** (`Cohesive.CohesiveModule.shift`).
* Generators: `Q[a]^p = Q^{p+a}` (`Cohesive.shiftQ`), as Mathlib's `(K⟦a⟧).X p = K.X (p + a)`.
* Sign isomorphism: `ι_a : Tot(Q[a]) ≃ Tot(Q)`, `α ⊗ e ↦ (−1)^{a|α|} α ⊗ e`
  (`Cohesive.shiftIota_tmul`). It has degree `a`: total degree `m` goes to `m + a`
  (`Cohesive.shiftIota_mem_totDeg_iff`) and `ι_a(β x) = (−1)^{a|β|} β ι_a(x)`
  (`Cohesive.shiftIota_smul`).
* Operator: `𝕏[a] = (−1)^a ι_a⁻¹ ∘ 𝕏 ∘ ι_a` (`Cohesive.CohesiveModule.shift_X`). On generators
  this is `𝕏[a]^j = (−1)^{a(j+1)} 𝕏^j`. So `𝕏[a]⁰ = (−1)^a 𝕏⁰`, which is Mathlib's shift of a
  cochain complex (`CochainComplex.shiftFunctor_obj_d'`: the differential is multiplied by
  `a.negOnePow`), and `𝕏[a]¹ = 𝕏¹` for every `a`, so the connection stays a connection.
* `ι_a ∈ Hom^a(M[a], M)` is closed (`Cohesive.shiftIota_mem_hom`, `Cohesive.δ_shiftIota`).
* ⚠ [[B][Block], §2.4] writes `𝔼[1] = −𝔼`. That is correct for Block's right modules. In the
  left-module
  convention, `−𝕏` on `A ⊗ Q[1]` breaks the Leibniz rule (`−∇` is not a connection), so the
  shift is transported along `ι_a` instead (blueprint-tr §1 audit; conventions §2, v1.9).

**Shift on morphisms and the shift functor** (Z2.b).
* `[φ]⟦a⟧ = [φ[a]]` with `φ[a] := ι_a⁻¹ ∘ φ ∘ ι_a` (`Cohesive.conjH0`, `Cohesive.shiftZ0`,
  `Cohesive.shiftFunctorHoP_map_mk`), with no further sign.
  Conjugation satisfies `δ(ι_a⁻¹ h ι_a) = (−1)^a ι_a⁻¹ (δh) ι_a`, so cycles and
  boundaries are preserved.
* On objects, `(M⟦a⟧).as = M.as.shift a` holds by `rfl` (`Cohesive.shiftFunctor_obj_as`).
* Structure isomorphisms. A *shift datum* (`Cohesive.IsShiftData`) is a bijection `v` of degree
  `m` with `𝕏' = (−1)^m v⁻¹ 𝕏 v`. Two shift data of the same degree onto the same module give
  the closed isomorphism `v₂⁻¹ ∘ v₁` (`Cohesive.shiftCompIso`). Then `M[0] ≅ M` comes from
  `(ι_0, id)` (`Cohesive.shiftFunctorZeroHoP`) and `M[a+b] ≅ M[a][b]` from
  `(ι_{a+b}, ι_a ∘ ι_b)` (`Cohesive.shiftFunctorAddHoP`). The latter has no sign on generators,
  since `(−1)^{(a+b)|α|} = (−1)^{a|α|}(−1)^{b|α|}`.
* Morphisms into a shift: `ι_n ∘ − : Hom^m(M, N[n]) ≃ Hom^{m+n}(M, N)`, with
  `δ(ι_n ∘ φ) = (−1)^n ι_n ∘ δφ` (K4.a).

**Cone of `φ ∈ Z⁰(M, N)`** (`Cohesive.cone`; Mathlib's `CochainComplex.mappingCone`).
* Generators `Q_C^p = Q_N^p × Q_M^{p+1}` (`Cohesive.coneQ`). Through `Cohesive.Tot.prodEquiv`
  and `ι₁`, `Tot(C) ≃ₗ[k] Tot(M) × Tot(N)` (`Cohesive.coneEquiv`), and `inl`, `inr`, `fst`, `snd`
  are the coordinate inclusions and projections. The factor `ι₁` gives the degrees:
  `inl ∈ Hom^{−1}(M, C)`, `inr ∈ Hom^0(N, C)`, `fst ∈ Hom^1(C, M)`, `snd ∈ Hom^0(C, N)`.
* Identities: `fst ∘ inl = id`, `snd ∘ inr = id`, `fst ∘ inr = 0`, `snd ∘ inl = 0`,
  `inl ∘ fst + inr ∘ snd = id` (`Cohesive.coneInl_coneFst_add`).
* Operator: `𝕏_C = inr 𝕏_N snd + inr φ fst − inl 𝕏_M fst` (`Cohesive.coneX`). In coordinates,
  `𝕏_C(inl e + inr f) = −inl(𝕏_M e) + inr(φ e + 𝕏_N f)`, which is Mathlib's mapping-cone
  differential (`CochainComplex.mappingCone.d_fst_v`, `CochainComplex.mappingCone.d_snd_v`). In
  the coordinates `(f, e') ∈ Tot(N) × Tot(M[1])`, `e = ι₁ e'`, it is Block's matrix
  `[[𝕏_N, φ ∘ ι₁], [0, 𝕏_M[1]]]`, since `𝕏_M[1] = −ι₁⁻¹ 𝕏_M ι₁`.
* `δ inl = inr ∘ φ`, `δ inr = 0`, `δ fst = 0`, `δ snd = −φ ∘ fst` (`Cohesive.δ_coneInl`,
  `Cohesive.δ_coneSnd`; Mathlib's `CochainComplex.mappingCone.δ_inl`,
  `CochainComplex.mappingCone.δ_snd`).

**Triangles.**
* Cone triangle: `M →[φ] N →[inr] C(φ) →[w_φ] M⟦1⟧` (`Cohesive.coneTriangle`), with
  `w_φ = −ι₁⁻¹ ∘ fst` (`Cohesive.coneW`). This is Mathlib's
  `(CochainComplex.mappingCone.triangle φ).mor₃`, with no extra sign. The sign matters: flipping
  the sign of the third map alone cannot be undone by a triangle isomorphism with components
  `±id`, and the resulting triangle is in general not distinguished (blueprint §11 v1.18).
* Rotation: `(coneTriangle φ).rotate ≅ coneTriangle inr_φ`, where `inr_φ : N → C(φ)` is the
  second map of the cone triangle, with components `(id, id, [rotHom])`,
  `rotHom = lift (φ ∘ ι₁) (−inl ∘ ι₁)`; Mathlib's rotation puts `−φ⟦1⟧` third, and
  `w_{inr_φ} ∘ rotHom = −φ[1]` holds exactly.
* Shift: `C(φ)[n] ≅ C(φ[n])` by `lift ((−1)^n ι_n⁻¹ fst ι_n) (ι_n⁻¹ snd ι_n)`
  (`Cohesive.shiftConeHom`). The triangle isomorphism `Cohesive.shiftTriangleIso` has components
  `(id, (−1)^n, [shiftConeHom])` relative to Mathlib's
  `CategoryTheory.Pretriangulated.Triangle.shiftFunctor`, which multiplies all three maps by
  `(−1)^n` and composes the third with `shiftFunctorComm 1 n`.
* Composite (octahedron): for `uv = v ∘ u`, `m₁ = coneMap u uv id v 0 : C(u) → C(uv)` and
  `m₂ = coneMap uv v u id 0 : C(uv) → C(v)` (`Cohesive.compMor₁`, `Cohesive.compMor₂`), and the
  third map is `w_v ≫ inr_u⟦1⟧`. All four octahedron squares hold exactly on representatives.

## Implementation notes

* **Direct route.** Mathlib has no dg-categories. The total-complex functor is not full, and
  curvature rules out ordinary complexes, so the structure cannot be transported from
  `HomotopyCategory`. Transport along `J` would need the main theorem. The proofs therefore copy
  Mathlib's `HomotopyCategory` files step by step (`CategoryTheory.hasShiftMk`,
  `CategoryTheory.IsTriangulated.mk'`,
  `CategoryTheory.Pretriangulated.invRotateIsoRotateRotateShiftFunctorNegOne`); some names
  (`coneTriangle`, `exists_coneTriangle_hom`) follow the dg-cone files
  `CategoryTheory/DG/Twisted/` of the TauCeti project (blueprint-tr §3b).
* **Identities as `LinearMap` equalities.** Maps are `k`-linear maps of total modules, so
  identities between them are `LinearMap.ext` + `simp`, with no degreewise `ext`. `inl`, `inr`,
  `fst`, `snd` are Mathlib's `LinearMap.inl/inr/fst/snd` transported along `Cohesive.coneEquiv`
  (built from `Cohesive.Tot.prodEquiv` and `ι₁`).
* **Homotopies.** A map of cones from a square commuting in `Ho(P_A)` takes
  `h ∈ Hom^{−1}(M₁, N₂)` with `δh = b ∘ φ₁ − φ₂ ∘ a` (Mathlib's `Homotopy (φ₁ ≫ b) (a ≫ φ₂)`)
  and is `desc (inl₂ ∘ a + inr₂ ∘ h) (inr₂ ∘ b)` (`Cohesive.coneMap`). The homotopy equivalences
  `Cohesive.rotHom`/`Cohesive.rotInv` and `Cohesive.compHom`/`Cohesive.compInv` have
  `inv ∘ hom = id` exactly and `hom ∘ inv − id = δH` for an explicit `H`.
* **Contractible triangles.** `C(id_M)` is zero because `δ(inl ∘ snd) = id`
  (`Cohesive.isZero_of_contraction`).
* **Not done.** `J` is not shown to commute with shifts or to be a triangulated functor
  (`J.CommShift`, `J.IsTriangulated`: optional item Z2.h in blueprint-tr §5, not proposed). The
  main theorems do not use the structure on this page.
* **Not frozen.** The instances on `HoP` are not part of the term-dependency closure of the main
  statements (blueprint §11 v1.18, item 1), so none of these files are frozen;
  `Algebra/Shift.lean` and `Algebra/ShiftHoP.lean` were unfrozen by that decision.
* ⚠ The blueprint's single file `Algebra/UnitModule.lean` (K4.b) is split into
  `Algebra/UnitModule.lean`, `Algebra/UnitCohomology.lean` (generic dga, `c = 0`) and
  `Forms/DolbeaultCohomology.lean`. Cohomology is `ℤ`-indexed, `Bⁿ = d(𝒜^{n−1})` with integer
  subtraction. The blueprint's `Algebra/Pretriangulated.lean` (Z2.f) and
  `Algebra/Triangulated.lean` (Z2.g) are split for size into the files listed below.

## Files

* `Algebra/Shift.lean` (Z2.a), `Algebra/ShiftHoP.lean` (Z2.b).
* `Algebra/HomShift.lean` (K4.a); `Algebra/UnitModule.lean`, `Algebra/UnitCohomology.lean`,
  `Forms/DolbeaultCohomology.lean` (K4.b).
* `Algebra/TotProd.lean`, `Algebra/HoPZero.lean` (Z2.c).
* `Algebra/Cone.lean` (Z2.d), `Algebra/ConeMaps.lean` (Z2.e).
* `Algebra/ConeTriangle.lean`, `Algebra/ConeRotate.lean`, `Algebra/ConeShift.lean`,
  `Algebra/Pretriangulated.lean` (Z2.f1–f4).
* `Algebra/ConeCompAux.lean`, `Algebra/ConeComp.lean`, `Algebra/ConeCompTriangle.lean`,
  `Algebra/Triangulated.lean` (Z2.g1–g2).
* `ChecksForms.lean` (the checks `K4`, `K4_of_neg`, `K4_of_gt`, `K4_zero`).

## References

* [[B][Block]] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2, §2.4 (Prop 2.4.1).
* [[BK][BondalKapranov]] A. Bondal, M. Kapranov, *Enhanced triangulated categories*, Math. USSR
  Sb. 70 (1991),
  Props 1–2.
* Mathlib: `Mathlib/Algebra/Homology/HomotopyCategory/{Shift, MappingCone, Pretriangulated,
  Triangulated}.lean`.
* TauCeti project (Apache License 2.0, not a dependency): dg-cone files
  `CategoryTheory/DG/Twisted/`, a source of names only.
* Blueprint: `blueprint/blueprint-tr.md` (Z2, K4), `blueprint/blueprint.md` §9 (K4) and §11
  (v1.16, v1.18, v1.21); conventions: `blueprint/conventions.md` §2.
-/
