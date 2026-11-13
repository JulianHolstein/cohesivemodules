-- FROZEN (gate 4, 29 Oct 2026; C0 resolving data, in the main statement). Do not edit.
import Cohesivemodules.Algebra.FromComplexDef
import Cohesivemodules.Algebra.BaseChangeDef
import Cohesivemodules.Sheaf.FineDef
import Cohesivemodules.Sheaf.RingOfDef
import Mathlib.Analysis.Complex.Basic

set_option linter.style.header false

/-!
# C0: resolving data

Blueprint item C0 (§4, v1.9 "one carrier", v1.10 `c = 0`), [A, Assumptions 7.2 at h = 0].
These definitions enter the main statement through `blockFunctor E X := J` (C1, F15) for the
Dolbeault data of F14; they are frozen at gate 4.

* `DgaPresheaf X`: a presheaf of bounded graded-commutative, possibly curved ℂ-dgas on
  `Opens X`: for each open `U` an algebra `A U` with grading `𝒜 U` and a `GCDga` structure,
  restriction maps `res : V ≤ U → DgaHom (𝒜 U) (𝒜 V)`, functorial pointwise.
* `DgaPresheaf.pre0`: the presheaf of commutative rings `U ↦ ↥(𝒜_U 0)` (the one carrier of
  `𝒜⁰`, blueprint C0 v1.9).
* `PreResolvingData X` (C0.a): a dga presheaf satisfying the sheaf condition (gluing form), with
  `c = 0`, a sheaf of commutative rings `O` and ring maps `ρ_U : O(U) →+* ↥(𝒜_U 0)`, natural, with
  `d ∘ ρ_U = 0`; `𝒜⁰` fine; each `𝒜^q` locally free over `𝒜⁰` of finite rank (local frame form).
* `ResolvingData X` (C0.b): in addition `O → 𝒜⁰ → 𝒜¹ → ⋯` is exact (sectionwise injectivity,
  closed `0`-forms come from `O`, local exactness in degrees `≥ 1`) and the local lifting
  property LL.

## Deviations
* ⚠ (blueprint C0) LL is required only for global cohesive modules restricted to opens
  (sectionwise form of [A, Assumption 6]); [A] Assumption 5's first half (K-flatness of `𝒜` over
  `R`) is not assumed.
* The sheaf conditions are stated in gluing form on the dga presheaf (`glue`, `degree_local`),
  plus the sheaf condition of `𝒜⁰` as a `CommRingCat` presheaf (`isSheaf0`); the sheaves `𝒜^q`
  of the blueprint are derived from these in `Comparison/Setup.lean`.
* Local freeness is stated as a local frame (`locFrame`): near every point, `𝒜^q` has a finite
  family `e` such that every section of `𝒜^q` over every smaller open is uniquely a
  `𝒜⁰`-combination of the restrictions of `e`. This is "locally free of finite rank" written
  sectionwise; `Comparison/Setup.lean` turns it into `IsLocallyFinFreeSummand`.
* The exactness of the resolution is stated sectionwise and locally (the form of F12 and H1);
  `Comparison/Setup.lean` turns it into a quasi-isomorphism of sheaf complexes.
* (v1.10) `c = 0` is a field: `α(M)` is a complex only if `𝕏² = c = 0`, and A10 needs it in LL.
* `X : Type`, ℂ-algebras, `CommRingCat.{0}` (conventions §7).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable (X : Type) [TopologicalSpace X]

/-- **C0.** A presheaf of bounded graded-commutative curved ℂ-dgas on `Opens X`: for each open `U`
an algebra `A U` graded by `𝒜 U` (A1), and dga maps `res h : 𝒜 U → 𝒜 V` for `V ≤ U` (A9), with
`res (le_refl U) = id` and `res h' ∘ res h = res (h'.trans h)` pointwise. (Pointwise, not as
equalities of `DgaHom`s: base change along `res` depends on the map through an instance.) -/
structure DgaPresheaf where
  /-- The algebra of sections over `U`. -/
  A : Opens X → Type
  [ring : ∀ U, Ring (A U)]
  [alg : ∀ U, Algebra ℂ (A U)]
  /-- The grading of `A U`. -/
  𝒜 : ∀ U, ℤ → Submodule ℂ (A U)
  [graded : ∀ U, GradedAlgebra (𝒜 U)]
  [dga : ∀ U, GCDga (𝒜 U)]
  /-- Restriction to a smaller open, a map of (possibly curved) dgas. -/
  res : ∀ {U V : Opens X}, V ≤ U → DgaHom (𝒜 U) (𝒜 V)
  res_id : ∀ (U : Opens X) (a : A U), res (le_refl U) a = a
  res_comp : ∀ {U V W : Opens X} (h : V ≤ U) (h' : W ≤ V) (a : A U),
    res h' (res h a) = res (h'.trans h) a

attribute [instance] DgaPresheaf.ring DgaPresheaf.alg DgaPresheaf.graded DgaPresheaf.dga

variable {X}

namespace DgaPresheaf

variable (D : DgaPresheaf X)

/-- **C0 (one carrier, v1.9).** The presheaf of commutative rings `𝒜⁰ : U ↦ ↥(𝒜_U 0)`, with the
degree-`0` parts of the restriction maps. -/
def pre0 : (Opens X)ᵒᵖ ⥤ CommRingCat.{0} where
  obj U := CommRingCat.of ↥(D.𝒜 U.unop 0)
  map f := CommRingCat.ofHom (D.res (leOfHom f.unop)).f0
  map_id _ := CommRingCat.hom_ext (RingHom.ext fun _ ↦ Subtype.ext (D.res_id _ _))
  map_comp _ _ := CommRingCat.hom_ext (RingHom.ext fun _ ↦ Subtype.ext (D.res_comp _ _ _).symm)

/-- `pre0` on objects (rfl). -/
theorem pre0_obj (U : (Opens X)ᵒᵖ) : D.pre0.obj U = CommRingCat.of ↥(D.𝒜 U.unop 0) := rfl

end DgaPresheaf

variable (X) in
/-- **C0.a. Pre-resolving data.** [A, Assumptions 7.2 at h = 0], blueprint C0.a. A presheaf of
dgas `D` on `X` with:
* `glue`: sections of the algebras glue uniquely (the sheaf condition of `U ↦ A U`);
* `degree_local`: being of degree `q` is a local property;
* `isSheaf0`: `𝒜⁰ = D.pre0` is a sheaf of commutative rings;
* `c_eq_zero`: the curvature vanishes on every `U` (v1.10);
* a sheaf of commutative rings `O` and ring maps `ρ U : O(U) →+* ↥(𝒜_U 0)`, natural in `U`,
  with `d ∘ ρ U = 0`;
* `isFine0`: `𝒜⁰` is fine (S1);
* `locFrame`: every `𝒜^q` (`q : ℕ`) is locally free of finite rank over `𝒜⁰`: each `x` has an
  open `U ∋ x` and a finite family `e : ι → 𝒜_U^q` such that, over every `V ≤ U`, every
  `β ∈ 𝒜_V^q` is uniquely `∑ f i · res(e i)` with `f i ∈ 𝒜_V^0`.
No exactness and no LL: these are C0.b, so that J (C1) is defined without H1, H2. -/
structure PreResolvingData where
  /-- The presheaf of dgas `U ↦ 𝒜(U)`. -/
  D : DgaPresheaf X
  glue : ∀ {ι : Type} (U : ι → Opens X) (a : ∀ i, D.A (U i)),
    (∀ i j, D.res (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
      D.res (inf_le_right : U i ⊓ U j ≤ U j) (a j)) →
    ∃! b : D.A (⨆ i, U i), ∀ i, D.res (le_iSup U i) b = a i
  degree_local : ∀ {U : Opens X} (q : ℤ) (a : D.A U),
    (∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ D.res h a ∈ D.𝒜 V q) → a ∈ D.𝒜 U q
  isSheaf0 : Presheaf.IsSheaf (Opens.grothendieckTopology X) D.pre0
  c_eq_zero : ∀ U, GCDga.c (𝒜 := D.𝒜 U) = 0
  /-- The structure sheaf `O` (for the Dolbeault data: holomorphic functions). -/
  O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}
  /-- `ρ_U : O(U) →+* 𝒜⁰(U)`. -/
  ρ : ∀ U : Opens X, O.obj.obj (op U) →+* ↥(D.𝒜 U 0)
  ρ_natural : ∀ {U V : Opens X} (h : V ≤ U) (f : O.obj.obj (op U)),
    (D.res h).f0 (ρ U f) = ρ V (O.obj.map (homOfLE h).op f)
  d_ρ : ∀ U (f : O.obj.obj (op U)), GCDga.d (𝒜 := D.𝒜 U) (ρ U f : D.A U) = 0
  isFine0 : IsFine (ringOf (⟨D.pre0, isSheaf0⟩ : Sheaf _ CommRingCat))
  locFrame : ∀ (q : ℕ) (x : X), ∃ (U : Opens X) (_ : x ∈ U) (ι : Type) (_ : Fintype ι)
    (e : ι → D.𝒜 U q), ∀ (V : Opens X) (h : V ≤ U), ∀ β ∈ D.𝒜 V q,
      ∃! f : ι → D.𝒜 V 0, β = ∑ i, (f i : D.A V) * D.res h (e i)

namespace PreResolvingData

variable (P : PreResolvingData X)

/-- **C0.** The sheaf of commutative rings `𝒜⁰`, `𝒜⁰(U) = ↥(𝒜_U 0)`. -/
abbrev A0 : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0} := ⟨P.D.pre0, P.isSheaf0⟩

/-- **C0.** The global dga `A = 𝒜(X)`, graded by `𝒜X`. -/
abbrev 𝒜X : ℤ → Submodule ℂ (P.D.A ⊤) := P.D.𝒜 ⊤

/-- **C0.** Restriction from `X` to `V`. -/
abbrev r (V : Opens X) : DgaHom P.𝒜X (P.D.𝒜 V) := P.D.res le_top

/-- **C0.** The sheaf of rings `R = O` over which J lands (`ringOf`, conventions §7). -/
abbrev R : RingSheaf X := ringOf P.O

/-- One carrier (v1.9): global sections of `𝒜⁰` are `A⁰ = ↥(𝒜_X 0)`, by `rfl`. -/
theorem A0_obj_top : (P.A0.obj.obj (op ⊤) : Type) = ↥(P.𝒜X 0) := rfl

end PreResolvingData

variable (X) in
/-- **C0.b. Resolving data.** [A, Assumptions 7.2 at h = 0], blueprint C0.b. Pre-resolving data
such that
* `O → 𝒜⁰ → 𝒜¹ → ⋯` is a resolution: `ρ_U` is injective (`ρ_injective`), every `d`-closed
  section of `𝒜⁰` over `U` is in the image of `ρ_U` (`exact0`), and in degrees `q + 1 ≥ 1` every
  closed form is locally exact (`exactq`, the form of H1);
* LL (local lifting, the form of H2): for every cohesive module `M` over `A = 𝒜(X)` and `x : X`,
  there are an open `U′ ∋ x`, a bounded complex `W` of finitely generated projective
  `O(U′)`-modules, and an isomorphism in `Ho(P_{𝒜(U′)})` between `M|U′` (A9, base change along
  `res`) and `𝒜(U′) ⊗_{O(U′)} W` (A10, along `ρ_{U′}`). -/
structure ResolvingData extends PreResolvingData X where
  ρ_injective : ∀ U, Function.Injective (ρ U)
  exact0 : ∀ (U : Opens X) (a : D.𝒜 U 0), GCDga.d (𝒜 := D.𝒜 U) (a : D.A U) = 0 →
    ∃ f, ρ U f = a
  exactq : ∀ (U : Opens X) (q : ℕ) (x : X), x ∈ U →
    ∀ a ∈ D.𝒜 U ((q : ℤ) + 1), GCDga.d (𝒜 := D.𝒜 U) a = 0 →
      ∃ (U' : Opens X) (h : U' ≤ U), x ∈ U' ∧
        ∃ η ∈ D.𝒜 U' (q : ℤ), GCDga.d (𝒜 := D.𝒜 U') η = D.res h a
  LL : ∀ (M : CohesiveModule (D.𝒜 ⊤)) (x : X),
    ∃ (U' : Opens X) (_ : x ∈ U')
      (W : CochainComplex (ModuleCat.{0} (O.obj.obj (op U'))) ℤ)
      (hW : IsBoundedFGProj (O.obj.obj (op U')) W),
      Nonempty (HoP.mk (M.baseChange (D.res (le_top : U' ≤ ⊤))) ≅
        HoP.mk (CohesiveModule.fromComplex (ρ := ρ U') W (d_ρ U') (c_eq_zero U') hW))

end Cohesive
