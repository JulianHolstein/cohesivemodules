-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Algebra.CurvedDga
import Cohesivemodules.Comparison.SetupDef

set_option linter.style.header false

/-!
# Z3.a: curved presheaves of dgas and `DgaSheafData`

Blueprint item Z3.a (`blueprint/blueprint-tw.md` §2.1; blueprint §11 v1.19, decisions D1, D11).
* `DgaPresheaf.withCurvature D h`: the presheaf `D` with curvature `h|U` on every `U`, for a
  closed `h ∈ 𝒜²(X)`; same algebras, gradings and restriction maps.
* `DgaSheafData X`: the fields of `PreResolvingData` (C0.a) except `c_eq_zero`, so that a curved
  presheaf can carry the sheaf data; `PreResolvingData.toSheafData`, `DgaSheafData.withCurvature`.

## Deviations
* [A, Assumptions 7.2] state the assumptions for the curved algebra directly; here the curved data
  are the flat `PreResolvingData` with the curvature changed (the sheaf fields do not involve `c`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace DgaPresheaf

variable (D : DgaPresheaf X) (h : D.A ⊤) (hh : h ∈ D.𝒜 ⊤ 2)
  (hd : GCDga.d (𝒜 := D.𝒜 ⊤) h = 0)

/-- Z3.a: the curved instance on `D.𝒜 U`, curvature `h|U` (reducible, P15). -/
@[reducible] def curvedInst (U : Opens X) : GCDga (D.𝒜 U) :=
  (D.dga U).withC (D.res le_top h) ((D.res le_top).map_mem hh)
    (by rw [← (D.res le_top).map_d, hd]; exact map_zero _)

/-- **Z3.a.** [A, §7.2]. The presheaf of dgas `D` with curvature `h|U` on every open `U`, for a
closed `h ∈ 𝒜²(X)`: same algebras, gradings and restriction maps (these preserve the curvatures
since `res (h|U) = h|V`, `res_comp`). A `def`: instance search sees `(D.withCurvature h …).𝒜 U`
as a term distinct from `D.𝒜 U`. -/
def withCurvature : DgaPresheaf X where
  A := D.A
  𝒜 := D.𝒜
  graded := D.graded
  dga := D.curvedInst h hh hd
  res {U V} h' :=
    @DgaHom.mk ℂ _ (D.A U) _ _ (D.𝒜 U) _ (D.curvedInst h hh hd U) (D.A V) _ _ (D.𝒜 V) _
      (D.curvedInst h hh hd V) (D.res h').toAlgHom (D.res h').map_mem (D.res h').map_d
      (D.res_comp le_top h' h)
  res_id := D.res_id
  res_comp := D.res_comp

/-- Z3.a: same algebras (rfl). -/
theorem withCurvature_A : (D.withCurvature h hh hd).A = D.A := rfl

/-- Z3.a: same gradings (rfl). -/
theorem withCurvature_𝒜 : (D.withCurvature h hh hd).𝒜 = D.𝒜 := rfl

/-- Z3.a: same restriction maps (rfl). -/
theorem withCurvature_res_apply {U V : Opens X} (h' : V ≤ U) (a : D.A U) :
    (D.withCurvature h hh hd).res h' a = D.res h' a := rfl

/-- Z3.a: the curvature over `U` is `h|U` (rfl). -/
theorem withCurvature_c (U : Opens X) :
    GCDga.c (𝒜 := (D.withCurvature h hh hd).𝒜 U) = D.res le_top h := rfl

/-- Z3.a: the differential over `U` is that of `D` (rfl). -/
theorem withCurvature_d (U : Opens X) :
    GCDga.d (𝒜 := (D.withCurvature h hh hd).𝒜 U) = GCDga.d (𝒜 := D.𝒜 U) := rfl

/-- Z3.a: the presheaf `𝒜⁰` is unchanged (rfl). -/
theorem withCurvature_pre0 : (D.withCurvature h hh hd).pre0 = D.pre0 := rfl

end DgaPresheaf

variable (X) in
/-- **Z3.a (D11).** [A, Assumptions 7.2]. The fields of pre-resolving data (C0.a) without
`c_eq_zero`: a presheaf of (possibly curved) dgas `D`, with the gluing and degree-locality of
sections, `𝒜⁰` a fine sheaf of commutative rings, a structure sheaf `O` with `ρ : O → 𝒜⁰`
(`d ∘ ρ = 0`), and `𝒜^q` locally free over `𝒜⁰`. Field by field as `PreResolvingData`. -/
structure DgaSheafData where
  /-- The presheaf of dgas `U ↦ 𝒜(U)`. -/
  D : DgaPresheaf X
  glue : ∀ {ι : Type} (U : ι → Opens X) (a : ∀ i, D.A (U i)),
    (∀ i j, D.res (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
      D.res (inf_le_right : U i ⊓ U j ≤ U j) (a j)) →
    ∃! b : D.A (⨆ i, U i), ∀ i, D.res (le_iSup U i) b = a i
  degree_local : ∀ {U : Opens X} (q : ℤ) (a : D.A U),
    (∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧ D.res h a ∈ D.𝒜 V q) → a ∈ D.𝒜 U q
  isSheaf0 : Presheaf.IsSheaf (Opens.grothendieckTopology X) D.pre0
  /-- The structure sheaf `O`. -/
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

/-- **Z3.a.** Pre-resolving data forget `c_eq_zero`. -/
def PreResolvingData.toSheafData (P : PreResolvingData X) : DgaSheafData X where
  D := P.D
  glue := P.glue
  degree_local := P.degree_local
  isSheaf0 := P.isSheaf0
  O := P.O
  ρ := P.ρ
  ρ_natural := P.ρ_natural
  d_ρ := P.d_ρ
  isFine0 := P.isFine0
  locFrame := P.locFrame

/-- **Z3.a.** [A, §7.2]. The sheaf data with curvature `h|U` on every `U`
(`DgaPresheaf.withCurvature`); every other field is that of `S` (none involves `c`). Reducible
(Z3.o), so that instance search sees `(S.withCurvature h …).O` as `S.O`. -/
abbrev DgaSheafData.withCurvature (S : DgaSheafData X) (h : S.D.A ⊤) (hh : h ∈ S.D.𝒜 ⊤ 2)
    (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) : DgaSheafData X where
  D := S.D.withCurvature h hh hd
  glue := S.glue
  degree_local := S.degree_local
  isSheaf0 := S.isSheaf0
  O := S.O
  ρ := S.ρ
  ρ_natural := S.ρ_natural
  d_ρ := S.d_ρ
  isFine0 := S.isFine0
  locFrame := S.locFrame

/-- Z3.a: `toSheafData` keeps the presheaf (rfl). -/
theorem PreResolvingData.toSheafData_D (P : PreResolvingData X) : P.toSheafData.D = P.D := rfl

/-- Z3.a: `toSheafData` keeps `O` (rfl). -/
theorem PreResolvingData.toSheafData_O (P : PreResolvingData X) : P.toSheafData.O = P.O := rfl

/-- Z3.a: the curved sheaf data have the curved presheaf (rfl). -/
theorem DgaSheafData.withCurvature_D (S : DgaSheafData X) (h : S.D.A ⊤) (hh : h ∈ S.D.𝒜 ⊤ 2)
    (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) :
    (S.withCurvature h hh hd).D = S.D.withCurvature h hh hd := rfl

/-- Z3.a: the curved sheaf data keep `O` (rfl). -/
theorem DgaSheafData.withCurvature_O (S : DgaSheafData X) (h : S.D.A ⊤) (hh : h ∈ S.D.𝒜 ⊤ 2)
    (hd : GCDga.d (𝒜 := S.D.𝒜 ⊤) h = 0) : (S.withCurvature h hh hd).O = S.O := rfl

end Cohesive
