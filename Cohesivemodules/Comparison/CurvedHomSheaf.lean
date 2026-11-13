import Cohesivemodules.Comparison.SheafDataAlphaDef
import Cohesivemodules.Comparison.HomSheafAux
import Cohesivemodules.Comparison.CurvedHomRetract
import Cohesivemodules.Sheaf.Soft
import Cohesivemodules.Algebra.BaseChangeResAPI

set_option linter.style.header false

/-!
# Z3.q: Hom sheaves of cohesive modules over (possibly curved) sheaf data (copy of C3)

Blueprint item Z3.q (`blueprint/blueprint-tw.md` §3 F′ (a)). C3 (`Comparison/HomSheaf.lean`) word
for word over `S : DgaSheafData X` (no `c_eq_zero`), so that it applies to the curved data
`S.withCurvature h` and to cohesive modules over a curved algebra. Only the proof of `δ² = 0`
(`homD_homD`) changes: `δ²χ = 𝕏₂²χ − χ𝕏₁² = c·χ − χ(c·) = 0`.

Blueprint item C3 (§4), [A, Def 7.2.5 ff.], [B, §4.1]. For cohesive modules `M₁`, `M₂` over
`𝒜(U₀)` and `V ≤ U₀`, the sections of `ℋ(M₁, M₂)` in degree `n` over `V` are

  `ℋ^n(V) = {χ : Tot(M₁) →ₗ[ℂ] Tot(M₂|V) | χ has degree n, χ(a·x) = (-1)^{n|a|} res_V(a)·χ(x)}`

(`homAlong`): degree-`n` maps semilinear along the restriction `res_V : 𝒜(U₀) → 𝒜(V)`. By the
base-change adjunction (A9, uniqueness `hom_eq_of_bcF'`) these are exactly the degree-`n` maps
`M₁|V → M₂|V` over `𝒜(V)`, the blueprint's `Hom^n_{P_{𝒜(V)}}(M₁|V, M₂|V)`; this spelling makes
restriction a postcomposition (`totRes`), strictly functorial.
* `homAlong`, `HomSec` (an `O(V)`-module through `ρ_V`), `homRes` (restriction), `homδV`
  (`δχ = 𝕏₂ ∘ χ - (-1)^n χ ∘ 𝕏₁`, conventions §2, = `CochainComplex.HomComplex.δ`).
* For `U₀ = X`: the complex of sheaves of `O`-modules `S.ℋ M₁ M₂` (`homPre`, `homSh`, `homD`).
* **C3** `exists_homTopEquiv`: `ℋ(M₁, M₂)(X) ≅ Hom^•_{P_A}(M₁, M₂)` as complexes.
* **C3.a(ii)** `isSoft_homSh`: `𝒜⁰(X)` acts on each `ℋ^n` (multiplication by `res_V(a)`), so
  the terms are soft (S3.b(i)). ⚠ The differential is not `𝒜⁰`-linear (`δ(aχ) = da·χ + a·δχ`).

## Deviations
* `ℋ^n(V)` is spelled as maps out of `Tot(M₁)` semilinear along `res_V`, not as maps out of
  `Tot(M₁|V)`; canonically isomorphic (base-change adjunction).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- Degree-`0` elements commute with the `A`-action on `Tot`. -/
private theorem smul0_smul_comm {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
    (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    (c : 𝒜 0) (b : A) (y : Tot 𝒜 Q) : c • b • y = b • c • y := by
  have h : ∀ (f : 𝒜 0) (x : Tot 𝒜 Q), f • x = (f : A) • x := by
    intro f x
    induction x using Tot.induction_on with
    | ht a e =>
      exact (TensorProduct.smul_tmul' (R := 𝒜 0) f a e).trans (Tot.smul_tmul (f : A) a e).symm
    | hadd x y hx hy => rw [smul_add, hx, hy, smul_add]
  rw [h, h, ← mul_smul, ← mul_smul, GCDga.central 𝒜 c.2 b]

namespace DgaSheafData

variable (S : DgaSheafData X) {U₀ : Opens X}

section Sections

variable (M₁ M₂ : CohesiveModule (S.D.𝒜 U₀))

/-- `totRes` is semilinear over `res : 𝒜(V) → 𝒜(W)`, for every element of `𝒜(V)`. -/
private theorem totRes_smulA {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (b : S.D.A V)
    (x : S.TotSec M₂ hV) :
    S.totRes M₂ hV hW (b • x) = S.D.res hW b • S.totRes M₂ hV hW x := by
  exact bcTotRes_smul (S.D.res hW) (S.D.res hV) (S.D.res (hW.trans hV)) (S.D.res_comp hV hW)
    M₂.Q b x

/-- `totRes` is `ℂ`-linear. -/
theorem totRes_smulC {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) (c : ℂ) (x : S.TotSec M₂ hV) :
    S.totRes M₂ hV hW (c • x) = c • S.totRes M₂ hV hW x := by
  rw [← algebraMap_smul (S.D.A V) c x, S.totRes_smulA M₂ hV hW,
    ← algebraMap_smul (S.D.A W) c (S.totRes M₂ hV hW x)]
  congr 1
  exact (S.D.res hW).toAlgHom.commutes c

/-- `totRes` as a `ℂ`-linear map. -/
def totResL {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) :
    S.TotSec M₂ hV →ₗ[ℂ] S.TotSec M₂ (hW.trans hV) where
  toFun := S.totRes M₂ hV hW
  map_add' := map_add _
  map_smul' := S.totRes_smulC M₂ hV hW

/-- **C3.** `ℋ^n(V)`: `ℂ`-linear maps `χ : Tot(M₁) → Tot(M₂|V)` of degree `n` with
`χ(a·x) = (-1)^{n|a|} res_V(a)·χ(x)` for homogeneous `a ∈ 𝒜(U₀)`; an `𝒜⁰(V)`-submodule. -/
def homAlong (n : ℤ) {V : Opens X} (h : V ≤ U₀) :
    Submodule ↥(S.D.𝒜 V 0) (M₁.T →ₗ[ℂ] S.TotSec M₂ h) where
  carrier := {χ | (∀ {m : ℤ} {x : M₁.T}, x ∈ totDeg (S.D.𝒜 U₀) M₁.Q m →
      χ x ∈ totDeg (S.D.𝒜 V) (M₂.baseChange (S.D.res h)).Q (m + n)) ∧
    ∀ {p : ℤ} {a : S.D.A U₀}, a ∈ S.D.𝒜 U₀ p → ∀ x : M₁.T,
      χ (a • x) = (n * p).negOnePow • (S.D.res h a) • χ x}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun hx => add_mem (hφ.1 hx) (hψ.1 hx), fun ha x => by
      simp only [LinearMap.add_apply, hφ.2 ha, hψ.2 ha, smul_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => by simp⟩
  smul_mem' := fun c φ hφ =>
    ⟨fun hx => S.smul0_mem_totDeg M₂ c (hφ.1 hx), fun {p a} ha x => by
      simp only [LinearMap.smul_apply, hφ.2 ha]
      rw [smul_comm c, smul0_smul_comm]⟩

/-- **C3.** `ℋ^n(V)` as a type. -/
def HomSec (n : ℤ) {V : Opens X} (h : V ≤ U₀) : Type := ↥(S.homAlong M₁ M₂ n h)

instance (n : ℤ) {V : Opens X} (h : V ≤ U₀) : AddCommGroup (S.HomSec M₁ M₂ n h) :=
  inferInstanceAs (AddCommGroup ↥(S.homAlong M₁ M₂ n h))

/-- **C3.** `O(V)` acts on `ℋ^n(V)` through `ρ_V` (postcomposition with multiplication). -/
instance (n : ℤ) {V : Opens X} (h : V ≤ U₀) :
    Module (S.O.obj.obj (op V)) (S.HomSec M₁ M₂ n h) :=
  Module.compHom ↥(S.homAlong M₁ M₂ n h) (S.ρ V)

/-- Postcomposition with `totRes` preserves `homAlong`. -/
theorem totResL_comp_mem (n : ℤ) {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V)
    {χ : M₁.T →ₗ[ℂ] S.TotSec M₂ hV} (hχ : χ ∈ S.homAlong M₁ M₂ n hV) :
    S.totResL M₂ hV hW ∘ₗ χ ∈ S.homAlong M₁ M₂ n (hW.trans hV) := by
  refine ⟨fun {m x} hx => S.totRes_mem M₂ hV hW (hχ.1 hx), fun {p a} ha x => ?_⟩
  change S.totRes M₂ hV hW (χ (a • x)) = _
  rw [hχ.2 ha, Units.smul_def, map_zsmul, S.totRes_smulA M₂ hV hW, S.D.res_comp hV hW,
    ← Units.smul_def]
  rfl

/-- **C3.** Restriction `ℋ^n(V) → ℋ^n(W)`: postcomposition with `totRes`; semilinear over
`O(V) → O(W)`. -/
def homRes (n : ℤ) {V W : Opens X} (hV : V ≤ U₀) (hW : W ≤ V) :
    S.HomSec M₁ M₂ n hV →ₛₗ[(S.O.obj.map (homOfLE hW).op).hom]
      S.HomSec M₁ M₂ n (hW.trans hV) where
  toFun χ := ⟨S.totResL M₂ hV hW ∘ₗ χ.1, S.totResL_comp_mem M₁ M₂ n hV hW χ.2⟩
  map_add' χ ψ := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' f χ := Subtype.ext <| LinearMap.ext fun x => by
    change S.totRes M₂ hV hW ((S.ρ V f) • χ.1 x) = (S.ρ W _) • S.totRes M₂ hV hW (χ.1 x)
    rw [S.totRes_smul0, S.ρ_natural]

/-- The differential preserves `homAlong` (degree `n ↦ n + 1`). -/
theorem homδ_mem (n : ℤ) {V : Opens X} (h : V ≤ U₀) {χ : M₁.T →ₗ[ℂ] S.TotSec M₂ h}
    (hχ : χ ∈ S.homAlong M₁ M₂ n h) :
    (M₂.baseChange (S.D.res h)).X ∘ₗ χ - n.negOnePow • (χ ∘ₗ M₁.X) ∈
      S.homAlong M₁ M₂ (n + 1) h := by
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · have e1 : (M₂.baseChange (S.D.res h)).X (χ x) ∈
        totDeg (S.D.𝒜 V) (M₂.baseChange (S.D.res h)).Q (m + (n + 1)) := by
      have := (M₂.baseChange (S.D.res h)).X_mem (hχ.1 hx); rwa [add_assoc] at this
    have e2 : χ (M₁.X x) ∈ totDeg (S.D.𝒜 V) (M₂.baseChange (S.D.res h)).Q (m + (n + 1)) := by
      have := hχ.1 (M₁.X_mem hx); rwa [add_assoc, add_comm 1 n] at this
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Units.smul_def]
    exact sub_mem e1 (Submodule.smul_of_tower_mem _ _ e2)
  · have hda := GCDga.d_mem (𝒜 := S.D.𝒜 U₀) ha
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      M₁.leibniz ha, map_add, hχ.2 ha, hχ.2 hda, (M₂.baseChange (S.D.res h)).leibniz
        ((S.D.res h).map_mem ha), Units.smul_def, map_zsmul, (S.D.res h).map_d]
    simp only [negOnePow_parity, parity_simps]
    by_cases hn : Even n <;> by_cases hp : Even p <;> simp [hn, hp, smul_sub, smul_neg]

/-- **C3.** The differential `δχ = 𝕏₂ ∘ χ - (-1)^n χ ∘ 𝕏₁` on `ℋ^n(V)` (conventions §2);
`O(V)`-linear (`d ∘ ρ_V = 0`). -/
def homδV (n : ℤ) {V : Opens X} (h : V ≤ U₀) :
    S.HomSec M₁ M₂ n h →ₗ[S.O.obj.obj (op V)] S.HomSec M₁ M₂ (n + 1) h where
  toFun χ := ⟨(M₂.baseChange (S.D.res h)).X ∘ₗ χ.1 - n.negOnePow • (χ.1 ∘ₗ M₁.X),
    S.homδ_mem M₁ M₂ n h χ.2⟩
  map_add' χ ψ := Subtype.ext <| by
    change (M₂.baseChange (S.D.res h)).X ∘ₗ (χ.1 + ψ.1) -
      n.negOnePow • ((χ.1 + ψ.1) ∘ₗ M₁.X) = (_ - _ • _) + (_ - _ • _)
    simp only [LinearMap.comp_add, LinearMap.add_comp, smul_add]
    abel
  map_smul' f χ := Subtype.ext <| LinearMap.ext fun x => by
    change (M₂.baseChange (S.D.res h)).X ((S.ρ V f) • χ.1 x) -
      n.negOnePow • ((S.ρ V f) • χ.1 (M₁.X x)) =
      (S.ρ V f) • ((M₂.baseChange (S.D.res h)).X (χ.1 x) - n.negOnePow • χ.1 (M₁.X x))
    rw [S.X_smulO M₂ h f, smul_sub, smul_comm (n.negOnePow) (S.ρ V f)]

end Sections

section Global

variable (M₁ M₂ : CohesiveModule S.𝒜X)

/-- **C3.** `ℋ^n(M₁, M₂)` as a presheaf of `O`-modules on `X`. -/
def homPre (n : ℤ) : PresheafOfModules.{0} S.R.obj where
  obj V := ModuleCat.of (S.O.obj.obj (op V.unop)) (S.HomSec M₁ M₂ n (le_top : V.unop ≤ ⊤))
  map {U V} f := ModuleCat.semilinearMapAddEquiv (S.R.obj.map f).hom
      (ModuleCat.of (S.O.obj.obj (op U.unop)) (S.HomSec M₁ M₂ n (le_top : U.unop ≤ ⊤)))
      (ModuleCat.of (S.O.obj.obj (op V.unop)) (S.HomSec M₁ M₂ n (le_top : V.unop ≤ ⊤)))
      (S.homRes M₁ M₂ n le_top (leOfHom f.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    exact Subtype.ext (LinearMap.ext fun y => S.totRes_id M₂ _ (x.1 y))
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    exact Subtype.ext (LinearMap.ext fun y => (S.totRes_comp M₂ _ _ _ (x.1 y)).symm)

/-- **C3.** `ℋ^n(M₁, M₂)` is a sheaf (`Q₁^p` finitely generated projective, C1.a). -/
theorem isSheaf_homPre (n : ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (S.homPre M₁ M₂ n).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (X := TopCat.of X) (S.homPre M₁ M₂ n).presheaf).2 ?_
  intro ι U sf hsf
  let s' : ∀ a, S.HomSec M₁ M₂ n (le_top : U a ≤ ⊤) := sf
  have hc : ∀ a b x, S.totRes M₂ le_top (inf_le_left : U a ⊓ U b ≤ U a) ((s' a).1 x) =
      S.totRes M₂ le_top (inf_le_right : U a ⊓ U b ≤ U b) ((s' b).1 x) := fun a b x =>
    LinearMap.congr_fun (congrArg Subtype.val (hsf a b)) x
  choose t ht hu using fun x => S.car_glue M₂ U (fun a => (s' a).1 x) (fun a b => hc a b x)
  have hadd : ∀ x y, t (x + y) = t x + t y := fun x y =>
    (hu (x + y) (t x + t y) fun a => by rw [map_add, ht x a, ht y a, map_add]).symm
  have hsmul : ∀ (c : ℂ) x, t (c • x) = c • t x := fun c x =>
    (hu (c • x) (c • t x) fun a => by
      rw [S.totRes_smulC M₂ le_top _ c, ht x a, map_smul]).symm
  let tL : M₁.T →ₗ[ℂ] S.TotSec M₂ (le_top : (⨆ a, U a) ≤ ⊤) :=
    { toFun := t, map_add' := hadd, map_smul' := hsmul }
  have hmem : tL ∈ S.homAlong M₁ M₂ n (le_top : (⨆ a, U a) ≤ ⊤) := by
    refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
    · refine S.car_mem_totDeg_of_local M₂ (t x) (m + n) fun pt hpt => ?_
      obtain ⟨a, ha⟩ := Opens.mem_iSup.1 hpt
      refine ⟨U a, le_iSup U a, ha, ?_⟩
      rw [ht x a]
      exact (s' a).2.1 hx
    · refine (hu (a • x) ((n * p).negOnePow • (S.D.res le_top) a • t x) fun i => ?_).symm
      rw [Units.smul_def, map_zsmul, S.totRes_smulA M₂, S.D.res_comp, ht x i,
        ← Units.smul_def, (s' i).2.2 ha x]
  refine ⟨⟨tL, hmem⟩, fun a => ?_, fun s'' hs'' => ?_⟩
  · exact Subtype.ext (LinearMap.ext fun x => ht x a)
  · exact Subtype.ext (LinearMap.ext fun x =>
      hu x (s''.1 x) fun a => congrArg (fun χ : S.HomSec M₁ M₂ n le_top => χ.1 x) (hs'' a))

/-- **C3.** The sheaf of `O`-modules `ℋ^n(M₁, M₂)`. -/
def homSh (n : ℤ) : Mod S.R := ⟨S.homPre M₁ M₂ n, S.isSheaf_homPre M₁ M₂ n⟩

/-- **C3.** The differential `ℋ^n ⟶ ℋ^{n+1}`. -/
def homD (n : ℤ) : S.homSh M₁ M₂ n ⟶ S.homSh M₁ M₂ (n + 1) :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (S.homδV M₁ M₂ n (le_top : V.unop ≤ ⊤))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       refine LinearMap.ext fun y => ?_
       change (M₂.baseChange (S.D.res (le_top : V.unop ≤ ⊤))).X (S.totRes M₂ le_top
           (leOfHom f.unop) (x.1 y)) - n.negOnePow • S.totRes M₂ le_top (leOfHom f.unop)
           (x.1 (M₁.X y)) = S.totRes M₂ le_top (leOfHom f.unop)
           ((M₂.baseChange (S.D.res (le_top : U.unop ≤ ⊤))).X (x.1 y) -
             n.negOnePow • x.1 (M₁.X y))
       rw [S.X_totRes M₂ le_top (leOfHom f.unop), map_sub, Units.smul_def, Units.smul_def,
         map_zsmul] }⟩

/-- `δ² = 0` on `ℋ`: `δ²χ = 𝕏₂² ∘ χ − χ ∘ 𝕏₁² = c·χ − χ(c·) = 0` (the curvature `c` has
degree `2`, so `χ(c·y) = c·χ(y)`). -/
theorem homD_homD (n : ℤ) : S.homD M₁ M₂ n ≫ S.homD M₁ M₂ (n + 1) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  refine LinearMap.ext fun y => ?_
  have h0 : ∀ z, (M₂.baseChange (S.D.res (le_top : V.unop ≤ ⊤))).X
      ((M₂.baseChange (S.D.res (le_top : V.unop ≤ ⊤))).X z) =
      GCDga.c (𝒜 := S.D.𝒜 V.unop) • z := fun z =>
    (M₂.baseChange (S.D.res (le_top : V.unop ≤ ⊤))).flat z
  change (M₂.baseChange (S.D.res (le_top : V.unop ≤ ⊤))).X
      ((M₂.baseChange (S.D.res (le_top : V.unop ≤ ⊤))).X (x.1 y) -
        n.negOnePow • x.1 (M₁.X y)) -
      (n + 1).negOnePow • ((M₂.baseChange (S.D.res (le_top : V.unop ≤ ⊤))).X (x.1 (M₁.X y)) -
        n.negOnePow • x.1 (M₁.X (M₁.X y))) = 0
  have h1 : x.1 (M₁.X (M₁.X y)) = GCDga.c (𝒜 := S.D.𝒜 V.unop) • x.1 y := by
    rw [M₁.flat y, x.2.2 (GCDga.c_mem (𝒜 := S.𝒜X)) y, mul_comm, Int.negOnePow_two_mul,
      one_smul]
    exact congrArg (· • x.1 y) ((S.D.res (le_top : V.unop ≤ ⊤)).map_c)
  rw [h1, map_sub, h0, Units.smul_def, map_zsmul, Units.smul_def, Int.negOnePow_succ]
  have h2 : (n.negOnePow : ℤ) * n.negOnePow = 1 := by
    rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  simp only [Units.val_neg, neg_smul, smul_sub, Units.smul_def, smul_smul]
  rw [show (-(n.negOnePow : ℤ) * n.negOnePow) = -1 by rw [neg_mul, h2], neg_smul, one_smul]
  abel

/-- **C3.** The complex of sheaves of `O`-modules `ℋ(M₁, M₂)`. -/
def ℋ : CochainComplex (Mod S.R) ℤ :=
  CochainComplex.of (S.homSh M₁ M₂) (S.homD M₁ M₂) (S.homD_homD M₁ M₂)

/-- `F = bcF` along `r_X : 𝒜(X) → 𝒜(X)` as a `ℂ`-linear map `Tot(M₂) → Tot(M₂|X)`. -/
def bcFTop : M₂.T →ₗ[ℂ] S.TotSec M₂ (le_top : (⊤ : Opens X) ≤ ⊤) where
  toFun := bcF (S.r ⊤) M₂.Q
  map_add' := map_add _
  map_smul' := bcF_smul_k (S.r ⊤) M₂.Q

/-- `F ∘ φ` lies in `ℋ^n(X)` for `φ ∈ Hom^n(M₁, M₂)`. -/
theorem bcFTop_comp_mem {n : ℤ} (φ : Hom M₁.toQuasiCohesive M₂.toQuasiCohesive n) :
    S.bcFTop M₂ ∘ₗ φ.1 ∈ S.homAlong M₁ M₂ n (le_top : (⊤ : Opens X) ≤ ⊤) := by
  refine ⟨fun {m x} hx => bcF_mem_totDeg (S.r ⊤) M₂.Q (φ.2.1 hx), fun {p a} ha x => ?_⟩
  change bcF (S.r ⊤) M₂.Q (φ.1 (a • x)) = _
  rw [φ.2.2 ha, Units.smul_def, map_zsmul, bcF_smul, ← Units.smul_def]
  rfl

/-- **C3.** `Hom^n_{P_A}(M₁, M₂) → ℋ^n(M₁, M₂)(X)`, `φ ↦ F ∘ φ` (`F = bcF` along `r_X`, which is
the identity map of `𝒜(X)`). -/
def homTop (n : ℤ) : Hom M₁.toQuasiCohesive M₂.toQuasiCohesive n →+
    S.HomSec M₁ M₂ n (le_top : (⊤ : Opens X) ≤ ⊤) where
  toFun φ := ⟨S.bcFTop M₂ ∘ₗ φ.1, S.bcFTop_comp_mem M₁ M₂ φ⟩
  map_zero' := Subtype.ext (LinearMap.comp_zero _)
  map_add' _ _ := Subtype.ext (LinearMap.comp_add _ _ _)

/-- `r_X ∘ r_X = id` pointwise. -/
private theorem rTop_rTop (a : S.D.A ⊤) : S.r ⊤ (S.r ⊤ a) = a :=
  (S.D.res_comp le_top le_top a).trans (S.D.res_id ⊤ a)

/-- The inverse of `bcFTop` as a `ℂ`-linear map (`invTot` along `r_X`). -/
private def invTopL : S.TotSec M₂ (le_top : (⊤ : Opens X) ≤ ⊤) →ₗ[ℂ] M₂.T where
  toFun := invTot (S.r ⊤) (S.r ⊤) S.rTop_rTop M₂.Q
  map_add' := map_add _
  map_smul' := invTot_smul_k (S.r ⊤) (S.r ⊤) S.rTop_rTop M₂.Q

/-- `invTopL` is semilinear along `r_X`. -/
private theorem invTopL_smul (b : S.D.A ⊤) (y : S.TotSec M₂ (le_top : (⊤ : Opens X) ≤ ⊤)) :
    S.invTopL M₂ (b • y) = S.r ⊤ b • S.invTopL M₂ y :=
  invTot_smul (S.r ⊤) (S.r ⊤) S.rTop_rTop M₂.Q b y

/-- The inverse of `F`, composed with `χ ∈ ℋ^n(X)`, lies in `Hom^n`. -/
private theorem invTop_comp_mem {n : ℤ} {χ : M₁.T →ₗ[ℂ] S.TotSec M₂ (le_top : (⊤ : Opens X) ≤ ⊤)}
    (hχ : χ ∈ S.homAlong M₁ M₂ n (le_top : (⊤ : Opens X) ≤ ⊤)) :
    S.invTopL M₂ ∘ₗ χ ∈ Hom M₁.toQuasiCohesive M₂.toQuasiCohesive n := by
  refine ⟨fun {m x} hx => invTot_mem (S.r ⊤) (S.r ⊤) S.rTop_rTop M₂.Q (hχ.1 hx),
    fun {p a} ha x => ?_⟩
  change S.invTopL M₂ (χ (a • x)) = _
  rw [hχ.2 ha, Units.smul_def, map_zsmul, S.invTopL_smul, S.rTop_rTop, ← Units.smul_def]
  rfl

/-- **C3.** `homTop` is bijective: `ℋ(M₁, M₂)(X) ≅ Hom^•_{P_A}(M₁, M₂)` in each degree. -/
theorem homTop_bijective (n : ℤ) : Function.Bijective (S.homTop M₁ M₂ n) := by
  have hinv : ∀ y, S.invTopL M₂ (S.bcFTop M₂ y) = y := fun y =>
    invTot_bcF (S.r ⊤) (S.r ⊤) S.rTop_rTop M₂.Q y
  have hsurj : ∀ z, S.bcFTop M₂ (S.invTopL M₂ z) = z := fun z =>
    bcF_invTot (S.r ⊤) (S.r ⊤) S.rTop_rTop M₂.Q S.rTop_rTop z
  constructor
  · intro φ φ' h
    apply Subtype.ext
    refine LinearMap.ext fun x => ?_
    have h1 : S.bcFTop M₂ (φ.1 x) = S.bcFTop M₂ (φ'.1 x) :=
      congrArg (fun χ : S.HomSec M₁ M₂ n le_top => χ.1 x) h
    rw [← hinv (φ.1 x), ← hinv (φ'.1 x), h1]
  · intro χ
    refine ⟨⟨S.invTopL M₂ ∘ₗ χ.1, S.invTop_comp_mem M₁ M₂ χ.2⟩, ?_⟩
    apply Subtype.ext
    refine LinearMap.ext fun x => ?_
    exact hsurj (χ.1 x)

/-- **C3.** `homTop` commutes with the differentials (conventions §2, A4's `δ`). -/
theorem homδV_homTop (n : ℤ) (φ : Hom M₁.toQuasiCohesive M₂.toQuasiCohesive n) :
    S.homδV M₁ M₂ n le_top (S.homTop M₁ M₂ n φ) =
      S.homTop M₁ M₂ (n + 1) ⟨δ M₁.toQuasiCohesive M₂.toQuasiCohesive n φ.1,
        δ_mem M₁.toQuasiCohesive M₂.toQuasiCohesive φ.2⟩ := by
  apply Subtype.ext
  refine LinearMap.ext fun x => ?_
  change (M₂.baseChange (S.D.res (le_top : (⊤ : Opens X) ≤ ⊤))).X (S.bcFTop M₂ (φ.1 x)) -
    n.negOnePow • S.bcFTop M₂ (φ.1 (M₁.X x)) =
    S.bcFTop M₂ (M₂.X (φ.1 x) - n.negOnePow • φ.1 (M₁.X x))
  rw [map_sub, Units.smul_def, Units.smul_def, map_zsmul,
    show (M₂.baseChange (S.D.res (le_top : (⊤ : Opens X) ≤ ⊤))).X (S.bcFTop M₂ (φ.1 x)) =
      S.bcFTop M₂ (M₂.X (φ.1 x)) from bc_extend_bcF (S.r ⊤) M₂.toQuasiCohesive (φ.1 x)]

/-- Multiplication by `res_V(a)` on `ℋ^n(V)` (`a ∈ 𝒜⁰(X)`), `O(V)`-linear. -/
private def actV (a : ↥(S.𝒜X 0)) (n : ℤ) {V : Opens X} (h : V ≤ ⊤) :
    S.HomSec M₁ M₂ n h →ₗ[S.O.obj.obj (op V)] S.HomSec M₁ M₂ n h where
  toFun χ := (S.D.res h).f0 a • (show ↥(S.homAlong M₁ M₂ n h) from χ)
  map_add' χ ψ := smul_add _ (show ↥(S.homAlong M₁ M₂ n h) from χ) ψ
  map_smul' f χ := by
    change (S.D.res h).f0 a • (S.ρ V f • (show ↥(S.homAlong M₁ M₂ n h) from χ)) =
      S.ρ V f • ((S.D.res h).f0 a • (show ↥(S.homAlong M₁ M₂ n h) from χ))
    exact smul_comm _ _ _

/-- `actV` commutes with restriction. -/
private theorem actV_res (a : ↥(S.𝒜X 0)) (n : ℤ) {V W : Opens X} (hV : V ≤ ⊤) (hW : W ≤ V)
    (χ : S.HomSec M₁ M₂ n hV) :
    S.homRes M₁ M₂ n hV hW (S.actV M₁ M₂ a n hV χ) =
      S.actV M₁ M₂ a n (hW.trans hV) (S.homRes M₁ M₂ n hV hW χ) := by
  refine Subtype.ext (LinearMap.ext fun x => ?_)
  change S.totRes M₂ hV hW ((S.D.res hV).f0 a • χ.1 x) =
    (S.D.res (hW.trans hV)).f0 a • S.totRes M₂ hV hW (χ.1 x)
  rw [S.totRes_smul0 M₂ hV hW ((S.D.res hV).f0 a)]
  refine congrArg (· • _) (Subtype.ext ?_)
  exact S.D.res_comp hV hW a

/-- The action of `a ∈ 𝒜⁰(X)` as an endomorphism of the sheaf `ℋ^n`. -/
private def actHom (a : ↥(S.𝒜X 0)) (n : ℤ) : S.homSh M₁ M₂ n ⟶ S.homSh M₁ M₂ n :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (S.actV M₁ M₂ a n (le_top : V.unop ≤ ⊤))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact (S.actV_res M₁ M₂ a n le_top (leOfHom f.unop) x).symm }⟩

/-- **C3.a(ii).** On compact Hausdorff `X`, every term of `ℋ(M₁, M₂)` is soft: `𝒜⁰(X)` acts by
`χ ↦ res_V(a)·χ` (S3.b(i), `S.isFine0`). -/
theorem isSoft_homSh [CompactSpace X] [T2Space X] (n : ℤ) : IsSoft (S.homSh M₁ M₂ n) := by
  let act : (ringOf S.A0).obj.obj (op ⊤) →+ (S.homSh M₁ M₂ n ⟶ S.homSh M₁ M₂ n) :=
    { toFun := fun a => S.actHom M₁ M₂ (a : ↥(S.𝒜X 0)) n
      map_zero' := by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
        apply ModuleCat.hom_ext
        refine DFunLike.ext _ _ fun x => ?_
        refine Subtype.ext (LinearMap.ext fun y => ?_)
        change (S.D.res (le_top : V.unop ≤ ⊤)).f0 0 • x.1 y = (0 : S.TotSec M₂ le_top)
        rw [map_zero, zero_smul]
      map_add' := fun (a b : ↥(S.𝒜X 0)) => by
        refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
        apply ModuleCat.hom_ext
        refine DFunLike.ext _ _ fun x => ?_
        refine Subtype.ext (LinearMap.ext fun y => ?_)
        change (S.D.res (le_top : V.unop ≤ ⊤)).f0 (a + b : ↥(S.𝒜X 0)) • x.1 y =
          (S.D.res (le_top : V.unop ≤ ⊤)).f0 (a : ↥(S.𝒜X 0)) • x.1 y +
            (S.D.res (le_top : V.unop ≤ ⊤)).f0 (b : ↥(S.𝒜X 0)) • x.1 y
        rw [map_add, add_smul] }
  refine IsSoft.of_action S.isFine0 (S.homSh M₁ M₂ n) act ?_ ?_
  · refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    refine Subtype.ext (LinearMap.ext fun y => ?_)
    change (S.D.res (le_top : V.unop ≤ ⊤)).f0 1 • x.1 y = x.1 y
    rw [map_one, one_smul]
  · intro ρ V hρ
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    refine Subtype.ext (LinearMap.ext fun y => ?_)
    change (S.D.res (le_top : V ≤ ⊤)).f0 ρ • x.1 y = (0 : S.TotSec M₂ le_top)
    rw [show (S.D.res (le_top : V ≤ ⊤)).f0 ρ = 0 from hρ, zero_smul]

end Global

end DgaSheafData

end Cohesive
