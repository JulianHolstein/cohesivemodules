import Cohesivemodules.Algebra.Lifting
import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.Localization
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Category.ModuleCat.Projective

set_option linter.style.header false

/-!
# A11.a: the cone condition from flatness and a quasi-isomorphism

Blueprint item A11.a ([A, proof of Prop 3.3.4, case 2]). The cone condition `ConeLift` used by the
lifting theorem (`lift_core`) holds when each `A^b` is flat over `A⁰`, `P` is a bounded-above
complex of projective `A⁰`-modules and `e₀ : P → (Q, 𝕏⁰)` is a quasi-isomorphism:
* `A^b ⊗_{A⁰} -` is exact (flatness), so `A^b ⊗ e₀` is a quasi-isomorphism and its mapping cone
  is acyclic (`cone_acyclic`);
* `P` is K-projective (Mathlib `isKProjective_of_projective`), so every cocycle from `P` into an
  acyclic complex is a coboundary (`kproj_eq_δ`);
* a cocycle into the cone is exactly a pair `(K, L)` satisfying the cycle conditions of
  `ConeLift`, and a preimage gives `(φ, ψ)` (`cone_lift`).
The translation between pure maps of form degree `b` and Mathlib cochains `P → A^b ⊗ X` carries
the sign `(-1)^{bn}` (the leading operator `𝕏̂⁰` acts on `A^b ⊗ X` with the sign `(-1)^b`).

The last section states A11 in blueprint form (`lifting`): `P` a bounded Mathlib complex of
finitely generated projective `A⁰`-modules, `e₀ : P → (Q, 𝕏⁰)` (`QuasiCohesive.complex0`) a
quasi-isomorphism, each `A^b` flat over `A⁰`.

This file is split off from `Lifting.lean` (blueprint §7 lists A11–A12 in `Lifting.lean`) only to
keep file sizes manageable.

Part 1 of 2 of the original `Algebra/LiftingCone.lean`, split for size; continued in
`Algebra/LiftingCone.lean`.
-/

noncomputable section

open CategoryTheory

/-! ## Homological algebra in an abelian category -/

namespace CochainComplex

open HomComplex HomotopyCategory

variable {C : Type*} [Category C] [Abelian C]

/-- A11.a: the mapping cone of a quasi-isomorphism is acyclic. -/
theorem cone_acyclic {X Y : CochainComplex C ℤ} (f : X ⟶ Y) [QuasiIso f] :
    (mappingCone f).Acyclic := by
  have h1 : HomotopyCategory.quasiIso C _ ((HomotopyCategory.quotient _ _).map f) :=
    (quotient_map_mem_quasiIso_iff f).2 ((HomologicalComplex.mem_quasiIso_iff f).2 inferInstance)
  rw [quasiIso_eq_trW_subcategoryAcyclic] at h1
  have := ((subcategoryAcyclic C).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 h1
  exact (quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 this

/-- A11.a: shifts of acyclic complexes are acyclic. -/
theorem acyclic_shift {L : CochainComplex C ℤ} (hL : L.Acyclic) (n : ℤ) : (L⟦n⟧).Acyclic := by
  rw [← quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hL ⊢
  exact ObjectProperty.prop_of_iso _
    (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso n).symm.app L)
    ((subcategoryAcyclic C).le_shift n _ hL)

set_option backward.defeqAttrib.useBackward true in
/-- A11.a: a cocycle from a K-projective complex into an acyclic complex is a coboundary (the
K-projective analogue of Mathlib's `IsKInjective.eq_δ_of_cocycle'`, with the same proof). -/
theorem kproj_eq_δ {K L : CochainComplex C ℤ} {n : ℤ}
    (z : Cocycle K L n) [K.IsKProjective] (hL : L.Acyclic) (m : ℤ) (hm : m + 1 = n) :
    ∃ (α : Cochain K L m), δ m n α = z.1 := by
  obtain ⟨φ, hφ⟩ := (Cocycle.equivHom ..).surjective (z.rightShift n 0 (zero_add n))
  rw [Cocycle.ext_iff] at hφ
  dsimp at hφ
  obtain ⟨h⟩ := IsKProjective.nonempty_homotopy_zero φ (acyclic_shift hL n)
  obtain ⟨f, hf⟩ := Cochain.equivHomotopy _ _ h
  simp only [Int.reduceNeg, Cochain.ofHom_zero, add_zero] at hf
  refine ⟨n.negOnePow • Cochain.rightUnshift f m (by lia), ?_⟩
  apply (Cochain.rightShiftAddEquiv _ _ _ n 0 (by simp)).injective
  dsimp
  rw [← hφ, hf, δ_units_smul, Cochain.rightShift_units_smul,
    Cochain.δ_rightUnshift _ _ _ _ 0 (by simp)]
  simp [smul_smul]

/-- A11.a: the components of a cochain into a mapping cone, and their differentials. -/
theorem cone_components {K F G : CochainComplex C ℤ} (f : F ⟶ G) {n₀ n₁ n₂ : ℤ}
    (h₀ : n₀ + 1 = n₁) (h₁ : n₁ + 1 = n₂)
    (α : Cochain K F n₂) (β : Cochain K G n₁) (w : Cochain K (mappingCone f) n₀)
    (hw : δ n₀ n₁ w = mappingCone.liftCochain f α β h₁) :
    δ n₁ n₂ (w.comp (mappingCone.fst f).1 h₀) = -α ∧
      δ n₀ n₁ (w.comp (mappingCone.snd f) (add_zero n₀)) +
        (w.comp (mappingCone.fst f).1 h₀).comp (Cochain.ofHom f) (add_zero n₁) = β := by
  have hw' : w = mappingCone.liftCochain f (w.comp (mappingCone.fst f).1 h₀)
      (w.comp (mappingCone.snd f) (add_zero n₀)) h₀ := by
    rw [mappingCone.ext_cochain_to_iff _ _ n₁ h₀]
    simp
  rw [hw', mappingCone.δ_liftCochain f _ _ _ n₂ h₁] at hw
  have hw2 : mappingCone.liftCochain f (-δ n₁ n₂ (w.comp (mappingCone.fst f).1 h₀))
      (δ n₀ n₁ (w.comp (mappingCone.snd f) (add_zero n₀)) +
        (w.comp (mappingCone.fst f).1 h₀).comp (Cochain.ofHom f) (add_zero n₁)) h₁ =
      mappingCone.liftCochain f α β h₁ := by
    rw [← hw, mappingCone.liftCochain, Cochain.neg_comp]
  have e1 := congrArg (fun γ => γ.comp (mappingCone.fst f).1 h₁) hw2
  have e2 := congrArg (fun γ => γ.comp (mappingCone.snd f) (add_zero n₁)) hw2
  simp only [mappingCone.liftCochain_fst, mappingCone.liftCochain_snd] at e1 e2
  exact ⟨by rw [← neg_neg (δ n₁ n₂ _), e1], e2⟩

/-- **A11.a** Lifting through the cone of a quasi-isomorphism: if `K` is K-projective and
`f : F → G` is a quasi-isomorphism, every pair `(α, β)` with `δα = 0` and `δβ + α f = 0` is
`(-δx, δy + x f)` for some `(x, y)` (the cone of `f ∘ -` is acyclic in `Hom(K, -)`). -/
theorem cone_lift {K F G : CochainComplex C ℤ} [K.IsKProjective] (f : F ⟶ G) [QuasiIso f]
    {n₀ n₁ n₂ n₃ : ℤ} (h₀ : n₀ + 1 = n₁) (h₁ : n₁ + 1 = n₂) (h₂ : n₂ + 1 = n₃)
    (α : Cochain K F n₂) (β : Cochain K G n₁) (hα : δ n₂ n₃ α = 0)
    (hβ : δ n₁ n₂ β + α.comp (Cochain.ofHom f) (add_zero n₂) = 0) :
    ∃ (x : Cochain K F n₁) (y : Cochain K G n₀), δ n₁ n₂ x = -α ∧
      δ n₀ n₁ y + x.comp (Cochain.ofHom f) (add_zero n₁) = β := by
  let z := mappingCone.liftCocycle f (Cocycle.mk α n₃ h₂ hα) β h₁ hβ
  obtain ⟨w, hw⟩ := kproj_eq_δ z (cone_acyclic f) n₀ h₀
  exact ⟨_, _, cone_components f h₀ h₁ α β w hw⟩

end CochainComplex

/-! ## Pure maps of form degree `b` as Mathlib cochains -/

namespace Cohesive

open TensorProduct DirectSum MonoidalCategory CochainComplex HomComplex

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

section Translation

variable (Xc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ)

/-- A11.a: the generator family of a Mathlib complex of `A⁰`-modules. -/
abbrev Gens : ℤ → Type := fun j => Xc.X j

/-- A11.a: the differential of a Mathlib complex on the direct sum of its terms. -/
def dGen : (⨁ j, Gens Xc j) →ₗ[𝒜 0] (⨁ j, Gens Xc j) :=
  DirectSum.toModule (𝒜 0) ℤ _ fun j => lof (𝒜 0) ℤ (Gens Xc) (j + 1) ∘ₗ (Xc.d j (j + 1)).hom

variable {Xc} in
/-- A11.a: a chain map on the direct sums of the terms. -/
def genMap {Yc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ} (f : Xc ⟶ Yc) :
    (⨁ j, Gens Xc j) →ₗ[𝒜 0] (⨁ j, Gens Yc j) :=
  DirectSum.toModule (𝒜 0) ℤ _ fun j => lof (𝒜 0) ℤ (Gens Yc) j ∘ₗ (f.f j).hom

variable (𝒜) in
/-- A11.a: the `A⁰`-module `A^b`. -/
abbrev pieceMod (b : ℤ) : ModuleCat.{0} (𝒜 0) := ModuleCat.of (𝒜 0) (GCDga.piece 𝒜 b)

/-- A11.a: the complex `A^b ⊗_{A⁰} X` (Mathlib's `tensorLeft`, applied termwise). -/
abbrev tensC (b : ℤ) : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ :=
  ((tensorLeft (pieceMod 𝒜 b)).mapHomologicalComplex _).obj Xc

variable {Xc} in
/-- A11.a: the chain map `A^b ⊗ f`. -/
abbrev tensMap (b : ℤ) {Yc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ} (f : Xc ⟶ Yc) :
    tensC Xc b ⟶ tensC Yc b :=
  ((tensorLeft (pieceMod 𝒜 b)).mapHomologicalComplex _).map f

variable (𝒜) in
/-- A11.a: the projection `A → A^b` as an `A⁰`-linear map. -/
def projPiece (b : ℤ) : A →ₗ[𝒜 0] GCDga.piece 𝒜 b :=
  LinearMap.codRestrict (GCDga.piece 𝒜 b) (GCDga.proj 𝒜 b) fun a => GCDga.proj_mem 𝒜 b a

/-- A11.a: `A^b ⊗ X^j → A ⊗_{A⁰} ⨁ X`, `a ⊗ y ↦ a ⊗ (y in degree j)`. -/
def pieceTot (b j : ℤ) : GCDga.piece 𝒜 b ⊗[𝒜 0] Xc.X j →ₗ[𝒜 0] Tot 𝒜 (Gens Xc) :=
  TensorProduct.lift (LinearMap.mk₂ (𝒜 0)
    (fun a y => Tot.tmul 𝒜 (Gens Xc) (a : A) (lof (𝒜 0) ℤ (Gens Xc) j y))
    (fun a a' y => by rw [Submodule.coe_add, Tot.add_tmul])
    (fun r a y => by
      rw [GCDga.coe_smul_piece, ← Tot.smul_tmul, Tot.smul0_eq])
    (fun a y y' => by rw [map_add, Tot.tmul_add])
    (fun r a y => by
      rw [map_smul, Tot.tmul_smul0, ← GCDga.central 𝒜 r.2, ← Tot.smul_tmul, Tot.smul0_eq]))

/-- A11.a: the extraction `A ⊗_{A⁰} ⨁ X → A^b ⊗ X^j`, `a ⊗ e ↦ a_b ⊗ e_j`. -/
def extr (b j : ℤ) : Tot 𝒜 (Gens Xc) →ₗ[𝒜 0] GCDga.piece 𝒜 b ⊗[𝒜 0] Xc.X j :=
  TensorProduct.map (projPiece 𝒜 b) (DirectSum.component (𝒜 0) ℤ (Gens Xc) j)

variable {Xc}

/-- A11.a: `pieceTot` on pure tensors. -/
theorem pieceTot_tmul (b j : ℤ) (a : GCDga.piece 𝒜 b) (y : Xc.X j) :
    pieceTot Xc b j (a ⊗ₜ y) = Tot.tmul 𝒜 (Gens Xc) (a : A) (lof (𝒜 0) ℤ (Gens Xc) j y) := rfl

/-- A11.a: `extr` on pure tensors. -/
theorem extr_tmul (b j : ℤ) (a : A) (e : ⨁ i, Gens Xc i) :
    extr Xc b j (Tot.tmul 𝒜 (Gens Xc) a e) = projPiece 𝒜 b a ⊗ₜ e j := rfl

/-- A11.a: `π_b(a) = a` for `a ∈ A^b`. -/
theorem projPiece_of_mem {b : ℤ} (a : GCDga.piece 𝒜 b) : projPiece 𝒜 b (a : A) = a := by
  apply Subtype.ext
  show GCDga.proj 𝒜 b (a : A) = a
  rw [GCDga.proj_of_mem 𝒜 ((GCDga.mem_piece 𝒜).1 a.2)]
  simp only [↓reduceIte]

/-- A11.a: `extr ∘ pieceTot = id`. -/
theorem extr_pieceTot (b j : ℤ) (t : GCDga.piece 𝒜 b ⊗[𝒜 0] Xc.X j) :
    extr Xc b j (pieceTot Xc b j t) = t := by
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    rw [pieceTot_tmul, extr_tmul, projPiece_of_mem, lof_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- A11.a: `pieceTot` lands in form degree `b`. -/
theorem projF_pieceTot (b j : ℤ) (t : GCDga.piece 𝒜 b ⊗[𝒜 0] Xc.X j) :
    Tot.projF 𝒜 (Gens Xc) b (pieceTot Xc b j t) = pieceTot Xc b j t := by
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    rw [pieceTot_tmul, Tot.projF_tmul_of_mem ((GCDga.mem_piece 𝒜).1 a.2)]
    simp only [↓reduceIte]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- A11.a: `pieceTot` lands in total degree `b + j`. -/
theorem pieceTot_mem (b j : ℤ) (t : GCDga.piece 𝒜 b ⊗[𝒜 0] Xc.X j) :
    pieceTot Xc b j t ∈ totDeg 𝒜 (Gens Xc) (b + j) := by
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    rw [pieceTot_tmul]
    exact tmul_mem_totDeg (Q := Gens Xc) ((GCDga.mem_piece 𝒜).1 a.2) (show Gens Xc j from y)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- A11.a: the `k`-action on the total module is the action of `algebraMap k A r ∈ A⁰`. -/
theorem Tot.smul_k_eq_smul0 {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    (r : k) (y : Tot 𝒜 Q) :
    r • y = (⟨algebraMap k A r, SetLike.algebraMap_mem_graded 𝒜 r⟩ : 𝒜 0) • y := by
  rw [Tot.smul0_eq, algebraMap_smul]

/-- A11.a: on total degree `m = b + j`, `pieceTot ∘ extr` is the identity on form degree `b`. -/
theorem pieceTot_extr {b j m : ℤ} (hj : b + j = m) {y : Tot 𝒜 (Gens Xc)}
    (hy : y ∈ totDeg 𝒜 (Gens Xc) m) :
    pieceTot Xc b j (extr Xc b j (Tot.projF 𝒜 (Gens Xc) b y)) = Tot.projF 𝒜 (Gens Xc) b y := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, hqp, ha, rfl⟩ := hx
    change pieceTot Xc b j (extr Xc b j (Tot.projF 𝒜 (Gens Xc) b
      (Tot.tmul 𝒜 (Gens Xc) a (lof (𝒜 0) ℤ (Gens Xc) p e)))) =
      Tot.projF 𝒜 (Gens Xc) b (Tot.tmul 𝒜 (Gens Xc) a (lof (𝒜 0) ℤ (Gens Xc) p e))
    simp only [Tot.projF_tmul_of_mem ha]
    split_ifs with h
    · subst h
      obtain rfl : p = j := by omega
      rw [extr_tmul, lof_apply, pieceTot_tmul]
      have : ((projPiece 𝒜 q a : GCDga.piece 𝒜 q) : A) = a := by
        show GCDga.proj 𝒜 q a = a
        rw [GCDga.proj_of_mem 𝒜 ha]
        simp only [↓reduceIte]
      rw [this]
    · rw [map_zero, map_zero]
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | smul r x _ hx =>
    rw [Tot.projF_smul_k, Tot.smul_k_eq_smul0, map_smul, map_smul, hx]

omit [GCDga 𝒜] in
variable (Xc) in
/-- A11.a: `∂(y in degree j) = d y in degree j + 1`. -/
theorem dGen_lof (j : ℤ) (y : Xc.X j) :
    dGen Xc (lof (𝒜 0) ℤ (Gens Xc) j y) =
      lof (𝒜 0) ℤ (Gens Xc) (j + 1) ((Xc.d j (j + 1)).hom y) :=
  DirectSum.toModule_lof _ _ _

/-- A11.a: the component of `∂e` in degree `j + 1` is `d(e_j)`. -/
theorem dGen_apply (j : ℤ) (e : ⨁ i, Gens Xc i) :
    dGen Xc e (j + 1) = (Xc.d j (j + 1)).hom (e j) := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    rw [show DirectSum.of (Gens Xc) p x = lof (𝒜 0) ℤ (Gens Xc) p x from rfl, dGen_lof]
    by_cases h : p = j
    · subst h
      rw [lof_apply, lof_apply]
    · rw [show (lof (𝒜 0) ℤ (Gens Xc) (p + 1) ((Xc.d p (p + 1)).hom x)) (j + 1) = 0 from
          DFinsupp.single_eq_of_ne (by omega),
        show (lof (𝒜 0) ℤ (Gens Xc) p x) j = 0 from DFinsupp.single_eq_of_ne (Ne.symm h),
        map_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy, map_add]

variable {Yc : CochainComplex (ModuleCat.{0} (𝒜 0)) ℤ}

/-- A11.a: the component of `f e` in degree `j` is `f(e_j)`. -/
theorem genMap_apply (f : Xc ⟶ Yc) (j : ℤ) (e : ⨁ i, Gens Xc i) :
    genMap f e j = (f.f j).hom (e j) := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p x =>
    rw [show DirectSum.of (Gens Xc) p x = lof (𝒜 0) ℤ (Gens Xc) p x from rfl, genMap,
      DirectSum.toModule_lof]
    by_cases h : p = j
    · subst h
      rw [LinearMap.comp_apply, lof_apply, lof_apply]
    · rw [LinearMap.comp_apply,
        show (lof (𝒜 0) ℤ (Gens Yc) p ((f.f p).hom x)) j = 0 from
          DFinsupp.single_eq_of_ne (Ne.symm h),
        show (lof (𝒜 0) ℤ (Gens Xc) p x) j = 0 from DFinsupp.single_eq_of_ne (Ne.symm h),
        map_zero]
  | add x y hx hy => rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy, map_add]

omit [GCDga 𝒜] in
/-- A11.a: an element of degree `m` is concentrated in degree `m`. -/
theorem concAt_lof {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    (m : ℤ) (y : Q m) : Tot.ConcAt m (lof (𝒜 0) ℤ Q m y) :=
  fun _ hi => DFinsupp.single_eq_of_ne hi

omit [GCDga 𝒜] in
/-- A11.a: `f(y in degree j) = f y in degree j`. -/
theorem genMap_lof (f : Xc ⟶ Yc) (j : ℤ) (y : Xc.X j) :
    genMap f (lof (𝒜 0) ℤ (Gens Xc) j y) = lof (𝒜 0) ℤ (Gens Yc) j ((f.f j).hom y) :=
  DirectSum.toModule_lof _ _ _

/-- A11.a: `π_b ∘ τ₁ = (-1)^b π_b`. -/
theorem projPiece_twist_one (b : ℤ) (a : A) :
    projPiece 𝒜 b (GCDga.twist 𝒜 1 a) = b.negOnePow • projPiece 𝒜 b a := by
  apply Subtype.ext
  show GCDga.proj 𝒜 b (GCDga.twist 𝒜 1 a) = ((b.negOnePow • projPiece 𝒜 b a :
    GCDga.piece 𝒜 b) : A)
  rw [proj_twist, GCDga.twist_of_mem 𝒜 1 (GCDga.proj_mem 𝒜 b a), one_mul, Units.smul_def,
    Units.smul_def]
  rfl

/-- A11.a: `extr ∘ ∂̂ = (-1)^b (1 ⊗ d) ∘ extr`: the leading operator acts on `A^b ⊗ X` with the
sign `(-1)^b`. -/
theorem extr_hatGen_d (b j : ℤ) (y : Tot 𝒜 (Gens Xc)) :
    extr Xc b (j + 1) (hatGen 1 (dGen Xc) y) =
      b.negOnePow • ((tensC Xc b).d j (j + 1)).hom (extr Xc b j y) := by
  induction y using Tot.induction_on with
  | ht a e =>
    rw [hatGen_tmul, extr_tmul, extr_tmul, dGen_apply, projPiece_twist_one,
      ← TensorProduct.smul_tmul']
    rfl
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]

/-- A11.a: `extr ∘ f̂ = (1 ⊗ f) ∘ extr` for a chain map `f`. -/
theorem extr_hatGen_map (f : Xc ⟶ Yc) (b j : ℤ) (y : Tot 𝒜 (Gens Xc)) :
    extr Yc b j (hatGen 0 (genMap f) y) = ((tensMap b f).f j).hom (extr Xc b j y) := by
  induction y using Tot.induction_on with
  | ht a e =>
    rw [hatGen_tmul, extr_tmul, extr_tmul, genMap_apply, GCDga.twist_zero]
    rfl
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Translation

end Cohesive
end
