import Cohesivemodules.Algebra.Cone

set_option linter.style.header false

/-!
# Z2.e: maps into and out of cones, maps of cones

Blueprint item Z2.e (`blueprint/blueprint-tr.md` §3, §5), following Mathlib's
`CochainComplex.mappingCone.desc`, `lift` and `mapOfHomotopy`. For `φ ∈ Z⁰(M, N)` (any curvature):
* `coneInrZ0 φ`: `inr` as a closed map `N → C(φ)`;
* `coneDesc φ α β`: for `α ∈ Hom^{−1}(M, T)` and closed `β : N → T` with `δα = β ∘ φ`, the
  closed map `α ∘ fst + β ∘ snd : C(φ) → T` (`desc ∘ inl = α`, `desc ∘ inr = β`);
* `coneLift φ α β`: for closed `α ∈ Hom^1(T, M)` and `β ∈ Hom^0(T, N)` with `δβ = −φ ∘ α`, the
  closed map `inl ∘ α + inr ∘ β : T → C(φ)` (`fst ∘ lift = α`, `snd ∘ lift = β`);
* `coneMap`: for closed `a : M₁ → M₂`, `b : N₁ → N₂` and `h ∈ Hom^{−1}(M₁, N₂)` with
  `δh = b ∘ φ₁ − φ₂ ∘ a` (Mathlib's `Homotopy (φ₁ ≫ b) (a ≫ φ₂)`), the closed map of cones
  `desc (inl₂ ∘ a + inr₂ ∘ h) (inr₂ ∘ b)`, with `coneMap ∘ inr₁ = inr₂ ∘ b` and
  `fst₂ ∘ coneMap = a ∘ fst₁`.
-/

noncomputable section

namespace Cohesive

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable {M N T : CohesiveModule 𝒜} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive)

/-- Z2.e: `inr` is closed of degree `0`. -/
theorem coneInr_mem_Z0 : coneInr M N ∈ Z0 N.toQuasiCohesive (cone φ).toQuasiCohesive :=
  ⟨coneInr_mem_hom φ, δ_coneInr φ⟩

/-- **Z2.e.** `inr : N → C(φ)` as a closed degree-`0` map. -/
def coneInrZ0 : Z0 N.toQuasiCohesive (cone φ).toQuasiCohesive := ⟨coneInr M N, coneInr_mem_Z0 φ⟩

/-- Z2.e: the map underlying `coneDesc` is closed of degree `0`. -/
theorem coneDesc_mem (α : M.T →ₗ[k] T.T) (hα : α ∈ Hom M.toQuasiCohesive T.toQuasiCohesive (-1))
    (β : Z0 N.toQuasiCohesive T.toQuasiCohesive)
    (h : δ M.toQuasiCohesive T.toQuasiCohesive (-1) α = β.1 ∘ₗ φ.1) :
    α ∘ₗ coneFst M N + β.1 ∘ₗ coneSnd M N ∈ Z0 (cone φ).toQuasiCohesive T.toQuasiCohesive := by
  obtain ⟨hβ, hβδ⟩ := Submodule.mem_inf.1 β.2
  have hβδ' : δ N.toQuasiCohesive T.toQuasiCohesive 0 β.1 = 0 := LinearMap.mem_ker.1 hβδ
  refine ⟨?_, ?_⟩
  · have h1 := comp_mem _ _ _ hα (coneFst_mem_hom φ)
    have h2 := comp_mem _ _ _ hβ (coneSnd_mem_hom φ)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h1
    rw [add_zero] at h2
    exact Submodule.add_mem _ h1 h2
  · show δ (cone φ).toQuasiCohesive T.toQuasiCohesive 0
      (α ∘ₗ coneFst M N + β.1 ∘ₗ coneSnd M N) = 0
    have h1 := δ_comp (cone φ).toQuasiCohesive M.toQuasiCohesive T.toQuasiCohesive (-1) 1
      α (coneFst M N)
    have h2 := δ_comp (cone φ).toQuasiCohesive N.toQuasiCohesive T.toQuasiCohesive 0 0
      β.1 (coneSnd M N)
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h1
    rw [add_zero] at h2
    erw [map_add, h1, h2, δ_coneFst, hβδ', h, δ_coneSnd]
    simp only [LinearMap.comp_zero, smul_zero, Int.negOnePow_zero, one_smul]
    refine LinearMap.ext fun x => ?_
    change β.1 (φ.1 (coneFst M N x)) + 0 + (0 + β.1 (-(φ.1 (coneFst M N x)))) = 0
    rw [map_neg]
    abel

/-- **Z2.e.** Mathlib's `mappingCone.desc`: for `α ∈ Hom^{−1}(M, T)` and a closed `β : N → T`
with `δα = β ∘ φ`, the closed map `α ∘ fst + β ∘ snd : C(φ) → T`. -/
def coneDesc (α : M.T →ₗ[k] T.T) (hα : α ∈ Hom M.toQuasiCohesive T.toQuasiCohesive (-1))
    (β : Z0 N.toQuasiCohesive T.toQuasiCohesive)
    (h : δ M.toQuasiCohesive T.toQuasiCohesive (-1) α = β.1 ∘ₗ φ.1) :
    Z0 (cone φ).toQuasiCohesive T.toQuasiCohesive :=
  ⟨α ∘ₗ coneFst M N + β.1 ∘ₗ coneSnd M N, coneDesc_mem φ α hα β h⟩

/-- Z2.e: `coneDesc` (rfl). -/
theorem coneDesc_coe (α : M.T →ₗ[k] T.T) (hα : α ∈ Hom M.toQuasiCohesive T.toQuasiCohesive (-1))
    (β : Z0 N.toQuasiCohesive T.toQuasiCohesive)
    (h : δ M.toQuasiCohesive T.toQuasiCohesive (-1) α = β.1 ∘ₗ φ.1) :
    (coneDesc φ α hα β h).1 = α ∘ₗ coneFst M N + β.1 ∘ₗ coneSnd M N := rfl

/-- Z2.e: `desc ∘ inl = α`. -/
theorem coneDesc_coneInl (α : M.T →ₗ[k] T.T)
    (hα : α ∈ Hom M.toQuasiCohesive T.toQuasiCohesive (-1))
    (β : Z0 N.toQuasiCohesive T.toQuasiCohesive)
    (h : δ M.toQuasiCohesive T.toQuasiCohesive (-1) α = β.1 ∘ₗ φ.1) :
    (coneDesc φ α hα β h).1 ∘ₗ coneInl M N = α := by
  refine LinearMap.ext fun x => ?_
  have e1 := LinearMap.congr_fun (coneFst_coneInl M N) x
  have e2 := LinearMap.congr_fun (coneSnd_coneInl M N) x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at e1 e2
  change α (coneFst M N (coneInl M N x)) + β.1 (coneSnd M N (coneInl M N x)) = α x
  rw [e1, e2, map_zero, add_zero]

/-- Z2.e: `desc ∘ inr = β`. -/
theorem coneDesc_coneInr (α : M.T →ₗ[k] T.T)
    (hα : α ∈ Hom M.toQuasiCohesive T.toQuasiCohesive (-1))
    (β : Z0 N.toQuasiCohesive T.toQuasiCohesive)
    (h : δ M.toQuasiCohesive T.toQuasiCohesive (-1) α = β.1 ∘ₗ φ.1) :
    (coneDesc φ α hα β h).1 ∘ₗ coneInr M N = β.1 := by
  refine LinearMap.ext fun x => ?_
  have e1 := LinearMap.congr_fun (coneFst_coneInr M N) x
  have e2 := LinearMap.congr_fun (coneSnd_coneInr M N) x
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at e1 e2
  change α (coneFst M N (coneInr M N x)) + β.1 (coneSnd M N (coneInr M N x)) = β.1 x
  rw [e1, e2, map_zero, zero_add]

/-- Z2.e: the map underlying `coneLift` is closed of degree `0`. -/
theorem coneLift_mem (α : T.T →ₗ[k] M.T) (hα : α ∈ Hom T.toQuasiCohesive M.toQuasiCohesive 1)
    (hδα : δ T.toQuasiCohesive M.toQuasiCohesive 1 α = 0) (β : T.T →ₗ[k] N.T)
    (hβ : β ∈ Hom T.toQuasiCohesive N.toQuasiCohesive 0)
    (h : δ T.toQuasiCohesive N.toQuasiCohesive 0 β = -(φ.1 ∘ₗ α)) :
    coneInl M N ∘ₗ α + coneInr M N ∘ₗ β ∈ Z0 T.toQuasiCohesive (cone φ).toQuasiCohesive := by
  refine ⟨?_, ?_⟩
  · have h1 := comp_mem _ _ _ (coneInl_mem_hom φ) hα
    have h2 := comp_mem _ _ _ (coneInr_mem_hom φ) hβ
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h1
    rw [add_zero] at h2
    exact Submodule.add_mem _ h1 h2
  · show δ T.toQuasiCohesive (cone φ).toQuasiCohesive 0
      (coneInl M N ∘ₗ α + coneInr M N ∘ₗ β) = 0
    have h1 := δ_comp T.toQuasiCohesive M.toQuasiCohesive (cone φ).toQuasiCohesive (-1) 1
      (coneInl M N) α
    have h2 := δ_comp T.toQuasiCohesive N.toQuasiCohesive (cone φ).toQuasiCohesive 0 0
      (coneInr M N) β
    rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h1
    rw [add_zero] at h2
    erw [map_add, h1, h2, δ_coneInl, δ_coneInr, hδα, h]
    simp only [Int.negOnePow_zero, one_smul]
    refine LinearMap.ext fun x => ?_
    change coneInr M N (φ.1 (α x)) + 0 + (0 + coneInr M N (-(φ.1 (α x)))) = 0
    rw [map_neg]
    abel

/-- **Z2.e.** Mathlib's `mappingCone.lift`: for a closed `α ∈ Hom^1(T, M)` and `β ∈ Hom^0(T, N)`
with `δβ = −φ ∘ α`, the closed map `inl ∘ α + inr ∘ β : T → C(φ)`. -/
def coneLift (α : T.T →ₗ[k] M.T) (hα : α ∈ Hom T.toQuasiCohesive M.toQuasiCohesive 1)
    (hδα : δ T.toQuasiCohesive M.toQuasiCohesive 1 α = 0) (β : T.T →ₗ[k] N.T)
    (hβ : β ∈ Hom T.toQuasiCohesive N.toQuasiCohesive 0)
    (h : δ T.toQuasiCohesive N.toQuasiCohesive 0 β = -(φ.1 ∘ₗ α)) :
    Z0 T.toQuasiCohesive (cone φ).toQuasiCohesive :=
  ⟨coneInl M N ∘ₗ α + coneInr M N ∘ₗ β, coneLift_mem φ α hα hδα β hβ h⟩

/-- Z2.e: `fst ∘ lift = α`. -/
theorem coneFst_coneLift (α : T.T →ₗ[k] M.T)
    (hα : α ∈ Hom T.toQuasiCohesive M.toQuasiCohesive 1)
    (hδα : δ T.toQuasiCohesive M.toQuasiCohesive 1 α = 0) (β : T.T →ₗ[k] N.T)
    (hβ : β ∈ Hom T.toQuasiCohesive N.toQuasiCohesive 0)
    (h : δ T.toQuasiCohesive N.toQuasiCohesive 0 β = -(φ.1 ∘ₗ α)) :
    coneFst M N ∘ₗ (coneLift φ α hα hδα β hβ h).1 = α := by
  change coneFst M N ∘ₗ (coneInl M N ∘ₗ α + coneInr M N ∘ₗ β) = α
  rw [LinearMap.comp_add, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, coneFst_coneInl,
    coneFst_coneInr]
  simp

/-- Z2.e: `snd ∘ lift = β`. -/
theorem coneSnd_coneLift (α : T.T →ₗ[k] M.T)
    (hα : α ∈ Hom T.toQuasiCohesive M.toQuasiCohesive 1)
    (hδα : δ T.toQuasiCohesive M.toQuasiCohesive 1 α = 0) (β : T.T →ₗ[k] N.T)
    (hβ : β ∈ Hom T.toQuasiCohesive N.toQuasiCohesive 0)
    (h : δ T.toQuasiCohesive N.toQuasiCohesive 0 β = -(φ.1 ∘ₗ α)) :
    coneSnd M N ∘ₗ (coneLift φ α hα hδα β hβ h).1 = β := by
  change coneSnd M N ∘ₗ (coneInl M N ∘ₗ α + coneInr M N ∘ₗ β) = β
  rw [LinearMap.comp_add, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, coneSnd_coneInl,
    coneSnd_coneInr]
  simp

section Map

variable {M₁ N₁ M₂ N₂ : CohesiveModule 𝒜} (φ₁ : Z0 M₁.toQuasiCohesive N₁.toQuasiCohesive)
  (φ₂ : Z0 M₂.toQuasiCohesive N₂.toQuasiCohesive) (a : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive)
  (b : Z0 N₁.toQuasiCohesive N₂.toQuasiCohesive) (h : M₁.T →ₗ[k] N₂.T)
  (hh : h ∈ Hom M₁.toQuasiCohesive N₂.toQuasiCohesive (-1))
  (hδ : δ M₁.toQuasiCohesive N₂.toQuasiCohesive (-1) h = b.1 ∘ₗ φ₁.1 - φ₂.1 ∘ₗ a.1)

include hh in
/-- Z2.e: `inl₂ ∘ a + inr₂ ∘ h ∈ Hom^{−1}(M₁, C(φ₂))`. -/
theorem coneMap_α_mem :
    coneInl M₂ N₂ ∘ₗ a.1 + coneInr M₂ N₂ ∘ₗ h ∈
      Hom M₁.toQuasiCohesive (cone φ₂).toQuasiCohesive (-1) := by
  have h1 := comp_mem _ _ _ (coneInl_mem_hom φ₂) (Submodule.mem_inf.1 a.2).1
  have h2 := comp_mem _ _ _ (coneInr_mem_hom φ₂) hh
  rw [add_zero] at h1
  rw [zero_add] at h2
  exact add_mem h1 h2

include hδ in
/-- Z2.e: `δ(inl₂ ∘ a + inr₂ ∘ h) = (inr₂ ∘ b) ∘ φ₁` (`δ inl = inr φ`, `δh = bφ₁ − φ₂a`). -/
theorem coneMap_δ :
    δ M₁.toQuasiCohesive (cone φ₂).toQuasiCohesive (-1) (coneInl M₂ N₂ ∘ₗ a.1 + coneInr M₂ N₂ ∘ₗ h)
      = (compZ0 _ _ _ (coneInrZ0 φ₂) b).1 ∘ₗ φ₁.1 := by
  have haδ : δ M₁.toQuasiCohesive M₂.toQuasiCohesive 0 a.1 = 0 :=
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 a.2).2
  have h1 := δ_comp M₁.toQuasiCohesive M₂.toQuasiCohesive (cone φ₂).toQuasiCohesive (-1) 0
    (coneInl M₂ N₂) a.1
  have h2 := δ_comp M₁.toQuasiCohesive N₂.toQuasiCohesive (cone φ₂).toQuasiCohesive 0 (-1)
    (coneInr M₂ N₂) h
  rw [show (-1 : ℤ) + 0 = -1 by norm_num] at h1
  rw [show (0 : ℤ) + -1 = -1 by norm_num] at h2
  refine (map_add (δ M₁.toQuasiCohesive (cone φ₂).toQuasiCohesive (-1)) _ _).trans ?_
  erw [h1, h2, δ_coneInl, δ_coneInr, haδ, hδ, compZ0_apply]
  simp only [Int.negOnePow_zero, one_smul]
  refine LinearMap.ext fun x => ?_
  change coneInr M₂ N₂ (φ₂.1 (a.1 x)) + 0 +
    (0 + coneInr M₂ N₂ (b.1 (φ₁.1 x) - φ₂.1 (a.1 x))) = coneInr M₂ N₂ (b.1 (φ₁.1 x))
  rw [map_sub]
  abel

/-- **Z2.e.** Mathlib's `mappingCone.mapOfHomotopy`: a square `b ∘ φ₁ ≃ φ₂ ∘ a` commuting up to
the homotopy `h` (`δh = b ∘ φ₁ − φ₂ ∘ a`) gives the closed map of cones
`desc (inl₂ ∘ a + inr₂ ∘ h) (inr₂ ∘ b) : C(φ₁) → C(φ₂)`. -/
def coneMap : Z0 (cone φ₁).toQuasiCohesive (cone φ₂).toQuasiCohesive :=
  coneDesc φ₁ (coneInl M₂ N₂ ∘ₗ a.1 + coneInr M₂ N₂ ∘ₗ h) (coneMap_α_mem φ₂ a h hh)
    (compZ0 _ _ _ (coneInrZ0 φ₂) b) (coneMap_δ φ₁ φ₂ a b h hδ)

/-- Z2.e: `coneMap ∘ inr₁ = inr₂ ∘ b`. -/
theorem coneMap_coneInr :
    (coneMap φ₁ φ₂ a b h hh hδ).1 ∘ₗ coneInr M₁ N₁ = coneInr M₂ N₂ ∘ₗ b.1 := by
  exact coneDesc_coneInr φ₁ _ _ _ _

/-- Z2.e: `fst₂ ∘ coneMap = a ∘ fst₁`. -/
theorem coneFst_coneMap :
    coneFst M₂ N₂ ∘ₗ (coneMap φ₁ φ₂ a b h hh hδ).1 = a.1 ∘ₗ coneFst M₁ N₁ := by
  change coneFst M₂ N₂ ∘ₗ
    ((coneInl M₂ N₂ ∘ₗ a.1 + coneInr M₂ N₂ ∘ₗ h) ∘ₗ coneFst M₁ N₁ +
      (coneInr M₂ N₂ ∘ₗ b.1) ∘ₗ coneSnd M₁ N₁) = a.1 ∘ₗ coneFst M₁ N₁
  simp only [LinearMap.comp_add, LinearMap.add_comp, ← LinearMap.comp_assoc, coneFst_coneInl,
    coneFst_coneInr, LinearMap.id_comp, LinearMap.zero_comp, add_zero]

end Map

end Cohesive
