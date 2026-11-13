import Cohesivemodules.Algebra.ConeMaps
import Cohesivemodules.Algebra.ShiftHoP
import Cohesivemodules.Algebra.HoPZero
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

set_option linter.style.header false

/-!
# Z2.f1: the cone triangle and the distinguished triangles of `Ho(P_A)`

Blueprint item Z2.f (`blueprint/blueprint-tr.md` §3, §3c), following Mathlib's
`HomotopyCategory.Pretriangulated`. For `φ ∈ Z⁰(M, N)` (any curvature):
* `coneW φ = −ι₁⁻¹ ∘ fst ∈ Z⁰(C(φ), M[1])` (Mathlib's `(triangle φ).mor₃`, signs in
  `Scratch/P14_TR.lean`);
* `coneTriangle φ : M →[φ] N →[inr] C(φ) →[w_φ] M⟦1⟧` in `HoP 𝒜`;
* `distinguishedTriangles`: the triangles isomorphic to some `coneTriangle φ`;
* four of the five axioms of `Pretriangulated`: `isomorphic_distinguished`,
  `contractible_distinguished` (`C(id)` is zero: `δ(inl ∘ snd) = id`),
  `distinguished_cocone_triangle`, `complete_distinguished_triangle_morphism` (via `coneMap`,
  Z2.e). Rotation is Z2.f2 (`ConeRotate.lean`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Pretriangulated

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable {M N : CohesiveModule 𝒜} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive)

/-- **Z2.f.** The third map of the cone triangle, `w_φ = −ι₁⁻¹ ∘ fst : Tot(C(φ)) → Tot(M[1])`. -/
def coneW (M N : CohesiveModule 𝒜) : Tot 𝒜 (coneQ M N) →ₗ[k] Tot 𝒜 (shiftQ M.Q 1) :=
  -((shiftIota 𝒜 M.Q 1).symm.toLinearMap ∘ₗ coneFst M N)

/-- `ι_a⁻¹(β y) = (−1)^{a|β|} β ι_a⁻¹(y)`. -/
private theorem shiftIota_symm_smul' (M : CohesiveModule 𝒜) (a : ℤ) {p : ℤ} {β : A}
    (hβ : β ∈ 𝒜 p) (y : Tot 𝒜 M.Q) :
    (shiftIota 𝒜 M.Q a).symm (β • y) = (a * p).negOnePow • β • (shiftIota 𝒜 M.Q a).symm y := by
  apply (shiftIota 𝒜 M.Q a).injective
  rw [LinearEquiv.apply_symm_apply, Units.smul_def, map_zsmul, shiftIota_smul M.Q a hβ,
    LinearEquiv.apply_symm_apply, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

/-- `w_φ ∈ Hom⁰(C(φ), M[1])`. -/
private theorem coneW_mem_hom :
    coneW M N ∈ Hom (cone φ).toQuasiCohesive (M.shift 1).toQuasiCohesive 0 := by
  refine ⟨fun {m z} hz => ?_, fun {p β} hβ (z : Tot 𝒜 (coneQ M N)) => ?_⟩
  · rw [add_zero]
    have h1 := coneFst_mem_totDeg M N hz
    have h2 := (shiftIota_mem_totDeg_iff M.Q 1 m ((shiftIota 𝒜 M.Q 1).symm (coneFst M N z))).1
      (by rw [LinearEquiv.apply_symm_apply]; exact h1)
    exact neg_mem h2
  · change -(shiftIota 𝒜 M.Q 1).symm (coneFst M N (β • z)) =
      ((0 : ℤ) * p).negOnePow • β • -(shiftIota 𝒜 M.Q 1).symm (coneFst M N z)
    rw [coneFst_smul M N hβ, zero_mul, Int.negOnePow_zero, one_smul, one_mul, Units.smul_def,
      map_zsmul, shiftIota_symm_smul' M 1 hβ, one_mul]
    generalize p.negOnePow = s
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp

/-- `δ w_φ = 0`. -/
private theorem δ_coneW :
    δ (cone φ).toQuasiCohesive (M.shift 1).toQuasiCohesive 0 (coneW M N) = 0 := by
  refine LinearMap.ext fun (z : Tot 𝒜 (coneQ M N)) => ?_
  have h : M.X (coneFst M N z) - (1 : ℤ).negOnePow • coneFst M N (coneX φ z) = 0 :=
    LinearMap.congr_fun (δ_coneFst φ) z
  have h' : M.X (coneFst M N z) = -coneFst M N (coneX φ z) := by
    rw [Int.negOnePow_one] at h
    simp only [Units.neg_smul, one_smul, sub_neg_eq_add] at h
    exact eq_neg_of_add_eq_zero_left h
  change ((1 : ℤ).negOnePow • ((shiftIota 𝒜 M.Q 1).symm.toLinearMap ∘ₗ M.X ∘ₗ
      (shiftIota 𝒜 M.Q 1).toLinearMap)) (-(shiftIota 𝒜 M.Q 1).symm (coneFst M N z)) -
    (0 : ℤ).negOnePow • (-(shiftIota 𝒜 M.Q 1).symm (coneFst M N (coneX φ z))) = 0
  simp only [Int.negOnePow_one, Int.negOnePow_zero, map_neg, Units.neg_smul, one_smul]
  simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, h', map_neg, neg_neg, sub_self]

/-- Z2.f: `w_φ` is closed of degree `0`. -/
theorem coneW_mem_Z0 :
    coneW M N ∈ Z0 (cone φ).toQuasiCohesive (M.shift 1).toQuasiCohesive := by
  exact ⟨coneW_mem_hom φ, LinearMap.mem_ker.2 (δ_coneW φ)⟩

/-- **Z2.f.** `w_φ ∈ Z⁰(C(φ), M[1])`. -/
def coneWZ0 : Z0 (cone φ).toQuasiCohesive (M.shift 1).toQuasiCohesive :=
  ⟨coneW M N, coneW_mem_Z0 φ⟩

/-- **Z2.f.** [B, §2.4]. The cone triangle `M →[φ] N →[inr] C(φ) →[w_φ] M⟦1⟧` in `Ho(P_A)`
(Mathlib's `triangleh φ`). -/
def coneTriangle : Triangle (HoP 𝒜) :=
  Triangle.mk (X := (⟨M⟩ : HoP 𝒜)) (Y := ⟨N⟩) (Z := ⟨cone φ⟩)
    (Submodule.Quotient.mk φ) (Submodule.Quotient.mk (coneInrZ0 φ))
    (show (⟨cone φ⟩ : HoP 𝒜) ⟶ (⟨M⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from Submodule.Quotient.mk (coneWZ0 φ))

variable (𝒜) in
/-- **Z2.f.** The distinguished triangles of `Ho(P_A)`: those isomorphic to a cone triangle
`coneTriangle φ` for a closed degree-`0` map `φ` (Mathlib's `distinguishedTriangles`). -/
def distinguishedTriangles : Set (Triangle (HoP 𝒜)) :=
  {T | ∃ (M N : CohesiveModule 𝒜) (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive),
    Nonempty (T ≅ coneTriangle φ)}

/-- Z2.f: distinguished triangles are closed under isomorphism. -/
theorem isomorphic_distinguished (T₁ : Triangle (HoP 𝒜)) (hT₁ : T₁ ∈ distinguishedTriangles 𝒜)
    (T₂ : Triangle (HoP 𝒜)) (e : T₂ ≅ T₁) : T₂ ∈ distinguishedTriangles 𝒜 := by
  obtain ⟨M, N, φ, ⟨e'⟩⟩ := hT₁
  exact ⟨M, N, φ, ⟨e ≪≫ e'⟩⟩

/-- `inl ∘ snd ∈ Hom^{−1}(C(id), C(id))`. -/
private theorem inl_snd_mem (M : CohesiveModule 𝒜) :
    coneInl M M ∘ₗ coneSnd M M ∈ Hom (cone (idZ0 M.toQuasiCohesive)).toQuasiCohesive
      (cone (idZ0 M.toQuasiCohesive)).toQuasiCohesive (-1) := by
  have h := comp_mem _ _ _ (coneInl_mem_hom (idZ0 M.toQuasiCohesive))
    (coneSnd_mem_hom (idZ0 M.toQuasiCohesive))
  rwa [show (-1 : ℤ) + 0 = -1 by norm_num] at h

/-- `δ(inl ∘ snd) = id` on `C(id)`. -/
private theorem δ_inl_snd (M : CohesiveModule 𝒜) :
    δ (cone (idZ0 M.toQuasiCohesive)).toQuasiCohesive
      (cone (idZ0 M.toQuasiCohesive)).toQuasiCohesive (-1) (coneInl M M ∘ₗ coneSnd M M) =
      LinearMap.id := by
  have h := δ_comp (cone (idZ0 M.toQuasiCohesive)).toQuasiCohesive
    M.toQuasiCohesive (cone (idZ0 M.toQuasiCohesive)).toQuasiCohesive (-1) 0
    (coneInl M M) (coneSnd M M)
  rw [show (-1 : ℤ) + 0 = -1 by norm_num] at h
  erw [h, δ_coneInl, δ_coneSnd]
  refine LinearMap.ext fun (x : Tot 𝒜 (coneQ M M)) => ?_
  have h2 := LinearMap.congr_fun (coneInl_coneFst_add M M) x
  change coneInr M M (coneSnd M M x) + (-1 : ℤ).negOnePow • coneInl M M (-coneFst M M x) = x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at h2
  simp only [Int.negOnePow_neg, Int.negOnePow_one, map_neg, Units.neg_smul, one_smul, neg_neg]
  rw [add_comm]
  exact h2

/-- **Z2.f.** `X →[id] X → 0 → X⟦1⟧` is distinguished: it is isomorphic to the cone triangle of
`id_X`, whose cone is zero (`δ(inl ∘ snd) = id`, `isZero_of_contraction`). -/
theorem contractible_distinguished (X : HoP 𝒜) :
    contractibleTriangle X ∈ distinguishedTriangles 𝒜 := by
  obtain ⟨X⟩ := X
  refine ⟨X, X, idZ0 X.toQuasiCohesive, ⟨?_⟩⟩
  have h : Limits.IsZero (⟨cone (idZ0 X.toQuasiCohesive)⟩ : HoP 𝒜) :=
    isZero_of_contraction _ (inl_snd_mem X) (by erw [δ_inl_snd, sub_self]; simp)
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) h.isoZero.symm
    (by simp [coneTriangle]; rfl) (h.eq_of_tgt _ _) ((Limits.isZero_zero _).eq_of_src _ _)

/-- **Z2.f.** Every morphism of `Ho(P_A)` is the first map of a distinguished triangle (the cone
triangle of a representative). -/
theorem distinguished_cocone_triangle {X Y : HoP 𝒜} (f : X ⟶ Y) :
    ∃ (Z : HoP 𝒜) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles 𝒜 := by
  obtain ⟨φ, rfl⟩ : ∃ φ : Z0 X.as.toQuasiCohesive Y.as.toQuasiCohesive,
      Submodule.Quotient.mk φ = f := Submodule.Quotient.mk_surjective _ f
  exact ⟨⟨cone φ⟩, Submodule.Quotient.mk (coneInrZ0 φ),
    show (⟨cone φ⟩ : HoP 𝒜) ⟶ X⟦(1 : ℤ)⟧ from Submodule.Quotient.mk (coneWZ0 φ),
    X.as, Y.as, φ, ⟨Iso.refl _⟩⟩

/-- **Z2.f.** On cone triangles: closed `a`, `b` with `[b ∘ φ₁] = [φ₂ ∘ a]` in `Ho(P_A)` extend to a
morphism of triangles, with third component `[coneMap]` (Z2.e; `h` from `b φ₁ − φ₂ a ∈ B⁰`). -/
theorem exists_coneTriangle_hom {M₁ N₁ M₂ N₂ : CohesiveModule 𝒜}
    (φ₁ : Z0 M₁.toQuasiCohesive N₁.toQuasiCohesive) (φ₂ : Z0 M₂.toQuasiCohesive N₂.toQuasiCohesive)
    (a : (coneTriangle φ₁).obj₁ ⟶ (coneTriangle φ₂).obj₁)
    (b : (coneTriangle φ₁).obj₂ ⟶ (coneTriangle φ₂).obj₂)
    (hab : (coneTriangle φ₁).mor₁ ≫ b = a ≫ (coneTriangle φ₂).mor₁) :
    ∃ c : (coneTriangle φ₁).obj₃ ⟶ (coneTriangle φ₂).obj₃,
      (coneTriangle φ₁).mor₂ ≫ c = b ≫ (coneTriangle φ₂).mor₂ ∧
        (coneTriangle φ₁).mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ (coneTriangle φ₂).mor₃ := by
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive,
      Submodule.Quotient.mk a₀ = a := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : Z0 N₁.toQuasiCohesive N₂.toQuasiCohesive,
      Submodule.Quotient.mk b₀ = b := Submodule.Quotient.mk_surjective _ b
  have hab' : (Submodule.Quotient.mk (compZ0 _ _ _ b₀ φ₁) : H0 M₁.toQuasiCohesive N₂.toQuasiCohesive)
      = Submodule.Quotient.mk (compZ0 _ _ _ φ₂ a₀) := hab
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at hab'
  obtain ⟨h, hh, hδ⟩ := hab'
  refine ⟨Submodule.Quotient.mk (coneMap φ₁ φ₂ a₀ b₀ h hh hδ), ?_, ?_⟩
  · exact congrArg Submodule.Quotient.mk (Subtype.ext (coneMap_coneInr φ₁ φ₂ a₀ b₀ h hh hδ))
  · refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    refine LinearMap.ext fun (x : Tot 𝒜 (coneQ M₁ N₁)) => ?_
    have hf := LinearMap.congr_fun (coneFst_coneMap φ₁ φ₂ a₀ b₀ h hh hδ) x
    change (shiftIota 𝒜 M₂.Q 1).symm (a₀.1 ((shiftIota 𝒜 M₁.Q 1)
        (-(shiftIota 𝒜 M₁.Q 1).symm (coneFst M₁ N₁ x)))) =
      -(shiftIota 𝒜 M₂.Q 1).symm (coneFst M₂ N₂ ((coneMap φ₁ φ₂ a₀ b₀ h hh hδ).1 x))
    rw [map_neg, LinearEquiv.apply_symm_apply, map_neg, map_neg]
    exact congrArg (fun y => -(shiftIota 𝒜 M₂.Q 1).symm y) hf.symm

/-- **Z2.f.** Morphisms of distinguished triangles: a commutative square extends to a morphism of
triangles (reduce to cone triangles along the isomorphisms, `exists_coneTriangle_hom`). -/
theorem complete_distinguished_triangle_morphism (T₁ T₂ : Triangle (HoP 𝒜))
    (hT₁ : T₁ ∈ distinguishedTriangles 𝒜) (hT₂ : T₂ ∈ distinguishedTriangles 𝒜)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (hab : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧ T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨M₁, N₁, φ₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨M₂, N₂, φ₂, ⟨e₂⟩⟩ := hT₂
  have c1 := e₁.inv.comm₁
  have c2 := e₂.hom.comm₁
  have hab' : (coneTriangle φ₁).mor₁ ≫ (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) =
      (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁) ≫ (coneTriangle φ₂).mor₁ := by
    rw [reassoc_of% c1, reassoc_of% hab, Category.assoc, Category.assoc, c2]
  obtain ⟨c', hc₂, hc₃⟩ := exists_coneTriangle_hom φ₁ φ₂ _ _ hab'
  refine ⟨e₁.hom.hom₃ ≫ c' ≫ e₂.inv.hom₃, ?_, ?_⟩
  · have d1 := e₁.hom.comm₂
    have d2 := e₂.inv.comm₂
    rw [reassoc_of% d1, reassoc_of% hc₂]
    rw [d2]
    simp only [Iso.hom_inv_id_triangle_hom₂_assoc]
  · have d1 := e₁.hom.comm₃
    have d2 := e₂.inv.comm₃
    simp only [Category.assoc]
    rw [← d2, ← reassoc_of% hc₃, ← reassoc_of% d1]
    simp only [← Functor.map_comp, Category.assoc, Iso.hom_inv_id_triangle_hom₁_assoc,
      Iso.hom_inv_id_triangle_hom₁, Category.comp_id]

end Cohesive
