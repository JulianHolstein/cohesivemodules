import Cohesivemodules.Algebra.ConeTriangle

set_option linter.style.header false

/-!
# Z2.f2: rotation of cone triangles

Blueprint item Z2.f (`blueprint/blueprint-tr.md` §3c, "Rotation"), following Mathlib's
`CochainComplex.mappingCone.rotateHomotopyEquiv` and `rotateTrianglehIso`. For `φ ∈ Z⁰(M, N)` and
`ψ := inr_φ ∈ Z⁰(N, C(φ))` (primes: structure maps of `C(ψ)`):
* `rotHom φ := lift_ψ (φ ∘ ι₁) (−inl ∘ ι₁) : M[1] → C(ψ)`, `rotInv φ := desc_ψ 0 w_φ : C(ψ) → M[1]`;
* `rotInv ∘ rotHom = id`; `rotHom ∘ rotInv − id = δH`, `H = −inl' ∘ snd ∘ snd'`;
* `rotHom ∘ w_φ − inr' = δH₂`, `H₂ = −inl' ∘ snd`; `w_ψ ∘ rotHom = −φ[1]` (`φ[1] = ι₁⁻¹ φ ι₁`);
* `rotateTriangleIso φ : (coneTriangle φ).rotate ≅ coneTriangle ψ` (components `id`, `id`,
  `[rotHom]`), hence `rotate_distinguished'`: rotations of distinguished triangles are
  distinguished.
The `leftShift` signs of Mathlib's formulas are absorbed (blueprint-tr §3c).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Pretriangulated

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable {M N : CohesiveModule 𝒜} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive)

/-- Z2.f2: `ι₁ : Tot(M[1]) → Tot(M)` as a linear map. -/
abbrev ι₁ (M : CohesiveModule 𝒜) : (M.shift 1).T →ₗ[k] M.T := (shiftIota 𝒜 M.Q 1).toLinearMap

/-- Z2.f2: `φ ∘ ι₁ ∈ Hom^1(M[1], N)`. -/
theorem rot_α_mem : φ.1 ∘ₗ ι₁ M ∈ Hom (M.shift 1).toQuasiCohesive N.toQuasiCohesive 1 := by
  have h := comp_mem _ _ _ (Submodule.mem_inf.1 φ.2).1 (shiftIota_mem_hom M 1)
  rwa [zero_add] at h

/-- Z2.f2: `φ ∘ ι₁` is closed. -/
theorem rot_δα : δ (M.shift 1).toQuasiCohesive N.toQuasiCohesive 1 (φ.1 ∘ₗ ι₁ M) = 0 := by
  have h := δ_comp (M.shift 1).toQuasiCohesive M.toQuasiCohesive N.toQuasiCohesive 0 1 φ.1
    (ι₁ M)
  rw [zero_add] at h
  rw [h, LinearMap.mem_ker.1 (Submodule.mem_inf.1 φ.2).2, δ_shiftIota]
  simp

/-- Z2.f2: `−inl ∘ ι₁ ∈ Hom^0(M[1], C(φ))`. -/
theorem rot_β_mem :
    -(coneInl M N ∘ₗ ι₁ M) ∈ Hom (M.shift 1).toQuasiCohesive (cone φ).toQuasiCohesive 0 := by
  have h := comp_mem _ _ _ (coneInl_mem_hom φ) (shiftIota_mem_hom M 1)
  rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  exact neg_mem h

/-- Z2.f2: `δ(−inl ∘ ι₁) = −inr_φ ∘ (φ ∘ ι₁)`. -/
theorem rot_δβ :
    δ (M.shift 1).toQuasiCohesive (cone φ).toQuasiCohesive 0 (-(coneInl M N ∘ₗ ι₁ M)) =
      -((coneInrZ0 φ).1 ∘ₗ (φ.1 ∘ₗ ι₁ M)) := by
  have h := δ_comp (M.shift 1).toQuasiCohesive M.toQuasiCohesive (cone φ).toQuasiCohesive (-1) 1
    (coneInl M N) (ι₁ M)
  rw [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  erw [map_neg, h, δ_coneInl, δ_shiftIota]
  erw [LinearMap.comp_zero, smul_zero, add_zero]
  rfl

/-- **Z2.f2.** Mathlib's `rotateHomotopyEquiv.hom`:
`lift_{inr_φ} (φ ∘ ι₁) (−inl ∘ ι₁) : M[1] → C(inr_φ)`. -/
def rotHom : Z0 (M.shift 1).toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive :=
  coneLift (coneInrZ0 φ) (φ.1 ∘ₗ ι₁ M) (rot_α_mem φ) (rot_δα φ) (-(coneInl M N ∘ₗ ι₁ M))
    (rot_β_mem φ) (rot_δβ φ)

/-- Z2.f2: `δ 0 = w_φ ∘ inr_φ` (both are `0`: `fst ∘ inr = 0`). -/
theorem rotInv_cond :
    δ N.toQuasiCohesive (M.shift 1).toQuasiCohesive (-1) 0 = (coneWZ0 φ).1 ∘ₗ (coneInrZ0 φ).1 := by
  rw [map_zero]
  change 0 = coneW M N ∘ₗ coneInr M N
  rw [coneW, LinearMap.neg_comp, LinearMap.comp_assoc, coneFst_coneInr, LinearMap.comp_zero,
    neg_zero]

/-- **Z2.f2.** Mathlib's `rotateHomotopyEquiv.inv`: `desc_{inr_φ} 0 w_φ : C(inr_φ) → M[1]`. -/
def rotInv : Z0 (cone (coneInrZ0 φ)).toQuasiCohesive (M.shift 1).toQuasiCohesive :=
  coneDesc (coneInrZ0 φ) 0 (Submodule.zero_mem _) (coneWZ0 φ) (rotInv_cond φ)

/-- **Z2.f2.** `rotInv ∘ rotHom = id`. -/
theorem rotInv_rotHom : (rotInv φ).1 ∘ₗ (rotHom φ).1 = LinearMap.id := by
  refine LinearMap.ext fun (x : (M.shift 1).T) => ?_
  have e1 := LinearMap.congr_fun (coneSnd_coneInl N (cone φ)) (φ.1 (ι₁ M x))
  have e2 : coneSnd N (cone φ) (coneInr N (cone φ) (-(coneInl M N (ι₁ M x)) : (cone φ).T)) =
      -(coneInl M N (ι₁ M x)) :=
    LinearMap.congr_fun (coneSnd_coneInr N (cone φ)) (-(coneInl M N (ι₁ M x)) : (cone φ).T)
  have e3 := LinearMap.congr_fun (coneFst_coneInl M N) (ι₁ M x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at e1 e3
  have key : ∀ y, (rotInv φ).1 y = (coneWZ0 φ).1 (coneSnd N (cone φ) y) :=
    fun y => zero_add _
  have hx : (rotHom φ).1 x = coneInl N (cone φ) (φ.1 (ι₁ M x)) +
      coneInr N (cone φ) (-(coneInl M N (ι₁ M x))) := rfl
  change (rotInv φ).1 ((rotHom φ).1 x) = x
  rw [key, hx, map_add, e1]
  erw [e2, zero_add]
  change -((shiftIota 𝒜 M.Q 1).symm (coneFst M N (-(coneInl M N (ι₁ M x))))) = x
  rw [map_neg, e3]
  rw [map_neg, neg_neg]
  exact LinearEquiv.symm_apply_apply _ _

/-- Z2.f2: the homotopy `H = −inl' ∘ snd ∘ snd' ∈ Hom^{−1}(C(ψ), C(ψ))`. -/
theorem rotH_mem :
    -(coneInl N (cone φ) ∘ₗ coneSnd M N ∘ₗ coneSnd N (cone φ)) ∈
      Hom (cone (coneInrZ0 φ)).toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive (-1) := by
  have h := comp_mem _ _ _ (coneInl_mem_hom (coneInrZ0 φ))
    (comp_mem _ _ _ (coneSnd_mem_hom φ) (coneSnd_mem_hom (coneInrZ0 φ)))
  rw [show (-1 : ℤ) + (0 + 0) = -1 by norm_num] at h
  exact neg_mem h

/-- Z2.f2: typing helper, `inl : M → C(φ)` with codomain `(cone φ).T`. -/
private abbrev φl : M.T →ₗ[k] (cone φ).T := coneInl M N

/-- Z2.f2: typing helper, `inr : N → C(φ)` with codomain `(cone φ).T`. -/
private abbrev φr : N.T →ₗ[k] (cone φ).T := coneInr M N

/-- Z2.f2: typing helper, `fst : C(φ) → M` with domain `(cone φ).T`. -/
private abbrev φf : (cone φ).T →ₗ[k] M.T := coneFst M N

/-- Z2.f2: typing helper, `snd : C(φ) → N` with domain `(cone φ).T`. -/
private abbrev φs : (cone φ).T →ₗ[k] N.T := coneSnd M N

/-- Z2.f2: typing helper, `inl' : N → C(ψ)` with codomain `(cone ψ).T`. -/
private abbrev ψl : N.T →ₗ[k] (cone (coneInrZ0 φ)).T := coneInl N (cone φ)

/-- Z2.f2: typing helper, `inr' : C(φ) → C(ψ)` with typed source and target. -/
private abbrev ψr : (cone φ).T →ₗ[k] (cone (coneInrZ0 φ)).T := coneInr N (cone φ)

/-- Z2.f2: typing helper, `fst' : C(ψ) → N` with domain `(cone ψ).T`. -/
private abbrev ψf : (cone (coneInrZ0 φ)).T →ₗ[k] N.T := coneFst N (cone φ)

/-- Z2.f2: typing helper, `snd' : C(ψ) → C(φ)` with typed source and target. -/
private abbrev ψs : (cone (coneInrZ0 φ)).T →ₗ[k] (cone φ).T := coneSnd N (cone φ)

/-- Z2.f2: `rotInv = w ∘ snd'` pointwise. -/
private theorem rotInv_aux (z : (cone (coneInrZ0 φ)).T) :
    (rotInv φ).1 z = (coneWZ0 φ).1 (ψs φ z) := zero_add _

/-- Z2.f2: `ι₁ (w s) = −fst s`. -/
private theorem rot_ι_w (s : (cone φ).T) :
    ι₁ M ((coneWZ0 φ).1 s) = -(φf φ s) := by
  change shiftIota 𝒜 M.Q 1 (-(shiftIota 𝒜 M.Q 1).symm (coneFst M N s)) = _
  rw [map_neg, LinearEquiv.apply_symm_apply]
  rfl

/-- Z2.f2: `δ(−(a ∘ g)) z = −(δa (g z) − a (δg z))` for `a ∈ Hom^{−1}`, `g ∈ Hom^0`. -/
private theorem δ_neg_comp_apply {P Q R : QuasiCohesive 𝒜} (a : Q.T →ₗ[k] R.T)
    (g : P.T →ₗ[k] Q.T) (z : P.T) :
    δ P R (-1) (-(a ∘ₗ g)) z =
      -((δ Q R (-1) a) (g z) + (-1 : ℤ).negOnePow • a (δ P Q 0 g z)) := by
  have h := δ_comp P Q R (-1) 0 a g
  rw [add_zero] at h
  rw [map_neg, LinearMap.neg_apply, h]
  rfl

/-- Z2.f2: `δ(snd ∘ snd') = −φ ∘ fst ∘ snd' − fst'`, pointwise. -/
private theorem rot_δg (z : (cone (coneInrZ0 φ)).T) :
    δ (cone (coneInrZ0 φ)).toQuasiCohesive N.toQuasiCohesive 0 (φs φ ∘ₗ ψs φ) z =
      -(φ.1 (φf φ (ψs φ z))) - ψf φ z := by
  have h := δ_comp (cone (coneInrZ0 φ)).toQuasiCohesive (cone φ).toQuasiCohesive
    N.toQuasiCohesive 0 0 (coneSnd M N) (coneSnd N (cone φ))
  rw [add_zero] at h
  erw [h, δ_coneSnd, δ_coneSnd]
  have e := LinearMap.congr_fun (coneSnd_coneInr M N) (coneFst N (cone φ) z)
  change -(φ.1 (coneFst M N (coneSnd N (cone φ) z))) +
    (0 : ℤ).negOnePow • coneSnd M N (-(coneInr M N (coneFst N (cone φ) z))) = _
  rw [Int.negOnePow_zero, one_smul, map_neg]
  erw [e]
  rw [sub_eq_add_neg]
  rfl

/-- Z2.f2: `rotHom ∘ rotInv − id = δH`, in typed form. -/
private theorem rotHom_rotInv_aux :
    (rotHom φ).1 ∘ₗ (rotInv φ).1 - LinearMap.id =
      δ (cone (coneInrZ0 φ)).toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive (-1)
        (-(ψl φ ∘ₗ φs φ ∘ₗ ψs φ)) := by
  refine LinearMap.ext fun (z : (cone (coneInrZ0 φ)).T) => ?_
  rw [δ_neg_comp_apply]
  have hg := rot_δg φ z
  have d1 : ψl φ (ψf φ z) + ψr φ (ψs φ z) = z :=
    LinearMap.congr_fun (coneInl_coneFst_add N (cone φ)) z
  have d2 : φl φ (φf φ (ψs φ z)) + φr φ (φs φ (ψs φ z)) = ψs φ z :=
    LinearMap.congr_fun (coneInl_coneFst_add M N) (ψs φ z)
  have hx : (rotHom φ).1 ((rotInv φ).1 z) = ψl φ (φ.1 (ι₁ M ((rotInv φ).1 z))) +
      ψr φ (-(φl φ (ι₁ M ((rotInv φ).1 z)))) := rfl
  have hy : ι₁ M ((rotInv φ).1 z) = -(φf φ (ψs φ z)) :=
    (congrArg (ι₁ M) (rotInv_aux φ z)).trans (rot_ι_w φ _)
  have hδl : ∀ y, (δ N.toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive (-1)) (ψl φ) y =
      ψr φ (φr φ y) := fun y => LinearMap.congr_fun (δ_coneInl (coneInrZ0 φ)) y
  change (rotHom φ).1 ((rotInv φ).1 z) - z = _
  rw [hx, hy, hδl, hg, LinearMap.comp_apply, Int.negOnePow_neg, Int.negOnePow_one]
  clear hx hy hg hδl
  generalize ψs φ z = s at *
  generalize ψf φ z = c at *
  subst d1
  have e : ψr φ s = ψr φ (φl φ (φf φ s)) + ψr φ (φr φ (φs φ s)) := by
    rw [← map_add, d2]
  rw [e]
  simp only [map_neg, map_sub, Units.neg_smul, one_smul, neg_neg]
  abel

/-- **Z2.f2.** `rotHom ∘ rotInv − id = δH`, `H = −inl' ∘ snd ∘ snd'` (Mathlib's
`homotopyInvHomId`). -/
theorem rotHom_rotInv :
    (rotHom φ).1 ∘ₗ (rotInv φ).1 - LinearMap.id =
      δ (cone (coneInrZ0 φ)).toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive (-1)
        (-(coneInl N (cone φ) ∘ₗ coneSnd M N ∘ₗ coneSnd N (cone φ))) := by
  convert rotHom_rotInv_aux φ using 3
  exact congrArg _ (LinearMap.ext fun x => rfl)

/-- Z2.f2: the homotopy `H₂ = −inl' ∘ snd ∈ Hom^{−1}(C(φ), C(ψ))`. -/
theorem rotH₂_mem :
    -(coneInl N (cone φ) ∘ₗ coneSnd M N) ∈
      Hom (cone φ).toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive (-1) := by
  have h := comp_mem _ _ _ (coneInl_mem_hom (coneInrZ0 φ)) (coneSnd_mem_hom φ)
  rw [show (-1 : ℤ) + 0 = -1 by norm_num] at h
  exact neg_mem h

/-- Z2.f2: `δ inl' = inr' ∘ inr`, pointwise. -/
private theorem rot_δψl (y : N.T) :
    (δ N.toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive (-1)) (ψl φ) y =
      ψr φ (φr φ y) := LinearMap.congr_fun (δ_coneInl (coneInrZ0 φ)) y

/-- Z2.f2: `rotHom ∘ w_φ − inr' = δH₂`, in typed form. -/
private theorem rotHom_coneW_aux :
    (rotHom φ).1 ∘ₗ (coneWZ0 φ).1 - ψr φ =
      δ (cone φ).toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive (-1)
        (-(ψl φ ∘ₗ φs φ)) := by
  refine LinearMap.ext fun (z : (cone φ).T) => ?_
  rw [δ_neg_comp_apply]
  have hδs : (δ (cone φ).toQuasiCohesive N.toQuasiCohesive 0) (φs φ) z = -(φ.1 (φf φ z)) :=
    LinearMap.congr_fun (δ_coneSnd φ) z
  have d2 : φl φ (φf φ z) + φr φ (φs φ z) = z :=
    LinearMap.congr_fun (coneInl_coneFst_add M N) z
  have hx : (rotHom φ).1 ((coneWZ0 φ).1 z) = ψl φ (φ.1 (ι₁ M ((coneWZ0 φ).1 z))) +
      ψr φ (-(φl φ (ι₁ M ((coneWZ0 φ).1 z)))) := rfl
  have hy : ι₁ M ((coneWZ0 φ).1 z) = -(φf φ z) := rot_ι_w φ z
  change (rotHom φ).1 ((coneWZ0 φ).1 z) - ψr φ z = _
  rw [hx, hy, rot_δψl, hδs, Int.negOnePow_neg, Int.negOnePow_one]
  clear hx hy hδs
  generalize φf φ z = a at *
  generalize φs φ z = b at *
  subst d2
  simp only [map_neg, map_add, Units.neg_smul, one_smul, neg_neg]
  abel

/-- **Z2.f2.** `rotHom ∘ w_φ − inr' = δH₂`, `H₂ = −inl' ∘ snd` (Mathlib's
`rotateHomotopyEquivComm₂Homotopy`). -/
theorem rotHom_coneW :
    (rotHom φ).1 ∘ₗ (coneWZ0 φ).1 - (coneInrZ0 (coneInrZ0 φ)).1 =
      δ (cone φ).toQuasiCohesive (cone (coneInrZ0 φ)).toQuasiCohesive (-1)
        (-(coneInl N (cone φ) ∘ₗ coneSnd M N)) := by
  convert rotHom_coneW_aux φ using 3
  · rfl
  · exact congrArg _ (LinearMap.ext fun x => rfl)

/-- **Z2.f2.** `w_ψ ∘ rotHom = −φ[1]`, `φ[1] = ι₁⁻¹ ∘ φ ∘ ι₁`
(Mathlib's `rotateHomotopyEquiv_comm₃`). -/
theorem coneW_rotHom :
    (coneWZ0 (coneInrZ0 φ)).1 ∘ₗ (rotHom φ).1 =
      -((shiftIota 𝒜 N.Q 1).symm.toLinearMap ∘ₗ φ.1 ∘ₗ ι₁ M) := by
  refine LinearMap.ext fun (x : (M.shift 1).T) => ?_
  have e1 : ∀ y, ψf φ (ψl φ y) = y := fun y => LinearMap.congr_fun (coneFst_coneInl N (cone φ)) y
  have e2 : ∀ y, ψf φ (ψr φ y) = 0 := fun y => LinearMap.congr_fun (coneFst_coneInr N (cone φ)) y
  have hx : (rotHom φ).1 x = ψl φ (φ.1 (ι₁ M x)) + ψr φ (-(φl φ (ι₁ M x))) := rfl
  change -((shiftIota 𝒜 N.Q 1).symm (ψf φ ((rotHom φ).1 x))) =
    -((shiftIota 𝒜 N.Q 1).symm (φ.1 (ι₁ M x)))
  rw [hx, map_add, e1, e2, add_zero]

/-- Z2.f2: closed maps differing by a coboundary `δH`, `H ∈ Hom^{−1}`, agree in `H⁰`. -/
private theorem hmk_eq {M₁ M₂ : QuasiCohesive 𝒜} (f g : Z0 M₁ M₂) (H : M₁.T →ₗ[k] M₂.T)
    (hH : H ∈ Hom M₁ M₂ (-1)) (h : f.1 - g.1 = δ M₁ M₂ (-1) H) :
    (Submodule.Quotient.mk f : H0 M₁ M₂) = Submodule.Quotient.mk g := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact ⟨H, hH, h.symm⟩

/-- **Z2.f2.** Mathlib's `rotateTrianglehIso`: `(coneTriangle φ).rotate ≅ coneTriangle inr_φ`, with
components `id`, `id` and the homotopy equivalence `[rotHom] : M⟦1⟧ ≅ C(inr_φ)`. -/
def rotateTriangleIso : (coneTriangle φ).rotate ≅ coneTriangle (coneInrZ0 φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    { hom := show (⟨M⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ ⟶ ⟨cone (coneInrZ0 φ)⟩ from
        Submodule.Quotient.mk (rotHom φ)
      inv := show (⟨cone (coneInrZ0 φ)⟩ : HoP 𝒜) ⟶ (⟨M⟩ : HoP 𝒜)⟦(1 : ℤ)⟧ from
        Submodule.Quotient.mk (rotInv φ)
      hom_inv_id := congrArg Submodule.Quotient.mk (Subtype.ext (rotInv_rotHom φ))
      inv_hom_id := hmk_eq _ (idZ0 _) _ (rotH_mem φ) (rotHom_rotInv φ) }
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by
      refine Eq.trans (b := (coneTriangle (coneInrZ0 φ)).mor₂) ?_ (Category.id_comp _).symm
      exact hmk_eq (compZ0 _ _ _ (rotHom φ) (coneWZ0 φ)) (coneInrZ0 (coneInrZ0 φ)) _
        (rotH₂_mem φ) (rotHom_coneW φ))
    (by
      rw [Iso.refl_hom]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      show -(Submodule.Quotient.mk (conjZ0 (isShiftData_shiftIota M 1)
          (isShiftData_shiftIota N 1) φ) : H0 _ _) =
        Submodule.Quotient.mk (compZ0 _ _ _ (coneWZ0 (coneInrZ0 φ)) (rotHom φ))
      rw [← Submodule.Quotient.mk_neg]
      exact congrArg _ (Subtype.ext (coneW_rotHom φ).symm))

/-- **Z2.f2.** The rotation of a distinguished triangle is distinguished. -/
theorem rotate_distinguished' (T : Triangle (HoP 𝒜)) (hT : T ∈ distinguishedTriangles 𝒜) :
    T.rotate ∈ distinguishedTriangles 𝒜 := by
  obtain ⟨M, N, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨(rotate (HoP 𝒜)).mapIso e ≪≫ rotateTriangleIso φ⟩⟩

end Cohesive
