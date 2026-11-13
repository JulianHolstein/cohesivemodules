import Cohesivemodules.Algebra.ConeRotate

set_option linter.style.header false

/-!
# Z2.f3: shifting cone triangles

Blueprint item Z2.f (`blueprint/blueprint-tr.md` §3c, "Shift"), following Mathlib's
`CochainComplex.mappingCone.shiftIso` and `shiftTrianglehIso`. For `φ ∈ Z⁰(M, N)` and `n : ℤ`, with
`φ[n] = ι_n⁻¹ φ ι_n` (`shiftZ0`, the shift of `HoP` on morphisms, Z2.b):
* `shiftConeHom φ n := lift_{φ[n]} ((−1)^n ι_n⁻¹ fst ι_n) (ι_n⁻¹ snd ι_n) : C(φ)[n] → C(φ[n])`;
* `shiftConeInv φ n := desc_{φ[n]} ((−1)^n ι_n⁻¹ inl ι_n) (ι_n⁻¹ inr ι_n) : C(φ[n]) → C(φ)[n]`;
* they are mutually inverse (exactly);
* `shiftTriangleIso φ n : (Triangle.shiftFunctor _ n).obj (coneTriangle φ) ≅ coneTriangle φ[n]`
  (components `id`, `(−1)^n`, `[shiftConeHom]`; the third square uses `shiftFunctorComm` of
  `HoP`), hence `shift_distinguished`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Pretriangulated

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable {M N : CohesiveModule 𝒜} (φ : Z0 M.toQuasiCohesive N.toQuasiCohesive) (n : ℤ)

/-- **Z2.f3.** `φ[n] = ι_n⁻¹ ∘ φ ∘ ι_n ∈ Z⁰(M[n], N[n])` (`conjZ0`, the shift on morphisms). -/
abbrev shiftZ0 : Z0 (M.shift n).toQuasiCohesive (N.shift n).toQuasiCohesive :=
  conjZ0 (isShiftData_shiftIota M n) (isShiftData_shiftIota N n) φ

/-- Z2.f3: `ι_n` of `C(φ)`. -/
abbrev ιC : ((cone φ).shift n).T →ₗ[k] (cone φ).T := (shiftIota 𝒜 (cone φ).Q n).toLinearMap

/-- Z2.f3: the first component `(−1)^n ι_n⁻¹ ∘ fst ∘ ι_n` of `shiftConeHom`. -/
abbrev shiftConeα : ((cone φ).shift n).T →ₗ[k] (M.shift n).T :=
  n.negOnePow • ((shiftIota 𝒜 M.Q n).symm.toLinearMap ∘ₗ coneFst M N ∘ₗ ιC φ n)

/-- Z2.f3: the second component `ι_n⁻¹ ∘ snd ∘ ι_n` of `shiftConeHom`. -/
abbrev shiftConeβ : ((cone φ).shift n).T →ₗ[k] (N.shift n).T :=
  (shiftIota 𝒜 N.Q n).symm.toLinearMap ∘ₗ coneSnd M N ∘ₗ ιC φ n

/-- Z2.f3: typing helper, `inl : M → C(φ)` with codomain `(cone φ).T`. -/
private abbrev sInl : M.T →ₗ[k] (cone φ).T := coneInl M N

/-- Z2.f3: typing helper, `inr : N → C(φ)` with codomain `(cone φ).T`. -/
private abbrev sInr : N.T →ₗ[k] (cone φ).T := coneInr M N

/-- Z2.f3: typing helper, `fst : C(φ) → M` with domain `(cone φ).T`. -/
private abbrev sFst : (cone φ).T →ₗ[k] M.T := coneFst M N

/-- Z2.f3: typing helper, `snd : C(φ) → N` with domain `(cone φ).T`. -/
private abbrev sSnd : (cone φ).T →ₗ[k] N.T := coneSnd M N

section Generic

variable {P' P Q' Q R' R : QuasiCohesive 𝒜} {v : P'.T ≃ₗ[k] P.T} {u : Q'.T ≃ₗ[k] Q.T}
  {w : R'.T ≃ₗ[k] R.T} {m : ℤ} (hv : IsShiftData P' P v m) (hw : IsShiftData R' R w m)

include hv hw in
/-- Z2.f3: `(−1)^m w⁻¹ f v ∈ Hom^j` for `f ∈ Hom^j`. -/
private theorem sconj_mem {j : ℤ} {f : P.T →ₗ[k] R.T} (hf : f ∈ Hom P R j) :
    m.negOnePow • (w.symm.toLinearMap ∘ₗ f ∘ₗ v.toLinearMap) ∈ Hom P' R' j := by
  rw [Units.smul_def]
  exact zsmul_mem (conjL_mem hv hw hf) _

include hv hw in
/-- Z2.f3: `δ((−1)^m w⁻¹ f v) = w⁻¹ (δf) v`. -/
private theorem δ_sconj (j : ℤ) (f : P.T →ₗ[k] R.T) :
    δ P' R' j (m.negOnePow • (w.symm.toLinearMap ∘ₗ f ∘ₗ v.toLinearMap)) =
      w.symm.toLinearMap ∘ₗ δ P R j f ∘ₗ v.toLinearMap := by
  have h := δ_conjL hv hw j f
  rw [Units.smul_def, map_zsmul]
  change (m.negOnePow : ℤ) • δ P' R' j (conjL v w f) = _
  rw [h, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
  rfl

include hv hw in
/-- Z2.f3: conjugation of a composite, sign-adjusted: if `δ s = −(g f)` then
`δ(w⁻¹ s v) = −((w⁻¹ g u) ∘ ((−1)^m u⁻¹ f v))`. -/
private theorem δ_conj_neg {j : ℤ} (s : P.T →ₗ[k] R.T) (g : Q.T →ₗ[k] R.T) (f : P.T →ₗ[k] Q.T)
    (h : δ P R j s = -(g ∘ₗ f)) :
    δ P' R' j (w.symm.toLinearMap ∘ₗ s ∘ₗ v.toLinearMap) =
      -((w.symm.toLinearMap ∘ₗ g ∘ₗ u.toLinearMap) ∘ₗ
        (m.negOnePow • (u.symm.toLinearMap ∘ₗ f ∘ₗ v.toLinearMap))) := by
  have h1 := δ_conjL hv hw j s
  change δ P' R' j (conjL v w s) = _
  rw [h1, h]
  refine LinearMap.ext fun x => ?_
  simp only [conjL_apply, LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, Units.smul_def, map_neg, map_zsmul, LinearEquiv.apply_symm_apply,
    smul_neg]

include hv hw in
/-- Z2.f3: if `δ s = g f` then `δ((−1)^m w⁻¹ s v) = (w⁻¹ g u) ∘ (u⁻¹ f v)`. -/
private theorem δ_sconj_comp {j : ℤ} (s : P.T →ₗ[k] R.T) (g : Q.T →ₗ[k] R.T) (f : P.T →ₗ[k] Q.T)
    (h : δ P R j s = g ∘ₗ f) :
    δ P' R' j (m.negOnePow • (w.symm.toLinearMap ∘ₗ s ∘ₗ v.toLinearMap)) =
      (w.symm.toLinearMap ∘ₗ g ∘ₗ u.toLinearMap) ∘ₗ (u.symm.toLinearMap ∘ₗ f ∘ₗ v.toLinearMap) := by
  rw [δ_sconj hv hw, h]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

end Generic

theorem shiftConeα_mem :
    shiftConeα φ n ∈ Hom ((cone φ).shift n).toQuasiCohesive (M.shift n).toQuasiCohesive 1 :=
  sconj_mem (isShiftData_shiftIota (cone φ) n) (isShiftData_shiftIota M n) (coneFst_mem_hom φ)

theorem δ_shiftConeα :
    δ ((cone φ).shift n).toQuasiCohesive (M.shift n).toQuasiCohesive 1 (shiftConeα φ n) = 0 := by
  have h0 : δ (cone φ).toQuasiCohesive M.toQuasiCohesive 1 (sFst φ) = 0 := δ_coneFst φ
  refine Eq.trans (δ_sconj (isShiftData_shiftIota (cone φ) n) (isShiftData_shiftIota M n) 1
    (sFst φ)) ?_
  rw [h0]
  simp only [LinearMap.zero_comp, LinearMap.comp_zero]

theorem shiftConeβ_mem :
    shiftConeβ φ n ∈ Hom ((cone φ).shift n).toQuasiCohesive (N.shift n).toQuasiCohesive 0 :=
  conjL_mem (isShiftData_shiftIota (cone φ) n) (isShiftData_shiftIota N n) (coneSnd_mem_hom φ)

/-- Z2.f3: `δ(ι⁻¹ snd ι) = −φ[n] ∘ ((−1)^n ι⁻¹ fst ι)`. -/
theorem δ_shiftConeβ :
    δ ((cone φ).shift n).toQuasiCohesive (N.shift n).toQuasiCohesive 0 (shiftConeβ φ n) =
      -((shiftZ0 φ n).1 ∘ₗ shiftConeα φ n) :=
  δ_conj_neg (Q' := (M.shift n).toQuasiCohesive) (Q := M.toQuasiCohesive)
    (u := shiftIota 𝒜 M.Q n) (isShiftData_shiftIota (cone φ) n) (isShiftData_shiftIota N n)
    _ φ.1 (sFst φ) (δ_coneSnd φ)

/-- **Z2.f3.** Mathlib's `shiftIso.hom`: `C(φ)[n] → C(φ[n])`. -/
def shiftConeHom :
    Z0 ((cone φ).shift n).toQuasiCohesive (cone (shiftZ0 φ n)).toQuasiCohesive :=
  coneLift (shiftZ0 φ n) (shiftConeα φ n) (shiftConeα_mem φ n) (δ_shiftConeα φ n)
    (shiftConeβ φ n) (shiftConeβ_mem φ n) (δ_shiftConeβ φ n)

/-- Z2.f3: the first component `(−1)^n ι_n⁻¹ ∘ inl ∘ ι_n` of `shiftConeInv`. -/
abbrev shiftConeα' : (M.shift n).T →ₗ[k] ((cone φ).shift n).T :=
  n.negOnePow • ((shiftIota 𝒜 (cone φ).Q n).symm.toLinearMap ∘ₗ coneInl M N ∘ₗ
    (shiftIota 𝒜 M.Q n).toLinearMap)

theorem shiftConeα'_mem :
    shiftConeα' φ n ∈ Hom (M.shift n).toQuasiCohesive ((cone φ).shift n).toQuasiCohesive (-1) :=
  sconj_mem (isShiftData_shiftIota M n) (isShiftData_shiftIota (cone φ) n) (coneInl_mem_hom φ)

/-- Z2.f3: `ι_n⁻¹ ∘ inr ∘ ι_n` is closed of degree `0`. -/
theorem shiftConeβ'_mem :
    (shiftIota 𝒜 (cone φ).Q n).symm.toLinearMap ∘ₗ coneInr M N ∘ₗ (shiftIota 𝒜 N.Q n).toLinearMap
      ∈ Z0 (N.shift n).toQuasiCohesive ((cone φ).shift n).toQuasiCohesive :=
  conjL_mem_Z0 (isShiftData_shiftIota N n) (isShiftData_shiftIota (cone φ) n) (coneInr_mem_Z0 φ)

/-- Z2.f3: the second component of `shiftConeInv`. -/
def shiftConeβ' : Z0 (N.shift n).toQuasiCohesive ((cone φ).shift n).toQuasiCohesive :=
  ⟨_, shiftConeβ'_mem φ n⟩

/-- Z2.f3: `δ((−1)^n ι⁻¹ inl ι) = (ι⁻¹ inr ι) ∘ φ[n]`. -/
theorem δ_shiftConeα' :
    δ (M.shift n).toQuasiCohesive ((cone φ).shift n).toQuasiCohesive (-1) (shiftConeα' φ n) =
      (shiftConeβ' φ n).1 ∘ₗ (shiftZ0 φ n).1 :=
  δ_sconj_comp (Q' := (N.shift n).toQuasiCohesive) (Q := N.toQuasiCohesive)
    (u := shiftIota 𝒜 N.Q n) (isShiftData_shiftIota M n) (isShiftData_shiftIota (cone φ) n)
    (coneInl M N) (sInr φ) φ.1 (δ_coneInl φ)

/-- **Z2.f3.** Mathlib's `shiftIso.inv`: `C(φ[n]) → C(φ)[n]`. -/
def shiftConeInv :
    Z0 (cone (shiftZ0 φ n)).toQuasiCohesive ((cone φ).shift n).toQuasiCohesive :=
  coneDesc (shiftZ0 φ n) (shiftConeα' φ n) (shiftConeα'_mem φ n) (shiftConeβ' φ n)
    (δ_shiftConeα' φ n)

/-- Z2.f3: `fst(inl a + inr b) = a`. -/
private theorem cone_fst_add {M N : CohesiveModule 𝒜} (a : M.T) (b : N.T) :
    coneFst M N (coneInl M N a + coneInr M N b) = a := by
  have e1 := LinearMap.congr_fun (coneFst_coneInl M N) a
  have e2 := LinearMap.congr_fun (coneFst_coneInr M N) b
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at e1 e2
  rw [map_add, e1, e2, add_zero]

/-- Z2.f3: `snd(inl a + inr b) = b`. -/
private theorem cone_snd_add {M N : CohesiveModule 𝒜} (a : M.T) (b : N.T) :
    coneSnd M N (coneInl M N a + coneInr M N b) = b := by
  have e1 := LinearMap.congr_fun (coneSnd_coneInl M N) a
  have e2 := LinearMap.congr_fun (coneSnd_coneInr M N) b
  simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.zero_apply] at e1 e2
  rw [map_add, e1, e2, zero_add]

/-- Z2.f3: `inl (fst z) + inr (snd z) = z`. -/
private theorem cone_decomp' {M N : CohesiveModule 𝒜} (z : Tot 𝒜 (coneQ M N)) :
    coneInl M N (coneFst M N z) + coneInr M N (coneSnd M N z) = z :=
  LinearMap.congr_fun (coneInl_coneFst_add M N) z

/-- Z2.f3: `ι_n(ι_n⁻¹ x) = x` for the linear-map coercions. -/
private theorem ι_ι_symm {P : CohesiveModule 𝒜} (x : P.T) :
    (shiftIota 𝒜 P.Q n) ((shiftIota 𝒜 P.Q n).symm x) = x :=
  LinearEquiv.apply_symm_apply _ _

/-- Z2.f3: `shiftConeHom` pointwise. -/
private theorem shiftConeHom_apply (x : ((cone φ).shift n).T) :
    (shiftConeHom φ n).1 x = coneInl (M.shift n) (N.shift n) (shiftConeα φ n x) +
      coneInr (M.shift n) (N.shift n) (shiftConeβ φ n x) := rfl

/-- Z2.f3: `shiftConeInv` pointwise. -/
private theorem shiftConeInv_apply (y : (cone (shiftZ0 φ n)).T) :
    (shiftConeInv φ n).1 y = shiftConeα' φ n (coneFst (M.shift n) (N.shift n) y) +
      (shiftConeβ' φ n).1 (coneSnd (M.shift n) (N.shift n) y) := rfl

section Abstract

variable {Cs C Ms M' Ns N' : Type} [AddCommGroup Cs] [Module k Cs] [AddCommGroup C] [Module k C]
  [AddCommGroup Ms] [Module k Ms] [AddCommGroup M'] [Module k M'] [AddCommGroup Ns]
  [Module k Ns] [AddCommGroup N'] [Module k N'] (s : ℤˣ) (iC : Cs ≃ₗ[k] C) (iM : Ms ≃ₗ[k] M')
  (iN : Ns ≃ₗ[k] N') (inl : M' →ₗ[k] C) (inr : N' →ₗ[k] C) (fst : C →ₗ[k] M')
  (snd : C →ₗ[k] N')

/-- Z2.f3: abstract form of `inv ∘ hom = id`. -/
private theorem abs_inv_hom (hd : ∀ z, inl (fst z) + inr (snd z) = z) (x : Cs) :
    (s • (iC.symm.toLinearMap ∘ₗ inl ∘ₗ iM.toLinearMap))
        ((s • (iM.symm.toLinearMap ∘ₗ fst ∘ₗ iC.toLinearMap)) x) +
      (iC.symm.toLinearMap ∘ₗ inr ∘ₗ iN.toLinearMap)
        ((iN.symm.toLinearMap ∘ₗ snd ∘ₗ iC.toLinearMap) x) = x := by
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Units.smul_def,
    map_zsmul, LinearEquiv.apply_symm_apply, smul_smul, ← Units.val_mul, Int.units_mul_self,
    Units.val_one, one_smul, ← map_add, hd, LinearEquiv.symm_apply_apply]

/-- Z2.f3: abstract form of `α ∘ inv = fst'`. -/
private theorem abs_α_inv (h1 : ∀ a, fst (inl a) = a) (h2 : ∀ b, fst (inr b) = 0) (a : Ms)
    (b : Ns) :
    (s • (iM.symm.toLinearMap ∘ₗ fst ∘ₗ iC.toLinearMap))
      ((s • (iC.symm.toLinearMap ∘ₗ inl ∘ₗ iM.toLinearMap)) a +
        (iC.symm.toLinearMap ∘ₗ inr ∘ₗ iN.toLinearMap) b) = a := by
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Units.smul_def,
    map_zsmul, LinearEquiv.apply_symm_apply, map_add, h1, h2, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul, add_zero, smul_zero, map_zero,
    LinearEquiv.symm_apply_apply]

/-- Z2.f3: abstract form of `β ∘ inv = snd'`. -/
private theorem abs_β_inv (h1 : ∀ a, snd (inl a) = 0) (h2 : ∀ b, snd (inr b) = b) (a : Ms)
    (b : Ns) :
    (iN.symm.toLinearMap ∘ₗ snd ∘ₗ iC.toLinearMap)
      ((s • (iC.symm.toLinearMap ∘ₗ inl ∘ₗ iM.toLinearMap)) a +
        (iC.symm.toLinearMap ∘ₗ inr ∘ₗ iN.toLinearMap) b) = b := by
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Units.smul_def,
    map_zsmul, LinearEquiv.apply_symm_apply, map_add, h1, h2, smul_zero, map_zero, zero_add,
    LinearEquiv.symm_apply_apply]

end Abstract

/-- **Z2.f3.** `shiftConeInv ∘ shiftConeHom = id`. -/
theorem shiftConeInv_shiftConeHom :
    (shiftConeInv φ n).1 ∘ₗ (shiftConeHom φ n).1 = LinearMap.id := by
  refine LinearMap.ext fun (x : ((cone φ).shift n).T) => ?_
  change (shiftConeInv φ n).1 ((shiftConeHom φ n).1 x) = x
  rw [shiftConeInv_apply, shiftConeHom_apply, cone_fst_add, cone_snd_add]
  exact abs_inv_hom n.negOnePow (shiftIota 𝒜 (cone φ).Q n) (shiftIota 𝒜 M.Q n)
    (shiftIota 𝒜 N.Q n) (coneInl M N) (coneInr M N) (coneFst M N) (coneSnd M N)
    (cone_decomp' (M := M) (N := N)) x

/-- **Z2.f3.** `shiftConeHom ∘ shiftConeInv = id`. -/
theorem shiftConeHom_shiftConeInv :
    (shiftConeHom φ n).1 ∘ₗ (shiftConeInv φ n).1 = LinearMap.id := by
  refine LinearMap.ext fun (y : (cone (shiftZ0 φ n)).T) => ?_
  change (shiftConeHom φ n).1 ((shiftConeInv φ n).1 y) = y
  rw [shiftConeHom_apply, shiftConeInv_apply]
  have ha := abs_α_inv n.negOnePow (shiftIota 𝒜 (cone φ).Q n) (shiftIota 𝒜 M.Q n)
    (shiftIota 𝒜 N.Q n) (coneInl M N) (coneInr M N) (coneFst M N)
    (fun a => LinearMap.congr_fun (coneFst_coneInl M N) a)
    (fun b => LinearMap.congr_fun (coneFst_coneInr M N) b)
    (coneFst (M.shift n) (N.shift n) y) (coneSnd (M.shift n) (N.shift n) y)
  have hb := abs_β_inv n.negOnePow (shiftIota 𝒜 (cone φ).Q n) (shiftIota 𝒜 M.Q n)
    (shiftIota 𝒜 N.Q n) (coneInl M N) (coneInr M N) (coneSnd M N)
    (fun a => LinearMap.congr_fun (coneSnd_coneInl M N) a)
    (fun b => LinearMap.congr_fun (coneSnd_coneInr M N) b)
    (coneFst (M.shift n) (N.shift n) y) (coneSnd (M.shift n) (N.shift n) y)
  erw [ha, hb]
  exact cone_decomp' y

/-- Z2.f3: closed maps differing by nothing agree in `H⁰` (rewriting helper). -/
private theorem hmk_eq' {M₁ M₂ : QuasiCohesive 𝒜} (f g : Z0 M₁ M₂) (h : f.1 = g.1) :
    (Submodule.Quotient.mk f : H0 M₁ M₂) = Submodule.Quotient.mk g :=
  congrArg Submodule.Quotient.mk (Subtype.ext h)

/-- Z2.f3: `C(φ)[n] ≅ C(φ[n])` in `Ho(P_A)`, with `[shiftConeHom]` as the forward map. -/
private def shiftConeIso : (⟨cone φ⟩ : HoP 𝒜)⟦n⟧ ≅ (⟨cone (shiftZ0 φ n)⟩ : HoP 𝒜) where
  hom := show (⟨cone φ⟩ : HoP 𝒜)⟦n⟧ ⟶ ⟨cone (shiftZ0 φ n)⟩ from
    Submodule.Quotient.mk (shiftConeHom φ n)
  inv := show (⟨cone (shiftZ0 φ n)⟩ : HoP 𝒜) ⟶ (⟨cone φ⟩ : HoP 𝒜)⟦n⟧ from
    Submodule.Quotient.mk (shiftConeInv φ n)
  hom_inv_id := hmk_eq' _ (idZ0 _) (shiftConeInv_shiftConeHom φ n)
  inv_hom_id := hmk_eq' _ (idZ0 _) (shiftConeHom_shiftConeInv φ n)

/-- Z2.f3: composition of classes of representatives. -/
private theorem comp_mk' {X Y Z : HoP 𝒜} (φ' : Z0 X.as.toQuasiCohesive Y.as.toQuasiCohesive)
    (ψ : Z0 Y.as.toQuasiCohesive Z.as.toQuasiCohesive) :
    (Submodule.Quotient.mk φ' : X ⟶ Y) ≫ (Submodule.Quotient.mk ψ : Y ⟶ Z) =
      (show X ⟶ Z from Submodule.Quotient.mk (compZ0 _ _ _ ψ φ')) := rfl

/-- Z2.f3: composition of morphisms given as classes of representatives. -/
private theorem comp_mk_eq {X Y Z : HoP 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z)
    (φ' : Z0 X.as.toQuasiCohesive Y.as.toQuasiCohesive)
    (ψ : Z0 Y.as.toQuasiCohesive Z.as.toQuasiCohesive)
    (hf : f = Submodule.Quotient.mk φ') (hg : g = Submodule.Quotient.mk ψ) :
    f ≫ g = (show X ⟶ Z from Submodule.Quotient.mk (compZ0 _ _ _ ψ φ')) := by
  subst hf hg
  rfl

/-- Z2.f3: comparisons compose (abstract form, used for `shiftFunctorComm`). -/
private theorem abs_comm {B P1 P2 P3 P4 : Type} [AddCommGroup B] [Module k B]
    [AddCommGroup P1] [Module k P1] [AddCommGroup P2] [Module k P2] [AddCommGroup P3]
    [Module k P3] [AddCommGroup P4] [Module k P4] (t1 : P1 ≃ₗ[k] B) (a1 : P2 ≃ₗ[k] B)
    (a2 : P3 ≃ₗ[k] B) (t2 : P4 ≃ₗ[k] B) :
    (t2.symm.toLinearMap ∘ₗ a2.toLinearMap) ∘ₗ ((a2.symm.toLinearMap ∘ₗ a1.toLinearMap) ∘ₗ
        (a1.symm.toLinearMap ∘ₗ t1.toLinearMap)) = t2.symm.toLinearMap ∘ₗ t1.toLinearMap := by
  ext x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- Z2.f3: `shiftFunctorComm 1 n` on `M`, unfolded to the comparison isomorphisms. -/
private theorem comm_app_eq (M : HoP 𝒜) :
    (shiftFunctorComm (HoP 𝒜) 1 n).hom.app M =
      (shiftFunctorAddHoP 𝒜 1 n).inv.app M ≫
        eqToHom (congrArg (fun a => (shiftFunctorHoP 𝒜 a).obj M) (add_comm 1 n)) ≫
        (shiftFunctorAddHoP 𝒜 n 1).hom.app M := by
  simp only [shiftFunctorComm, shiftFunctorAdd', Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  rfl

/-- Z2.f3: `shiftFunctorComm 1 n` on `M` as the comparison of `ι_1 ι_n` with `ι_n ι_1`. -/
private theorem comm_app_mk (M : CohesiveModule 𝒜) :
    (shiftFunctorComm (HoP 𝒜) 1 n).hom.app (⟨M⟩ : HoP 𝒜) =
      Submodule.Quotient.mk (shiftCompZ0
        ((isShiftData_shiftIota (M.shift 1) n).trans (isShiftData_shiftIota M 1))
        (((isShiftData_shiftIota (M.shift n) 1).trans (isShiftData_shiftIota M n)).congr_deg
          (add_comm 1 n))) := by
  rw [comm_app_eq, eqToHom_shiftFunctorHoP_obj (⟨M⟩ : HoP 𝒜) (add_comm 1 n)]
  refine (congrArg (fun t => _ ≫ t) (comp_mk_eq _ _ _ _ rfl rfl)).trans
    ((comp_mk_eq _ _ _ _ rfl rfl).trans (hmk_eq' _ _ ?_))
  exact abs_comm ((shiftIota 𝒜 (M.shift 1).Q n).trans (shiftIota 𝒜 M.Q 1))
    (shiftIota 𝒜 M.Q (1 + n)) (shiftIota 𝒜 M.Q (n + 1))
    ((shiftIota 𝒜 (M.shift n).Q 1).trans (shiftIota 𝒜 M.Q n))

/-- Z2.f3: generic form of the first square. -/
private theorem sq₁ {X Y : HoP 𝒜} (f f' : X ⟶ Y) (h : f = f') (u : ℤˣ) :
    (u • f) ≫ (u • Iso.refl Y).hom = 𝟙 X ≫ f' := by
  subst h
  change (u • f) ≫ (u • 𝟙 Y) = _
  rw [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul,
    Category.comp_id, Category.id_comp]

/-- Z2.f3: generic form of the second square. -/
private theorem sq₂ {X Y Z : HoP 𝒜} (f : X ⟶ Y) (e : Y ⟶ Z) (f' : X ⟶ Z) (h : f ≫ e = f')
    (u : ℤˣ) : (u • f) ≫ e = (u • Iso.refl X).hom ≫ f' := by
  subst h
  change (u • f) ≫ e = (u • 𝟙 X) ≫ (f ≫ e)
  rw [Linear.units_smul_comp, Linear.units_smul_comp, Category.id_comp]

/-- Z2.f3: generic form of the third square. -/
private theorem sq₃ {X Y W : HoP 𝒜} (s : X ⟶ (shiftFunctor (HoP 𝒜) (1 : ℤ)).obj W) (e : X ⟶ Y)
    (w' : Y ⟶ (shiftFunctor (HoP 𝒜) (1 : ℤ)).obj W) (h : s = e ≫ w') :
    s ≫ (shiftFunctor (HoP 𝒜) (1 : ℤ)).map (𝟙 W) = e ≫ w' := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id, h]

/-- Z2.f3: `shiftConeHom ∘ (ι⁻¹ inr ι) = inr'`. -/
private theorem hom_conj_inr (v : (N.shift n).T) :
    (shiftConeHom φ n).1 ((shiftConeβ' φ n).1 v) = coneInr (M.shift n) (N.shift n) v := by
  rw [shiftConeHom_apply]
  have ha := abs_α_inv n.negOnePow (shiftIota 𝒜 (cone φ).Q n) (shiftIota 𝒜 M.Q n)
    (shiftIota 𝒜 N.Q n) (coneInl M N) (coneInr M N) (coneFst M N)
    (fun a => LinearMap.congr_fun (coneFst_coneInl M N) a)
    (fun b => LinearMap.congr_fun (coneFst_coneInr M N) b) 0 v
  have hb := abs_β_inv n.negOnePow (shiftIota 𝒜 (cone φ).Q n) (shiftIota 𝒜 M.Q n)
    (shiftIota 𝒜 N.Q n) (coneInl M N) (coneInr M N) (coneSnd M N)
    (fun a => LinearMap.congr_fun (coneSnd_coneInl M N) a)
    (fun b => LinearMap.congr_fun (coneSnd_coneInr M N) b) 0 v
  simp only [map_zero, zero_add] at ha hb
  erw [ha, hb, map_zero, zero_add]

/-- Z2.f3: the second square, in the form `inr⟦n⟧' ≫ [hom] = inr'`. -/
private theorem tri_c₂_core :
    (shiftFunctor (HoP 𝒜) n).map (coneTriangle φ).mor₂ ≫ (shiftConeIso φ n).hom =
      (coneTriangle (shiftZ0 φ n)).mor₂ := by
  change (Submodule.Quotient.mk (conjZ0 (isShiftData_shiftIota N n)
      (isShiftData_shiftIota (cone φ) n) (coneInrZ0 φ)) : (⟨N.shift n⟩ : HoP 𝒜) ⟶
        ⟨(cone φ).shift n⟩) ≫
    (Submodule.Quotient.mk (shiftConeHom φ n) : (⟨(cone φ).shift n⟩ : HoP 𝒜) ⟶
      ⟨cone (shiftZ0 φ n)⟩) = (show (⟨N.shift n⟩ : HoP 𝒜) ⟶ ⟨cone (shiftZ0 φ n)⟩ from
        Submodule.Quotient.mk (coneInrZ0 (shiftZ0 φ n)))
  refine (comp_mk' _ _).trans (hmk_eq' _ _ ?_)
  exact LinearMap.ext fun v => hom_conj_inr φ n v

/-- Z2.f3: abstract form of the third square, at the level of linear maps. -/
private theorem abs_c3 {Cs C B M1 M1n Mn1 Mn Hc : Type} [AddCommGroup Cs] [Module k Cs]
    [AddCommGroup C] [Module k C] [AddCommGroup B] [Module k B] [AddCommGroup M1] [Module k M1]
    [AddCommGroup M1n] [Module k M1n] [AddCommGroup Mn1] [Module k Mn1] [AddCommGroup Mn]
    [Module k Mn] [AddCommGroup Hc] [Module k Hc] (s : ℤˣ) (iC : Cs ≃ₗ[k] C)
    (fst : C →ₗ[k] B) (i1 : M1 ≃ₗ[k] B) (j1 : M1n ≃ₗ[k] M1) (j2 : Mn1 ≃ₗ[k] Mn)
    (iM : Mn ≃ₗ[k] B) (hom : Cs →ₗ[k] Hc) (fst' : Hc →ₗ[k] Mn)
    (hα : ∀ x, fst' (hom x) = s • iM.symm (fst (iC x))) :
    (s : ℤ) • (((j2.trans iM).symm.toLinearMap ∘ₗ (j1.trans i1).toLinearMap) ∘ₗ
        (j1.symm.toLinearMap ∘ₗ (-(i1.symm.toLinearMap ∘ₗ fst)) ∘ₗ iC.toLinearMap)) =
      (-(j2.symm.toLinearMap ∘ₗ fst')) ∘ₗ hom := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply, map_neg,
    map_zsmul, hα, Units.smul_def, smul_neg]

/-- Z2.f3: a unit multiple of a class of a representative. -/
private theorem smul_mk_eq {X Y : HoP 𝒜} (u : ℤˣ) (z : Z0 X.as.toQuasiCohesive Y.as.toQuasiCohesive)
    (f : X ⟶ Y) (hf : f = Submodule.Quotient.mk z) :
    u • f = (show X ⟶ Y from Submodule.Quotient.mk ((u : ℤ) • z)) := by
  subst hf
  rw [Units.smul_def]
  exact (Submodule.Quotient.mk_smul _ _ _).symm

/-- Z2.f3: first square of `shiftTriangleIso`. -/
private theorem tri_c₁ :
    ((Triangle.shiftFunctor (HoP 𝒜) n).obj (coneTriangle φ)).mor₁ ≫
        (n.negOnePow • Iso.refl ((Triangle.shiftFunctor (HoP 𝒜) n).obj (coneTriangle φ)).obj₂).hom =
      𝟙 ((Triangle.shiftFunctor (HoP 𝒜) n).obj (coneTriangle φ)).obj₁ ≫
        (coneTriangle (shiftZ0 φ n)).mor₁ :=
  sq₁ (X := (⟨M.shift n⟩ : HoP 𝒜)) (Y := ⟨N.shift n⟩) _ (Submodule.Quotient.mk (shiftZ0 φ n))
    rfl n.negOnePow

/-- Z2.f3: `fst' ∘ shiftConeHom = α`. -/
private theorem fst_hom (x : ((cone φ).shift n).T) :
    coneFst (M.shift n) (N.shift n) ((shiftConeHom φ n).1 x) = shiftConeα φ n x :=
  (congrArg (coneFst (M.shift n) (N.shift n)) (shiftConeHom_apply φ n x)).trans
    (cone_fst_add _ _)

/-- Z2.f3: the third square, in the form `(−1)^n (w⟦n⟧' ≫ comm) = [hom] ≫ w'`. -/
private theorem tri_c₃_core :
    n.negOnePow • ((shiftFunctor (HoP 𝒜) n).map (coneTriangle φ).mor₃ ≫
        (shiftFunctorComm (HoP 𝒜) 1 n).hom.app (⟨M⟩ : HoP 𝒜)) =
      (shiftConeIso φ n).hom ≫ (coneTriangle (shiftZ0 φ n)).mor₃ := by
  rw [comm_app_mk]
  refine (congrArg (fun t => n.negOnePow • t) (comp_mk_eq _ _ _ _ rfl rfl)).trans ?_
  refine Eq.trans (smul_mk_eq _ _ _ rfl) (Eq.trans ?_ (comp_mk_eq _ _ _ _ rfl rfl).symm)
  refine hmk_eq' _ _ ?_
  exact abs_c3 n.negOnePow (shiftIota 𝒜 (cone φ).Q n) (coneFst M N) (shiftIota 𝒜 M.Q 1)
    (shiftIota 𝒜 (M.shift 1).Q n) (shiftIota 𝒜 (M.shift n).Q 1) (shiftIota 𝒜 M.Q n)
    (shiftConeHom φ n).1 (coneFst (M.shift n) (N.shift n))
    (fun x => fst_hom φ n x)

/-- **Z2.f3.** Mathlib's `shiftTrianglehIso`: the `n`-th shift of the cone triangle of `φ` is
isomorphic to the cone triangle of `φ[n]`, with components `id`, `(−1)^n • id` and
`[shiftConeHom]`. -/
def shiftTriangleIso :
    (Triangle.shiftFunctor (HoP 𝒜) n).obj (coneTriangle φ) ≅ coneTriangle (shiftZ0 φ n) :=
  Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (shiftConeIso φ n)
    (tri_c₁ φ n) (sq₂ _ _ _ (tri_c₂_core φ n) n.negOnePow)
    (sq₃ _ _ _ (tri_c₃_core φ n))

/-- **Z2.f3.** Shifts of distinguished triangles are distinguished. -/
theorem shift_distinguished (T : Triangle (HoP 𝒜)) (hT : T ∈ distinguishedTriangles 𝒜) (n : ℤ) :
    (Triangle.shiftFunctor (HoP 𝒜) n).obj T ∈ distinguishedTriangles 𝒜 := by
  obtain ⟨M, N, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨(Triangle.shiftFunctor (HoP 𝒜) n).mapIso e ≪≫ shiftTriangleIso φ n⟩⟩

end Cohesive
