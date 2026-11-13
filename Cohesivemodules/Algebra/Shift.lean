import Cohesivemodules.Algebra.Cohesive

set_option linter.style.header false

/-!
# Z2.a: the shift of cohesive modules

Blueprint item Z2.a (`blueprint/blueprint-tr.md` §2; §11 v1.16). For `a : ℤ` the shift `M[a]` has
generators `Q[a]^p = Q^{p+a}` and operator `𝕏[a] = (−1)^a ι_a⁻¹ 𝕏 ι_a`, where the sign isomorphism
`ι_a : Tot(Q[a]) ≃ Tot(Q)`, `α ⊗ e ↦ (−1)^{a|α|} α ⊗ e` (`GCDga.twist a` on `A`, reindexing on
the generators), has degree `a`: it maps total degree `m` to `m + a` and
`ι_a(β x) = (−1)^{a|β|} β ι_a(x)`.
* `shiftQ Q a`, `shiftIota Q a`;
* the generic transport `QuasiCohesive.transport` (`(−1)^m u⁻¹ 𝕏 u` for a bijection `u` of degree
  `m`) and its Leibniz/flatness proof;
* `CohesiveModule.shift M a`; `shiftIota_mem` (`ι_a ∈ Hom^a(M[a], M)`), `δ_shiftIota` (closed).

## Deviations
* [B, §2.4] writes `𝔼[1] = −𝔼` for right modules; in the left-module encoding (conventions §3)
  this breaks Leibniz, so the shift is transported along `ι_a` (blueprint-tr audit).
-/

noncomputable section

namespace Cohesive

open DirectSum TensorProduct

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

/-- **Z2.a.** The shifted generators `Q[a]^p = Q^{p+a}`. -/
def shiftQ (Q : ℤ → Type) (a : ℤ) : ℤ → Type := fun p => Q (p + a)

instance (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] (a p : ℤ) : AddCommGroup (shiftQ Q a p) :=
  inferInstanceAs (AddCommGroup (Q (p + a)))

instance (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (a p : ℤ) :
    Module (𝒜 0) (shiftQ Q a p) :=
  inferInstanceAs (Module (𝒜 0) (Q (p + a)))

variable (𝒜) in
/-- Z2.a: the sign twist `τₙ` as an `A⁰`-linear involution of `A`. -/
def twistEquiv (n : ℤ) : A ≃ₗ[𝒜 0] A :=
  LinearEquiv.ofInvolutive (GCDga.twist 𝒜 n) (twist_involutive 𝒜 n)

/-- Z2.a: `map f g` is `k`-linear on `A ⊗_{A⁰} M` when `f` is `k`-linear. -/
private theorem map_smul_aux {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module (𝒜 0) M]
    [Module (𝒜 0) N] (f : A →ₗ[𝒜 0] A) (hf : ∀ (r : k) a, f (r • a) = r • f a)
    (g : M →ₗ[𝒜 0] N) (r : k) (x : A ⊗[𝒜 0] M) :
    TensorProduct.map f g (r • x) = r • TensorProduct.map f g x := by
  refine TensorProduct.inductionOn x (fun a e => ?_) (fun x y hx hy => ?_)
  · rw [TensorProduct.smul_tmul' r a e, TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', hf]
  · rw [smul_add, map_add, hx, hy, map_add, smul_add]

variable (𝒜) in
/-- **Z2.a.** The sign isomorphism `ι_a : Tot(Q[a]) ≃ Tot(Q)`, `α ⊗ e ↦ (−1)^{a|α|} α ⊗ e`
(`GCDga.twist a` on `A`, reindexing `⨁_p Q^{p+a} ≃ ⨁_p Q^p`). -/
def shiftIota (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (a : ℤ) :
    Tot 𝒜 (shiftQ Q a) ≃ₗ[k] Tot 𝒜 Q :=
  { (TensorProduct.congr (twistEquiv 𝒜 a)
      (DirectSum.lequivCongrLeft (𝒜 0) (Equiv.subRight a)).symm).toAddEquiv with
    map_smul' := fun r x => map_smul_aux (M := ⨁ p, shiftQ Q a p) (N := ⨁ p, Q p)
      (twistEquiv 𝒜 a).toLinearMap (fun r b => GCDga.twist_smul 𝒜 a r b)
      (DirectSum.lequivCongrLeft (𝒜 0) (Equiv.subRight a)).symm.toLinearMap r (x : A ⊗[𝒜 0] _) }

/-- Z2.a: `ι_a (α ⊗ e) = (−1)^{a|α|} α ⊗ e` for `α ∈ A^q`, `e ∈ Q^{p+a}`. -/
theorem shiftIota_tmul (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    (a : ℤ) {q : ℤ} {α : A} (hα : α ∈ 𝒜 q) (p : ℤ) (e : Q (p + a)) :
    shiftIota 𝒜 Q a (α ⊗ₜ[𝒜 0] lof (𝒜 0) ℤ (shiftQ Q a) p e) =
      (a * q).negOnePow • (α ⊗ₜ[𝒜 0] lof (𝒜 0) ℤ Q (p + a) e) := by
  refine (TensorProduct.congr_tmul (twistEquiv 𝒜 a)
    (DirectSum.lequivCongrLeft (𝒜 0) (Equiv.subRight a)).symm α
    (lof (𝒜 0) ℤ (fun p => Q ((Equiv.subRight a).symm p)) p e)).trans ?_
  have h : (DirectSum.lequivCongrLeft (𝒜 0) (Equiv.subRight a)).symm
      (lof (𝒜 0) ℤ (fun p => Q ((Equiv.subRight a).symm p)) p e) = lof (𝒜 0) ℤ Q (p + a) e :=
    DirectSum.lequivCongrLeft_symm_lof (R := 𝒜 0) (M := Q) (h := Equiv.subRight a) (k := p)
  exact (congrArg₂ (fun x y => x ⊗ₜ[𝒜 0] y) (GCDga.twist_of_mem 𝒜 a hα) h).trans
    (Tot.tmul_units_smul (𝒜 := 𝒜) (Q := Q) _ α _)

/-- Z2.a: `ι_a` raises the total degree by `a`. -/
private theorem shiftIota_mem_of_mem (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (a m : ℤ) {x : Tot 𝒜 (shiftQ Q a)}
    (hx : x ∈ totDeg 𝒜 (shiftQ Q a) m) : shiftIota 𝒜 Q a x ∈ totDeg 𝒜 Q (m + a) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, b, e, rfl, hb, rfl⟩ := hx
    rw [shiftIota_tmul Q a hb p e]
    refine zsmul_mem (x := (b ⊗ₜ[𝒜 0] lof (𝒜 0) ℤ Q (p + a) e : Tot 𝒜 Q)) ?_ _
    have := tmul_mem_totDeg (𝒜 := 𝒜) (Q := Q) hb e
    rwa [← add_assoc] at this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- Z2.a: `ι_a⁻¹` lowers the total degree by `a`. -/
private theorem shiftIota_symm_mem_of_mem (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (a m : ℤ) {y : Tot 𝒜 Q} (hy : y ∈ totDeg 𝒜 Q (m + a)) :
    (shiftIota 𝒜 Q a).symm y ∈ totDeg 𝒜 (shiftQ Q a) m := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q, p', b, e, hqp, hb, rfl⟩ := hy
    obtain ⟨p, rfl⟩ : ∃ p, p' = p + a := ⟨p' - a, by omega⟩
    have h2 := shiftIota_tmul Q a hb p e
    have key : shiftIota 𝒜 Q a ((a * q).negOnePow •
          (b ⊗ₜ[𝒜 0] lof (𝒜 0) ℤ (shiftQ Q a) p e : Tot 𝒜 (shiftQ Q a))) =
        (b ⊗ₜ[𝒜 0] lof (𝒜 0) ℤ Q (p + a) e : Tot 𝒜 Q) :=
      (map_zsmul (shiftIota 𝒜 Q a) ((a * q).negOnePow : ℤ) _).trans
        ((congrArg (fun z => ((a * q).negOnePow : ℤ) • z) h2).trans
          ((smul_smul _ _ _).trans
            ((congrArg (· • (b ⊗ₜ[𝒜 0] lof (𝒜 0) ℤ Q (p + a) e : Tot 𝒜 Q))
              (Int.units_mul_self _)).trans (one_smul _ _))))
    have hmem := (LinearEquiv.symm_apply_eq _).2 key.symm
    rw [hmem]
    have hq : Tot.tmul 𝒜 (shiftQ Q a) b (lof (𝒜 0) ℤ (shiftQ Q a) p e) ∈
        totDeg 𝒜 (shiftQ Q a) m := by
      have := tmul_mem_totDeg (𝒜 := 𝒜) (Q := shiftQ Q a) hb (p := p) e
      rwa [show q + p = m by omega] at this
    exact zsmul_mem hq _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- Z2.a: `ι_a` has degree `a`: total degree `m` goes to `m + a`, and back. -/
theorem shiftIota_mem_totDeg_iff (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)]
    [∀ p, Module (𝒜 0) (Q p)] (a m : ℤ) (x : Tot 𝒜 (shiftQ Q a)) :
    shiftIota 𝒜 Q a x ∈ totDeg 𝒜 Q (m + a) ↔ x ∈ totDeg 𝒜 (shiftQ Q a) m := by
  refine ⟨fun h => ?_, shiftIota_mem_of_mem Q a m⟩
  simpa using shiftIota_symm_mem_of_mem Q a m h

/-- Z2.a: `ι_a (β x) = (−1)^{a|β|} β ι_a(x)` for `β ∈ A^p`. -/
theorem shiftIota_smul (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    (a : ℤ) {p : ℤ} {β : A} (hβ : β ∈ 𝒜 p) (x : Tot 𝒜 (shiftQ Q a)) :
    shiftIota 𝒜 Q a (β • x) = (a * p).negOnePow • β • shiftIota 𝒜 Q a x := by
  induction x using Tot.induction_on with
  | ht c e =>
    have e1 : shiftIota 𝒜 Q a (Tot.tmul 𝒜 (shiftQ Q a) (β * c) e) =
        Tot.tmul 𝒜 Q (GCDga.twist 𝒜 a (β * c))
          ((DirectSum.lequivCongrLeft (𝒜 0) (Equiv.subRight a)).symm e) :=
      TensorProduct.congr_tmul _ _ _ _
    have e2 : shiftIota 𝒜 Q a (Tot.tmul 𝒜 (shiftQ Q a) c e) =
        Tot.tmul 𝒜 Q (GCDga.twist 𝒜 a c)
          ((DirectSum.lequivCongrLeft (𝒜 0) (Equiv.subRight a)).symm e) :=
      TensorProduct.congr_tmul _ _ _ _
    rw [Tot.smul_tmul, e1, e2, Tot.smul_tmul, GCDga.twist_mul_of_mem 𝒜 a hβ,
      ← Tot.tmul_units_smul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add, smul_add]

/-- Z2.a: the inverse of a bijection of degree `m` has the dual semilinearity. -/
private theorem transport_symm_smul {Q₁ Q₂ : ℤ → Type} [∀ p, AddCommGroup (Q₁ p)]
    [∀ p, Module (𝒜 0) (Q₁ p)] [∀ p, AddCommGroup (Q₂ p)] [∀ p, Module (𝒜 0) (Q₂ p)]
    (u : Tot 𝒜 Q₁ ≃ₗ[k] Tot 𝒜 Q₂) (m : ℤ)
    (hsmul : ∀ {p : ℤ} {β : A}, β ∈ 𝒜 p → ∀ x, u (β • x) = (m * p).negOnePow • β • u x)
    {q : ℤ} {γ : A} (hγ : γ ∈ 𝒜 q) (y : Tot 𝒜 Q₂) :
    u.symm (γ • y) = (m * q).negOnePow • γ • u.symm y := by
  have h := hsmul hγ (u.symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [LinearEquiv.symm_apply_eq, Units.smul_def, map_zsmul, h, ← Units.smul_def, smul_smul,
    Int.units_mul_self, one_smul]

/-- Z2.a: the inverse of a bijection of degree `m` has degree `-m` (in the form needed). -/
private theorem transport_symm_mem {Q₁ Q₂ : ℤ → Type} [∀ p, AddCommGroup (Q₁ p)]
    [∀ p, Module (𝒜 0) (Q₁ p)] [∀ p, AddCommGroup (Q₂ p)] [∀ p, Module (𝒜 0) (Q₂ p)]
    (u : Tot 𝒜 Q₁ ≃ₗ[k] Tot 𝒜 Q₂) (m : ℤ)
    (hdeg : ∀ n x, u x ∈ totDeg 𝒜 Q₂ (n + m) ↔ x ∈ totDeg 𝒜 Q₁ n) (n : ℤ) {y : Tot 𝒜 Q₂}
    (hy : y ∈ totDeg 𝒜 Q₂ (n + m)) : u.symm y ∈ totDeg 𝒜 Q₁ n :=
  (hdeg n _).1 (by rwa [LinearEquiv.apply_symm_apply])

/-- **Z2.a.** Transport of a quasi-cohesive structure along a bijection `u` of degree `m`
(maps total degree `n` to `n + m`, `u(β x) = (−1)^{m|β|} β u(x)`): the operator
`(−1)^m u⁻¹ 𝕏 u` satisfies degree, Leibniz and flatness (the curvature has even degree). -/
def QuasiCohesive.transport (M : QuasiCohesive 𝒜) (Q' : ℤ → Type) [∀ p, AddCommGroup (Q' p)]
    [∀ p, Module (𝒜 0) (Q' p)] (u : Tot 𝒜 Q' ≃ₗ[k] Tot 𝒜 M.Q) (m : ℤ)
    (hdeg : ∀ n x, u x ∈ totDeg 𝒜 M.Q (n + m) ↔ x ∈ totDeg 𝒜 Q' n)
    (hsmul : ∀ {p : ℤ} {β : A}, β ∈ 𝒜 p → ∀ x, u (β • x) = (m * p).negOnePow • β • u x) :
    QuasiCohesive 𝒜 where
  Q := Q'
  X := m.negOnePow • (u.symm.toLinearMap ∘ₗ M.X ∘ₗ u.toLinearMap)
  X_mem := fun {n x} hx => by
    have h1 := M.X_mem ((hdeg n x).2 hx)
    have h2 : M.X (u x) ∈ totDeg 𝒜 M.Q ((n + 1) + m) := by rwa [add_right_comm] at h1
    exact zsmul_mem (transport_symm_mem u m hdeg (n + 1) h2) _
  leibniz := fun {p β} hβ x => by
    have hd := GCDga.d_mem (𝒜 := 𝒜) hβ
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Units.smul_def]
    rw [hsmul hβ x]
    simp only [Units.smul_def, map_zsmul]
    rw [M.leibniz hβ]
    simp only [Units.smul_def, map_zsmul, map_add]
    rw [transport_symm_smul u m hsmul hd, transport_symm_smul u m hsmul hβ,
      LinearEquiv.symm_apply_apply, mul_add, mul_one, Int.negOnePow_add]
    generalize (m * p).negOnePow = s1
    generalize m.negOnePow = s2
    generalize p.negOnePow = s3
    rcases Int.units_eq_one_or s1 with rfl | rfl <;>
      rcases Int.units_eq_one_or s2 with rfl | rfl <;>
      rcases Int.units_eq_one_or s3 with rfl | rfl <;> simp
  flat := fun x => by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, Units.smul_def,
      map_zsmul, LinearEquiv.apply_symm_apply, M.flat]
    rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
      transport_symm_smul u m hsmul (GCDga.c_mem (𝒜 := 𝒜)), LinearEquiv.symm_apply_apply,
      mul_comm, Int.negOnePow_two_mul, one_smul]

/-- **Z2.a.** The shift `M[a]` of a cohesive module: generators `Q^{p+a}`, operator
`(−1)^a ι_a⁻¹ 𝕏 ι_a`. -/
def CohesiveModule.shift (M : CohesiveModule 𝒜) (a : ℤ) : CohesiveModule 𝒜 :=
  { M.toQuasiCohesive.transport (shiftQ M.Q a) (shiftIota 𝒜 M.Q a) a
      (fun n x => shiftIota_mem_totDeg_iff M.Q a n x) (shiftIota_smul M.Q a) with
    bounded := by
      obtain ⟨b₁, b₂, h⟩ := M.bounded
      exact ⟨b₁ - a, b₂ - a, fun p hp => h (p + a) (by omega)⟩
    finite := fun p => M.finite (p + a)
    projective := fun p => M.projective (p + a) }

/-- Z2.a: the operator of `M[a]` (rfl). -/
theorem CohesiveModule.shift_X (M : CohesiveModule 𝒜) (a : ℤ) :
    (M.shift a).X = a.negOnePow •
      ((shiftIota 𝒜 M.Q a).symm.toLinearMap ∘ₗ M.X ∘ₗ (shiftIota 𝒜 M.Q a).toLinearMap) :=
  rfl

/-- **Z2.a.** `ι_a ∈ Hom^a(M[a], M)`. -/
theorem shiftIota_mem_hom (M : CohesiveModule 𝒜) (a : ℤ) :
    (shiftIota 𝒜 M.Q a).toLinearMap ∈
      Hom (M.shift a).toQuasiCohesive M.toQuasiCohesive a :=
  ⟨fun {m x} hx => (shiftIota_mem_totDeg_iff M.Q a m x).2 hx,
    fun {_ _} hβ x => shiftIota_smul M.Q a hβ x⟩

/-- **Z2.a.** `ι_a` is closed: `δ ι_a = 𝕏 ι_a − (−1)^a ι_a 𝕏[a] = 0`. -/
theorem δ_shiftIota (M : CohesiveModule 𝒜) (a : ℤ) :
    δ (M.shift a).toQuasiCohesive M.toQuasiCohesive a (shiftIota 𝒜 M.Q a).toLinearMap = 0 := by
  ext x
  have hX : shiftIota 𝒜 M.Q a ((M.shift a).X x) = a.negOnePow • M.X (shiftIota 𝒜 M.Q a x) := by
    change shiftIota 𝒜 M.Q a (a.negOnePow • (shiftIota 𝒜 M.Q a).symm (M.X (shiftIota 𝒜 M.Q a x)))
      = _
    rw [Units.smul_def, map_zsmul, LinearEquiv.apply_symm_apply, ← Units.smul_def]
  change M.X (shiftIota 𝒜 M.Q a x) - a.negOnePow • shiftIota 𝒜 M.Q a ((M.shift a).X x) = 0
  rw [hX, smul_smul, Int.units_mul_self, one_smul, sub_self]

end Cohesive
