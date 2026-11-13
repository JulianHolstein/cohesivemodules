import Cohesivemodules.Algebra.ConeCompAux

set_option linter.style.header false

/-!
# Z2.g1: the cone triangle of a composite

Blueprint item Z2.g (`blueprint/blueprint-tr.md` §3d), following Mathlib's
`CochainComplex.mappingConeCompTriangle` and `mappingConeCompHomotopyEquiv`. For
`u ∈ Z⁰(X₁, X₂)`, `v ∈ Z⁰(X₂, X₃)` and `uv := v ∘ u`:
* `compMor₁ u v := coneMap u uv id v 0 : C(u) → C(uv)` and `compMor₂ u v := coneMap uv v u id 0`;
* `compHom u v := lift_{m₁} (inr_u ∘ fst_v) (inr_{uv} ∘ snd_v) : C(v) → C(m₁)` and
  `compInv u v := desc_{m₁} (inl_v ∘ snd_u) m₂ : C(m₁) → C(v)`, with `inv ∘ hom = id` exactly and
  `hom ∘ inv − id = δH`, `H = −inl_D ∘ inl_u ∘ fst_{uv} ∘ snd_D` (`D = C(m₁)`);
* the triangle `C(u) → C(uv) → C(v) → C(u)⟦1⟧` (`compTriangle`) is distinguished (in
  `Algebra/ConeCompTriangle.lean`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Pretriangulated

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]

variable {X₁ X₂ X₃ : CohesiveModule 𝒜} (u : Z0 X₁.toQuasiCohesive X₂.toQuasiCohesive)
  (v : Z0 X₂.toQuasiCohesive X₃.toQuasiCohesive)

/-- Z2.g1: the homotopy `0` witnesses `v ∘ u − (v ∘ u) ∘ id = 0`. -/
theorem compMor₁_cond :
    δ X₁.toQuasiCohesive X₃.toQuasiCohesive (-1) 0 =
      v.1 ∘ₗ u.1 - (compZ0 _ _ _ v u).1 ∘ₗ (idZ0 X₁.toQuasiCohesive).1 := by
  rw [map_zero]
  exact (sub_self _).symm

/-- **Z2.g1.** [B, §2.4]; Mathlib `mappingConeCompTriangle.mor₁`. The map of cones
`m₁ := coneMap u (v ∘ u) id v 0 : C(u) → C(v ∘ u)`. -/
def compMor₁ : Z0 (cone u).toQuasiCohesive (cone (compZ0 _ _ _ v u)).toQuasiCohesive :=
  coneMap u (compZ0 _ _ _ v u) (idZ0 _) v 0 (Submodule.zero_mem _) (compMor₁_cond u v)

/-- Z2.g1: the homotopy `0` witnesses `id ∘ (v ∘ u) − v ∘ u = 0`. -/
theorem compMor₂_cond :
    δ X₁.toQuasiCohesive X₃.toQuasiCohesive (-1) 0 =
      (idZ0 X₃.toQuasiCohesive).1 ∘ₗ (compZ0 _ _ _ v u).1 - v.1 ∘ₗ u.1 := by
  rw [map_zero]
  exact (sub_self _).symm

/-- **Z2.g1.** [B, §2.4]; Mathlib `mappingConeCompTriangle.mor₂`. The map of cones
`m₂ := coneMap (v ∘ u) v u id 0 : C(v ∘ u) → C(v)`. -/
def compMor₂ : Z0 (cone (compZ0 _ _ _ v u)).toQuasiCohesive (cone v).toQuasiCohesive :=
  coneMap (compZ0 _ _ _ v u) v u (idZ0 _) 0 (Submodule.zero_mem _) (compMor₂_cond u v)

/-- Z2.g1: the first component `inr_u ∘ fst_v : C(v) → C(u)` (degree `1`) of `compHom`. -/
abbrev compα : (cone v).T →ₗ[k] (cone u).T := (coneInrZ0 u).1 ∘ₗ coneFst X₂ X₃

/-- Z2.g1: `inr_u ∘ fst_v ∈ Hom¹(C(v), C(u))`. -/
theorem compα_mem : compα u v ∈ Hom (cone v).toQuasiCohesive (cone u).toQuasiCohesive 1 := by
  have h := comp_mem _ _ _ (coneInr_mem_hom u) (coneFst_mem_hom v)
  rwa [zero_add] at h

/-- Z2.g1: `inr_u ∘ fst_v` is closed. -/
theorem δ_compα : δ (cone v).toQuasiCohesive (cone u).toQuasiCohesive 1 (compα u v) = 0 := by
  have h := δ_comp (cone v).toQuasiCohesive X₂.toQuasiCohesive (cone u).toQuasiCohesive 0 1
    (coneInr X₁ X₂) (coneFst X₂ X₃)
  rw [zero_add] at h
  erw [h, δ_coneInr, δ_coneFst, LinearMap.zero_comp, smul_zero, add_zero]

/-- Z2.g1: the second component `inr_{uv} ∘ snd_v : C(v) → C(v ∘ u)` (degree `0`) of
`compHom`. -/
abbrev compβ : (cone v).T →ₗ[k] (cone (compZ0 _ _ _ v u)).T :=
  (coneInrZ0 (compZ0 _ _ _ v u)).1 ∘ₗ coneSnd X₂ X₃

/-- Z2.g1: `inr_{uv} ∘ snd_v ∈ Hom⁰(C(v), C(v ∘ u))`. -/
theorem compβ_mem :
    compβ u v ∈ Hom (cone v).toQuasiCohesive (cone (compZ0 _ _ _ v u)).toQuasiCohesive 0 := by
  have h := comp_mem (cone v).toQuasiCohesive X₃.toQuasiCohesive
    (cone (compZ0 _ _ _ v u)).toQuasiCohesive (coneInr_mem_hom (compZ0 _ _ _ v u))
    (coneSnd_mem_hom v)
  exact h

/-- Z2.g1: typing helper, `snd_v : C(v) → X₃`. -/
private abbrev sndV : (cone v).T →ₗ[k] X₃.T := coneSnd X₂ X₃

/-- Z2.g1: typing helper, `fst_v : C(v) → X₂`. -/
private abbrev fstV : (cone v).T →ₗ[k] X₂.T := coneFst X₂ X₃

/-- Z2.g1: typing helper, `inr_{uv} : X₃ → C(v ∘ u)`. -/
private abbrev inrUV : X₃.T →ₗ[k] (cone (compZ0 _ _ _ v u)).T :=
  (coneInrZ0 (compZ0 _ _ _ v u)).1

/-- Z2.g1: `δ(inr_{uv} ∘ snd_v) = −inr_{uv} ∘ v ∘ fst_v = −m₁ ∘ (inr_u ∘ fst_v)`. -/
theorem δ_compβ :
    δ (cone v).toQuasiCohesive (cone (compZ0 _ _ _ v u)).toQuasiCohesive 0 (compβ u v) =
      -((compMor₁ u v).1 ∘ₗ compα u v) := by
  have h : δ (cone v).toQuasiCohesive (cone (compZ0 _ _ _ v u)).toQuasiCohesive 0 (compβ u v) =
      δ X₃.toQuasiCohesive (cone (compZ0 _ _ _ v u)).toQuasiCohesive 0 (inrUV u v) ∘ₗ sndV v +
        (0 : ℤ).negOnePow • (inrUV u v ∘ₗ
          δ (cone v).toQuasiCohesive X₃.toQuasiCohesive 0 (sndV v)) :=
    δ_comp (cone v).toQuasiCohesive X₃.toQuasiCohesive
      (cone (compZ0 _ _ _ v u)).toQuasiCohesive 0 0 (inrUV u v) (sndV v)
  have hm : (compMor₁ u v).1 ∘ₗ (coneInrZ0 u).1 = inrUV u v ∘ₗ v.1 :=
    coneMap_coneInr u (compZ0 _ _ _ v u) (idZ0 _) v 0 (Submodule.zero_mem _) (compMor₁_cond u v)
  have hs : δ (cone v).toQuasiCohesive X₃.toQuasiCohesive 0 (sndV v) =
      -(v.1 ∘ₗ fstV v) := δ_coneSnd v
  have hi : δ X₃.toQuasiCohesive (cone (compZ0 _ _ _ v u)).toQuasiCohesive 0 (inrUV u v) =
      0 := δ_coneInr _
  refine h.trans (LinearMap.ext fun z => ?_)
  have e1 := LinearMap.congr_fun hi (sndV v z)
  have e2 := LinearMap.congr_fun hs z
  have e3 := LinearMap.congr_fun hm (fstV v z)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.neg_apply] at e1 e2 e3 ⊢
  refine (congrArg₂ (· + ·) e1
    (congrArg (fun y => (0 : ℤ).negOnePow • inrUV u v y) e2)).trans ?_
  refine Eq.trans ?_ (congrArg Neg.neg e3).symm
  simp only [LinearMap.zero_apply, Int.negOnePow_zero, one_smul, zero_add, map_neg]

/-- **Z2.g1.** Mathlib `MappingConeCompHomotopyEquiv.hom`. The comparison map
`lift_{m₁} (inr_u ∘ fst_v) (inr_{uv} ∘ snd_v) : C(v) → C(m₁)`. -/
def compHom : Z0 (cone v).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive :=
  coneLift (compMor₁ u v) (compα u v) (compα_mem u v) (δ_compα u v) (compβ u v) (compβ_mem u v)
    (δ_compβ u v)

/-- Z2.g1: the first component `inl_v ∘ snd_u : C(u) → C(v)` (degree `−1`) of `compInv`. -/
abbrev compα' : (cone u).T →ₗ[k] (cone v).T := coneInl X₂ X₃ ∘ₗ coneSnd X₁ X₂

/-- Z2.g1: typing helper, `snd_u : C(u) → X₂`. -/
private abbrev sndU : (cone u).T →ₗ[k] X₂.T := coneSnd X₁ X₂

/-- Z2.g1: typing helper, `fst_u : C(u) → X₁`. -/
private abbrev fstU : (cone u).T →ₗ[k] X₁.T := coneFst X₁ X₂

/-- Z2.g1: typing helper, `inl_v : X₂ → C(v)`. -/
private abbrev inlV : X₂.T →ₗ[k] (cone v).T := coneInl X₂ X₃

/-- Z2.g1: typing helper, `inr_v : X₃ → C(v)`. -/
private abbrev inrV : X₃.T →ₗ[k] (cone v).T := coneInr X₂ X₃

/-- Z2.g1: typing helper, `fst_{uv} : C(v ∘ u) → X₁`. -/
private abbrev fstUV : (cone (compZ0 _ _ _ v u)).T →ₗ[k] X₁.T := coneFst X₁ X₃

/-- Z2.g1: typing helper, `snd_{uv} : C(v ∘ u) → X₃`. -/
private abbrev sndUV : (cone (compZ0 _ _ _ v u)).T →ₗ[k] X₃.T := coneSnd X₁ X₃

/-- Z2.g1: typing helper, `inl_{uv} : X₁ → C(v ∘ u)`. -/
private abbrev inlUV : X₁.T →ₗ[k] (cone (compZ0 _ _ _ v u)).T := coneInl X₁ X₃

/-- Z2.g1: `m₁ z = inl_{uv} (fst_u z) + inr_{uv} (v (snd_u z))`. -/
private theorem compMor₁_apply (z : (cone u).T) :
    (compMor₁ u v).1 z = inlUV u v (fstU u z) + inrUV u v (v.1 (sndU u z)) := by
  change (coneInl X₁ X₃ (fstU u z) + coneInr X₁ X₃ (0 : X₃.T)) +
    coneInr X₁ X₃ (v.1 (sndU u z)) = _
  simp only [map_zero, add_zero]
  rfl

/-- Z2.g1: `m₂ w = inl_v (u (fst_{uv} w)) + inr_v (snd_{uv} w)`. -/
private theorem compMor₂_apply (w : (cone (compZ0 _ _ _ v u)).T) :
    (compMor₂ u v).1 w = inlV v (u.1 (fstUV u v w)) + inrV v (sndUV u v w) := by
  change (coneInl X₂ X₃ (u.1 (fstUV u v w)) + coneInr X₂ X₃ (0 : X₃.T)) +
    coneInr X₂ X₃ (sndUV u v w) = _
  simp only [map_zero, add_zero]
  rfl

/-- Z2.g1: `fst_{uv} (m₁ z) = fst_u z`. -/
private theorem fstUV_compMor₁ (z : (cone u).T) : fstUV u v ((compMor₁ u v).1 z) = fstU u z := by
  refine (congrArg (fstUV u v) (compMor₁_apply u v z)).trans ?_
  have a1 : fstUV u v (inlUV u v (fstU u z)) = fstU u z :=
    LinearMap.congr_fun (coneFst_coneInl X₁ X₃) _
  have a2 : fstUV u v (inrUV u v (v.1 (sndU u z))) = 0 :=
    LinearMap.congr_fun (coneFst_coneInr X₁ X₃) _
  simp only [map_add, a1, a2, add_zero]

/-- Z2.g1: `snd_{uv} (m₁ z) = v (snd_u z)`. -/
private theorem sndUV_compMor₁ (z : (cone u).T) :
    sndUV u v ((compMor₁ u v).1 z) = v.1 (sndU u z) := by
  refine (congrArg (sndUV u v) (compMor₁_apply u v z)).trans ?_
  have a1 : sndUV u v (inlUV u v (fstU u z)) = 0 :=
    LinearMap.congr_fun (coneSnd_coneInl X₁ X₃) _
  have a2 : sndUV u v (inrUV u v (v.1 (sndU u z))) = v.1 (sndU u z) :=
    LinearMap.congr_fun (coneSnd_coneInr X₁ X₃) _
  simp only [map_add, a1, a2, zero_add]

/-- Z2.g1: `inl_v ∘ snd_u ∈ Hom⁻¹(C(u), C(v))`. -/
theorem compα'_mem : compα' u v ∈ Hom (cone u).toQuasiCohesive (cone v).toQuasiCohesive (-1) :=
  comp_mem_eq (M₁ := (cone u).toQuasiCohesive) (M₂ := X₂.toQuasiCohesive)
    (M₃ := (cone v).toQuasiCohesive) (-1) (by norm_num) (coneInl_mem_hom v) (coneSnd_mem_hom u)

/-- Z2.g1: `δ(inl_v ∘ snd_u) = inr_v v snd_u + inl_v u fst_u = m₂ ∘ m₁`. -/
theorem δ_compα' :
    δ (cone u).toQuasiCohesive (cone v).toQuasiCohesive (-1) (compα' u v) =
      (compMor₂ u v).1 ∘ₗ (compMor₁ u v).1 := by
  have h : δ (cone u).toQuasiCohesive (cone v).toQuasiCohesive (-1) (compα' u v) =
      δ X₂.toQuasiCohesive (cone v).toQuasiCohesive (-1) (inlV v) ∘ₗ sndU u +
        (-1 : ℤ).negOnePow • (inlV v ∘ₗ
          δ (cone u).toQuasiCohesive X₂.toQuasiCohesive 0 (sndU u)) :=
    δ_comp_eq (M₁ := (cone u).toQuasiCohesive) (M₂ := X₂.toQuasiCohesive)
      (M₃ := (cone v).toQuasiCohesive) (-1) 0 (-1) (by norm_num) (inlV v) (sndU u)
  have hl : δ X₂.toQuasiCohesive (cone v).toQuasiCohesive (-1) (inlV v) =
      inrV v ∘ₗ v.1 := δ_coneInl v
  have hs : δ (cone u).toQuasiCohesive X₂.toQuasiCohesive 0 (sndU u) =
      -(u.1 ∘ₗ fstU u) := δ_coneSnd u
  refine h.trans (LinearMap.ext fun z => ?_)
  have e1 := LinearMap.congr_fun hl (sndU u z)
  have e2 := LinearMap.congr_fun hs z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.neg_apply] at e1 e2 ⊢
  refine (congrArg₂ (· + ·) e1
    (congrArg (fun y => (-1 : ℤ).negOnePow • inlV v y) e2)).trans ?_
  refine Eq.trans ?_ (compMor₂_apply u v _).symm
  refine Eq.trans ?_ (congrArg₂ (fun a b => inlV v (u.1 a) + inrV v b)
    (fstUV_compMor₁ u v z).symm (sndUV_compMor₁ u v z).symm)
  simp only [map_neg, Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg]
  abel

/-- **Z2.g1.** Mathlib `MappingConeCompHomotopyEquiv.inv`. The comparison map
`desc_{m₁} (inl_v ∘ snd_u) m₂ : C(m₁) → C(v)`. -/
def compInv : Z0 (cone (compMor₁ u v)).toQuasiCohesive (cone v).toQuasiCohesive :=
  coneDesc (compMor₁ u v) (compα' u v) (compα'_mem u v) (compMor₂ u v) (δ_compα' u v)

/-- Z2.g1: typing helper, `inl_u : X₁ → C(u)`. -/
private abbrev inlU : X₁.T →ₗ[k] (cone u).T := coneInl X₁ X₂

/-- Z2.g1: typing helper, `inr_u : X₂ → C(u)`. -/
private abbrev inrU : X₂.T →ₗ[k] (cone u).T := coneInr X₁ X₂

/-- Z2.g1: typing helper, `fst_D : D → C(u)` for `D = C(m₁)`. -/
private abbrev fstD : (cone (compMor₁ u v)).T →ₗ[k] (cone u).T :=
  coneFst (cone u) (cone (compZ0 _ _ _ v u))

/-- Z2.g1: typing helper, `snd_D : D → C(v ∘ u)`. -/
private abbrev sndD : (cone (compMor₁ u v)).T →ₗ[k] (cone (compZ0 _ _ _ v u)).T :=
  coneSnd (cone u) (cone (compZ0 _ _ _ v u))

/-- Z2.g1: typing helper, `inl_D : C(u) → D`. -/
private abbrev inlD : (cone u).T →ₗ[k] (cone (compMor₁ u v)).T :=
  coneInl (cone u) (cone (compZ0 _ _ _ v u))

/-- Z2.g1: typing helper, `inr_D : C(v ∘ u) → D`. -/
private abbrev inrD : (cone (compZ0 _ _ _ v u)).T →ₗ[k] (cone (compMor₁ u v)).T :=
  coneInr (cone u) (cone (compZ0 _ _ _ v u))

/-- Z2.g1: `hom z = inl_D (inr_u (fst_v z)) + inr_D (inr_{uv} (snd_v z))` (rfl). -/
private theorem compHom_apply (z : (cone v).T) :
    (compHom u v).1 z = inlD u v (compα u v z) + inrD u v (compβ u v z) := rfl

/-- Z2.g1: `inv w = inl_v (snd_u (fst_D w)) + m₂ (snd_D w)` (rfl). -/
private theorem compInv_apply (w : (cone (compMor₁ u v)).T) :
    (compInv u v).1 w = compα' u v (fstD u v w) + (compMor₂ u v).1 (sndD u v w) := rfl

/-- Z2.g1: `fst_D ∘ hom = inr_u ∘ fst_v`, pointwise. -/
private theorem fstD_compHom (z : (cone v).T) :
    fstD u v ((compHom u v).1 z) = compα u v z :=
  LinearMap.congr_fun (coneFst_coneLift (compMor₁ u v) (compα u v) (compα_mem u v)
    (δ_compα u v) (compβ u v) (compβ_mem u v) (δ_compβ u v)) z

/-- Z2.g1: `snd_D ∘ hom = inr_{uv} ∘ snd_v`, pointwise. -/
private theorem sndD_compHom (z : (cone v).T) :
    sndD u v ((compHom u v).1 z) = compβ u v z :=
  LinearMap.congr_fun (coneSnd_coneLift (compMor₁ u v) (compα u v) (compα_mem u v)
    (δ_compα u v) (compβ u v) (compβ_mem u v) (δ_compβ u v)) z

/-- Z2.g1: `m₂ (inr_{uv} y) = inr_v y`. -/
private theorem compMor₂_inrUV (y : X₃.T) : (compMor₂ u v).1 (inrUV u v y) = inrV v y := by
  refine (compMor₂_apply u v _).trans ?_
  have a1 : fstUV u v (inrUV u v y) = 0 := LinearMap.congr_fun (coneFst_coneInr X₁ X₃) y
  have a2 : sndUV u v (inrUV u v y) = y := LinearMap.congr_fun (coneSnd_coneInr X₁ X₃) y
  refine (congrArg₂ (· + ·) (congrArg (fun t => inlV v (u.1 t)) a1)
    (congrArg (inrV v) a2)).trans ?_
  simp only [map_zero, zero_add]

/-- **Z2.g1.** `compInv ∘ compHom = id` (Mathlib `MappingConeCompHomotopyEquiv.hom_inv_id`). -/
theorem compInv_compHom : (compInv u v).1 ∘ₗ (compHom u v).1 = LinearMap.id := by
  refine LinearMap.ext fun z => ?_
  refine (compInv_apply u v _).trans ?_
  refine (congrArg₂ (fun a b => compα' u v a + (compMor₂ u v).1 b) (fstD_compHom u v z)
    (sndD_compHom u v z)).trans ?_
  have b1 : sndU u (inrU u (fstV v z)) = fstV v z := LinearMap.congr_fun (coneSnd_coneInr X₁ X₂) _
  refine (congrArg₂ (· + ·) (congrArg (inlV v) b1) (compMor₂_inrUV u v _)).trans ?_
  exact LinearMap.congr_fun (coneInl_coneFst_add X₂ X₃) z

/-- Z2.g1: the homotopy `H = −inl_D ∘ inl_u ∘ fst_{uv} ∘ snd_D` on `D = C(m₁)`. -/
abbrev compH : (cone (compMor₁ u v)).T →ₗ[k] (cone (compMor₁ u v)).T :=
  -(coneInl (cone u) (cone (compZ0 _ _ _ v u)) ∘ₗ coneInl X₁ X₂ ∘ₗ coneFst X₁ X₃ ∘ₗ
    coneSnd (cone u) (cone (compZ0 _ _ _ v u)))

/-- Z2.g1: `H ∈ Hom⁻¹(D, D)`. -/
theorem compH_mem :
    compH u v ∈ Hom (cone (compMor₁ u v)).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive
      (-1) := by
  have h1 := comp_mem_eq (M₁ := (cone (compMor₁ u v)).toQuasiCohesive)
    (M₂ := (cone (compZ0 _ _ _ v u)).toQuasiCohesive) (M₃ := X₁.toQuasiCohesive) 1
    (by norm_num) (coneFst_mem_hom (compZ0 _ _ _ v u)) (coneSnd_mem_hom (compMor₁ u v))
  have h2 := comp_mem_eq (M₃ := (cone u).toQuasiCohesive) 0 (by norm_num)
    (coneInl_mem_hom u) h1
  have h3 := comp_mem_eq (M₃ := (cone (compMor₁ u v)).toQuasiCohesive) (-1) (by norm_num)
    (coneInl_mem_hom (compMor₁ u v)) h2
  exact neg_mem h3

/-- Z2.g1: `m₁ (inl_u x) = inl_{uv} x`. -/
private theorem compMor₁_inlU (x : X₁.T) :
    (compMor₁ u v).1 (inlU u x) = inlUV u v x := by
  refine (compMor₁_apply u v _).trans ?_
  have a1 : fstU u (inlU u x) = x := LinearMap.congr_fun (coneFst_coneInl X₁ X₂) x
  have a2 : sndU u (inlU u x) = 0 := LinearMap.congr_fun (coneSnd_coneInl X₁ X₂) x
  refine (congrArg₂ (fun a b => inlUV u v a + inrUV u v (v.1 b)) a1 a2).trans ?_
  simp only [map_zero, add_zero]

/-- Z2.g1: `fst_v (inv w) = snd_u (fst_D w) + u (fst_{uv} (snd_D w))`. -/
private theorem fstV_compInv (w : (cone (compMor₁ u v)).T) :
    fstV v ((compInv u v).1 w) = sndU u (fstD u v w) + u.1 (fstUV u v (sndD u v w)) := by
  refine (congrArg (fstV v) (compInv_apply u v w)).trans ?_
  refine (congrArg (fstV v) (congrArg (fun t => inlV v (sndU u (fstD u v w)) + t)
    (compMor₂_apply u v (sndD u v w)))).trans ?_
  have a1 : fstV v (inlV v (sndU u (fstD u v w))) = sndU u (fstD u v w) :=
    LinearMap.congr_fun (coneFst_coneInl X₂ X₃) _
  have a2 : fstV v (inlV v (u.1 (fstUV u v (sndD u v w)))) = u.1 (fstUV u v (sndD u v w)) :=
    LinearMap.congr_fun (coneFst_coneInl X₂ X₃) _
  have a3 : fstV v (inrV v (sndUV u v (sndD u v w))) = 0 :=
    LinearMap.congr_fun (coneFst_coneInr X₂ X₃) _
  simp only [map_add, a1, a2, a3, add_zero]

/-- Z2.g1: `snd_v (inv w) = snd_{uv} (snd_D w)`. -/
private theorem sndV_compInv (w : (cone (compMor₁ u v)).T) :
    sndV v ((compInv u v).1 w) = sndUV u v (sndD u v w) := by
  refine (congrArg (sndV v) (compInv_apply u v w)).trans ?_
  refine (congrArg (sndV v) (congrArg (fun t => inlV v (sndU u (fstD u v w)) + t)
    (compMor₂_apply u v (sndD u v w)))).trans ?_
  have a1 : sndV v (inlV v (sndU u (fstD u v w))) = 0 :=
    LinearMap.congr_fun (coneSnd_coneInl X₂ X₃) _
  have a2 : sndV v (inlV v (u.1 (fstUV u v (sndD u v w)))) = 0 :=
    LinearMap.congr_fun (coneSnd_coneInl X₂ X₃) _
  have a3 : sndV v (inrV v (sndUV u v (sndD u v w))) = sndUV u v (sndD u v w) :=
    LinearMap.congr_fun (coneSnd_coneInr X₂ X₃) _
  simp only [map_add, a1, a2, a3, zero_add]

/-- Z2.g1: `hom (inv z)` in coordinates `a = fst_D z`, `b = snd_D z`. -/
private theorem compHom_compInv_apply (z : (cone (compMor₁ u v)).T) :
    (compHom u v).1 ((compInv u v).1 z) =
      inlD u v (inrU u (sndU u (fstD u v z) + u.1 (fstUV u v (sndD u v z)))) +
        inrD u v (inrUV u v (sndUV u v (sndD u v z))) :=
  (compHom_apply u v _).trans
    (congrArg₂ (fun x y => inlD u v (inrU u x) + inrD u v (inrUV u v y))
      (fstV_compInv u v z) (sndV_compInv u v z))

/-- Z2.g1: `δ(fst_{uv} ∘ snd_D) z = fst_u (fst_D z)`. -/
private theorem δ_fstUV_sndD_apply (z : (cone (compMor₁ u v)).T) :
    δ (cone (compMor₁ u v)).toQuasiCohesive X₁.toQuasiCohesive 1 (fstUV u v ∘ₗ sndD u v) z =
      fstU u (fstD u v z) := by
  have h4 : δ (cone (compMor₁ u v)).toQuasiCohesive X₁.toQuasiCohesive 1
      (fstUV u v ∘ₗ sndD u v) =
      δ (cone (compZ0 _ _ _ v u)).toQuasiCohesive X₁.toQuasiCohesive 1 (fstUV u v) ∘ₗ sndD u v +
        (1 : ℤ).negOnePow • (fstUV u v ∘ₗ
          δ (cone (compMor₁ u v)).toQuasiCohesive (cone (compZ0 _ _ _ v u)).toQuasiCohesive 0
            (sndD u v)) :=
    δ_comp_eq (M₁ := (cone (compMor₁ u v)).toQuasiCohesive)
      (M₂ := (cone (compZ0 _ _ _ v u)).toQuasiCohesive) (M₃ := X₁.toQuasiCohesive) 1 0 1
      (by norm_num) (fstUV u v) (sndD u v)
  have h6 : δ (cone (compZ0 _ _ _ v u)).toQuasiCohesive X₁.toQuasiCohesive 1 (fstUV u v) = 0 :=
    δ_coneFst _
  have h7 : δ (cone (compMor₁ u v)).toQuasiCohesive (cone (compZ0 _ _ _ v u)).toQuasiCohesive 0
      (sndD u v) = -((compMor₁ u v).1 ∘ₗ fstD u v) := δ_coneSnd _
  refine (LinearMap.congr_fun h4 z).trans ?_
  have e6 := LinearMap.congr_fun h6 (sndD u v z)
  have e7 := LinearMap.congr_fun h7 z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.neg_apply, LinearMap.zero_apply] at e6 e7 ⊢
  refine (congrArg₂ (· + ·) e6 (congrArg (fun y => (1 : ℤ).negOnePow • fstUV u v y) e7)).trans ?_
  simp only [map_neg, Int.negOnePow_one, Units.neg_smul, one_smul, neg_neg, zero_add]
  exact fstUV_compMor₁ u v _

/-- Z2.g1: `δ(inl_u fst_{uv} snd_D) z = inr_u (u (fst_{uv} b)) − inl_u (fst_u a)`, with
`a = fst_D z`, `b = snd_D z`. -/
private theorem δ_K_apply (z : (cone (compMor₁ u v)).T) :
    δ (cone (compMor₁ u v)).toQuasiCohesive (cone u).toQuasiCohesive 0
      (inlU u ∘ₗ fstUV u v ∘ₗ sndD u v) z =
      inrU u (u.1 (fstUV u v (sndD u v z))) - inlU u (fstU u (fstD u v z)) := by
  have h3 : δ (cone (compMor₁ u v)).toQuasiCohesive (cone u).toQuasiCohesive 0
      (inlU u ∘ₗ fstUV u v ∘ₗ sndD u v) =
      δ X₁.toQuasiCohesive (cone u).toQuasiCohesive (-1) (inlU u) ∘ₗ (fstUV u v ∘ₗ sndD u v) +
        (-1 : ℤ).negOnePow • (inlU u ∘ₗ
          δ (cone (compMor₁ u v)).toQuasiCohesive X₁.toQuasiCohesive 1
            (fstUV u v ∘ₗ sndD u v)) :=
    δ_comp_eq (M₁ := (cone (compMor₁ u v)).toQuasiCohesive) (M₂ := X₁.toQuasiCohesive)
      (M₃ := (cone u).toQuasiCohesive) (-1) 1 0 (by norm_num) (inlU u) (fstUV u v ∘ₗ sndD u v)
  have h5 : δ X₁.toQuasiCohesive (cone u).toQuasiCohesive (-1) (inlU u) = inrU u ∘ₗ u.1 :=
    δ_coneInl u
  refine (LinearMap.congr_fun h3 z).trans ?_
  have e5 := LinearMap.congr_fun h5 (fstUV u v (sndD u v z))
  have e4 := δ_fstUV_sndD_apply u v z
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply] at e5 ⊢
  refine (congrArg₂ (· + ·) e5
    (congrArg (fun y => (-1 : ℤ).negOnePow • inlU u y) e4)).trans ?_
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  exact (sub_eq_add_neg _ _).symm

/-- Z2.g1: the typing helper `inl_D` is `coneInl` (rfl). -/
private theorem inlD_eq : inlD u v = coneInl (cone u) (cone (compZ0 _ _ _ v u)) := rfl

/-- Z2.g1: `δ inl_D = inr_D ∘ m₁`. -/
private theorem δ_inlD :
    δ (cone u).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive (-1) (inlD u v) =
      inrD u v ∘ₗ (compMor₁ u v).1 :=
  (congrArg _ (inlD_eq u v)).trans (δ_inl_cone_aux u (compZ0 _ _ _ v u) (compMor₁ u v))

/-- Z2.g1: `H = −(inl_D ∘ (inl_u ∘ fst_{uv} ∘ snd_D))` (rfl). -/
private theorem compH_eq :
    compH u v = -(inlD u v ∘ₗ (inlU u ∘ₗ fstUV u v ∘ₗ sndD u v)) := rfl

/-- Z2.g1: `δH` pointwise: with `K = inl_u fst_{uv} snd_D` one has
`δ(inl_D K) z = inr_D inl_{uv} fst_{uv} b − inl_D inr_u u fst_{uv} b + inl_D inl_u fst_u a`. -/
private theorem δ_compH_apply (z : (cone (compMor₁ u v)).T) :
    δ (cone (compMor₁ u v)).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive (-1)
      (compH u v) z =
      -(inrD u v (inlUV u v (fstUV u v (sndD u v z))) -
        inlD u v (inrU u (u.1 (fstUV u v (sndD u v z)))) +
        inlD u v (inlU u (fstU u (fstD u v z)))) := by
  have hneg : δ (cone (compMor₁ u v)).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive (-1)
      (compH u v) = -(δ (cone (compMor₁ u v)).toQuasiCohesive
        (cone (compMor₁ u v)).toQuasiCohesive (-1)
        (inlD u v ∘ₗ inlU u ∘ₗ fstUV u v ∘ₗ sndD u v)) :=
    (congrArg (δ (cone (compMor₁ u v)).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive
      (-1)) (compH_eq u v)).trans
      (map_neg (δ (cone (compMor₁ u v)).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive
        (-1)) (inlD u v ∘ₗ inlU u ∘ₗ fstUV u v ∘ₗ sndD u v))
  have h1 : δ (cone (compMor₁ u v)).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive (-1)
      (inlD u v ∘ₗ inlU u ∘ₗ fstUV u v ∘ₗ sndD u v) =
      δ (cone u).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive (-1) (inlD u v) ∘ₗ
        (inlU u ∘ₗ fstUV u v ∘ₗ sndD u v) + (-1 : ℤ).negOnePow • (inlD u v ∘ₗ
          δ (cone (compMor₁ u v)).toQuasiCohesive (cone u).toQuasiCohesive 0
            (inlU u ∘ₗ fstUV u v ∘ₗ sndD u v)) :=
    δ_comp_eq (M₁ := (cone (compMor₁ u v)).toQuasiCohesive) (M₂ := (cone u).toQuasiCohesive)
      (M₃ := (cone (compMor₁ u v)).toQuasiCohesive) (-1) 0 (-1) (by norm_num) (inlD u v)
      (inlU u ∘ₗ fstUV u v ∘ₗ sndD u v)
  have h2 := δ_inlD u v
  refine (congrArg (fun f => f z) hneg).trans (Eq.trans (LinearMap.neg_apply _ _) ?_)
  refine congrArg Neg.neg ?_
  refine (LinearMap.congr_fun h1 z).trans ?_
  have e2 := LinearMap.congr_fun h2 (inlU u (fstUV u v (sndD u v z)))
  have eK := δ_K_apply u v z
  have e8 := compMor₁_inlU u v (fstUV u v (sndD u v z))
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply]
  refine (congrArg₂ (· + ·) e2
    (congrArg (fun y => (-1 : ℤ).negOnePow • inlD u v y) eK)).trans ?_
  simp only [LinearMap.comp_apply, e8, map_sub, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul]
  abel

/-- **Z2.g1.** `compHom ∘ compInv − id = δH` (Mathlib
`MappingConeCompHomotopyEquiv.homotopyInvHomId`; sign checked in blueprint-tr §3d). -/
theorem compHom_compInv :
    (compHom u v).1 ∘ₗ (compInv u v).1 - LinearMap.id =
      δ (cone (compMor₁ u v)).toQuasiCohesive (cone (compMor₁ u v)).toQuasiCohesive (-1)
        (compH u v) := by
  refine LinearMap.ext fun z => ?_
  refine Eq.trans ?_ (δ_compH_apply u v z).symm
  refine (congrArg (fun t => t - z) (compHom_compInv_apply u v z)).trans ?_
  have hz : inlD u v (fstD u v z) + inrD u v (sndD u v z) = z :=
    LinearMap.congr_fun (coneInl_coneFst_add (cone u) (cone (compZ0 _ _ _ v u))) z
  have ha : inlU u (fstU u (fstD u v z)) + inrU u (sndU u (fstD u v z)) = fstD u v z :=
    LinearMap.congr_fun (coneInl_coneFst_add X₁ X₂) _
  have hb : inlUV u v (fstUV u v (sndD u v z)) + inrUV u v (sndUV u v (sndD u v z)) =
      sndD u v z :=
    LinearMap.congr_fun (coneInl_coneFst_add X₁ X₃) _
  exact alg_aux (inlD u v) (inrD u v) (inlU u) (inrU u) (inlUV u v) (inrUV u v) _ _ z _ _ _ _ _
    hz ha hb

/-- **Z2.g1.** `compInv ∘ inr_D = m₂` (Mathlib `mappingConeCompHomotopyEquiv_comm₁`). -/
theorem compInv_coneInr :
    (compInv u v).1 ∘ₗ (coneInrZ0 (compMor₁ u v)).1 = (compMor₂ u v).1 :=
  coneDesc_coneInr (compMor₁ u v) (compα' u v) (compα'_mem u v) (compMor₂ u v) (δ_compα' u v)

/-- **Z2.g1.** `w_D ∘ compHom = inr_u[1] ∘ w_v` (Mathlib `mappingConeCompHomotopyEquiv_comm₂`);
both sides are `−ι₁⁻¹ ∘ inr_u ∘ fst_v`. -/
theorem coneW_compHom :
    (coneWZ0 (compMor₁ u v)).1 ∘ₗ (compHom u v).1 =
      (shiftZ0 (coneInrZ0 u) 1).1 ∘ₗ (coneWZ0 v).1 := by
  refine LinearMap.ext fun z => ?_
  have hD := fstD_compHom u v z
  change -(shiftIota 𝒜 (cone u).Q 1).symm (fstD u v ((compHom u v).1 z)) =
    (shiftIota 𝒜 (cone u).Q 1).symm (inrU u ((shiftIota 𝒜 X₂.Q 1)
      (-(shiftIota 𝒜 X₂.Q 1).symm (fstV v z))))
  refine (congrArg (fun t => -(shiftIota 𝒜 (cone u).Q 1).symm t) hD).trans ?_
  simp only [map_neg, LinearEquiv.apply_symm_apply]
  rfl

end Cohesive
