import Cohesivemodules.Algebra.BaseChangeExt
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.Ab

set_option linter.style.header false

/-!
# Hom complexes along a map of (possibly curved) dgas, and A10.a along a dga map

Used by C4 step 3 (blueprint §4, `quasiIso_Φ`). For a dga map `f : A → B`, a quasi-cohesive
`A`-module `M` and a quasi-cohesive `B`-module `N`:
* `HomAlongT f M N n`: degree-`n` `k`-linear maps `χ : Tot M → Tot N` semilinear along `f`,
  `χ(a·x) = (-1)^{n|a|} f(a)·χ(x)` (A9's `HomAlong` with an arbitrary target; equal to it for
  `N = f^*M₂`, `homAlongT_baseChange`);
* `δAl`: the differential `χ ↦ 𝕏_N ∘ χ - (-1)^n χ ∘ 𝕏_M` (conventions §2, as A4's `δ`);
* `alongComplex f M N`: the resulting complex of abelian groups;
* `alongPre`: precomposition with a closed degree-`0` map `θ : M' → M`; a quasi-isomorphism when
  `θ` is a homotopy equivalence (`quasiIso_alongPre`);
* `famComplex`: A10.a's complex `Hom^•_R(W, N)` of families (`HomR`, `homRδ`);
* `alongEv`: evaluation on the generators `1 ⊗ (1 ⊗ w)` of `A ⊗_R W`, from
  `alongComplex f (A ⊗_R W) N` to the families for `f₀ ∘ ρ`; an isomorphism (`isIso_alongEv`,
  A10.a along `f`).

Not part of the main statement; not frozen.

Part 1 of 2 of the original `Algebra/HomAlongT.lean`, split for size; continued in
`Algebra/HomAlongT.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]

variable (f : DgaHom 𝒜 ℬ)

/-! ### The complex of maps along `f` -/

/-- Degree-`n` `k`-linear maps `Tot(M) → Tot(N)` semilinear along `f`:
`χ(a·x) = (-1)^{n|a|} f(a)·χ(x)` for homogeneous `a` (A9's `HomAlong`, arbitrary target). -/
def HomAlongT (M : QuasiCohesive 𝒜) (N : QuasiCohesive ℬ) (n : ℤ) :
    Submodule k (M.T →ₗ[k] N.T) where
  carrier := {χ | (∀ {m : ℤ} {x : M.T}, x ∈ totDeg 𝒜 M.Q m → χ x ∈ totDeg ℬ N.Q (m + n)) ∧
    ∀ {p : ℤ} {a : A}, a ∈ 𝒜 p → ∀ x : M.T, χ (a • x) = (n * p).negOnePow • f a • χ x}
  add_mem' := fun {φ ψ} hφ hψ =>
    ⟨fun hx => add_mem (hφ.1 hx) (hψ.1 hx), fun ha x => by
      simp only [LinearMap.add_apply, hφ.2 ha, hψ.2 ha, smul_add]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => by simp⟩
  smul_mem' := fun r φ hφ =>
    ⟨fun hx => Submodule.smul_mem _ r (hφ.1 hx), fun ha x => by
      simp only [LinearMap.smul_apply, hφ.2 ha]
      rw [smul_comm r, smul_comm r]⟩

/-- For `N = f^*M₂`, `HomAlongT` is A9's `HomAlong` (rfl). -/
theorem homAlongT_baseChange (M₁ M₂ : QuasiCohesive 𝒜) (n : ℤ) :
    HomAlongT f M₁ (M₂.baseChange f) n = HomAlong f M₁ M₂ n := rfl

/-- The differential `δχ = 𝕏_N ∘ χ - (-1)^n χ ∘ 𝕏_M` (conventions §2, as A4's `δ`). -/
def δAl (M : QuasiCohesive 𝒜) (N : QuasiCohesive ℬ) (n : ℤ) :
    (M.T →ₗ[k] N.T) →ₗ[k] (M.T →ₗ[k] N.T) where
  toFun χ := N.X ∘ₗ χ - n.negOnePow • (χ ∘ₗ M.X)
  map_add' χ ψ := by
    simp only [LinearMap.comp_add, LinearMap.add_comp, smul_add]
    abel
  map_smul' r χ := by
    simp only [LinearMap.comp_smul, LinearMap.smul_comp, RingHom.id_apply, smul_sub]
    rw [smul_comm r]

/-- `δAl` on an element (rfl). -/
theorem δAl_apply (M : QuasiCohesive 𝒜) (N : QuasiCohesive ℬ) (n : ℤ) (χ : M.T →ₗ[k] N.T)
    (x : M.T) : δAl M N n χ x = N.X (χ x) - n.negOnePow • χ (M.X x) := rfl

variable {f}

/-- `δAl` maps `HomAlongT f M N n` to `HomAlongT f M N (n + 1)` (as A4's `δ_mem`). -/
theorem δAl_mem {M : QuasiCohesive 𝒜} {N : QuasiCohesive ℬ} {n : ℤ} {χ : M.T →ₗ[k] N.T}
    (hχ : χ ∈ HomAlongT f M N n) : δAl M N n χ ∈ HomAlongT f M N (n + 1) := by
  obtain ⟨h₁, h₂⟩ := hχ
  refine ⟨fun {m x} hx => ?_, fun {p a} ha x => ?_⟩
  · have e1 : N.X (χ x) ∈ totDeg ℬ N.Q (m + (n + 1)) := by
      have := N.X_mem (h₁ hx); rwa [add_assoc] at this
    have e2 : χ (M.X x) ∈ totDeg ℬ N.Q (m + (n + 1)) := by
      have := h₁ (M.X_mem hx); rwa [add_assoc, add_comm 1 n] at this
    simp only [δAl_apply, Units.smul_def]
    exact sub_mem e1 (Submodule.smul_of_tower_mem _ _ e2)
  · have hda := GCDga.d_mem (𝒜 := 𝒜) ha
    have hfa := f.map_mem ha
    simp only [δAl_apply, M.leibniz ha, map_add, h₂ ha, h₂ hda, N.leibniz hfa, Units.smul_def,
      map_zsmul, f.map_d]
    simp only [negOnePow_parity, parity_simps]
    by_cases hn : Even n <;> by_cases hp : Even p <;> simp [hn, hp, smul_sub, smul_neg]

/-- `δAl ∘ δAl = 0` on maps along `f` (the curvatures cancel: `f(c) = c`, `DgaHom.map_c`). -/
theorem δAl_δAl {M : QuasiCohesive 𝒜} {N : QuasiCohesive ℬ} {n : ℤ} {χ : M.T →ₗ[k] N.T}
    (hχ : χ ∈ HomAlongT f M N n) : δAl M N (n + 1) (δAl M N n χ) = 0 := by
  ext x
  have hc : χ (GCDga.c (𝒜 := 𝒜) • x) = GCDga.c (𝒜 := ℬ) • χ x := by
    rw [hχ.2 (GCDga.c_mem (𝒜 := 𝒜)), show n * 2 = 2 * n by ring, Int.negOnePow_two_mul,
      one_smul, ← f.map_c]
  simp only [δAl_apply, map_sub, Units.smul_def, map_zsmul, M.flat, N.flat, hc,
    LinearMap.zero_apply]
  simp only [negOnePow_parity, parity_simps]
  by_cases hn : Even n
  · simp [hn]
  · simp [hn]; abel

variable (f)

/-- The differential of `alongComplex` in degree `n`. -/
def alongD (M : QuasiCohesive 𝒜) (N : QuasiCohesive ℬ) (n : ℤ) :
    HomAlongT f M N n →ₗ[k] HomAlongT f M N (n + 1) :=
  (δAl M N n).restrict fun _ hχ => δAl_mem hχ

/-- The complex `Hom^•_{along f}(M, N)` of abelian groups, differential `δAl`. -/
def alongComplex (M : QuasiCohesive 𝒜) (N : QuasiCohesive ℬ) :
    CochainComplex AddCommGrpCat.{0} ℤ :=
  CochainComplex.of (fun n => AddCommGrpCat.of (HomAlongT f M N n))
    (fun n => AddCommGrpCat.ofHom (alongD f M N n).toAddMonoidHom)
    (fun n => by
      ext χ x
      exact LinearMap.congr_fun (δAl_δAl χ.2) x)

/-- `alongComplex` in degree `n` (rfl). -/
theorem alongComplex_X (M : QuasiCohesive 𝒜) (N : QuasiCohesive ℬ) (n : ℤ) :
    (alongComplex f M N).X n = AddCommGrpCat.of (HomAlongT f M N n) := rfl

/-! ### Precomposition with a homotopy equivalence -/

variable {f}

/-- Precomposition with `θ ∈ Hom^m(M', M)` maps `HomAlongT f M N n` to degree `n + m`. -/
theorem comp_mem_homAlongT {M M' : QuasiCohesive 𝒜} {N : QuasiCohesive ℬ} {n m : ℤ}
    {χ : M.T →ₗ[k] N.T} {θ : M'.T →ₗ[k] M.T} (hχ : χ ∈ HomAlongT f M N n)
    (hθ : θ ∈ Hom M' M m) : χ ∘ₗ θ ∈ HomAlongT f M' N (n + m) := by
  refine ⟨fun {q x} hx => ?_, fun {p a} ha x => ?_⟩
  · have := hχ.1 (hθ.1 hx)
    rwa [add_assoc, add_comm m n] at this
  · simp only [LinearMap.comp_apply, hθ.2 ha, Units.smul_def, map_zsmul, hχ.2 ha, smul_smul]
    rw [← Units.val_mul, ← Int.negOnePow_add, add_mul, add_comm (n * p)]

/-- `δAl` commutes with precomposition by a closed degree-`0` map `θ`. -/
theorem δAl_comp_Z0 {M M' : QuasiCohesive 𝒜} {N : QuasiCohesive ℬ} (n : ℤ)
    (χ : M.T →ₗ[k] N.T) (θ : Z0 M' M) : δAl M' N n (χ ∘ₗ θ.1) = δAl M N n χ ∘ₗ θ.1 := by
  have hθ : M.X ∘ₗ θ.1 = θ.1 ∘ₗ M'.X := by
    have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 θ.2).2
    rw [δ_apply] at this
    simpa [sub_eq_zero] using this
  ext x
  have := LinearMap.congr_fun hθ x
  simp only [δAl_apply, LinearMap.comp_apply] at this ⊢
  rw [this]

variable (f)

/-- Precomposition with a closed degree-`0` map `θ : M' → M`, `χ ↦ χ ∘ θ`, as a chain map
`alongComplex f M N ⟶ alongComplex f M' N`. -/
def alongPre {M M' : QuasiCohesive 𝒜} (N : QuasiCohesive ℬ) (θ : Z0 M' M) :
    alongComplex f M N ⟶ alongComplex f M' N :=
  CochainComplex.ofHom
    (fun n => AddCommGrpCat.ofHom
      { toFun := fun χ => ⟨χ.1 ∘ₗ θ.1, by
          simpa only [add_zero] using comp_mem_homAlongT χ.2 (Submodule.mem_inf.1 θ.2).1⟩
        map_zero' := Subtype.ext (LinearMap.zero_comp _)
        map_add' := fun χ ψ => Subtype.ext (LinearMap.add_comp _ _ _) })
    (fun n => by
      simp only [alongComplex, CochainComplex.of_d]
      ext χ x
      exact LinearMap.congr_fun (δAl_comp_Z0 n χ.1 θ) x)

/-- `alongPre` on an element. -/
theorem alongPre_f_apply {M M' : QuasiCohesive 𝒜} (N : QuasiCohesive ℬ) (θ : Z0 M' M) (n : ℤ)
    (χ : HomAlongT f M N n) :
    (((alongPre f N θ).f n).hom χ).1 = χ.1 ∘ₗ θ.1 := rfl

/-- Leibniz rule for `δAl` and precomposition with a map `φ` out of another module. -/
private theorem δAl_comp_hom {M M' : QuasiCohesive 𝒜} {N : QuasiCohesive ℬ} (n m : ℤ)
    (χ : M.T →ₗ[k] N.T) (φ : M'.T →ₗ[k] M.T) :
    δAl M' N (n + m) (χ ∘ₗ φ) = δAl M N n χ ∘ₗ φ + n.negOnePow • (χ ∘ₗ δ M' M m φ) := by
  ext x
  simp only [δAl_apply, δ_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_sub, Units.smul_def, map_zsmul, smul_sub, smul_smul,
    Int.negOnePow_add]
  abel

/-- The homotopy component `χ ↦ (-1)^i χ ∘ h` of degree `-1` on `alongComplex f P N`. -/
private def alongHomMap (f : DgaHom 𝒜 ℬ) {P : QuasiCohesive 𝒜} (N : QuasiCohesive ℬ)
    (h : Hom P P (-1)) (i j : ℤ) (hij : i + -1 = j) :
    (alongComplex f P N).X i ⟶ (alongComplex f P N).X j :=
  AddCommGrpCat.ofHom
    { toFun := fun χ => ⟨i.negOnePow • (χ.1 ∘ₗ h.1), by
        subst hij
        exact Submodule.smul_of_tower_mem _ _ (comp_mem_homAlongT χ.2 h.2)⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun χ ψ => Subtype.ext (by
        simp only [Submodule.coe_add, LinearMap.add_comp, smul_add]) }

/-- The homotopy of degree `-1` on `alongComplex f P N` (zero off `i + -1 = j`). -/
private def alongHomHom (f : DgaHom 𝒜 ℬ) {P : QuasiCohesive 𝒜} (N : QuasiCohesive ℬ)
    (h : Hom P P (-1)) (i j : ℤ) : (alongComplex f P N).X i ⟶ (alongComplex f P N).X j :=
  if hij : i + -1 = j then alongHomMap f N h i j hij else 0

/-- If `Θ - id = δh` then precomposition with `Θ` is homotopic to the identity. -/
private theorem alongPre_homotopic {P : QuasiCohesive 𝒜} (N : QuasiCohesive ℬ) (Θ : Z0 P P)
    (h : Hom P P (-1)) (hΘ : δ P P (-1) h.1 = Θ.1 - (idZ0 P).1) :
    Nonempty (Homotopy (alongPre f N Θ) (𝟙 (alongComplex f P N))) := by
  refine ⟨{ hom := alongHomHom f N h, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    have : ¬ (i + -1 = j) := by
      intro h'
      apply hij
      change j + 1 = i
      omega
    simp only [alongHomHom, this, ↓reduceDIte]
  · intro i'
    obtain ⟨i, rfl⟩ : ∃ i, i' = i + 1 := ⟨i' - 1, by omega⟩
    have e1 : (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) := rfl
    have e2 : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    rw [dNext_eq _ e1, prevD_eq _ e2]
    have h1 : i + 1 + -1 = i := by omega
    have h2 : i + 1 + 1 + -1 = i + 1 := by omega
    have d1 : (alongComplex f P N).d (i + 1) (i + 1 + 1) =
      AddCommGrpCat.ofHom (alongD f P N (i + 1)).toAddMonoidHom := by
      simp only [alongComplex, CochainComplex.of_d]
    have d2 : (alongComplex f P N).d i (i + 1) =
      AddCommGrpCat.ofHom (alongD f P N i).toAddMonoidHom := by
      simp only [alongComplex, CochainComplex.of_d]
    rw [d1, d2]
    have k1 : alongHomHom f N h (i + 1 + 1) (i + 1) = alongHomMap f N h _ _ h2 := by
      simp only [alongHomHom, h2, ↓reduceDIte]
    have k2 : alongHomHom f N h (i + 1) i = alongHomMap f N h _ _ h1 := by
      simp only [alongHomHom, h1, ↓reduceDIte]
    rw [k1, k2]
    ext χ
    have L := δAl_comp_hom (i + 1) (-1) χ.1 h.1
    rw [h1] at L
    apply Subtype.ext
    show χ.1 ∘ₗ Θ.1 = (i + 1 + 1).negOnePow • (δAl P N (i + 1) χ.1 ∘ₗ h.1) +
      δAl P N i ((i + 1).negOnePow • (χ.1 ∘ₗ h.1)) + χ.1
    have hs : ∀ (u : ℤˣ) (g : P.T →ₗ[k] N.T), δAl P N i (u • g) = u • δAl P N i g := by
      intro u g
      ext x
      simp only [δAl_apply, LinearMap.smul_apply, Units.smul_def, map_zsmul, smul_sub]
    rw [hs, L, hΘ]
    ext x
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, map_sub, Units.smul_def, Int.negOnePow_succ, Units.val_neg,
      neg_smul, smul_add, smul_neg, smul_sub, neg_neg, smul_smul, LinearMap.neg_apply, idZ0,
      LinearMap.id_apply]
    have uu : ((i.negOnePow : ℤˣ) : ℤ) * (i.negOnePow : ℤˣ) = 1 := by
      rw [← Units.val_mul, Int.units_mul_self]; rfl
    simp only [neg_mul, uu, neg_smul, one_smul]
    abel

/-- **C4 step 3.** Precomposition with a homotopy equivalence `θ : M' → M` (inverse `θ'`,
`θ' ∘ θ ∼ id`, `θ ∘ θ' ∼ id` in `H0`) is a quasi-isomorphism of the along complexes (it is a
homotopy equivalence: a homotopy `h` with `δh = θθ' - id` gives `χ ↦ (-1)^n χ ∘ h`). -/
theorem quasiIso_alongPre {M M' : QuasiCohesive 𝒜} (N : QuasiCohesive ℬ) (θ : Z0 M' M)
    (θ' : Z0 M M')
    (h₁ : (Submodule.Quotient.mk (compZ0 _ _ _ θ' θ) : H0 M' M') =
      Submodule.Quotient.mk (idZ0 M'))
    (h₂ : (Submodule.Quotient.mk (compZ0 _ _ _ θ θ') : H0 M M) =
      Submodule.Quotient.mk (idZ0 M)) :
    QuasiIso (alongPre f N θ) := by
  have key : ∀ {P : QuasiCohesive 𝒜} (Θ : Z0 P P),
      (Submodule.Quotient.mk Θ : H0 P P) = Submodule.Quotient.mk (idZ0 P) →
      Nonempty (Homotopy (alongPre f N Θ) (𝟙 (alongComplex f P N))) := by
    intro P Θ hΘ
    have hab := Submodule.Quotient.eq _ |>.1 hΘ
    rw [Submodule.mem_comap] at hab
    obtain ⟨h, hh, hδ⟩ := hab
    exact alongPre_homotopic f N Θ ⟨h, hh⟩ hδ
  obtain ⟨H1⟩ := key (compZ0 _ _ _ θ θ') h₂
  obtain ⟨H2⟩ := key (compZ0 _ _ _ θ' θ) h₁
  exact (HomotopyEquiv.mk (alongPre f N θ) (alongPre f N θ')
    (by exact H1) (by exact H2)).quasiIso_hom

end Cohesive
end
