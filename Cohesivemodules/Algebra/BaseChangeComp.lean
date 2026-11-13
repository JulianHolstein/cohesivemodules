import Cohesivemodules.Algebra.BaseChangeFunctor

set_option linter.style.header false

/-!
# A9: base change along maps of (possibly curved) dgas (part 2 of 3)

Split from `Algebra/BaseChange.lean` for size;
continues `Algebra/BaseChangeFunctor.lean`.
-/

noncomputable section
namespace Cohesive
open TensorProduct DirectSum
variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
variable (f : DgaHom 𝒜 ℬ) (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
variable (M : QuasiCohesive 𝒜)

/-! ## A9.a: base change along a composite

For maps of (possibly curved) dgas `f : A → B` and `g : B → C`, the generators
 `C⁰ ⊗_{A⁰} Q^p` of `(g ∘ f)^*M` and
`C⁰ ⊗_{B⁰} (B⁰ ⊗_{A⁰} Q^p)` of `g^*(f^*M)` are identified by `γ ⊗ q ↦ γ ⊗ (1 ⊗ q)`, with
inverse `γ ⊗ (β ⊗ q) ↦ γ g(β) ⊗ q`. -/

section Composite

variable {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]

/-- **A9.a** The composite `g ∘ f` of maps of (possibly curved) dgas. -/
def DgaHom.comp (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ) : DgaHom 𝒜 𝒞 where
  toAlgHom := g.toAlgHom.comp f.toAlgHom
  map_mem ha := g.map_mem (f.map_mem ha)
  map_d a := by
    show g (f _) = GCDga.d (𝒜 := 𝒞) (g (f a))
    rw [f.map_d, g.map_d]
  map_c := by
    show g (f _) = _
    rw [f.map_c, g.map_c]

/-- A9.a: `(g ∘ f)(a) = g(f(a))`. -/
@[simp] theorem DgaHom.comp_apply (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ) (a : A) :
    g.comp f a = g (f a) := rfl

/-- A9.a: the identity `f.B0 → B⁰`. -/
def DgaHom.unB0 (f : DgaHom 𝒜 ℬ) (β : f.B0) : ℬ 0 := β

/-- A9.a: `unB0 (r • β) = f(r) unB0 β`. -/
theorem DgaHom.unB0_smul (f : DgaHom 𝒜 ℬ) (r : 𝒜 0) (β : f.B0) :
    f.unB0 (r • β) = f.f0 r * f.unB0 β := rfl

/-- A9.a: `unB0` is additive. -/
theorem DgaHom.unB0_add (f : DgaHom 𝒜 ℬ) (β β' : f.B0) :
    f.unB0 (β + β') = f.unB0 β + f.unB0 β' := rfl

/-- A9.a: `f₀` of a composite. -/
theorem DgaHom.comp_f0 (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ) (r : 𝒜 0) :
    (g.comp f).f0 r = g.f0 (f.f0 r) := rfl

variable {f Q} in
/-- A9.a: `β ⊗ (r q) = f(r)β ⊗ q`. -/
theorem BCGen.tmul_smul0' {p : ℤ} (β : ℬ 0) (r : 𝒜 0) (q : Q p) :
    BCGen.tmul f Q β (r • q) = BCGen.tmul f Q (f.f0 r * β) q :=
  (TensorProduct.smul_tmul (R := 𝒜 0) r (f.ofB0 β) q).symm

variable (g : DgaHom ℬ 𝒞)

/-- The bi-additive map `(γ, q) ↦ γ ⊗ (1 ⊗ q)` on degree `p`. -/
def bcCompAux (p : ℤ) : (g.comp f).B0 →+ Q p →+ BCGen g (BCGen f Q) p :=
  AddMonoidHom.mk'
    (fun γ => AddMonoidHom.mk'
      (fun q => BCGen.tmul g (BCGen f Q) ((g.comp f).unB0 γ) (BCGen.tmul f Q 1 q))
      (fun q q' => by rw [BCGen.tmul_add, BCGen.tmul_add]))
    (fun γ γ' => AddMonoidHom.ext fun q => BCGen.add_tmul _ _ _)

/-- **A9.a** The generator comparison `u : C⁰ ⊗_{A⁰} Q^p → C⁰ ⊗_{B⁰} (B⁰ ⊗_{A⁰} Q^p)`,
`γ ⊗ q ↦ γ ⊗ (1 ⊗ q)`. -/
def bcCompU (p : ℤ) : BCGen (g.comp f) Q p →+ BCGen g (BCGen f Q) p :=
  TensorProduct.liftAddHom (R := 𝒜 0) (bcCompAux f Q g p) fun r γ q => by
    show BCGen.tmul g (BCGen f Q) ((g.comp f).unB0 (r • γ)) (BCGen.tmul f Q 1 q) =
      BCGen.tmul g (BCGen f Q) ((g.comp f).unB0 γ) (BCGen.tmul f Q 1 (r • q))
    rw [BCGen.tmul_smul0, DgaHom.unB0_smul, DgaHom.comp_f0, BCGen.tmul_smul0']

/-- A9.a: `u(γ ⊗ q) = γ ⊗ (1 ⊗ q)`. -/
theorem bcCompU_tmul (p : ℤ) (γ : 𝒞 0) (q : Q p) :
    bcCompU f Q g p (BCGen.tmul (g.comp f) Q γ q) =
      BCGen.tmul g (BCGen f Q) γ (BCGen.tmul f Q 1 q) := rfl

/-- The bi-additive map `(β, q) ↦ g(β) ⊗ q` on degree `p`. -/
def bcCompWAux (p : ℤ) : f.B0 →+ Q p →+ BCGen (g.comp f) Q p :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk' (fun q => BCGen.tmul (g.comp f) Q (g.f0 (f.unB0 β)) q)
      (fun q q' => BCGen.tmul_add _ _ _))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, DgaHom.unB0_add, map_add,
        BCGen.add_tmul])

/-- The map `B⁰ ⊗_{A⁰} Q^p → C⁰ ⊗_{A⁰} Q^p`, `β ⊗ q ↦ g(β) ⊗ q`. -/
def bcCompW (p : ℤ) : BCGen f Q p →+ BCGen (g.comp f) Q p :=
  TensorProduct.liftAddHom (R := 𝒜 0) (bcCompWAux f Q g p) fun r β q => by
    show BCGen.tmul (g.comp f) Q (g.f0 (f.unB0 (r • β))) q =
      BCGen.tmul (g.comp f) Q (g.f0 (f.unB0 β)) (r • q)
    rw [BCGen.tmul_smul0', DgaHom.unB0_smul, map_mul, DgaHom.comp_f0]

/-- A9.a: `w(β ⊗ q) = g(β) ⊗ q`. -/
theorem bcCompW_tmul (p : ℤ) (β : ℬ 0) (q : Q p) :
    bcCompW f Q g p (BCGen.tmul f Q β q) = BCGen.tmul (g.comp f) Q (g.f0 β) q := rfl

/-- A9.a: `w(β x) = g(β) w(x)`. -/
theorem bcCompW_smul (p : ℤ) (β : ℬ 0) (x : BCGen f Q p) :
    bcCompW f Q g p (β • x) = g.f0 β • bcCompW f Q g p x := by
  induction x using BCGen.induction_on with
  | ht β' q => rw [BCGen.smul_tmul, bcCompW_tmul, bcCompW_tmul, BCGen.smul_tmul, map_mul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The bi-additive map `(γ, x) ↦ γ w(x)` on degree `p`. -/
def bcCompVAux (p : ℤ) : g.B0 →+ BCGen f Q p →+ BCGen (g.comp f) Q p :=
  AddMonoidHom.mk'
    (fun γ => AddMonoidHom.mk' (fun x => g.unB0 γ • bcCompW f Q g p x)
      (fun x x' => by rw [map_add, smul_add]))
    (fun γ γ' => AddMonoidHom.ext fun x => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, DgaHom.unB0_add, add_smul])

/-- **A9.a** The inverse comparison `v : C⁰ ⊗_{B⁰} (B⁰ ⊗_{A⁰} Q^p) → C⁰ ⊗_{A⁰} Q^p`,
`γ ⊗ (β ⊗ q) ↦ γ g(β) ⊗ q`. -/
def bcCompV (p : ℤ) : BCGen g (BCGen f Q) p →+ BCGen (g.comp f) Q p :=
  TensorProduct.liftAddHom (R := ℬ 0) (bcCompVAux f Q g p) fun b γ x => by
    show g.unB0 (b • γ) • bcCompW f Q g p x = g.unB0 γ • bcCompW f Q g p (b • x)
    rw [bcCompW_smul, DgaHom.unB0_smul, mul_comm, mul_smul]

/-- A9.a: `v(γ ⊗ x) = γ w(x)`. -/
theorem bcCompV_tmul (p : ℤ) (γ : 𝒞 0) (x : BCGen f Q p) :
    bcCompV f Q g p (BCGen.tmul g (BCGen f Q) γ x) = γ • bcCompW f Q g p x := rfl

/-- A9.a: `v ∘ u = id`. -/
theorem bcCompV_U (p : ℤ) (x : BCGen (g.comp f) Q p) :
    bcCompV f Q g p (bcCompU f Q g p x) = x := by
  induction x using BCGen.induction_on with
  | ht γ q =>
    rw [bcCompU_tmul, bcCompV_tmul, bcCompW_tmul, BCGen.smul_tmul, map_one, mul_one]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- A9.a: `u ∘ v = id`. -/
theorem bcCompU_V (p : ℤ) (y : BCGen g (BCGen f Q) p) :
    bcCompU f Q g p (bcCompV f Q g p y) = y := by
  induction y using BCGen.induction_on with
  | ht γ x =>
    induction x using BCGen.induction_on with
    | ht β q =>
      rw [bcCompV_tmul, bcCompW_tmul, BCGen.smul_tmul, bcCompU_tmul,
        BCGen.tmul_eq_smul (f := f) β q,
        BCGen.tmul_smul0', mul_comm]
    | hadd x y hx hy => rw [BCGen.tmul_add, map_add, map_add, hx, hy]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- A9.a: `u` is `C⁰`-linear. -/
theorem bcCompU_smul (p : ℤ) (c : 𝒞 0) (x : BCGen (g.comp f) Q p) :
    bcCompU f Q g p (c • x) = c • bcCompU f Q g p x := by
  induction x using BCGen.induction_on with
  | ht γ q => rw [BCGen.smul_tmul, bcCompU_tmul, bcCompU_tmul, BCGen.smul_tmul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- A9.a: `v` is `C⁰`-linear. -/
theorem bcCompV_smul (p : ℤ) (c : 𝒞 0) (y : BCGen g (BCGen f Q) p) :
    bcCompV f Q g p (c • y) = c • bcCompV f Q g p y := by
  induction y using BCGen.induction_on with
  | ht γ x => rw [BCGen.smul_tmul, bcCompV_tmul, bcCompV_tmul, mul_smul]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- A9.a: `u(ι_{g∘f} e) = ι_g(ι_f e)` on the direct sums. -/
theorem famMap_bcCompU_bcι (e : ⨁ p, Q p) :
    famMap (bcCompU f Q g) (bcι (g.comp f) Q e) = bcι g (BCGen f Q) (bcι f Q e) := by
  induction e using DirectSum.induction_on with
  | zero => simp
  | of p q =>
    rw [show DirectSum.of Q p q = lof (𝒜 0) ℤ Q p q from rfl, bcι_lof, bcι_lof, bcι_lof]
    exact famMap_of _ p _
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable (M : QuasiCohesive 𝒜)

/-- **A9.a** The comparison `(g ∘ f)^*M → g^*(f^*M)` on total modules,
`c ⊗ (γ ⊗ q) ↦ c ⊗ (γ ⊗ (1 ⊗ q))`. -/
def bcCompTot : Tot 𝒞 (BCGen (g.comp f) M.Q) →ₗ[k] Tot 𝒞 (BCGen g (BCGen f M.Q)) :=
  famTot (bcCompU f M.Q g) (bcCompU_smul f M.Q g)

/-- **A9.a** The inverse comparison `g^*(f^*M) → (g ∘ f)^*M` on total modules,
`c ⊗ (γ ⊗ (β ⊗ q)) ↦ c ⊗ (γ g(β) ⊗ q)`. -/
def bcCompTotInv : Tot 𝒞 (BCGen g (BCGen f M.Q)) →ₗ[k] Tot 𝒞 (BCGen (g.comp f) M.Q) :=
  famTot (bcCompV f M.Q g) (bcCompV_smul f M.Q g)

/-- A9.a: the inverse comparison is a left inverse. -/
theorem bcCompTotInv_bcCompTot (x : Tot 𝒞 (BCGen (g.comp f) M.Q)) :
    bcCompTotInv f g M (bcCompTot f g M x) = x := by
  rw [bcCompTot, bcCompTotInv, famTot_famTot _ _ _ _ (fun p => AddMonoidHom.id _)
    (fun _ _ _ => rfl) (bcCompV_U f M.Q g), famTot_id _ _ fun _ _ => rfl]

/-- A9.a: the inverse comparison is a right inverse. -/
theorem bcCompTot_bcCompTotInv (y : Tot 𝒞 (BCGen g (BCGen f M.Q))) :
    bcCompTot f g M (bcCompTotInv f g M y) = y := by
  rw [bcCompTot, bcCompTotInv, famTot_famTot _ _ _ _ (fun p => AddMonoidHom.id _)
    (fun _ _ _ => rfl) (bcCompU_V f M.Q g), famTot_id _ _ fun _ _ => rfl]

/-- **A9.a** The comparison intertwines the maps `F`: `i ∘ F_{g∘f} = F_g ∘ F_f`. -/
theorem bcCompTot_bcF (x : Tot 𝒜 M.Q) :
    bcCompTot f g M (bcF (g.comp f) M.Q x) = bcF g (BCGen f M.Q) (bcF f M.Q x) := by
  induction x using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul, bcF_tmul, bcF_tmul, bcCompTot, famTot_tmul, famMap_bcCompU_bcι]
    rfl
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- A9.a: `𝕏` of `g^*(f^*M)`, typed on the generators `BCGen g (BCGen f Q)`. -/
def bcCompX : Tot 𝒞 (BCGen g (BCGen f M.Q)) →ₗ[k] Tot 𝒞 (BCGen g (BCGen f M.Q)) :=
  ((M.baseChange f).baseChange g).X

/-- A9.a: `𝕏` of `(g ∘ f)^*M`, typed on the generators `BCGen (g ∘ f) Q`. -/
def bcCompX' : Tot 𝒞 (BCGen (g.comp f) M.Q) →ₗ[k] Tot 𝒞 (BCGen (g.comp f) M.Q) :=
  (M.baseChange (g.comp f)).X

/-- A9.a: `𝕏_{g^*f^*M} (F_g (F_f x)) = F_g (F_f (𝕏 x))`. -/
theorem bcCompX_bcF_bcF (x : Tot 𝒜 M.Q) :
    bcCompX f g M (bcF g (BCGen f M.Q) (bcF f M.Q x)) =
      bcF g (BCGen f M.Q) (bcF f M.Q (M.X x)) := by
  have h : bcCompX f g M (bcF g (BCGen f M.Q) (bcF f M.Q x)) =
      bcF g (BCGen f M.Q) ((M.baseChange f).X (bcF f M.Q x)) :=
    bc_extend_bcF g (M.baseChange f) (bcF f M.Q x)
  rw [h, baseChange_X_apply, bc_extend_bcF]

/-- A9.a: `𝕏_{(g∘f)^*M} (F_{g∘f} x) = F_{g∘f} (𝕏 x)`. -/
theorem bcCompX'_bcF (x : Tot 𝒜 M.Q) :
    bcCompX' f g M (bcF (g.comp f) M.Q x) = bcF (g.comp f) M.Q (M.X x) :=
  bc_extend_bcF (g.comp f) M x

/-- **A9.a** The comparison `(g ∘ f)^*M → g^*(f^*M)` as a degree-`0` map. -/
def bcCompHom : Hom (M.baseChange (g.comp f)) ((M.baseChange f).baseChange g) 0 :=
  ⟨bcCompTot f g M, fun hx => by
    rw [add_zero]
    exact famTot_mem_totDeg (bcCompU f M.Q g) (bcCompU_smul f M.Q g) hx,
   fun _ x => by
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    exact famTot_smul (bcCompU f M.Q g) (bcCompU_smul f M.Q g) _ x⟩

/-- **A9.a** The inverse comparison `g^*(f^*M) → (g ∘ f)^*M` as a degree-`0` map. -/
def bcCompHomInv : Hom ((M.baseChange f).baseChange g) (M.baseChange (g.comp f)) 0 :=
  ⟨bcCompTotInv f g M, fun hx => by
    rw [add_zero]
    exact famTot_mem_totDeg (bcCompV f M.Q g) (bcCompV_smul f M.Q g) hx,
   fun _ x => by
    rw [zero_mul, Int.negOnePow_zero, one_smul]
    exact famTot_smul (bcCompV f M.Q g) (bcCompV_smul f M.Q g) _ x⟩

/-- **A9.a** The comparison is closed: `δ i = 0`. -/
theorem bcCompHom_closed :
    δ (M.baseChange (g.comp f)) ((M.baseChange f).baseChange g) 0 (bcCompHom f g M).1 = 0 := by
  have hδ := δ_mem (M.baseChange (g.comp f)) ((M.baseChange f).baseChange g)
    (bcCompHom f g M).2
  refine hom_eq_of_bcF' (g.comp f) (0 + 1) (M₁ := M) hδ (zero_mem _) fun x => ?_
  show bcCompX f g M (bcCompTot f g M (bcF (g.comp f) M.Q x)) -
    (0 : ℤ).negOnePow • bcCompTot f g M (bcCompX' f g M (bcF (g.comp f) M.Q x)) = 0
  rw [bcCompX'_bcF, bcCompTot_bcF, bcCompTot_bcF, bcCompX_bcF_bcF, Int.negOnePow_zero, one_smul,
    sub_self]

/-- **A9.a** The comparison commutes with `𝕏`. -/
theorem bcCompTot_X (x : Tot 𝒞 (BCGen (g.comp f) M.Q)) :
    bcCompX f g M (bcCompTot f g M x) = bcCompTot f g M (bcCompX' f g M x) := by
  have h : bcCompX f g M (bcCompTot f g M x) -
      (0 : ℤ).negOnePow • bcCompTot f g M (bcCompX' f g M x) = 0 :=
    LinearMap.congr_fun (bcCompHom_closed f g M) x
  rwa [Int.negOnePow_zero, one_smul, sub_eq_zero] at h

/-- **A9.a** The inverse comparison commutes with `𝕏`. -/
theorem bcCompTotInv_X (y : Tot 𝒞 (BCGen g (BCGen f M.Q))) :
    bcCompX' f g M (bcCompTotInv f g M y) = bcCompTotInv f g M (bcCompX f g M y) := by
  have h := bcCompTot_X f g M (bcCompTotInv f g M y)
  rw [bcCompTot_bcCompTotInv] at h
  rw [h, bcCompTotInv_bcCompTot]

/-- **A9.a** The inverse comparison is closed: `δ j = 0`. -/
theorem bcCompHomInv_closed :
    δ ((M.baseChange f).baseChange g) (M.baseChange (g.comp f)) 0 (bcCompHomInv f g M).1 = 0 := by
  refine LinearMap.ext fun (y : Tot 𝒞 (BCGen g (BCGen f M.Q))) => ?_
  show bcCompX' f g M (bcCompTotInv f g M y) -
    (0 : ℤ).negOnePow • bcCompTotInv f g M (bcCompX f g M y) = 0
  rw [bcCompTotInv_X, Int.negOnePow_zero, one_smul, sub_self]

/-- **A9.a** The comparison `(g ∘ f)^*M → g^*(f^*M)` as a closed degree-`0` map. -/
def bcCompZ0 : Z0 (M.baseChange (g.comp f)) ((M.baseChange f).baseChange g) :=
  ⟨(bcCompHom f g M).1, Submodule.mem_inf.2 ⟨(bcCompHom f g M).2,
    LinearMap.mem_ker.2 (bcCompHom_closed f g M)⟩⟩

/-- **A9.a** The inverse comparison `g^*(f^*M) → (g ∘ f)^*M` as a closed degree-`0` map. -/
def bcCompInvZ0 : Z0 ((M.baseChange f).baseChange g) (M.baseChange (g.comp f)) :=
  ⟨(bcCompHomInv f g M).1, Submodule.mem_inf.2 ⟨(bcCompHomInv f g M).2,
    LinearMap.mem_ker.2 (bcCompHomInv_closed f g M)⟩⟩

/-! ### Naturality on Hom complexes -/

section Natural

variable {M₁ M₂ : QuasiCohesive 𝒜} (n : ℤ)

/-- A9.a: `g^*(f^*φ)`, typed on the generators `BCGen g (BCGen f Q)`. -/
def bcCompHomL (φ : Hom M₁ M₂ n) :
    Tot 𝒞 (BCGen g (BCGen f M₁.Q)) →ₗ[k] Tot 𝒞 (BCGen g (BCGen f M₂.Q)) :=
  bcHomL g n (M₁ := M₁.baseChange f) (M₂ := M₂.baseChange f) ⟨bcHomL f n φ, bcHomL_mem f n φ⟩

/-- A9.a: `g^*(f^*φ) ∈ Hom^n`. -/
theorem bcCompHomL_mem (φ : Hom M₁ M₂ n) :
    bcCompHomL f g n φ ∈ Hom ((M₁.baseChange f).baseChange g) ((M₂.baseChange f).baseChange g) n :=
  bcHomL_mem g n (M₁ := M₁.baseChange f) (M₂ := M₂.baseChange f) ⟨bcHomL f n φ, bcHomL_mem f n φ⟩

/-- A9.a: `g^*(f^*φ) ∘ F_g ∘ F_f = F_g ∘ F_f ∘ φ`. -/
theorem bcCompHomL_bcF_bcF (φ : Hom M₁ M₂ n) (x : M₁.T) :
    bcCompHomL f g n φ (bcF g (BCGen f M₁.Q) (bcF f M₁.Q x)) =
      bcF g (BCGen f M₂.Q) (bcF f M₂.Q (φ.1 x)) := by
  have h : bcCompHomL f g n φ (bcF g (BCGen f M₁.Q) (bcF f M₁.Q x)) =
      bcF g (BCGen f M₂.Q) (bcHomL f n φ (bcF f M₁.Q x)) :=
    bcHomL_bcF g n (M₁ := M₁.baseChange f) (M₂ := M₂.baseChange f)
      ⟨bcHomL f n φ, bcHomL_mem f n φ⟩ (bcF f M₁.Q x)
  rw [h, bcHomL_bcF]

/-- **A9.a** Naturality of the comparison on Hom complexes, in every degree `n`:
`i₂ ∘ (g ∘ f)^*φ = g^*(f^*φ) ∘ i₁` for `φ ∈ Hom^n(M₁, M₂)`. -/
theorem bcCompTot_natural (φ : Hom M₁ M₂ n) :
    bcCompTot f g M₂ ∘ₗ bcHomL (g.comp f) n φ = bcCompHomL f g n φ ∘ₗ bcCompTot f g M₁ := by
  have h₁ : bcCompTot f g M₂ ∘ₗ bcHomL (g.comp f) n φ ∈
      Hom (M₁.baseChange (g.comp f)) ((M₂.baseChange f).baseChange g) n := by
    have := comp_mem _ _ _ (bcCompHom f g M₂).2 (bcHomL_mem (g.comp f) n φ)
    rwa [zero_add] at this
  have h₂ : bcCompHomL f g n φ ∘ₗ bcCompTot f g M₁ ∈
      Hom (M₁.baseChange (g.comp f)) ((M₂.baseChange f).baseChange g) n := by
    have := comp_mem (M₁.baseChange (g.comp f)) ((M₁.baseChange f).baseChange g)
      ((M₂.baseChange f).baseChange g) (bcCompHomL_mem f g n φ) (bcCompHom f g M₁).2
    rwa [add_zero] at this
  refine hom_eq_of_bcF' (g.comp f) n h₁ h₂ fun x => ?_
  show bcCompTot f g M₂ (bcHomL (g.comp f) n φ (bcF (g.comp f) M₁.Q x)) =
    bcCompHomL f g n φ (bcCompTot f g M₁ (bcF (g.comp f) M₁.Q x))
  rw [bcHomL_bcF, bcCompTot_bcF, bcCompTot_bcF, bcCompHomL_bcF_bcF]

end Natural

/-! ### The natural isomorphism `(g ∘ f)^* ≅ g^* ∘ f^*` on `Ho(P)` -/

section HoIso

open CategoryTheory

/-- **A9.a** The comparison `(g ∘ f)^*M ≅ g^*(f^*M)` as an isomorphism in `Ho(P_C)`. -/
def bcCompIso (M : HoP 𝒜) :
    (bcHoFunctor (g.comp f)).obj M ≅ (bcHoFunctor f ⋙ bcHoFunctor g).obj M where
  hom := Submodule.Quotient.mk (bcCompZ0 f g M.as.toQuasiCohesive)
  inv := Submodule.Quotient.mk (bcCompInvZ0 f g M.as.toQuasiCohesive)
  hom_inv_id := by
    change Submodule.Quotient.mk (compZ0 _ _ _ (bcCompInvZ0 f g _) (bcCompZ0 f g _)) =
      Submodule.Quotient.mk (idZ0 _)
    congr 1
    exact Subtype.ext (LinearMap.ext fun x => bcCompTotInv_bcCompTot f g _ x)
  inv_hom_id := by
    change Submodule.Quotient.mk (compZ0 _ _ _ (bcCompZ0 f g _) (bcCompInvZ0 f g _)) =
      Submodule.Quotient.mk (idZ0 _)
    congr 1
    exact Subtype.ext (LinearMap.ext fun y => bcCompTot_bcCompTotInv f g _ y)

/-- **A9.a** Base change along a composite is naturally isomorphic to the composite of base
changes: `bcHoFunctor (g ∘ f) ≅ bcHoFunctor f ⋙ bcHoFunctor g`, with components the
comparisons `c ⊗ (γ ⊗ q) ↦ c ⊗ (γ ⊗ (1 ⊗ q))` ([B, §2.7]; the underlying naturality holds on
Hom complexes in every degree, `bcCompTot_natural`). -/
def bcCompNatIso : bcHoFunctor (g.comp f) ≅ bcHoFunctor f ⋙ bcHoFunctor g :=
  NatIso.ofComponents (bcCompIso f g) fun {M N} φ => by
    induction φ using Submodule.Quotient.induction_on
    rename_i φ
    change Submodule.Quotient.mk (compZ0 _ _ _ (bcCompZ0 f g _) (bcZ0 (g.comp f) φ)) =
      Submodule.Quotient.mk (compZ0 _ _ _ (bcZ0 g (bcZ0 f φ)) (bcCompZ0 f g _))
    congr 1
    exact Subtype.ext (bcCompTot_natural f g 0 ⟨φ.1, (Submodule.mem_inf.1 φ.2).1⟩)

end HoIso

end Composite

end Cohesive
end
