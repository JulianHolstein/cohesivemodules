import Cohesivemodules.Comparison.AlphaDef
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

set_option linter.style.header false

/-!
# C3 helpers: `Tot(M|V)` is a retract of `A(V)^{Idx}`

Used for the sheaf condition of `ℋ(M₁, M₂)` (`Comparison/HomSheaf.lean`). The generic statements
(frame of a cohesive module, coordinates `iTot`, section `rTot`, naturality for `bcTotRes`) are
the same as the private ones of `Comparison/AlphaSheafAux.lean`, re-proved here without degree
bookkeeping on the target, so that `V ↦ Tot(M|V)` itself satisfies unique gluing.
-/

noncomputable section

namespace Cohesive

namespace HomRetract

open TensorProduct DirectSum

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  (f : DgaHom 𝒜 ℬ) {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

variable (𝒜) in
/-- A finite set of generators of each `Q^p` with dual coordinates, and a bounded range. -/
structure Frm (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] where
  /-- number of generators of `Q^p` -/
  m : ℤ → ℕ
  /-- the generators -/
  x : ∀ p, Fin (m p) → Q p
  /-- the dual coordinates -/
  φ : ∀ p, Fin (m p) → (Q p →ₗ[𝒜 0] 𝒜 0)
  /-- `q = ∑ φ_j(q) x_j` -/
  sum_eq : ∀ p (q : Q p), ∑ j, φ p j q • x p j = q
  /-- lower bound of the degrees -/
  lo : ℤ
  /-- upper bound of the degrees -/
  hi : ℤ
  /-- `Q^p = 0` outside `[lo, hi]` -/
  zero : ∀ p, (p < lo ∨ hi < p) → ∀ q : Q p, q = 0

/-- The index type of the generators. -/
abbrev Frm.Idx (F : Frm 𝒜 Q) : Type := Σ p : ℤ, Fin (F.m p)

/-- The bi-additive map `(β, q) ↦ β · f(φ q)`. -/
def iGenAux (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) : f.B0 →+ Q p →+ ℬ 0 :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk' (fun q => (show ℬ 0 from β) * f.f0 (φ q))
      (fun q q' => by rw [map_add, map_add, mul_add]))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      exact add_mul (show ℬ 0 from β) (show ℬ 0 from β') _)

/-- `iGenAux` is `𝒜⁰`-balanced. -/
theorem iGenAux_balanced (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) (r : 𝒜 0) (β : f.B0) (q : Q p) :
    iGenAux f p φ (r • β) q = iGenAux f p φ β (r • q) := by
  show (show ℬ 0 from (r • β : f.B0)) * f.f0 (φ q) = (show ℬ 0 from β) * f.f0 (φ (r • q))
  rw [show (show ℬ 0 from (r • β : f.B0)) = f.f0 r * (show ℬ 0 from β) from rfl, map_smul,
    smul_eq_mul, map_mul]
  ring

/-- The coordinate `β ⊗ q ↦ β · f(φ q)` on the generators `B⁰ ⊗_{A⁰} Q^p`. -/
def iGen (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) : BCGen f Q p →+ ℬ 0 :=
  TensorProduct.liftAddHom (R := 𝒜 0) (iGenAux f p φ) (iGenAux_balanced f p φ)

/-- `iGen` on pure tensors (rfl). -/
theorem iGen_tmul (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) (β : ℬ 0) (q : Q p) :
    iGen f p φ (BCGen.tmul f Q β q) = β * f.f0 (φ q) := rfl

/-- `iGen` is `B⁰`-linear. -/
theorem iGen_smul (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) (γ : ℬ 0) (x : BCGen f Q p) :
    iGen f p φ (γ • x) = γ * iGen f p φ x := by
  induction x using BCGen.induction_on with
  | ht β q => rw [BCGen.smul_tmul, iGen_tmul, iGen_tmul, mul_assoc]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]

variable (F : Frm 𝒜 Q)

/-- The bi-additive map `(b, e) ↦ (b · coordinate_{p,j}(e_p))_{p,j}`. -/
def iTotAux : B →+ (⨁ p, BCGen f Q p) →+ (F.Idx → B) :=
  AddMonoidHom.mk'
    (fun b => AddMonoidHom.mk'
      (fun e pj => b * ((iGen f pj.1 (F.φ pj.1 pj.2) (e pj.1) : ℬ 0) : B))
      (fun e e' => by
        funext pj
        simp only [DirectSum.add_apply, map_add, Pi.add_apply, AddMemClass.coe_add, mul_add]))
    (fun b b' => AddMonoidHom.ext fun e => by
      funext pj
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, Pi.add_apply, add_mul])

/-- `iTotAux` is `B⁰`-balanced. -/
theorem iTotAux_balanced (γ : ℬ 0) (b : B) (e : ⨁ p, BCGen f Q p) :
    iTotAux f F (γ • b) e = iTotAux f F b (γ • e) := by
  funext pj
  show (γ • b) * ((iGen f pj.1 (F.φ pj.1 pj.2) (e pj.1) : ℬ 0) : B) =
    b * ((iGen f pj.1 (F.φ pj.1 pj.2) ((γ • e) pj.1) : ℬ 0) : B)
  rw [DirectSum.smul_apply, iGen_smul, GCDga.smul0_def, GCDga.central ℬ γ.2 b, mul_assoc]
  rfl

/-- The coordinates `Tot(f^*M) → B^{Idx}`. -/
def iTot : Tot ℬ (BCGen f Q) →+ (F.Idx → B) :=
  TensorProduct.liftAddHom (R := ℬ 0) (iTotAux f F) (iTotAux_balanced f F)

/-- `iTot` on pure tensors (rfl). -/
theorem iTot_tmul (b : B) (e : ⨁ p, BCGen f Q p) (pj : F.Idx) :
    iTot f F (Tot.tmul ℬ _ b e) pj =
      b * ((iGen f pj.1 (F.φ pj.1 pj.2) (e pj.1) : ℬ 0) : B) := rfl

/-- The map `B^{Idx} → Tot(f^*M)`, `(a_{p,j}) ↦ ∑ a_{p,j} ⊗ ι(x_{p,j})`. -/
def rTot : (F.Idx → B) →+ Tot ℬ (BCGen f Q) :=
  AddMonoidHom.mk'
    (fun a => ∑ p ∈ Finset.Icc F.lo F.hi, ∑ j : Fin (F.m p),
      Tot.tmul ℬ _ (a ⟨p, j⟩) (lof (ℬ 0) ℤ (BCGen f Q) p (BCGen.tmul f Q 1 (F.x p j))))
    (fun a a' => by
      simp only [Pi.add_apply, Tot.add_tmul, Finset.sum_add_distrib])

/-- `β ⊗ (r q) = (β f(r)) • (1 ⊗ q)`. -/
theorem tmul_smul_eq (p : ℤ) (β : ℬ 0) (r : 𝒜 0) (q : Q p) :
    BCGen.tmul f Q β (r • q) = (β * f.f0 r) • BCGen.tmul f Q 1 q := by
  rw [BCGen.tmul_eq_smul β (r • q), BCGen.tmul_smul0, smul_smul]

/-- `∑ (β f(φ_j q)) • (1 ⊗ x_j) = β ⊗ q`. -/
theorem gen_decomp (p : ℤ) (β : ℬ 0) (q : Q p) :
    ∑ j, (β * f.f0 (F.φ p j q)) • BCGen.tmul f Q 1 (F.x p j) = BCGen.tmul f Q β q := by
  conv_rhs => rw [← F.sum_eq p q]
  rw [BCGen.tmul_def, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← tmul_smul_eq f p β]
  rfl

/-- `rTot ∘ iTot = id` on a pure tensor `b ⊗ (β ⊗ q)` in a degree `p` inside the range. -/
theorem rTot_iTot_in (b : B) (p : ℤ) (hp : p ∈ Finset.Icc F.lo F.hi) (β : ℬ 0)
    (q : Q p) :
    rTot f F (iTot f F (Tot.tmul ℬ _ b (DirectSum.of (BCGen f Q) p (BCGen.tmul f Q β q)))) =
      Tot.tmul ℬ _ b (DirectSum.of (BCGen f Q) p (BCGen.tmul f Q β q)) := by
  show ∑ p' ∈ Finset.Icc F.lo F.hi, ∑ j : Fin (F.m p'), Tot.tmul ℬ _ (iTot f F (Tot.tmul ℬ _ b
    (DirectSum.of (BCGen f Q) p (BCGen.tmul f Q β q))) ⟨p', j⟩)
      (lof (ℬ 0) ℤ (BCGen f Q) p' (BCGen.tmul f Q 1 (F.x p' j))) = _
  rw [Finset.sum_eq_single p]
  · conv_rhs => rw [← gen_decomp f F p β q]
    rw [map_sum, show ∀ g : Fin (F.m p) → ⨁ p', BCGen f Q p',
      Tot.tmul ℬ _ b (∑ j, g j) = ∑ j, Tot.tmul ℬ _ b (g j) from
      fun g => TensorProduct.tmul_sum _ _ _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iTot_tmul, DirectSum.of_eq_same, iGen_tmul,
      show DirectSum.of (BCGen f Q) p ((β * f.f0 (F.φ p j q)) • BCGen.tmul f Q 1 (F.x p j)) =
        (β * f.f0 (F.φ p j q)) • lof (ℬ 0) ℤ (BCGen f Q) p (BCGen.tmul f Q 1 (F.x p j)) from
        map_smul (DirectSum.lof (ℬ 0) ℤ (BCGen f Q) p) _ _, Tot.tmul_smul0]
  · intro p' _ hne
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [iTot_tmul, DirectSum.of_eq_of_ne _ _ _ hne, map_zero]
    simp only [ZeroMemClass.coe_zero, mul_zero, Tot.zero_tmul]
  · intro h; exact absurd hp h

/-- `rTot ∘ iTot = id` on a pure tensor with a single generator component. -/
theorem rTot_iTot_of (b : B) (p : ℤ) (z : BCGen f Q p) :
    rTot f F (iTot f F (Tot.tmul ℬ _ b (DirectSum.of (BCGen f Q) p z))) =
      Tot.tmul ℬ _ b (DirectSum.of (BCGen f Q) p z) := by
  induction z using BCGen.induction_on with
  | ht β q =>
    by_cases hp : p ∈ Finset.Icc F.lo F.hi
    · exact rTot_iTot_in f F b p hp β q
    · have hq : BCGen.tmul f Q β q = 0 := by
        have h0 : q = 0 := F.zero p (by simp only [Finset.mem_Icc] at hp; omega) q
        rw [h0, BCGen.tmul_def, TensorProduct.tmul_zero]
        rfl
      rw [hq, map_zero, Tot.tmul_zero, map_zero, map_zero]
  | hadd x y hx hy =>
    rw [map_add, Tot.tmul_add, map_add, map_add, hx, hy]

/-- `rTot ∘ iTot = id`. -/
theorem rTot_iTot (y : Tot ℬ (BCGen f Q)) : rTot f F (iTot f F y) = y := by
  induction y using Tot.induction_on with
  | ht b e =>
    induction e using DirectSum.induction_on with
    | zero => simp only [Tot.tmul_zero, map_zero]
    | of p z => exact rTot_iTot_of f F b p z
    | add x y hx hy => rw [Tot.tmul_add, map_add, map_add, hx, hy]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- `iTot` is `B`-semilinear. -/
theorem iTot_smul (c : B) (y : Tot ℬ (BCGen f Q)) (pj : F.Idx) :
    iTot f F (c • y) pj = c * iTot f F y pj := by
  induction y using Tot.induction_on with
  | ht b e => rw [Tot.smul_tmul, iTot_tmul, iTot_tmul, mul_assoc]
  | hadd x y hx hy => rw [smul_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, mul_add]

/-- `iTot` maps elements of total degree `n` to coordinates `a_{p,j} ∈ B^{n-p}`. -/
theorem iTot_mem {n : ℤ} {y : Tot ℬ (BCGen f Q)} (hy : y ∈ totDeg ℬ (BCGen f Q) n)
    (pj : F.Idx) : iTot f F y pj ∈ ℬ (n - pj.1) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, hqp, ha, rfl⟩ := hx
    change iTot f F (Tot.tmul ℬ _ a (lof (ℬ 0) ℤ (BCGen f Q) p e)) pj ∈ _
    rw [iTot_tmul]
    obtain ⟨p', j⟩ := pj
    by_cases hpp : p' = p
    · subst hpp
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
      have := SetLike.GradedMul.mul_mem ha (iGen f p' (F.φ p' j) e).2
      rwa [show q + 0 = n - p' by omega] at this
    · rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hpp, map_zero]
      simp only [ZeroMemClass.coe_zero, mul_zero]
      exact zero_mem _
  | zero => simp only [map_zero, Pi.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add, Pi.add_apply]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [← algebraMap_smul B r x, iTot_smul]
    have := Submodule.smul_mem (ℬ (n - pj.1)) r hx
    rwa [Algebra.smul_def] at this

/-- `rTot` maps coordinates `a_{p,j} ∈ B^{n-p}` to elements of total degree `n`. -/
theorem rTot_mem {n : ℤ} {a : F.Idx → B} (ha : ∀ pj, a pj ∈ ℬ (n - pj.1)) :
    rTot f F a ∈ totDeg ℬ (BCGen f Q) n := by
  show (∑ p ∈ Finset.Icc F.lo F.hi, ∑ j : Fin (F.m p), Tot.tmul ℬ _ (a ⟨p, j⟩)
    (lof (ℬ 0) ℤ (BCGen f Q) p (BCGen.tmul f Q 1 (F.x p j)))) ∈ totDeg ℬ (BCGen f Q) n
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun j _ => ?_
  have := tmul_mem_totDeg (ha ⟨p, j⟩) (BCGen.tmul f Q 1 (F.x p j))
  rwa [show n - (⟨p, j⟩ : F.Idx).1 + p = n by simp only; omega] at this

section Natural

variable {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]
  (g : DgaHom ℬ 𝒞) (f' : DgaHom 𝒜 𝒞) (hgf : ∀ a, g (f a) = f' a)

/-- `iGen` is natural for `bcGenRes`. -/
theorem iGen_bcGenRes (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) (z : BCGen f Q p) :
    iGen f' p φ (bcGenRes g f f' hgf Q p z) = g.f0 (iGen f p φ z) := by
  induction z using BCGen.induction_on with
  | ht β q =>
    rw [bcGenRes_tmul, iGen_tmul, iGen_tmul, map_mul]
    exact congrArg (g.f0 β * ·) (Subtype.ext (hgf _)).symm
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- `iTot` is natural for `bcTotRes`. -/
theorem iTot_bcTotRes (y : Tot ℬ (BCGen f Q)) (pj : F.Idx) :
    iTot f' F (bcTotRes g f f' hgf Q y) pj = g (iTot f F y pj) := by
  induction y using Tot.induction_on with
  | ht b e =>
    rw [bcTotRes_tmul, iTot_tmul, iTot_tmul, DirectSum.map_apply, iGen_bcGenRes f g f' hgf,
      g.map_mul']
    rfl
  | hadd x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, g.map_add']

/-- `rTot` is natural for `bcTotRes`. -/
theorem bcTotRes_rTot (a : F.Idx → B) :
    bcTotRes g f f' hgf Q (rTot f F a) = rTot f' F (fun pj => g (a pj)) := by
  show bcTotRes g f f' hgf Q (∑ p ∈ Finset.Icc F.lo F.hi, ∑ j : Fin (F.m p), _) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bcTotRes_tmul, DirectSum.lof_eq_of, DirectSum.map_of, bcGenRes_tmul]
  have h1 : g.f0 (1 : ℬ 0) = 1 := map_one g.f0
  rw [h1]
  rfl

end Natural

variable (𝒜) in
/-- A cohesive module admits a `Frm`: generators and dual coordinates of each `Q^p` (finitely
generated projective) and a bounded range of degrees. -/
theorem exists_frm (M : CohesiveModule 𝒜) : Nonempty (Frm 𝒜 M.Q) := by
  have h : ∀ p, ∃ (m : ℕ) (x : Fin m → M.Q p) (φ : Fin m → (M.Q p →ₗ[𝒜 0] 𝒜 0)),
      ∀ q, ∑ j, φ j q • x j = q := fun p => by
    have := M.finite p
    have := M.projective p
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝒜 0) (M.Q p)
    obtain ⟨h, hh⟩ := Module.projective_lifting_property f LinearMap.id hf
    refine ⟨n, fun j => f (Pi.single j 1), fun j => (LinearMap.proj j) ∘ₗ h, fun q => ?_⟩
    have := LinearMap.congr_fun hh q
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    conv_rhs => rw [← this, ← Finset.univ_sum_single (h q)]
    simp only [map_sum, LinearMap.comp_apply, LinearMap.proj_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    congr 1
    ext i
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  choose m x φ hφ using h
  obtain ⟨lo, hi, hb⟩ := M.bounded
  exact ⟨⟨m, x, φ, hφ, lo, hi, fun p hp q => by
    have := hb p hp
    exact Subsingleton.elim q 0⟩⟩

open TopologicalSpace in
/-- Unique gluing passes to a retract. -/
theorem glue_of_retract {X : Type} [TopologicalSpace X] {Fv Gv : Opens X → Type}
    (resF : ∀ {V W : Opens X}, W ≤ V → Fv V → Fv W)
    (resG : ∀ {V W : Opens X}, W ≤ V → Gv V → Gv W)
    (i : ∀ V, Fv V → Gv V) (r : ∀ V, Gv V → Fv V)
    (hri : ∀ V x, r V (i V x) = x)
    (hi : ∀ {V W} (h : W ≤ V) x, resG h (i V x) = i W (resF h x))
    (hr : ∀ {V W} (h : W ≤ V) y, resF h (r V y) = r W (resG h y))
    (hG : ∀ {ι : Type} (U : ι → Opens X) (s : ∀ a, Gv (U a)),
      (∀ a b, resG (inf_le_left : U a ⊓ U b ≤ U a) (s a) =
        resG (inf_le_right : U a ⊓ U b ≤ U b) (s b)) →
      ∃! t : Gv (⨆ a, U a), ∀ a, resG (le_iSup U a) t = s a)
    {ι : Type} (U : ι → Opens X) (s : ∀ a, Fv (U a))
    (hs : ∀ a b, resF (inf_le_left : U a ⊓ U b ≤ U a) (s a) =
      resF (inf_le_right : U a ⊓ U b ≤ U b) (s b)) :
    ∃! t : Fv (⨆ a, U a), ∀ a, resF (le_iSup U a) t = s a := by
  obtain ⟨t, ht, hu⟩ := hG U (fun a => i _ (s a)) fun a b => by rw [hi, hi, hs a b]
  refine ⟨r _ t, fun a => ?_, fun t' ht' => ?_⟩
  · rw [hr, ht, hri]
  · have : i _ t' = t := hu (i _ t') fun a => by rw [hi, ht']
    rw [← this, hri]

end HomRetract

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) {U₀ : Opens X}

/-- Gluing of families of sections of the algebras `A(U)`, indexed by a type `J`. -/
theorem glue_fun (J : Type) {ι : Type} (U : ι → Opens X) (s : ∀ a, J → P.D.A (U a))
    (h : ∀ a b j, P.D.res (inf_le_left : U a ⊓ U b ≤ U a) (s a j) =
      P.D.res (inf_le_right : U a ⊓ U b ≤ U b) (s b j)) :
    ∃! t : J → P.D.A (⨆ a, U a), ∀ a j, P.D.res (le_iSup U a) (t j) = s a j := by
  choose t ht hu using fun j => P.glue U (fun a => s a j) (fun a b => h a b j)
  exact ⟨t, fun a j => ht j a, fun t' ht' => funext fun j => hu j (t' j) fun a => ht' a j⟩

/-- Unique gluing in `Tot(M|V)`, `V ↦ Tot(M|V)` (`M` cohesive over `𝒜(X)`). -/
theorem car_glue (M : CohesiveModule P.𝒜X) {ι : Type} (U : ι → Opens X)
    (s : ∀ a, P.TotSec M (le_top : U a ≤ ⊤))
    (hs : ∀ a b, P.totRes M le_top (inf_le_left : U a ⊓ U b ≤ U a) (s a) =
      P.totRes M le_top (inf_le_right : U a ⊓ U b ≤ U b) (s b)) :
    ∃! t : P.TotSec M (le_top : (⨆ a, U a) ≤ ⊤),
      ∀ a, P.totRes M le_top (le_iSup U a) t = s a := by
  obtain ⟨F⟩ := HomRetract.exists_frm P.𝒜X M
  refine HomRetract.glue_of_retract (Fv := fun V => P.TotSec M (le_top : V ≤ ⊤))
    (Gv := fun V => F.Idx → P.D.A V)
    (fun {V W} h x => P.totRes M le_top h x)
    (fun {V W} h y pj => P.D.res h (y pj))
    (fun V x => HomRetract.iTot (P.D.res (le_top : V ≤ ⊤)) F x)
    (fun V a => HomRetract.rTot (P.D.res (le_top : V ≤ ⊤)) F a)
    ?_ ?_ ?_ ?_ U s hs
  · intro V x
    exact HomRetract.rTot_iTot _ F x
  · intro V W h x
    funext pj
    exact (HomRetract.iTot_bcTotRes _ F (P.D.res h) _ (P.D.res_comp le_top h) x pj).symm
  · intro V W h y
    exact HomRetract.bcTotRes_rTot _ F (P.D.res h) _ (P.D.res_comp le_top h) y
  · intro ι' U' s' hs'
    obtain ⟨t, ht, hu⟩ := P.glue_fun F.Idx U' s' (fun a b j => congrFun (hs' a b) j)
    exact ⟨t, fun a => funext (ht a), fun t' ht' => hu t' fun a j => congrFun (ht' a) j⟩

/-- Being of total degree `k` in `Tot(M|V)` is a local property. -/
theorem car_mem_totDeg_of_local (M : CohesiveModule P.𝒜X) {V : Opens X}
    (y : P.TotSec M (le_top : V ≤ ⊤)) (k : ℤ)
    (h : ∀ x ∈ V, ∃ (W : Opens X) (hW : W ≤ V), x ∈ W ∧
      P.totRes M le_top hW y ∈ totDeg (P.D.𝒜 W) (M.baseChange (P.D.res (hW.trans le_top))).Q k) :
    y ∈ totDeg (P.D.𝒜 V) (M.baseChange (P.D.res (le_top : V ≤ ⊤))).Q k := by
  obtain ⟨F⟩ := HomRetract.exists_frm P.𝒜X M
  rw [← HomRetract.rTot_iTot (P.D.res (le_top : V ≤ ⊤)) F y]
  refine HomRetract.rTot_mem _ F fun pj => ?_
  refine P.degree_local (k - pj.1) _ fun x hx => ?_
  obtain ⟨W, hW, hxW, hmem⟩ := h x hx
  refine ⟨W, hW, hxW, ?_⟩
  have := HomRetract.iTot_mem _ F hmem pj
  exact (congrArg (· ∈ P.D.𝒜 W (k - pj.1))
    (HomRetract.iTot_bcTotRes _ F (P.D.res hW) _ (P.D.res_comp le_top hW) y pj)).mp this

end PreResolvingData

end Cohesive
