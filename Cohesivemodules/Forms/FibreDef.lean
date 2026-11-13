-- FROZEN (gate 3, 26 Oct 2026; F2 definitions, in the main statement). Do not edit without approval.
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

set_option linter.style.header false

/-!
# F2: the conjugate space and the fibre `Λ^{0,q}(E; F)` (definitions)

Blueprint item F2 (conventions §6; prototype `Scratch/P2_Fibres.lean`, decision: keep `Conj E`).
This file holds the definitions of F2 that the main statement depends on, with their basic API
and the declarations their constructions need; it will be frozen at gate 3. The remaining F2
results are in `Cohesivemodules/Forms/Fibre.lean`.

Definitions: `Conj`, `Conj.toConj`, `Conj.ofConj`, the instances `NormedAddCommGroup (Conj E)`,
`Module ℂ (Conj E)`, `NormedSpace ℂ (Conj E)`, `FiniteDimensional ℂ (Conj E)`, `Conj.basis`,
`Conj.map`, `DolbeaultFibre`, `form0Equiv`, `algEquiv`, `extToFibre`, `extEquivFibre`.

## Deviations
* ⚠ (blueprint F2) `Λ^{0,q}` is `Conj E [⋀^Fin q]→L[ℂ] F`, not a subtype of `ℝ`-alternating maps
  antilinear in each slot (the same maps).
-/

noncomputable section

namespace Cohesive

open ContinuousAlternatingMap ComplexConjugate

/-! ## The conjugate space -/

/-- **F2.** The conjugate space `Ē`: `E` with `c • v := c̄ • v` and the same norm (conventions §6).
A `def`, not an `abbrev`, so that `E`'s `ℂ`-action never leaks onto it. -/
def Conj (E : Type) : Type := E

namespace Conj

variable {E : Type}

/-- F2: the identity `E → Ē`. -/
def toConj : E ≃ Conj E := Equiv.refl _

/-- F2: the identity `Ē → E`. -/
def ofConj : Conj E ≃ E := Equiv.refl _

@[simp] theorem ofConj_toConj (v : E) : ofConj (toConj v) = v := rfl
@[simp] theorem toConj_ofConj (v : Conj E) : toConj (ofConj v) = v := rfl

variable [NormedAddCommGroup E]

/-- F2: `Ē` has the norm of `E`. -/
instance : NormedAddCommGroup (Conj E) := inferInstanceAs (NormedAddCommGroup E)

@[simp] theorem ofConj_add (v w : Conj E) : ofConj (v + w) = ofConj v + ofConj w := rfl
@[simp] theorem ofConj_neg (v : Conj E) : ofConj (-v) = -ofConj v := rfl
@[simp] theorem ofConj_zero : ofConj (0 : Conj E) = 0 := rfl
@[simp] theorem toConj_add (v w : E) : toConj (v + w) = toConj v + toConj w := rfl
@[simp] theorem toConj_zero : toConj (0 : E) = 0 := rfl
@[simp] theorem norm_ofConj (v : Conj E) : ‖ofConj v‖ = ‖v‖ := rfl

variable [NormedSpace ℂ E]

/-- F2: the conjugate `ℂ`-action on `Ē`. -/
instance : Module ℂ (Conj E) := Module.compHom E (starRingEnd ℂ)

/-- F2: `c • v = c̄ • v` on `Ē`. -/
theorem smul_def (c : ℂ) (v : Conj E) : c • v = toConj (conj c • ofConj v) := rfl

@[simp] theorem ofConj_smul (c : ℂ) (v : Conj E) : ofConj (c • v) = conj c • ofConj v := rfl

@[simp] theorem toConj_smul (c : ℂ) (v : E) : toConj (c • v) = conj c • toConj v := by
  rw [smul_def, ofConj_toConj, Complex.conj_conj]

/-- F2: `Ē` is a normed `ℂ`-space. -/
instance : NormedSpace ℂ (Conj E) where
  norm_smul_le c v := by
    rw [← norm_ofConj, ofConj_smul, norm_smul, RCLike.norm_conj, norm_ofConj]

/-- Coordinates of `Ē` w.r.t. `b`: the conjugated coordinates of `E`. -/
private def reprEquiv {ι : Type} (b : Module.Basis ι ℂ E) : Conj E ≃ₗ[ℂ] (ι →₀ ℂ) where
  toFun v := (b.repr (ofConj v)).mapRange conj (map_zero _)
  map_add' v w := by
    ext i; simp only [ofConj_add, map_add, Finsupp.mapRange_apply, Finsupp.coe_add,
      Pi.add_apply]
  map_smul' c v := by
    ext i; simp only [ofConj_smul, map_smul, Finsupp.mapRange_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Complex.conj_conj]
  invFun f := toConj (b.repr.symm (f.mapRange conj (map_zero _)))
  left_inv v := by
    show toConj (b.repr.symm (((b.repr (ofConj v)).mapRange conj (map_zero _)).mapRange conj
      (map_zero _))) = v
    have : ((b.repr (ofConj v)).mapRange conj (map_zero _)).mapRange conj (map_zero _)
        = b.repr (ofConj v) := by
      ext i; simp only [Finsupp.mapRange_apply, Complex.conj_conj]
    rw [this, LinearEquiv.symm_apply_apply]; rfl
  right_inv f := by
    simp only [ofConj_toConj, LinearEquiv.apply_symm_apply]
    ext i; simp only [Finsupp.mapRange_apply, Complex.conj_conj]

/-- F2: `Ē` is finite-dimensional when `E` is. -/
instance [FiniteDimensional ℂ E] : FiniteDimensional ℂ (Conj E) :=
  Module.Finite.equiv (reprEquiv (Module.finBasis ℂ E)).symm

/-- F2.c: a basis `b` of `E` gives the basis `i ↦ b i` of `Ē` (coordinates conjugated). -/
def basis {ι : Type} (b : Module.Basis ι ℂ E) : Module.Basis ι ℂ (Conj E) :=
  Module.Basis.ofRepr (reprEquiv b)

/-- F2.c: the basis of `Ē` from `b` consists of the same vectors. -/
theorem basis_apply {ι : Type} (b : Module.Basis ι ℂ E) (i : ι) :
    Conj.basis b i = toConj (b i) := by
  apply (reprEquiv b).injective
  rw [show (reprEquiv b) (Conj.basis b i) = Finsupp.single i 1 from
    Module.Basis.repr_self (Conj.basis b) i]
  simp only [reprEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, ofConj_toConj,
    Module.Basis.repr_self]
  ext j; simp only [Finsupp.mapRange_apply]
  by_cases h : i = j <;> simp [h]

/-- F2: `finrank ℂ Ē = finrank ℂ E`. -/
theorem finrank_eq [FiniteDimensional ℂ E] :
    Module.finrank ℂ (Conj E) = Module.finrank ℂ E := by
  rw [Module.finrank_eq_card_basis (Conj.basis (Module.finBasis ℂ E))]
  exact (Module.finrank_eq_card_basis (Module.finBasis ℂ E)).symm

/-- **F2.** (conventions §6, used in F7) A `ℂ`-linear map `T : E → E'` is also `ℂ`-linear
`Ē → Ē'` (e.g. `T = DG(x)` for holomorphic `G`). -/
def map {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (T : E →L[ℂ] E') :
    Conj E →L[ℂ] Conj E' where
  toFun v := toConj (T (ofConj v))
  map_add' v w := by rw [ofConj_add, map_add]; rfl
  map_smul' c v := by
    rw [RingHom.id_apply, ofConj_smul, map_smul, toConj_smul, Complex.conj_conj]
  cont := T.continuous.comp continuous_id

/-- F2: formula for `Conj.map`. -/
@[simp] theorem map_apply {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (T : E →L[ℂ] E')
    (v : Conj E) : Conj.map T v = toConj (T (ofConj v)) := rfl

end Conj

open Conj

/-! ## The fibre -/

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **F2.** The fibre `Λ^{0,q}(E; F) = Conj E [⋀^Fin q]→L[ℂ] F` of `(0,q)`-forms with values in
`F` at a point: continuous `ℂ`-alternating maps on `Ē`, i.e. `ℝ`-alternating maps on `E` that are
antilinear in each slot. [B, §4.1], [A, §7.1]; conventions §6.

⚠ Replaces the blueprint's earlier subtype of `ℝ`-alternating maps (same maps). -/
abbrev DolbeaultFibre (q : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℂ F] : Type :=
  Conj E [⋀^Fin q]→L[ℂ] F

variable {E} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (E F) in
/-- **F2.a.** `Λ^{0,0}(E; F) ≅ F`: a `0`-form at a point is a value (`constOfIsEmptyLIE`). -/
def form0Equiv : F ≃ₗᵢ[ℂ] DolbeaultFibre E 0 F := constOfIsEmptyLIE ℂ (Conj E) F (Fin 0)

/-- F2.a: the `0`-form of a value `f` takes the value `f` on the empty family. -/
@[simp] theorem form0Equiv_apply (f : F) (v : Fin 0 → Conj E) : form0Equiv E F f v = f := rfl

/-- F2.c: `Λ^{0,q}(E; F) = 0` for `q > dim_ℂ E`: an alternating map on more vectors than the
dimension vanishes. -/
theorem dolbeaultFibre_subsingleton [FiniteDimensional ℂ E] {q : ℕ} (hq : Module.finrank ℂ E < q) :
    Subsingleton (DolbeaultFibre E q F) := by
  refine ⟨fun f g => ?_⟩
  have key : ∀ (h : DolbeaultFibre E q F) (v : Fin q → Conj E), h v = 0 := by
    intro h v
    have hv : ¬ LinearIndependent ℂ v := fun hl => by
      have := hl.fintype_card_le_finrank
      rw [Fintype.card_fin, Conj.finrank_eq] at this
      omega
    exact h.toAlternatingMap.map_linearDependent v hv
  ext v
  rw [key f v, key g v]

/-! ## F2.b: the exterior-algebra bridge -/

section Bridge

variable [FiniteDimensional ℂ E]

/-- F2.b: in finite dimension every `ℂ`-alternating map on `Ē` is continuous. (Not in Mathlib:
there is no finite-dimensional continuity for multilinear maps, see P2.) -/
theorem alternating_continuous {q : ℕ} (f : Conj E [⋀^Fin q]→ₗ[ℂ] F) : Continuous f := by
  classical
  let b := Module.finBasis ℂ (Conj E)
  let m : MultilinearMap ℂ (fun _ : Fin q => Conj E) F := f.toMultilinearMap
  have hv : ∀ v : Fin q → Conj E, f v =
      ∑ r : Fin q → Fin (Module.finrank ℂ (Conj E)),
        (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i)) := by
    intro v
    have h1 : v = fun i => ∑ j, b.repr (v i) j • b j :=
      funext fun i => (b.sum_repr (v i)).symm
    have h2 : f v = m v := rfl
    rw [h2]
    conv_lhs => rw [h1]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    rfl
  have hc : ∀ j, Continuous fun x : Conj E => b.repr x j := fun j =>
    (b.coord j).continuous_of_finiteDimensional
  have : (f : (Fin q → Conj E) → F) = fun v =>
      ∑ r : Fin q → Fin (Module.finrank ℂ (Conj E)),
        (∏ i, b.repr (v i) (r i)) • f (fun i => b (r i)) := funext hv
  rw [this]
  refine continuous_finsetSum _ fun r _ => ?_
  refine Continuous.smul ?_ continuous_const
  exact continuous_finsetProd _ fun i _ => (hc (r i)).comp (continuous_apply i)

variable (E F) in
/-- F2.b: in finite dimension, algebraic and continuous alternating maps on `Ē` agree. -/
def algEquiv (q : ℕ) : (Conj E [⋀^Fin q]→ₗ[ℂ] F) ≃ₗ[ℂ] DolbeaultFibre E q F where
  toFun f := { f with cont := alternating_continuous f }
  invFun f := f.toAlternatingMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable (E) in
/-- **F2.b.** The exterior-algebra bridge `Φ_q : ⋀^q_ℂ (Ē)^* → Λ^{0,q}(E; ℂ)`,
`φ₁ ∧ ⋯ ∧ φ_q ↦ (v ↦ det (φ_i (v_j)))`: `exteriorPower.pairingDual`, read as an alternating
map (`exteriorPower.alternatingMapLinearEquiv`), made continuous by finite dimension
(conventions §6). -/
def extToFibre (q : ℕ) : ⋀[ℂ]^q (Module.Dual ℂ (Conj E)) →ₗ[ℂ] DolbeaultFibre E q ℂ :=
  (algEquiv E ℂ q).toLinearMap ∘ₗ
    exteriorPower.alternatingMapLinearEquiv.symm.toLinearMap ∘ₗ
      exteriorPower.pairingDual ℂ (Conj E) q

/-- **F2.b.** `Φ_q` is bijective (basis lemmas `ιMultiDual_apply_diag`,
`ιMultiDual_apply_nondiag`, `Module.Basis.exteriorPower`). -/
theorem extToFibre_bijective (q : ℕ) : Function.Bijective (extToFibre E q) := by
  have h := exteriorPower.bijective_pairingDual ℂ (Conj E) q
  have h1 : Function.Bijective
      (exteriorPower.alternatingMapLinearEquiv.symm.toLinearMap ∘ₗ
        exteriorPower.pairingDual ℂ (Conj E) q) :=
    (exteriorPower.alternatingMapLinearEquiv.symm.bijective).comp h
  exact ((algEquiv E ℂ q).bijective).comp h1

variable (E) in
/-- **F2.b.** `Φ_q` as a linear equivalence `⋀^q_ℂ (Ē)^* ≃ Λ^{0,q}(E; ℂ)`. -/
def extEquivFibre (q : ℕ) : ⋀[ℂ]^q (Module.Dual ℂ (Conj E)) ≃ₗ[ℂ] DolbeaultFibre E q ℂ :=
  LinearEquiv.ofBijective (extToFibre E q) (extToFibre_bijective q)

/-- F2.b: `extEquivFibre` is `extToFibre`. -/
@[simp] theorem extEquivFibre_apply (q : ℕ) (x : ⋀[ℂ]^q (Module.Dual ℂ (Conj E))) :
    extEquivFibre E q x = extToFibre E q x := rfl

end Bridge

end Cohesive
