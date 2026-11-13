import Cohesivemodules.Comparison.TwistDatumDef

set_option linter.style.header false

/-!
# Z3.c: special twist data

Blueprint item Z3.c (`blueprint/blueprint-tw.md` §2.2, checks K8, K14). Non-vacuity witnesses:
* `TwistCocycle.trivial R`: the one-member cover `{⊤}` with `ȟ = 1`;
* `exactTwistDatum S β h`: for `h = dβ` with `β ∈ 𝒜¹(X)`, the datum on `{⊤}` with `h⁰ = β`,
  `u = 1`, `ȟ = 1`;
* `trivialTwistDatum S`: the case `β = 0`, a twist datum for `h = 0`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- **Z3.c.** The trivial cocycle: the cover `{⊤}` (`ι = Unit`), `ȟ = 1`. -/
def TwistCocycle.trivial (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}) :
    TwistCocycle R where
  ι := Unit
  U _ := ⊤
  iSup_eq := iSup_const
  ch _ _ _ := 1
  normalized _ _ _ _ := rfl
  cocycle _ _ _ _ _ _ _ _ _ := by simp only [map_one, inv_one, mul_one]

/-- Z3.c: `d 1 = 0` in a (possibly curved) gc dga (Leibniz). -/
theorem GCDga.d_one' {k A : Type} [CommRing k] [Ring A] [Algebra k A] {𝒜 : ℤ → Submodule k A}
    [GradedAlgebra 𝒜] [GCDga 𝒜] : GCDga.d (𝒜 := 𝒜) 1 = 0 := by
  have h := GCDga.leibniz (𝒜 := 𝒜) (SetLike.GradedOne.one_mem (A := 𝒜)) (1 : A)
  simp only [mul_one, Int.negOnePow_zero, one_smul, one_mul] at h
  exact add_eq_left.mp h.symm

/-- **Z3.c (K14).** For `h = dβ` with `β ∈ 𝒜¹(X)`: the twist datum on the cover `{⊤}` with
`h⁰ = β`, `u = 1`, `ȟ = 1`. -/
def exactTwistDatum (S : DgaSheafData X) (β : S.D.A ⊤) (hβ : β ∈ S.D.𝒜 ⊤ 1) (h : S.D.A ⊤)
    (hh : GCDga.d (𝒜 := S.D.𝒜 ⊤) β = h) : TwistDatum S h where
  ι := Unit
  U _ := ⊤
  iSup_eq := iSup_const
  ch _ _ _ := 1
  normalized _ _ _ _ := rfl
  cocycle _ _ _ _ _ _ _ _ _ := by simp only [map_one, inv_one, mul_one]
  h0 _ := β
  h0_mem _ := hβ
  d_h0 _ := by rw [hh]; exact (S.D.res_id ⊤ h).symm
  u _ _ := 1
  d_u _ _ := by
    rw [sub_self, zero_mul]
    exact GCDga.d_one'
  u_self _ := rfl
  u_symm _ _ := by simp only [map_one, inv_one]
  ρ_ch _ _ _ := by
    simp only [Units.val_one, map_one, inv_one, mul_one]

/-- **Z3.c (K8).** The trivial twist datum for `h = 0`: cover `{⊤}`, `h⁰ = 0`, `u = 1`, `ȟ = 1`. -/
def trivialTwistDatum (S : DgaSheafData X) : TwistDatum S 0 :=
  exactTwistDatum S 0 (Submodule.zero_mem _) 0 (map_zero _)

end Cohesive
