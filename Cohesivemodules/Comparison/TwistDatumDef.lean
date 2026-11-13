-- FROZEN (gate 12, 6 Nov 2026; in MainStatementTwisted). Do not edit.
import Cohesivemodules.Comparison.CurvedPresheaf
import Cohesivemodules.Sheaf.Twisted.CocycleDef
import Cohesivemodules.Forms.CurvedDolbeault

set_option linter.style.header false

/-!
# Z3.c: twist data (the Čech–Dolbeault zigzag, multiplicative form)

Blueprint item Z3.c (`blueprint/blueprint-tw.md` §2.2; blueprint §11 v1.19, decision D2). For
sheaf data `S` (with `ρ : O → 𝒜⁰`) and a closed `h ∈ 𝒜²(X)`, a twist datum is a finite cover with
* primitives `h⁰_α ∈ 𝒜¹(U_α)`, `d h⁰_α = h|U_α`;
* gluing units `u_αβ ∈ 𝒜⁰(U_α ∩ U_β)ˣ` with `d u_αβ = (h⁰_β − h⁰_α) u_αβ`, `u_αα = 1`,
  `u_βα = u_αβ⁻¹`;
* a normalized Čech 2-cocycle `ȟ` of units of `O` (`TwistCocycle`) with
  `ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹` on `U_α ∩ U_β ∩ U_γ`.

## Deviations
* [A, Def 7.2.2] uses `(h⁰, h¹, h², exp_ℛ)` with `u = exp h¹`, `ȟ = exp_ℛ h²` and needs a cover
  on which closed 1-forms on double intersections are exact (implicit Leray hypothesis); here
  the units `u`, `ȟ` are the data, and existence (`exists_twistData`, Z3.d) uses only local H1.
* The cocycle and normalization of `ȟ` are fields (of `TwistCocycle`), although they follow from
  `ρ_ch`, `u_self`, `u_symm` and injectivity of `ρ` (blueprint-tw B.6).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- Z3.c: `U_α ∩ U_β ∩ U_γ ≤ U_β ∩ U_γ`. -/
theorem tri_le_bc {U₁ U₂ U₃ : Opens X} : U₁ ⊓ U₂ ⊓ U₃ ≤ U₂ ⊓ U₃ :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- Z3.c: `U_α ∩ U_β ∩ U_γ ≤ U_α ∩ U_γ`. -/
theorem tri_le_ac {U₁ U₂ U₃ : Opens X} : U₁ ⊓ U₂ ⊓ U₃ ≤ U₁ ⊓ U₃ :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

/-- **Z3.c.** [A, Def 7.2.2] (multiplicative form). A twist datum for the closed `h ∈ 𝒜²(X)`
over the sheaf data `S`: a normalized unit cocycle `ȟ` of `S.O` on a finite cover (`TwistCocycle`),
primitives `h0 α` of `h|U_α` of degree `1`, gluing units `u α β` of `𝒜⁰(U_α ∩ U_β)` with
logarithmic derivative `h0 β − h0 α`, `u α α = 1`, `u β α = u α β⁻¹` (after restriction along
`U_β ∩ U_α = U_α ∩ U_β`), and `ρ(ȟ_αβγ) = u_βγ · u_αβ · u_αγ⁻¹` on `U_α ∩ U_β ∩ U_γ`. -/
structure TwistDatum (S : DgaSheafData X) (h : S.D.A ⊤) extends TwistCocycle S.O where
  /-- The primitives `h⁰_α`. -/
  h0 : ∀ α, S.D.A (U α)
  h0_mem : ∀ α, h0 α ∈ S.D.𝒜 (U α) 1
  d_h0 : ∀ α, GCDga.d (𝒜 := S.D.𝒜 (U α)) (h0 α) = S.D.res le_top h
  /-- The gluing units `u_αβ`. -/
  u : ∀ α β, (↥(S.D.𝒜 (U α ⊓ U β) 0))ˣ
  d_u : ∀ α β, GCDga.d (𝒜 := S.D.𝒜 (U α ⊓ U β)) ((u α β : ↥(S.D.𝒜 (U α ⊓ U β) 0)) :
      S.D.A (U α ⊓ U β)) =
    (S.D.res inf_le_right (h0 β) - S.D.res inf_le_left (h0 α)) *
      ((u α β : ↥(S.D.𝒜 (U α ⊓ U β) 0)) : S.D.A (U α ⊓ U β))
  u_self : ∀ α, u α α = 1
  u_symm : ∀ α β, u β α =
    (Units.map (S.D.res (inf_comm (U β) (U α)).le).f0.toMonoidHom (u α β))⁻¹
  ρ_ch : ∀ α β γ, S.ρ (U α ⊓ U β ⊓ U γ) (ch α β γ : S.O.obj.obj (op (U α ⊓ U β ⊓ U γ))) =
    (S.D.res tri_le_bc).f0 (u β γ : ↥(S.D.𝒜 (U β ⊓ U γ) 0)) *
      (S.D.res inf_le_left).f0 (u α β : ↥(S.D.𝒜 (U α ⊓ U β) 0)) *
      (S.D.res tri_le_ac).f0 ((u α γ)⁻¹ : (↥(S.D.𝒜 (U α ⊓ U γ) 0))ˣ)

section Dolbeault

open Manifold
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
  [T2Space X] [CompactSpace X]

/-- **Z3.c.** Twist data for a closed `h ∈ 𝒜^{0,2}(X)` over the (flat) Dolbeault data
(`O = O_X`, `ρ` the inclusion of holomorphic functions, F14). -/
abbrev TwistData (h : DolbeaultClosed2 E X) : Type 1 :=
  TwistDatum (dolbeaultPreData E X).toSheafData h.1

end Dolbeault

end Cohesive
