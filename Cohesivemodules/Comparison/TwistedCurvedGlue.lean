import Cohesivemodules.Comparison.TwistedCurvedComp

set_option linter.style.header false

/-!
# Z3.t: gluing the curved connection (blueprint-tw G′ (h))

Part 2 of the curved model of `TwistedCurvedModel.lean` (split for file size). The local
elements `θ_α(πgen α s) + h⁰_α ⊗ πgen α s` are compatible on `U_α ∩ U_β` (`yloc_compat`, using
`twModel_TD_comm` and `d(u_αβ⁻¹) = −u_αβ⁻¹(h⁰_β − h⁰_α)`), so they glue in the sheaf `T^{p+1}`
(C7.a) to `tG p s`; `θgen`, `πTot_θgen`, `πTot_θext` and the Leibniz rule `θext_leibniz` of the
extension are the input of `exists_θh`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum
open PreResolvingData (topO)

attribute [local instance] PreResolvingData.tDegModuleC

variable {X : Type} [TopologicalSpace X] [CompactSpace X] (P : PreResolvingData X)
  {h : P.D.A ⊤} (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2)
  (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (K' : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ)

variable (θ : ∀ α, P.Conn (T.U α) (twFα P T K' α))
  (hθ : ∀ α, P.IsBCConn (T.U α) (twKα P T K' α) (θ α))

include hθ in
/-- Z3.t: the gluing `φ^T` intertwines the connections on generators (`twModel_TD_comm` on
`1 ⊗ z`). -/
theorem twTotφ_θ (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (z : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    twTotφ P T K' α β hα hβ (((θ α).θ (ovr hα)).θ
        (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z)) =
      ((θ β).θ (ovr hβ)).θ
        (lof ↥(P.D.𝒜 (ovr hβ).unop.left 0) ℤ (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p
          (twGenφ P T K' α β hα hβ p z)) := by
  have hx : Tot.tmul (P.D.𝒜 (ovr hα).unop.left) (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) 1
      (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z) ∈
      P.tDeg (T.U α) (twFα P T K' α) p (ovr hα) := by
    have := tmul_mem_totDeg (𝒜 := P.D.𝒜 (ovr hα).unop.left)
      (Q := (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)))
      (SetLike.GradedOne.one_mem (A := P.D.𝒜 (ovr hα).unop.left)) z
    rwa [zero_add] at this
  have h2 := congrArg Subtype.val (twModel_TD_comm P T K' θ hθ p α β hα hβ ⟨_, hx⟩)
  have h3 : twTotφ P T K' α β hα hβ (((θ α).θ (ovr hα)).extend (Tot.tmul _ _ 1
      (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z))) =
      ((θ β).θ (ovr hβ)).extend (twTotφ P T K' α β hα hβ (Tot.tmul _ _ 1
      (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z))) :=
    h2
  have h4 : twTotφ P T K' α β hα hβ (Tot.tmul _ _ 1
      (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z)) =
      Tot.tmul (P.D.𝒜 (ovr hβ).unop.left) (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) 1
        (lof ↥(P.D.𝒜 (ovr hβ).unop.left 0) ℤ (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p
          (twGenφ P T K' α β hα hβ p z)) := by
    rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
    simp only [twTotφ, totMapAlong_tmul, famMap_of]
    rfl
  rw [GenData.extend_tmul_one, h4, GenData.extend_tmul_one] at h3
  exact h3

/-- Z3.t: the component `γ` of the restriction of a global section to `W ≤ U_γ` is the restriction
of `πgen γ s` (naturality of `untwistRestrIso`). -/
theorem cmpW_glob (γ : T.ι) {W : Opens X} (hγ : W ≤ T.U γ) (p : ℤ)
    (s : twGens P T K' p) :
    cmpW P T K' γ hγ p
        (P.fRes ⊤ (twFtop P T K') p (PreResolvingData.toV (ovr (hγ.trans le_top))) s) =
      P.fRes (T.U γ) (twFα P T K' γ) p (PreResolvingData.toV (ovr hγ)) (πgen P T K' γ p s) := by
  have n := PresheafOfModules.naturality_apply (untwistRestrIso P T (K'.X p) γ).hom.val
    (PreResolvingData.toV (ovr hγ))
    ((((untwF P T K').X p).val.map (homOfLE (le_top : T.U γ ≤ ⊤)).op).hom s)
  have hc : (((untwF P T K').X p).val.map (homOfLE (hγ.trans le_top)).op).hom s =
      (((untwF P T K').X p).val.map (homOfLE hγ).op).hom
        ((((untwF P T K').X p).val.map (homOfLE (le_top : T.U γ ≤ ⊤)).op).hom s) :=
    (PresheafOfModules.congr_map_apply ((untwF P T K').X p).val
      (Subsingleton.elim (homOfLE (hγ.trans le_top)).op
      ((homOfLE (le_top : T.U γ ≤ ⊤)).op ≫ (homOfLE hγ).op)) s).trans
      (PresheafOfModules.map_comp_apply ((untwF P T K').X p).val
        (homOfLE (le_top : T.U γ ≤ ⊤)).op (homOfLE hγ).op s)
  exact (congrArg (fun t => ((untwistRestrIso P T (K'.X p) γ).hom.val.app (ovr hγ)).hom t) hc).trans
    n

/-- Z3.t: `h⁰_α` as an element of the algebra at the terminal object of `Over U_α`. -/
abbrev h0A (α : T.ι) : P.D.A (topO (T.U α)).unop.left := T.h0 α

/-- Z3.t: `h⁰_α|W` as an element of the algebra at the over-object `W ≤ U`. -/
abbrev h0W (α : T.ι) {W U : Opens X} (hU : W ≤ U) (hα : W ≤ T.U α) :
    P.D.A (ovr hU).unop.left := P.D.res hα (T.h0 α)

/-- Z3.t: `φ^T(1 ⊗ z) = 1 ⊗ φ^B(z)` on generators. -/
theorem twTotφ_tmul_lof (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α)
    (hβ : W ≤ T.U β) (z : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    twTotφ P T K' α β hα hβ (Tot.tmul _ _ 1
      (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z)) =
      Tot.tmul (P.D.𝒜 (ovr hβ).unop.left) (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) 1
        (lof ↥(P.D.𝒜 (ovr hβ).unop.left 0) ℤ (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p
          (twGenφ P T K' α β hα hβ p z)) := by
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  simp only [twTotφ, totMapAlong_tmul, famMap_of]
  rfl

/-- Z3.t: the local element `θ_α(z) + b ⊗ z` on sections over `W ≤ U_α`. -/
def yW (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (b : P.D.A (ovr hα).unop.left) (p : ℤ)
    (z : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) : P.TTot (T.U α) (twFα P T K' α) (ovr hα) :=
  ((θ α).θ (ovr hα)).θ
      (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z) +
    b • Tot.tmul (P.D.𝒜 (ovr hα).unop.left)
      (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) 1
      (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z)

/-- Z3.t: restriction of the local element: `tRes(θ_α z + b ⊗ z) = θ_α(z|W') + b|W' ⊗ z|W'`
(`Conn.natural`, `tRes_smul`). -/
theorem tRes_yW (α : T.ι) {W W' : Opens X} (hα : W ≤ T.U α) (hW' : W' ≤ W)
    (b : P.D.A (ovr hα).unop.left) (p : ℤ) (z : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    P.tRes (T.U α) (twFα P T K' α) ((Over.homMk (homOfLE hW') :
        Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op)
      (yW P T K' θ α hα b p z) =
      yW P T K' θ α (hW'.trans hα) (P.D.res hW' b) p
        (P.fRes (T.U α) (twFα P T K' α) p ((Over.homMk (homOfLE hW') :
          Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op) z) := by
  unfold yW
  rw [map_add]
  have n := (θ α).natural ((Over.homMk (homOfLE hW') :
    Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op)
    (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z)
  have n' : P.tRes (T.U α) (twFα P T K' α) ((Over.homMk (homOfLE hW') :
        Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op)
      (((θ α).θ (ovr hα)).θ (lof ↥(P.D.𝒜 (ovr hα).unop.left 0) ℤ
        (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) p z)) =
      ((θ α).θ (ovr (hW'.trans hα))).θ (lof ↥(P.D.𝒜 (ovr (hW'.trans hα)).unop.left 0) ℤ
        (P.FSec (T.U α) (twFα P T K' α) · (ovr (hW'.trans hα))) p
        (P.fRes (T.U α) (twFα P T K' α) p ((Over.homMk (homOfLE hW') :
          Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op) z)) :=
    n.trans (congrArg ((θ α).θ (ovr (hW'.trans hα))).θ
      (famMap_of (fun p => P.fRes (T.U α) (twFα P T K' α) p ((Over.homMk (homOfLE hW') :
        Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op)) p z))
  refine congrArg₂ (· + ·) n' ?_
  rw [P.tRes_smul]
  refine congrArg (fun t => _ • t) ?_
  rw [PreResolvingData.tRes_apply, totMapAlong_tmul, DgaHom.map_one']
  exact congrArg (Tot.tmul (P.D.𝒜 (ovr (hW'.trans hα)).unop.left)
    (P.FSec (T.U α) (twFα P T K' α) · (ovr (hW'.trans hα))) 1)
    (famMap_of (fun p => P.fRes (T.U α) (twFα P T K' α) p ((Over.homMk (homOfLE hW') :
      Over.mk (homOfLE (hW'.trans hα)) ⟶ Over.mk (homOfLE hα)).op)) p z)

include hθ in
/-- Z3.t: the compatibility of the local elements on `W ≤ U_α ⊓ U_β`:
`u_αβ⁻¹ · φ^T(θ_α z + h⁰_α ⊗ z) = θ_β(u⁻¹ φ z) + h⁰_β ⊗ u⁻¹ φ z`. -/
theorem yW_compat (p : ℤ) (α β : T.ι) {W : Opens X} (hα : W ≤ T.U α) (hβ : W ≤ T.U β)
    (z : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    (Subtype.val (fuA P T α β hα hβ) : P.D.A (ovr hβ).unop.left) •
        twTotφ P T K' α β hα hβ (yW P T K' θ α hα (h0W P T α hα hα) p z) =
      yW P T K' θ β hβ (h0W P T β hβ hβ) p
        (fuA P T α β hα hβ • twGenφ P T K' α β hα hβ p z) := by
  have e1 : twTotφ P T K' α β hα hβ (yW P T K' θ α hα (h0W P T α hα hα) p z) =
      ((θ β).θ (ovr hβ)).θ
        (lof ↥(P.D.𝒜 (ovr hβ).unop.left 0) ℤ (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p
          (twGenφ P T K' α β hα hβ p z)) +
      h0W P T α hβ hα • Tot.tmul (P.D.𝒜 (ovr hβ).unop.left)
        (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) 1
        (lof ↥(P.D.𝒜 (ovr hβ).unop.left 0) ℤ (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p
          (twGenφ P T K' α β hα hβ p z)) := by
    unfold yW
    rw [map_add, twTotφ_θ P T K' θ hθ p α β hα hβ z]
    refine congrArg _ ?_
    exact (totMapAlong_smul (idAt P T hα hβ) (twGenφ P T K' α β hα hβ)
      (twGenφ_smul P T K' α β hα hβ) _ _).trans
      (congrArg _ (twTotφ_tmul_lof P T K' p α β hα hβ z))
  rw [e1]
  unfold yW
  rw [map_smul (DirectSum.lof ↥(P.D.𝒜 (ovr hβ).unop.left 0) ℤ
    (P.FSec (T.U β) (twFα P T K' β) · (ovr hβ)) p) (fuA P T α β hα hβ)]
  exact compat_alg ((θ β).θ (ovr hβ)) (fuA P T α β hα hβ) _ _ (d_fuA P T α β hα hβ) _

/-- Z3.t: the local element on `U_α`, transported to sections of `F` over `U_α`
(`cTotWInv`), for the global generator `s`. -/
def yloc (α : T.ι) (p : ℤ) (s : twGens P T K' p) :
    P.TTot ⊤ (twFtop P T K') (ovr ((le_refl (T.U α)).trans (le_top : T.U α ≤ ⊤))) :=
  cTotWInv P T K' α (le_refl (T.U α))
    (yW P T K' θ α (le_refl (T.U α)) (h0A P T α) p (πgen P T K' α p s))

include hθ in
/-- Z3.t: the transported local elements agree on `U_α ⊓ U_β` (`cTotW β` is injective;
`cTotW_compat`, `yW_compat`, `cmpW_glob`). -/
theorem yloc_compat (α β : T.ι) (p : ℤ) (s : twGens P T K' p) :
    P.tRes ⊤ (twFtop P T K') (resF ((le_refl (T.U α)).trans (le_top : T.U α ≤ ⊤))
        (inf_le_left : T.U α ⊓ T.U β ≤ T.U α)) (yloc P T K' θ α p s) =
      P.tRes ⊤ (twFtop P T K') (resF ((le_refl (T.U β)).trans (le_top : T.U β ≤ ⊤))
        (inf_le_right : T.U α ⊓ T.U β ≤ T.U β)) (yloc P T K' θ β p s) := by
  have hα : T.U α ⊓ T.U β ≤ T.U α := inf_le_left
  have hβ : T.U α ⊓ T.U β ≤ T.U β := inf_le_right
  refine (cTotWInv_cTotW P T K' β (inf_le_right : T.U α ⊓ T.U β ≤ T.U β) _).symm.trans
    (Eq.trans (congrArg (cTotWInv P T K' β hβ) ?_)
      (cTotWInv_cTotW P T K' β (inf_le_right : T.U α ⊓ T.U β ≤ T.U β) _))
  have L1 := cTotW_compat P T K' α β hα hβ (P.tRes ⊤ (twFtop P T K')
    (resF ((le_refl (T.U α)).trans (le_top : T.U α ≤ ⊤)) hα) (yloc P T K' θ α p s))
  have L2 := cTotW_tRes P T K' α (le_refl (T.U α)) hα (yloc P T K' θ α p s)
  have L3 : cTotW P T K' α (le_refl (T.U α)) (yloc P T K' θ α p s) =
      yW P T K' θ α (le_refl (T.U α)) (h0A P T α) p (πgen P T K' α p s) :=
    cTotW_cTotWInv P T K' α (le_refl (T.U α))
      (yW P T K' θ α (le_refl (T.U α)) (h0A P T α) p (πgen P T K' α p s))
  have L4 := tRes_yW P T K' θ α (le_refl (T.U α)) hα (h0A P T α) p (πgen P T K' α p s)
  have R2 := cTotW_tRes P T K' β (le_refl (T.U β)) hβ (yloc P T K' θ β p s)
  have R3 : cTotW P T K' β (le_refl (T.U β)) (yloc P T K' θ β p s) =
      yW P T K' θ β (le_refl (T.U β)) (h0A P T β) p (πgen P T K' β p s) :=
    cTotW_cTotWInv P T K' β (le_refl (T.U β))
      (yW P T K' θ β (le_refl (T.U β)) (h0A P T β) p (πgen P T K' β p s))
  have R4 := tRes_yW P T K' θ β (le_refl (T.U β)) hβ (h0A P T β) p (πgen P T K' β p s)
  have hz : P.fRes (T.U β) (twFα P T K' β) p (PreResolvingData.toV (ovr hβ))
      (πgen P T K' β p s) = fuA P T α β hα hβ • twGenφ P T K' α β hα hβ p
        (P.fRes (T.U α) (twFα P T K' α) p (PreResolvingData.toV (ovr hα)) (πgen P T K' α p s)) :=
    (cmpW_glob P T K' β hβ p s).symm.trans ((cmpW_compat P T K' α β hα hβ p _).trans
      (congrArg _ (congrArg _ (cmpW_glob P T K' α hα p s))))
  rw [L1, L2, L3, L4, R2, R3, R4, yW_compat P T K' θ hθ p α β hα hβ]
  exact congrArg (yW P T K' θ β hβ _ p) hz.symm

/-- Z3.t: `secRes` of the sheaf `T^n` is `tRes` (general opens over `⊤`). -/
theorem secRes_val (n : ℤ) {W W' : Opens X} (hW : W ≤ ⊤) (hW' : W' ≤ W)
    (z : P.tDeg ⊤ (twFtop P T K') n (ovr hW)) :
    (show P.tDeg ⊤ (twFtop P T K') n (ovr (hW'.trans hW)) from
      secRes P.A0 (P.tShAC ⊤ (twFtop P T K') n) hW hW' z).1 =
      P.tRes ⊤ (twFtop P T K') (resF hW hW') z.1 := rfl

/-- Z3.t: the local element has total degree `p + 1`. -/
theorem yW_mem (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (b : P.D.A (ovr hα).unop.left)
    (hb : b ∈ P.D.𝒜 (ovr hα).unop.left 1) (p : ℤ)
    (z : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    yW P T K' θ α hα b p z ∈ totDeg (P.D.𝒜 (ovr hα).unop.left)
      (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)) (p + 1) := by
  refine add_mem ((θ α).mem (ovr hα) p z) ?_
  have h1 := tmul_mem_totDeg (𝒜 := P.D.𝒜 (ovr hα).unop.left)
    (Q := (P.FSec (T.U α) (twFα P T K' α) · (ovr hα)))
    (SetLike.GradedOne.one_mem (A := P.D.𝒜 (ovr hα).unop.left)) z
  have h2 := smul_mem_totDeg (𝒜 := P.D.𝒜 (ovr hα).unop.left)
    (Q := (P.FSec (T.U α) (twFα P T K' α) · (ovr hα))) hb h1
  rw [show 1 + (0 + p) = p + 1 by ring] at h2
  exact h2

/-- Z3.t: the transported local element has total degree `p + 1`. -/
theorem yloc_mem (α : T.ι) (p : ℤ) (s : twGens P T K' p) :
    yloc P T K' θ α p s ∈ P.tDeg ⊤ (twFtop P T K') (p + 1)
      (ovr ((le_refl (T.U α)).trans (le_top : T.U α ≤ ⊤))) :=
  totMapAlong_mem_totDeg _ _ _
    (yW_mem P T K' θ α (le_refl (T.U α)) (h0A P T α) (T.h0_mem α) p (πgen P T K' α p s))

/-- Z3.t: the underlying total element of a section of the sheaf `T^n` over `W ≤ ⊤`. -/
def secVal (n : ℤ) {W : Opens X} (hW : W ≤ ⊤)
    (z : sec P.A0 (P.tShAC ⊤ (twFtop P T K') n) hW) : P.TTot ⊤ (twFtop P T K') (ovr hW) :=
  Subtype.val (p := fun x => x ∈ P.tDeg ⊤ (twFtop P T K') n (ovr hW)) z

/-- Z3.t: `secVal` is injective. -/
theorem secVal_inj (n : ℤ) {W : Opens X} (hW : W ≤ ⊤)
    {z z' : sec P.A0 (P.tShAC ⊤ (twFtop P T K') n) hW}
    (h : secVal P T K' n hW z = secVal P T K' n hW z') : z = z' :=
  Subtype.ext h

/-- Z3.t: `secVal` of a restriction is the restriction of `secVal`. -/
theorem secVal_secRes (n : ℤ) {W W' : Opens X} (hW : W ≤ ⊤) (hW' : W' ≤ W)
    (z : sec P.A0 (P.tShAC ⊤ (twFtop P T K') n) hW) :
    secVal P T K' n (hW'.trans hW) (secRes P.A0 (P.tShAC ⊤ (twFtop P T K') n) hW hW' z) =
      P.tRes ⊤ (twFtop P T K') (resF hW hW') (secVal P T K' n hW z) := rfl

-- Raised heartbeats: the gluing hypothesis `hs` of `sec_existsUnique_gluing` compares sections
-- over `U_α ⊓ U_β` whose indices differ only by proof terms of `U_α ⊓ U_β ≤ ⊤`, and the
-- elaborator's `isDefEq` on the sheaf of modules `T^n` unfolds heavily before using proof
-- irrelevance (the proof is a single `apply`/`exact`).
set_option maxHeartbeats 2000000 in
/-- Z3.t: gluing in the sheaf `T^n` (C7.a): a family of elements of `T^n(U_α)` that agree on
`U_α ⊓ U_β` comes from a global element. -/
theorem glue_aux (n : ℤ)
    (x : ∀ α : T.ι, P.TTot ⊤ (twFtop P T K')
      (ovr ((le_refl (T.U α)).trans (le_top : T.U α ≤ ⊤))))
    (hx : ∀ α, x α ∈ P.tDeg ⊤ (twFtop P T K') n
      (ovr ((le_refl (T.U α)).trans (le_top : T.U α ≤ ⊤))))
    (hc : ∀ α β, P.tRes ⊤ (twFtop P T K') (resF ((le_refl (T.U α)).trans
        (le_top : T.U α ≤ ⊤)) (inf_le_left : T.U α ⊓ T.U β ≤ T.U α)) (x α) =
      P.tRes ⊤ (twFtop P T K') (resF ((le_refl (T.U β)).trans (le_top : T.U β ≤ ⊤))
        (inf_le_right : T.U α ⊓ T.U β ≤ T.U β)) (x β)) :
    ∃ t : P.TTot ⊤ (twFtop P T K') (ovr (le_refl (⊤ : Opens X))),
      t ∈ P.tDeg ⊤ (twFtop P T K') n (ovr (le_refl (⊤ : Opens X))) ∧
        ∀ α, P.tRes ⊤ (twFtop P T K') (toUα P T α) t = x α := by
  obtain ⟨t, ht, -⟩ := sec_existsUnique_gluing (R := P.A0) (le_refl (⊤ : Opens X))
    (P.tShAC ⊤ (twFtop P T K') n) T.U (fun α => le_top) T.iSup_eq.ge
    (fun α => ⟨x α, hx α⟩) (fun α β => by
      apply secVal_inj
      exact hc α β)
  refine ⟨t.1, t.2, fun α => ?_⟩
  exact (secVal_secRes P T K' n (le_refl (⊤ : Opens X)) (le_top : T.U α ≤ ⊤) t).symm.trans
    (congrArg (secVal P T K' n _) (ht α))

include hθ in
/-- Z3.t: gluing of the transported local elements in the sheaf `T^{p+1}` (C7.a). -/
theorem exists_glue (p : ℤ) (s : twGens P T K' p) :
    ∃ t : P.TTot ⊤ (twFtop P T K') (ovr (le_refl (⊤ : Opens X))),
      t ∈ P.tDeg ⊤ (twFtop P T K') (p + 1) (ovr (le_refl (⊤ : Opens X))) ∧
        ∀ α, P.tRes ⊤ (twFtop P T K') (toUα P T α) t = yloc P T K' θ α p s :=
  glue_aux P T K' (p + 1) (fun α => yloc P T K' θ α p s) (fun α => yloc_mem P T K' θ α p s)
    (fun α β => yloc_compat P T K' θ hθ α β p s)

/-- Z3.t: `yW` is additive in the section. -/
theorem yW_add (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (b : P.D.A (ovr hα).unop.left)
    (p : ℤ) (z z' : P.FSec (T.U α) (twFα P T K' α) p (ovr hα)) :
    yW P T K' θ α hα b p (z + z') = yW P T K' θ α hα b p z + yW P T K' θ α hα b p z' := by
  unfold yW
  simp only [map_add, Tot.tmul_add, smul_add]
  abel

/-- Z3.t: `yW` vanishes on `0`. -/
theorem yW_zero (α : T.ι) {W : Opens X} (hα : W ≤ T.U α) (b : P.D.A (ovr hα).unop.left)
    (p : ℤ) : yW P T K' θ α hα b p 0 = 0 := by
  unfold yW
  simp only [map_zero, Tot.tmul_zero, smul_zero, add_zero]

/-- Z3.t: `yloc` is additive in the global generator. -/
theorem yloc_add (α : T.ι) (p : ℤ) (s s' : twGens P T K' p) :
    yloc P T K' θ α p (s + s') = yloc P T K' θ α p s + yloc P T K' θ α p s' := by
  unfold yloc
  rw [map_add (πgen P T K' α p)]
  exact (congrArg (cTotWInv P T K' α (le_refl (T.U α)))
    (yW_add P T K' θ α (le_refl (T.U α)) (h0A P T α) p _ _)).trans (map_add _ _ _)

/-- Z3.t: `yloc` vanishes on `0`. -/
theorem yloc_zero (α : T.ι) (p : ℤ) : yloc P T K' θ α p 0 = 0 := by
  unfold yloc
  rw [map_zero (πgen P T K' α p)]
  exact (congrArg (cTotWInv P T K' α (le_refl (T.U α)))
    (yW_zero P T K' θ α (le_refl (T.U α)) (h0A P T α) p)).trans (map_zero _)

include hθ in
/-- Z3.t: the glued element `θ^h(s) ∈ T^{p+1}(X)` (a choice in `exists_glue`). -/
def tG (p : ℤ) (s : twGens P T K' p) :
    P.TTot ⊤ (twFtop P T K') (ovr (le_refl (⊤ : Opens X))) :=
  (exists_glue P T K' θ hθ p s).choose

include hθ in
/-- Z3.t: `tG` has total degree `p + 1`. -/
theorem tG_mem (p : ℤ) (s : twGens P T K' p) :
    tG P T K' θ hθ p s ∈ P.tDeg ⊤ (twFtop P T K') (p + 1) (ovr (le_refl (⊤ : Opens X))) :=
  (exists_glue P T K' θ hθ p s).choose_spec.1

include hθ in
/-- Z3.t: the restriction of `tG` to `U_α` is the transported local element. -/
theorem tG_res (α : T.ι) (p : ℤ) (s : twGens P T K' p) :
    P.tRes ⊤ (twFtop P T K') (toUα P T α) (tG P T K' θ hθ p s) = yloc P T K' θ α p s :=
  (exists_glue P T K' θ hθ p s).choose_spec.2 α

include hθ in
/-- Z3.t: `tG` is additive (uniqueness `tDeg_ext`). -/
theorem tG_add (p : ℤ) (s s' : twGens P T K' p) :
    tG P T K' θ hθ p (s + s') = tG P T K' θ hθ p s + tG P T K' θ hθ p s' :=
  tDeg_ext P T K' (p + 1) (tG_mem P T K' θ hθ p _)
    (add_mem (tG_mem P T K' θ hθ p _) (tG_mem P T K' θ hθ p _)) fun α => by
      rw [tG_res P T K' θ hθ, map_add, tG_res P T K' θ hθ, tG_res P T K' θ hθ, yloc_add]

include hθ in
/-- Z3.t: `tG` vanishes on `0`. -/
theorem tG_zero (p : ℤ) : tG P T K' θ hθ p 0 = 0 :=
  tDeg_ext P T K' (p + 1) (tG_mem P T K' θ hθ p _) (zero_mem _) fun α => by
    rw [tG_res P T K' θ hθ, map_zero, yloc_zero]

include hθ in
/-- Z3.t: `tG` as an additive map `F^p(X) → T^{p+1}(X)`, the generator map of `θ^h`. -/
def θgen (p : ℤ) : twGens P T K' p →+ TotX P T K' where
  toFun s := tG P T K' θ hθ p s
  map_zero' := tG_zero P T K' θ hθ p
  map_add' := tG_add P T K' θ hθ p

include hθ in
/-- Z3.t: `πTot α (θ^h s) = θ_α(s_α) + h⁰_α ⊗ s_α` (`tG_res`, `cTotW_cTotWInv`). -/
theorem πTot_θgen (α : T.ι) (p : ℤ) (s : twGens P T K' p) :
    πTot P T K' α (θgen P T K' θ hθ p s) =
      yW P T K' θ α (le_refl (T.U α)) (h0A P T α) p (πgen P T K' α p s) := by
  have e1 : πTot P T K' α (θgen P T K' θ hθ p s) =
      cTotW P T K' α (le_refl (T.U α)) (P.tRes ⊤ (twFtop P T K') (toUα P T α)
        (tG P T K' θ hθ p s)) :=
    (πTot_eq_cTot P T K' α (tG P T K' θ hθ p s)).trans
      (congrArg (cTot P T K' α) (tRes_toV P T K' α _))
  rw [e1, tG_res P T K' θ hθ]
  exact cTotW_cTotWInv P T K' α (le_refl (T.U α)) _

include hθ in
/-- Z3.t: `πTot_θgen` on all of `⨁_p F^p(X)` for the additive extension `θ^h`. -/
theorem πTot_θext (α : T.ι) (e : ⨁ p, twGens P T K' p) :
    πTot P T K' α (DirectSum.toAddMonoid (θgen P T K' θ hθ) e) =
      ((θ α).θ (topO (T.U α))).θ (famMap (πgen P T K' α) e) +
        h0A P T α • Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
          (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1 (famMap (πgen P T K' α) e) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero, add_zero, Tot.tmul_zero]
  | of p s =>
    rw [DirectSum.toAddMonoid_of, famMap_of]
    exact πTot_θgen P T K' θ hθ α p s
  | add x y hx hy =>
    simp only [map_add, hx, hy, Tot.tmul_add, smul_add]
    abel

include hθ in
/-- Z3.t: the Leibniz rule for `θ^h` on generators (`πTot_ext`, Leibniz of `θ_α`). -/
theorem θext_leibniz (f : ↥(P.D.𝒜 (topO (⊤ : Opens X)).unop.left 0))
    (e : ⨁ p, twGens P T K' p) :
    DirectSum.toAddMonoid (θgen P T K' θ hθ) (f • e) =
      Tot.tmul (P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (twGens P T K')
        (GCDga.d (𝒜 := P.D.𝒜 (topO (⊤ : Opens X)).unop.left) (f : P.D.A (topO ⊤).unop.left)) e +
      (f : P.D.A (topO (⊤ : Opens X)).unop.left) •
        DirectSum.toAddMonoid (θgen P T K' θ hθ) e := by
  refine πTot_ext P T K' _ _ fun α => ?_
  have h0m : h0A P T α ∈ P.D.𝒜 (topO (T.U α)).unop.left 1 := T.h0_mem α
  have hE := famMap_smul_along (resα P T α) (πgen P T K' α) (πgen_smul P T K' α) f e
  have hL := ((θ α).θ (topO (T.U α))).leibniz ((resα P T α).f0 f) (famMap (πgen P T K' α) e)
  have R1 : πTot P T K' α (Tot.tmul _ _ (GCDga.d (𝒜 := P.D.𝒜 (topO (⊤ : Opens X)).unop.left)
      (f : P.D.A (topO ⊤).unop.left)) e) =
      Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
        (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α)))
        (GCDga.d (𝒜 := P.D.𝒜 (topO (T.U α)).unop.left)
          (((resα P T α).f0 f : ↥(P.D.𝒜 (topO (T.U α)).unop.left 0)) :
            P.D.A (topO (T.U α)).unop.left)) (famMap (πgen P T K' α) e) :=
    (totMapAlong_tmul _ _ _ _ _).trans
      (congrArg (fun a => Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
        (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) a (famMap (πgen P T K' α) e))
        ((resα P T α).map_d f))
  have R2 : πTot P T K' α ((f : P.D.A (topO (⊤ : Opens X)).unop.left) •
      DirectSum.toAddMonoid (θgen P T K' θ hθ) e) =
      (((resα P T α).f0 f : ↥(P.D.𝒜 (topO (T.U α)).unop.left 0)) :
        P.D.A (topO (T.U α)).unop.left) •
        (((θ α).θ (topO (T.U α))).θ (famMap (πgen P T K' α) e) +
          h0A P T α • Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
            (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1 (famMap (πgen P T K' α) e)) :=
    (totMapAlong_smul (resα P T α) (πgen P T K' α) (πgen_smul P T K' α) _ _).trans
      (congrArg _ (πTot_θext P T K' θ hθ α e))
  have R3 : h0A P T α • Tot.tmul (P.D.𝒜 (topO (T.U α)).unop.left)
      (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1
      (((resα P T α).f0 f) • famMap (πgen P T K' α) e) =
      (((resα P T α).f0 f : ↥(P.D.𝒜 (topO (T.U α)).unop.left 0)) :
        P.D.A (topO (T.U α)).unop.left) • (h0A P T α • Tot.tmul
          (P.D.𝒜 (topO (T.U α)).unop.left)
          (P.FSec (T.U α) (twFα P T K' α) · (topO (T.U α))) 1 (famMap (πgen P T K' α) e)) := by
    rw [Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul, smul_smul, smul_smul,
      GCDga.central (P.D.𝒜 (topO (T.U α)).unop.left) ((resα P T α).f0 f).2]
  rw [πTot_θext P T K' θ hθ α, hE, map_add, R1, R2, hL, R3, smul_add]
  abel
end Cohesive
