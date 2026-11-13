import Cohesivemodules.Comparison.TwistedPsi
import Cohesivemodules.Comparison.FullyFaithfulGlobal
import Cohesivemodules.Comparison.ModelDual
import Cohesivemodules.Sheaf.Twisted.HomSoftTw
import Cohesivemodules.Sheaf.Twisted.Perfect
import Cohesivemodules.Algebra.QuasiIsoElem
import Cohesivemodules.Sheaf.Soft

set_option linter.style.header false

/-!
# Z3.s: global part of C4^tw (blueprint-tw F′ (h), (k))

Blueprint item Z3.s (`blueprint/blueprint-tw.md` §3 F′ (h), (k); [A, Prop 7.2.19, §7.4]); twisted
copy of C4 step 4–5 (`Comparison/FullyFaithfulGlobal.lean`, `quasiIso_Γ_Ψ_comp`):
* bounds: `J_T(M)` is bounded below and (for compact `X`) above, `ℋ^h(M₁, M₂)` is bounded below;
* softness (F′ (h)): `𝒜⁰(X)` acts on every `J_T(M₁)^p` by multiplication (a morphism of twisted
  sheaves: `𝒜⁰` is commutative and `u_αβ` has degree `0`), so every term of
  `𝓗om^tw(J_T M₁, L)` is soft (`isSoft_twHomComplex_X`);
* `quasiIso_Γ_Ψtw_comp`: if `Ψ^tw ≫ r_*` is a quasi-isomorphism, so is its global sections;
* the `H⁰` dictionary (F′ (k)): if `Γ(Ψ^tw ≫ r_*)` is a quasi-isomorphism, then
  `[φ] ↦ [J_T(φ) ≫ r]` is a bijection from `H0(M₁, M₂)` to homotopy classes of chain maps
  `J_T(M₁) → I` (`twHomTopEquiv`, `Ψtw_top`).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X]

/-- Elements of total degree `m > b + N` of `𝒜 ⊗ Q` vanish when `Q^p = 0` for `p > b` and
`𝒜^q = 0` for `q > N` (copy of the private C4 lemma). -/
private theorem eq_zero_of_totDeg_gt' {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
    {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]
    (b N : ℤ) (hQ : ∀ p, b < p → Subsingleton (Q p)) (hA : ∀ q, N < q → ∀ a ∈ 𝒜 q, a = 0)
    {m : ℤ} (hm : b + N < m) {x : Tot 𝒜 Q} (hx : x ∈ totDeg 𝒜 Q m) : x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, p, a, e, hqp, ha, rfl⟩ := hx
    by_cases hp : b < p
    · have := hQ p hp
      rw [Subsingleton.elim e 0, map_zero, TensorProduct.tmul_zero]
      rfl
    · rw [hA q (by lia) a ha, TensorProduct.zero_tmul]
      rfl
  | zero => rfl
  | add x y _ _ hx hy => rw [hx, hy, add_zero]
  | smul r x _ hx => rw [hx, smul_zero]

namespace DgaSheafData

variable (S : DgaSheafData X) (M₁ M₂ : CohesiveModule S.𝒜X)

/-- **Z3.s (copy of C4 `exists_isStrictlyGE_ℋ`).** `ℋ(M₁, M₂)` over sheaf data `S` (e.g. the
curved data `S_h`) is bounded below (`Q₁`, `Q₂` bounded, `𝒜` bounded). -/
theorem exists_isStrictlyGE_ℋ' : ∃ a : ℤ, (S.ℋ M₁ M₂).IsStrictlyGE a := by
  obtain ⟨a₁, b₁, h₁⟩ := M₁.bounded
  obtain ⟨a₂, b₂, h₂⟩ := M₂.bounded
  refine ⟨a₂ - b₁ - GCDga.N (𝒜 := S.𝒜X), ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  change Limits.IsZero (S.homSh M₁ M₂ n)
  refine isZero_of_sections_subsingleton fun V => ⟨fun χ χ' => ?_⟩
  have hz : ∀ ψ : S.HomSec M₁ M₂ n (le_top : V.unop ≤ ⊤), ψ = 0 := fun ψ =>
    Subtype.ext (linearMap_eq_zero_of_totDeg ψ.1 a₁ b₁ h₁ fun m _ hm x hx =>
      eq_zero_of_totDeg_lt a₂ (fun p hp => bcGen_subsingleton (S.D.res le_top) (Q := M₂.Q) p
        (h₂ p (Or.inl hp))) (by lia) (ψ.2.1 hx))
  exact (hz χ).trans (hz χ').symm

/-- Multiplication by `0` (`smul0L`). -/
theorem smul0L_zero' {U₀ : Opens X} (M : CohesiveModule (S.D.𝒜 U₀)) (n : ℤ) {V : Opens X}
    (hV : V ≤ U₀) (x : S.sheafOfSec M n hV) : S.smul0L M n hV 0 x = 0 :=
  zero_smul _ (show ↥(S.deg0 M n hV) from x)

/-- Multiplication by a sum (`smul0L`). -/
theorem smul0L_add' {U₀ : Opens X} (M : CohesiveModule (S.D.𝒜 U₀)) (n : ℤ) {V : Opens X}
    (hV : V ≤ U₀) (u v : ↥(S.D.𝒜 V 0)) (x : S.sheafOfSec M n hV) :
    S.smul0L M n hV (u + v) x = S.smul0L M n hV u x + S.smul0L M n hV v x :=
  add_smul _ _ (show ↥(S.deg0 M n hV) from x)

end DgaSheafData

variable (D : ResolvingData X) {h : D.D.A ⊤} (T : TwistDatum D.toSheafData h)
  (hh : h ∈ D.D.𝒜 ⊤ 2) (hd : GCDga.d (𝒜 := D.D.𝒜 ⊤) h = 0)

/-- **Z3.s.** `J_T(M)` is bounded below: its components are restrictions of `α(M)^n`, which
vanish below the lowest degree of the generators. -/
theorem exists_isStrictlyGE_twistedSheafOf
    (M : CohesiveModule (D.toSheafData.withCurvature h hh hd).𝒜X) :
    ∃ n : ℤ, (T.twistedSheafOf hh hd M).IsStrictlyGE n := by
  obtain ⟨a₁, b₁, h₁⟩ := M.bounded
  refine ⟨a₁, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  refine TwMod.isZero_of_comp fun α =>
    Functor.map_isZero (restr (ringOf D.toSheafData.O) (T.U α)) ?_
  change Limits.IsZero ((D.toSheafData.withCurvature h hh hd).sheafOfSh M n)
  refine isZero_of_sections_subsingleton fun V => ⟨fun x y => ?_⟩
  have hz : ∀ z : (D.toSheafData.withCurvature h hh hd).sheafOfSec M n
      (le_top : V.unop ≤ ⊤), z = 0 := fun z =>
    Subtype.ext (eq_zero_of_totDeg_lt a₁ (fun p hp => bcGen_subsingleton
      ((D.toSheafData.withCurvature h hh hd).D.res le_top) (Q := M.Q) p
      (h₁ p (Or.inl hp))) hn z.2)
  exact (hz x).trans (hz y).symm

/-- **Z3.s.** For compact `X`, `J_T(M)` is bounded above (copy of C4
`exists_isStrictlyLE_sheafOf`: elements of total degree `> b + N` vanish, `zero_above`). -/
theorem exists_isStrictlyLE_twistedSheafOf [CompactSpace X]
    (M : CohesiveModule (D.toSheafData.withCurvature h hh hd).𝒜X) :
    ∃ n : ℤ, (T.twistedSheafOf hh hd M).IsStrictlyLE n := by
  obtain ⟨a, b, hb⟩ := M.bounded
  refine ⟨b + GCDga.N (D.D.𝒜 ⊤), ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  refine TwMod.isZero_of_comp fun α =>
    Functor.map_isZero (restr (ringOf D.toSheafData.O) (T.U α)) ?_
  change Limits.IsZero ((D.toSheafData.withCurvature h hh hd).sheafOfSh M n)
  refine isZero_of_sections_subsingleton fun V => ⟨fun x y => ?_⟩
  have hz : ∀ z : (D.toSheafData.withCurvature h hh hd).sheafOfSec M n
      (le_top : V.unop ≤ ⊤), z = 0 := fun z =>
    Subtype.ext (eq_zero_of_totDeg_gt' (𝒜 := (D.toSheafData.withCurvature h hh hd).D.𝒜 V.unop)
      b (GCDga.N (D.D.𝒜 ⊤))
      (fun p hp => bcGen_subsingleton ((D.toSheafData.withCurvature h hh hd).D.res
        (le_top : V.unop ≤ ⊤)) (Q := M.Q) p (hb p (Or.inr hp)))
      (fun q hq a ha => D.zero_above hq V.unop ha) hn z.2)
  exact (hz x).trans (hz y).symm

/-! ### Softness (F′ (h)) -/

section Soft

variable (M₁ : CohesiveModule (D.toSheafData.withCurvature h hh hd).𝒜X)

/-- **Z3.s** (blueprint-tw F′ (h)): multiplication by `res_V(a)` on `α(M₁)^p` (curved data),
`a ∈ 𝒜⁰(X)`, as an endomorphism of the sheaf on `X`. -/
def actTw (a : ↥(D.D.𝒜 ⊤ 0)) (p : ℤ) :
    (D.toSheafData.withCurvature h hh hd).sheafOfSh M₁ p ⟶
      (D.toSheafData.withCurvature h hh hd).sheafOfSh M₁ p :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom ((D.toSheafData.withCurvature h hh hd).smul0L M₁ p
        (le_top : V.unop ≤ ⊤) ((D.D.res (le_top : V.unop ≤ ⊤)).f0 a))
     naturality := by
       intro U V f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       exact (((D.toSheafData.withCurvature h hh hd).sheafOfRes_smul0L M₁ p le_top
         (leOfHom f.unop) _ x).trans (congrArg (fun u => (D.toSheafData.withCurvature h hh
           hd).smul0L M₁ p _ u _)
             (Subtype.ext (by exact D.D.res_comp _ _ (a : D.D.A ⊤))))).symm }⟩

/-- Z3.s: `actTw` on sections (rfl). -/
theorem actTw_app (a : ↥(D.D.𝒜 ⊤ 0)) (p : ℤ) (V : Opens X)
    (x : (D.toSheafData.withCurvature h hh hd).sheafOfSec M₁ p (le_top : V ≤ ⊤)) :
    ((actTw D hh hd M₁ a p).val.app (op V)).hom x =
      (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top ((D.D.res le_top).f0 a) x :=
  rfl

/-- **Z3.s** (blueprint-tw F′ (h)): the action of `a ∈ 𝒜⁰(X)` on `J_T(M₁)^p` by multiplication,
a morphism of twisted sheaves (`𝒜⁰` is commutative, so it commutes with the gluing maps
`u_αβ·`). -/
def actTwMod (a : ↥(D.D.𝒜 ⊤ 0)) (p : ℤ) :
    T.twTerm hh hd M₁ p ⟶ T.twTerm hh hd M₁ p where
  f α := (restr (ringOf D.toSheafData.O) (T.U α)).map (actTw D hh hd M₁ a p)
  comm := by
    intro α β W hα hβ x
    let u : ↥(D.toSheafData.D.𝒜 W 0) := (D.toSheafData.D.res (le_inf hα hβ)).f0 (T.u α β)
    let a' : ↥(D.toSheafData.D.𝒜 W 0) := (D.D.res (le_top : W ≤ ⊤)).f0 a
    have hc : u * a' = a' * u := Subtype.ext (GCDga.central (D.toSheafData.D.𝒜 W) u.2 _)
    change (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top u
        ((D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top a' x) =
      (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top a'
        ((D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top u x)
    exact (((D.toSheafData.withCurvature h hh hd).smul0L_mul M₁ p le_top u a' x).symm.trans
      (congrArg (fun w => (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top w x)
        hc)).trans ((D.toSheafData.withCurvature h hh hd).smul0L_mul M₁ p le_top a' u x)

/-- **Z3.s (F′ (h)).** [A, Lemma 7.2.8]. On compact Hausdorff `X`, every term of
`𝓗om^tw(J_T M₁, L)` is soft: `𝒜⁰(X)` acts on each `J_T(M₁)^p` by multiplication
(`actTwMod`), unitally, and by `0` over `V` when `a|V = 0` (`isSoft_twHomComplex_X`). -/
theorem isSoft_twHomComplex_twistedSheafOf_X [CompactSpace X] [T2Space X]
    (L : CochainComplex (TwMod D.toSheafData.O T.U T.ch) ℤ) (n : ℤ) :
    IsSoft ((twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) L T.iSup_eq).X n) := by
  let act : ∀ p : ℤ, (ringOf D.toSheafData.A0).obj.obj (op ⊤) →+
      ((T.twistedSheafOf hh hd M₁).X p ⟶ (T.twistedSheafOf hh hd M₁).X p) := fun p =>
    { toFun := fun a => actTwMod D T hh hd M₁ (a : ↥(D.D.𝒜 ⊤ 0)) p
      map_zero' := by
        refine TwMod.hom_ext fun α => ?_
        ext Y x
        change (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top
          ((D.D.res (le_top : Y.unop.left ≤ ⊤)).f0 0) x = 0
        rw [map_zero]
        exact (D.toSheafData.withCurvature h hh hd).smul0L_zero' M₁ p le_top x
      map_add' := fun (a b : ↥(D.D.𝒜 ⊤ 0)) => by
        refine TwMod.hom_ext fun α => ?_
        ext Y x
        change (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top
          ((D.D.res (le_top : Y.unop.left ≤ ⊤)).f0 (a + b)) x =
          (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top
            ((D.D.res (le_top : Y.unop.left ≤ ⊤)).f0 a) x +
          (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top
            ((D.D.res (le_top : Y.unop.left ≤ ⊤)).f0 b) x
        rw [map_add]
        exact (D.toSheafData.withCurvature h hh hd).smul0L_add' M₁ p le_top _ _ x }
  refine isSoft_twHomComplex_X T.ch_aba T.iSup_eq D.toSheafData.isFine0 act (fun p => ?_)
    (fun p ρ V hρ α W hW hα => ?_) L n
  · refine TwMod.hom_ext fun α => ?_
    ext Y x
    change (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top
      ((D.D.res (le_top : Y.unop.left ≤ ⊤)).f0 1) x = x
    rw [map_one]
    exact (D.toSheafData.withCurvature h hh hd).smul0L_one M₁ p le_top x
  · apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    change (D.toSheafData.withCurvature h hh hd).smul0L M₁ p le_top
      ((D.D.res (le_top : W ≤ ⊤)).f0 ρ) x = 0
    have e : (D.D.res (le_top : W ≤ ⊤)).f0 ρ =
        (D.D.res hW).f0 ((D.D.res (le_top : V ≤ ⊤)).f0 ρ) :=
      Subtype.ext (by exact (D.D.res_comp _ _ (show ↥(D.D.𝒜 ⊤ 0) from ρ).1).symm)
    rw [e, show (D.D.res (le_top : V ≤ ⊤)).f0 ρ = 0 from hρ, map_zero]
    exact (D.toSheafData.withCurvature h hh hd).smul0L_zero' M₁ p le_top x

end Soft

/-! ### Global sections (F′ (k)) -/

section Global

variable (M₁ M₂ : CohesiveModule (D.toSheafData.withCurvature h hh hd).𝒜X)

/-- **Z3.s (copy of C4 `quasiIso_Γ_Ψ_comp`).** If `Ψ^tw ≫ r_*` is a quasi-isomorphism and `I`
is bounded below, its global sections form a quasi-isomorphism (both sides soft and bounded
below, `quasiIso_globalSections_of_isSoft`). -/
theorem quasiIso_Γ_Ψtw_comp [CompactSpace X] [T2Space X]
    {I : CochainComplex (TwMod D.toSheafData.O T.U T.ch) ℤ} (r : T.twistedSheafOf hh hd M₂ ⟶ I)
    (a : ℤ) [I.IsStrictlyGE a]
    (hq : QuasiIso (T.Ψtw hh hd M₁ M₂ ≫
      twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r)) :
    QuasiIso (((globalSections (ringOf D.toSheafData.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (T.Ψtw hh hd M₁ M₂ ≫
        twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r)) := by
  obtain ⟨b, hb⟩ := exists_isStrictlyLE_twistedSheafOf D T hh hd M₁
  obtain ⟨c, hc⟩ := (D.toSheafData.withCurvature h hh hd).exists_isStrictlyGE_ℋ' M₁ M₂
  haveI := hb
  haveI := hc
  haveI : (twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) I T.iSup_eq).IsStrictlyGE
      (a - b) := twHomComplex_isStrictlyGE T.ch_aba T.iSup_eq _ _ a b
  haveI : ((D.toSheafData.withCurvature h hh hd).ℋ M₁ M₂).IsStrictlyGE (min c (a - b)) :=
    ((D.toSheafData.withCurvature h hh hd).ℋ M₁ M₂).isStrictlyGE_of_ge _ c (min_le_left _ _)
  haveI : (twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) I T.iSup_eq).IsStrictlyGE
      (min c (a - b)) :=
    (twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) I T.iSup_eq).isStrictlyGE_of_ge _
      (a - b) (min_le_right _ _)
  exact quasiIso_globalSections_of_isSoft (min c (a - b))
    (fun i => (D.toSheafData.withCurvature h hh hd).isSoft_homSh M₁ M₂ i)
    (fun i => isSoft_twHomComplex_twistedSheafOf_X D T hh hd M₁ I i) _

/-- A closed section of `ℋ^{h,0}(X)` is `F ∘ φ` for a closed `φ ∈ Z⁰` (C3, curved copy). -/
private theorem exists_Z0_homTop'
    (y : (D.toSheafData.withCurvature h hh hd).HomSec M₁ M₂ 0 (le_top : (⊤ : Opens X) ≤ ⊤))
    (hy : (D.toSheafData.withCurvature h hh hd).homδV M₁ M₂ 0 le_top y = 0) :
    ∃ φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive,
      (D.toSheafData.withCurvature h hh hd).homTop M₁ M₂ 0
        ((D.toSheafData.withCurvature h hh hd).toHom0 φ) = y := by
  obtain ⟨φ0, rfl⟩ := ((D.toSheafData.withCurvature h hh hd).homTop_bijective M₁ M₂ 0).2 y
  rw [(D.toSheafData.withCurvature h hh hd).homδV_homTop M₁ M₂ 0 φ0,
    ← map_zero ((D.toSheafData.withCurvature h hh hd).homTop M₁ M₂ (0 + 1))] at hy
  have h1 := ((D.toSheafData.withCurvature h hh hd).homTop_bijective M₁ M₂ (0 + 1)).1 hy
  have h2 : δ M₁.toQuasiCohesive M₂.toQuasiCohesive 0 φ0.1 = 0 := congrArg Subtype.val h1
  exact ⟨⟨φ0.1, Submodule.mem_inf.2 ⟨φ0.2, h2⟩⟩, rfl⟩

/-- Under `twHomTopEquiv`, `Γ(Ψ^tw ≫ r_*)` sends `F ∘ φ` to the cochain of `J_T(φ) ≫ r`. -/
private theorem equiv_Γ_Ψtw_comp {I : CochainComplex (TwMod D.toSheafData.O T.U T.ch) ℤ}
    (r : T.twistedSheafOf hh hd M₂ ⟶ I) (φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive) :
    twHomTopEquiv T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) I 0
        ((((((globalSections (ringOf D.toSheafData.O)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (T.Ψtw hh hd M₁ M₂ ≫
            twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r)).f 0)).hom
          ((D.toSheafData.withCurvature h hh hd).homTop M₁ M₂ 0
            ((D.toSheafData.withCurvature h hh hd).toHom0 φ))) =
      Cochain.ofHom (T.twMap hh hd φ ≫ r) := by
  change twHomTopEquiv T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) I 0
      ((((twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r).f 0).val.app
        (op ⊤)).hom (((T.Ψtw hh hd M₁ M₂).f 0).val.app (op ⊤)
          ((D.toSheafData.withCurvature h hh hd).homTop M₁ M₂ 0
            ((D.toSheafData.withCurvature h hh hd).toHom0 φ)))) = _
  rw [twHomTopEquiv_map₂, T.Ψtw_top hh hd M₁ M₂ φ, Cochain.ofHom_comp]

/-- **Z3.s (C4 step 5, surjectivity on `H⁰`, twisted).** If `Γ(Ψ^tw ≫ r_*)` is a
quasi-isomorphism, every chain map `g : J_T(M₁) ⟶ I` is homotopic to `J_T(φ) ≫ r` for a closed
degree-`0` map `φ : M₁ → M₂`. -/
theorem exists_homotopy_twMap_comp {I : CochainComplex (TwMod D.toSheafData.O T.U T.ch) ℤ}
    (r : T.twistedSheafOf hh hd M₂ ⟶ I)
    (hΓ : QuasiIso (((globalSections (ringOf D.toSheafData.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (T.Ψtw hh hd M₁ M₂ ≫
        twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r)))
    (g : T.twistedSheafOf hh hd M₁ ⟶ I) :
    ∃ φ : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive,
      Nonempty (Homotopy (T.twMap hh hd φ ≫ r) g) := by
  let E := twHomTopEquiv T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) I
  let z := (E 0).symm (Cochain.ofHom g)
  have hz : (((twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) I T.iSup_eq).d 0 1).val.app
      (op ⊤)).hom z = 0 := by
    apply (E 1).injective
    refine (twHomTopEquiv_d T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) I 0 z).trans ?_
    rw [(E 0).apply_symm_apply, δ_ofHom, map_zero]
  obtain ⟨y, w, hy, hyw⟩ := exists_cocycle_of_quasiIso
    (((globalSections (ringOf D.toSheafData.O)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (T.Ψtw hh hd M₁ M₂ ≫ twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r)) z hz
  obtain ⟨φ, hφ⟩ := exists_Z0_homTop' D hh hd M₁ M₂ y hy
  refine ⟨φ, ?_⟩
  have h0 := equiv_Γ_Ψtw_comp D T hh hd M₁ M₂ r φ
  rw [hφ] at h0
  have h1 : Cochain.ofHom (T.twMap hh hd φ ≫ r) =
      Cochain.ofHom g + CochainComplex.HomComplex.δ (-1) 0 (E (-1) w) := by
    refine h0.symm.trans ((congrArg (E 0) hyw).trans ?_)
    refine (E 0).map_add z _ |>.trans (congrArg₂ (· + ·) ((E 0).apply_symm_apply _) ?_)
    exact twHomTopEquiv_d T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) I (-1) w
  refine ⟨(Cochain.equivHomotopy _ _).symm ⟨E (-1) w, ?_⟩⟩
  rw [h1, add_comm]

/-- **Z3.s (C4 step 5, injectivity on `H⁰`, twisted).** If `Γ(Ψ^tw ≫ r_*)` is a
quasi-isomorphism and `J_T(φ) ≫ r`, `J_T(φ') ≫ r` are homotopic, then `φ` and `φ'` agree in
`H0(M₁, M₂)`. -/
theorem mk_eq_of_homotopy_twMap_comp {I : CochainComplex (TwMod D.toSheafData.O T.U T.ch) ℤ}
    (r : T.twistedSheafOf hh hd M₂ ⟶ I)
    (hΓ : QuasiIso (((globalSections (ringOf D.toSheafData.O)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (T.Ψtw hh hd M₁ M₂ ≫
        twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r)))
    (φ φ' : Z0 M₁.toQuasiCohesive M₂.toQuasiCohesive)
    (H : Homotopy (T.twMap hh hd φ ≫ r) (T.twMap hh hd φ' ≫ r)) :
    (Submodule.Quotient.mk φ : H0 M₁.toQuasiCohesive M₂.toQuasiCohesive) =
      Submodule.Quotient.mk φ' := by
  let E := twHomTopEquiv T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) I
  let Sh := D.toSheafData.withCurvature h hh hd
  let G := ((globalSections (ringOf D.toSheafData.O)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (T.Ψtw hh hd M₁ M₂ ≫
      twHomMap₂ T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) r)
  obtain ⟨c, hc⟩ := Cochain.equivHomotopy _ _ H
  let y := Sh.homTop M₁ M₂ 0 (Sh.toHom0 (φ - φ'))
  have hyd : Sh.homδV M₁ M₂ 0 le_top y = 0 := by
    have h0 : (⟨δ M₁.toQuasiCohesive M₂.toQuasiCohesive 0 (Sh.toHom0 (φ - φ')).1,
        δ_mem M₁.toQuasiCohesive M₂.toQuasiCohesive (Sh.toHom0 (φ - φ')).2⟩ :
        Hom M₁.toQuasiCohesive M₂.toQuasiCohesive (0 + 1)) = 0 :=
      Subtype.ext (Submodule.mem_inf.1 (φ - φ').2).2
    rw [Sh.homδV_homTop M₁ M₂ 0, h0, map_zero]
  have hyw : (G.f 0).hom y =
      ((((globalSections (ringOf D.toSheafData.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) I
          T.iSup_eq)).d (-1) 0).hom ((E (-1)).symm c) := by
    apply (E 0).injective
    have hy : y = Sh.homTop M₁ M₂ 0 (Sh.toHom0 φ) - Sh.homTop M₁ M₂ 0 (Sh.toHom0 φ') :=
      (congrArg (Sh.homTop M₁ M₂ 0) (rfl : Sh.toHom0 (φ - φ') = Sh.toHom0 φ - Sh.toHom0 φ')).trans
        (map_sub (Sh.homTop M₁ M₂ 0) (Sh.toHom0 φ) (Sh.toHom0 φ'))
    have hL : E 0 ((G.f 0).hom y) =
        Cochain.ofHom (T.twMap hh hd φ ≫ r) - Cochain.ofHom (T.twMap hh hd φ' ≫ r) := by
      refine (congrArg (fun t => E 0 ((G.f 0).hom t)) hy).trans ?_
      refine (congrArg (E 0) (map_sub (G.f 0).hom _ _)).trans ?_
      refine ((E 0).map_sub _ _).trans ?_
      rw [equiv_Γ_Ψtw_comp D T hh hd M₁ M₂ r φ, equiv_Γ_Ψtw_comp D T hh hd M₁ M₂ r φ']
    have hR' : E 0 (((((globalSections (ringOf D.toSheafData.O)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (twHomComplex T.ch_aba (T.twistedSheafOf hh hd M₁) I
          T.iSup_eq)).d (-1) 0).hom ((E (-1)).symm c)) = CochainComplex.HomComplex.δ (-1) 0 c := by
      have hd1 := twHomTopEquiv_d T.ch_aba T.iSup_eq (T.twistedSheafOf hh hd M₁) I (-1)
        ((E (-1)).symm c)
      have hs : (E (-1)) ((E (-1)).symm c) = c := (E (-1)).apply_symm_apply c
      exact hd1.trans (congrArg (CochainComplex.HomComplex.δ (-1) (-1 + 1)) hs)
    rw [hL, hR', hc, add_sub_cancel_right]
  obtain ⟨v, hv⟩ := exists_eq_d_of_quasiIso G y hyd _ hyw
  obtain ⟨ψ, hψ⟩ := (Sh.homTop_bijective M₁ M₂ (-1)).2 v
  have h1 : Sh.homTop M₁ M₂ 0 (Sh.toHom0 (φ - φ')) =
      Sh.homTop M₁ M₂ (-1 + 1) ⟨δ M₁.toQuasiCohesive M₂.toQuasiCohesive (-1) ψ.1,
        δ_mem M₁.toQuasiCohesive M₂.toQuasiCohesive ψ.2⟩ := by
    refine hv.trans ?_
    rw [← hψ]
    exact (Sh.homδV_homTop M₁ M₂ (-1) ψ)
  have h2 := (Sh.homTop_bijective M₁ M₂ 0).1 h1
  refine (Submodule.Quotient.eq _).2 ?_
  exact ⟨ψ.1, ψ.2, (congrArg Subtype.val h2).symm⟩

end Global

end Cohesive
