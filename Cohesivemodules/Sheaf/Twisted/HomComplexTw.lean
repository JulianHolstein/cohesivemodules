import Cohesivemodules.Sheaf.Twisted.HomTw
import Cohesivemodules.Sheaf.Twisted.GlueEquiv
import Cohesivemodules.Sheaf.HomSheafComplex
import Cohesivemodules.Sheaf.RestrictionBasic

set_option linter.style.header false

/-!
# Z3.r: the twisted Hom complex `𝓗om^tw(K, L)`

Blueprint item Z3.r (`blueprint/blueprint-tw.md` §3 F.2, F′ (d), (f)). For complexes `K`, `L` of
twisted sheaves (normalized `ȟ`) on a cover `U` of `X`:
* `twHomX K L n = ∏_{p + n = q} glue(homTw(Kᵖ, L^q))`, a sheaf of `R`-modules on `X` (`glue`,
  C.7 (b)); `twHomD` with Mathlib's sign, as S7's `homComplexD`;
* `glueRestrIso`: `glue(N)|U_α ≅ N_α` (C.7 (c)), natural in `N`;
* `twHomXRestrIso`: `(twHomX K L n)|U_α ≅ 𝓗om(K_α, L_α)ⁿ` (restriction preserves products), and
  under it `twHomD` is `homComplexD` (`twHomD_restr`). Hence `δ² = 0` (`twHomD_comp`): restricted
  to every `U_α` it is the untwisted `δ² = 0`, and morphisms of sheaves agree if they agree on a
  cover (`hom_ext_of_restr`);
* `twHomComplex hU K L` (`𝓗om^tw(K, L)`), functorial in both variables (`twHomMap₂`, `twHomMap₁`);
  `twHomRestrIso`: `𝓗om^tw(K, L)|U_α ≅ 𝓗om(K_α, L_α)` as complexes, natural in `K` and `L`
  (F′ (f) for `V = U_α`).

## Deviations
* As `homTw`: `ȟ` normalized. The cover hypothesis `⨆ U_α = ⊤` is used only for `δ² = 0`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Limits TopologicalSpace Opposite
open CochainComplex.HomComplex

variable {X : Type} [TopologicalSpace X] {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}}
  {ι : Type} {U : ι → Opens X}

section Glue

/-- **Z3.r.** `glue(N)|U_α ≅ N_α`: the `α`-component of `ofSheafGlueIso` (C.7 (c)). -/
def glueRestrIso (M : TwMod R U (fun _ _ _ => 1)) (α : ι) :
    (restr (ringOf R) (U α)).obj ((glue R U).obj M) ≅ M.M α :=
  (TwMod.comp R U (fun _ _ _ => 1) α).mapIso (ofSheafGlueIso M)

/-- Z3.r: naturality of `glueRestrIso`. -/
theorem glueRestrIso_hom_naturality {M M' : TwMod R U (fun _ _ _ => 1)} (f : M ⟶ M') (α : ι) :
    (restr (ringOf R) (U α)).map ((glue R U).map f) ≫ (glueRestrIso M' α).hom =
      (glueRestrIso M α).hom ≫ f.f α := by
  have h := congrArg (fun h => (TwMod.comp R U (fun _ _ _ => 1) α).map h)
    (ofSheafGlueIso_hom_naturality f)
  simp only [glueRestrIso, Functor.mapIso_hom] at h ⊢
  exact h

/-- **Z3.r.** Morphisms of sheaves of modules on `X` that agree on every member of an open cover
agree (sheaf separation). -/
theorem hom_ext_of_restr (hU : ⨆ α, U α = ⊤) {F G : Mod (ringOf R)} {f g : F ⟶ G}
    (h : ∀ α, (restr (ringOf R) (U α)).map f = (restr (ringOf R) (U α)).map g) : f = g := by
  refine eq_of_locally_eq f g fun V s x hx => ?_
  have hx' : x ∈ ⨆ α, U α := by rw [hU]; trivial
  obtain ⟨α, hα⟩ := Opens.mem_iSup.1 hx'
  refine ⟨V ⊓ U α, inf_le_left, ⟨hx, hα⟩, ?_⟩
  exact congrArg (fun φ => (φ.val.app
    (op (Over.mk (homOfLE (inf_le_right : V ⊓ U α ≤ U α))))).hom (mres F inf_le_left s)) (h α)

end Glue

variable {ch : ∀ α β γ, (R.obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ} (hch : ∀ α β, ch α β α = 1)

/-- Z3.r: the component complexes `K ↦ K_α` (termwise `comp α`). -/
abbrev compC (α : ι) :
    CochainComplex (TwMod R U ch) ℤ ⥤ CochainComplex (Mod ((ringOf R).over (U α))) ℤ :=
  (TwMod.comp R U ch α).mapHomologicalComplex (ComplexShape.up ℤ)

variable (K L : CochainComplex (TwMod R U ch) ℤ)

/-- **Z3.r (F′ (d)).** Degree `n` of `𝓗om^tw(K, L)`: `∏_{p + n = q} glue(homTw(Kᵖ, L^q))`,
indexed by Mathlib's `Triplet n` as S7's `homComplexX`. -/
abbrev twHomX (n : ℤ) : Mod (ringOf R) :=
  ∏ᶜ fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))

/-- **Z3.r (F′ (d)).** The differential of `𝓗om^tw(K, L)`, with Mathlib's sign as S7's
`homComplexD`: the component at `p + (n+1) = q` is
`φ_{p, p+n} ≫ d_L + (-1)^{n+1} d_K ≫ φ_{p+1, q}`. -/
def twHomD (n : ℤ) : twHomX hch K L n ⟶ twHomX hch K L (n + 1) :=
  Pi.lift fun T : Triplet (n + 1) ↦
    Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
        ⟨T.p, T.p + n, rfl⟩ ≫
        (glue R U).map (homTwPost hch (K.X T.p) (L.d (T.p + n) T.q)) +
      (n + 1).negOnePow •
        (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
            ⟨T.p + 1, T.q, by have := T.hpq; lia⟩ ≫
          (glue R U).map (homTwPre hch (K.d T.p (T.p + 1)) (L.X T.q)))

/-- **Z3.r (F′ (f)).** `(twHomX K L n)|U_α ≅ 𝓗om(K_α, L_α)ⁿ`: restriction preserves products
(right adjoint), and `glueRestrIso` on each factor. -/
def twHomXRestrIso (n : ℤ) (α : ι) :
    (restr (ringOf R) (U α)).obj (twHomX hch K L n) ≅
      homComplexX (isCommSheaf_over (U α)) ((compC α).obj K) ((compC α).obj L) n :=
  PreservesProduct.iso (restr (ringOf R) (U α)) _ ≪≫
    Pi.mapIso fun T : Triplet n ↦ glueRestrIso (homTw hch (K.X T.p) (L.X T.q)) α

/-- Z3.r: the factors of `twHomXRestrIso` are `glueRestrIso`. -/
theorem twHomXRestrIso_hom_π (n : ℤ) (α : ι) (T : Triplet n) :
    (twHomXRestrIso hch K L n α).hom ≫
        Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over (U α)) ((K.X T.p).M α)
          ((L.X T.q).M α)) T =
      (restr (ringOf R) (U α)).map
          (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T) ≫
        (glueRestrIso (homTw hch (K.X T.p) (L.X T.q)) α).hom := by
  rw [twHomXRestrIso, Iso.trans_hom]
  erw [Category.assoc]
  have key : (Pi.mapIso fun T : Triplet n ↦ glueRestrIso (homTw hch (K.X T.p) (L.X T.q)) α).hom ≫
      Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over (U α)) ((K.X T.p).M α)
        ((L.X T.q).M α)) T =
      Pi.π (fun T : Triplet n ↦ (restr (ringOf R) (U α)).obj ((glue R U).obj
        (homTw hch (K.X T.p) (L.X T.q)))) T ≫
        (glueRestrIso (homTw hch (K.X T.p) (L.X T.q)) α).hom :=
    Pi.map_π (fun T : Triplet n ↦ (glueRestrIso (homTw hch (K.X T.p) (L.X T.q)) α).hom) T
  refine (congrArg (fun z => (PreservesProduct.iso (restr (ringOf R) (U α))
    fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))).hom ≫ z) key).trans ?_
  rw [PreservesProduct.iso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (piComparison_comp_π (restr (ringOf R) (U α))
      (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T))

/-- `twHomXRestrIso_hom_π` with the target factor spelled through `compC` (defeq). -/
private theorem restrIso_π' (n : ℤ) (α : ι) (T : Triplet n) :
    (twHomXRestrIso hch K L n α).hom ≫
        Pi.π (fun T : Triplet n ↦ homSheaf (isCommSheaf_over (U α)) (((compC α).obj K).X T.p)
          (((compC α).obj L).X T.q)) T =
      (restr (ringOf R) (U α)).map
          (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T) ≫
        (glueRestrIso (homTw hch (K.X T.p) (L.X T.q)) α).hom :=
  twHomXRestrIso_hom_π hch K L n α T

/-- The `T`-component of `twHomD`. -/
private theorem twHomD_π (n : ℤ) (T : Triplet (n + 1)) :
    twHomD hch K L n ≫
        Pi.π (fun T : Triplet (n + 1) ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q))) T =
      Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
          ⟨T.p, T.p + n, rfl⟩ ≫
          (glue R U).map (homTwPost hch (K.X T.p) (L.d (T.p + n) T.q)) +
        (n + 1).negOnePow •
          (Pi.π (fun T : Triplet n ↦ (glue R U).obj (homTw hch (K.X T.p) (L.X T.q)))
              ⟨T.p + 1, T.q, by have := T.hpq; lia⟩ ≫
            (glue R U).map (homTwPre hch (K.d T.p (T.p + 1)) (L.X T.q))) :=
  Pi.lift_comp_π _ _

/-- **Z3.r.** Under `twHomXRestrIso`, the restriction of `twHomD` to `U_α` is the untwisted
differential `homComplexD` of `𝓗om(K_α, L_α)`. -/
theorem twHomD_restr (n : ℤ) (α : ι) :
    (restr (ringOf R) (U α)).map (twHomD hch K L n) ≫ (twHomXRestrIso hch K L (n + 1) α).hom =
      (twHomXRestrIso hch K L n α).hom ≫
        homComplexD (isCommSheaf_over (U α)) ((compC α).obj K) ((compC α).obj L) n := by
  apply Pi.hom_ext
  intro T
  rw [Category.assoc, Category.assoc, homComplexD_π, restrIso_π']
  conv_rhs => rw [Preadditive.comp_add, Linear.comp_units_smul, ← Category.assoc,
    ← Category.assoc, restrIso_π', restrIso_π']
  have h1 := glueRestrIso_hom_naturality (homTwPost hch (K.X T.p) (L.d (T.p + n) T.q)) α
  have h2 := glueRestrIso_hom_naturality (homTwPre hch (K.d T.p (T.p + 1)) (L.X T.q)) α
  erw [← Category.assoc (f := (restr (ringOf R) (U α)).map (twHomD hch K L n)), ← Functor.map_comp,
    twHomD_π]
  rw [Functor.map_add, Functor.map_units_smul]
  erw [Preadditive.add_comp, Linear.units_smul_comp]
  rw [Functor.map_comp, Functor.map_comp]
  congr 1

/-- **Z3.r.** `δ² = 0` on `𝓗om^tw(K, L)`: on every `U_α` it is the untwisted `δ² = 0`
(`twHomD_restr`, `homComplexD_comp`), and `U` covers `X` (`hom_ext_of_restr`). -/
theorem twHomD_comp (hU : ⨆ α, U α = ⊤) (n : ℤ) :
    twHomD hch K L n ≫ twHomD hch K L (n + 1) = 0 := by
  refine hom_ext_of_restr hU fun α => ?_
  rw [Functor.map_zero, Functor.map_comp]
  rw [← cancel_mono (twHomXRestrIso hch K L (n + 1 + 1) α).hom, zero_comp, Category.assoc,
    twHomD_restr, ← Category.assoc, twHomD_restr, Category.assoc, homComplexD_comp, comp_zero]

/-- **Z3.r (F′ (d)). The twisted Hom complex** `𝓗om^tw(K, L)` of two complexes of twisted
sheaves (normalized `ȟ`, `U` a cover of `X`): a complex of sheaves of `R`-modules on `X`, degree
`n` the product of the glued Hom sheaves `glue(homTw(Kᵖ, L^q))`, `p + n = q`, Mathlib's sign. -/
def twHomComplex (hU : ⨆ α, U α = ⊤) : CochainComplex (Mod (ringOf R)) ℤ :=
  CochainComplex.of (twHomX hch K L) (twHomD hch K L) (twHomD_comp hch K L hU)

/-- Z3.r: the differential of `twHomComplex` in degree `n` is `twHomD` (rfl up to `of_d`). -/
theorem twHomComplex_d (hU : ⨆ α, U α = ⊤) (n : ℤ) :
    (twHomComplex hch K L hU).d n (n + 1) = twHomD hch K L n :=
  CochainComplex.of_d (twHomX hch K L) (twHomD hch K L) n

variable {K L}

/-- `twHomMap₂` commutes with the differentials. -/
private theorem twHomMap₂_comm (K : CochainComplex (TwMod R U ch) ℤ)
    {L L' : CochainComplex (TwMod R U ch) ℤ} (g : L ⟶ L') (n : ℤ) :
    Limits.Pi.map (fun T : Triplet n ↦ (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q))) ≫
        twHomD hch K L' n =
      twHomD hch K L n ≫ Limits.Pi.map
        (fun T : Triplet (n + 1) ↦ (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q))) := by
  apply Pi.hom_ext
  intro T
  rw [Category.assoc, Category.assoc, Pi.map_π, twHomD_π, ← Category.assoc (twHomD hch K L n),
    twHomD_π]
  rw [Preadditive.comp_add, Linear.comp_units_smul, Preadditive.add_comp,
    Linear.units_smul_comp]
  have e1 := Pi.map_π (fun T : Triplet n ↦ (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q)))
    ⟨T.p, T.p + n, rfl⟩
  have e2 := Pi.map_π (fun T : Triplet n ↦ (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q)))
    ⟨T.p + 1, T.q, by have := T.hpq; lia⟩
  have h3 : (glue R U).map (homTwPost hch (K.X T.p) (g.f (T.p + n))) ≫
      (glue R U).map (homTwPost hch (K.X T.p) (L'.d (T.p + n) T.q)) =
      (glue R U).map (homTwPost hch (K.X T.p) (L.d (T.p + n) T.q)) ≫
      (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← homTwPost_comp, ← homTwPost_comp, g.comm]
  have h4 : (glue R U).map (homTwPost hch (K.X (T.p + 1)) (g.f T.q)) ≫
      (glue R U).map (homTwPre hch (K.d T.p (T.p + 1)) (L'.X T.q)) =
      (glue R U).map (homTwPre hch (K.d T.p (T.p + 1)) (L.X T.q)) ≫
      (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, homTwPre_homTwPost]
  simp only [← Category.assoc, e1, e2]
  simp only [Category.assoc, h3, h4]

/-- **Z3.r.** Functoriality in the target: `g : L ⟶ L'` induces `𝓗om^tw(K, L) ⟶ 𝓗om^tw(K, L')`
(post-composition in each factor). -/
def twHomMap₂ (hU : ⨆ α, U α = ⊤) (K : CochainComplex (TwMod R U ch) ℤ)
    {L L' : CochainComplex (TwMod R U ch) ℤ} (g : L ⟶ L') :
    twHomComplex hch K L hU ⟶ twHomComplex hch K L' hU where
  f n := Limits.Pi.map fun T : Triplet n ↦ (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q))
  comm' := fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    rw [twHomComplex_d, twHomComplex_d]
    exact twHomMap₂_comm hch K g i

/-- `twHomMap₁` commutes with the differentials. -/
private theorem twHomMap₁_comm {K K' : CochainComplex (TwMod R U ch) ℤ} (f : K' ⟶ K)
    (L : CochainComplex (TwMod R U ch) ℤ) (n : ℤ) :
    Limits.Pi.map (fun T : Triplet n ↦ (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q))) ≫
        twHomD hch K' L n =
      twHomD hch K L n ≫ Limits.Pi.map
        (fun T : Triplet (n + 1) ↦ (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q))) := by
  apply Pi.hom_ext
  intro T
  rw [Category.assoc, Category.assoc, Pi.map_π, twHomD_π, ← Category.assoc (twHomD hch K L n),
    twHomD_π]
  rw [Preadditive.comp_add, Linear.comp_units_smul, Preadditive.add_comp,
    Linear.units_smul_comp]
  have e1 := Pi.map_π (fun T : Triplet n ↦ (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q)))
    ⟨T.p, T.p + n, rfl⟩
  have e2 := Pi.map_π (fun T : Triplet n ↦ (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q)))
    ⟨T.p + 1, T.q, by have := T.hpq; lia⟩
  have h3 : (glue R U).map (homTwPre hch (f.f T.p) (L.X (T.p + n))) ≫
      (glue R U).map (homTwPost hch (K'.X T.p) (L.d (T.p + n) T.q)) =
      (glue R U).map (homTwPost hch (K.X T.p) (L.d (T.p + n) T.q)) ≫
      (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, homTwPre_homTwPost]
  have h4 : (glue R U).map (homTwPre hch (f.f (T.p + 1)) (L.X T.q)) ≫
      (glue R U).map (homTwPre hch (K'.d T.p (T.p + 1)) (L.X T.q)) =
      (glue R U).map (homTwPre hch (K.d T.p (T.p + 1)) (L.X T.q)) ≫
      (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, homTwPre_comp, homTwPre_comp, f.comm]
  simp only [← Category.assoc, e1, e2]
  simp only [Category.assoc, h3, h4]

/-- **Z3.r.** Functoriality in the source: `f : K' ⟶ K` induces `𝓗om^tw(K, L) ⟶ 𝓗om^tw(K', L)`
(pre-composition in each factor). -/
def twHomMap₁ (hU : ⨆ α, U α = ⊤) {K K' : CochainComplex (TwMod R U ch) ℤ} (f : K' ⟶ K)
    (L : CochainComplex (TwMod R U ch) ℤ) :
    twHomComplex hch K L hU ⟶ twHomComplex hch K' L hU where
  f n := Limits.Pi.map fun T : Triplet n ↦ (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q))
  comm' := fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    rw [twHomComplex_d, twHomComplex_d]
    exact twHomMap₁_comm hch f L i

variable (K L)

/-- **Z3.r (F′ (f), `V = U_α`).** `𝓗om^tw(K, L)|U_α ≅ 𝓗om(K_α, L_α)` as complexes of sheaves on
`Over U_α` (termwise `twHomXRestrIso`, compatible with the differentials by `twHomD_restr`). -/
def twHomRestrIso (hU : ⨆ α, U α = ⊤) (α : ι) :
    ((restr (ringOf R) (U α)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (twHomComplex hch K L hU) ≅
      homSheafComplex (isCommSheaf_over (U α)) ((compC α).obj K) ((compC α).obj L) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => twHomXRestrIso hch K L n α) (by
    rintro i j rfl
    rw [homComplex_d]
    show _ = (restr (ringOf R) (U α)).map ((twHomComplex hch K L hU).d i (i + 1)) ≫ _
    rw [twHomComplex_d]
    exact (twHomD_restr hch K L i α).symm)

/-- Z3.r: the components of `twHomRestrIso` are `twHomXRestrIso` (rfl). -/
theorem twHomRestrIso_hom_f (hU : ⨆ α, U α = ⊤) (α : ι) (n : ℤ) :
    (twHomRestrIso hch K L hU α).hom.f n = (twHomXRestrIso hch K L n α).hom := rfl

variable {K L}

/-- **Z3.r.** `twHomRestrIso` is natural in the target (`twHomMap₂` ↔ `homComplexMap₂`). -/
theorem twHomRestrIso_naturality₂ (hU : ⨆ α, U α = ⊤) (K : CochainComplex (TwMod R U ch) ℤ)
    {L L' : CochainComplex (TwMod R U ch) ℤ} (g : L ⟶ L') (α : ι) :
    ((restr (ringOf R) (U α)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (twHomMap₂ hch hU K g) ≫ (twHomRestrIso hch K L' hU α).hom =
      (twHomRestrIso hch K L hU α).hom ≫
        homComplexMap₂ (isCommSheaf_over (U α)) ((compC α).obj K) ((compC α).map g) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine Pi.hom_ext _ _ fun T => ?_
  have h1 := glueRestrIso_hom_naturality (homTwPost hch (K.X T.p) (g.f T.q)) α
  have e1 := Pi.map_π (fun T : Triplet n ↦ (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q))) T
  have e2 := Pi.map_π (fun T : Triplet n ↦ homPost (isCommSheaf_over (U α))
    (((compC α).obj K).X T.p) (((compC α).map g).f T.q)) T
  show (restr (ringOf R) (U α)).map (Limits.Pi.map fun T : Triplet n ↦
      (glue R U).map (homTwPost hch (K.X T.p) (g.f T.q))) ≫
      (twHomXRestrIso hch K L' n α).hom ≫ _ = (twHomXRestrIso hch K L n α).hom ≫
      Limits.Pi.map (fun T : Triplet n ↦ homPost (isCommSheaf_over (U α))
        (((compC α).obj K).X T.p) (((compC α).map g).f T.q)) ≫ _
  rw [e2]
  conv_lhs => rw [restrIso_π']
  conv_rhs => rw [← Category.assoc, restrIso_π']
  erw [← Category.assoc, ← Functor.map_comp, e1, Functor.map_comp, Category.assoc, h1]

/-- **Z3.r.** `twHomRestrIso` is natural in the source (`twHomMap₁` ↔ `homComplexMap₁`). -/
theorem twHomRestrIso_naturality₁ (hU : ⨆ α, U α = ⊤) {K K' : CochainComplex (TwMod R U ch) ℤ}
    (f : K' ⟶ K) (L : CochainComplex (TwMod R U ch) ℤ) (α : ι) :
    ((restr (ringOf R) (U α)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (twHomMap₁ hch hU f L) ≫ (twHomRestrIso hch K' L hU α).hom =
      (twHomRestrIso hch K L hU α).hom ≫
        homComplexMap₁ (isCommSheaf_over (U α)) ((compC α).map f) ((compC α).obj L) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine Pi.hom_ext _ _ fun T => ?_
  have h1 := glueRestrIso_hom_naturality (homTwPre hch (f.f T.p) (L.X T.q)) α
  have e1 := Pi.map_π (fun T : Triplet n ↦ (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q))) T
  have e2 := Pi.map_π (fun T : Triplet n ↦ homPre (isCommSheaf_over (U α))
    (((compC α).map f).f T.p) (((compC α).obj L).X T.q)) T
  show (restr (ringOf R) (U α)).map (Limits.Pi.map fun T : Triplet n ↦
      (glue R U).map (homTwPre hch (f.f T.p) (L.X T.q))) ≫
      (twHomXRestrIso hch K' L n α).hom ≫ _ = (twHomXRestrIso hch K L n α).hom ≫
      Limits.Pi.map (fun T : Triplet n ↦ homPre (isCommSheaf_over (U α))
        (((compC α).map f).f T.p) (((compC α).obj L).X T.q)) ≫ _
  rw [e2]
  conv_lhs => rw [restrIso_π']
  conv_rhs => rw [← Category.assoc, restrIso_π']
  erw [← Category.assoc, ← Functor.map_comp, e1, Functor.map_comp, Category.assoc, h1]

end Cohesive
