import Cohesivemodules.Comparison.ModelDef
import Cohesivemodules.Comparison.ModelCrit
import Cohesivemodules.Algebra.TotalQuasiIso
import Cohesivemodules.Algebra.BaseChangeX0

set_option linter.style.header false

/-!
# C7.f: the quasi-isomorphism criterion for `Ξ_e`

Blueprint item C7.f (§4, v1.11). `G0 M` is the form-degree-`0` part of `α_U(M)`: the complex of
sheaves of `𝒜⁰|U`-modules `V ↦ 𝒜⁰(V) ⊗_{𝒜⁰(U)} Q^p` (the generators of `M|V`, A9) with
differential `𝕏⁰` (the complex `complex0` of `M|V`, A11). `gr0Ξ e : G0 M → F` is the
`(0,0)`-component of `Ξ_e` (A12 `comp0L`). The criterion `quasiIso_Ξ`: if `gr0Ξ e` is a
quasi-isomorphism, so is `Ξ_e`. Proof plan (blueprint C7.f): filter `α_U(M)` and `T` by form
degree (A6 `filTot` sectionwise), short exact sequences sectionwise (A12 `filSC_shortExact`), A7
in sheaves; `gr^b Ξ_e` is a retract of a finite power of `gr⁰ Ξ_e = gr0Ξ e` (the splitting of
`𝒜^b` over `𝒜⁰`, S4.b).

## Deviations
* None beyond those of `ModelDef.lean`.

Part 1 of 2 of the original `Comparison/ModelFil.lean`, split for size; continued in
`Comparison/ModelFil.lean`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum

variable {X : Type} [TopologicalSpace X]

section BCGenRes

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]
  (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ) (f' : DgaHom 𝒜 𝒞) (hgf : ∀ a, g (f a) = f' a)
  (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- `famMap` of `bcGenRes` maps `ι e` to `ι' e`. -/
private theorem famMap_bcGenRes_bcι (e : DirectSum ℤ fun p => Q p) :
    famMap (fun p => bcGenRes g f f' hgf Q p) (bcι f Q e) = bcι f' Q e := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p q =>
    rw [show DirectSum.of Q p q = DirectSum.lof (𝒜 0) ℤ Q p q from rfl, bcι_lof, bcι_lof]
    change famMap _ (DirectSum.of _ p _) = DirectSum.of _ p _
    rw [famMap_of, bcGenRes_tmul]
    exact congrArg (fun β => DirectSum.of (BCGen f' Q) p (BCGen.tmul f' Q β q))
      (Subtype.ext (by exact g.map_one'))
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `totMapAlong` along `bcGenRes` is `bcTotRes`. -/
theorem totMapAlong_bcGenRes_eq (y : Tot ℬ (BCGen f Q)) :
    totMapAlong g (fun p => bcGenRes g f f' hgf Q p)
      (fun p r x => bcGenRes_smul g f f' hgf Q p r x) y = bcTotRes g f f' hgf Q y := by
  induction y using Tot.induction_on with
  | ht b e =>
    rw [totMapAlong_tmul, bcTotRes_tmul]
    congr 1
    induction e using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of p z => rw [famMap_of, DirectSum.map_of]
    | add x y hx hy => simp only [map_add, hx, hy]
  | hadd x y hx hy => simp only [map_add, hx, hy]

/-- `totMapAlong` along `bcGenRes` commutes with `F`. -/
private theorem tmA_bcF (y : Tot 𝒜 Q) :
    totMapAlong g (fun p => bcGenRes g f f' hgf Q p)
      (fun p r x => bcGenRes_smul g f f' hgf Q p r x) (bcF f Q y) = bcF f' Q y := by
  induction y using Tot.induction_on with
  | ht a e =>
    rw [bcF_tmul, bcF_tmul, totMapAlong_tmul, hgf, famMap_bcGenRes_bcι g f f' hgf]
  | hadd x y hx hy => simp only [map_add, hx, hy]

/-- `totMapAlong` along `bcGenRes` commutes with `θ'`. -/
theorem tmA_bcθ (M : QuasiCohesive 𝒜) (e : DirectSum ℤ fun p => BCGen f M.Q p) :
    totMapAlong g (fun p => bcGenRes g f f' hgf M.Q p)
      (fun p r x => bcGenRes_smul g f f' hgf M.Q p r x) (bcθ f M e) =
      bcθ f' M (famMap (fun p => bcGenRes g f f' hgf M.Q p) e) := by
  induction e using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of p z =>
    induction z using BCGen.induction_on with
    | ht β q =>
      rw [bcθ_of, bcθp_tmul, map_add, totMapAlong_tmul, totMapAlong_smul, tmA_bcF g f f' hgf,
        famMap_of, bcGenRes_tmul, bcθ_of, bcθp_tmul, g.map_d]
      have hmap : famMap (fun p => bcGenRes g f f' hgf M.Q p)
          (DirectSum.of (BCGen f M.Q) p (BCGen.tmul f M.Q 1 q)) =
          DirectSum.of (BCGen f' M.Q) p (BCGen.tmul f' M.Q 1 q) := by
        rw [famMap_of, bcGenRes_tmul]
        exact congrArg (fun β => DirectSum.of (BCGen f' M.Q) p (BCGen.tmul f' M.Q β q))
          (Subtype.ext (by exact g.map_one'))
      change Tot.tmul _ _ _ (famMap _ (DirectSum.of _ p _)) + _ = _
      rw [hmap]
      rfl
    | hadd x y hx hy =>
      rw [(DirectSum.of (BCGen f M.Q) p).map_add]
      simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end BCGenRes

section G0Coord

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]
  (f : DgaHom 𝒜 ℬ) {Q : ℤ → Type} [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

/-- The bi-additive map `(β, q) ↦ β · f(φ q)`. -/
private def g0CoordAux (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) : f.B0 →+ Q p →+ ℬ 0 :=
  AddMonoidHom.mk'
    (fun β => AddMonoidHom.mk' (fun q => (show ℬ 0 from β) * f.f0 (φ q))
      (fun q q' => by rw [map_add, map_add, mul_add]))
    (fun β β' => AddMonoidHom.ext fun q => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      exact add_mul (show ℬ 0 from β) (show ℬ 0 from β') _)

/-- `g0CoordAux` is `𝒜⁰`-balanced. -/
private theorem g0CoordAux_balanced (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) (r : 𝒜 0) (β : f.B0)
    (q : Q p) : g0CoordAux f p φ (r • β) q = g0CoordAux f p φ β (r • q) := by
  show (show ℬ 0 from (r • β : f.B0)) * f.f0 (φ q) = (show ℬ 0 from β) * f.f0 (φ (r • q))
  rw [show (show ℬ 0 from (r • β : f.B0)) = f.f0 r * (show ℬ 0 from β) from rfl, map_smul,
    smul_eq_mul, map_mul]
  ring

/-- The coordinate `β ⊗ q ↦ β · f(φ q)` on the generators `B⁰ ⊗_{A⁰} Q^p`. -/
private def g0Coord (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) : BCGen f Q p →+ ℬ 0 :=
  TensorProduct.liftAddHom (R := 𝒜 0) (g0CoordAux f p φ) (g0CoordAux_balanced f p φ)

/-- `g0Coord` on pure tensors (rfl). -/
private theorem g0Coord_tmul (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) (β : ℬ 0) (q : Q p) :
    g0Coord f p φ (BCGen.tmul f Q β q) = β * f.f0 (φ q) := rfl

/-- `g0Coord` is natural for `bcGenRes`. -/
private theorem g0Coord_bcGenRes (g : DgaHom ℬ 𝒞) (f' : DgaHom 𝒜 𝒞)
    (hgf : ∀ a, g (f a) = f' a) (p : ℤ) (φ : Q p →ₗ[𝒜 0] 𝒜 0) (z : BCGen f Q p) :
    g0Coord f' p φ (bcGenRes g f f' hgf Q p z) = g.f0 (g0Coord f p φ z) := by
  induction z using BCGen.induction_on with
  | ht β q =>
    rw [bcGenRes_tmul, g0Coord_tmul, g0Coord_tmul, map_mul]
    exact congrArg (g.f0 β * ·) (Subtype.ext (hgf _)).symm
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The generators `(b_j) ↦ ∑ b_j ⊗ x_j`. -/
private def g0Rec (p : ℤ) {m : ℕ} (x : Fin m → Q p) (b : Fin m → ℬ 0) : BCGen f Q p :=
  ∑ j, BCGen.tmul f Q (b j) (x j)

/-- `g0Rec` is additive in the coordinates. -/
private theorem g0Rec_add (p : ℤ) {m : ℕ} (x : Fin m → Q p) (b b' : Fin m → ℬ 0) :
    g0Rec f p x (b + b') = g0Rec f p x b + g0Rec f p x b' := by
  simp only [g0Rec, Pi.add_apply, BCGen.add_tmul, Finset.sum_add_distrib]

/-- `g0Rec` is natural for `bcGenRes`. -/
private theorem bcGenRes_g0Rec (g : DgaHom ℬ 𝒞) (f' : DgaHom 𝒜 𝒞)
    (hgf : ∀ a, g (f a) = f' a) (p : ℤ) {m : ℕ} (x : Fin m → Q p) (b : Fin m → ℬ 0) :
    bcGenRes g f f' hgf Q p (g0Rec f p x b) = g0Rec f' p x (fun j => g.f0 (b j)) := by
  simp only [g0Rec, map_sum, bcGenRes_tmul]

/-- `∑ φ_j(q) x_j = q` gives `g0Rec (coordinates of z) = z`. -/
private theorem g0Rec_g0Coord (p : ℤ) {m : ℕ} (x : Fin m → Q p) (φ : Fin m → (Q p →ₗ[𝒜 0] 𝒜 0))
    (hφ : ∀ q, ∑ j, φ j q • x j = q) (z : BCGen f Q p) :
    g0Rec f p x (fun j => g0Coord f p (φ j) z) = z := by
  induction z using BCGen.induction_on with
  | ht β q =>
    have h1 : ∀ j, BCGen.tmul f Q (β * f.f0 (φ j q)) (x j) =
        BCGen.tmul f Q β (φ j q • x j) := fun j => by
      rw [BCGen.tmul_eq_smul β (φ j q • x j), BCGen.tmul_smul0, smul_smul,
        BCGen.tmul_eq_smul (β * f.f0 _)]
    have h2 : BCGen.tmul f Q β (∑ j, φ j q • x j) = ∑ j, BCGen.tmul f Q β (φ j q • x j) := by
      rw [BCGen.tmul_def, TensorProduct.tmul_sum]
      rfl
    simp only [g0Coord_tmul, g0Rec]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), ← h2, hφ]
  | hadd x y hx hy =>
    have : (fun j => g0Coord f p (φ j) (x + y)) =
        (fun j => g0Coord f p (φ j) x) + (fun j => g0Coord f p (φ j) y) := by
      funext j
      exact map_add _ _ _
    rw [this, g0Rec_add, hx, hy]

end G0Coord

namespace PreResolvingData

variable (P : PreResolvingData X) (U : Opens X) (M : CohesiveModule (P.D.𝒜 U))

/-! ## The form-degree-`0` part `G0 M` of `α_U(M)` -/

/-- The generators of `M|V`: `𝒜⁰(V) ⊗_{𝒜⁰(U)} Q^p` (A9). -/
abbrev G0Sec (p : ℤ) (V : (Over U)ᵒᵖ) : Type :=
  BCGen (P.D.res (leOfHom V.unop.hom)) M.Q p

/-- **C7.f.** Restriction of generators along `f : V ⟶ W` (`bcGenRes`). -/
def g0Res (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) :
    P.G0Sec U M p V →ₛₗ[(P.D.res (leOfHom f.unop.left)).f0] P.G0Sec U M p W where
  toFun := bcGenRes (P.D.res (leOfHom f.unop.left)) (P.D.res (leOfHom V.unop.hom))
    (P.D.res (leOfHom W.unop.hom)) (P.D.res_comp _ _) M.Q p
  map_add' := map_add _
  map_smul' γ x := bcGenRes_smul _ _ _ _ M.Q p γ x

/-- C7.f: `g0Res` on pure tensors (rfl). -/
theorem g0Res_tmul (p : ℤ) {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (β : ↥(P.D.𝒜 V.unop.left 0)) (q : M.Q p) :
    P.g0Res U M p f (BCGen.tmul (P.D.res (leOfHom V.unop.hom)) M.Q β q) =
      BCGen.tmul (P.D.res (leOfHom W.unop.hom)) M.Q ((P.D.res (leOfHom f.unop.left)).f0 β) q :=
  rfl

/-- `g0Res` along the identity is the identity. -/
theorem g0Res_id (p : ℤ) (V : (Over U)ᵒᵖ) (x : P.G0Sec U M p V) :
    P.g0Res U M p (𝟙 V) x = x := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [g0Res_tmul]
    exact congrArg (BCGen.tmul _ M.Q · q) (Subtype.ext (P.D.res_id _ _))
  | hadd x y hx hy => rw [map_add, hx, hy]

/-- `g0Res` is functorial. -/
theorem g0Res_comp (p : ℤ) {V W Y : (Over U)ᵒᵖ} (f : V ⟶ W) (g : W ⟶ Y) (x : P.G0Sec U M p V) :
    P.g0Res U M p (f ≫ g) x = P.g0Res U M p g (P.g0Res U M p f x) := by
  induction x using BCGen.induction_on with
  | ht β q =>
    rw [g0Res_tmul, g0Res_tmul, g0Res_tmul]
    exact congrArg (BCGen.tmul _ M.Q · q) (Subtype.ext (P.D.res_comp _ _ _).symm)
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **C7.f.** `G0^p` as a presheaf of `𝒜⁰|U`-modules on the over-site of `U`. -/
def G0Pre (p : ℤ) : PresheafOfModules.{0} ((ringOf P.A0).over U).obj where
  obj V := ModuleCat.of ↥(P.D.𝒜 V.unop.left 0) (P.G0Sec U M p V)
  map {V W} f := ModuleCat.semilinearMapAddEquiv (((ringOf P.A0).over U).obj.map f).hom
      (ModuleCat.of ↥(P.D.𝒜 V.unop.left 0) (P.G0Sec U M p V))
      (ModuleCat.of ↥(P.D.𝒜 W.unop.left 0) (P.G0Sec U M p W))
      (P.g0Res U M p f)
  map_id V := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    exact P.g0Res_id U M p V x
  map_comp f g := by
    apply ModuleCat.hom_ext
    refine DFunLike.ext _ _ fun x => ?_
    exact P.g0Res_comp U M p f g x

/-- Helper: the type-valued presheaf `V ↦ G0^p(V)` on the over-site of `U`. -/
private def G0Ty (p : ℤ) : (Over U)ᵒᵖ ⥤ Type where
  obj V := P.G0Sec U M p V
  map {V W} f := ↾(fun x => P.g0Res U M p f x)
  map_id V := by
    ext x
    exact P.g0Res_id U M p V x
  map_comp f g := by
    ext x
    exact P.g0Res_comp U M p f g x

/-- Helper: the presheaf `V ↦ 𝒜⁰(V)^m` of types on `X`. -/
private def g0Ty (m : ℕ) : (Opens X)ᵒᵖ ⥤ Type where
  obj V := Fin m → ↥(P.D.𝒜 V.unop 0)
  map {V W} f := ↾(fun y i => ⟨P.D.res (leOfHom f.unop) (y i), (P.D.res _).map_mem (y i).2⟩)
  map_id V := by
    ext y i
    exact P.D.res_id _ _
  map_comp f g := by
    ext y i
    exact (P.D.res_comp _ _ _).symm

/-- Helper: `g0Ty m` is a sheaf of types (`P.glue` and `P.degree_local`). -/
private theorem isSheaf_g0Ty (m : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (P.g0Ty m) := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types (X := TopCat.of X)
    (P.g0Ty m)).2 ?_
  intro ι U sf hsf
  have h : ∀ i j a, P.D.res (inf_le_left : U i ⊓ U j ≤ U i) (sf i a : P.D.A (U i)) =
      P.D.res (inf_le_right : U i ⊓ U j ≤ U j) (sf j a : P.D.A (U j)) :=
    fun i j a => congrArg Subtype.val (congrFun (hsf i j) a)
  have hmem : ∀ a, ∃! b : ↥(P.D.𝒜 (⨆ i, U i) 0),
      ∀ i, P.D.res (le_iSup U i) (b : P.D.A (⨆ i, U i)) = (sf i a : P.D.A (U i)) := by
    intro a
    obtain ⟨b, hb, hb'⟩ := P.glue U (fun i => (sf i a : P.D.A (U i))) (fun i j => h i j a)
    have hm : b ∈ P.D.𝒜 (⨆ i, U i) 0 := by
      refine P.degree_local 0 b fun x hx => ?_
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
      exact ⟨U i, le_iSup U i, hi, by rw [hb i]; exact (sf i a).2⟩
    exact ⟨⟨b, hm⟩, hb, fun b'' hb'' => Subtype.ext (hb' _ hb'')⟩
  choose t ht hu using hmem
  exact ⟨t, fun i => funext fun a => Subtype.ext (ht a i),
    fun t' ht' => funext fun a => hu a (t' a) fun i =>
      congrArg Subtype.val (congrFun (ht' i) a)⟩


/-- Helper: `Q^p` has a finite family of generators with dual coordinates. -/
private theorem exists_gens (p : ℤ) : ∃ (m : ℕ) (x : Fin m → M.Q p)
    (φ : Fin m → (M.Q p →ₗ[P.D.𝒜 U 0] P.D.𝒜 U 0)), ∀ q, ∑ j, φ j q • x j = q := by
  have := M.finite p
  have := M.projective p
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (P.D.𝒜 U 0) (M.Q p)
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

/-- **C7.f.** `G0^p` is a sheaf (`Q^p` is a summand of a finite free `𝒜⁰(U)`-module, so `G0^p` is
a retract of a finite power of `𝒜⁰|U`). -/
theorem isSheaf_G0Pre (p : ℤ) :
    Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U) (P.G0Pre U M p).presheaf := by
  obtain ⟨m, x, φ, hφ⟩ := P.exists_gens U M p
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat), isSheaf_iff_isSheaf_of_type]
  have hG : Presieve.IsSheaf ((Opens.grothendieckTopology X).over U)
      ((Over.forget U).op ⋙ P.g0Ty m) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((Over.forget U).op_comp_isSheaf_of_isSheaf _ _ _ (P.isSheaf_g0Ty m))
  intro Y S hS
  refine isSheafFor_of_retract (F := P.G0Ty U M p) (G := (Over.forget U).op ⋙ P.g0Ty m)
    { app := fun V => ↾(fun z j =>
        (g0Coord (P.D.res (leOfHom V.unop.hom)) p (φ j) z : ↥(P.D.𝒜 V.unop.left 0)))
      naturality := fun V W f => by
        ext z
        funext j
        exact Subtype.ext (congrArg Subtype.val
          (g0Coord_bcGenRes (P.D.res (leOfHom V.unop.hom)) (P.D.res (leOfHom f.unop.left))
            (P.D.res (leOfHom W.unop.hom)) (P.D.res_comp _ _) p (φ j) z)) }
    { app := fun V => ↾(fun (b : Fin m → ↥(P.D.𝒜 V.unop.left 0)) =>
        (g0Rec (P.D.res (leOfHom V.unop.hom)) p x b : P.G0Sec U M p V))
      naturality := fun V W f => by
        ext b
        exact (bcGenRes_g0Rec (P.D.res (leOfHom V.unop.hom)) (P.D.res (leOfHom f.unop.left))
          (P.D.res (leOfHom W.unop.hom)) (P.D.res_comp _ _) p x b).symm }
    ?_ S (hG S hS)
  ext V z
  exact g0Rec_g0Coord (P.D.res (leOfHom V.unop.hom)) p x φ hφ z

/-- **C7.f.** The sheaf `G0^p` of `𝒜⁰|U`-modules. -/
def G0Sh (p : ℤ) : Mod ((ringOf P.A0).over U) := ⟨P.G0Pre U M p, P.isSheaf_G0Pre U M p⟩

end PreResolvingData
end Cohesive
end
