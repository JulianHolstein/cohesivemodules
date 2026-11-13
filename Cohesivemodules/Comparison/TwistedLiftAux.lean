import Cohesivemodules.Comparison.TwistedXi
import Cohesivemodules.Comparison.ModelFilBase
import Cohesivemodules.Comparison.TwistedEssSurjPrep

set_option linter.style.header false

/-!
# Z3.u: helpers for the curved lifting (blueprint-tw G′ (i), (k))

Helpers for `TwistedLift.lean`, split off for file size, in the namespace `Cohesive.TwLift`:
* (A)–(C) of G′ (i): `PcT` (`Γ(Pt)` over `𝒜⁰(X)`), `X0comp_Nh` (`𝕏⁰` of `N^h` is `d_F` on global
  sections), `isoN0` (`Γ(F) ≅ (N^h).complex0`), `e0MapT` (`e⁰ = Γ(f⁰)`), `quasiIso_e0MapT`;
* the base change of sections (G′ (k)): `nuS α S : 𝒜⁰(U_α) ⊗_{𝒜⁰(X)} Γ(S) → S(U_α)`,
  `β ⊗ q ↦ β·q|U_α`, bijective for `S` a summand of a finite free `𝒜⁰`-module (`nuS_bij`; free
  case `nuS_free_bij`, retracts `nuS_retract`, generic `bij_of_family`), with `nuS_tmul`,
  `nuS_smul`;
* `eps_sub_smul_deg_one`: `ε((𝕏 − β·) y) = ε(𝕏 y)` for `β` of form degree `1`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace DirectSum
open PreResolvingData (topO)

namespace TwLift


variable {X : Type} [TopologicalSpace X] [CompactSpace X] (P : PreResolvingData X)
  {h : P.D.A ⊤} (T : TwistDatum P.toSheafData h) (hh : h ∈ P.D.𝒜 ⊤ 2)
  (hd : GCDga.d (𝒜 := P.D.𝒜 ⊤) h = 0)
  (K' : CochainComplex (TwMod P.toSheafData.O T.U T.ch) ℤ)
  (θ : ∀ α, P.Conn (T.U α) (twFα P T K' α))
  (hθ : ∀ α, P.IsBCConn (T.U α) (twKα P T K' α) (θ α))

/-- The complex of global sections `Γ(Pt)` as a complex of `𝒜⁰(X)`-modules. -/
abbrev PcT (Pt : CochainComplex (Mod (ringOf P.A0)) ℤ) :
    CochainComplex (ModuleCat.{0} ↥(𝒜h P hh hd 0)) ℤ :=
  ((globalSections (ringOf P.A0)).mapHomologicalComplex (ComplexShape.up ℤ)).obj Pt

/-- `𝕏⁰` of `N^h` is the differential of `F` on global sections (`θh_eps`). -/
theorem X0comp_Nh (p : ℤ) (s : twGens P T K' p) :
    (Nh P T hh hd K' θ hθ).X0comp p s = P.fD ⊤ (twFtop P T K') p (topO ⊤) s := by
  have h : (Nh P T hh hd K' θ hθ).X0 (lof ↥(𝒜h P hh hd 0) ℤ (twGens P T K') p s) =
      lof ↥(𝒜h P hh hd 0) ℤ (twGens P T K') (p + 1) (P.fD ⊤ (twFtop P T K') p (topO ⊤) s) := by
    show Tot.eps (𝒜h P hh hd) (twGens P T K')
      ((θh P T hh hd K' θ hθ).extend (Tot.tmul (𝒜h P hh hd) (twGens P T K') 1 _)) = _
    rw [GenData.extend_tmul_one]
    exact θh_eps P T hh hd K' θ hθ p s
  show DirectSum.component (𝒜h P hh hd 0) ℤ (twGens P T K') (p + 1)
    ((Nh P T hh hd K' θ hθ).X0 (lof ↥(𝒜h P hh hd 0) ℤ (twGens P T K') p s)) = _
  rw [h, DirectSum.component.lof_self]

/-- `Γ(F) ≅ (N^h).complex0` (identity components; the differential is `θh_eps`). -/
def isoN0 :
    ((globalSections (ringOf P.A0)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (untwF P T K') ≅ (Nh P T hh hd K' θ hθ).complex0 :=
  HomologicalComplex.Hom.isoOfComponents (fun p => Iso.refl _) (fun i j hij => by
    obtain rfl : i + 1 = j := hij
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun s => ?_
    exact ((Nh P T hh hd K' θ hθ).complex0_d i s).trans (X0comp_Nh P T hh hd K' θ hθ i s))

/-- The chain map `e⁰ = Γ(f⁰)` followed by `isoN0`. -/
def e0MapT (Pt : CochainComplex (Mod (ringOf P.A0)) ℤ) (f₀ : Pt ⟶ untwF P T K') :
    PcT P hh hd Pt ⟶ (Nh P T hh hd K' θ hθ).complex0 :=
  ((globalSections (ringOf P.A0)).mapHomologicalComplex (ComplexShape.up ℤ)).map f₀ ≫
    (isoN0 P T hh hd K' θ hθ).hom

/-- `e⁰` is a quasi-isomorphism (`Γ(f⁰)` is one by S3, `𝒜⁰` fine). -/
theorem quasiIso_e0MapT (Pt : CochainComplex (Mod (ringOf P.A0)) ℤ)
    (f₀ : Pt ⟶ untwF P T K') [QuasiIso f₀] : QuasiIso (e0MapT P T hh hd K' θ hθ Pt f₀) := by
  have h1 : QuasiIso (((globalSections (ringOf P.A0)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f₀) := quasiIso_globalSections P.isFine0 f₀
  have h6 : IsIso (isoN0 P T hh hd K' θ hθ).hom := (isoN0 P T hh hd K' θ hθ).isIso_hom
  have h4 : QuasiIso (isoN0 P T hh hd K' θ hθ).hom := quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := h1) (hφ' := h4)

/-- Generic: `ε((X − β·) y) = ε(X y)` for `β` of form degree `1`. -/
theorem eps_sub_smul_deg_one {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜] {Q : ℤ → Type}
    [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)] (X : Tot 𝒜 Q →ₗ[k] Tot 𝒜 Q) {β : A}
    (hβ : β ∈ 𝒜 1) (y : Tot 𝒜 Q) :
    Tot.eps 𝒜 Q ((X - DistribSMul.toLinearMap k (Tot 𝒜 Q) β) y) = Tot.eps 𝒜 Q (X y) := by
  rw [LinearMap.sub_apply, map_sub, DistribSMul.toLinearMap_apply, Tot.eps_smul,
    Tot.proj0_of_mem_ne hβ one_ne_zero, zero_smul, sub_zero]

/-- Generic: a natural additive comparison `ν_S : B ⊗_A F(S) → G(S)` that is bijective on the `Z_j`
is bijective on every `S` with maps `π_j : S → Z_j`, `ι_j : Z_j → S`, `∑ π_j ≫ ι_j = 𝟙`. -/
theorem bij_of_family {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞] {A B : Type}
    [CommRing A] [CommRing B] [Algebra A B] (F : 𝒞 ⥤ ModuleCat.{0} A) (G : 𝒞 ⥤ ModuleCat.{0} B)
    [F.Additive] [G.Additive] (ν : ∀ S, TensorProduct A B ↑(F.obj S) →+ ↑(G.obj S))
    (hnat : ∀ {S S' : 𝒞} (g : S ⟶ S') (x : TensorProduct A B ↑(F.obj S)),
      ν S' (LinearMap.lTensor B (F.map g).hom x) = (G.map g).hom (ν S x))
    {S : 𝒞} {m : ℕ} (Z : Fin m → 𝒞) (π : ∀ j, S ⟶ Z j) (ι : ∀ j, Z j ⟶ S)
    (htot : ∑ j, π j ≫ ι j = 𝟙 S) (hZ : ∀ j, Function.Bijective (ν (Z j))) :
    Function.Bijective (ν S) := by
  have hF : ∀ x : TensorProduct A B ↑(F.obj S), ∑ j, LinearMap.lTensor B (F.map (ι j)).hom
      (LinearMap.lTensor B (F.map (π j)).hom x) = x := by
    intro x
    have h0 : (F.map (∑ j, π j ≫ ι j)).hom = ∑ j, (F.map (π j ≫ ι j)).hom := by
      rw [Functor.map_sum]; exact ModuleCat.hom_sum _ _
    have h1 : LinearMap.lTensor B (F.map (∑ j, π j ≫ ι j)).hom x = x := by
      rw [htot, CategoryTheory.Functor.map_id, ModuleCat.hom_id]
      exact LinearMap.lTensor_id_apply B _ x
    rw [h0] at h1
    have e := map_sum (LinearMap.lTensorHom (R := A) (M := B)) (fun j => (F.map (π j ≫ ι j)).hom)
      Finset.univ
    have e' := LinearMap.congr_fun e x
    rw [LinearMap.sum_apply] at e'
    refine Eq.trans ?_ h1
    refine Eq.trans ?_ e'.symm
    exact Finset.sum_congr rfl fun j _ => by
      rw [Functor.map_comp, ModuleCat.hom_comp]
      exact (LinearMap.lTensor_comp_apply B _ _ x).symm
  have hG : ∀ y : ↑(G.obj S), ∑ j, (G.map (ι j)).hom ((G.map (π j)).hom y) = y := by
    intro y
    have h0 : (G.map (∑ j, π j ≫ ι j)).hom = ∑ j, (G.map (π j ≫ ι j)).hom := by
      rw [Functor.map_sum]; exact ModuleCat.hom_sum _ _
    have h1 := LinearMap.congr_fun h0 y
    rw [htot, CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.sum_apply] at h1
    refine Eq.trans ?_ h1.symm
    exact Finset.sum_congr rfl fun j _ => by rw [Functor.map_comp, ModuleCat.hom_comp]; rfl
  constructor
  · intro x y hxy
    have hj : ∀ j, LinearMap.lTensor B (F.map (π j)).hom x =
        LinearMap.lTensor B (F.map (π j)).hom y := fun j =>
      (hZ j).1 ((hnat (π j) x).trans ((congrArg _ hxy).trans (hnat (π j) y).symm))
    rw [← hF x, ← hF y]
    exact Finset.sum_congr rfl fun j _ => by rw [hj j]
  · intro y
    have hj : ∀ j, ∃ z, ν (Z j) z = (G.map (π j)).hom y := fun j => (hZ j).2 _
    choose z hz using hj
    refine ⟨∑ j, LinearMap.lTensor B (F.map (ι j)).hom (z j), ?_⟩
    rw [map_sum]
    refine Eq.trans ?_ (hG y)
    exact Finset.sum_congr rfl fun j _ => by rw [hnat, hz]

/-- The ring `𝒜⁰(U_α)`, as the base change `B⁰` of the curved restriction. -/
abbrev Bα (α : T.ι) : Type :=
  ((P.toSheafData.withCurvature h hh hd).D.res (le_top : T.U α ≤ ⊤)).B0

/-- Global sections as a functor to `𝒜⁰(X)`-modules (`𝒜⁰(X)` of the curved algebra). -/
abbrev FΓ : Mod (ringOf P.A0) ⥤ ModuleCat.{0} ↥(𝒜h P hh hd 0) :=
  globalSections (ringOf P.A0)

/-- Sections over `U_α` of the restriction, as a functor to `𝒜⁰(U_α)`-modules. -/
abbrev GU (α : T.ι) : Mod (ringOf P.A0) ⥤ ModuleCat.{0} (Bα P T hh hd α) :=
  restr (ringOf P.A0) (T.U α) ⋙ gammaT ((ringOf P.A0).over (T.U α)) (Over.mk (𝟙 (T.U α)))

/-- `FΓ` is additive (it is `globalSections`). -/
instance : (FΓ P hh hd).Additive :=
  inferInstanceAs (globalSections (ringOf P.A0)).Additive

/-- `GU` is additive (restriction followed by evaluation at the terminal object). -/
instance (α : T.ι) : (GU P T hh hd α).Additive where
  map_add := rfl

/-- Restriction of global sections to `U_α`. -/
def rhoS (α : T.ι) (S : Mod (ringOf P.A0)) :
    ↑((FΓ P hh hd).obj S) →+ ↑((GU P T hh hd α).obj S) :=
  (S.val.map (homOfLE (le_top : T.U α ≤ ⊤)).op).hom.toAddMonoidHom

omit [CompactSpace X] in
/-- `rhoS` is semilinear along `𝒜⁰(X) → 𝒜⁰(U_α)`. -/
theorem rhoS_smul (α : T.ι) (S : Mod (ringOf P.A0)) (r : ↥(𝒜h P hh hd 0))
    (q : ↑((FΓ P hh hd).obj S)) :
    rhoS P T hh hd α S (r • q) = algebraMap ↥(𝒜h P hh hd 0) (Bα P T hh hd α) r •
      rhoS P T hh hd α S q :=
  (S.val.map (homOfLE (le_top : T.U α ≤ ⊤)).op).hom.map_smul r q

/-- The comparison `ν_S : 𝒜⁰(U_α) ⊗_{𝒜⁰(X)} Γ(S) → S(U_α)`, `β ⊗ q ↦ β · q|U_α`. -/
def nuS (α : T.ι) (S : Mod (ringOf P.A0)) :
    TensorProduct ↥(𝒜h P hh hd 0) (Bα P T hh hd α) ↑((FΓ P hh hd).obj S) →+
      ↑((GU P T hh hd α).obj S) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun β => AddMonoidHom.mk' (fun q => β • rhoS P T hh hd α S q)
      (fun q q' => by rw [map_add, smul_add]))
      (fun β β' => AddMonoidHom.ext fun q => by
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
        exact add_smul β β' _))
    (fun r β q => by
      simp only [AddMonoidHom.mk'_apply]
      rw [rhoS_smul, smul_smul, Algebra.smul_def, mul_comm])

omit [CompactSpace X] in
/-- `rhoS` is natural in `S`. -/
theorem rhoS_nat (α : T.ι) {S S' : Mod (ringOf P.A0)} (g : S ⟶ S')
    (q : ↑((FΓ P hh hd).obj S)) :
    rhoS P T hh hd α S' ((FΓ P hh hd).map g q) = (GU P T hh hd α).map g (rhoS P T hh hd α S q) :=
  (PresheafOfModules.naturality_apply g.val (homOfLE (le_top : T.U α ≤ ⊤)).op q).symm

omit [CompactSpace X] in
/-- `ν` is natural in `S`. -/
theorem nuS_nat (α : T.ι) {S S' : Mod (ringOf P.A0)} (g : S ⟶ S')
    (x : TensorProduct ↥(𝒜h P hh hd 0) (Bα P T hh hd α) ↑((FΓ P hh hd).obj S)) :
    nuS P T hh hd α S' (LinearMap.lTensor (Bα P T hh hd α) ((FΓ P hh hd).map g).hom x) =
      ((GU P T hh hd α).map g).hom (nuS P T hh hd α S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul β q =>
    simp only [LinearMap.lTensor_tmul]
    refine Eq.trans ?_ (((GU P T hh hd α).map g).hom.map_smul β _).symm
    exact congrArg (β • ·) (rhoS_nat P T hh hd α g q)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

omit [CompactSpace X] in
/-- `rhoS` sends the unit section of `unit R` to `1`. -/
theorem rhoS_unit_one (α : T.ι) :
    rhoS P T hh hd α (SheafOfModules.unit (ringOf P.A0))
      (1 : (ringOf P.A0).obj.obj (op ⊤)) = (1 : (ringOf P.A0).obj.obj (op (T.U α))) :=
  map_one ((ringOf P.A0).obj.map (homOfLE (le_top : T.U α ≤ ⊤)).op).hom

omit [CompactSpace X] in
/-- `ν` is bijective on the unit module `𝒜⁰`. -/
theorem nuS_unit_bij (α : T.ι) :
    Function.Bijective (nuS P T hh hd α (SheafOfModules.unit (ringOf P.A0))) := by
  let one0 : ↑((FΓ P hh hd).obj (SheafOfModules.unit (ringOf P.A0))) :=
    (1 : (ringOf P.A0).obj.obj (op ⊤))
  have hr : ∀ q : ↑((FΓ P hh hd).obj (SheafOfModules.unit (ringOf P.A0))),
      ∃ r : ↥(𝒜h P hh hd 0), r • one0 = q := fun q =>
    ⟨show ↥(𝒜h P hh hd 0) from q, by exact mul_one (show ↥(𝒜h P hh hd 0) from q)⟩
  have h1 : ∀ y : Bα P T hh hd α,
      nuS P T hh hd α (SheafOfModules.unit (ringOf P.A0))
        (TensorProduct.tmul ↥(𝒜h P hh hd 0) y one0) = y := by
    intro y
    show y • rhoS P T hh hd α (SheafOfModules.unit (ringOf P.A0)) one0 = y
    rw [rhoS_unit_one]
    exact mul_one y
  refine Function.bijective_iff_has_inverse.2 ⟨fun y => TensorProduct.tmul ↥(𝒜h P hh hd 0) y one0,
    fun x => ?_, h1⟩
  induction x using TensorProduct.inductionOn with
  | tmul β q =>
    obtain ⟨r, rfl⟩ := hr q
    have h2 : nuS P T hh hd α (SheafOfModules.unit (ringOf P.A0))
        (TensorProduct.tmul ↥(𝒜h P hh hd 0) β (r • one0)) =
        β * algebraMap ↥(𝒜h P hh hd 0) (Bα P T hh hd α) r := by
      show β • rhoS P T hh hd α (SheafOfModules.unit (ringOf P.A0)) (r • one0) = _
      rw [rhoS_smul, rhoS_unit_one]
      exact congrArg (β * ·) (mul_one _)
    rw [h2, mul_comm, ← Algebra.smul_def]
    exact TensorProduct.smul_tmul r β one0
  | add x y hx hy =>
    beta_reduce at hx hy ⊢
    rw [map_add]
    exact (TensorProduct.add_tmul _ _ one0).trans (congrArg₂ (· + ·) hx hy)

omit [CompactSpace X] in
/-- `ν` is bijective on `S` if it is on a module `S'` of which `S` is a retract. -/
theorem nuS_retract (α : T.ι) {S S' : Mod (ringOf P.A0)} (i : S ⟶ S') (p : S' ⟶ S)
    (hip : i ≫ p = 𝟙 S) (h : Function.Bijective (nuS P T hh hd α S')) :
    Function.Bijective (nuS P T hh hd α S) :=
  bij_of_family (FΓ P hh hd) (GU P T hh hd α) (nuS P T hh hd α)
    (fun g x => nuS_nat P T hh hd α g x) (fun _ : Fin 1 => S') (fun _ => i) (fun _ => p)
    (by simp only [Finset.univ_unique, Finset.sum_singleton, hip]) (fun _ => h)

omit [CompactSpace X] in
/-- `ν` is bijective on `𝒜⁰^m`. -/
theorem nuS_free_bij (α : T.ι) (m : ℕ) :
    Function.Bijective (nuS P T hh hd α (SheafOfModules.free (R := ringOf P.A0) (Fin m))) := by
  have : Limits.HasFiniteBiproducts (Mod (ringOf P.A0)) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  have hb : Function.Bijective (nuS P T hh hd α
      (Limits.biproduct fun _ : Fin m => SheafOfModules.unit (ringOf P.A0))) :=
    bij_of_family (FΓ P hh hd) (GU P T hh hd α) (nuS P T hh hd α)
      (fun g x => nuS_nat P T hh hd α g x) (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0))
      (fun j => Limits.biproduct.π (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)) j)
      (fun j => Limits.biproduct.ι (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)) j)
      (Limits.biproduct.total (f := fun _ : Fin m => SheafOfModules.unit (ringOf P.A0)))
      (fun _ => nuS_unit_bij P T hh hd α)
  exact nuS_retract P T hh hd α (Limits.biproduct.isoCoproduct
    (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0))).inv
    (Limits.biproduct.isoCoproduct (fun _ : Fin m => SheafOfModules.unit (ringOf P.A0))).hom
    (Iso.inv_hom_id _) hb

omit [CompactSpace X] in
/-- `ν` is bijective on every direct summand of a finite free module. -/
theorem nuS_bij (α : T.ι) {S : Mod (ringOf P.A0)} (hS : IsFinFreeSummand S) :
    Function.Bijective (nuS P T hh hd α S) := by
  obtain ⟨m, i, p, hip⟩ := hS
  exact nuS_retract P T hh hd α i p hip (nuS_free_bij P T hh hd α m)

omit [CompactSpace X] in
/-- `ν` on a pure tensor. -/
theorem nuS_tmul (α : T.ι) (S : Mod (ringOf P.A0)) (β : Bα P T hh hd α)
    (q : ↑((FΓ P hh hd).obj S)) :
    nuS P T hh hd α S (TensorProduct.tmul ↥(𝒜h P hh hd 0) β q) = β • rhoS P T hh hd α S q :=
  rfl

omit [CompactSpace X] in
/-- `ν` is `𝒜⁰(U_α)`-linear. -/
theorem nuS_smul (α : T.ι) (S : Mod (ringOf P.A0)) (r : Bα P T hh hd α)
    (x : TensorProduct ↥(𝒜h P hh hd 0) (Bα P T hh hd α) ↑((FΓ P hh hd).obj S)) :
    nuS P T hh hd α S (r • x) = r • nuS P T hh hd α S x := by
  induction x using TensorProduct.inductionOn with
  | tmul β q =>
    rw [TensorProduct.smul_tmul']
    exact mul_smul r β (rhoS P T hh hd α S q)
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

end TwLift

end Cohesive
