import Cohesivemodules.Comparison.SetupDef
import Cohesivemodules.Comparison.SetupAux
import Cohesivemodules.Sheaf.Projective
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.RingTheory.Flat.Basic

set_option linter.style.header false

/-!
# C0: consequences of the resolving data

Blueprint item C0 (§4), API used by C2–C5. For pre-resolving data `P` (C0.a):
* `isComm_ringOf`: the sheaf of rings of a sheaf of commutative rings is commutative (audit G9;
  `isComm_forget₂` of `ChecksSheaf.lean`, which library files may not import).
* `P.piecePre q`, `P.pieceSheaf q : Mod (ringOf P.A0)`: the sheaf `𝒜^q` of `𝒜⁰`-modules,
  `𝒜^q(U) = GCDga.piece (𝒜_U) q` (one carrier, v1.9), a sheaf by `P.glue`, `P.degree_local`.
* `isLocallyFinFreeSummand_pieceSheaf` (from `P.locFrame`), `isFinFreeSummand_pieceSheaf` (S4.b,
  `X` compact), `projective_piece`, `flat_piece`: `𝒜^q(X)` is a finitely generated projective,
  hence flat, `𝒜⁰(X)`-module (S4.c), as A11 and A12 need.
* `P.dgaO q : Mod P.R`, `P.dgaComplex`: the complex `𝒜^•` of sheaves of `O`-modules (`O` acting
  through `ρ`, `d` is `O`-linear by `d ∘ ρ = 0`), and `P.ρhat : O[0] ⟶ 𝒜^•` (audit G8).
* For resolving data `D` (C0.b): `quasiIso_ρhat`: `O → 𝒜^•` is a quasi-isomorphism (the local,
  sectionwise exactness fields of C0.b, through S6).
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- **C0** (audit G9). The sheaf of rings `ringOf R` of a sheaf of commutative rings is commutative. -/
theorem isComm_ringOf (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{0}) :
    IsComm (ringOf R) := by
  intro U a b
  exact mul_comm (show R.obj.obj (op U) from a) b

namespace PreResolvingData

variable (P : PreResolvingData X)

/-! ## The sheaves `𝒜^q` of `𝒜⁰`-modules -/

/-- Restriction of `𝒜^q`, as a semilinear map over `res : 𝒜⁰(U) → 𝒜⁰(V)`. -/
def resPiece (q : ℤ) {U V : Opens X} (h : V ≤ U) :
    GCDga.piece (P.D.𝒜 U) q →ₛₗ[(P.D.res h).f0] GCDga.piece (P.D.𝒜 V) q where
  toFun a := ⟨P.D.res h a, (P.D.res h).map_mem a.2⟩
  map_add' a b := Subtype.ext ((P.D.res h).map_add' a b)
  map_smul' f a := Subtype.ext ((P.D.res h).map_mul' f a)

/-- **C0.** `𝒜^q` as a presheaf of `𝒜⁰`-modules, `U ↦ GCDga.piece (𝒜_U) q`. -/
def piecePre (q : ℤ) : PresheafOfModules.{0} (ringOf P.A0).obj where
  obj U := ModuleCat.of ↥(P.D.𝒜 U.unop 0) ↥(GCDga.piece (P.D.𝒜 U.unop) q)
  map {U V} f := ModuleCat.semilinearMapAddEquiv ((ringOf P.A0).obj.map f).hom
      (ModuleCat.of ↥(P.D.𝒜 U.unop 0) ↥(GCDga.piece (P.D.𝒜 U.unop) q))
      (ModuleCat.of ↥(P.D.𝒜 V.unop 0) ↥(GCDga.piece (P.D.𝒜 V.unop) q))
      (P.resPiece q (leOfHom f.unop))
  map_id := by
    intro U
    refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
    exact Subtype.ext (P.D.res_id _ _)
  map_comp := by
    intro U V W f g
    refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
    exact Subtype.ext (P.D.res_comp _ _ _).symm

/-- Gluing of degree-`q` sections (`P.glue` and `P.degree_local`). -/
private theorem glue_piece (q : ℤ) {ι : Type} (U : ι → Opens X)
    (a : ∀ i, ↥(GCDga.piece (P.D.𝒜 (U i)) q))
    (h : ∀ i j, P.D.res (inf_le_left : U i ⊓ U j ≤ U i) (a i : P.D.A (U i)) =
      P.D.res (inf_le_right : U i ⊓ U j ≤ U j) (a j : P.D.A (U j))) :
    ∃! b : ↥(GCDga.piece (P.D.𝒜 (⨆ i, U i)) q),
      ∀ i, P.D.res (le_iSup U i) (b : P.D.A (⨆ i, U i)) = (a i : P.D.A (U i)) := by
  obtain ⟨b, hb, hb'⟩ := P.glue U (fun i => (a i : P.D.A (U i))) h
  have hmem : b ∈ P.D.𝒜 (⨆ i, U i) q := by
    refine P.degree_local q b fun x hx => ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
    exact ⟨U i, le_iSup U i, hi, by rw [hb i]; exact (a i).2⟩
  refine ⟨⟨b, hmem⟩, hb, fun b'' hb'' => Subtype.ext (hb' _ hb'')⟩

/-- **C0.** `𝒜^q` is a sheaf (`P.glue`, `P.degree_local`). -/
theorem isSheaf_piecePre (q : ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (P.piecePre q).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (X := TopCat.of X) (P.piecePre q).presheaf).2 ?_
  intro ι U sf hsf
  obtain ⟨b, hb, hu⟩ := P.glue_piece q U sf fun i j => congrArg Subtype.val (hsf i j)
  exact ⟨b, fun i => Subtype.ext (hb i), fun s hs => hu s fun i => congrArg Subtype.val (hs i)⟩

/-- **C0.** The sheaf `𝒜^q` of `𝒜⁰`-modules. -/
def pieceSheaf (q : ℤ) : Mod (ringOf P.A0) := ⟨P.piecePre q, P.isSheaf_piecePre q⟩

/-- A frame indexed by a finite type can be reindexed by `Fin m`. -/
private theorem frame_fin (q : ℕ) (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (m : ℕ) (e : Fin m → ↥(P.D.𝒜 U q)),
      ∀ (V : Opens X) (h : V ≤ U), ∀ β ∈ P.D.𝒜 V q, ∃! f : Fin m → ↥(P.D.𝒜 V 0),
        β = ∑ i, (f i : P.D.A V) * P.D.res h (e i : P.D.A U) := by
  obtain ⟨U, hx, ι, hι, e, he⟩ := P.locFrame q x
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨U, hx, Fintype.card ι, fun j => e (σ.symm j), fun V h β hβ => ?_⟩
  obtain ⟨f, hf, hu⟩ := he V h β hβ
  refine ⟨fun j => f (σ.symm j), ?_, fun g hg => ?_⟩
  · rw [hf]
    exact (Equiv.sum_comp σ.symm (fun i => (f i : P.D.A V) * P.D.res h (e i : P.D.A U))).symm
  · funext j
    have := hu (fun i => g (σ i)) (by
      rw [hg]
      exact (Equiv.sum_comp σ (fun j => (g j : P.D.A V) *
        P.D.res h (e (σ.symm j) : P.D.A U))).symm.trans
        (Finset.sum_congr rfl fun i _ => by simp only [Equiv.symm_apply_apply]))
    rw [← this]
    simp only [Equiv.apply_symm_apply]

/-- Coefficient maps of a frame: `𝒜_V^q → 𝒜_V⁰ᵐ`, `𝒜⁰`-linear and compatible with restriction. -/
private theorem frame_coef (q : ℤ) (U : Opens X) (m : ℕ) (e : Fin m → ↥(P.D.𝒜 U q))
    (hfr : ∀ (V : Opens X) (h : V ≤ U), ∀ β ∈ P.D.𝒜 V q, ∃! f : Fin m → ↥(P.D.𝒜 V 0),
      β = ∑ i, (f i : P.D.A V) * P.D.res h (e i : P.D.A U)) :
    ∃ c : ∀ V : Opens X, V ≤ U → ↥(GCDga.piece (P.D.𝒜 V) q) →ₗ[↥(P.D.𝒜 V 0)]
        (Fin m → ↥(P.D.𝒜 V 0)),
      (∀ V h (β : ↥(GCDga.piece (P.D.𝒜 V) q)),
        (β : P.D.A V) = ∑ i, (c V h β i : P.D.A V) * P.D.res h (e i : P.D.A U)) ∧
      ∀ V W (h : V ≤ U) (hW : W ≤ V) (β : ↥(GCDga.piece (P.D.𝒜 V) q)) i,
        c W (hW.trans h) (P.resPiece q hW β) i = (P.D.res hW).f0 (c V h β i) := by
  choose c0 hc0 huniq using fun V (h : V ≤ U) (β : ↥(GCDga.piece (P.D.𝒜 V) q)) =>
    hfr V h β β.2
  have hadd : ∀ V (h : V ≤ U) (β γ : ↥(GCDga.piece (P.D.𝒜 V) q)),
      c0 V h (β + γ) = c0 V h β + c0 V h γ := fun V h β γ => by
    symm
    refine huniq V h (β + γ) _ ?_
    simp only [Submodule.coe_add, Pi.add_apply, AddMemClass.coe_add, add_mul,
      Finset.sum_add_distrib]
    rw [← hc0 V h β, ← hc0 V h γ]
  have hsmul : ∀ V (h : V ≤ U) (r : ↥(P.D.𝒜 V 0)) (β : ↥(GCDga.piece (P.D.𝒜 V) q)),
      c0 V h (r • β) = r • c0 V h β := fun V h r β => by
    symm
    refine huniq V h (r • β) _ ?_
    simp only [GCDga.coe_smul_piece, Pi.smul_apply, smul_eq_mul]
    have h1 : (β : P.D.A V) = ∑ i, (c0 V h β i : P.D.A V) * P.D.res h (e i : P.D.A U) :=
      hc0 V h β
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  refine ⟨fun V h => ⟨⟨c0 V h, hadd V h⟩, hsmul V h⟩, fun V h β => hc0 V h β, ?_⟩
  intro V W h hW β i
  have h1 : (β : P.D.A V) = ∑ i, (c0 V h β i : P.D.A V) * P.D.res h (e i : P.D.A U) :=
    hc0 V h β
  have h2 : (↑(P.resPiece q hW β) : P.D.A W) = ∑ i, ((P.D.res hW).f0 (c0 V h β i) : P.D.A W) *
      P.D.res (hW.trans h) (e i : P.D.A U) := by
    show P.D.res hW (β : P.D.A V) = _
    rw [h1]
    show (P.D.res hW).toAlgHom _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    show P.D.res hW _ * P.D.res hW (P.D.res h _) = _
    rw [P.D.res_comp]
    rfl
  exact (congrFun (huniq W (hW.trans h) (P.resPiece q hW β)
    (fun i => (P.D.res hW).f0 (c0 V h β i)) h2) i).symm

/-- The coefficient functionals of a frame as morphisms `𝒜^q|U ⟶ 𝒜⁰|U` of sheaves of modules. -/
private theorem exists_cj (q : ℤ) (U : Opens X) (m : ℕ)
    (c : ∀ V : Opens X, V ≤ U → ↥(GCDga.piece (P.D.𝒜 V) q) →ₗ[↥(P.D.𝒜 V 0)]
      (Fin m → ↥(P.D.𝒜 V 0)))
    (hc2 : ∀ V W (h : V ≤ U) (hW : W ≤ V) (β : ↥(GCDga.piece (P.D.𝒜 V) q)) i,
      c W (hW.trans h) (P.resPiece q hW β) i = (P.D.res hW).f0 (c V h β i)) :
    ∃ cj : Fin m → ((restr (ringOf P.A0) U).obj (P.pieceSheaf q) ⟶
        SheafOfModules.unit ((ringOf P.A0).over U)),
      ∀ j Z (a : ↑(((restr (ringOf P.A0) U).obj (P.pieceSheaf q)).val.obj Z)),
        (show ↥(P.D.𝒜 Z.unop.left 0) from ((cj j).val.app Z).hom a) =
          c Z.unop.left (leOfHom Z.unop.hom) (show ↥(GCDga.piece (P.D.𝒜 Z.unop.left) q) from a)
            j := by
  refine ⟨fun j =>
    ⟨PresheafOfModules.homMk
      { app := fun Z => AddCommGrpCat.ofHom
          { toFun := fun a => c Z.unop.left (leOfHom Z.unop.hom) a j
            map_zero' := by
              have := map_zero (c Z.unop.left (leOfHom Z.unop.hom))
              exact congrFun this j
            map_add' := fun a b => by
              have := (c Z.unop.left (leOfHom Z.unop.hom)).map_add a b
              exact congrFun this j }
        naturality := by
          intro Z Z' f
          refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a => ?_)
          exact (hc2 Z.unop.left Z'.unop.left (leOfHom Z.unop.hom) (leOfHom f.unop.left)
            (show ↥(GCDga.piece (P.D.𝒜 Z.unop.left) q) from a) j) }
      (fun Z r a => by
        have := (c Z.unop.left (leOfHom Z.unop.hom)).map_smul r a
        exact congrFun this j)⟩, fun j Z a => rfl⟩

/-- The frame sections as morphisms `𝒜⁰|U ⟶ 𝒜^q|U` of sheaves of modules. -/
private theorem exists_ej (q : ℤ) (U : Opens X) (m : ℕ) (e : Fin m → ↥(P.D.𝒜 U q)) :
    ∃ ej : Fin m → (SheafOfModules.unit ((ringOf P.A0).over U) ⟶
        (restr (ringOf P.A0) U).obj (P.pieceSheaf q)),
      ∀ j Z (r : ↑((SheafOfModules.unit ((ringOf P.A0).over U)).val.obj Z)),
        ((show ↥(GCDga.piece (P.D.𝒜 Z.unop.left) q) from ((ej j).val.app Z).hom r) :
            P.D.A Z.unop.left) =
          ((show ↥(P.D.𝒜 Z.unop.left 0) from r) : P.D.A Z.unop.left) *
            P.D.res (leOfHom Z.unop.hom) (e j : P.D.A U) := by
  refine ⟨fun j => ((restr (ringOf P.A0) U).obj (P.pieceSheaf q)).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk
        (fun Z => (show ↥(GCDga.piece (P.D.𝒜 Z.unop.left) q) from
          P.resPiece q (leOfHom Z.unop.hom) (e j)))
        (fun Z Z' f => Subtype.ext (P.D.res_comp _ _ _))), fun j Z r => rfl⟩

/-- **C0.** `𝒜^q` is locally a direct summand of a finite free `𝒜⁰`-module (from the local frame
`P.locFrame`; in fact locally free). -/
theorem isLocallyFinFreeSummand_pieceSheaf (q : ℕ) :
    IsLocallyFinFreeSummand (P.pieceSheaf q) := by
  intro x
  obtain ⟨U, hx, m, e, hfr⟩ := P.frame_fin q x
  obtain ⟨c, hc1, hc2⟩ := P.frame_coef q U m e hfr
  refine ⟨U, hx, ?_⟩
  obtain ⟨cj, hcj⟩ := P.exists_cj q U m c hc2
  obtain ⟨ej, hej⟩ := P.exists_ej q U m e
  have hsum : ∑ j, cj j ≫ ej j = 𝟙 _ := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro Z
    refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
    clear hfr
    have hs : (∑ j, cj j ≫ ej j).val.app Z = ∑ j, ((cj j ≫ ej j).val.app Z) :=
      Functor.map_sum (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ Z) _ _
    rw [hs, ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Subtype.ext ?_
    change (↑(∑ d, (show ↥(GCDga.piece (P.D.𝒜 Z.unop.left) q) from
      ((cj d ≫ ej d).val.app Z).hom a)) : P.D.A Z.unop.left) =
        ((show ↥(GCDga.piece (P.D.𝒜 Z.unop.left) q) from a) : P.D.A Z.unop.left)
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Eq.trans (Finset.sum_congr rfl fun j _ => (hej j Z _).trans
      (congrArg (· * _) (congrArg Subtype.val (hcj j Z a)))) (hc1 _ _ _).symm
  have : Limits.HasFiniteBiproducts (Mod ((ringOf P.A0).over U)) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  let iso := Limits.biproduct.isoCoproduct
    (fun _ : Fin m => SheafOfModules.unit ((ringOf P.A0).over U))
  have h2 : (Limits.biproduct.lift cj ≫ iso.hom) ≫ iso.inv ≫ Limits.biproduct.desc ej =
      𝟙 ((restr (ringOf P.A0) U).obj (P.pieceSheaf q)) := by
    rw [Category.assoc, ← Category.assoc iso.hom, iso.hom_inv_id, Category.id_comp,
      Limits.biproduct.lift_desc, hsum]
  exact ⟨m, Limits.biproduct.lift cj ≫ iso.hom, iso.inv ≫ Limits.biproduct.desc ej, h2⟩

/-- **C0 + S4.b.** On compact `X`, `𝒜^q` is a direct summand of a finite free `𝒜⁰`-module. -/
theorem isFinFreeSummand_pieceSheaf [CompactSpace X] (q : ℕ) :
    IsFinFreeSummand (P.pieceSheaf q) :=
  isFinFreeSummand_of_locally P.isFine0 (isComm_ringOf _)
    (P.isLocallyFinFreeSummand_pieceSheaf q)

/-- In negative degrees the global piece is trivial. -/
private theorem subsingleton_piece_neg {q : ℤ} (hq : q < 0) :
    Subsingleton ↥(GCDga.piece P.𝒜X q) :=
  ⟨fun a b => Subtype.ext
    ((GCDga.eq_zero_of_neg (P.D.𝒜 ⊤) hq a.2).trans
      (GCDga.eq_zero_of_neg (P.D.𝒜 ⊤) hq b.2).symm)⟩

/-- **C0 + S4.c.** On compact `X`, `𝒜^q(X)` is a finitely generated projective
`𝒜⁰(X)`-module (every `q : ℤ`; `0` for `q < 0`). -/
theorem projective_piece [CompactSpace X] (q : ℤ) :
    Module.Projective ↥(P.𝒜X 0) ↥(GCDga.piece P.𝒜X q) := by
  by_cases hq : 0 ≤ q
  · lift q to ℕ using hq
    exact projective_globalSections (P.isFinFreeSummand_pieceSheaf q)
  · have := P.subsingleton_piece_neg (not_le.1 hq)
    exact Module.Projective.of_free

/-- **C0 + S4.c.** On compact `X`, `𝒜^q(X)` is finitely generated over `𝒜⁰(X)`. -/
theorem finite_piece [CompactSpace X] (q : ℤ) :
    Module.Finite ↥(P.𝒜X 0) ↥(GCDga.piece P.𝒜X q) := by
  by_cases hq : 0 ≤ q
  · lift q to ℕ using hq
    exact finite_globalSections (P.isFinFreeSummand_pieceSheaf q)
  · have := P.subsingleton_piece_neg (not_le.1 hq)
    infer_instance

/-- **C0.** On compact `X`, `𝒜^q(X)` is flat over `𝒜⁰(X)` (the hypothesis of A11 and A12). -/
theorem flat_piece [CompactSpace X] (q : ℤ) :
    Module.Flat ↥(P.𝒜X 0) ↥(GCDga.piece P.𝒜X q) :=
  have := P.projective_piece q
  inferInstance

/-! ## The complex `𝒜^•` of sheaves of `O`-modules and `ρ : O → 𝒜^•` -/

/-- Sections of `𝒜^q` over `U` as an `O(U)`-module (through `ρ_U`); a type synonym, so that the
`O(U)`-action does not clash with the `𝒜⁰(U)`-action. -/
def PieceO (q : ℤ) (U : Opens X) : Type := ↥(GCDga.piece (P.D.𝒜 U) q)

instance (q : ℤ) (U : Opens X) : AddCommGroup (P.PieceO q U) :=
  inferInstanceAs (AddCommGroup ↥(GCDga.piece (P.D.𝒜 U) q))

instance (q : ℤ) (U : Opens X) : Module (P.O.obj.obj (op U)) (P.PieceO q U) :=
  Module.compHom ↥(GCDga.piece (P.D.𝒜 U) q) (P.ρ U)

/-- Restriction of `𝒜^q`, as a semilinear map of `O`-modules over `O(U) → O(V)`. -/
def resPieceO (q : ℤ) {U V : Opens X} (h : V ≤ U) :
    P.PieceO q U →ₛₗ[(P.O.obj.map (homOfLE h).op).hom] P.PieceO q V where
  toFun a := P.resPiece q h a
  map_add' a b := map_add (P.resPiece q h) a b
  map_smul' f a := by
    refine Subtype.ext ?_
    show P.D.res h ((P.ρ U f : P.D.A U) *
        ((show ↥(GCDga.piece (P.D.𝒜 U) q) from a : ↥(GCDga.piece (P.D.𝒜 U) q)) : P.D.A U)) =
      ((P.ρ V (P.O.obj.map (homOfLE h).op f) : P.D.A V)) *
        P.D.res h ((show ↥(GCDga.piece (P.D.𝒜 U) q) from a : ↥(GCDga.piece (P.D.𝒜 U) q)) : P.D.A U)
    rw [(P.D.res h).map_mul', ← P.ρ_natural h f]
    rfl

/-- **C0.** `𝒜^q` as a presheaf of `O`-modules (`O` acting through `ρ`). -/
def dgaPre (q : ℤ) : PresheafOfModules.{0} P.R.obj where
  obj U := ModuleCat.of (P.O.obj.obj (op U.unop)) (P.PieceO q U.unop)
  map {U V} f := ModuleCat.semilinearMapAddEquiv (P.R.obj.map f).hom
      (ModuleCat.of (P.O.obj.obj (op U.unop)) (P.PieceO q U.unop))
      (ModuleCat.of (P.O.obj.obj (op V.unop)) (P.PieceO q V.unop))
      (P.resPieceO q (leOfHom f.unop))
  map_id := by
    intro U
    refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
    exact Subtype.ext (P.D.res_id _ _)
  map_comp := by
    intro U V W f g
    refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
    exact Subtype.ext (P.D.res_comp _ _ _).symm

/-- `𝒜^q` is a sheaf of `O`-modules (the same presheaf of groups as `piecePre`). -/
theorem isSheaf_dgaPre (q : ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (P.dgaPre q).presheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing
    (X := TopCat.of X) (P.dgaPre q).presheaf).2 ?_
  intro ι U sf hsf
  obtain ⟨b, hb, hu⟩ := P.glue_piece q U sf fun i j => congrArg Subtype.val (hsf i j)
  exact ⟨b, fun i => Subtype.ext (hb i), fun s hs => hu s fun i => congrArg Subtype.val (hs i)⟩

/-- **C0.** `𝒜^q` as a sheaf of `O`-modules (`O` acting through `ρ`). -/
def dgaO (q : ℤ) : Mod P.R := ⟨P.dgaPre q, P.isSheaf_dgaPre q⟩

/-- `d : 𝒜^q(U) → 𝒜^{q+1}(U)` is `O(U)`-linear (`d ∘ ρ_U = 0`, Leibniz). -/
def dgaDV (q : ℤ) (U : Opens X) : P.PieceO q U →ₗ[P.O.obj.obj (op U)] P.PieceO (q + 1) U where
  toFun a := ⟨GCDga.d (𝒜 := P.D.𝒜 U)
    ((show ↥(GCDga.piece (P.D.𝒜 U) q) from a) : P.D.A U), GCDga.d_mem a.2⟩
  map_add' a b := Subtype.ext (map_add (GCDga.d (𝒜 := P.D.𝒜 U)) _ _)
  map_smul' f a := by
    refine Subtype.ext ?_
    have h := GCDga.leibniz_zero (𝒜 := P.D.𝒜 U) (P.ρ U f).2
      (Subtype.val (show ↥(GCDga.piece (P.D.𝒜 U) q) from a))
    rw [P.d_ρ, zero_mul, zero_add] at h
    exact h

/-- **C0.** `d : 𝒜^q → 𝒜^{q+1}` as a map of sheaves of `O`-modules. -/
def dgaD (q : ℤ) : P.dgaO q ⟶ P.dgaO (q + 1) :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom (P.dgaDV q U.unop)
     naturality := by
       intro U V f
       refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
       exact Subtype.ext ((P.D.res (leOfHom f.unop)).map_d _).symm }⟩

/-- `d² = 0` on `𝒜^•` (`c = 0`). -/
theorem dgaD_dgaD (q : ℤ) : P.dgaD q ≫ P.dgaD (q + 1) = 0 := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
  exact Subtype.ext (GCDga.d_d _)

/-- **C0.** The complex `𝒜^•` of sheaves of `O`-modules. -/
def dgaComplex : CochainComplex (Mod P.R) ℤ :=
  CochainComplex.of P.dgaO P.dgaD P.dgaD_dgaD

/-- `ρ_U` as an `O(U)`-linear map `O(U) → 𝒜⁰(U)`. -/
def ρV (U : Opens X) : P.O.obj.obj (op U) →ₗ[P.O.obj.obj (op U)] P.PieceO 0 U where
  toFun f := ⟨(P.ρ U f : P.D.A U), (P.ρ U f).2⟩
  map_add' a b := Subtype.ext (by
    show ((P.ρ U (a + b) : ↥(P.D.𝒜 U 0)) : P.D.A U) = _
    rw [map_add]
    rfl)
  map_smul' f g := Subtype.ext (by
    simp only [smul_eq_mul, map_mul, RingHom.id_apply]
    rfl)

/-- **C0.** `ρ : O → 𝒜⁰` as a map of sheaves of `O`-modules. -/
def ρO : SheafOfModules.unit P.R ⟶ P.dgaO 0 :=
  ⟨{ app := fun U ↦ (show ModuleCat.of (P.O.obj.obj (op U.unop)) (P.O.obj.obj (op U.unop)) ⟶
        (P.dgaO 0).val.obj U from ModuleCat.ofHom (P.ρV U.unop))
     naturality := by
       intro U V f
       refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
       exact Subtype.ext (congrArg Subtype.val (P.ρ_natural (leOfHom f.unop) a).symm) }⟩

/-- `d ∘ ρ = 0` as maps of sheaves. -/
theorem ρO_dgaD : P.ρO ≫ P.dgaD 0 = 0 := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (DFunLike.ext _ _ fun a => ?_)
  exact Subtype.ext (P.d_ρ _ a)

/-- **C0.** `ρ̂ : O[0] → 𝒜^•`. -/
def ρhat : (HomologicalComplex.single (Mod P.R) (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit P.R) ⟶ P.dgaComplex :=
  HomologicalComplex.mkHomFromSingle P.ρO (by
    intro k hk
    have hk' : (0 : ℤ) + 1 = k := hk
    subst hk'
    show P.ρO ≫ CochainComplex.of.d P.dgaO P.dgaD 0 (0 + 1) = 0
    rw [CochainComplex.of_d]
    exact P.ρO_dgaD)

end PreResolvingData

namespace ResolvingData

variable (D : ResolvingData X)

/-- The sheaves `𝒜^i`, `i < 0`, are zero. -/
private theorem isZero_dgaO_neg {i : ℤ} (hi : i < 0) : Limits.IsZero (D.dgaO i) :=
  isZero_of_sections_subsingleton fun V =>
    ⟨fun a b => by
      have ha := GCDga.eq_zero_of_neg (D.toPreResolvingData.D.𝒜 V.unop) hi
        (show ↥(GCDga.piece (D.toPreResolvingData.D.𝒜 V.unop) i) from a).2
      have hb := GCDga.eq_zero_of_neg (D.toPreResolvingData.D.𝒜 V.unop) hi
        (show ↥(GCDga.piece (D.toPreResolvingData.D.𝒜 V.unop) i) from b).2
      exact Subtype.ext (ha.trans hb.symm)⟩

/-- `ρ` is injective on sections. -/
private theorem ρO_inj (V : (Opens X)ᵒᵖ) : Function.Injective (D.ρO.val.app V) :=
  fun _ _ hab => D.ρ_injective V.unop (Subtype.ext (congrArg Subtype.val hab))

/-- Closed sections of `𝒜⁰` come from `O`. -/
private theorem ρO_surj (V : (Opens X)ᵒᵖ) (s : (D.dgaO 0).val.obj V)
    (hs : (D.dgaD 0).val.app V s = 0) : ∃ r, D.ρO.val.app V r = s := by
  obtain ⟨r, hr⟩ := D.exact0 V.unop
    (show ↥(GCDga.piece (D.toPreResolvingData.D.𝒜 V.unop) 0) from s)
    (congrArg Subtype.val hs)
  exact ⟨r, Subtype.ext (congrArg Subtype.val hr)⟩

/-- `𝒜^•` is exact in degrees `n + 1`, `n ≥ 0` (local exactness `exactq`, S6). -/
private theorem exactAt_pos (n : ℕ) : D.dgaComplex.ExactAt ((n : ℤ) + 1) := by
  have hd : ∀ m : ℤ, D.dgaComplex.d m (m + 1) = D.dgaD m := fun m =>
    CochainComplex.of_d _ _ m
  rw [HomologicalComplex.exactAt_iff' _ (n : ℤ) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (by simp)
    (by simp), shortComplex_exact_iff]
  intro U s hs x hx
  have hs' : ((D.dgaComplex.d ((n : ℤ) + 1) ((n : ℤ) + 1 + 1)).val.app (op U)).hom s = 0 := hs
  rw [hd] at hs'
  obtain ⟨U', h, hxU', η, hη, hdη⟩ := D.exactq U n x hx
    (show ↥(GCDga.piece (D.toPreResolvingData.D.𝒜 U) ((n : ℤ) + 1)) from s).1
    (show ↥(GCDga.piece (D.toPreResolvingData.D.𝒜 U) ((n : ℤ) + 1)) from s).2
    (congrArg Subtype.val hs')
  refine ⟨U', h, hxU', (⟨η, hη⟩ : ↥(GCDga.piece (D.toPreResolvingData.D.𝒜 U') (n : ℤ))), ?_⟩
  refine Subtype.ext ?_
  have hf : ((D.dgaComplex.d (n : ℤ) ((n : ℤ) + 1)).val.app (op U')).hom
      (⟨η, hη⟩ : ↥(GCDga.piece (D.toPreResolvingData.D.𝒜 U') (n : ℤ))) =
      ((D.dgaD (n : ℤ)).val.app (op U')).hom ⟨η, hη⟩ := by
    rw [hd]
    rfl
  exact (congrArg Subtype.val hf).trans hdη

/-- **C0.b (G8).** `O → 𝒜⁰ → 𝒜¹ → ⋯` is a resolution: `ρ̂` is a quasi-isomorphism (from
`ρ_injective`, `exact0`, `exactq`; local exactness suffices, S6). -/
theorem quasiIso_ρhat : QuasiIso D.ρhat :=
  quasiIso_mkHomFromSingle (L := D.dgaComplex) D.ρO _
    (fun i hi => D.isZero_dgaO_neg hi) D.ρO_inj
    (fun V s hs => D.ρO_surj V s hs)
    (fun i hi => by
      obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ i - 1 by omega)
      have := D.exactAt_pos n
      rwa [show (n : ℤ) + 1 = i by omega] at this)

end ResolvingData

end Cohesive
