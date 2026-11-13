import Cohesivemodules.Comparison.ModelTSheaf

set_option linter.style.header false

/-!
# C7: the explicit model `T(K)` (definitions) (part 2 of 2)

Split from `Comparison/ModelDef.lean` for size; continues `Comparison/ModelTSheaf.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace DirectSum
variable {X : Type} [TopologicalSpace X]
namespace PreResolvingData
variable (P : PreResolvingData X) (U : Opens X)
  (F : CochainComplex (Mod ((ringOf P.A0).over U)) ℤ)
variable {P U F}
variable (P U F)

/-! ## The differential -/

variable {P U F}

/-- `𝕏_V` commutes with restriction (`Conn.natural`, `totMapAlong_extend`). -/
theorem Conn.X_tRes (θ : P.Conn U F) {V W : (Over U)ᵒᵖ} (f : V ⟶ W) (x : P.TTot U F V) :
    (θ.N W).X (P.tRes U F f x) = P.tRes U F f ((θ.N V).X x) :=
  (totMapAlong_extend (P.D.res (leOfHom f.unop.left)) (fun p => P.fRes U F p f)
    (fun p => P.fRes_smul U F f p) (θ.θ V) (θ.θ W) (fun e => θ.natural f e) x).symm

/-- `𝕏_V` is `O(V)`-linear (`d ∘ ρ = 0`). -/
theorem Conn.X_smulO (θ : P.Conn U F) (V : (Over U)ᵒᵖ) (r : P.O.obj.obj (op V.unop.left))
    (x : P.TTot U F V) :
    (θ.N V).X ((P.ρ V.unop.left r : P.D.A V.unop.left) • x) =
      (P.ρ V.unop.left r : P.D.A V.unop.left) • (θ.N V).X x := by
  have h := (θ.N V).leibniz (p := 0) (P.ρ V.unop.left r).2 x
  refine h.trans ?_
  erw [P.d_ρ, zero_smul, zero_add, Int.negOnePow_zero, one_smul]

/-- **C7.c.** The differential `T^n(V) → T^{n+1}(V)`, `x ↦ 𝕏_V x`. -/
def Conn.TDV (θ : P.Conn U F) (n : ℤ) (V : (Over U)ᵒᵖ) :
    P.TSec U F n V →ₗ[P.O.obj.obj (op V.unop.left)] P.TSec U F (n + 1) V where
  toFun x := ⟨(θ.N V).X x.1, (θ.N V).X_mem x.2⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' r x := Subtype.ext (θ.X_smulO V r x.1)

/-- **C7.c.** The differential `T^n → T^{n+1}` as a map of sheaves. -/
def Conn.TD [CompactSpace X] (θ : P.Conn U F) (n : ℤ) : P.TSh U F n ⟶ P.TSh U F (n + 1) :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (θ.TDV n V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact θ.X_tRes f x.1 }⟩

/-- `d² = 0` on `T` (`Conn.flat` and `c = 0`). -/
theorem Conn.TD_TD [CompactSpace X] (θ : P.Conn U F) (n : ℤ) :
    θ.TD n ≫ θ.TD (n + 1) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  have h := (θ.N V).flat x.1
  erw [P.c_eq_zero, zero_smul] at h
  exact h

/-- **C7.c.** The complex `T` of sheaves of `R|U`-modules. -/
def Conn.TC [CompactSpace X] (θ : P.Conn U F) : CochainComplex (Mod (P.R.over U)) ℤ :=
  CochainComplex.of (P.TSh U F) θ.TD θ.TD_TD

/-! ## The comparison map `Ξ_e` (C7.e) -/

section Xi

variable (θ : P.Conn U F) (M : CohesiveModule (P.D.𝒜 U))

/-- The terminal object `U` of the over-site of `U`. A `def`, not an `abbrev`: instance search
must not unfold it, or `↥(𝒜 ((topO U).unop.left) 0)`-modules are not found. -/
def topO (U : Opens X) : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))

/-- The map `V ⟶ U` in the over-site, as a morphism `op U ⟶ op V`. -/
def toV (V : (Over U)ᵒᵖ) : topO U ⟶ V := (Over.homMk V.unop.hom (by simp)).op

variable {θ M} (e : Z0 M.toQuasiCohesive (θ.N (topO U)))

/-- `res_V ∘ e : Tot(M) → Tot(N_V)` is semilinear along `res_V` and of degree `0`. -/
theorem resE_mem (V : (Over U)ᵒᵖ) :
    (P.tRes U F (toV V)).comp e.1 ∈ LinAlong (P.D.res (leOfHom V.unop.hom)) M.toQuasiCohesive
      (θ.N V) := by
  refine ⟨fun {m x} hx => ?_, fun a x => ?_⟩
  · have h := e.2.1.1 hx
    rw [add_zero] at h
    exact P.tRes_mem U F (toV V) h
  · exact (congrArg (P.tRes U F (toV V)) (hom0_smul e.2.1 a x)).trans
      (P.tRes_smul U F (toV V) a _)

/-- **C7.e.** On `V`: the `𝒜(V)`-linear extension `Tot(M|V) → Tot(N_V)` of `res_V ∘ e`. -/
def ΞV (V : (Over U)ᵒᵖ) : (M.baseChange (P.D.res (leOfHom V.unop.hom))).T →ₗ[ℂ] (θ.N V).T :=
  bcLift ⟨(P.tRes U F (toV V)).comp e.1, resE_mem e V⟩

/-- `ΞV` is closed of degree `0` (`e` closed, `Conn.X_tRes`, `bcLift_mem_Z0`). -/
theorem ΞV_mem (V : (Over U)ᵒᵖ) :
    ΞV e V ∈ Z0 (M.baseChange (P.D.res (leOfHom V.unop.hom))).toQuasiCohesive (θ.N V) := by
  refine bcLift_mem_Z0 _ fun x => ?_
  have h := LinearMap.mem_ker.1 e.2.2
  have h1 : (θ.N (topO U)).X (e.1 x) = e.1 (M.X x) := by
    exact closed0_X h x
  exact (θ.X_tRes (toV V) _).trans (congrArg (P.tRes U F (toV V)) h1)

section BCUniq

variable {k : Type} [CommRing k] {A : Type} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [GCDga 𝒜]
  {B : Type} [Ring B] [Algebra k B] {ℬ : ℤ → Submodule k B} [GradedAlgebra ℬ] [GCDga ℬ]
  {C : Type} [Ring C] [Algebra k C] {𝒞 : ℤ → Submodule k C} [GradedAlgebra 𝒞] [GCDga 𝒞]
  (g : DgaHom ℬ 𝒞) (f : DgaHom 𝒜 ℬ) (f' : DgaHom 𝒜 𝒞) (hgf : ∀ a, g (f a) = f' a)
  (Q : ℤ → Type) [∀ p, AddCommGroup (Q p)] [∀ p, Module (𝒜 0) (Q p)]

variable {N : Type} [AddCommGroup N] [Module C N]

/-- Uniqueness (degree `0`, copy of `bc_ext_semilinear` of `FullyFaithfulAux`): two additive
maps out of `Tot(f^*Q)` that are `g`-semilinear and agree on the image of `F` are equal. -/
private theorem bc_ext_semilinear_mdl (ψ ψ' : Tot ℬ (BCGen f Q) →+ N)
    (hs : ∀ (b : B) (y), ψ (b • y) = g b • ψ y)
    (hs' : ∀ (b : B) (y), ψ' (b • y) = g b • ψ' y)
    (h : ∀ x, ψ (bcF f Q x) = ψ' (bcF f Q x)) : ψ = ψ' := by
  have hgen : ∀ e' : ⨁ p, BCGen f Q p,
      ψ (Tot.tmul ℬ _ 1 e') = ψ' (Tot.tmul ℬ _ 1 e') := by
    intro e'
    induction e' using DirectSum.induction_on with
    | zero => rw [Tot.tmul_zero, map_zero, map_zero]
    | of p x =>
      induction x using BCGen.induction_on with
      | ht β q =>
        have hx : DirectSum.of (BCGen f Q) p (BCGen.tmul f Q β q) =
            (β : ℬ 0) • bcι f Q (lof (𝒜 0) ℤ Q p q) := by
          rw [bcι_lof, ← map_smul, ← BCGen.tmul_eq_smul]; rfl
        have hF1 : Tot.tmul ℬ _ 1 (bcι f Q (lof (𝒜 0) ℤ Q p q)) =
            bcF f Q (Tot.tmul 𝒜 Q 1 (lof (𝒜 0) ℤ Q p q)) := by
          rw [bcF_tmul, f.map_one']
        rw [hx, Tot.tmul_smul0, one_mul, Tot.tmul_eq_smul (β : B), hs, hs', hF1, h]
      | hadd x y hx hy =>
        rw [(DirectSum.of (BCGen f Q) p).map_add, Tot.tmul_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [Tot.tmul_add, map_add, map_add, hx, hy]
  ext x
  induction x using Tot.induction_on with
  | ht b e' => rw [Tot.tmul_eq_smul b e', hs, hs', hgen]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

end BCUniq

/-- `ΞV` commutes with restriction (uniqueness in `eq_bcLift`). -/
theorem ΞV_res {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (x : (M.baseChange (P.D.res (leOfHom V.unop.hom))).T) :
    ΞV e W (P.totRes M (leOfHom V.unop.hom) (leOfHom f.unop.left) x) =
      P.tRes U F f (ΞV e V x) := by
  have hcomp : toV V ≫ f = toV W :=
    Quiver.Hom.unop_inj (Over.OverMorphism.ext (Subsingleton.elim _ _))
  have key := bc_ext_semilinear_mdl (P.D.res (leOfHom f.unop.left))
    (P.D.res (leOfHom V.unop.hom)) M.Q
    (N := (θ.N W).T)
    ((ΞV e W).toAddMonoidHom.comp (P.totRes M (leOfHom V.unop.hom) (leOfHom f.unop.left)))
    ((P.tRes U F f).toAddMonoidHom.comp (ΞV e V).toAddMonoidHom)
    (fun b y => by
      change ΞV e W (bcTotRes _ _ _ _ M.Q (b • y)) =
        P.D.res (leOfHom f.unop.left) b • ΞV e W (bcTotRes _ _ _ _ M.Q y)
      rw [bcTotRes_smul]
      exact hom0_smul (ΞV_mem e W).1 _ _)
    (fun b y => by
      change P.tRes U F f (ΞV e V (b • y)) =
        P.D.res (leOfHom f.unop.left) b • P.tRes U F f (ΞV e V y)
      exact (congrArg (P.tRes U F f) (hom0_smul (ΞV_mem e V).1 b y)).trans
        (P.tRes_smul U F f b _))
    (fun y => by
      change ΞV e W (bcTotRes _ _ _ _ M.Q (bcF _ M.Q y)) =
        P.tRes U F f (ΞV e V (bcF _ M.Q y))
      rw [bcTotRes_bcF]
      refine (bcLift_bcF _ y).trans (Eq.trans ?_ (congrArg (P.tRes U F f)
        (bcLift_bcF _ y)).symm)
      change P.tRes U F (toV W) (e.1 y) = P.tRes U F f (P.tRes U F (toV V) (e.1 y))
      have h := P.tRes_comp U F (toV V) f (e.1 y)
      rw [hcomp] at h
      exact h)
  exact DFunLike.congr_fun key x

/-- `ΞV` is `O(V)`-linear. -/
theorem ΞV_smulO (V : (Over U)ᵒᵖ) (r : P.O.obj.obj (op V.unop.left))
    (x : (M.baseChange (P.D.res (leOfHom V.unop.hom))).T) :
    ΞV e V ((P.ρ V.unop.left r : P.D.A V.unop.left) • x) =
      (P.ρ V.unop.left r : P.D.A V.unop.left) • ΞV e V x :=
  hom0_smul (ΞV_mem e V).1 _ _

/-- **C7.e.** `Ξ_e` on `α_U(M)^n(V) → T^n(V)`. -/
def ΞL (n : ℤ) (V : (Over U)ᵒᵖ) :
    P.sheafOfSec M n (leOfHom V.unop.hom) →ₗ[P.O.obj.obj (op V.unop.left)] P.TSec U F n V where
  toFun x := ⟨ΞV e V x.1, by
    have := (ΞV_mem e V).1.1 x.2
    rwa [add_zero] at this⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' r x := Subtype.ext (ΞV_smulO e V r x.1)

/-- **C7.e.** `Ξ_e : α_U(M)^n → T^n` as a map of sheaves. -/
def Ξn [CompactSpace X] (n : ℤ) : P.sheafOfOverSh U M n ⟶ P.TSh U F n :=
  ⟨{ app := fun V ↦ ModuleCat.ofHom (ΞL e n V)
     naturality := by
       intro V W f
       apply ModuleCat.hom_ext
       refine DFunLike.ext _ _ fun x => ?_
       apply Subtype.ext
       exact ΞV_res e f x.1 }⟩

/-- `Ξ_e` commutes with the differentials (`ΞV_mem`). -/
theorem Ξn_comm [CompactSpace X] (n : ℤ) :
    Ξn e n ≫ θ.TD n = P.sheafOfOverD U M n ≫ Ξn e (n + 1) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  apply Subtype.ext
  exact closed0_X (LinearMap.mem_ker.1 (ΞV_mem e V).2) x.1

/-- **C7.e.** The comparison map `Ξ_e : α_U(M) → T` of complexes of sheaves of `R|U`-modules. -/
def Ξ [CompactSpace X] : P.sheafOfOver U M ⟶ θ.TC where
  f n := Ξn e n
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    have e1 : θ.TC.d i (i + 1) = θ.TD i := CochainComplex.of_d _ _ _
    have e2 : (P.sheafOfOver U M).d i (i + 1) = P.sheafOfOverD U M i := CochainComplex.of_d _ _ _
    rw [e1, e2]
    exact Ξn_comm e i

end Xi

end PreResolvingData

end Cohesive
