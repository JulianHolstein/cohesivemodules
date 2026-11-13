import Cohesivemodules.Forms.ExpForm
import Cohesivemodules.Comparison.TwistDatumDef

set_option linter.style.header false

/-!
# Z3.d: a twist datum from primitives (B.4–B.6)

Blueprint item Z3.d (`blueprint/blueprint-tw.md` §3 B.4–B.6; blueprint §11 v1.19). From a finite
cover with primitives `h⁰_α` of `h` and normalized primitives `η_αβ` of `h⁰_β − h⁰_α`
(`exists_cover_primitives`): `u_αβ := exp η_αβ` (`expUnit`, `dbar_expForm`), and `ȟ_αβγ` the
holomorphic unit with `ρ(ȟ_αβγ) = u_βγ u_αβ u_αγ⁻¹` (F12: the right side is a `∂̄`-closed unit,
its `∂̄`-logarithm being `ω_βγ + ω_αβ − ω_αγ = 0`, so it and its inverse are `ρ` of holomorphic
functions; `ρ` is injective). The normalization and cocycle of `ȟ` follow from those of `u` and
injectivity of `ρ` (B.6).
-/

noncomputable section

namespace Cohesive

open TopologicalSpace Manifold CategoryTheory Opposite
open scoped ContDiff

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]

/-- Z3.d helper: two degree-0 forms with equal values are equal. -/
private theorem ext0_tw {V : Opens X} (a b : ↥(dolbeaultGrade E V 0))
    (h : ∀ y, evalForm0 E y a = evalForm0 E y b) : a = b := by
  refine Subtype.ext (Subtype.ext ?_)
  rw [form0_eq_funForm E a, form0_eq_funForm E b]
  congr 1
  funext y
  exact h y

/-- Z3.d helper: restriction of a restriction is the restriction along the composite. -/
private theorem dolbeaultRes_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (x : DolbeaultAlg E U) :
    dolbeaultRes E h₂ (dolbeaultRes E h₁ x) = dolbeaultRes E (h₂.trans h₁) x :=
  rfl

/-- Z3.d helper: the combined exponent `η_βγ + η_αβ − η_αγ` on `U_α ∩ U_β ∩ U_γ`. -/
private def epsTw {ι : Type} (U : ι → Opens X) (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (α β γ : ι) : dolbeaultGrade E (U α ⊓ U β ⊓ U γ) 0 :=
  (dolbeaultRes E (tri_le_bc (U₁ := U α) (U₂ := U β) (U₃ := U γ))).f0 (η β γ) +
    (dolbeaultRes E (inf_le_left (a := U α ⊓ U β) (b := U γ))).f0 (η α β) +
    -((dolbeaultRes E (tri_le_ac (U₁ := U α) (U₂ := U β) (U₃ := U γ))).f0 (η α γ))

/-- Z3.d helper: `∂̄ (a + b − c) = 0` if the three `∂̄`'s combine to `0`. -/
private theorem d_comb {W : Opens X} (a b c da db dc : DolbeaultAlg E W)
    (ha : GCDga.d (𝒜 := dolbeaultGrade E W) a = da)
    (hb : GCDga.d (𝒜 := dolbeaultGrade E W) b = db)
    (hc : GCDga.d (𝒜 := dolbeaultGrade E W) c = dc) (h : da + db + -dc = 0) :
    GCDga.d (𝒜 := dolbeaultGrade E W) (a + b + -c) = 0 := by
  rw [map_add, map_add, map_neg, ha, hb, hc]
  exact h

/-- Z3.d helper: restriction commutes with `∂̄`, in equation form. -/
private theorem d_res_eq {U V : Opens X} (h : V ≤ U) (x p : DolbeaultAlg E U)
    (hx : GCDga.d (𝒜 := dolbeaultGrade E U) x = p) :
    GCDga.d (𝒜 := dolbeaultGrade E V) (dolbeaultRes E h x) = dolbeaultRes E h p := by
  subst hx
  exact ((dolbeaultRes E h).map_d x).symm

/-- Z3.d helper: the hypothesis `d η_αβ = h⁰_β| − h⁰_α|`, as a `Prop` (elaborated once; the
coercions of `dolbeaultRes` are expensive to elaborate, so helpers take it as a bundle). -/
private def DEta {ι : Type} (U : ι → Opens X) (h0 : ∀ α, DolbeaultAlg E (U α))
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0) : Prop :=
  ∀ α β, GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β))
        ((η α β : dolbeaultGrade E (U α ⊓ U β) 0) : DolbeaultAlg E (U α ⊓ U β)) =
      dolbeaultRes E (inf_le_right (a := U α) (b := U β)) (h0 β) -
        dolbeaultRes E (inf_le_left (a := U α) (b := U β)) (h0 α)

/-- Z3.d helper: `∂̄ (η_βγ + η_αβ − η_αγ) = 0` on the triple intersection. -/
private theorem dbar_epsTw {ι : Type} (U : ι → Opens X) (h0 : ∀ α, DolbeaultAlg E (U α))
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (d_η : DEta E U h0 η) (α β γ : ι) :
    GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β ⊓ U γ))
      ((epsTw E U η α β γ : dolbeaultGrade E (U α ⊓ U β ⊓ U γ) 0) :
        DolbeaultAlg E (U α ⊓ U β ⊓ U γ)) = 0 := by
  show GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β ⊓ U γ))
    (dolbeaultRes E (tri_le_bc (U₁ := U α) (U₂ := U β) (U₃ := U γ)) (η β γ : DolbeaultAlg E _) +
    dolbeaultRes E (inf_le_left (a := U α ⊓ U β) (b := U γ)) (η α β : DolbeaultAlg E _) +
    -(dolbeaultRes E (tri_le_ac (U₁ := U α) (U₂ := U β) (U₃ := U γ)) (η α γ : DolbeaultAlg E _)))
      = 0
  refine d_comb E _ _ _ _ _ _
    (d_res_eq E (tri_le_bc (U₁ := U α) (U₂ := U β) (U₃ := U γ)) _ _ (d_η β γ))
    (d_res_eq E (inf_le_left (a := U α ⊓ U β) (b := U γ)) _ _ (d_η α β))
    (d_res_eq E (tri_le_ac (U₁ := U α) (U₂ := U β) (U₃ := U γ)) _ _ (d_η α γ)) ?_
  simp only [map_sub, dolbeaultRes_res]
  abel

/-- Z3.d helper: value of `exp α` as a unit. -/
private theorem eval_expUnit {V : Opens X} (a : dolbeaultGrade E V 0) (y : V) :
    evalForm0 E y ((expUnit E a : (↥(dolbeaultGrade E V 0))ˣ) : ↥(dolbeaultGrade E V 0)) =
      Complex.exp (evalForm0 E y a) :=
  evalForm0_expForm E a y

/-- Z3.d helper: value of `exp (−α)` as the inverse unit. -/
private theorem eval_expUnit_inv {V : Opens X} (a : dolbeaultGrade E V 0) (y : V) :
    evalForm0 E y (((expUnit E a)⁻¹ : (↥(dolbeaultGrade E V 0))ˣ) : ↥(dolbeaultGrade E V 0)) =
      Complex.exp (-evalForm0 E y a) := by
  show evalForm0 E y (expForm E (-a)) = _
  have hn : evalForm0 E y (-a) = - evalForm0 E y a := (evalForm0 E y).map_neg a
  rw [evalForm0_expForm, hn]

/-- Z3.d helper: evaluation commutes with negation. -/
private theorem eval_neg {V : Opens X} (a : dolbeaultGrade E V 0) (y : V) :
    evalForm0 E y (-a) = - evalForm0 E y a := (evalForm0 E y).map_neg a

/-- Z3.d helper: value of the exponent `ε_αβγ` at a point. -/
private theorem eval_epsTw {ι : Type} (U : ι → Opens X)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0) (α β γ : ι) (y : ↥(U α ⊓ U β ⊓ U γ)) :
    evalForm0 E y (epsTw E U η α β γ) =
      evalForm0 E (⟨y.1, tri_le_bc y.2⟩ : ↥(U β ⊓ U γ)) (η β γ) +
        evalForm0 E (⟨y.1, (inf_le_left : U α ⊓ U β ⊓ U γ ≤ U α ⊓ U β) y.2⟩ :
          ↥(U α ⊓ U β)) (η α β) -
          evalForm0 E (⟨y.1, tri_le_ac y.2⟩ : ↥(U α ⊓ U γ)) (η α γ) := by
  unfold epsTw
  rw [(evalForm0 E y).map_add, (evalForm0 E y).map_add, eval_neg]
  rw [evalForm0_res, evalForm0_res, evalForm0_res]
  ring

/-- Z3.d helper: the product `u_βγ u_αβ u_αγ⁻¹` (restricted) is `exp ε_αβγ`. -/
private theorem rhs_eq_exp {ι : Type} (U : ι → Opens X)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0) (α β γ : ι) :
    (dolbeaultRes E (tri_le_bc (U₁ := U α) (U₂ := U β) (U₃ := U γ))).f0
        ((expUnit E (η β γ) : (↥(dolbeaultGrade E (U β ⊓ U γ) 0))ˣ) :
          ↥(dolbeaultGrade E (U β ⊓ U γ) 0)) *
      (dolbeaultRes E (inf_le_left (a := U α ⊓ U β) (b := U γ))).f0
        ((expUnit E (η α β) : (↥(dolbeaultGrade E (U α ⊓ U β) 0))ˣ) :
          ↥(dolbeaultGrade E (U α ⊓ U β) 0)) *
      (dolbeaultRes E (tri_le_ac (U₁ := U α) (U₂ := U β) (U₃ := U γ))).f0
        (((expUnit E (η α γ))⁻¹ : (↥(dolbeaultGrade E (U α ⊓ U γ) 0))ˣ) :
          ↥(dolbeaultGrade E (U α ⊓ U γ) 0)) = expForm E (epsTw E U η α β γ) := by
  refine ext0_tw E _ _ fun y ↦ ?_
  rw [(evalForm0 E y).map_mul, (evalForm0 E y).map_mul, evalForm0_res, evalForm0_res,
    evalForm0_res, eval_expUnit, eval_expUnit, eval_expUnit_inv, evalForm0_expForm,
    eval_epsTw, ← Complex.exp_add, ← Complex.exp_add]
  congr 1

/-- Z3.d helper: `∂̄ (exp δ) = 0` if `∂̄ δ = 0`. -/
private theorem dbar_expForm_eq_zero {W : Opens X} (δ : dolbeaultGrade E W 0)
    (h : GCDga.d (𝒜 := dolbeaultGrade E W) (δ : DolbeaultAlg E W) = 0) :
    GCDga.d (𝒜 := dolbeaultGrade E W) ((expForm E δ : dolbeaultGrade E W 0) : DolbeaultAlg E W) =
      0 := by
  rw [dbar_expForm, h, mul_zero]

/-- Z3.d helper (F12): `exp ε` with `∂̄ ε = 0` is `ρ` of a holomorphic unit. -/
private theorem exists_unit_rho {W : Opens X} (ε : dolbeaultGrade E W 0)
    (hε : GCDga.d (𝒜 := dolbeaultGrade E W) (ε : DolbeaultAlg E W) = 0) :
    ∃ c : ((holSheaf E X).obj.obj (op W))ˣ,
      dolbeaultRhoU E W (c : (holSheaf E X).obj.obj (op W)) = expForm E ε := by
  have hn : GCDga.d (𝒜 := dolbeaultGrade E W) ((-ε : dolbeaultGrade E W 0) : DolbeaultAlg E W) =
      0 := by
    show GCDga.d (𝒜 := dolbeaultGrade E W) (-(ε : DolbeaultAlg E W)) = 0
    rw [map_neg, hε, neg_zero]
  obtain ⟨f, hf⟩ := exists_dolbeaultRhoU_of_dbar_eq_zero E (expForm E ε)
    (dbar_expForm_eq_zero E ε hε)
  obtain ⟨g, hg⟩ := exists_dolbeaultRhoU_of_dbar_eq_zero E (expForm E (-ε))
    (dbar_expForm_eq_zero E (-ε) hn)
  have hfg : f * g = 1 := by
    refine dolbeaultRhoU_injective E W ?_
    rw [map_mul, hf, hg, map_one]
    exact expForm_mul_neg E ε
  exact ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, hf⟩

/-- Z3.d helper: the value at `y ∈ W` of `ρ_W f` as a ring map `O_X(W) → ℂ`. -/
private def phiTw (W : Opens X) (y : W) : (holSheaf E X).obj.obj (op W) →+* ℂ :=
  (evalForm0 E y).comp (dolbeaultRhoU E W)

/-- Z3.d helper: `φ` is compatible with restriction of units. -/
private theorem phiTw_unitRes {W W' : Opens X} (h : W' ≤ W)
    (c : ((holSheaf E X).obj.obj (op W))ˣ) (y : W') :
    phiTw E W' y ((unitRes (holSheaf E X) h c : ((holSheaf E X).obj.obj (op W'))ˣ) :
      (holSheaf E X).obj.obj (op W')) = phiTw E W ⟨y, h y.2⟩ (c : (holSheaf E X).obj.obj (op W)) :=
  rfl

/-- Z3.d helper: the value of the cocycle `ȟ_αβγ` is `exp ε_αβγ(y)`. -/
private theorem phiTw_ch {ι : Type} (U : ι → Opens X) (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (ch : ∀ α β γ, ((holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ)
    (hch : ∀ α β γ, dolbeaultRhoU E (U α ⊓ U β ⊓ U γ)
      (ch α β γ : (holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ))) = expForm E (epsTw E U η α β γ))
    (α β γ : ι) (y : ↥(U α ⊓ U β ⊓ U γ)) :
    phiTw E (U α ⊓ U β ⊓ U γ) y
      (ch α β γ : (holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ))) =
      Complex.exp (evalForm0 E (⟨y.1, tri_le_bc y.2⟩ : ↥(U β ⊓ U γ)) (η β γ) +
        evalForm0 E (⟨y.1, (inf_le_left : U α ⊓ U β ⊓ U γ ≤ U α ⊓ U β) y.2⟩ :
          ↥(U α ⊓ U β)) (η α β) -
          evalForm0 E (⟨y.1, tri_le_ac y.2⟩ : ↥(U α ⊓ U γ)) (η α γ)) := by
  show evalForm0 E y (dolbeaultRhoU E _ (ch α β γ : (holSheaf E X).obj.obj _)) = _
  rw [hch, evalForm0_expForm, eval_epsTw]

/-- Z3.d helper (B.6): the cocycle condition for `ȟ`, by injectivity of `ρ` and values. -/
private theorem cocycle_aux {ι : Type} (U : ι → Opens X)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (ch : ∀ α β γ, ((holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ)
    (hch : ∀ α β γ, dolbeaultRhoU E (U α ⊓ U β ⊓ U γ)
      (ch α β γ : (holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ))) = expForm E (epsTw E U η α β γ))
    (α β γ δ : ι) (W : Opens X) (hα : W ≤ U α) (hβ : W ≤ U β) (hγ : W ≤ U γ) (hδ : W ≤ U δ) :
    unitRes (holSheaf E X) (le_inf (le_inf hβ hγ) hδ) (ch β γ δ) *
      (unitRes (holSheaf E X) (le_inf (le_inf hα hγ) hδ) (ch α γ δ))⁻¹ *
      unitRes (holSheaf E X) (le_inf (le_inf hα hβ) hδ) (ch α β δ) *
      (unitRes (holSheaf E X) (le_inf (le_inf hα hβ) hγ) (ch α β γ))⁻¹ = 1 := by
  refine Units.ext (dolbeaultRhoU_injective E W (ext0_tw E _ _ fun y ↦ ?_))
  show phiTw E W y _ = phiTw E W y _
  rw [Units.val_mul, Units.val_mul, Units.val_mul, map_mul, map_mul, map_mul,
    map_units_inv, map_units_inv, Units.val_one, map_one, phiTw_unitRes, phiTw_unitRes,
    phiTw_unitRes, phiTw_unitRes, phiTw_ch E U η ch hch, phiTw_ch E U η ch hch,
    phiTw_ch E U η ch hch, phiTw_ch E U η ch hch, ← Complex.exp_neg, ← Complex.exp_neg,
    ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  ring

/-- Z3.d helper (B.6): normalization of `ȟ`, from `η_αα = 0` and `η_βα = −η_αβ`. -/
private theorem normalized_aux {ι : Type} (U : ι → Opens X)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (η_self : ∀ α (y : ↥(U α ⊓ U α)), evalForm0 E y (η α α) = 0)
    (η_symm : ∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
      -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
        ↥(U α ⊓ U β)) (η α β))
    (ch : ∀ α β γ, ((holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ)
    (hch : ∀ α β γ, dolbeaultRhoU E (U α ⊓ U β ⊓ U γ)
      (ch α β γ : (holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ))) = expForm E (epsTw E U η α β γ))
    (α β γ : ι) (h : α = β ∨ β = γ ∨ α = γ) : ch α β γ = 1 := by
  refine Units.ext (dolbeaultRhoU_injective E _ (ext0_tw E _ _ fun y ↦ ?_))
  show phiTw E _ y _ = phiTw E _ y _
  rw [phiTw_ch E U η ch hch, Units.val_one, map_one]
  convert Complex.exp_zero using 2
  rcases h with rfl | rfl | rfl
  · have := η_self α ⟨y.1, (inf_le_left : U α ⊓ U α ⊓ U γ ≤ U α ⊓ U α) y.2⟩
    linear_combination this
  · have := η_self β ⟨y.1, tri_le_bc y.2⟩
    linear_combination this
  · have := η_symm α β ⟨y.1, tri_le_bc y.2⟩
    have h2 := η_self α ⟨y.1, tri_le_ac y.2⟩
    linear_combination this - h2

/-- Z3.d helper: `u_αα = exp η_αα = 1`. -/
private theorem u_self_aux {V : Opens X} (a : dolbeaultGrade E V 0)
    (h : ∀ y : V, evalForm0 E y a = 0) : expUnit E a = 1 := by
  refine Units.ext (ext0_tw E _ _ fun y ↦ ?_)
  show evalForm0 E y (expForm E a) = evalForm0 E y 1
  rw [evalForm0_expForm, h, (evalForm0 E y).map_one, Complex.exp_zero]

/-- Z3.d helper: `u_βα = (u_αβ|)⁻¹` from `η_βα = −η_αβ` pointwise. -/
private theorem u_symm_aux {ι : Type} (U : ι → Opens X)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (η_symm : ∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
      -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
        ↥(U α ⊓ U β)) (η α β)) (α β : ι) :
    expUnit E (η β α) =
      (Units.map (dolbeaultRes E (inf_comm (U β) (U α)).le).f0.toMonoidHom
        (expUnit E (η α β)))⁻¹ := by
  refine Units.ext (ext0_tw E _ _ fun y ↦ ?_)
  show evalForm0 E y (expForm E (η β α)) =
    evalForm0 E y ((dolbeaultRes E (inf_comm (U β) (U α)).le).f0 (expForm E (-(η α β))))
  rw [evalForm0_expForm, evalForm0_res, evalForm0_expForm, eval_neg, η_symm α β y]

/-- Z3.d helper: `∂̄ (exp a) = p · exp a` when `∂̄ a = p` (degree-0 elements are central). -/
private theorem d_u_aux {V : Opens X} (a : dolbeaultGrade E V 0) (p : DolbeaultAlg E V)
    (hp : GCDga.d (𝒜 := dolbeaultGrade E V) (a : DolbeaultAlg E V) = p) :
    GCDga.d (𝒜 := dolbeaultGrade E V) ((expUnit E a : (↥(dolbeaultGrade E V 0))ˣ) :
      ↥(dolbeaultGrade E V 0)) = p * ((expUnit E a : (↥(dolbeaultGrade E V 0))ˣ) :
      ↥(dolbeaultGrade E V 0)) := by
  show GCDga.d (𝒜 := dolbeaultGrade E V) (expForm E a : DolbeaultAlg E V) =
    p * (expForm E a : DolbeaultAlg E V)
  rw [dbar_expForm, hp]
  exact GCDga.central (dolbeaultGrade E V) (expForm E a).2 p

/-- Z3.d helper: the gluing units `u_αβ = exp η_αβ`, typed in the Dolbeault sheaf data. -/
private def uTw [T2Space X] [CompactSpace X] {ι : Type} (U : ι → Opens X)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0) (α β : ι) :
    (↥((dolbeaultPreData E X).toSheafData.D.𝒜 (U α ⊓ U β) 0))ˣ :=
  expUnit E (η α β)

/-- Z3.d helper (B.5–B.6): the cocycle `ȟ` with `ρ ȟ = exp ε`, normalized and satisfying the
cocycle condition. -/
private theorem exists_ch_aux {ι : Type} (U : ι → Opens X) (h0 : ∀ α, DolbeaultAlg E (U α))
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0) (d_η : DEta E U h0 η)
    (η_self : ∀ α (y : ↥(U α ⊓ U α)), evalForm0 E y (η α α) = 0)
    (η_symm : ∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
      -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
        ↥(U α ⊓ U β)) (η α β)) :
    ∃ ch : ∀ α β γ, ((holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ,
      (∀ α β γ, dolbeaultRhoU E (U α ⊓ U β ⊓ U γ)
        (ch α β γ : (holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ))) =
          expForm E (epsTw E U η α β γ)) ∧
      (∀ α β γ, (α = β ∨ β = γ ∨ α = γ) → ch α β γ = 1) ∧
      (∀ α β γ δ (W : Opens X) (hα : W ≤ U α) (hβ : W ≤ U β) (hγ : W ≤ U γ) (hδ : W ≤ U δ),
        unitRes (holSheaf E X) (le_inf (le_inf hβ hγ) hδ) (ch β γ δ) *
          (unitRes (holSheaf E X) (le_inf (le_inf hα hγ) hδ) (ch α γ δ))⁻¹ *
          unitRes (holSheaf E X) (le_inf (le_inf hα hβ) hδ) (ch α β δ) *
          (unitRes (holSheaf E X) (le_inf (le_inf hα hβ) hγ) (ch α β γ))⁻¹ = 1) := by
  have hex : ∀ α β γ, ∃ c : ((holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ)))ˣ,
      dolbeaultRhoU E (U α ⊓ U β ⊓ U γ) (c : (holSheaf E X).obj.obj (op (U α ⊓ U β ⊓ U γ))) =
        expForm E (epsTw E U η α β γ) :=
    fun α β γ ↦ exists_unit_rho E _ (dbar_epsTw E U h0 η d_η α β γ)
  choose ch hch using hex
  exact ⟨ch, hch, normalized_aux E U η η_self η_symm ch hch,
    fun α β γ δ W hα hβ hγ hδ ↦ cocycle_aux E U η ch hch α β γ δ W hα hβ hγ hδ⟩

/-- Z3.d helper: the Dolbeault sheaf data, as `DgaSheafData` (for readable field statements). -/
private abbrev sdTw (X : Type) [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ∞ X]
    [T2Space X] [CompactSpace X] : DgaSheafData X :=
  (dolbeaultPreData E X).toSheafData

/-- Z3.d helper: the field `d_u` of the twist datum, in the Dolbeault sheaf data. -/
private theorem d_u_field [T2Space X] [CompactSpace X] {ι : Type} (U : ι → Opens X)
    (h0 : ∀ α, DolbeaultAlg E (U α)) (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (d_η : DEta E U h0 η) (α β : ι) :
    GCDga.d (𝒜 := (sdTw E X).D.𝒜 (U α ⊓ U β))
      ((uTw E U η α β : ↥((sdTw E X).D.𝒜 (U α ⊓ U β) 0)) : (sdTw E X).D.A (U α ⊓ U β)) =
    ((sdTw E X).D.res (inf_le_right (a := U α) (b := U β)) (h0 β : (sdTw E X).D.A (U β)) -
      (sdTw E X).D.res (inf_le_left (a := U α) (b := U β)) (h0 α : (sdTw E X).D.A (U α))) *
      ((uTw E U η α β : ↥((sdTw E X).D.𝒜 (U α ⊓ U β) 0)) : (sdTw E X).D.A (U α ⊓ U β)) :=
  d_u_aux E (η α β) _ (d_η α β)

/-- Z3.d helper: the field `u_self` of the twist datum. -/
private theorem u_self_field [T2Space X] [CompactSpace X] {ι : Type} (U : ι → Opens X)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (η_self : ∀ α (y : ↥(U α ⊓ U α)), evalForm0 E y (η α α) = 0) (α : ι) :
    uTw E U η α α = 1 :=
  u_self_aux E (η α α) (η_self α)

/-- Z3.d helper: the field `u_symm` of the twist datum. -/
private theorem u_symm_field [T2Space X] [CompactSpace X] {ι : Type} (U : ι → Opens X)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (η_symm : ∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
      -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
        ↥(U α ⊓ U β)) (η α β)) (α β : ι) :
    uTw E U η β α =
      (Units.map ((sdTw E X).D.res (inf_comm (U β) (U α)).le).f0.toMonoidHom
        (uTw E U η α β))⁻¹ :=
  u_symm_aux E U η η_symm α β

/-- Z3.d helper: the hypothesis `d h⁰_α = h|U_α`, as a `Prop` (see `DEta`). -/
private def DH0 [T2Space X] [CompactSpace X] (h : DolbeaultClosed2 E X) {ι : Type}
    (U : ι → Opens X) (h0 : ∀ α, DolbeaultAlg E (U α)) : Prop :=
  ∀ α, GCDga.d (𝒜 := dolbeaultGrade E (U α)) (h0 α) = dolbeaultRes E (le_top (a := U α)) h.1

/-- Z3.d helper: assemble the twist datum from the cocycle `ȟ` and the primitives. -/
private theorem twistData_aux [T2Space X] [CompactSpace X] (h : DolbeaultClosed2 E X)
    (T : TwistCocycle (holSheaf E X))
    (h0 : ∀ α, DolbeaultAlg E (T.U α)) (h0_mem : ∀ α, h0 α ∈ dolbeaultGrade E (T.U α) 1)
    (d_h0 : DH0 E h T.U h0)
    (η : ∀ α β, dolbeaultGrade E (T.U α ⊓ T.U β) 0) (d_η : DEta E T.U h0 η)
    (η_self : ∀ α (y : ↥(T.U α ⊓ T.U α)), evalForm0 E y (η α α) = 0)
    (η_symm : ∀ α β (y : ↥(T.U β ⊓ T.U α)), evalForm0 E y (η β α) =
      -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
        ↥(T.U α ⊓ T.U β)) (η α β))
    (hch : ∀ α β γ, dolbeaultRhoU E (T.U α ⊓ T.U β ⊓ T.U γ)
        (T.ch α β γ : (holSheaf E X).obj.obj (op (T.U α ⊓ T.U β ⊓ T.U γ))) =
          expForm E (epsTw E T.U η α β γ)) :
    Nonempty (TwistData E X h) := by
  refine ⟨@TwistDatum.mk X _ (dolbeaultPreData E X).toSheafData h.1 T h0 h0_mem d_h0
    (uTw E T.U η) ?_ ?_ ?_ ?_⟩
  · exact d_u_field E T.U h0 η d_η
  · exact u_self_field E T.U η η_self
  · exact u_symm_field E T.U η η_symm
  · exact fun α β γ ↦ (hch α β γ).trans (rhs_eq_exp E T.U η α β γ).symm

/-- Z3.d helper: the content of `twistData_of_primitives`, with bundled hypotheses. -/
private theorem twistData_core [T2Space X] [CompactSpace X] (h : DolbeaultClosed2 E X)
    (ι : Type) [Fintype ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (h0 : ∀ α, DolbeaultAlg E (U α)) (h0_mem : ∀ α, h0 α ∈ dolbeaultGrade E (U α) 1)
    (d_h0 : DH0 E h U h0) (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0) (d_η : DEta E U h0 η)
    (η_self : ∀ α (y : ↥(U α ⊓ U α)), evalForm0 E y (η α α) = 0)
    (η_symm : ∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
      -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
        ↥(U α ⊓ U β)) (η α β)) :
    Nonempty (TwistData E X h) := by
  obtain ⟨ch, hch, hnorm, hcoc⟩ := exists_ch_aux E U h0 η d_η η_self η_symm
  exact twistData_aux E h
    { ι := ι, U := U, iSup_eq := hU, ch := ch, normalized := hnorm, cocycle := hcoc }
    h0 h0_mem d_h0 η d_η η_self η_symm hch

/-- **Z3.d (B.4–B.6).** Primitives as in `exists_cover_primitives` give a twist datum for `h`. -/
theorem twistData_of_primitives [T2Space X] [CompactSpace X] (h : DolbeaultClosed2 E X)
    (ι : Type) [Fintype ι] (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)
    (h0 : ∀ α, DolbeaultAlg E (U α)) (h0_mem : ∀ α, h0 α ∈ dolbeaultGrade E (U α) 1)
    (d_h0 : ∀ α, GCDga.d (𝒜 := dolbeaultGrade E (U α)) (h0 α) = dolbeaultRes E le_top h.1)
    (η : ∀ α β, dolbeaultGrade E (U α ⊓ U β) 0)
    (d_η : ∀ α β, GCDga.d (𝒜 := dolbeaultGrade E (U α ⊓ U β))
        ((η α β : dolbeaultGrade E (U α ⊓ U β) 0) : DolbeaultAlg E (U α ⊓ U β)) =
      dolbeaultRes E inf_le_right (h0 β) - dolbeaultRes E inf_le_left (h0 α))
    (η_self : ∀ α (y : ↥(U α ⊓ U α)), evalForm0 E y (η α α) = 0)
    (η_symm : ∀ α β (y : ↥(U β ⊓ U α)), evalForm0 E y (η β α) =
      -evalForm0 E (⟨y.1, Opens.mem_inf.2 ⟨(Opens.mem_inf.1 y.2).2, (Opens.mem_inf.1 y.2).1⟩⟩ :
        ↥(U α ⊓ U β)) (η α β)) :
    Nonempty (TwistData E X h) := by
  exact twistData_core E h ι U hU h0 h0_mem d_h0 η d_η η_self η_symm

end Cohesive
