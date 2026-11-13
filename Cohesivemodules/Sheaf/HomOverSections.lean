import Cohesivemodules.Sheaf.HomOver
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

set_option linter.style.header false

/-!
# Sections of `𝓗om` on an over-site, elementwise

Blueprint item S7 (§4), in the form used by C4 step 3 (`quasiIso_Φ`):
* `homSectionsIso`: the complex of sections of `𝓗om(K, I)` over `V` (as abelian groups) is
  Mathlib's Hom complex `HomComplex (K|V) (I|V)`;
* `homComplexOverIso_map₁_sections`: the section over `Y : Over X` of
  `(𝓗om restriction iso) ≫ f^*`, read as a cochain, evaluated at `Y` on `m`, is the original
  section evaluated on `f(m)`.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite CochainComplex.HomComplex

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{0}] [J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  {R : Sheaf J RingCat.{0}}

/-- **S7.** The complex of sections of `𝓗om(K, I)` over `V` (as abelian groups) is Mathlib's Hom
complex `HomComplex (K|V) (I|V)`: in degree `n`, `homComplexSectionsEquiv`; the differentials
match by `homComplexSectionsEquiv_d`. -/
def homSectionsIso (hR : IsCommSheaf R) (K I : CochainComplex (Mod R) ℤ) (V : C) :
    ((forget₂ (ModuleCat ↑(R.obj.obj (op V))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (((SheafOfModules.evaluation.{0} R (op V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (homSheafComplex hR K I)) ≅
      CochainComplex.HomComplex ((overC V).obj K) ((overC V).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (homComplexSectionsEquiv hR K I n V).toAddCommGrpIso) (fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      ext z
      exact (homComplexSectionsEquiv_d hR K I i V z).symm)

/-- `homSectionsIso` in degree `n` is `homComplexSectionsEquiv` (rfl). -/
theorem homSectionsIso_hom_f (hR : IsCommSheaf R) (K I : CochainComplex (Mod R) ℤ) (V : C)
    (n : ℤ) (s : ((homSheafComplex hR K I).X n).val.obj (op V)) :
    ((homSectionsIso hR K I V).hom.f n).hom s = homComplexSectionsEquiv hR K I n V s := rfl

/-- **S7, restriction then precomposition, elementwise.** For `f : K' ⟶ K|X` on the over-site
of `X`, a section `s` of `𝓗om(K, L)ⁿ` over `Y.left` (`Y : Over X`) and `T : Triplet n`: the
`(p, q)` component of the image of `s` under `𝓗om(K, L)|X ≅ 𝓗om(K|X, L|X) ⟶ 𝓗om(K', L|X)`,
evaluated at `Y` on `m ∈ K'^p(Y)`, is the `(p, q)` component of `s` evaluated at `Y.left` on
`f(m)`. -/
theorem homComplexOverIso_map₁_sections (hR : IsCommSheaf R) (K L : CochainComplex (Mod R) ℤ)
    (X : C) {K' : CochainComplex (Mod (R.over X)) ℤ} (f : K' ⟶ (overC X).obj K) (n : ℤ)
    (Y : Over X) (s : ((homSheafComplex hR K L).X n).val.obj (op Y.left)) (T : Triplet n)
    (m : (K'.X T.p).val.obj (op Y)) :
    ((homComplexSectionsEquiv (hR.over X) K' ((overC X).obj L) n Y
        ((((homComplexOverIso hR K L X).hom ≫ homComplexMap₁ (hR.over X) f _).f n).val.app
          (op Y) s) T).val.app (op (Over.mk (𝟙 Y)))).hom m =
      ((homComplexSectionsEquiv hR K L n Y.left s T).val.app (op (Over.mk (𝟙 Y.left)))).hom
        (((f.f T.p).val.app (op Y)).hom m) := by
  have hπ : ∀ (m : ℤ) (T' : Triplet m),
      ((homComplexOverIso hR K L X).hom.f m) ≫ Limits.Pi.π (fun T : Triplet m ↦
        homSheaf (hR.over X) (((overC X).obj K).X T.p) (((overC X).obj L).X T.q)) T' =
      (SheafOfModules.overFunctor.{0} R X).map (Limits.Pi.π (fun T : Triplet m ↦
        homSheaf hR (K.X T.p) (L.X T.q)) T') ≫
        (homSheafOverIso hR (K.X T'.p) (L.X T'.q) X).hom := by
    intro m T'
    show (Limits.piComparison (SheafOfModules.overFunctor.{0} R X)
        (fun T : Triplet m ↦ homSheaf hR (K.X T.p) (L.X T.q)) ≫ Limits.Pi.map
      (fun T : Triplet m ↦ (homSheafOverIso hR (K.X T.p) (L.X T.q) X).hom)) ≫ _ = _
    rw [Category.assoc]
    erw [Limits.Pi.map_π]
    rw [← Category.assoc, Limits.piComparison_comp_π]
  rw [homComplexSectionsEquiv_apply, homComplexSectionsEquiv_apply]
  have h1 := congrArg (fun g ↦ ((g.val.app (op Y)).hom
      (((homComplexOverIso hR K L X).hom.f n).val.app (op Y) s)))
    (Limits.Pi.map_π (fun T : Triplet n ↦ homPre (hR.over X) (f.f T.p)
      (((overC X).obj L).X T.q)) T)
  have h2 := congrArg (fun g ↦ ((g.val.app (op Y)).hom s)) (hπ n T)
  simp only at h1 h2
  refine (congrArg (fun φ ↦ (φ.val.app (op (Over.mk (𝟙 Y)))).hom m)
    (congrArg (homSheafSectionsEquiv (hR.over X) (K'.X T.p) (((overC X).obj L).X T.q) Y)
      h1)).trans ?_
  exact congrArg (fun a : ((homSheaf (hR.over X) (((overC X).obj K).X T.p)
    (((overC X).obj L).X T.q)).val.obj (op Y)) ↦
      (((a : ((((overC X).obj K).X T.p).over Y ⟶ (((overC X).obj L).X T.q).over Y)).val.app
        (op (Over.mk (𝟙 Y)))).hom (((f.f T.p).val.app (op Y)).hom m))) h2

end Cohesive
