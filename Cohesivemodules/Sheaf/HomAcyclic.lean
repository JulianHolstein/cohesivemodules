import Cohesivemodules.Sheaf.HomAcyclic.Bounded

set_option linter.style.header false

/-!
# S7.b, S7.c: Hom complexes and quasi-isomorphisms

Blueprint items S7.b and S7.c (§3), on a space (`Opens X`). Split of blueprint §7's `Hom.lean`
(size only); the definitions are in `Sheaf/Hom.lean`.

* S7.b `𝓗om(P, -)` preserves quasi-isomorphisms for `P` strictly perfect.
* S7.c `𝓗om(C, I)` is acyclic for `C` acyclic and `I` bounded below with injective terms;
  hence `𝓗om(-, I)` preserves quasi-isomorphisms.

This file holds the main theorems; the helpers are split off for size into
* `Sheaf/HomAcyclic/HomGood.lean`: precomposition on Hom complexes, sections of `𝓗om(K, I)`,
  the predicate `HomGood` and its closure properties;
* `Sheaf/HomAcyclic/Bounded.lean`: `HomGood` for bounded complexes of summands of finite free
  modules.
-/

universe v u

noncomputable section

namespace Cohesive

open CategoryTheory Opposite Limits

variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

open TopologicalSpace CochainComplex.HomComplex
open scoped ZeroObject
/-- **S7.b.** For `P` strictly perfect, `𝓗om(P, -)` preserves quasi-isomorphisms. Proof: `P` is
bounded with terms summands of `Rᵐ`, and `𝓗om(Rᵐ, L) ≅ Lᵐ`; induction on the length of `P`
(stupid truncations, cones). -/
theorem quasiIso_homComplexMap₂ (hR : IsCommSheaf R) {P : CochainComplex (Mod R) ℤ}
    (hP : IsStrictlyPerfect P) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') [QuasiIso g] :
    QuasiIso (homComplexMap₂ hR P g) := by
  obtain ⟨⟨a, b, hGE, hLE⟩, hfree⟩ := hP
  have : P.IsStrictlyLE (a + ((b - a).toNat : ℕ)) :=
    CochainComplex.isStrictlyLE_of_le P b _ (by lia)
  exact HomGood.of_bounded hR (b - a).toNat a P hfree L L' g

/-- **S7.c.** For `I` bounded below with injective terms, `𝓗om(C, I)` is acyclic whenever `C` is
acyclic: sections over `V` are `Hom^•(C|V, I|V)`, `I|V` is bounded below with injective terms
(S5.c), hence K-injective (`CochainComplex.isKInjective_of_injective`), and `C|V` is acyclic
(S5.a); then S6 (sectionwise). -/
theorem acyclic_homComplex (hR : IsCommSheaf R) {C' I : CochainComplex (Mod R) ℤ}
    (hC : C'.Acyclic) (n : ℤ) [I.IsStrictlyGE n] [∀ i, Injective (I.X i)] :
    (homSheafComplex hR C' I).Acyclic := by
  have hsec : ∀ V : (Opens X)ᵒᵖ, (((SheafOfModules.evaluation.{0} R V).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (homSheafComplex hR C' I)).Acyclic := by
    intro V
    obtain ⟨V⟩ := V
    intro i
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by lia⟩
    rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 1 + 1) (by simp) (by simp)]
    refine (ShortComplex.moduleCat_exact_iff _).2 fun s hs => ?_
    have hFacyc : ((overC V).obj C').Acyclic := fun j => (hC j).map (restr R V)
    have : ∀ i, Injective (((overC V).obj I).X i) := fun i => restr_injective R V (I.X i)
    have : ((overC V).obj I).IsStrictlyGE n :=
      (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi =>
        (restr R V).map_isZero (CochainComplex.isZero_of_isStrictlyGE I n i hi)
    have : ((overC V).obj I).IsKInjective :=
      CochainComplex.isKInjective_of_injective ((overC V).obj I) n
    have hz : δ (m + 1) (m + 1 + 1) (homComplexSectionsEquiv hR C' I (m + 1) V s) = 0 := by
      rw [← homComplexSectionsEquiv_d hR C' I (m + 1) V s]
      exact (map_eq_zero_iff _ (AddEquiv.injective _)).2 hs
    obtain ⟨y, hy⟩ := coboundary_of_cocycle _ _ hFacyc (m + 1) m rfl _ hz
    refine ⟨(homComplexSectionsEquiv hR C' I m V).symm y, ?_⟩
    apply (homComplexSectionsEquiv hR C' I (m + 1) V).injective
    have hd := homComplexSectionsEquiv_d hR C' I m V
      ((homComplexSectionsEquiv hR C' I m V).symm y)
    rw [AddEquiv.apply_symm_apply] at hd
    exact hd.trans hy
  have hq : QuasiIso (0 : homSheafComplex hR C' I ⟶ 0) := by
    refine quasiIso_of_sectionwise _ fun V => ⟨fun i => ?_⟩
    refine (quasiIsoAt_iff_exactAt' _ i ?_).2 (hsec V i)
    exact HomologicalComplex.acyclic_of_isZero _
      (Functor.map_isZero _ (isZero_zero _)) i
  intro i
  exact (quasiIsoAt_iff_exactAt' (0 : homSheafComplex hR C' I ⟶ 0) i
    (HomologicalComplex.acyclic_of_isZero _ (isZero_zero _) i)).1 (hq.quasiIsoAt i)


/-- **S7.c, for quasi-isomorphisms.** For `I` bounded below with injective terms, `𝓗om(-, I)`
maps quasi-isomorphisms to quasi-isomorphisms (S7.c on the mapping cone). -/
theorem quasiIso_homComplexMap₁ (hR : IsCommSheaf R) {K K' : CochainComplex (Mod R) ℤ}
    (f : K' ⟶ K) [QuasiIso f] {I : CochainComplex (Mod R) ℤ} (n : ℤ) [I.IsStrictlyGE n]
    [∀ i, Injective (I.X i)] : QuasiIso (homComplexMap₁ hR f I) := by
  refine quasiIso_of_sectionwise _ fun V => ?_
  obtain ⟨V⟩ := V
  have hq : QuasiIso ((overC V).map f) :=
    inferInstanceAs (QuasiIso (((restr R V).mapHomologicalComplex (ComplexShape.up ℤ)).map f))
  have : ∀ i, Injective (((overC V).obj I).X i) := fun i => restr_injective R V (I.X i)
  have : ((overC V).obj I).IsStrictlyGE n :=
    (CochainComplex.isStrictlyGE_iff _ n).2 fun i hi =>
      (restr R V).map_isZero (CochainComplex.isZero_of_isStrictlyGE I n i hi)
  have : ((overC V).obj I).IsKInjective :=
    CochainComplex.isKInjective_of_injective ((overC V).obj I) n
  have hpre := quasiIso_homComplexPrecomp' ((overC V).map f) ((overC V).obj I)
  have hsq : (secHomIso hR K I V).hom ≫
      homComplexPrecomp ((overC V).map f) ((overC V).obj I) =
      ((forget₂ (ModuleCat ↑(R.obj.obj (op V))) AddCommGrpCat).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (((SheafOfModules.evaluation.{0} R (op V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (homComplexMap₁ hR f I)) ≫ (secHomIso hR K' I V).hom := by
    refine HomologicalComplex.hom_ext _ _ fun m ↦ ?_
    ext z : 2
    funext T
    show (Cochain.ofHom ((overC V).map f)).comp (homComplexSectionsEquiv hR K I m V z)
      (zero_add m) T = homComplexSectionsEquiv hR K' I m V
        (((homComplexMap₁ hR f I).f m).val.app (op V) z) T
    rw [homComplexSectionsEquiv_apply]
    have h1 := congrArg (fun g ↦ ((g.val.app (op V)).hom z))
      (Limits.Pi.map_π (fun T : Triplet m ↦ homPre hR (f.f T.p) (I.X T.q)) T)
    have hl := Cochain.zero_cochain_comp_v (Cochain.ofHom ((overC V).map f))
      (homComplexSectionsEquiv hR K I m V z) T.p T.q T.hpq
    refine hl.trans (Eq.trans ?_ (congrArg (homSheafSectionsEquiv hR (K'.X T.p) (I.X T.q) V)
      h1.symm))
    rw [Cochain.ofHom_v]
    show (f.f T.p).over V ≫ homComplexSectionsEquiv hR K I m V z T = _
    erw [homComplexSectionsEquiv_apply]
    rfl
  refine (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat ↑(R.obj.obj (op V))) AddCommGrpCat)).1 ?_
  exact (quasiIso_iff_of_arrow_mk_iso _
    (homComplexPrecomp ((overC V).map f) ((overC V).obj I))
    (Arrow.isoMk (secHomIso hR K I V) (secHomIso hR K' I V) hsq)).2 hpre

end Cohesive
