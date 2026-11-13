import Cohesivemodules.Sheaf.Hom

set_option linter.style.header false

/-!
# Sections of `𝓗om` and post-composition

Blueprint item S7 (§4), used in C4 step 5: under `homComplexSectionsEquiv`, the sections of the
functoriality map `homComplexMap₂ g` are post-composition with `g|X`.
-/

namespace Cohesive

open CategoryTheory Opposite CochainComplex.HomComplex

variable {C : Type} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{0}}

/-- **S7.** Over `X`, the section map of `homComplexMap₂ g : 𝓗om(K, L) ⟶ 𝓗om(K, L')` is
post-composition with `g|X`: for a section `s` of `𝓗om(K, L)ⁿ` over `X`, read as a cochain
`K|X → L|X` (`homComplexSectionsEquiv`), its image is that cochain composed with `g|X`. -/
theorem homComplexSectionsEquiv_homComplexMap₂ (hR : IsCommSheaf R)
    (K : CochainComplex (Mod R) ℤ) {L L' : CochainComplex (Mod R) ℤ} (g : L ⟶ L') (n : ℤ)
    (X : C) (s : ((homSheafComplex hR K L).X n).val.obj (op X)) :
    homComplexSectionsEquiv hR K L' n X
        ((((homComplexMap₂ hR K g).f n).val.app (op X)).hom s) =
      (homComplexSectionsEquiv hR K L n X s).comp (Cochain.ofHom ((overC X).map g))
        (add_zero n) := by
  funext T
  rw [homComplexSectionsEquiv_apply]
  have h1 := congrArg (fun g ↦ ((g.val.app (op X)).hom s))
    (Limits.Pi.map_π (fun T : Triplet n ↦ homPost hR (K.X T.p) (g.f T.q)) T)
  have hl := Cochain.comp_zero_cochain_v (homComplexSectionsEquiv hR K L n X s)
    (Cochain.ofHom ((overC X).map g)) T.p T.q T.hpq
  refine Eq.trans ?_ hl.symm
  rw [Cochain.ofHom_v]
  refine (congrArg (homSheafSectionsEquiv hR (K.X T.p) (L'.X T.q) X) h1).trans ?_
  show _ = homComplexSectionsEquiv hR K L n X s T ≫ (g.f T.q).over X
  rw [homComplexSectionsEquiv_apply]
  rfl

end Cohesive
