import Cohesivemodules.Sheaf.SoftBasic

set_option linter.style.header false

/-!
# S3.b: soft sheaves (part 2 of 2)

Split from `Sheaf/Soft.lean` for size;
continues `Sheaf/SoftBasic.lean`.
-/

noncomputable section
namespace Cohesive
open CategoryTheory Opposite TopologicalSpace Limits
variable {X : Type} [TopologicalSpace X] {R : RingSheaf X}

/-- Sections of a kernel are computed sectionwise. -/
private lemma kernel_sections' {M N : Mod R} (g : M ⟶ N) (V : Opens X) :
    ∀ s : M.val.obj (op V), g.val.app (op V) s = 0 → ∃ u, (kernel.ι g).val.app (op V) u = s := by
  have hex := ShortComplex.exact_kernel g
  have hex' := hex.map_of_mono_of_preservesKernel (SheafOfModules.evaluation.{0} R (op V))
    inferInstance inferInstance
  exact (ShortComplex.moduleCat_exact_iff _).1 hex'

/-- S3.b(iv): the map `Kⁱ ⟶ Zⁱ⁺¹` onto the cycles. -/
def toCyc (K : CochainComplex (Mod R) ℤ) (i : ℤ) :
    K.X i ⟶ kernel (K.d (i + 1) (i + 1 + 1)) :=
  kernel.lift _ (K.d i (i + 1)) (K.d_comp_d _ _ _)

/-- S3.b(iv): `Kⁱ ⟶ Zⁱ⁺¹ ⟶ Kⁱ⁺¹` is the differential. -/
lemma toCyc_ι (K : CochainComplex (Mod R) ℤ) (i : ℤ) :
    toCyc K i ≫ kernel.ι (K.d (i + 1) (i + 1 + 1)) = K.d i (i + 1) :=
  kernel.lift_ι _ _ _

/-- S3.b(iv): the short complex `0 → Zⁱ → Kⁱ → Zⁱ⁺¹ → 0`. -/
def cycSC (K : CochainComplex (Mod R) ℤ) (i : ℤ) : ShortComplex (Mod R) :=
  ShortComplex.mk (kernel.ι (K.d i (i + 1))) (toCyc K i) (by
    rw [← cancel_mono (kernel.ι (K.d (i + 1) (i + 1 + 1))), Category.assoc, toCyc_ι,
      kernel.condition, zero_comp])

/-- S3.b(iv): for an acyclic complex, `0 → Zⁱ → Kⁱ → Zⁱ⁺¹ → 0` is short exact. -/
lemma cycSC_shortExact (K : CochainComplex (Mod R) ℤ) (hK : K.Acyclic) (i : ℤ) :
    (cycSC K i).ShortExact := by
  have hepi : Epi (toCyc K i) := by
    have h := (HomologicalComplex.exactAt_iff' K i (i + 1) (i + 1 + 1)
      ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl))
      ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel (i + 1) (i + 1 + 1) from
        rfl))).1 (hK (i + 1))
    exact (ShortComplex.exact_iff_epi_kernel_lift _).1 h
  have hmono : Mono (cycSC K i).f := show Mono (kernel.ι (K.d i (i + 1))) from inferInstance
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ ?_)
  intro A k hk
  have key : ∀ (k : A ⟶ K.X i), k ≫ toCyc K i = 0 → k ≫ K.d i (i + 1) = 0 := by
    intro k hk
    rw [← toCyc_ι, ← Category.assoc, hk, zero_comp]
  exact ⟨kernel.lift _ k (key k hk), kernel.lift_ι _ _ _⟩

/-- S3.b(iv): the cycle sheaves of a bounded-below acyclic complex with soft terms are soft. -/
lemma cyc_soft [CompactSpace X] [T2Space X] (K : CochainComplex (Mod R) ℤ) (n : ℤ)
    [K.IsStrictlyGE n] (hK : K.Acyclic) (hsoft : ∀ i, IsSoft (K.X i)) (i : ℤ) :
    IsSoft (kernel (K.d i (i + 1))) := by
  have hlow : ∀ j, j < n → IsSoft (kernel (K.d j (j + 1))) := fun j hj =>
    IsSoft.of_isZero (IsZero.of_mono (kernel.ι _) (K.isZero_of_isStrictlyGE n j hj))
  have hstep : ∀ j, IsSoft (kernel (K.d j (j + 1))) →
      IsSoft (kernel (K.d (j + 1) (j + 1 + 1))) :=
    fun j h => IsSoft.of_shortExact (cycSC_shortExact K hK j) h (hsoft j)
  refine Int.inductionOn' (motive := fun i => IsSoft (kernel (K.d i (i + 1)))) i n ?_ ?_ ?_
  · have h := hstep (n - 1) (hlow (n - 1) (by omega))
    have e : n - 1 + 1 = n := by omega
    rw [e] at h
    exact h
  · intro j _ h
    exact hstep j h
  · intro j hj _
    exact hlow (j - 1) (by omega)

/-- **S3.b(iv).** On compact Hausdorff `X`, a bounded-below acyclic complex of `R`-modules with
soft terms has acyclic complex of global sections: the cycle sheaves are soft by induction from
the bottom ((iii)), and global cycles lift by (ii). -/
theorem acyclic_globalSections_of_isSoft [CompactSpace X] [T2Space X]
    {K : CochainComplex (Mod R) ℤ} (n : ℤ) [K.IsStrictlyGE n] (hK : K.Acyclic)
    (hsoft : ∀ i, IsSoft (K.X i)) :
    (((globalSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have key : ∀ j : ℤ, ((((globalSections R).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K).ExactAt (j + 1)) := by
    intro j
    refine (HomologicalComplex.exactAt_iff' _ j (j + 1) (j + 1 + 1)
      ((ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl))
      ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel (j + 1) (j + 1 + 1) from
        rfl))).2 ?_
    rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    obtain ⟨z', hz'⟩ := kernel_sections' (K.d (j + 1) (j + 1 + 1)) ⊤ z hz
    obtain ⟨w, hw⟩ := surjective_globalSections_of_isSoft (cycSC_shortExact K hK j)
      (cyc_soft K n hK hsoft j) z'
    refine ⟨w, ?_⟩
    have hw' : (toCyc K j).val.app (op ⊤) w = z' := hw
    have h1 : (K.d j (j + 1)).val.app (op ⊤) w =
        (kernel.ι (K.d (j + 1) (j + 1 + 1))).val.app (op ⊤) ((toCyc K j).val.app (op ⊤) w) :=
      congr(ModuleCat.Hom.hom ($(congrArg (fun k => k.val.app (op ⊤)) (toCyc_ι K j).symm)) w)
    show (K.d j (j + 1)).val.app (op ⊤) w = z
    rw [h1, hw']
    exact hz'
  intro i
  have := key (i - 1)
  rwa [sub_add_cancel] at this

/-- **S3.b(iv), for quasi-isomorphisms.** On compact Hausdorff `X`, `Γ` maps a quasi-isomorphism
between bounded-below complexes with soft terms to a quasi-isomorphism (the mapping cone is
bounded below, with soft terms `Kⁱ⁺¹ ⊞ Lⁱ`). Used in C4 step 4. -/
theorem quasiIso_globalSections_of_isSoft [CompactSpace X] [T2Space X]
    {K L : CochainComplex (Mod R) ℤ} (n : ℤ) [K.IsStrictlyGE n] [L.IsStrictlyGE n]
    (hKs : ∀ i, IsSoft (K.X i)) (hLs : ∀ i, IsSoft (L.X i)) (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((globalSections R).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hc := (quasiIso_iff_acyclic_mappingCone f).1 inferInstance
  rw [quasiIso_iff_acyclic_mappingCone]
  have hge : (CochainComplex.mappingCone f).IsStrictlyGE (n - 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨K.isZero_of_isStrictlyGE n (i + 1) (by omega),
      L.isZero_of_isStrictlyGE n i (by omega)⟩
  have h := acyclic_globalSections_of_isSoft (n - 1) hc fun i =>
    IsSoft.of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm
      ((hKs (i + 1)).biprod (hLs i))
  intro i
  exact (h i).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso f (globalSections R))

end Cohesive
