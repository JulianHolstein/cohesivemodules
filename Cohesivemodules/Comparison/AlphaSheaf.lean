import Cohesivemodules.Comparison.AlphaDef
import Cohesivemodules.Comparison.AlphaSheafAux

set_option linter.style.header false

/-!
# C1.a: `α(M)^n` is a sheaf

Blueprint item C1.a (§4), [B, §4.1], [A, Lemma 7.2.7 (proof)]. For pre-resolving data `P` and a
cohesive module `M` over `𝒜(X)`, the presheaf of `O`-modules `α(M)^n` (`sheafOfPre`) satisfies the
sheaf condition.

Proof outline (blueprint C1.a): `α(M)^n(V) ≅ ⊕_p 𝒜^{n-p}(V) ⊗_{𝒜⁰(X)} Q^p` (cancel `𝒜⁰(V)`),
finitely many `p` (`M.bounded`); each `Q^p` is a direct summand of `𝒜⁰(X)^m` (finitely generated
projective), so `𝒜^{n-p}(V) ⊗ Q^p` is a summand of `𝒜^{n-p}(V)^m`, compatibly with restriction;
`V ↦ 𝒜^q(V)` is a sheaf of abelian groups by `P.glue` and `P.degree_local`, and finite sums and
summands (images of idempotent endomorphisms) of sheaves are sheaves. Neither fineness nor local
freeness is used.
-/

noncomputable section

namespace Cohesive

open CategoryTheory Opposite TopologicalSpace

variable {X : Type} [TopologicalSpace X]

namespace PreResolvingData

variable (P : PreResolvingData X) (M : CohesiveModule P.𝒜X)

/-- **C1.a** `α(M)^n` is a sheaf (of abelian groups, hence of `O`-modules). [B, §4.1]. -/
theorem isSheaf_sheafOfPre (n : ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (P.sheafOfPre M n).presheaf :=
  P.isSheaf_sheafOfPre_aux M n

end PreResolvingData

end Cohesive
