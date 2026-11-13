# Numbering table for the sources

Rule (post-mortem §2.1): a citation in a docstring or blueprint is written only after looking
it up here. Kind and number must match. Sources without a table are cited by section only.

## [A] P. Antweiler, arXiv 2411.19595v1 (`references/Antweiler.pdf`)

Extracted 12 Nov 2026 with `mutool draw -F txt`; one line per numbered item (kind, number, first
words). Chapters 3, 4 and 7 (the ones cited in this project).

```
Definition 3.1.1. A dg-category (= differential graded category) over K is a category
Definition 3.1.2. Let C be a dg-category. To C we can associate its homotopy category
Definition 3.1.3. A (non-negatively graded) cdg-category (= curved differential graded
Remark 3.1.4. In the following we will always assume that the occuring cdg-categories
Remark 3.1.5. There is a notion of curved A∞-algebras and curved A∞-categories
Example 3.1.6. Let G be a group and set K := Z. We define the cdg-category of
Definition 3.1.7. Let C be a cdg-category.
Example 3.1.8. Rep∞(G) is sufficiently Maurer-Cartan but not Maurer-Cartan. One
Definition 3.1.10. We define the dg-category C0 to be the full subcategory of C con-
Example 3.1.11. For a group G, the objects of the dg-category of Rep0
Definition 3.1.12. Let C be a cdg-category. We define its associated dg-category of
Remark 3.1.13. The above construction appears in a similar way in [BK91].
Remark 3.1.14. We defined C0 as a full subcategory of C. Equivalently, C0 can be
Example 3.1.15. We again consider the cdg-category Rep∞(G) and its associated dg-
Definition 3.2.1. Let C and D be cdg-categories. An A∞-functor F : C →D assigns to
Definition 3.2.2. Let F, G : C →D be A∞-functors of cdg-categories. An A∞-natural
Definition 3.2.3. Let F, G : C →D be A∞-functors of cdg-categories and let
Definition 3.2.4. Let F : C →D be a proper A∞-functor of cdg-categories. We define
Lemma 3.2.5. In the setting of the previous definition Tw(F) indeed defines an A∞-
Definition 3.2.6. Let η : F →G be a proper A∞-natural transformation of proper
Lemma 3.2.7. In the setting of the previous definition, we have that Tw(η) : Tw(F) ⇒
Remark 3.2.8. A∞-functors and A∞-natural transformations of cdg-categories (or
Definition 3.3.1. Let C be a cdg-category. Note that by definition C is an additive
Definition 3.3.2. Let C be a cdg-category. We define a decreasing filtration on the
Proposition 3.3.3. Let C be a sufficiently Maurer-Cartan cdg-category which is split.
Proposition 3.3.4. Let C be a cdg-category. Let (E∗, E) be some object in Tw(C) and let
Lemma 3.3.5. Let C be a cdg-category. Let f ∈Hom0(F ∗, E∗) be a closed morphism
Proposition 3.3.6. Let F : C →D be a proper A∞-functor between cdg-categories such
Remark 3.3.7. Let (E∗, E) be an object of a dg-category Tw(C) associated to a cdg-
Proposition 3.3.8. Let F : C →D be a proper A∞-functor between cdg-categories such
Theorem 3.3.9. Let F : C →D be a proper A∞-functor between (non-negatively graded)
Definition 4.0.2. Let h be a closed 2-form on M. We define the cdg-category P(M)pre[h].
Lemma 4.0.3. P(M)pre[h] is a Maurer-Cartan cdg-category.
Remark 4.0.4. The above category can also be defined as follows. Let A∗be a non-
Definition 4.0.5. Let S be a simplicial set. Let H be a 2-cocycle H ∈C2(S; K∗). We
Lemma 4.0.6. Loc(S)pre[H] is indeed a sufficiently Maurer-Cartan cdg-category.
Definition 4.0.7. The associated dg-category of H-curved ∞-local systems on S will be
Definition 4.1.1. A diffeological space X is a set X endowed with a family of maps
Definition 4.1.2. A map between diffeological spaces f : X →Y is called smooth if for
Remark 4.1.3. Any smooth manifold M (possibly with corners) is a diffeological space.
Definition 4.1.4. A smooth vector bundle on a diffeological space X is a family of
Definition 4.1.5. Let X be a diffeological space and E a vector bundle on M. An
Remark 4.2.1. In the following proposition we will define holonomy forms. They will
Proposition 4.2.2. Let E1, E2, ... be a finite or countable family of vector bundles to-
Lemma 4.2.3. hol satisfies the following equations
Definition 4.2.4. Let x0, x1 ∈M. We denote by PM(x0, x1) the diffeological subspace
Corollary 4.2.5. The pullback holx0,x1
Lemma 4.2.6. The following identity holds
Definition 4.3.2. A collection of maps �n : I × In →∆n+1 is called admissible it
Remark 4.3.3. Igusa [Igu09] defined certain families of paths I × In →∆n+1, fulfilling
Lemma 4.3.5. Each �n is smooth on the subsets [
Theorem 4.3.6. There exists an admissible collection of maps �n : I × In →∆n+1.
Definition 4.4.1. In the following, we will consider smooth maps σ : ∆n+1 →M.
Lemma 4.4.2. Let σ : ∆n+1 →M be smooth. The following identity holds
Remark 4.4.3. We can do the same calculation as above for PT σ instead of holσ
Definition 4.4.4. We define an A∞-functor RH(M)pre[h] : P(M)pre[h] →Loc(M)pre[H],
Theorem 4.4.5. RH(M)pre[h] is indeed a proper A∞-functor of cdg-categories.
Lemma 4.5.1. P(M)pre[h] and Loc(M)pre[H] are split.
Lemma 4.5.2. Let (E, P) be an object of Loc(M)0[H] for H(σ) = e
Lemma 4.5.3. RH(M)0[h] : P(M)0[h] →Loc(M)0[H] is essentially surjective.
Lemma 4.5.4. There is an isomorphism of complexes
Corollary 4.5.5. The functor
Theorem 4.5.6. The induced A∞-functor
Definition 4.6.1. Let M and N be manifolds (possibly with boundary, or even diffe-
Definition 4.6.2. Let h be a closed 2-form on M and ω a 1-form. We define a dg-functor
Definition 4.6.3. Consider the inclusions ι1 : M →M × I, x �→(x, 1) and ι0 : M →
Lemma 4.6.4. ηpre and (ηpre)−1 are inverse to one another.
Corollary 4.6.5. Let f, g be smooth homotopic maps of manifolds f, g : M →N via
Corollary 4.6.6. Let f be a smooth homotopy equivalence of manifolds f : M →N.
Definition 7.1.1. A ˇh-twisted sheaf of left A∗cdg-modules M∗is given by the following
Definition 7.1.2. We define the dg-category (A∗, h)-Modˇh. Its objects are ˇh-twisted
Remark 7.1.3. If we have another representative ˇη with [ˇη] = [ˇh], where ˇη possibly
Remark 7.1.4. Given an object M∗and an x ∈X we can consider the stalks (Mα)x
Definition 7.1.5. Let X and Y be topological spaces. Let OY be a sheaf of k-algebras
Lemma 7.1.6. Let R be a sheaf of k-algebras. The abelian category R-Modˇh
Definition 7.1.7. Let R be a sheaf of commutative k-algebras. Let ω1 and ω2 be twists
Definition 7.1.8. Let A∗be a sheaf of cdg-algebras. We say that A∗exponentiates if
Example 7.2.1. There are two main examples satisfying the above assumptions. The
Definition 7.2.2. Note that d ◦exp ◦ρ = 0. As 0 →R →A0 →A1 is exact, we obtain
Definition 7.2.3. The dg-functor J : (A∗, h)-Mod →R-Mod
Remark 7.2.4. Similarly, we can define a functor in the other direction R-Mod
Definition 7.2.5. We define the full dg-subcategory (A∗, h)-Modcoh of (A∗, h)-Mod
Definition 7.2.6. Similarly we define the full dg-subcategory (A∗, h)-Modcoh of (A∗, h)-
Lemma 7.2.7. There is a dg-equivalence (A∗, h)-Modcoh →(A∗, h)-Modcoh.
Lemma 7.2.8. Let M∗be an acyclic, bounded below complex of sheaves of abelian groups
Lemma 7.2.9. Let C be an abelian category. Let B∗be a bounded above complex con-
Lemma 7.2.10. Let C be an abelian category. Consider a quasi-isomorphism of com-
Definition 7.2.11. Let Q be a sheaf of rings.
Lemma 7.2.12. Let Y be Hausdorff paracompact topological space of finite covering
Corollary 7.2.13. Let Y be as above and let S be a sheaf of rings on Y . Let M be a
Corollary 7.2.14. Let Y be as before and let S be a sheaf of rings on Y . Let M be
Lemma 7.2.15. Let S be a soft sheaf of commutative rings on any topological space Y .
Lemma 7.2.16. Let S be a soft sheaf of commutative rings on a paracompact Hausdorff
Lemma 7.2.17. J factors through DB
Proposition 7.2.18. J : H0((A∗, h)-Modcoh) →DB
Proposition 7.2.19. J : H0((A∗, h)-Modcoh) →DB
Theorem 7.2.20. Let R be a sheaf of k-algebras and let R →A∗be a quasi-isomorphism
Definition 7.3.1. Let R be a commutative ring and Y a topological space. Let M∗
Lemma 7.3.2. Let R be a PID and Y a connected, locally path connected topological
Theorem 7.3.3. Let M be a real, connected smooth manifold. Let K = R or K = C
Lemma 7.4.1. Let M∗be a globally bounded perfect complex over OX. Then the coho-
Corollary 7.4.2. Let X be a compact, complex manifold and M∗a complex of OX-
Theorem 7.4.3. Let X be a complex, connected smooth manifold. Let h ∈Ω0,2
```

Not numbered items: "Assumptions" of §7.2 are a list (items 1–7) before Example 7.2.1.

## [B], [CHL]

Not yet tabulated (blueprint v1.3 checked the blueprint citations; docstrings not re-checked).
