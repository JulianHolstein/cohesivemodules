# Status of the blueprint items

One row per blueprint node (99 nodes; the items of `blueprint.md` §1–§5 and the item tables of
`blueprint-tr.md`, `blueprint-dg.md`, `blueprint-ll.md`, `blueprint-tw.md`). Read by
`scripts/blueprint_gen.py` (documentation plan B6) for the status colours of the dependency graph
and the `\leanok` marks.

- **proved**: formalized, no `sorry` (the statement and its proof).
- **stated**: statement formalized, proof open (none at present).
- **todo**: not formalized. A3.b′ (flatness of cohesive modules beyond degree 0) and A8 (the
  homotopy criterion) are used by no other item and by none of the main theorems.

H1 and H2 enter the conditional main statement as hypotheses; both are theorems (Z4.g, Z5.i).
Lean files are relative to `Cohesivemodules/`. Which declarations each item links to is in
`blueprint/lean-map.md`.

## Building the documentation

From the repository root, after `lake exe cache get` and `lake build`:

1. `python3 scripts/blueprint_decls.py`: dump of all project declarations with docstrings and
   dependencies to `blueprint/.cache/decls.jsonl` (a few minutes; rerun after any Lean change).
2. `python3 scripts/blueprint_gen.py sync`, then `check` (must report 0 errors and no cycles),
   then `build`: writes `blueprint/src/chapters/*.tex` from the Markdown blueprints, this file
   and `lean-map.md`. Lean is the arbiter of the dependency edges.
3. `leanblueprint web` (output `blueprint/web/`, including the dependency graph
   `dep_graph_document.html`) and `leanblueprint pdf` (LuaLaTeX; `blueprint/print/print.pdf`).
   Requires [leanblueprint](https://github.com/PatrickMassot/leanblueprint).
4. API documentation: `lake build Cohesivemodules:docs` in `docbuild/` (doc-gen4; output
   `docbuild/.lake/build/doc`).
5. Serve the repository root over HTTP and open `index.html`; the `\lean` links of the blueprint
   point to `../../docbuild/.lake/build/doc`.

The workflow `.github/workflows/pages.yml` runs steps 3–4 on GitHub for each release (the
generated TeX of step 2 is committed), with the PDF built in TeX Live 2023, and publishes the
result at <https://julianholstein.github.io/cohesivemodules/>; there the API docs are served
from `api/` and the links to them are rewritten.

## Layer A (algebra)

| Item | Lean files | Status |
| --- | --- | --- |
| A1 Bounded gc dga | `Algebra/Dga.lean` | proved |
| A2 Connections | `Algebra/Connection.lean` | proved |
| A3 Cohesive modules | `Algebra/CohesiveDef.lean`, `Algebra/Cohesive.lean` | proved |
| A3.b′ Flatness in all degrees | — | todo |
| A4 Hom complexes | `Algebra/CohesiveDef.lean`, `Algebra/Cohesive.lean` | proved |
| A5 Ho(P_A) | `Algebra/CohesiveDef.lean` | proved |
| A6 Form-degree filtration | `Algebra/Filtration.lean` | proved |
| A7 Finite filtration comparison | `Algebra/Filtration.lean` | proved |
| A8 Homotopy criterion | — | todo |
| A9 Base change | `Algebra/BaseChange.lean` | proved |
| A10 Modules from complexes | `Algebra/BaseChange.lean` | proved |
| A11 Lifting theorem | `Algebra/Lifting.lean`, `Algebra/LiftingCone.lean` | proved |
| A12 Total quasi-isomorphism | `Algebra/TotalQuasiIso.lean` | proved |
| A13 Bridge to Block's convention | `Algebra/BlockDef.lean`, `Algebra/BlockBridge.lean` | proved |

## Layer S (sheaves)

| Item | Lean files | Status |
| --- | --- | --- |
| S1 Fine sheaves | `Sheaf/Fine.lean` | proved |
| S2 Γ exact over fine | `Sheaf/Fine.lean` | proved |
| S3 Acyclic complexes | `Sheaf/Acyclic.lean` | proved |
| S3.b Soft sheaves | `Sheaf/Soft.lean` | proved |
| S4 Projective modules | `Sheaf/Projective.lean` | proved |
| S5 Restriction, j_! | `Sheaf/Restriction.lean` | proved |
| S6 Locality | `Sheaf/Restriction.lean` | proved |
| S7 Hom sheaves | `Sheaf/Hom/Basic.lean`, `Sheaf/Hom.lean`, `Sheaf/HomAcyclic.lean`, `Sheaf/HomAction.lean` | proved |
| S8 Tensor, K-flat | `Sheaf/Flat.lean`, `Sheaf/Resolution.lean`, `Sheaf/FlatResolution.lean`, `Sheaf/BaseChange.lean` | proved |
| S9 Perfect complexes | `Sheaf/PerfectDef.lean`, `Sheaf/Perfect.lean` | proved |
| S10 Globalization | `Sheaf/Globalize.lean` | proved |
| S11 Derived wiring | `Sheaf/Derived.lean` | proved |

## Layer C (comparison)

| Item | Lean files | Status |
| --- | --- | --- |
| C0 Resolving data | `Comparison/SetupDef.lean`, `Comparison/Setup.lean` | proved |
| C1 Functor J | `Algebra/BaseChangeResDef.lean`, `Comparison/AlphaDef.lean`, `Comparison/FunctorDef.lean`, `Comparison/AlphaSheaf.lean`, `Comparison/AlphaOver.lean` | proved |
| C2 J lands in perfect complexes | `Comparison/PerfectAux.lean`, `Comparison/PerfectLoc.lean`, `Comparison/Perfect.lean` | proved |
| C3 Hom sheaves of cohesive modules | `Comparison/HomSheaf.lean` | proved |
| C4 Full faithfulness | `Comparison/FullyFaithful*.lean` | proved |
| C5 Essential surjectivity | `Comparison/EssSurjAux.lean`, `Comparison/EssSurj.lean` | proved |
| C6 Comparison theorem | `Comparison/Equivalence.lean` | proved |
| C7 Explicit model T(K) | `Algebra/TotMap.lean`, `Algebra/BaseChangeLift.lean`, `Comparison/Model*.lean` | proved |

## Layer F (Dolbeault forms) and the hypotheses

| Item | Lean files | Status |
| --- | --- | --- |
| F1 Realification | `Forms/Realify.lean` | proved |
| F2 Fibre Λ^{0,q} | `Forms/Fibre.lean` | proved |
| F3 ∂̄ on opens of E | `Forms/Dbar.lean` | proved |
| F4 ∂̄∂̄ = 0 | `Forms/Dbar.lean` | proved |
| F5 Product | `Forms/Product.lean` | proved |
| F6 Leibniz | `Forms/Leibniz.lean` | proved |
| F7 Holomorphic pullback | `Forms/Pullback.lean` | proved |
| F8 Cauchy–Riemann | `Forms/CauchyRiemann.lean` | proved |
| F9 Sheaves 𝒜^{0,q} | `Forms/SheafPred.lean`, `Forms/Sheaf.lean` | proved |
| F10 Dolbeault dga | `Forms/SheafDef.lean` | proved |
| F11 Fineness, local freeness | `Forms/Dolbeault.lean` | proved |
| F12 Holomorphic functions | `Forms/Holomorphic.lean`, `Forms/Dolbeault.lean` | proved |
| H1 Dolbeault–Grothendieck lemma | `Hypotheses.lean` (statement), `Forms/DolbeaultGrothendieck.lean` (proof, Z4.g) | proved |
| H2 Local gauge lemma | `Hypotheses.lean` (statement), `Forms/LocalGauge.lean` (proof, Z5.i) | proved |
| F14 Fields of C0 | `BlockFunctorDef.lean`, `Main.lean` | proved |
| F15 Main theorem, conditional | `BlockFunctorDef.lean`, `Main.lean` | proved |
| M Main statement, conditional | `StatementsConditional.lean`, `Main.lean` | proved |

## Z2: triangulated structure on Ho(P_A)

| Item | Lean files | Status |
| --- | --- | --- |
| Z2.a Shift | `Algebra/Shift.lean` | proved |
| Z2.b Shift on Ho(P_A) | `Algebra/ShiftHoP.lean` | proved |
| Z2.c Products, zero object | `Algebra/TotProd.lean`, `Algebra/HoPZero.lean` | proved |
| Z2.d Cone | `Algebra/Cone.lean` | proved |
| Z2.e Maps of cones | `Algebra/ConeMaps.lean` | proved |
| Z2.f Pretriangulated | `Algebra/ConeTriangle.lean`, `Algebra/ConeRotate.lean`, `Algebra/ConeShift.lean`, `Algebra/Pretriangulated.lean` | proved |
| Z2.g Triangulated (octahedron) | `Algebra/ConeComp.lean`, `Algebra/ConeCompAux.lean`, `Algebra/Triangulated.lean` | proved |

## Z4: proof of H1

| Item | Lean files | Status |
| --- | --- | --- |
| Z4.a Cauchy kernel | `Analysis/CauchyKernel.lean` | proved |
| Z4.b Cauchy–Pompeiu | `Analysis/Pompeiu.lean` | proved |
| Z4.c Parametric solver | `Analysis/CauchySolve.lean` | proved |
| Z4.d Contraction | `Forms/Contraction.lean` | proved |
| Z4.e Flat lemma | `Forms/FlatGrothendieck.lean` | proved |
| Z4.f Chart forms | `Forms/ChartForm.lean` | proved |
| Z4.g H1 | `Forms/DolbeaultGrothendieck.lean` | proved |
| Z4.h Corollary | `MainH1.lean` | proved |

## Z5: proof of H2

| Item | Lean files | Status |
| --- | --- | --- |
| Z5.a Kernel estimate | `Analysis/KernelEstimate.lean` | proved |
| Z5.b Solver derivatives | `Analysis/CauchySolveDeriv.lean` | proved |
| Z5.c Gauge solver | `Forms/GaugeSolve.lean` | proved |
| Z5.d Fibre operators | `Forms/FibreOps.lean` | proved |
| Z5.e Superconnection algebra | `Forms/Superconnection.lean` | proved |
| Z5.f Induction | `Forms/GaugeInduction.lean` | proved |
| Z5.g Local freeness | `Forms/LocalFree.lean` | proved |
| Z5.h Frame model | `Algebra/Frame.lean`, `Forms/FrameModel.lean` | proved |
| Z5.i Local gauge lemma | `Algebra/FrameIso.lean`, `Algebra/FrameBaseChange.lean`, `Forms/GaugeMatrix.lean`, `Forms/ChartTransport.lean`, `Forms/LocalGauge.lean` | proved |
| Z5.j Main theorem | `Statements.lean`, `MainH2.lean` | proved |

## Z3: the twisted theorem

| Item | Lean files | Status |
| --- | --- | --- |
| Z3.a Curved dga, `DgaSheafData` | `Algebra/CurvedDga.lean`, `Comparison/CurvedPresheaf.lean` | proved |
| Z3.b Gauge | `Algebra/Gauge.lean` | proved |
| Z3.c Curved Dolbeault algebra, twist data | `Forms/CurvedDolbeault.lean`, `Sheaf/Twisted/CocycleDef.lean`, `Comparison/TwistDatumDef.lean`, `Comparison/TwistDatumBasic.lean` | proved |
| Z3.d Twist data exist | `Forms/ExpForm.lean`, `Forms/TwistCover.lean`, `Forms/TwistFromPrimitives.lean`, `Forms/TwistExists.lean` | proved |
| Z3.e Local gauge lemma, curved and over opens | `Forms/CurvedRestrictDef.lean`, `Forms/CurvedLL.lean`, `Forms/LocalFreeOpen.lean`, `Forms/LocalGaugeOpen.lean` | proved |
| Z3.f Restriction over an open | `Sheaf/RestrOverDef.lean`, `Sheaf/RestrOver.lean` | proved |
| Z3.g Twisted sheaves | `Sheaf/Twisted/Def.lean`, `Sheaf/Twisted/Basic.lean` | proved |
| Z3.h Abelian category | `Sheaf/Twisted/{SecHom, SubQuot, Preadditive, Kernels, Cokernels, Biprod, Abelian}.lean` | proved |
| Z3.i Injectives | `Sheaf/Twisted/{SecRes, CocycleBasic, Pushforward, PushAdj, Injective}.lean` | proved |
| Z3.j Perfectness | `Sheaf/Twisted/PerfectDef.lean`, `Sheaf/Twisted/PerfectOver.lean`, `Sheaf/Twisted/Perfect.lean` | proved |
| Z3.k Gluing | `Sheaf/Twisted/{GlueSec, Glue, GlueEquiv, Rescale}.lean` | proved |
| Z3.l Generators | `Sheaf/Twisted/{ExtZero, ExtTw, ExtTwAdj, FlatResolution}.lean` | proved |
| Z3.l′ Base change | `Sheaf/BaseChangeRestrOver.lean`, `Sheaf/Twisted/BaseChange.lean` | proved |
| Z3.m C1 over `DgaSheafData` | `Comparison/SheafDataAlphaDef.lean`, `Comparison/SheafDataAlpha.lean`, `Comparison/SheafDataMap.lean` | proved |
| Z3.n The functor `J_T` | `Comparison/TwistedFunctorAux.lean`, `Comparison/TwistedFunctorDef.lean` | proved |
| Z3.o Local identification | `Comparison/TwistedLocal.lean` | proved |
| Z3.p J_T lands in perfect complexes | `Comparison/AlphaOverRestr.lean`, `Comparison/TwistedPerfect.lean`, `Comparison/TwistedPerfectAbstract.lean` | proved |
| Z3.q Curved Hom sheaves | `Comparison/CurvedHomSheaf.lean`, `Comparison/CurvedHomRetract.lean` | proved |
| Z3.r Twisted Hom sheaves | `Sheaf/Twisted/{HomTw, HomComplexTw, HomSectionsTw, HomSoftTw, HomRestrOver, HomRestrTw, InjectiveRestr}.lean` | proved |
| Z3.s Full faithfulness of J_T | `Comparison/TwistedPsiAux.lean`, `Comparison/TwistedPsi.lean`, `Comparison/TwistedFF*.lean`, `Comparison/TwistedFullyFaithful*.lean` | proved |
| Z3.t Curved model | `Comparison/TwistedUntwist.lean`, `Comparison/TwistedModel.lean` | proved |
| Z3.u Essential surjectivity of J_T | `Comparison/TwistedEssSurjPrep.lean`, `Comparison/ModelFilBase.lean`, `Comparison/TwistedXi.lean`, `Comparison/TwistedLiftAux.lean`, `Comparison/TwistedLift.lean`, `Comparison/TwistedEssSurj.lean` | proved |
| Z3.v Assembly | `TwistedBlockFunctorDef.lean`, `StatementsTwisted.lean`, `MainTwisted.lean`, `Comparison/GaugeSheaf.lean`, `Comparison/GaugeExactIso.lean` | proved |
