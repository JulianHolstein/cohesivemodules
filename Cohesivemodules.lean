-- This module serves as the root of the `Cohesivemodules` library.
-- Project files are imported here as they are created (blueprint §7).
import Cohesivemodules.Algebra.Dga
import Cohesivemodules.Analysis.CauchyKernel
import Cohesivemodules.Analysis.Pompeiu
import Cohesivemodules.Analysis.CauchySolve
import Cohesivemodules.Analysis.CauchySolveDeriv
import Cohesivemodules.Analysis.KernelEstimate
import Cohesivemodules.Forms.Contraction
import Cohesivemodules.Forms.ChartForm
import Cohesivemodules.Forms.FibreOps
import Cohesivemodules.Forms.GaugeSolve
import Cohesivemodules.Forms.Superconnection
import Cohesivemodules.Forms.GaugeInduction
import Cohesivemodules.Forms.LocalFree
import Cohesivemodules.Algebra.Frame
import Cohesivemodules.Forms.FrameModel
import Cohesivemodules.Algebra.FrameIso
import Cohesivemodules.Algebra.FrameBaseChange
import Cohesivemodules.Forms.GaugeMatrix
import Cohesivemodules.Forms.ChartTransport
import Cohesivemodules.Forms.LocalGauge
import Cohesivemodules.Algebra.ShiftHoP
import Cohesivemodules.Algebra.HomShift
import Cohesivemodules.Algebra.UnitModule
import Cohesivemodules.Algebra.UnitCohomology
import Cohesivemodules.Algebra.TotProd
import Cohesivemodules.Algebra.HoPZero
import Cohesivemodules.Algebra.Cone
import Cohesivemodules.Algebra.ConeMaps
import Cohesivemodules.Algebra.ConeTriangle
import Cohesivemodules.Algebra.ConeRotate
import Cohesivemodules.Algebra.ConeShift
import Cohesivemodules.Algebra.Pretriangulated
import Cohesivemodules.Algebra.ConeCompAux
import Cohesivemodules.Algebra.ConeComp
import Cohesivemodules.Algebra.ConeCompTriangle
import Cohesivemodules.Algebra.Triangulated
import Cohesivemodules.Hubs.CohesiveModules
import Cohesivemodules.Algebra.CurvedDga
import Cohesivemodules.Comparison.CurvedPresheaf
import Cohesivemodules.Forms.CurvedDolbeault
import Cohesivemodules.Sheaf.Twisted.CocycleDef
import Cohesivemodules.Comparison.TwistDatumDef
import Cohesivemodules.Comparison.TwistDatumBasic
import Cohesivemodules.ChecksTwisted
import Cohesivemodules.Algebra.Gauge
import Cohesivemodules.Forms.LocalFreeOpen
import Cohesivemodules.Forms.LocalGaugeOpen
import Cohesivemodules.Forms.ExpForm
import Cohesivemodules.Forms.TwistCover
import Cohesivemodules.Forms.TwistFromPrimitives
import Cohesivemodules.Forms.TwistExists
import Cohesivemodules.Forms.CurvedRestrictDef
import Cohesivemodules.Forms.CurvedLL
import Cohesivemodules.Sheaf.RestrOverDef
import Cohesivemodules.Sheaf.RestrOver
import Cohesivemodules.Sheaf.Twisted.Def
import Cohesivemodules.Sheaf.Twisted.Basic
import Cohesivemodules.Sheaf.Twisted.SecHom
import Cohesivemodules.Sheaf.Twisted.SubQuot
import Cohesivemodules.Sheaf.Twisted.Preadditive
import Cohesivemodules.Sheaf.Twisted.Kernels
import Cohesivemodules.Sheaf.Twisted.Cokernels
import Cohesivemodules.Sheaf.Twisted.Biprod
import Cohesivemodules.Sheaf.Twisted.Abelian
import Cohesivemodules.Sheaf.Twisted.SecRes
import Cohesivemodules.Sheaf.Twisted.CocycleBasic
import Cohesivemodules.Sheaf.Twisted.Pushforward
import Cohesivemodules.Sheaf.Twisted.PushAdj
import Cohesivemodules.Sheaf.Twisted.Injective
import Cohesivemodules.Sheaf.Twisted.PerfectDef
import Cohesivemodules.Sheaf.Twisted.PerfectOver
import Cohesivemodules.Sheaf.Twisted.Perfect
import Cohesivemodules.Sheaf.Twisted.GlueSec
import Cohesivemodules.Sheaf.Twisted.Glue
import Cohesivemodules.Sheaf.Twisted.GlueEquiv
import Cohesivemodules.Sheaf.Twisted.Rescale
import Cohesivemodules.Sheaf.Twisted.ExtZero
import Cohesivemodules.Sheaf.Twisted.ExtTw
import Cohesivemodules.Sheaf.Twisted.ExtTwAdj
import Cohesivemodules.Sheaf.Twisted.FlatResolution
import Cohesivemodules.Sheaf.BaseChangeRestrOver
import Cohesivemodules.Sheaf.Twisted.BaseChange
import Cohesivemodules.Comparison.TwistedUntwist
import Cohesivemodules.Comparison.TwistedModel
import Cohesivemodules.Comparison.TwistedCurvedAux
import Cohesivemodules.Comparison.TwistedCurvedComp
import Cohesivemodules.Comparison.TwistedCurvedGlue
import Cohesivemodules.Comparison.TwistedCurvedModel
import Cohesivemodules.Comparison.TwistedEssSurjPrep
import Cohesivemodules.Comparison.ModelFilBase
import Cohesivemodules.Comparison.TwistedXi
import Cohesivemodules.Comparison.TwistedLiftAux
import Cohesivemodules.Comparison.TwistedLift
import Cohesivemodules.Comparison.TwistedEssSurj
import Cohesivemodules.Comparison.SheafDataAlphaDef
import Cohesivemodules.Comparison.SheafDataAlpha
import Cohesivemodules.Comparison.SheafDataMap
import Cohesivemodules.Comparison.TwistedFunctorAux
import Cohesivemodules.Comparison.TwistedFunctorDef
import Cohesivemodules.Comparison.TwistedLocal
import Cohesivemodules.Comparison.AlphaOverRestr
import Cohesivemodules.Comparison.TwistedPerfect
import Cohesivemodules.Comparison.TwistedPerfectAbstract
import Cohesivemodules.Comparison.CurvedHomSheaf
import Cohesivemodules.Sheaf.Twisted.HomTw
import Cohesivemodules.Sheaf.Twisted.InjectiveRestr
import Cohesivemodules.Sheaf.Twisted.HomRestrOver
import Cohesivemodules.Sheaf.Twisted.HomComplexTw
import Cohesivemodules.Sheaf.Twisted.HomSectionsTw
import Cohesivemodules.Sheaf.Twisted.HomSoftTw
import Cohesivemodules.Sheaf.Twisted.HomRestrTw
import Cohesivemodules.Comparison.TwistedPsiAux
import Cohesivemodules.Comparison.TwistedPsi
import Cohesivemodules.Comparison.TwistedFullyFaithful
import Cohesivemodules.Comparison.TwistedFullyFaithfulDolbeault
import Cohesivemodules.ChecksTwistedFF
import Cohesivemodules.Forms.DolbeaultCohomology
import Cohesivemodules.Statements
import Cohesivemodules.MainH2
import Cohesivemodules.TwistedBlockFunctorDef
import Cohesivemodules.StatementsTwisted
import Cohesivemodules.MainTwisted
import Cohesivemodules.ChecksTwistedK8
import Cohesivemodules.ChecksK7
import Cohesivemodules.Forms.FlatGrothendieck
import Cohesivemodules.Forms.DolbeaultGrothendieck
import Cohesivemodules.Algebra.Connection
import Cohesivemodules.Algebra.CohesiveDef
import Cohesivemodules.Algebra.GeneratorsDef
import Cohesivemodules.Algebra.GenHomDef
import Cohesivemodules.Algebra.Cohesive
import Cohesivemodules.Algebra.Filtration
import Cohesivemodules.Algebra.BaseChangeDef
import Cohesivemodules.Algebra.FromComplexDef
import Cohesivemodules.Algebra.BaseChangeHomDef
import Cohesivemodules.Algebra.BaseChangeResDef
import Cohesivemodules.Algebra.BaseChangeResAPI
import Cohesivemodules.Algebra.BaseChangeX0
import Cohesivemodules.Algebra.BaseChangeExt
import Cohesivemodules.Algebra.BaseChangeFunctor
import Cohesivemodules.Algebra.BaseChangeComp
import Cohesivemodules.Algebra.BaseChange
import Cohesivemodules.Algebra.TotMap
import Cohesivemodules.Algebra.Shift
import Cohesivemodules.Algebra.BaseChangeLift
import Cohesivemodules.Algebra.DegreeZero
import Cohesivemodules.Algebra.LiftingHomT
import Cohesivemodules.Algebra.LiftingLead
import Cohesivemodules.Algebra.Lifting
import Cohesivemodules.Algebra.LiftingConeGens
import Cohesivemodules.Algebra.LiftingCone
import Cohesivemodules.Algebra.TotalQuasiIsoFil
import Cohesivemodules.Algebra.TotalQuasiIsoGr
import Cohesivemodules.Algebra.TotalQuasiIso
import Cohesivemodules.Algebra.BlockDef
import Cohesivemodules.Algebra.BlockBridgeSwap
import Cohesivemodules.Algebra.BlockBridge
import Cohesivemodules.Algebra.QuasiIsoElem
import Cohesivemodules.Algebra.HomAlongTBasic
import Cohesivemodules.Algebra.HomAlongT
import Cohesivemodules.Forms.Realify
import Cohesivemodules.Forms.FibreDef
import Cohesivemodules.Forms.Fibre
import Cohesivemodules.Forms.DbarDef
import Cohesivemodules.Forms.Dbar
import Cohesivemodules.Forms.CauchyRiemann
import Cohesivemodules.Forms.ProductDef
import Cohesivemodules.Forms.Product
import Cohesivemodules.Forms.Leibniz
import Cohesivemodules.Forms.PullbackDef
import Cohesivemodules.Forms.Pullback
import Cohesivemodules.Sheaf.Basic
import Cohesivemodules.Sheaf.FineDef
import Cohesivemodules.Sheaf.Fine
import Cohesivemodules.Sheaf.Acyclic
import Cohesivemodules.Sheaf.SoftBasic
import Cohesivemodules.Sheaf.Soft
import Cohesivemodules.Sheaf.ProjectiveBasic
import Cohesivemodules.Sheaf.Projective
import Cohesivemodules.Sheaf.RestrictionBasic
import Cohesivemodules.Sheaf.Restriction
import Cohesivemodules.Sheaf.PerfectDef
import Cohesivemodules.Sheaf.Perfect
import Cohesivemodules.Sheaf.Hom.Basic
import Cohesivemodules.Sheaf.HomSheafComplex
import Cohesivemodules.Sheaf.Hom
import Cohesivemodules.Sheaf.HomAction
import Cohesivemodules.Sheaf.HomAcyclic.HomGood
import Cohesivemodules.Sheaf.HomAcyclic.Bounded
import Cohesivemodules.Sheaf.HomAcyclic
import Cohesivemodules.Sheaf.HomOver
import Cohesivemodules.Sheaf.HomOverSections
import Cohesivemodules.Sheaf.HomSectionsMap
import Cohesivemodules.Sheaf.RestrEval
import Cohesivemodules.Sheaf.Globalize.Cone
import Cohesivemodules.Sheaf.Globalize.LocalFreeBasic
import Cohesivemodules.Sheaf.Globalize.LocalFree
import Cohesivemodules.Sheaf.Globalize.Locally
import Cohesivemodules.Sheaf.Globalize.Approx
import Cohesivemodules.Sheaf.GlobalizeEpi
import Cohesivemodules.Sheaf.Globalize
import Cohesivemodules.Sheaf.Derived
import Cohesivemodules.Sheaf.Flat.TensorLoc
import Cohesivemodules.Sheaf.Flat.TotAuxBasic
import Cohesivemodules.Sheaf.Flat.TotAux
import Cohesivemodules.Sheaf.Flat.Brutal
import Cohesivemodules.Sheaf.RingOfDef
import Cohesivemodules.Sheaf.Flat.Tensor
import Cohesivemodules.Sheaf.Flat.KFlat
import Cohesivemodules.Sheaf.FlatBasic
import Cohesivemodules.Sheaf.Flat
import Cohesivemodules.Sheaf.Resolution
import Cohesivemodules.Sheaf.FlatResolution
import Cohesivemodules.Sheaf.BaseChangeBasic
import Cohesivemodules.Sheaf.BaseChange
import Cohesivemodules.Sheaf.TensorSections
import Cohesivemodules.Forms.SheafPred
import Cohesivemodules.Forms.ChartAuxBasic
import Cohesivemodules.Forms.ChartAux
import Cohesivemodules.Forms.SheafBasic
import Cohesivemodules.Forms.Sheaf
import Cohesivemodules.Forms.SheafDef
import Cohesivemodules.Forms.Holomorphic
import Cohesivemodules.Forms.DolbeaultFine
import Cohesivemodules.Forms.DolbeaultFree
import Cohesivemodules.Forms.Dolbeault
import Cohesivemodules.Hypotheses
import Cohesivemodules.Comparison.SetupDef
import Cohesivemodules.Comparison.AlphaDef
import Cohesivemodules.Comparison.AlphaSheafAux
import Cohesivemodules.Comparison.AlphaSheaf
import Cohesivemodules.Comparison.FunctorDef
import Cohesivemodules.Comparison.SetupAux
import Cohesivemodules.Comparison.Setup
import Cohesivemodules.Comparison.AlphaOverAux
import Cohesivemodules.Comparison.AlphaOver
import Cohesivemodules.Comparison.ModelDual
import Cohesivemodules.Comparison.ModelTSheaf
import Cohesivemodules.Comparison.ModelDef
import Cohesivemodules.Comparison.ModelCritSite
import Cohesivemodules.Comparison.ModelCritCoord
import Cohesivemodules.Comparison.ModelCritFil
import Cohesivemodules.Comparison.ModelCrit
import Cohesivemodules.Comparison.ModelFilG0
import Cohesivemodules.Comparison.ModelFil
import Cohesivemodules.Comparison.ModelBC
import Cohesivemodules.Comparison.ModelConnNab
import Cohesivemodules.Comparison.ModelConn
import Cohesivemodules.Comparison.ModelTensorPair
import Cohesivemodules.Comparison.ModelTensorKappa
import Cohesivemodules.Comparison.ModelTensorCoord
import Cohesivemodules.Comparison.ModelTensorIso
import Cohesivemodules.Comparison.ModelTensor
import Cohesivemodules.Comparison.PerfectAux
import Cohesivemodules.Comparison.PerfectLoc
import Cohesivemodules.Comparison.PerfectModel
import Cohesivemodules.Comparison.Perfect
import Cohesivemodules.Comparison.HomSheafAux
import Cohesivemodules.Comparison.HomSheafRetract
import Cohesivemodules.Comparison.HomSheaf
import Cohesivemodules.Comparison.FullyFaithfulAux
import Cohesivemodules.Comparison.FullyFaithfulTop
import Cohesivemodules.Comparison.FullyFaithful
import Cohesivemodules.Comparison.FullyFaithfulPhiH
import Cohesivemodules.Comparison.FullyFaithfulPhi
import Cohesivemodules.Comparison.FullyFaithfulSquare
import Cohesivemodules.Comparison.FullyFaithfulGlobal
import Cohesivemodules.Comparison.FullyFaithfulLocal
import Cohesivemodules.Comparison.EssSurjAux
import Cohesivemodules.Comparison.EssSurjModel
import Cohesivemodules.Comparison.EssSurjCore
import Cohesivemodules.Comparison.EssSurj
import Cohesivemodules.Comparison.Equivalence
import Cohesivemodules.BlockFunctorDef
import Cohesivemodules.StatementsConditional
import Cohesivemodules.Main
import Cohesivemodules.MainH1
import Cohesivemodules.ChecksAlgebra
import Cohesivemodules.ChecksCurved
import Cohesivemodules.ChecksCurvedZero
import Cohesivemodules.Checks
import Cohesivemodules.ChecksSheaf
import Cohesivemodules.ChecksForms
import Cohesivemodules.ChecksComparison
import Cohesivemodules.ChecksMain
import Cohesivemodules.ChecksTwistedMain
import Cohesivemodules.Hubs.Triangulated
import Cohesivemodules.Hubs.SheavesPerfect
import Cohesivemodules.Hubs.Dolbeault
import Cohesivemodules.Hubs.BlockTheorem
import Cohesivemodules.Hubs.DolbeaultGrothendieck
import Cohesivemodules.Hubs.LocalGauge
import Cohesivemodules.Hubs.TwistedTheorem

set_option linter.style.header false

/-!
# Block's theorem: cohesive modules and perfect complexes

This library is a formalization, in Lean 4 and Mathlib, of J. Block's theorem comparing cohesive
modules over the Dolbeault algebra of a compact complex manifold with perfect complexes of
holomorphic sheaves ([[B][Block], Thm 4.1.3], in the perfect form of
[[A][Antweiler], Thm 7.2.20]), and of its twisted form ([[A][Antweiler], Thm 7.4.3]). Everything
is proved: there is no `sorry`, and the three main theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

This page states the main results and explains how the documentation is organized. Each part of
the library has a *hub*, an overview page with its main definitions and results, its conventions
and signs, and its files.

## Setting

Throughout, `E : Type` is a finite-dimensional complex normed space and `X : Type` a compact
Hausdorff complex manifold modelled on `E` (`IsManifold 𝓘(ℂ, E) ∞ X`: complex `C^∞`, i.e.
holomorphic, transition maps). `A = 𝒜_X(X)` is the Dolbeault algebra of smooth `(0, q)`-forms on
`X` with differential `∂̄` (`Cohesive.dolbeault`), and `O_X` is the sheaf of holomorphic functions
(`Cohesive.holSheaf`). A *cohesive module* over `A` is a bounded, finitely generated projective
graded `A⁰`-module `Q` with a flat `∂̄`-superconnection `𝕏` on `A ⊗_{A⁰} Q`; `Ho(P_A)`
(`Cohesive.HoP`) is their homotopy category.

## The main results

* **Block's theorem** (`Cohesive.MainStatement`, proved as `main_theorem`). The functor
  `Cohesive.blockFunctor E X : Ho(P_A) ⥤ D(O_X)`, `M ↦ α(M)`, from `Ho(P_A)` to the derived
  category of sheaves of `O_X`-modules, is full and faithful, and its essential image is
  `D_perf(X, O_X)` (`Cohesive.Perf`). Equivalently, `J` lands in `D_perf(X, O_X)` and its
  corestriction is an equivalence `Ho(P_A) ≃ D_perf(X, O_X)` (`Cohesive.Checks.blockFunctor_iff`).
* **Conditional form** (`Cohesive.MainStatementConditional`, proved as
  `main_theorem_conditional`). The same statement with two analytic hypotheses on `X`: H1, the
  Dolbeault–Grothendieck lemma (`Cohesive.DolbeaultGrothendieck`), and H2, the local gauge lemma
  in a weak form (`Cohesive.LocalGaugeLemma`). The project first formalized the theorem in this
  conditional version. Both hypotheses are now theorems (`Cohesive.dolbeaultGrothendieck`,
  `Cohesive.localGaugeLemma`), so the conditional statement is a corollary.
* **Twisted theorem** (`Cohesive.MainStatementTwisted`, proved as
  `Cohesive.main_theorem_twisted`). Let `h ∈ 𝒜^{0,2}(X)` be `∂̄`-closed, and let `T` be a twist
  datum for `h` (`Cohesive.TwistData`: a finite open cover with a `∂̄`-primitive of `h` on each
  member and a Čech 2-cocycle `ȟ` of units of `O_X`; one exists for every `h`,
  `Cohesive.exists_twistData`). Then
  the functor `Cohesive.twistedBlockFunctor h T` from `Ho(P_A)` for the curved algebra
  `(𝒜_X(X), ∂̄, h)` to the derived category of `ȟ`-twisted `O_X`-modules (`Cohesive.TwMod`) is
  full and faithful, and its essential image is the twisted perfect complexes (`Cohesive.TwPerf`).
  At `h = 0` it gives back Block's theorem (`Cohesive.K8_twisted_implies_unconditional`).

The statements live in `Statements.lean`, `StatementsConditional.lean` and
`StatementsTwisted.lean`. These files import only Mathlib and *frozen* definition files: every
definition the statements depend on was presented to a human at a review gate, where the
definitions were checked in excerpts, and was then marked `-- FROZEN` and never changed
afterwards, so the meaning of the statements cannot drift while proofs are written. To check that
the statements say what they should, it suffices to read these definitions; the list is in
`review/statement-defs.md`.

⚠ **Deviations from the sources** shared by the statements:
* `D_perf` instead of `D^b_coh` of [[B][Block]]: their identification (which needs Oka's
  coherence theorem) is not formalized.
* "Equivalence onto `D_perf`" is stated as full, faithful, and essential image equal to `Perf`.
  The equivalent form as an equivalence with the full subcategory is checked separately (K6).
* Left modules instead of Block's right modules; the curvature changes sign, `c = −c_Block`.
* The twisted theorem is stated for every twist datum `T`; that the result does not depend on `T`
  is not formalized, and [[A][Antweiler]]'s data `(h⁰, h¹, h², exp)` are replaced by
  multiplicative data.
Each hub repeats the deviations of its own part.

## Guide to the hubs

* [*Cohesive modules*](##Cohesivemodules.Hubs.CohesiveModules) (blueprint items A1–A13):
  curved dgas, cohesive modules, Hom complexes, `Ho(P_A)`, base change, and the lifting theorem.
* [*Triangulated structure*](##Cohesivemodules.Hubs.Triangulated) (Z2, K4): shifts and cones of
  cohesive modules, `Ho(P_A)` is triangulated, and the check
  `Hom(𝒜, 𝒜⟦n⟧) ≅ H^{0,n}_∂̄(X)` for the unit module `𝒜`.
* [*Sheaves and perfect complexes*](##Cohesivemodules.Hubs.SheavesPerfect) (S1–S11): sheaves of
  modules, fine and soft sheaves, Hom sheaves and tensor products, strictly perfect and perfect
  complexes, `D_perf`.
* [*Dolbeault algebra*](##Cohesivemodules.Hubs.Dolbeault) (F1–F12, K7): `(0, q)`-forms and `∂̄`,
  the Dolbeault algebra `𝒜_X`, and `O_X`.
* [*Block's theorem*](##Cohesivemodules.Hubs.BlockTheorem) (C0–C7, F14–F15): resolving data, the
  functor `J`, the abstract comparison theorem, and the main statements.
* [*Dolbeault–Grothendieck lemma*](##Cohesivemodules.Hubs.DolbeaultGrothendieck) (H1, Z4): H1 and
  its proof.
* [*Local gauge lemma*](##Cohesivemodules.Hubs.LocalGauge) (H2, Z5): H2 and its proof.
* [*Twisted theorem*](##Cohesivemodules.Hubs.TwistedTheorem) (Z3): curved Dolbeault algebras,
  twisted sheaves, and the twisted statement.

**How the parts depend on each other.**
* [*Cohesive modules*](##Cohesivemodules.Hubs.CohesiveModules) (algebra over an arbitrary curved
  dga) and [*Sheaves and perfect complexes*](##Cohesivemodules.Hubs.SheavesPerfect) (sheaf theory
  over an arbitrary sheaf of rings) are independent foundations.
* [*Dolbeault algebra*](##Cohesivemodules.Hubs.Dolbeault) builds the analytic objects on both: the
  Dolbeault algebra is a dga in the sense of *Cohesive modules*, and `𝒜⁰` is fine in the sense of
  *Sheaves and perfect complexes*.
* [*Block's theorem*](##Cohesivemodules.Hubs.BlockTheorem) proves an abstract comparison theorem
  for any resolving data, using the two foundations, and then applies it to the Dolbeault data,
  with H1 and H2 supplied by the
  [*Dolbeault–Grothendieck lemma*](##Cohesivemodules.Hubs.DolbeaultGrothendieck) and
  [*Local gauge lemma*](##Cohesivemodules.Hubs.LocalGauge) hubs. Both analytic hubs build on
  *Dolbeault algebra*; the proof of H2 also uses frames and base change from *Cohesive modules*
  and the parametric Cauchy-transform solver of the proof of H1.
* [*Twisted theorem*](##Cohesivemodules.Hubs.TwistedTheorem) uses all of the above: on each open
  of a cover the curved theory is reduced to the flat one by a gauge change.
* [*Triangulated structure*](##Cohesivemodules.Hubs.Triangulated) holds for every curved dga and
  is not used by any of the statements.

## Conventions

Each hub states its conventions in a section "Conventions and signs"; `blueprint/conventions.md`
is the reference. The most important ones:
* Universes: `X E : Type`; sheaves of modules are `SheafOfModules.{0}`.
* Smoothness: `∞` is `C^∞`; Mathlib's `⊤` means analytic and is never used for smoothness.
* Signs: left modules, the Hom differential `δφ = 𝕏 ∘ φ − (−1)^n φ ∘ 𝕏` (Mathlib's
  `CochainComplex.HomComplex.δ`), and Mathlib's shift and mapping-cone conventions.

## Checks

Non-vacuity and sanity checks are collected in the `Checks*.lean` files (blueprint §9). For
example: H1 and H2 hold in complex dimension `0` (K1); the corestriction of `J` to `D_perf` is an
equivalence (K6); the twisted statement implies the untwisted one (K8). The axioms of
`main_theorem`, `main_theorem_conditional` and the intermediate results are checked with
`#print axioms` and `#guard_msgs` in `ChecksMain.lean`, those of
`Cohesive.main_theorem_twisted` in `ChecksTwistedMain.lean`.

## Sources of this formalization

The informal blueprint is `blueprint/blueprint.md` (items A…, S…, F…, C…, H1–H2, Z…, K…, each with
statement and proof) with the parts `blueprint/blueprint-tr.md` (Z2), `blueprint-dg.md` (Z4),
`blueprint-ll.md` (Z5) and `blueprint-tw.md` (Z3). The status of every item is in
`blueprint/status.md`.

## References

* [[B][Block]] J. Block, *Duality and equivalence of module categories in noncommutative geometry*,
  arXiv math/0509284v2.
* [[A][Antweiler]] P. Antweiler, *Curved ∞-local systems and projectively flat Riemann–Hilbert
  correspondence*, arXiv 2411.19595v1.
* [[CHL][ChuangHolsteinLazarev]] J. Chuang, J. Holstein, A. Lazarev, *Maurer–Cartan moduli and
  theorems of Riemann–Hilbert type*, Appl. Categ. Struct. 29 (2021); numbering of
  arXiv 1802.02549v3.

All references, with backlinks to the pages that cite them: [References](references.html).
-/
