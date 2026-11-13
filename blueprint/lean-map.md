# Blueprint items → Lean names (documentation plan B10)

Read by `scripts/blueprint_gen.py`. Columns 2–4 are written by hand, columns 5–6 by
`scripts/blueprint_gen.py sync`; Lean is the arbiter of dependencies (human, 10 Nov 2026,
documentation plan B3′).
- **Lean**: the `\lean{}` names shown for the item (fully qualified; seeded from the docstring
  tags, curated). For dependencies, a declaration belongs to the item of its docstring tag; this
  column decides only for untagged declarations.
- **Extra uses**: edges to add (checked against Lean like the Markdown mentions).
- **Cycle breaks**: needed only where Lean itself has a cycle between two items; `sync` keeps an
  entry only while that holds. Currently none: the three such cycles (S5/S9, F9/F10, C5/C7) came
  from docstring tags naming a later item than the first one that uses the declaration, and are
  fixed by the owner overrides at the end of this file.
- **Dropped** (automatic): item numbers mentioned in the Markdown text that are not Lean
  dependencies, even through other items (e.g. "C4 uses S3.b" inside S3).
- **Lean uses** (automatic): Lean dependencies the remaining edges do not give, transitively
  reduced.

Items without Lean code (A8, A3.b′) keep their Markdown edges: there is nothing to check them
against.

| Item | Lean | Extra uses | Cycle breaks | Dropped (no Lean dependency) | Lean uses (B3) |
| --- | --- | --- | --- | --- | --- |
| M | `Cohesive.MainStatementConditional`, `main_theorem_conditional` | F15 |  | Z2.g, Z3.v, Z4.g, Z5.i |  |
| A1 | `Cohesive.GCDga` |  |  |  |  |
| A2 | `Cohesive.Connection`, `Cohesive.Connection.exists_connection`, `Cohesive.Connection.diff` |  |  |  | A1 |
| A3 | `Cohesive.QuasiCohesive`, `Cohesive.CohesiveModule`, `Cohesive.QuasiCohesive.ofGenerators`, `Cohesive.QuasiCohesive.X_eq_of_generators`, `Cohesive.QuasiCohesive.comp_one_leibniz`, `Cohesive.QuasiCohesive.X0` |  |  |  | A1 |
| A3.b′ |  |  |  |  |  |
| A4 | `Cohesive.Hom`, `Cohesive.δ`, `Cohesive.homEquivGen` |  |  |  | A3 |
| A5 | `Cohesive.HoP` |  |  |  |  |
| A6 | `Cohesive.filTot`, `Cohesive.filHom`, `Cohesive.memFilHom_iff`, `Cohesive.δ_mem_filHom` |  |  |  | A4 |
| A7 | `Cohesive.quasiIso_of_finite_filtration` |  |  |  |  |
| A8 |  |  |  |  |  |
| A9 | `Cohesive.DgaHom`, `Cohesive.CohesiveModule.baseChange`, `Cohesive.bcHoFunctor`, `Cohesive.bcCompNatIso`, `Cohesive.bcHomL`, `Cohesive.hom_eq_of_bcF`, `Cohesive.DgaHom.comp`, `Cohesive.bcCompTot` |  |  |  | A5 |
| A10 | `Cohesive.QuasiCohesive.fromComplex`, `Cohesive.IsBoundedFGProj`, `Cohesive.fcResP_δ`, `Cohesive.homRδ`, `Cohesive.homRδ_mem`, `Cohesive.fc_hom_ext` |  |  | C4 | A9 |
| A11 | `Cohesive.lifting`, `Cohesive.CohesiveModule.ofGenData`, `Cohesive.lift_core`, `Cohesive.liftStage_one`, `Cohesive.liftStage_succ`, `Cohesive.ConeLift` |  |  |  | A6 |
| A12 | `Cohesive.totMap_quasiIso`, `Cohesive.lifting_quasiIso`, `Cohesive.QuasiCohesive.totComplex`, `Cohesive.totMap`, `Cohesive.Z0.comp0` |  |  |  |  |
| A13 | `Cohesive.TotR.rAct`, `Cohesive.BlockCohesive`, `Cohesive.BlockHom`, `Cohesive.blockδ`, `Cohesive.blockSwap`, `Cohesive.BlockQuasiCohesive.toLeft` |  |  |  | A4 |
| S1 | `Cohesive.SupportedIn`, `Cohesive.IsFine`, `Cohesive.existsUnique_extend`, `Cohesive.exists_hom_extend` |  |  |  |  |
| S2 | `Cohesive.exists_local_preimage_of_epi`, `Cohesive.surjective_globalSections_of_epi` |  |  |  |  |
| S3 | `Cohesive.acyclic_globalSections`, `Cohesive.exactAt_globalSections`, `Cohesive.quasiIso_globalSections` |  |  | C4, S10, S3.b |  |
| S3.b | `Cohesive.IsSoft`, `Cohesive.IsSoft.of_action`, `Cohesive.isSoft_of_isFine`, `Cohesive.surjective_globalSections_of_isSoft`, `Cohesive.IsSoft.of_shortExact`, `Cohesive.acyclic_globalSections_of_isSoft` |  |  | C4 | S2 |
| S4 | `Cohesive.projective_free`, `Cohesive.projective_of_isFinFreeSummand`, `Cohesive.isFinFreeSummand_of_locally`, `Cohesive.finite_globalSections`, `Cohesive.projective_globalSections`, `Cohesive.bijective_globalSections_map` |  |  |  | S8 |
| S5 | `Cohesive.restrFreeIso`, `Cohesive.IsFinFreeSummand.restr`, `Cohesive.extZero`, `Cohesive.extZero_preservesFiniteLimits`, `Cohesive.isIso_extZeroAdj_unit`, `Cohesive.extZero_locally_zero` |  |  |  | S1 |
| S6 | `Cohesive.shortComplex_exact_iff`, `Cohesive.acyclic_of_locally`, `Cohesive.quasiIso_of_locally`, `Cohesive.quasiIso_of_sectionwise` |  |  |  | S2, S5 |
| S7 | `Cohesive.homSheaf`, `Cohesive.homPre`, `Cohesive.homPost`, `Cohesive.homSheafComplex`, `Cohesive.homComplexSectionsEquiv`, `Cohesive.homSheafOverIso` |  |  | C3, C4 | S6, S9 |
| S8 | `Cohesive.tensorBifunctor`, `Cohesive.tensorC`, `Cohesive.tensorCMap₂`, `Cohesive.IsFlat`, `Cohesive.IsKFlat`, `Cohesive.restrTensorIso` |  |  |  | S9 |
| S9 | `Cohesive.IsStrictlyPerfect`, `Cohesive.IsPerfect`, `Cohesive.perf_Q_obj_iff`, `Cohesive.IsPerfectIn`, `Cohesive.IsPerfect.exists_isPerfectIn`, `Cohesive.IsPerfectIn.exactAt` |  |  | S10 | S5 |
| S10 | `Cohesive.exists_strictlyPerfect_quasiIso`, `Cohesive.nullHomotopic_locally`, `Cohesive.lift_locally`, `Cohesive.split_locally`, `Cohesive.isFinFreeSummand_locally_of_acyclic`, `Cohesive.homology_finGen_locally`, `Cohesive.exists_epi_free_of_locally` |  |  |  | S7 |
| S11 | `Cohesive.exists_injective_resolution`, `Cohesive.exists_lift_of_isKProjective` |  |  |  |  |
| C0 | `Cohesive.DgaPresheaf`, `Cohesive.DgaPresheaf.pre0`, `Cohesive.PreResolvingData`, `Cohesive.ResolvingData`, `Cohesive.PreResolvingData.piecePre`, `Cohesive.PreResolvingData.pieceSheaf` |  |  | A11, C1, C2, C4, C5, F10, F14, H1, H2, Z3.v | S4, S6 |
| C1 | `Cohesive.PreResolvingData.sheafOf`, `Cohesive.PreResolvingData.JK`, `Cohesive.PreResolvingData.J`, `Cohesive.PreResolvingData.sheafOfOver` |  |  |  |  |
| C2 | `Cohesive.ResolvingData.quasiIso_of_gamma_eq`, `Cohesive.ResolvingData.exists_quasiIso_sheafOfOver_fromComplex`, `Cohesive.ResolvingData.isPerfect_sheafOf`, `Cohesive.ResolvingData.perf_J_obj` |  |  |  |  |
| C3 | `Cohesive.PreResolvingData.homAlong`, `Cohesive.PreResolvingData.homTop`, `Cohesive.PreResolvingData.isSoft_homSh` |  |  | C4 | Z3.m |
| C4 | `Cohesive.ResolvingData.bijective_J_map`, `Cohesive.ResolvingData.quasiIso_Φ`, `Cohesive.ResolvingData.bijective_J_map_comp`, `Cohesive.PreResolvingData.Ψ_top`, `Cohesive.ResolvingData.quasiIso_Ψ_comp`, `Cohesive.PreResolvingData.exists_isStrictlyGE_ℋ`, `Cohesive.ResolvingData.bijective_J_map` |  |  | S3 |  |
| C5 | `Cohesive.ResolvingData.exists_J_obj_iso`, `Cohesive.PreResolvingData.ρSheaf`, `Cohesive.ResolvingData.exists_flat_model`, `Cohesive.ResolvingData.isPerfect_sheafBC`, `Cohesive.ResolvingData.exists_sheafOfMap_quasiIso`, `Cohesive.ResolvingData.quasiIso_tensorCMap_ρhat`, `Cohesive.ResolvingData.tensorC_single_unit_iso` |  |  | A12, F11 |  |
| C6 | `Cohesive.ResolvingData.comparison` |  |  |  |  |
| C7 | `Cohesive.PreResolvingData.exists_TC_iso_tensorC`, `Cohesive.PreResolvingData.quasiIso_Ξ`, `Cohesive.PreResolvingData.Conn`, `Cohesive.PreResolvingData.Conn.N`, `Cohesive.PreResolvingData.TSh`, `Cohesive.PreResolvingData.Conn.TC`, `Cohesive.PreResolvingData.Ξ` |  |  | A12, C2, C4, C5 | A11, C1 |
| F1 | `Cohesive.isManifold_real`, `Cohesive.contMDiffRing_real_complex` |  |  |  |  |
| F2 | `Cohesive.Conj.map`, `Cohesive.form0Equiv`, `Cohesive.extToFibre`, `Cohesive.extToFibre_bijective`, `Cohesive.extEquivFibre`, `Cohesive.dzbarBasis` |  |  |  |  |
| F3 | `Cohesive.antiPart`, `Cohesive.dbarPart`, `Cohesive.dbar`, `Cohesive.dbar_add`, `Cohesive.dbar_const_smul`, `Cohesive.dbar_congr` |  |  |  | F5 |
| F4 | `Cohesive.dbar_dbar` |  |  |  | F3 |
| F5 | `Cohesive.TotFibre.ofDeg`, `Cohesive.TotFibre.deg`, `Cohesive.TotFibre.mulCLM`, `Cohesive.TotFibre.extEquivTotFibre_mul`, `Cohesive.TotFibre.ofDeg_mul_ofDeg`, `Cohesive.TotFibre.ofDeg_mul_comm` |  |  |  | F2 |
| F6 | `Cohesive.wedge`, `Cohesive.dbar_wedge` |  |  |  | F3 |
| F7 | `Cohesive.TotFibre.pull`, `Cohesive.pullback`, `Cohesive.dbar_pullback`, `Cohesive.pullback_smul`, `Cohesive.TotFibre.pull_mul`, `Cohesive.TotFibre.pull_one` |  |  |  | F3 |
| F8 | `Cohesive.dbar_eq_zero_iff_contDiffOn` |  |  |  | F3 |
| F9 | `Cohesive.IsDolbeault`, `Cohesive.IsOfDegree.dbarSec`, `Cohesive.restrictForm`, `Cohesive.dolbeaultLocalPredicate`, `Cohesive.IsDolbeault.contDiffAt_chartExpr` |  |  |  | F4, F6 |
| F10 | `Cohesive.dolbeault0`, `Cohesive.dolbeaultSubalgebra`, `Cohesive.dbarL`, `Cohesive.dolbeaultRes`, `Cohesive.dolbeault_glue`, `Cohesive.isOfDegree_of_locally` |  |  | C0 | A9 |
| F11 | `Cohesive.isFine_dolbeault0`, `Cohesive.dolbeault_locallyFree` |  |  |  | F1, F12, S1 |
| F12 | `Cohesive.dolbeaultRhoU`, `Cohesive.dolbeaultRho`, `Cohesive.dolbeaultRhoU_injective`, `Cohesive.dbar_dolbeaultRhoU`, `Cohesive.exists_dolbeaultRhoU_of_dbar_eq_zero`, `Cohesive.holSheaf` |  |  | F1 | F10 |
| H1 | `Cohesive.DolbeaultGrothendieck`, `Cohesive.dolbeaultGrothendieck` |  |  | F12, Z4.g | F10 |
| H2 | `Cohesive.LocalGaugeLemma`, `Cohesive.localGaugeLemma` |  |  | C0, Z5.i | F12 |
| F14 | `Cohesive.dolbeaultPresheaf`, `Cohesive.dolbeaultPreData`, `Cohesive.dolbeaultData` |  |  |  |  |
| F15 | `Cohesive.blockFunctor`, `Cohesive.blockPerf` |  |  |  |  |
| Z2.a | `Cohesive.shiftQ`, `Cohesive.shiftIota`, `Cohesive.QuasiCohesive.transport`, `Cohesive.CohesiveModule.shift`, `Cohesive.shiftIota_mem_hom`, `Cohesive.δ_shiftIota` |  |  |  | A4 |
| Z2.b | `Cohesive.shiftMkCoreHoP`, `Cohesive.isShiftData_shiftIota`, `Cohesive.IsShiftData.trans`, `Cohesive.shiftCompZ0`, `Cohesive.shiftCompIso`, `Cohesive.conjL` |  |  |  | A5, Z2.a |
| Z2.c | `Cohesive.prodQ`, `Cohesive.dsumProdEquiv`, `Cohesive.zeroCohesive`, `Cohesive.zeroHoP`, `Cohesive.isZero_zeroHoP` |  |  |  | A5 |
| Z2.d | `Cohesive.coneQ`, `Cohesive.cone`, `Cohesive.coneX` |  |  |  | Z2.a, Z2.c |
| Z2.e | `Cohesive.coneInrZ0`, `Cohesive.coneDesc`, `Cohesive.coneLift`, `Cohesive.coneMap` |  |  |  | Z2.d |
| Z2.f | `Cohesive.distinguishedTriangles`, `Cohesive.contractible_distinguished`, `Cohesive.distinguished_cocone_triangle`, `Cohesive.exists_coneTriangle_hom`, `Cohesive.complete_distinguished_triangle_morphism`, `Cohesive.rotateTriangleIso` |  |  |  |  |
| Z2.g | `Cohesive.compTriangle`, `Cohesive.compTriangle_distinguished`, `Cohesive.instIsTriangulatedHoP` |  |  | A6, F12, Z5.i |  |
| Z5.a | `Cohesive.integral_inv_norm_ball_zero`, `Cohesive.integrableOn_inv_norm_ball`, `Cohesive.integral_inv_norm_ball_le`, `Cohesive.norm_cauchySolve_le` |  |  |  | Z4.c |
| Z5.b | `Cohesive.pdbar`, `Cohesive.iteratedFDeriv_cauchySolve`, `Cohesive.pdbar_cauchySolve`, `Cohesive.pdbar_cauchySolve_comm` |  |  | Z4.e | Z4.c |
| Z5.c | `Cohesive.exists_gauge_solution`, `Cohesive.coordCLM`, `Cohesive.exists_cutoff_radius`, `Cohesive.neumannTerm`, `Cohesive.gaugeSeries`, `Cohesive.norm_iteratedFDeriv_neumannTerm_le`, `Cohesive.contDiff_gaugeSeries` |  |  |  | Z5.a, Z5.b |
| Z5.d | `Cohesive.dzbarTot`, `Cohesive.ctrTot`, `Cohesive.sgnTot`, `Cohesive.Fib`, `Cohesive.FibOp`, `Cohesive.compOp` |  |  | F6 | F5 |
| Z5.e | `Cohesive.dbarFib`, `Cohesive.dbarFib_eq_sum`, `Cohesive.dbarFib_add_sq`, `Cohesive.gauge_conj`, `Cohesive.gaugeOp_odd`, `Cohesive.mcOp_gaugeOp` |  |  |  | Z5.b, Z5.d |
| Z5.f | `Cohesive.gaugeSubalg`, `Cohesive.IsFlatSuperconn`, `Cohesive.IsGauge`, `Cohesive.exists_gauge_step`, `Cohesive.exists_gauge_of_aCoef`, `Cohesive.exists_gauge_holomorphic` |  |  |  | Z5.c, Z5.e |
| Z5.g | `Cohesive.exists_free_baseChange`, `Cohesive.coef0`, `Cohesive.evalForm0`, `Cohesive.continuous_evalForm0`, `Cohesive.isUnit_of_evalForm0_ne_zero`, `Cohesive.exists_free_away`, `Cohesive.free_baseChange_of_isUnit` |  |  |  | F12 |
| Z5.h | `Cohesive.GradedFrame`, `Cohesive.GradedFrame.vec`, `Cohesive.GradedFrame.coefTot`, `Cohesive.GradedFrame.sum_coefTot`, `Cohesive.GradedFrame.coefTot_mem`, `Cohesive.GradedFrame.mat` |  |  |  | F10, Z5.f |
| Z5.i | `Cohesive.matComplex`, `Cohesive.exists_iso_fromComplex_of_frame`, `Cohesive.exists_iso_of_gauge`, `Cohesive.exists_local_iso` |  |  |  | H2, Z5.g, Z5.h |
| Z5.j | `Cohesive.MainStatement`, `main_theorem`, `Cohesive.blockPerf_unconditional` | H1, H2 |  |  | M, Z4.g, Z5.i |
| Z3.a | `Cohesive.GCDga.withC`, `Cohesive.DgaPresheaf.withCurvature`, `Cohesive.DgaSheafData`, `Cohesive.PreResolvingData.toSheafData` |  |  |  | C0 |
| Z3.b | `Cohesive.CohesiveModule.gauge`, `Cohesive.QuasiCohesive.ungauge`, `Cohesive.gauge_hom`, `Cohesive.gauge_δ`, `Cohesive.gauge_Z0`, `Cohesive.gauge_B0` |  |  |  | Z3.a |
| Z3.c | `Cohesive.DolbeaultClosed2`, `Cohesive.curvedDolbeaultPresheaf`, `Cohesive.curvedDolbeault`, `Cohesive.TwistCocycle`, `Cohesive.TwistCocycle.trivial`, `Cohesive.exactTwistDatum` |  |  |  | F14, Z3.a |
| Z3.d | `Cohesive.expForm`, `Cohesive.expUnit`, `Cohesive.dbar_expForm`, `Cohesive.exists_cover_primitives`, `Cohesive.twistData_of_primitives`, `Cohesive.exists_twistData` |  |  |  | Z3.c, Z4.g, Z5.g |
| Z3.e | `Cohesive.curvedRes`, `Cohesive.curvedRestrict`, `Cohesive.curvedLL`, `Cohesive.localGaugeLemmaOpen`, `Cohesive.exists_free_baseChange_open` |  |  |  | Z3.b, Z3.c |
| Z3.f | `Cohesive.restrOver`, `Cohesive.restrOverAdj`, `Cohesive.restr_restrOver` |  |  |  | S1 |
| Z3.g | `Cohesive.sec`, `Cohesive.toSec`, `Cohesive.secRes`, `Cohesive.TwMod`, `Cohesive.TwMod.Hom`, `Cohesive.TwMod.comp` |  |  |  | S1 |
| Z3.h | `Cohesive.homOfSec`, `Cohesive.TwMod.Hom.glue_comm`, `Cohesive.TwMod.isIso_coimageImageComparison`, `Cohesive.TwMod.kerIsLimit`, `Cohesive.TwMod.cokIsColimit`, `Cohesive.sec_injective_of_mono` |  |  |  | Z3.f, Z3.g |
| Z3.i | `Cohesive.pushCounit`, `Cohesive.pushHomEquiv`, `Cohesive.TwistCocycle.unitRes_cyclic`, `Cohesive.TwMod.mono_of_mono_f`, `Cohesive.TwMod.comp_preservesMonomorphisms`, `Cohesive.push_preservesInjectiveObjects` |  |  | Z3.l | Z3.c, Z3.h |
| Z3.j | `Cohesive.glueNatIso`, `Cohesive.IsPerfectOver`, `Cohesive.IsStrictlyPerfect.restrOver`, `Cohesive.TwIsPerfect`, `Cohesive.IsPerfectOverIn`, `Cohesive.IsPerfectOverIn.exactAt` |  |  |  | Z3.c, Z3.h |
| Z3.k | `Cohesive.glueEval`, `Cohesive.glueCoeval`, `Cohesive.ofSheafGlueIso`, `Cohesive.toGlueOfSheaf`, `Cohesive.rescale`, `Cohesive.isSheaf_gluePre` |  |  | C7, Z3.l, Z3.l′, Z3.t | Z3.i |
| Z3.l | `Cohesive.extXRestrIso`, `Cohesive.extTwLiftSec`, `Cohesive.extTwLift`, `Cohesive.extTwUnit`, `Cohesive.extX_locally_zero`, `Cohesive.isFlat_extX` |  |  | Z3.l′ | Z3.k |
| Z3.l′ | `Cohesive.sheafBCRestrOverIso`, `Cohesive.sec_eq_of_bcUnit`, `Cohesive.bcφ_bcUnit` |  |  | Z3.k, Z3.u | S8, Z3.h |
| Z3.m | `Cohesive.DgaSheafData.A0`, `Cohesive.DgaSheafData.𝒜X`, `Cohesive.DgaSheafData.r`, `Cohesive.DgaSheafData.R`, `Cohesive.DgaSheafData.TotSec`, `Cohesive.DgaSheafData.deg0` |  |  |  | Z3.a |
| Z3.n | `Cohesive.DgaSheafData.smul0L`, `Cohesive.DgaSheafData.gaugeDV`, `Cohesive.DgaSheafData.gaugeDV_gaugeDV`, `Cohesive.DgaSheafData.gaugeDV_smul0L`, `Cohesive.DgaSheafData.bcHomL_gauge_homotopy`, `Cohesive.TwistDatum.twTerm` |  |  |  | Z3.i, Z3.m |
| Z3.o | `Cohesive.twLocalIso`, `Cohesive.curvedResM`, `Cohesive.gaugedRes`, `Cohesive.twCmp`, `Cohesive.twCmp_X` |  |  |  | Z3.b, Z3.n |
| Z3.p | `Cohesive.PreResolvingData.restrOverSheafOfIso`, `Cohesive.isPerfectOver_sheafOfOver`, `Cohesive.twIsPerfect_twistedSheafOf` |  |  |  | Z3.j, Z3.o, Z4.g |
| Z3.q | `Cohesive.DgaSheafData.ℋ` |  |  | C3 |  |
| Z3.r | `Cohesive.secHomOf`, `Cohesive.twHomComplex`, `Cohesive.twHomD_restr`, `Cohesive.hom_ext_of_restr`, `Cohesive.twHomRestrIso`, `Cohesive.twHomRestrOverIso` |  |  | Z3.q | S7, Z3.k |
| Z3.s | `Cohesive.bijective_twistedJ_map`, `Cohesive.full_twistedJ_dolbeault`, `Cohesive.faithful_twistedJ_dolbeault`, `Cohesive.TwistDatum.Ψtw`, `Cohesive.TwistDatum.Ψtw_top`, `Cohesive.LLOpen`, `Cohesive.jKtw`, `Cohesive.evLtw`, `Cohesive.ιtw` |  |  | Z3.q | Z3.p |
| Z3.t | `Cohesive.twModel_TD_comm`, `Cohesive.isRescale_untwist`, `Cohesive.untwistRestrIso`, `Cohesive.untwist_compat`, `Cohesive.untwist_ext`, `Cohesive.πTot` |  |  |  | Z3.k, Z3.l′, Z3.o |
| Z3.u | `Cohesive.exists_twistedJ_obj_iso`, `Cohesive.TwIsPerfect.exists_flat_model`, `Cohesive.isKFlat_twComp`, `Cohesive.exists_roof_sheafBC_restrOver`, `Cohesive.untwFRestrIso`, `Cohesive.isPerfect_untwF` |  |  | C5 | Z3.j |
| Z3.v | `Cohesive.twistedBlockFunctor`, `Cohesive.MainStatementTwisted`, `Cohesive.main_theorem_twisted`, `Cohesive.essImage_twistedBlockFunctor` |  |  |  | Z3.s, Z3.u |
| Z4.a | `Cohesive.locallyIntegrable_inv_complex` |  |  |  |  |
| Z4.b | `Cohesive.dbar_cauchyTransform` |  |  |  | Z4.a |
| Z4.c | `Cohesive.contDiff_cauchySolve`, `Cohesive.hasFDerivAt_cauchySolve`, `Cohesive.map_cauchySolve`, `Cohesive.dbar_cauchySolve` |  |  |  |  |
| Z4.d | `Cohesive.eq_zero_of_ctr_basis`, `Cohesive.dbarPart_comp_clm`, `Cohesive.ctr_dbar`, `Cohesive.ctr_dbar_zero`, `Cohesive.dbarPart_eq_zero_of_dbar_eq_zero` |  |  |  | F3 |
| Z4.e | `Cohesive.exists_dbar_eq`, `Cohesive.conjBasis`, `Cohesive.dbarPart_cauchySolve`, `Cohesive.dbarPart_cauchySolve_comm`, `Cohesive.involvesOnly_cauchySolve`, `Cohesive.exists_cutoff`, `Cohesive.contDiff_cutoff_smul` |  |  |  | F4, Z4.c, Z4.d |
| Z4.f | `Cohesive.chartOpen`, `Cohesive.chartForm`, `Cohesive.chartExpr_chartForm`, `Cohesive.isDolbeault_of_chartExpr`, `Cohesive.isDolbeault_chartForm`, `Cohesive.isOfDegree_chartForm` |  |  |  | F9 |
| Z4.g | `Cohesive.dolbeaultGrothendieck`, `Cohesive.flatExpr` |  |  |  | H1, Z4.e, Z4.f |
| Z4.h | `Cohesive.blockPerf_of_localGaugeLemma`, `main_theorem_of_localGaugeLemma` |  |  | Z5.i | M, Z4.g |

## Owner overrides

For dependencies, these declarations belong to the first item that uses them, not to the item of
their docstring tag (some are in frozen files, so the tag cannot be changed; CLAUDE.md now asks
for the earliest item). Facts about the dependency order, not judgment calls.

| Declaration | Item | Reason |
| --- | --- | --- |
| `Cohesive.IsFinFreeSummand` | S1 | Defined with S1's definitions in `Sheaf/Basic.lean` (PROGRESS S1 row); used by S4, S5 before S9 |
| `Cohesive.restr` | S1 | Defined with S1's definitions in `Sheaf/Basic.lean` (PROGRESS S1 row); used by S1 (`exists_hom_extend`) before S5 |
| `Cohesive.IsOfDegree` | F9 | Defined in `Forms/SheafPred.lean` (F9); used by F9's lemmas before F10 |
| `Cohesive.PreResolvingData.ρSheaf` | C7 | Used by the model `T(K)` of C7, which C5 uses |
| `Cohesive.unitTensorIso` | C7 | Used by C7 (`exists_TC_iso_tensorC`), which C5 uses |
| `Cohesive.LLOpen` | Z3.p | Used by the abstract Z3.p (`Comparison/TwistedPerfectAbstract.lean`, 12 Nov 2026), which Z3.s uses |
