import IxCCGrounding.Ground
import IxCCGrounding.Root
import IxCCGrounding.Direct.Sites

/-! # The grounding library's axiom fence: every theorem presented as proved uses at most
the three standard axioms. Building the library checks it (`#guard_msgs`). -/

/-- info: 'IxCC.Grounding.eq_of_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eq_of_inhabited

/-- info: 'IxCC.Grounding.eqn_tele' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqn_tele

/-- info: 'IxCC.Grounding.eqn_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqn_den

/-- info: 'IxCC.Grounding.okClosed_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.okClosed_of_check

/-- info: 'IxCC.Grounding.termCorr_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.termCorr_of_check

/-- info: 'IxCC.Grounding.eqnShape_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqnShape_body

/-- info: 'IxCC.Grounding.groundFacts_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.groundFacts_of_check

/-- info: 'IxCC.Grounding.runs_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.runs_of_corr

/-- info: 'IxCC.Grounding.runs_of_sites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.runs_of_sites

/-- info: 'IxCC.Grounding.fundHyps_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fundHyps_of

/-- info: 'IxCC.Grounding.allP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.allP

/-- info: 'IxCC.Grounding.fundamental_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fundamental_const

/-- info: 'IxCC.Grounding.fundamental_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fundamental_term

/-- info: 'IxCC.Grounding.allP_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.allP_of_check

/-- info: 'IxCC.Grounding.const_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.const_of_check

/-- info: 'IxCC.Grounding.apply_clo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.apply_clo

/-- info: 'IxCC.Grounding.apply_pap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.apply_pap

/-- info: 'IxCC.Grounding.last_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.last_regime

/-- info: 'IxCC.Grounding.proj_con' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.proj_con

/-- info: 'IxCC.Grounding.prim_fire_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.prim_fire_nat

/-- info: 'IxCC.Grounding.lit_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lit_den

/-- info: 'IxCC.Grounding.lit_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lit_mem

/-- info: 'IxCC.Grounding.litSet_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.litSet_indep

/-- info: 'IxCC.Grounding.natFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.natFacts

/-- info: 'IxCC.Grounding.lvAt_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lvAt_inst

/-- info: 'IxCC.Grounding.relEnv_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.relEnv_get

/-- info: 'IxCC.Grounding.den_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.den_agree

/-- info: 'IxCC.Grounding.den_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.den_lift

/-- info: 'IxCC.Grounding.den_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.den_inst

/-- info: 'IxCC.Grounding.fits_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fits_inst

/-- info: 'IxCC.Grounding.inst_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.inst_self

/-- info: 'IxCC.Grounding.holds_substPW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.holds_substPW

/-- info: 'IxCC.Grounding.lamTele_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lamTele_app

/-- info: 'IxCC.Grounding.lamTele_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lamTele_mem

/-- info: 'IxCC.Grounding.fits_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fits_transport

/-- info: 'IxCC.Grounding.appChain_of_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.appChain_of_fits

/-- info: 'IxCC.Grounding.fieldDom_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fieldDom_iff

/-- info: 'IxCC.Grounding.wrapper_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.wrapper_corr

/-- info: 'IxCC.Grounding.wrapper_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.wrapper_mem

/-- info: 'IxCC.Grounding.caseIota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseIota

/-- info: 'IxCC.Grounding.caseFires_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseFires_of_shape

/-- info: 'IxCC.Grounding.caseStored_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseStored_of_check

/-- info: 'IxCC.Grounding.caseProg_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseProg_of_check

/-- info: 'IxCC.Grounding.caseFacts_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseFacts_of_check

/-- info: 'IxCC.Grounding.caseFires_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseFires_of_check

/-- info: 'IxCC.Grounding.rootFacts_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootFacts_of_check

/-- info: 'IxCC.Grounding.foArgs_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.foArgs_of_check

/-- info: 'IxCC.Grounding.resultTag_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.resultTag_of_check

/-- info: 'IxCC.Grounding.boolListed_of_check' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.boolListed_of_check

/-- info: 'IxCC.Grounding.allP_of_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.allP_of_facts

/-- info: 'IxCC.Grounding.rootSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound

/-- info: 'IxCC.Grounding.fibRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fibRoot

/-- info: 'IxCC.Grounding.decideRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.decideRoot

/-- info: 'IxCC.Grounding.neverProp_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.neverProp_of_check

/-- info: 'IxCC.Grounding.eval_ne_zero_of_never' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eval_ne_zero_of_never

/-- info: 'IxCC.Grounding.projSort_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.projSort_of

/-- info: 'IxCC.Grounding.holds_of_pwAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.holds_of_pwAt

/-- info: 'IxCC.Grounding.profAt_of_lvAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.profAt_of_lvAt

/-- info: 'IxCC.Grounding.maxPlusLe_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.maxPlusLe_sound

/-- info: 'IxCC.Grounding.lvlEq_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lvlEq_sound

/-- info: 'IxCC.Grounding.litEqE_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.litEqE_sound

/-- info: 'IxCC.Grounding.eqUpTo_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqUpTo_sound

/-- info: 'IxCC.Grounding.den_inst1Lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.den_inst1Lift

/-- info: 'IxCC.Grounding.fits_inst1Lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fits_inst1Lift

/-- info: 'IxCC.Grounding.fits_uninst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fits_uninst

/-- info: 'IxCC.Grounding.piR_mem_univ'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.piR_mem_univ'

/-- info: 'IxCC.Grounding.hasTy_app' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.hasTy_app

/-- info: 'IxCC.Grounding.hasTy_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.hasTy_lam

/-- info: 'IxCC.Grounding.hasTy_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.hasTy_pi

/-- info: 'IxCC.Grounding.reduces_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.reduces_beta

/-- info: 'IxCC.Grounding.reduces_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.reduces_delta

/-- info: 'IxCC.Grounding.reduces_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.reduces_proj

/-- info: 'IxCC.Grounding.checks_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.checks_lam

/-- info: 'IxCC.Grounding.direct_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.direct_sound

/-! G2b: the level comparison's `imax a a` collapse, ι and the `Nat` primitives in the conversion, a
string literal by its constructor form, the step at its own fuel, the renaming-tolerant `case`
recursor clause and its implication from the landed one. -/

/-- info: 'IxCC.Grounding.eval_imaxCollapse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eval_imaxCollapse

/-- info: 'IxCC.Grounding.eval_lvlNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eval_lvlNorm

/-- info: 'IxCC.Grounding.den_inst_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.den_inst_exact

/-- info: 'IxCC.Grounding.reduces_strLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.reduces_strLit

/-- info: 'IxCC.Grounding.fits_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fits_rest

/-- info: 'IxCC.Grounding.den_majorForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.den_majorForm

/-- info: 'IxCC.Grounding.primStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.primStep_sound

/-- info: 'IxCC.Grounding.iotaStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.iotaStep_sound

/-- info: 'IxCC.Grounding.step_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.step_of

/-- info: 'IxCC.Grounding.caseRec_of_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseRec_of_named

/-- info: 'IxCC.Grounding.caseStored_of_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseStored_of_named

/-- info: 'IxCC.Grounding.spine_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spine_sound

/-- info: 'IxCC.Grounding.termRefused_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.termRefused_sound

/-- info: 'IxCC.Grounding.runPair_mem_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.runPair_mem_of_check

/-- info: 'IxCC.Grounding.sitesOkRes_of_sitesOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.sitesOkRes_of_sitesOk

/-- info: 'IxCC.Grounding.sitesOk_of_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.sitesOk_of_res

/-- info: 'IxCC.Grounding.directFacts_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.directFacts_of_check

/-- info: 'IxCC.Grounding.sitesOkRes_of_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.sitesOkRes_of_direct

/-- info: 'IxCC.Grounding.allP_of_check_of_sitesOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.allP_of_check_of_sitesOk

/-- info: 'IxCC.Grounding.const_of_check_of_sitesOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.const_of_check_of_sitesOk

/-- info: 'IxCC.Grounding.rootSound_of_sitesOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_of_sitesOk

/-- info: 'IxCC.Grounding.fibRoot_of_sitesOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fibRoot_of_sitesOk

/-- info: 'IxCC.Grounding.decideRoot_of_sitesOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.decideRoot_of_sitesOk
