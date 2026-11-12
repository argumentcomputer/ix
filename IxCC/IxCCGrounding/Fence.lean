import IxCCGrounding.Ground
import IxCCGrounding.Root
import IxCCGrounding.Direct.Sites
import IxCCGrounding.CaseBlind

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

/-- info: 'IxCC.Grounding.KTab.get_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.KTab.get_of

/-- info: 'IxCC.Grounding.DCtx.findProj?_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.DCtx.findProj?_eq

/-- info: 'IxCC.Grounding.DCtx.neverProp_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.DCtx.neverProp_sound

/-- info: 'IxCC.Grounding.betaStar_reduces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.betaStar_reduces

/-- info: 'IxCC.Grounding.fitsWith_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fitsWith_sound

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

/-! G3 parts A and B: recursor classes, the checked recursor shape, a recursor head. -/

/-- info: 'IxCC.Grounding.recClassB_recr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recClassB_recr

/-- info: 'IxCC.Grounding.recFacts_of_noRecr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recFacts_of_noRecr

/-- info: 'IxCC.Grounding.groundFacts_of_noRecr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.groundFacts_of_noRecr

/-- info: 'IxCC.Grounding.groundCheckWith_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.groundCheckWith_mono

/-- info: 'IxCC.Grounding.recClass_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recClass_of

/-- info: 'IxCC.Grounding.recStored_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recStored_of_check

/-- info: 'IxCC.Grounding.eqReflBasis_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqReflBasis_of_check

/-- info: 'IxCC.Grounding.eqReflBasisB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqReflBasisB_of

/-- info: 'IxCC.Grounding.recShape_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recShape_of

/-- info: 'IxCC.Grounding.head_tele' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.head_tele

/-- info: 'IxCC.Grounding.fire_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fire_step

/-- info: 'IxCC.Grounding.rootSound_noRecr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_noRecr

/-- info: 'IxCC.Grounding.fibRoot_noRecr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fibRoot_noRecr

/-- info: 'IxCC.Grounding.decideRoot_noRecr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.decideRoot_noRecr

/-! G3 part C: `Eq.rec` admitted (F3). -/

/-- info: 'IxCC.Grounding.eq_of_inhabited_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eq_of_inhabited_pt

/-- info: 'IxCC.Grounding.recClassB_eqRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recClassB_eqRec

/-- info: 'IxCC.Grounding.recFacts_of_emptyOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recFacts_of_emptyOnly

/-- info: 'IxCC.Grounding.eqRecBasis_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqRecBasis_of_check

/-- info: 'IxCC.Grounding.eqRecBasisB_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqRecBasisB_of

/-- info: 'IxCC.Grounding.peelLams_corr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.peelLams_corr

/-- info: 'IxCC.Grounding.peelLams_eqRecRhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.peelLams_eqRecRhs

/-- info: 'IxCC.Grounding.eqRefl_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqRefl_pt

/-- info: 'IxCC.Grounding.eqRec_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eqRec_iota

/-- info: 'IxCC.Grounding.recClassB_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recClassB_flat

/-- info: 'IxCC.Grounding.recFacts_of_eqRecOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recFacts_of_eqRecOnly

/-- info: 'IxCC.Grounding.lamSplit_spec' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.lamSplit_spec

/-- info: 'IxCC.Grounding.piSplit_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.piSplit_length

/-- info: 'IxCC.Grounding.recTele_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recTele_of_check

/-- info: 'IxCC.Grounding.recProg_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recProg_of_check

/-- info: 'IxCC.Grounding.recCtorsRaw_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recCtorsRaw_of_check

/-- info: 'IxCC.Grounding.getAppArgs_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.getAppArgs_inst

/-- info: 'IxCC.Grounding.lamTele_app_doms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lamTele_app_doms

/-- info: 'IxCC.Grounding.flatIota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.flatIota

/-- info: 'IxCC.Grounding.ctorImage_noLevels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.ctorImage_noLevels

/-- info: 'IxCC.Grounding.ctorImage_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.ctorImage_canon

/-- info: 'IxCC.Grounding.relSlots_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.relSlots_reverse

/-- info: 'IxCC.Grounding.flatIota_noLevels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.flatIota_noLevels

/-! ## The fragment's clause for fixed-width words (stage W1): no `word` entry in `Sl` -/

/-- info: 'IxCC.Grounding.noWord_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.noWord_of

/-! ## G3, part E: recursors without parameters whose rule bodies run (`noParams`) -/

/-- info: 'IxCC.Grounding.recClassB_noParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recClassB_noParams

/-- info: 'IxCC.Grounding.recFacts_of_flatOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recFacts_of_flatOnly

/-- info: 'IxCC.Grounding.recFields_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recFields_of_check

/-- info: 'IxCC.Grounding.recBodies_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recBodies_of_check

/-- info: 'IxCC.Grounding.recSites_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recSites_of_check

/-- info: 'IxCC.Grounding.recShapeNoParams_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recShapeNoParams_of

/-- info: 'IxCC.Grounding.holds_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.holds_below

/-- info: 'IxCC.Grounding.evalSites_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.evalSites_congr

/-- info: 'IxCC.Grounding.evalConsts_mentions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.evalConsts_mentions

/-- info: 'IxCC.Grounding.evalConsts_peel' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.evalConsts_peel

/-- info: 'IxCC.Grounding.lamTele_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lamTele_inj

/-- info: 'IxCC.Grounding.piBody_piTele' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.piBody_piTele

/-- info: 'IxCC.Grounding.piBody_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.piBody_inst

/-- info: 'IxCC.Grounding.ruleSites_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.ruleSites_ok

/-- info: 'IxCC.Grounding.runs_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.runs_peel

/-- info: 'IxCC.Grounding.relEnv_pushAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.relEnv_pushAll

/-- info: 'IxCC.Grounding.ctxSat_of_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.ctxSat_of_fits

/-- info: 'IxCC.Grounding.noParamsIota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.noParamsIota

/-- info: 'IxCC.Grounding.ctorFields_noLevels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.ctorFields_noLevels

/-- info: 'IxCC.Grounding.ctorFields_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.ctorFields_canon

/-- info: 'IxCC.Grounding.fire_noParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fire_noParams

/-! GR12: ι in #678's guarded form beside the landed law; the `case` lemma without canonicity. -/

/-- info: 'IxCC.Grounding.IotaRuleG.of_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.IotaRuleG.of_premises

/-- info: 'IxCC.Grounding.IotaLawG.toIotaLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.IotaLawG.toIotaLaw

/-- info: 'IxCC.Grounding.caseRulesBlind_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseRulesBlind_of_check

/-- info: 'IxCC.Grounding.den_inst_cv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.den_inst_cv

/-- info: 'IxCC.Grounding.den_inst_exact_cv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.den_inst_exact_cv

/-- info: 'IxCC.Grounding.fits_inst_cv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fits_inst_cv

/-- info: 'IxCC.Grounding.litSet_indep_cv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.litSet_indep_cv

/-- info: 'IxCC.Grounding.relV_lit_eq_cv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.relV_lit_eq_cv

/-- info: 'IxCC.Grounding.lamR_dom_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lamR_dom_of_mem

/-- info: 'IxCC.Grounding.spineOk_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spineOk_append

/-- info: 'IxCC.Grounding.fits_of_spineOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fits_of_spineOk

/-- info: 'IxCC.Grounding.fields_fit_of_spineOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fields_fit_of_spineOk

/-- info: 'IxCC.Grounding.caseIotaG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseIotaG

/-- info: 'IxCC.Grounding.caseFires_of_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseFires_of_blind

/-! GR12: the canonicity-free family (`LawsNoCanon`, `NoCanon`), and the laws other than canonicity (`LawsCore`). -/

/-- info: 'IxCC.Grounding.lawsCore_of_laws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lawsCore_of_laws

/-- info: 'IxCC.Grounding.LawsNoCanon.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.LawsNoCanon.core

/-- info: 'IxCC.Grounding.recNoLevels_ctor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.recNoLevels_ctor

/-- info: 'IxCC.Grounding.noCanon_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.noCanon_of_check

/-- info: 'IxCC.Grounding.caseBlind_of_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseBlind_of_noCanon

/-- info: 'IxCC.Grounding.caseFires_of_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseFires_of_noCanon

/-- info: 'IxCC.Grounding.fundHyps_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fundHyps_of_core

/-- info: 'IxCC.Grounding.fundHyps_of_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fundHyps_of_noCanon

/-- info: 'IxCC.Grounding.allP_of_check_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.allP_of_check_noCanon

/-- info: 'IxCC.Grounding.const_of_check_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.const_of_check_noCanon

/-- info: 'IxCC.Grounding.rootSound_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_core

/-- info: 'IxCC.Grounding.rootSound_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_noCanon

/-- info: 'IxCC.Grounding.fibRoot_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fibRoot_noCanon

/-- info: 'IxCC.Grounding.decideRoot_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.decideRoot_noCanon

/-! **The canonicity-free root theorems conclude exactly what the landed ones do**: each `example`
states the landed theorem's hypotheses with `LawsNoCanon` for `Laws` and the `NoCanon` fact (or its
checker) added, and its conclusion copied word for word from the landed theorem, and is proved by
the new theorem. -/

section NoCanonConclusions

open IxCC.Grounding Ix.Kernel Ix.Kernel.SetTheory
open IxCC.Src (Value CId Program Levels)

variable {V : Type} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

example (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonB p env κ Sl = true)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl)) :
    ∀ k, AllP M p κ lpsOf (· ∈ Sl) (Ok p ann) k :=
  allP_of_check_noCanon hL hchk hnc hT

example (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonB p env κ Sl = true)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {ls : Levels} {c : CId} {v : Value} {φ : LevelParam → Nat}
    (hrun : IxCC.Src.evalConst p k ls c = .ok v) (hc : c ∈ Sl) (hOk : Ok p ann c ls)
    (hlv : LvAt φ (lpsOf c) ls) :
    RelV M κ lpsOf (· ∈ Sl) (Ok p ann) v (M.cval (κ c) φ) :=
  const_of_check_noCanon hL hchk hnc hT hrun hc hOk hlv

example (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId} {args : List FoTy} {res : FoTy}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_noCanon hL hG hC hNC hR hT hA hrun hrb hRT hO φ ρ X hX

example (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [.nat] .nat)
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    {k n : Nat} {v : Value} {w : Nat} (hrun : IxCC.Src.run p k root [.lit n] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.nat w)) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (X : V) (hX : Denotes M.cval env φ ρ (.app (.const (κ root) []) (litE n)) X) :
    Denotes M.cval env φ ρ (litE w) X :=
  fibRoot_noCanon hL hG hC hNC hR hD hrun hrb φ ρ X hX

example (hL : LawsNoCanon M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root boolD : CId}
    (hb : p.known.bool = some boolD) (hBL : BoolListed p boolD)
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root [] (.enum boolD))
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    (hRT : ResultTag p env κ (· ∈ Sl) (.enum boolD) (.ctor 1 []))
    {k : Nat} {v : Value} (hrun : IxCC.Src.run p k root [] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.ctor 1 [])) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (X : V) (hX : Denotes M.cval env φ ρ (.const (κ root) []) X) :
    Denotes M.cval env φ ρ (.const boolTrueName []) X :=
  decideRoot_noCanon hL hb hBL hG hC hNC hR hD hRT hrun hrb φ ρ X hX

end NoCanonConclusions
