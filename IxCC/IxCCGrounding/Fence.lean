import IxCCGrounding.Ground
import IxCCGrounding.Root
import IxCCGrounding.Direct.Sites
import IxCCGrounding.CaseBlind
import IxCCGrounding.Adapt678
import IxCCGrounding.CaseLevels
import IxCCGrounding.RootInst
import IxCCGrounding.Graded
import IxCCGrounding.GradedHead
import IxCCGrounding.SelRetype

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

/-! #678's fields copied (`Laws678`) and the adapters to the canonicity-free laws (`Adapt678`). -/

/-- info: 'IxCC.Grounding.IotaRule678.toG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.IotaRule678.toG

/-- info: 'IxCC.Grounding.IotaLaw678.toG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.IotaLaw678.toG

/-- info: 'IxCC.Grounding.Laws678.defnValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.Laws678.defnValue

/-- info: 'IxCC.Grounding.Laws678.cvalParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.Laws678.cvalParams

/-- info: 'IxCC.Grounding.litDefs_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.litDefs_of_check

/-- info: 'IxCC.Grounding.finalSort_of_stripPis' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.finalSort_of_stripPis

/-- info: 'IxCC.Grounding.projCtor_of_projLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.projCtor_of_projLaw

/-- info: 'IxCC.Grounding.eval2_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eval2_div

/-- info: 'IxCC.Grounding.eval2_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eval2_mod

/-- info: 'IxCC.Grounding.eval2_shiftLeft' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.eval2_shiftLeft

/-- info: 'IxCC.Grounding.eval2_shiftRight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eval2_shiftRight

/-- info: 'IxCC.Grounding.eval2_beq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eval2_beq

/-- info: 'IxCC.Grounding.eval2_ble' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.eval2_ble

/-- info: 'IxCC.Grounding.natAccel_of_litOps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.natAccel_of_litOps

/-- info: 'IxCC.Grounding.lawsNoCanon_of_678' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.lawsNoCanon_of_678

/-- info: 'IxCC.Grounding.allP_of_check_678' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.allP_of_check_678

/-- info: 'IxCC.Grounding.const_of_check_678' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.const_of_check_678

/-- info: 'IxCC.Grounding.rootSound_678' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678

/-- info: 'IxCC.Grounding.fibRoot_678' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fibRoot_678

/-- info: 'IxCC.Grounding.decideRoot_678' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.decideRoot_678

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
    RelV M p κ lpsOf (· ∈ Sl) (Ok p ann) v (M.cval (κ c) φ) :=
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

/-! **The root theorems over #678's fields conclude exactly what the landed ones do**: each `example`
states the landed canonicity-free theorem's hypotheses with `Laws678` (verbatim copies of #678's
fields) for `LawsNoCanon` and the decided premise `LitDefs` (or its checker) added, and its conclusion
copied word for word from the landed theorem, and is proved by the new theorem. -/

section Conclusions678

open IxCC.Grounding Ix.Kernel Ix.Kernel.SetTheory
open IxCC.Src (Value CId Program Levels)

variable {V : Type} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

example (hL : Laws678 M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonB p env κ Sl = true)
    (hld : litDefsB env = true)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl)) :
    ∀ k, AllP M p κ lpsOf (· ∈ Sl) (Ok p ann) k :=
  allP_of_check_678 hL hchk hnc hld hT

example (hL : Laws678 M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonB p env κ Sl = true)
    (hld : litDefsB env = true)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {ls : Levels} {c : CId} {v : Value} {φ : LevelParam → Nat}
    (hrun : IxCC.Src.evalConst p k ls c = .ok v) (hc : c ∈ Sl) (hOk : Ok p ann c ls)
    (hlv : LvAt φ (lpsOf c) ls) :
    RelV M p κ lpsOf (· ∈ Sl) (Ok p ann) v (M.cval (κ c) φ) :=
  const_of_check_678 hL hchk hnc hld hT hrun hc hOk hlv

example (hL : Laws678 M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId} {args : List FoTy} {res : FoTy}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678 hL hG hC hNC hLD hR hT hA hrun hrb hRT hO φ ρ X hX

example (hL : Laws678 M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hR : RootFacts p env κ ann (· ∈ Sl) root [.nat] .nat)
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    {k n : Nat} {v : Value} {w : Nat} (hrun : IxCC.Src.run p k root [.lit n] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.nat w)) (φ : LevelParam → Nat) (ρ : BVarIdx → V)
    (X : V) (hX : Denotes M.cval env φ ρ (.app (.const (κ root) []) (litE n)) X) :
    Denotes M.cval env φ ρ (litE w) X :=
  fibRoot_678 hL hG hC hNC hLD hR hD hrun hrb φ ρ X hX

example (hL : Laws678 M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root boolD : CId}
    (hb : p.known.bool = some boolD) (hBL : BoolListed p boolD)
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFacts p env κ (· ∈ Sl))
    (hNC : NoCanon p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hR : RootFacts p env κ ann (· ∈ Sl) root [] (.enum boolD))
    (hD : DirectFacts p env κ lpsOf ann (· ∈ Sl))
    (hRT : ResultTag p env κ (· ∈ Sl) (.enum boolD) (.ctor 1 []))
    {k : Nat} {v : Value} (hrun : IxCC.Src.run p k root [] = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some (.ctor 1 [])) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (X : V) (hX : Denotes M.cval env φ ρ (.const (κ root) []) X) :
    Denotes M.cval env φ ρ (.const boolTrueName []) X :=
  decideRoot_678 hL hb hBL hG hC hNC hLD hR hD hRT hrun hrb φ ρ X hX

end Conclusions678

/-! **Step A: `case` entries over level-polymorphic families under a verified instance set**
(`IxCCGrounding.CaseLevels`, `IxCCGrounding.RootInst`). -/

/-- info: 'IxCC.Grounding.substFn_of_agree' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.substFn_of_agree

/-- info: 'IxCC.Grounding.majorAt_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.majorAt_of_agree

/-- info: 'IxCC.Grounding.caseFires_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseFires_of_agree

/-- info: 'IxCC.Grounding.posIn_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.posIn_spec

/-- info: 'IxCC.Grounding.eval_φAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.eval_φAt

/-- info: 'IxCC.Grounding.instFacts_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.instFacts_of_check

/-- info: 'IxCC.Grounding.caseLevelAgree_of_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseLevelAgree_of_inst

/-- info: 'IxCC.Grounding.CaseFactsRead.facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.CaseFactsRead.facts

/-- info: 'IxCC.Grounding.caseFactsRead_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseFactsRead_of_check

/-- info: 'IxCC.Grounding.noCanonA_of_noCanon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.noCanonA_of_noCanon

/-- info: 'IxCC.Grounding.noCanonA_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.noCanonA_of_check

/-- info: 'IxCC.Grounding.caseFires_of_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.caseFires_of_inst

/-- info: 'IxCC.Grounding.runs_of_sitesIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.runs_of_sitesIn

/-- info: 'IxCC.Grounding.fundHyps_of_inst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fundHyps_of_inst

/-- info: 'IxCC.Grounding.rootSound_678A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678A

/-- info: 'IxCC.Grounding.rootSound_678A_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678A_of_check

/-! **`rootSound_678A` concludes exactly what `rootSound_678` does**: the `example` states
`rootSound_678`'s hypotheses with `CaseFactsRead` for `CaseFacts`, `NoCanonA` for `NoCanon` and the
instance premises added, and `rootSound_678`'s conclusion copied word for word; the second, the
Boolean form, with `noCanonAB` for `noCanonB` and `instCheckB` added. -/

section ConclusionsA

open IxCC.Grounding Ix.Kernel Ix.Kernel.SetTheory
open IxCC.Src (Value CId Program Levels)

variable {V : Type} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

example (hL : Laws678 M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId} {args : List FoTy} {res : FoTy}
    {Inst : List (CId × Levels)}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678A hL hG hC hNC hLD hI hU hroot hR hT hA hrun hrb hRT hO φ ρ X hX

example (hL : Laws678 M) {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId} {args : List FoTy} {res : FoTy}
    {Inst : List (CId × Levels)}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    (hT : SitesOkRes M p κ lpsOf ann (· ∈ Sl))
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678A_of_check hL hchk hnc hld hinst hR hT hA hrun hrb hRT hO φ ρ X hX

end ConclusionsA

/-! **Typing at refused sites from #678's `graded` field** (`IxCCGrounding.Graded`). -/

/-- info: 'IxCC.Grounding.piBody_of_nthMeta' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.piBody_of_nthMeta

/-- info: 'IxCC.Grounding.piBody_succ' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.piBody_succ

/-- info: 'IxCC.Grounding.headRegimeAt_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.headRegimeAt_of_check

/-- info: 'IxCC.Grounding.headRegimeRes_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.headRegimeRes_of_check

/-- info: 'IxCC.Grounding.graded_sites' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.graded_sites

/-- info: 'IxCC.Grounding.graded_lam_of_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.graded_lam_of_pi

/-- info: 'IxCC.Grounding.runPair_graded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.runPair_graded

/-- info: 'IxCC.Grounding.exists_snoc' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.exists_snoc

/-- info: 'IxCC.Grounding.spine_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spine_mem

/-- info: 'IxCC.Grounding.head_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.head_pos

/-- info: 'IxCC.Grounding.sitesOkRes_of_graded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.sitesOkRes_of_graded

/-- info: 'IxCC.Grounding.rootSound_678G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678G

/-- info: 'IxCC.Grounding.rootSound_678G_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678G_of_check

/-! **`rootSound_678G` concludes exactly what `rootSound_678A` does, with no typing hypothesis**: the
`example`s state `rootSound_678A`'s hypotheses (and its Boolean form's) with `SitesOkRes` replaced by
`GradedLaw` and `HeadRegimeRes` (`headRegimeResB`), the conclusion copied word for word. -/

section ConclusionsG

open IxCC.Grounding Ix.Kernel Ix.Kernel.SetTheory
open IxCC.Src (Value CId Program Levels)

variable {V : Type} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

example (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hH : HeadRegimeRes p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678G hL hgr hG hC hNC hLD hI hU hroot hH hR hA hrun hrb hRT hO φ ρ X hX

example (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hhr : headRegimeResB p env κ lpsOf ann Sl = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678G_of_check hL hgr hchk hnc hld hinst hhr hR hA hrun hrb hRT hO φ ρ X hX

end ConclusionsG

/-! ## Step C: a `let` in a run term (the correspondence through a substitution, `Runs` with `σ`,
the environment relation under it, the walks' `let` cases) -/

/-- info: 'IxCC.Grounding.idσ_zero' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Grounding.idσ_zero

/-- info: 'IxCC.Grounding.liftσ_idσ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.liftσ_idσ

/-- info: 'IxCC.Grounding.idσ_get' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.idσ_get

/-- info: 'IxCC.Grounding.subAt0_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.subAt0_of_check

/-- info: 'IxCC.Grounding.termCorrS_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.termCorrS_of_check

/-- info: 'IxCC.Grounding.corrSB_idσ_of_termCorrB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.corrSB_idσ_of_termCorrB

/-- info: 'IxCC.Grounding.corrSB_of_termCorrB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.corrSB_of_termCorrB

/-- info: 'IxCC.Grounding.termCorrS_of_termCorr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.termCorrS_of_termCorr

/-- info: 'IxCC.Grounding.denotesIn_of_subAt0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.denotesIn_of_subAt0

/-- info: 'IxCC.Grounding.skipEnv_push_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.skipEnv_push_one

/-- info: 'IxCC.Grounding.relEnv_liftAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.relEnv_liftAll

/-- info: 'IxCC.Grounding.relEnv_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.relEnv_lift

/-- info: 'IxCC.Grounding.mentions_let_val' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.mentions_let_val

/-- info: 'IxCC.Grounding.mentions_let_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.mentions_let_body

/-- info: 'IxCC.Grounding.relEnv_pushAll_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.relEnv_pushAll_gen

/-- info: 'IxCC.Grounding.evalSites_mem_P' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.evalSites_mem_P

/-- info: 'IxCC.Grounding.gradedBy_of_subAt0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.gradedBy_of_subAt0

/-! **Every run-term site typed from `graded`: the head's type read through δ and β** (`IxCCGrounding.GradedHead`, step 1b). -/

/-- info: 'IxCC.Grounding.holds_pwChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.holds_pwChain

/-- info: 'IxCC.Grounding.tyRead_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.tyRead_of_check

/-- info: 'IxCC.Grounding.spineRead_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spineRead_of_check

/-- info: 'IxCC.Grounding.SpineRead.head_getApp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.SpineRead.head_getApp

/-- info: 'IxCC.Grounding.tyRead_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.tyRead_prefix

/-- info: 'IxCC.Grounding.spineRead_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spineRead_prefix

/-- info: 'IxCC.Grounding.mem_evalSitesPs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.mem_evalSitesPs

/-- info: 'IxCC.Grounding.mem_filter_irr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.mem_filter_irr

/-- info: 'IxCC.Grounding.profileOf_mem_okProfiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.profileOf_mem_okProfiles

/-- info: 'IxCC.Grounding.headRegime_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.headRegime_of_check

/-- info: 'IxCC.Grounding.mem_spineHere' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Grounding.mem_spineHere

/-- info: 'IxCC.Grounding.spinesPs_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spinesPs_tail

/-- info: 'IxCC.Grounding.spinesPs_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spinesPs_cover

/-- info: 'IxCC.Grounding.take_dropLast' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.take_dropLast

/-- info: 'IxCC.Grounding.headRegimeS_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.headRegimeS_of_check

/-- info: 'IxCC.Grounding.gradedBy_mkAppN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.gradedBy_mkAppN

/-- info: 'IxCC.Grounding.spineMem_of_graded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spineMem_of_graded

/-- info: 'IxCC.Grounding.beta_peel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.beta_peel

/-- info: 'IxCC.Grounding.gradedBy_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.gradedBy_lift

/-- info: 'IxCC.Grounding.gradedBy_lift1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.gradedBy_lift1

/-- info: 'IxCC.Grounding.denotesList_lift1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.denotesList_lift1

/-- info: 'IxCC.Grounding.tyRead_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.tyRead_pos

/-- info: 'IxCC.Grounding.gradedCtx_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.gradedCtx_get

/-- info: 'IxCC.Grounding.graded_sites_ctx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.graded_sites_ctx

/-- info: 'IxCC.Grounding.spineRead_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.spineRead_pos

/-- info: 'IxCC.Grounding.head_posG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.head_posG

/-- info: 'IxCC.Grounding.sitesOk_of_headRegime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.sitesOk_of_headRegime

/-- info: 'IxCC.Grounding.rootSound_678AS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678AS

/-- info: 'IxCC.Grounding.rootSound_678AG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678AG

/-- info: 'IxCC.Grounding.rootSound_678AG_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678AG_of_check

/-! **`rootSound_678AG` concludes exactly what `rootSound_678A` does, with no typing hypothesis and
no direct route at run-term sites**: the `example`s state `rootSound_678A`'s hypotheses (and its
Boolean form's) with `SitesOkRes` replaced by `GradedLaw` and `HeadRegime` (`headRegimeSB`, the
per-spine decision), the conclusion copied word for word. -/

section ConclusionsAG

open IxCC.Grounding Ix.Kernel Ix.Kernel.SetTheory
open IxCC.Src (Value CId Program Levels)

variable {V : Type} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

example (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hG : GroundFacts p env κ lpsOf ann (· ∈ Sl)) (hC : CaseFactsRead p env κ (· ∈ Sl))
    (hNC : NoCanonA p env κ (· ∈ Sl)) (hLD : LitDefs env)
    (hI : InstClosed p Inst) (hU : InstUniform p env κ lpsOf Inst) (hroot : (root, []) ∈ Inst)
    (hH : HeadRegime p env κ lpsOf ann (· ∈ Sl))
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678AG hL hgr hG hC hNC hLD hI hU hroot hH hR hA hrun hrb hRT hO φ ρ X hX

example (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheck p env κ lpsOf ann Sl = true) (hnc : noCanonAB p env κ Sl = true)
    (hld : litDefsB env = true) (hinst : instCheckB p env κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p env κ lpsOf ann Sl = true)
    (hR : RootFacts p env κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o) (hRT : ResultTag p env κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678AG_of_check hL hgr hchk hnc hld hinst hhr hR hA hrun hrb hRT hO φ ρ X hX

end ConclusionsAG

/-! **`autoParam`/`optParam` binders in an `eqn` function's type: the check on the retyped reading** (`IxCCGrounding.SelRetype`, step Ap). -/

/-- info: 'IxCC.Grounding.selDom_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selDom_of_check

/-- info: 'IxCC.Grounding.selTele_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selTele_of_check

/-- info: 'IxCC.Grounding.selIdx_peel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selIdx_peel

/-- info: 'IxCC.Grounding.selDom_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selDom_den

/-- info: 'IxCC.Grounding.selTele_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selTele_den

/-- info: 'IxCC.Grounding.selRetypeL_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selRetypeL_map

/-- info: 'IxCC.Grounding.selRetype_selEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selRetype_selEnv

/-- info: 'IxCC.Grounding.SelRetype1.name' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.SelRetype1.name

/-- info: 'IxCC.Grounding.SelRetype1.levelParams' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.SelRetype1.levelParams

/-- info: 'IxCC.Grounding.SelRetype1.eq_of_not_defn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.SelRetype1.eq_of_not_defn

/-- info: 'IxCC.Grounding.find?_retype' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.find?_retype

/-- info: 'IxCC.Grounding.find?_back' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.find?_back

/-- info: 'IxCC.Grounding.find?_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.find?_fwd

/-- info: 'IxCC.Grounding.find?_nondefn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.find?_nondefn

/-- info: 'IxCC.Grounding.findProj?_selRetype' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.findProj?_selRetype

/-- info: 'IxCC.Grounding.mem_retype' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.mem_retype

/-- info: 'IxCC.Grounding.denotes_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.denotes_transfer

/-- info: 'IxCC.Grounding.denotes_selRetype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.denotes_selRetype

/-- info: 'IxCC.Grounding.denotes_selRetype'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.denotes_selRetype'

/-- info: 'IxCC.Grounding.fits_selRetype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.fits_selRetype

/-- info: 'IxCC.Grounding.denotesList_selRetype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.denotesList_selRetype

/-- info: 'IxCC.Grounding.model_selRetype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.model_selRetype

/-- info: 'IxCC.Grounding.laws678_selRetype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.laws678_selRetype

/-- info: 'IxCC.Grounding.gradedLaw_selRetype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.gradedLaw_selRetype

/-- info: 'IxCC.Grounding.rootSound_678AGp_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.rootSound_678AGp_of_check

/-- info: 'IxCC.Grounding.selEnv_unrepaired_refuted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selEnv_unrepaired_refuted

/-- info: 'IxCC.Grounding.selEnv_repaired_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.selEnv_repaired_ok

/-! **`rootSound_678AGp_of_check` concludes for the reading what `rootSound_678A` does**: every
check on `selEnv`, the conclusion copied word for word. -/

section ConclusionsAGp

open IxCC.Grounding Ix.Kernel Ix.Kernel.SetTheory
open IxCC.Src (Value CId Program Levels)

variable {V : Type} [Ix.Kernel.SetTheory V] {env : KEnv} {M : Model V env}

example (hL : Laws678 M) (hgr : GradedLaw M.cval env) {p : Program} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId} {root : CId}
    {args : List FoTy} {res : FoTy} {Inst : List (CId × Levels)}
    (hchk : groundCheck p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hnc : noCanonAB p (selEnv p env κ Sl) κ Sl = true)
    (hld : litDefsB (selEnv p env κ Sl) = true)
    (hinst : instCheckB p (selEnv p env κ Sl) κ lpsOf [root] Inst = true)
    (hhr : headRegimeSB p (selEnv p env κ Sl) κ lpsOf ann Sl = true)
    (hR : RootFacts p (selEnv p env κ Sl) κ ann (· ∈ Sl) root args res)
    {k : Nat} {xs : List Value} {es : List KExpr} {v : Value} {o : IxCC.Sem.Obs} {eo : KExpr}
    (hA : FoArgs p κ args xs es) (hrun : IxCC.Src.run p k root xs = .ok v)
    (hrb : IxCC.Src.readbackAll p v = some o)
    (hRT : ResultTag p (selEnv p env κ Sl) κ (· ∈ Sl) res o)
    (hO : FoObs p κ res o eo) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V)
    (hX : Denotes M.cval env φ ρ (Expr.mkAppN (.const (κ root) []) es) X) :
    Denotes M.cval env φ ρ eo X :=
  rootSound_678AGp_of_check hL hgr hchk hnc hld hinst hhr hR hA hrun hrb hRT hO φ ρ X hX

end ConclusionsAGp

/-! ## Step C's closure-capture shape (`cloShapeB`, `cloSite?`; `TermCorrS.letClo`, `Runs.letClo`,
`RelV.clo`'s environment related at the members of the λ's domain, the walks' closure branch: the
landed theorems that changed keep the sets above) -/

/-- info: 'IxCC.Grounding.cloShapeB_lam' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.cloShapeB_lam

/-- info: 'IxCC.Grounding.cloSite?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.cloSite?_spec

/-! ## The witness shape (the minor-premise shape of a deep `let`: `UnderLams`, `lamPath`,
`witSite?`, `witDoms`, the conjunct `letWit`; `TermCorrS.letWit`, `Runs.letWit`, the walks' witness
branch: the landed theorems that changed keep the sets above) -/

/-- info: 'IxCC.Grounding.underLams_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.underLams_of_check

/-- info: 'IxCC.Grounding.witSite?_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.witSite?_spec

/-- info: 'IxCC.Grounding.witness_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.witness_of_check

/-- info: 'IxCC.Grounding.witDoms_of_termCorr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.witDoms_of_termCorr

/-- info: 'IxCC.Grounding.denotesIn_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.denotesIn_under

/-- info: 'IxCC.Grounding.ctxExt_of_wits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.ctxExt_of_wits

/-- info: 'IxCC.Grounding.relEnv_liftN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.relEnv_liftN

/-- info: 'IxCC.Grounding.gradedBy_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.gradedBy_under

/-- info: 'IxCC.Grounding.gradedCtx_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Grounding.gradedCtx_under
