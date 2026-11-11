import IxCCGrounding.Ground

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
