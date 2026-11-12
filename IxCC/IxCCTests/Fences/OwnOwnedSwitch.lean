import IxCC.Cfg.Rc.Proof.Native.PhysicalSimulation
import IxCC.Cfg.Rc.Proof.Owned.Admission
import IxCC.Own.Plain.Proof.Certificate
import IxCC.Own.Plain.Proof.Retained
import IxCC.Recheck.Rc.Proof.Replay

/-! Exact axiom inventory of heap stage 2's second landing: the verifier over the ownership
checker (the activation layer's new steps, the allocation step for a multiset of tokens, admission
with the captured-work budget, the checker's language and retained forms, the milestone-1
lemmas strengthened for it, and that nothing admitted before the switch is refused after it). -/

/-- info: 'IxCC.Cfg.Rc.Native.Spec.physical_inc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.physical_inc

/-- info: 'IxCC.Cfg.Rc.Native.Spec.physical_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.physical_dec

/-- info: 'IxCC.Cfg.Rc.Native.Spec.copy_marker_step_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.copy_marker_step_of

/-- info: 'IxCC.Cfg.Rc.Native.Spec.evalActions_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.evalActions_single

/-- info: 'IxCC.Cfg.Rc.Native.Spec.evalAction_inc_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.evalAction_inc_congr

/-- info: 'IxCC.Cfg.Rc.Native.Spec.evalAction_dec_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.evalAction_dec_congr

/-- info: 'IxCC.Cfg.Rc.Native.fused_allocation_source_wrapper_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.fused_allocation_source_wrapper_of

/-- info: 'IxCC.Cfg.Rc.Native.fused_allocation_instruction_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.fused_allocation_instruction_of

/-- info: 'IxCC.Cfg.Rc.Native.allocation_step_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.allocation_step_of

/-- info: 'IxCC.Cfg.Rc.checkScopedProgram_checkOwned' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checkScopedProgram_checkOwned

/-- info: 'IxCC.Cfg.Rc.checkScopedProgram_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checkScopedProgram_owned

/-- info: 'IxCC.Cfg.Rc.checkScopedProgram_ownedParts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.checkScopedProgram_ownedParts

/-- info: 'IxCC.Cfg.Rc.Native.Spec.holdRoots_sameRefs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.holdRoots_sameRefs

/-- info: 'IxCC.Cfg.Rc.Native.Spec.checked_owned_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.checked_owned_body

/-- info: 'IxCC.Cfg.Rc.Native.Spec.bind_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.bind_result

/-- info: 'IxCC.Cfg.Rc.Native.Spec.ownCase_erase' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.ownCase_erase

/-- info: 'IxCC.Own.Plain.Certificate.admit_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_ok

/-- info: 'IxCC.Own.Plain.Certificate.admit_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_of

/-- info: 'IxCC.Own.Plain.Certificate.admit_of_checkPlainMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_of_checkPlainMap

/-- info: 'IxCC.Own.Plain.Certificate.admit_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_mono

/-- info: 'IxCC.Own.Plain.Certificate.admit_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_budget

/-- info: 'IxCC.Own.Plain.Certificate.admitContract_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admitContract_ok

/-- info: 'IxCC.Own.Plain.Certificate.admitContract_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admitContract_of

/-- info: 'IxCC.Own.Plain.Certificate.admitContract_of_checkContractPlainMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admitContract_of_checkContractPlainMap

/-- info: 'IxCC.Own.Plain.Certificate.admitContract_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admitContract_mono

/-- info: 'IxCC.Own.Plain.Certificate.checkBudget_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.checkBudget_ok

/-- info: 'IxCC.Recheck.RcReplay.runFront_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.runFront_budget

/-- info: 'IxCC.Own.Plain.owned_call_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.owned_call_sim

/-- info: 'IxCC.Own.Plain.owned_refines_lang' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.owned_refines_lang

/-- info: 'IxCC.Own.Plain.owned_lower_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.owned_lower_refines

/-- info: 'IxCC.Own.Plain.owned_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.owned_retained

/-- info: 'IxCC.Own.Plain.ownedState_entry_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ownedState_entry_exact

/-- info: 'IxCC.Own.Plain.inc_step_refs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.inc_step_refs

/-- info: 'IxCC.Own.Plain.dec_step_refs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.dec_step_refs

/-- info: 'IxCC.Own.Plain.jump_body_refs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.jump_body_refs

/-- info: 'IxCC.Own.Plain.arg_step_refs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.arg_step_refs

