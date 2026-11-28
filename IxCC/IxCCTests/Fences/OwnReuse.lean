import IxCC.Own.Plain.Proof.Owned.Program
import IxCC.Own.Plain.Proof.Owned.Reset
import IxCC.Own.Plain.Proof.Certificate
import IxCC.Cfg.Rc.Proof.Inline
import IxCC.Cfg.Rc.Proof.Prune
import IxCC.Cfg.Rc.Proof.Physical.ReuseWrappers
import IxCC.Cfg.Rc.Proof.Physical.ReuseResult
import IxCC.Recheck.Rc.Proof.ObjectSound

/-! Exact axiom fences for Track A4: dynamic `reset`/`reuse`, static `@unique` unconditional
in-place `writeCell` reuse, certificate v3 admission (`decodeFull` / `admit_of_full`),
inline RC/reuse simulation, concrete LIR reuse wrapper execution, physical `reset`/`reuse`/`dropSlot`
simulation, and end-to-end `Recheck.RcReplay.sound`. -/

/-- info: 'IxCC.Own.Plain.checkOwnedFull_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwnedFull_refines

/-- info: 'IxCC.Own.Plain.checkOwnedFull_export_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwnedFull_export_refines

/-- info: 'IxCC.Own.Plain.checkOwnedFull_export_reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwnedFull_export_reclaims

/-- info: 'IxCC.Own.Plain.uniqsValid_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.uniqsValid_leaf

/-- info: 'IxCC.Own.Plain.uniqsValid_export' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.uniqsValid_export

/-- info: 'IxCC.Own.Plain.reset_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.reset_step

/-- info: 'IxCC.Own.Plain.reuse_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.reuse_step

/-- info: 'IxCC.Own.Plain.dropSlot_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.dropSlot_step

/-- info: 'IxCC.Own.Plain.Certificate.decodeWith_implies_decodeFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.decodeWith_implies_decodeFull

/-- info: 'IxCC.Own.Plain.Certificate.decode_implies_decodeFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.decode_implies_decodeFull

/-- info: 'IxCC.Own.Plain.Certificate.admit_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_of_full

/-- info: 'IxCC.Own.Plain.Certificate.admitContract_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admitContract_of_full

/-- info: 'IxCC.Cfg.Rc.Native.reuse_wrapper_inplace_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.reuse_wrapper_inplace_exec

/-- info: 'IxCC.Cfg.Rc.Native.reuse_wrapper_fallback_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.reuse_wrapper_fallback_exec

/-- info: 'IxCC.Cfg.Rc.Native.reset_wrapper_unique_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.reset_wrapper_unique_exec

/-- info: 'IxCC.Cfg.Rc.Native.reset_wrapper_shared_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.reset_wrapper_shared_exec

/-- info: 'IxCC.Cfg.Rc.Native.reset_wrapper_imm_exec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.reset_wrapper_imm_exec

/-- info: 'IxCC.Cfg.Rc.Native.Spec.physical_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.physical_reset

/-- info: 'IxCC.Cfg.Rc.Native.Spec.physical_reuse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.physical_reuse

/-- info: 'IxCC.Cfg.Rc.Native.Spec.physical_dropSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Native.Spec.physical_dropSlot

/-- info: 'IxCC.Cfg.Rc.Inline.inlineProgram_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Inline.inlineProgram_sim

/-- info: 'IxCC.Cfg.Rc.Prune.pruneUnusedReuse_inlineProgram_sim_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Cfg.Rc.Prune.pruneUnusedReuse_inlineProgram_sim_clock

/-- info: 'IxCC.Recheck.RcReplay.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.sound
