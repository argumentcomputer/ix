import IxCC.Own.Plain.Proof.Owned.Program
import IxCC.Own.Plain.Proof.Owned.Reach
import IxCC.Own.Plain.Proof.Owned.Takes
import IxCC.Own.Plain.Proof.Owned.Simulation
import IxCC.Own.Plain.Proof.Certificate
import IxCC.Cfg.Rc.Proof.Owned.Admission
import IxCC.Cfg.Rc.Proof.Physical.PublicEntry
import IxCC.Recheck.Rc.Proof.Replay

/-! Exact axiom fences for Track A3: interprocedural `@borrowed` parameters,
`ReachablePreserved`, certificate v2 admission (`decodeWith` / `admit_of_with`),
and physical simulation through `Cfg.Rc` and `Recheck.RcReplay`. -/

/-- info: 'IxCC.Own.Plain.checkOwnedWith_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwnedWith_refines

/-- info: 'IxCC.Own.Plain.checkContractOwnedWith_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkContractOwnedWith_refines

/-- info: 'IxCC.Own.Plain.checkOwnedWith_export_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwnedWith_export_refines

/-- info: 'IxCC.Own.Plain.checkOwnedWith_export_reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwnedWith_export_reclaims

/-- info: 'IxCC.Own.Plain.checkContractOwnedWith_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkContractOwnedWith_parts

/-- info: 'IxCC.Own.Plain.borrowsValid_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.borrowsValid_leaf

/-- info: 'IxCC.Own.Plain.borrowsValid_export' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.borrowsValid_export

/-- info: 'IxCC.Own.Plain.ownedState_entryWith_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ownedState_entryWith_exact

/-- info: 'IxCC.Own.Plain.takeOwnedArgs_call_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.takeOwnedArgs_call_sem

/-- info: 'IxCC.Own.Plain.takeOwnedArgs_tail_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.takeOwnedArgs_tail_sem

/-- info: 'IxCC.Own.Plain.ReachablePreserved.inc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ReachablePreserved.inc

/-- info: 'IxCC.Own.Plain.ReachablePreserved.alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ReachablePreserved.alloc

/-- info: 'IxCC.Own.Plain.ReachablePreserved.dropAll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ReachablePreserved.dropAll

/-- info: 'IxCC.Own.Plain.ReachablePreserved.reuseCell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ReachablePreserved.reuseCell

/-- info: 'IxCC.Own.Plain.ReachablePreserved.den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ReachablePreserved.den

/-- info: 'IxCC.Own.Plain.Certificate.decode_implies_decodeWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.decode_implies_decodeWith

/-- info: 'IxCC.Own.Plain.Certificate.admit_of_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Certificate.admit_of_with
