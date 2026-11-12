import IxCC.Own.Plain.Owned
import IxCC.Own.Plain.Proof.Owned.Context
import IxCC.Own.Plain.Proof.Owned.Roots
import IxCC.Own.Plain.Proof.Owned.State
import IxCC.Own.Plain.Proof.Owned.Takes
import IxCC.Own.Plain.Proof.Owned.Steps
import IxCC.Own.Plain.Proof.Owned.Binds
import IxCC.Own.Plain.Proof.Owned.Actions
import IxCC.Own.Plain.Proof.Owned.Rhs
import IxCC.Own.Plain.Proof.Owned.Joins
import IxCC.Own.Plain.Proof.Owned.Inversion
import IxCC.Own.Plain.Proof.Owned.Simulation
import IxCC.Own.Plain.Proof.Owned.Program
import IxCC.Own.Plain.Proof.OwnedCanonical
import IxCC.Own.Plain.Proof.OwnedAccepts

/-! Exact axiom fences for the ownership checker (heap stage 2, milestone 1,
`docs/data-and-roots-design.md`): refinement and reclamation for every body map the checker
accepts, the Own-level induction over a typing context, canonical acceptance (every map
`checkPlainMap` accepts, `checkOwned` accepts), and the landed `checked_program_refines`,
`checked_contract_program_refines` and `checked_program_reclaims` re-derived from them. -/

/-- info: 'IxCC.Own.Plain.checkOwned_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwned_refines

/-- info: 'IxCC.Own.Plain.checkContractOwned_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkContractOwned_refines

/-- info: 'IxCC.Own.Plain.checkOwned_reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwned_reclaims

/-- info: 'IxCC.Own.Plain.checkContractOwned_reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkContractOwned_reclaims

/-- info: 'IxCC.Own.Plain.checkOwned_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwned_shape

/-- info: 'IxCC.Own.Plain.checkContractOwned_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkContractOwned_shape

/-- info: 'IxCC.Own.Plain.owned_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.owned_refines

/-- info: 'IxCC.Own.Plain.owned_refines_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.owned_refines_of

/-- info: 'IxCC.Own.Plain.owned_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.owned_eval

/-- info: 'IxCC.Own.Plain.owned_call_of_smaller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.owned_call_of_smaller

/-- info: 'IxCC.Own.Plain.ownedState_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ownedState_entry

/-- info: 'IxCC.Own.Plain.checkContractOwned_parts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkContractOwned_parts

/-- info: 'IxCC.Own.Plain.checkOwned_contract' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkOwned_contract

/-- info: 'IxCC.Own.Plain.checkMapE_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkMapE_ok

/-- info: 'IxCC.Own.Plain.erases_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.erases_sound

/-- info: 'IxCC.Own.Plain.checkPlainMap_checkOwned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkPlainMap_checkOwned

/-- info: 'IxCC.Own.Plain.checkContractPlainMap_checkContractOwned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkContractPlainMap_checkContractOwned

/-- info: 'IxCC.Own.Plain.canonical_checkMapE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canonical_checkMapE

/-- info: 'IxCC.Own.Plain.lowerCode_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.lowerCode_checks

/-- info: 'IxCC.Own.Plain.canonical_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canonical_transfer

/-- info: 'IxCC.Own.Plain.canon_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canon_entry

/-- info: 'IxCC.Own.Plain.erases_self' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.erases_self

/-- info: 'IxCC.Own.Plain.checked_program_refines'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checked_program_refines'

/-- info: 'IxCC.Own.Plain.checked_contract_program_refines'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checked_contract_program_refines'

/-- info: 'IxCC.Own.Plain.checked_program_reclaims'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checked_program_reclaims'
