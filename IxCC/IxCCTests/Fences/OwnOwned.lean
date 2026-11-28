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

/-! Ownership signatures of primitives (`Own/Plain/PrimSig.lean`): the checker's step under a
signature is today's on today's primitives (`primStep_conservative`, so `bindStep` is `bindCtx`),
what an accepted step established, and the step against the semantics for a primitive that
touches no heap, from the signature's contract (`prim_step_pure`, `lamSig_pureSound`). -/

/-- info: 'IxCC.Own.Plain.primStep_conservative' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.primStep_conservative

/-- info: 'IxCC.Own.Plain.bindStep_eq_bindCtx' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.bindStep_eq_bindCtx

/-- info: 'IxCC.Own.Plain.primImmArgs_eq_sig' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.primImmArgs_eq_sig

/-- info: 'IxCC.Own.Plain.except_ok_bind' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.Plain.except_ok_bind

/-- info: 'IxCC.Own.Plain.primStep_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.primStep_eq

/-- info: 'IxCC.Own.Plain.primStep_noConsume' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.primStep_noConsume

/-- info: 'IxCC.Own.Plain.markImm_eq_immArgs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.markImm_eq_immArgs

/-- info: 'IxCC.Own.Plain.takeConsumed_noConsume' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.takeConsumed_noConsume

/-- info: 'IxCC.Own.Plain.Ctx.held_eq_avail' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.Plain.Ctx.held_eq_avail

/-- info: 'IxCC.Own.Plain.checkRead_of_avail' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkRead_of_avail

/-- info: 'IxCC.Own.Plain.checkRead_held' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkRead_held

/-- info: 'IxCC.Own.Plain.checkCode_bindStep' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkCode_bindStep

/-- info: 'IxCC.Own.Plain.primStep_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.primStep_ok

/-- info: 'IxCC.Own.Plain.takeConsumed_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.takeConsumed_sem

/-- info: 'IxCC.Own.Plain.OwnedPre.markImm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.OwnedPre.markImm

/-- info: 'IxCC.Own.Plain.OwnedPre.releaseIf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.OwnedPre.releaseIf

/-- info: 'IxCC.Own.Plain.evalArgs_var_at' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalArgs_var_at

/-- info: 'IxCC.Own.Plain.lamSig_pureSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.lamSig_pureSound

/-- info: 'IxCC.Own.Plain.prim_step_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.prim_step_pure
