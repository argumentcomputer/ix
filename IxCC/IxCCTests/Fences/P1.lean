import IxCC.Src.Relevance.Proof.P1.Prefix
import IxCC.Recheck.Proof.FrontAccepted

/-! Required axiom fences for P1's proved parts (relevance preservation is not proved; its
definitions are `Src.Relevance.Proof.P1.Defs`, whose `live_not_irr` is fenced in `Fences/Erase.lean`):
the prefix of a spine whose next argument is not read (`P1.Prefix`: `eval_shielded_prefix`,
`eval_erased_prefix` and the lemmas they rest on), and what the front end's acceptance gives
(`Recheck.Proof.FrontAccepted`: `front_accepted`, `shapeOk_of_run`).
Expected messages are preserved verbatim. -/

/-! The prefix lemmas (`P1.Prefix`). -/

/-- info: 'IxCC.Src.Relevance.Proof.P1.bind_ok_inv' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.bind_ok_inv

/-- info: 'IxCC.Src.Relevance.Proof.P1.spine_go_acc' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.spine_go_acc

/-- info: 'IxCC.Src.Relevance.Proof.P1.spineL_app' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.spineL_app

/-- info: 'IxCC.Src.Relevance.Proof.P1.mkApps_spineL' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.mkApps_spineL

/-- info: 'IxCC.Src.Relevance.Proof.P1.lamRels_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.lamRels_eq

/-- info: 'IxCC.Src.Relevance.Proof.P1.alwaysIrr_irrAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.alwaysIrr_irrAt

/-- info: 'IxCC.Src.Relevance.Proof.P1.applySpine_lamChain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.applySpine_lamChain

/-- info: 'IxCC.Src.Relevance.Proof.P1.applySpine_stuck' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.applySpine_stuck

/-- info: 'IxCC.Src.Relevance.Proof.P1.applySpine_ignoresSlot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.applySpine_ignoresSlot

/-- info: 'IxCC.Src.Relevance.Proof.P1.relevantRefs_mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.relevantRefs_mono

/-- info: 'IxCC.Src.Relevance.Proof.P1.head_mem_relevantRefs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.head_mem_relevantRefs

/-- info: 'IxCC.Src.Relevance.Proof.P1.spineC_head_lam' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.spineC_head_lam

/-- info: 'IxCC.Src.Relevance.Proof.P1.termC_lamBinder_erased' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.termC_lamBinder_erased

/-- info: 'IxCC.Src.Relevance.Proof.P1.body_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.body_prefix

/-- info: 'IxCC.Src.Relevance.Proof.P1.eval_shielded_prefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.eval_shielded_prefix

/-- info: 'IxCC.Src.Relevance.Proof.P1.eval_erased_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Src.Relevance.Proof.P1.eval_erased_prefix

/-! What the front end's acceptance gives (`Recheck.Proof.FrontAccepted`). -/

/-- info: 'IxCC.Recheck.front_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.front_accepted

/-- info: 'IxCC.Recheck.shapeOk_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.shapeOk_of_run
