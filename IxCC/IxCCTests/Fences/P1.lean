import IxCC.Src.Relevance.Proof.P1.Prefix
import IxCC.Recheck.Proof.FrontAccepted

/-! Required axiom fences for P1's proved parts (relevance preservation is not proved; its
definitions are `Src.Relevance.Proof.P1.Defs`, whose `live_not_irr` is fenced in `Fences/Erase.lean`):
the prefix of a spine whose next argument is not read (`P1.Prefix`: `eval_shielded_prefix`,
`eval_erased_prefix` and the lemmas they rest on), and what the front end's acceptance gives
(`Recheck.Proof.FrontAccepted`: `front_accepted`, `shapeOk_of_run`).
Expected messages are preserved verbatim. -/

#print axioms IxCC.Src.Relevance.Proof.P1.bind_ok_inv

#print axioms IxCC.Src.Relevance.Proof.P1.spine_go_acc

#print axioms IxCC.Src.Relevance.Proof.P1.spineL_app

#print axioms IxCC.Src.Relevance.Proof.P1.mkApps_spineL

#print axioms IxCC.Src.Relevance.Proof.P1.lamRels_eq

#print axioms IxCC.Src.Relevance.Proof.P1.alwaysIrr_irrAt

#print axioms IxCC.Src.Relevance.Proof.P1.applySpine_lamChain

#print axioms IxCC.Src.Relevance.Proof.P1.applySpine_stuck

#print axioms IxCC.Src.Relevance.Proof.P1.applySpine_ignoresSlot

#print axioms IxCC.Src.Relevance.Proof.P1.relevantRefs_mono

#print axioms IxCC.Src.Relevance.Proof.P1.head_mem_relevantRefs

#print axioms IxCC.Src.Relevance.Proof.P1.spineC_head_lam

#print axioms IxCC.Src.Relevance.Proof.P1.termC_lamBinder_erased

#print axioms IxCC.Src.Relevance.Proof.P1.body_prefix

#print axioms IxCC.Src.Relevance.Proof.P1.eval_shielded_prefix

#print axioms IxCC.Src.Relevance.Proof.P1.eval_erased_prefix

#print axioms IxCC.Recheck.front_accepted

#print axioms IxCC.Recheck.shapeOk_of_run
