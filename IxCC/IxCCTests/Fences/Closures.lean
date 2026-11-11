import IxCC.Anf.Proof.Entry
import IxCC.Anf.Proof.Pass.Closures
import IxCC.Recheck.Proof.Middle
import IxCC.Recheck.Proof.Soundness
import IxCC.Recheck.Proof.RootShape
import IxCC.Recheck.Rc.Proof.RootTree
import IxCC.Sem.View
import IxCC.Sem.TracedTransform

/-! Required axiom fences for the closures step (`Anf.Pipeline.closures`: the
roots' entries at their declared parameter counts, then P8) on the recheck
path: refinement on a set of inputs (`Sem.RefinesOn`, `Sem.Viewed.refinesOn`,
`Sem.RefinesOn.ofPure`); the identity relation from a program to an
extension of it (`Anf.Rel.Ident.level_ext`); the entries
(`Anf.Entry.Proof`: shape, exact arity on inputs of the declared count, and
refinement on them); the step (`Anf.Pipeline.Proof.closures_correct`,
`closures_lower_ne_closures`: `fir.closures` is unreachable after it, and
`closures_of_lower`: a program `Fir.lower` accepts with its roots at their
declared counts passes unchanged; `Fir.Proof.lower_ok_firstOrder`); and the
recheck path's middle end with the step (`Recheck.anfOf_refines` on the
covered inputs, `anfOf_of_lower`, `covered_of_unchanged` and
`sound_unchanged`: for a program the step leaves unchanged, every input is
covered, as before the step; `Artifact.covered_head` on each path: a claim's
inputs are covered). -/

/-- info: 'IxCC.Sem.Refines.on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Refines.on

/-- info: 'IxCC.Sem.RefinesOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.RefinesOn.mono

/-- info: 'IxCC.Sem.RefinesOn.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.RefinesOn.trans

/-- info: 'IxCC.Sem.RefinesOn.trans_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.RefinesOn.trans_refines

/-- info: 'IxCC.Sem.RefinesOn.refines_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.RefinesOn.refines_trans

/-- info: 'IxCC.Sem.RefinesOn.backward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.RefinesOn.backward

/-- info: 'IxCC.Sem.RefinesOn.safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.RefinesOn.safe

/-- info: 'IxCC.Sem.RefinesOn.diverges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.RefinesOn.diverges

/-- info: 'IxCC.Sem.Viewed.refines_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Viewed.refines_at

/-- info: 'IxCC.Sem.Viewed.refinesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.Viewed.refinesOn

/-- info: 'IxCC.Sem.RefinesOn.ofPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Sem.RefinesOn.ofPure

/-- info: 'IxCC.Anf.Rel.Ident.app_at_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Rel.Ident.app_at_ext

/-- info: 'IxCC.Anf.Rel.Ident.call_at_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Rel.Ident.call_at_ext

/-- info: 'IxCC.Anf.Rel.Ident.glob_at_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Rel.Ident.glob_at_ext

/-- info: 'IxCC.Anf.Rel.Ident.level_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Rel.Ident.level_ext

/-- info: 'IxCC.Anf.Entry.Proof.plan_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.plan_length

/-- info: 'IxCC.Anf.Entry.Proof.plan_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.plan_keys

/-- info: 'IxCC.Anf.Entry.Proof.plan_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.plan_root

/-- info: 'IxCC.Anf.Entry.Proof.get?_foldl_insert_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.get?_foldl_insert_not

/-- info: 'IxCC.Anf.Entry.Proof.get?_foldl_insert_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.get?_foldl_insert_mem

/-- info: 'IxCC.Anf.Entry.Proof.run_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_ok

/-- info: 'IxCC.Anf.Entry.Proof.keys_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.keys_nodup

/-- info: 'IxCC.Anf.Entry.Proof.key_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.key_ge

/-- info: 'IxCC.Anf.Entry.Proof.run_global_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_global_old

/-- info: 'IxCC.Anf.Entry.Proof.run_global_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_global_new

/-- info: 'IxCC.Anf.Entry.Proof.run_tables' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_tables

/-- info: 'IxCC.Anf.Entry.Proof.run_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_extends

/-- info: 'IxCC.Anf.Entry.Proof.run_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_wf

/-- info: 'IxCC.Anf.Entry.Proof.run_roots_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_roots_length

/-- info: 'IxCC.Anf.Entry.Proof.run_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_root

/-- info: 'IxCC.Anf.Entry.Proof.run_exactArity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_exactArity

/-- info: 'IxCC.Anf.Entry.Proof.eval_body' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.eval_body

/-- info: 'IxCC.Anf.Entry.Proof.run_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_entry

/-- info: 'IxCC.Anf.Entry.Proof.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Entry.Proof.run_refines

/-- info: 'IxCC.Anf.Pipeline.Proof.run_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.run_wf

/-- info: 'IxCC.Anf.Pipeline.Proof.closures_of_plain' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.closures_of_plain

/-- info: 'IxCC.Anf.Pipeline.Proof.closures_cases' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.closures_cases

/-- info: 'IxCC.Anf.Pipeline.Proof.closures_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.closures_firstOrder

/-- info: 'IxCC.Anf.Pipeline.Proof.closures_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.closures_correct

/-- info: 'IxCC.Anf.Pipeline.Proof.rows_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.rows_keys

/-- info: 'IxCC.Anf.Pipeline.Proof.closures_tables' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.closures_tables

/-- info: 'IxCC.Anf.Pipeline.Proof.closures_lower_ne_closures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.closures_lower_ne_closures

/-- info: 'IxCC.Anf.Pipeline.Proof.closures_of_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Pipeline.Proof.closures_of_lower

/-- info: 'IxCC.Fir.Proof.fo_of_countExp' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.fo_of_countExp

/-- info: 'IxCC.Fir.Proof.fo_of_countBind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.fo_of_countBind

/-- info: 'IxCC.Fir.Proof.fo_of_countAlts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.fo_of_countAlts

/-- info: 'IxCC.Fir.Proof.fo_of_countOpt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.fo_of_countOpt

/-- info: 'IxCC.Fir.Proof.foldl_isEmpty_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.foldl_isEmpty_inv

/-- info: 'IxCC.Fir.Proof.firstOrder_of_residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.firstOrder_of_residual

/-- info: 'IxCC.Fir.Proof.lower_ok_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.lower_ok_firstOrder

/-- info: 'IxCC.Recheck.declaredCounts_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.declaredCounts_get

/-- info: 'IxCC.Recheck.declaredCounts_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.declaredCounts_exact

/-- info: 'IxCC.Recheck.closuresOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.closuresOf_ok

/-- info: 'IxCC.Recheck.anfOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.anfOf_ok

/-- info: 'IxCC.Recheck.anfOf_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.anfOf_refines

/-- info: 'IxCC.Recheck.anfOf_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.anfOf_firstOrder

/-- info: 'IxCC.Recheck.anfOf_lower_ne_closures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.anfOf_lower_ne_closures

/-- info: 'IxCC.Recheck.anfOf_of_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.anfOf_of_lower

/-- info: 'IxCC.Recheck.covered_of_unchanged' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Recheck.covered_of_unchanged

/-- info: 'IxCC.Recheck.sound_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.sound_unchanged

/-- info: 'IxCC.Recheck.anfOf_known' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.anfOf_known

/-- info: 'IxCC.Recheck.anfOf_ctors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.anfOf_ctors

/-- info: 'IxCC.Recheck.ofKey_append_src' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.ofKey_append_src

/-- info: 'IxCC.Recheck.covered_rootsOf_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.covered_rootsOf_head

/-- info: 'IxCC.Recheck.Artifact.covered_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.Artifact.covered_head

/-- info: 'IxCC.Recheck.RcReplay.Artifact.covered_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.RcReplay.Artifact.covered_head
