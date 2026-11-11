import IxCC.Anf.Proof.Defun.FirstOrder
import IxCC.Anf.Proof.Defun.Rel
import IxCC.Fir.Proof.FirstOrder
import IxCC.Anf.Proof.Defun.Scope
import IxCC.Anf.Proof.Defun.Dispatch
import IxCC.Recheck.RootArity
import IxCC.Anf.Proof.Defun.Keys
import IxCC.Anf.Proof.Defun.Assemble
import IxCC.Anf.Proof.Defun.Rename
import IxCC.Anf.Proof.Defun.Translate
import IxCC.Anf.Proof.Defun.WellScoped
import IxCC.Anf.Proof.Defun.Fund
import IxCC.Anf.Proof.Defun.Correct

/-! Required axiom fences for P8 (closed-world defunctionalisation; on the
recheck path through the closures step, whose fences are `Fences.Closures`): its output is first order (`Anf.Defun.Proof.run_firstOrder`),
`Fir.lower` declines no first-order program for closures
(`Fir.Proof.lower_firstOrder`), and the value relation is the identity on
first-order values and keeps observations (`Anf.Defun.Proof.Rel`), the
dispatchers compute `applyN` (`Anf.Defun.Proof.Dispatch`), P8 keeps the roots
and their arities, and the root-arity guard pins a compiled root to its
declared count (`Recheck.RootArity`); the closure sources' keys are distinct
and the dispatcher lemmas hold of P8's own output, the walk is the
translation, the output is well scoped when the input is, and renaming is
exact on code without local functions; the fundamental lemma of the
translation holds at every clock bound, with the dispatcher and call
simulations; and P8 is correct (`Anf.Defun.correct`, its step form and its
composition with `Fir.lower`) (the last three sections). The headline
theorems come first, then every other public theorem of these modules. -/

/-- info: 'IxCC.Anf.Defun.Proof.run_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_firstOrder

/-- info: 'IxCC.Anf.Defun.Proof.defun_firstOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.defun_firstOrder

/-- info: 'IxCC.Fir.Proof.lower_firstOrder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.lower_firstOrder

/-- info: 'IxCC.Fir.Proof.lower_ne_closures' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.lower_ne_closures

/-- info: 'IxCC.Anf.Defun.Proof.dv_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dv_eq

/-- info: 'IxCC.Anf.Defun.Proof.dv_refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dv_refl

/-- info: 'IxCC.Anf.Defun.Proof.dv_obs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dv_obs

/-! The other theorems of `Anf.Defun.Proof.FirstOrder`, `Anf.Defun.Proof.Rel` and `Fir.Proof.FirstOrder`. -/

/-- info: 'IxCC.Anf.Defun.Proof.bind_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.bind_ok

/-- info: 'IxCC.Anf.Defun.Proof.pure_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.pure_ok

/-- info: 'IxCC.Anf.Defun.Proof.throw_ok' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.throw_ok

/-- info: 'IxCC.Anf.Defun.Proof.foldl_insert_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.foldl_insert_mem

/-- info: 'IxCC.Anf.Defun.Proof.ofList_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ofList_mem

/-- info: 'IxCC.Anf.Defun.Proof.mem_globalList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.mem_globalList

/-- info: 'IxCC.Anf.Defun.Proof.mem_numbered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.mem_numbered

/-- info: 'IxCC.Anf.Defun.Proof.renameVars_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameVars_fo

/-- info: 'IxCC.Anf.Defun.Proof.renameBind_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameBind_fo

/-- info: 'IxCC.Anf.Defun.Proof.renameAlts_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameAlts_fo

/-- info: 'IxCC.Anf.Defun.Proof.renameOpt_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameOpt_fo

/-- info: 'IxCC.Anf.Defun.Proof.exp_fo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.exp_fo

/-- info: 'IxCC.Anf.Defun.Proof.bind_fo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.bind_fo

/-- info: 'IxCC.Anf.Defun.Proof.alts_fo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.alts_fo

/-- info: 'IxCC.Anf.Defun.Proof.opt_fo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.opt_fo

/-- info: 'IxCC.Anf.Defun.Proof.global_fo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.global_fo

/-- info: 'IxCC.Anf.Defun.Proof.global_ps' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.global_ps

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_ps' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_ps

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_fo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_fo

/-- info: 'IxCC.Anf.Defun.Proof.altBody_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.altBody_fo

/-- info: 'IxCC.Anf.Defun.Proof.altsFirstOrder_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.altsFirstOrder_append

/-- info: 'IxCC.Anf.Defun.Proof.keyAlts_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.keyAlts_fo

/-- info: 'IxCC.Anf.Defun.Proof.dispAlts_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dispAlts_fo

/-- info: 'IxCC.Anf.Defun.Proof.dispatcher_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dispatcher_fo

/-- info: 'IxCC.Anf.Defun.Proof.run_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_ok

/-- info: 'IxCC.Anf.Defun.Proof.assemble_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_mem

/-- info: 'IxCC.Anf.Defun.Proof.keeps_assemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.keeps_assemble

/-- info: 'IxCC.Anf.Defun.Proof.dvs_refl' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dvs_refl

/-- info: 'IxCC.Anf.Defun.Proof.dvs_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dvs_eq

/-- info: 'IxCC.Anf.Defun.Proof.dvs_obs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dvs_obs

/-- info: 'IxCC.Fir.Proof.noClo_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.noClo_ok

/-- info: 'IxCC.Fir.Proof.noClo_pure' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.noClo_pure

/-- info: 'IxCC.Fir.Proof.noClo_error' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.noClo_error

/-- info: 'IxCC.Fir.Proof.noClo_throw' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.noClo_throw

/-- info: 'IxCC.Fir.Proof.noClo_bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.noClo_bind

/-- info: 'IxCC.Fir.Proof.noClo_atom' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.noClo_atom

/-- info: 'IxCC.Fir.Proof.noClo_atoms' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.noClo_atoms

/-- info: 'IxCC.Fir.Proof.noClo_atomVar' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.noClo_atomVar

/-- info: 'IxCC.Fir.Proof.exp_noClo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.exp_noClo

/-- info: 'IxCC.Fir.Proof.exps_noClo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.exps_noClo

/-- info: 'IxCC.Fir.Proof.opt_noClo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.opt_noClo

/-- info: 'IxCC.Fir.Proof.mem_globalList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.mem_globalList

/-- info: 'IxCC.Fir.Proof.functions_noClo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.functions_noClo

/-- info: 'IxCC.Fir.Proof.countExp_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.countExp_fo

/-- info: 'IxCC.Fir.Proof.countBind_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.countBind_fo

/-- info: 'IxCC.Fir.Proof.countAlts_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.countAlts_fo

/-- info: 'IxCC.Fir.Proof.countOpt_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.countOpt_fo

/-- info: 'IxCC.Fir.Proof.foldl_empty' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Fir.Proof.foldl_empty

/-- info: 'IxCC.Fir.Proof.fo_globals' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.fo_globals

/-- info: 'IxCC.Fir.Proof.foldl_isEmpty' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.foldl_isEmpty

/-- info: 'IxCC.Fir.Proof.residual_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Fir.Proof.residual_empty

/-! λ-lifting keeps scope (`Anf.Defun.Proof.Scope`). -/

/-- info: 'IxCC.Anf.Defun.Proof.lifted_ws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.lifted_ws

/-- info: 'IxCC.Anf.Defun.Proof.atom_free_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.atom_free_shift

/-- info: 'IxCC.Anf.Defun.Proof.atoms_free_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.atoms_free_shift

/-- info: 'IxCC.Anf.Defun.Proof.free_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.free_shift

/-- info: 'IxCC.Anf.Defun.Proof.bindFree_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.bindFree_shift

/-- info: 'IxCC.Anf.Defun.Proof.altsFree_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.altsFree_shift

/-- info: 'IxCC.Anf.Defun.Proof.optFree_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.optFree_shift

/-- info: 'IxCC.Anf.Defun.Proof.atom_rename_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.atom_rename_ws

/-- info: 'IxCC.Anf.Defun.Proof.atoms_rename_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.atoms_rename_ws

/-- info: 'IxCC.Anf.Defun.Proof.renameList_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameList_length

/-- info: 'IxCC.Anf.Defun.Proof.renameAlts_keys' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameAlts_keys

/-- info: 'IxCC.Anf.Defun.Proof.renameVars_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameVars_ws

/-- info: 'IxCC.Anf.Defun.Proof.renameBind_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameBind_ws

/-- info: 'IxCC.Anf.Defun.Proof.renameAlts_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameAlts_ws

/-- info: 'IxCC.Anf.Defun.Proof.renameOpt_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.renameOpt_ws

/-- info: 'IxCC.Anf.Defun.Proof.foldl_insert_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.foldl_insert_isSome

/-- info: 'IxCC.Anf.Defun.Proof.captures_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.captures_mem

/-- info: 'IxCC.Anf.Defun.Proof.capMap_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.capMap_lt

/-! The dispatchers (`Anf.Defun.Proof.Dispatch`), the roots and their arities (`Anf.Defun.Proof.FirstOrder`, `Recheck.RootArity`) and `RefinesOn` (`Anf.Defun.Proof.Rel`). -/

/-- info: 'IxCC.Recheck.checkRootArities_ok' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Recheck.checkRootArities_ok

/-- info: 'IxCC.Recheck.rootAritiesOk_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.rootAritiesOk_spec

/-- info: 'IxCC.Recheck.rootAritiesOk_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.rootAritiesOk_length

/-- info: 'IxCC.Recheck.exactDeclared_cfg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Recheck.exactDeclared_cfg

/-- info: 'IxCC.Anf.Defun.Proof.refinesOn_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.refinesOn_mono

/-- info: 'IxCC.Anf.Defun.Proof.run_roots' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_roots

/-- info: 'IxCC.Anf.Defun.Proof.run_arity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_arity

/-- info: 'IxCC.Anf.Defun.Proof.evalAtoms_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAtoms_append

/-- info: 'IxCC.Anf.Defun.Proof.downFrom_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.downFrom_succ

/-- info: 'IxCC.Anf.Defun.Proof.evalAtoms_downFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAtoms_downFrom

/-- info: 'IxCC.Anf.Defun.Proof.evalAtoms_downFrom_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAtoms_downFrom_nil

/-- info: 'IxCC.Anf.Defun.Proof.downFrom_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.downFrom_take

/-- info: 'IxCC.Anf.Defun.Proof.downFrom_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.downFrom_drop

/-- info: 'IxCC.Anf.Defun.Proof.downFrom_map_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.downFrom_map_shift

/-- info: 'IxCC.Anf.Defun.Proof.eval_bind_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eval_bind_ret

/-- info: 'IxCC.Anf.Defun.Proof.evalAlts_skip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAlts_skip

/-- info: 'IxCC.Anf.Defun.Proof.evalAlts_keyAlts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAlts_keyAlts

/-- info: 'IxCC.Anf.Defun.Proof.evalAlts_dispAlts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAlts_dispAlts

/-- info: 'IxCC.Anf.Defun.Proof.eval_dispatcher' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eval_dispatcher

/-- info: 'IxCC.Anf.Defun.Proof.evalAtoms_alt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAtoms_alt

/-- info: 'IxCC.Anf.Defun.Proof.eval_altBody_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eval_altBody_exact

/-- info: 'IxCC.Anf.Defun.Proof.eval_altBody_under' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eval_altBody_under

/-- info: 'IxCC.Anf.Defun.Proof.eval_altBody_over' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eval_altBody_over

/-- info: 'IxCC.Anf.Defun.Proof.call_dispatcher' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.call_dispatcher

/-- info: 'IxCC.Anf.Defun.Proof.dispatch_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dispatch_exact

/-- info: 'IxCC.Anf.Defun.Proof.dispatch_under' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dispatch_under

/-- info: 'IxCC.Anf.Defun.Proof.dispatch_over' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dispatch_over

/-! P8's key check is sound (`Anf.Defun.Proof.Keys`). -/

/-- info: 'IxCC.Anf.Defun.Proof.firstEqualKeys_none_go' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.firstEqualKeys_none_go

/-- info: 'IxCC.Anf.Defun.Proof.firstEqualKeys_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.firstEqualKeys_none

/-- info: 'IxCC.Anf.Defun.Proof.checkSources_ownerKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.checkSources_ownerKeys

/-! The closure sources' distinct keys and the linear key check (`Anf.Defun.Proof.Keys`), the assembled
program and the dispatcher lemmas on P8's output (`Assemble`), renaming (`Rename`), the walk as the
translation (`Translate`) and the output's scoping (`WellScoped`): the headline theorems, then every
other public theorem of these modules. -/

/-- info: 'IxCC.Anf.Defun.Proof.sources_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.sources_keys

/-- info: 'IxCC.Anf.Defun.Proof.firstEqualKeysT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.firstEqualKeysT_eq

/-- info: 'IxCC.Anf.Defun.Proof.run_dispatch_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_dispatch_exact

/-- info: 'IxCC.Anf.Defun.Proof.run_dispatch_under' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_dispatch_under

/-- info: 'IxCC.Anf.Defun.Proof.run_dispatch_over' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_dispatch_over

/-- info: 'IxCC.Anf.Defun.Proof.run_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_valid

/-- info: 'IxCC.Anf.Defun.Proof.ran_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ran_valid

/-- info: 'IxCC.Anf.Defun.Proof.wellScoped_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.wellScoped_run

/-- info: 'IxCC.Anf.Defun.Proof.wellScoped_ran' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.wellScoped_ran

/-- info: 'IxCC.Anf.Defun.Proof.eval_rename' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eval_rename

/-- info: 'IxCC.Anf.Defun.Proof.capRen_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.capRen_env

/-- info: 'IxCC.Anf.Defun.Proof.keyTrie_find_empty' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.keyTrie_find_empty

/-- info: 'IxCC.Anf.Defun.Proof.keyTrie_find_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.keyTrie_find_add

/-- info: 'IxCC.Anf.Defun.Proof.sameFirst_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.sameFirst_add

/-- info: 'IxCC.Anf.Defun.Proof.firstEqualKeysT_go' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.firstEqualKeysT_go

/-- info: 'IxCC.Anf.Defun.Proof.nodup_map_of_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.nodup_map_of_inj

/-- info: 'IxCC.Anf.Defun.Proof.eq_of_nodup_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eq_of_nodup_map

/-- info: 'IxCC.Anf.Defun.Proof.filterMap_sublist' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.filterMap_sublist

/-- info: 'IxCC.Anf.Defun.Proof.mem_ite_cons' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.mem_ite_cons

/-- info: 'IxCC.Anf.Defun.Proof.natSet_contains_ofList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.natSet_contains_ofList

/-- info: 'IxCC.Anf.Defun.Proof.natSet_contains_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.natSet_contains_insert

/-- info: 'IxCC.Anf.Defun.Proof.globalList_ids_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalList_ids_nodup

/-- info: 'IxCC.Anf.Defun.Proof.lamKeys_add' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.lamKeys_add

/-- info: 'IxCC.Anf.Defun.Proof.mem_lamKeys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.mem_lamKeys

/-- info: 'IxCC.Anf.Defun.Proof.lamKeys_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.lamKeys_nodup

/-- info: 'IxCC.Anf.Defun.Proof.Grows.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.Grows.refl

/-- info: 'IxCC.Anf.Defun.Proof.Grows.trans' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.Grows.trans

/-- info: 'IxCC.Anf.Defun.Proof.exp_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.exp_grows

/-- info: 'IxCC.Anf.Defun.Proof.bind_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.bind_grows

/-- info: 'IxCC.Anf.Defun.Proof.alts_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.alts_grows

/-- info: 'IxCC.Anf.Defun.Proof.opt_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.opt_grows

/-- info: 'IxCC.Anf.Defun.Proof.global_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.global_grows

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_parents' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_parents

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_keys

/-- info: 'IxCC.Anf.Defun.Proof.run_ran' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_ran

/-- info: 'IxCC.Anf.Defun.Proof.checkInput_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.checkInput_ok

/-- info: 'IxCC.Anf.Defun.Proof.ran_parents' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ran_parents

/-- info: 'IxCC.Anf.Defun.Proof.mem_ownerKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.mem_ownerKeys

/-- info: 'IxCC.Anf.Defun.Proof.ran_keysApart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ran_keysApart

/-- info: 'IxCC.Anf.Defun.Proof.ran_lifted_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ran_lifted_keys

/-- info: 'IxCC.Anf.Defun.Proof.escape_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.escape_sublist

/-- info: 'IxCC.Anf.Defun.Proof.numbered_map_key' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.numbered_map_key

/-- info: 'IxCC.Anf.Defun.Proof.sources_keys_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.sources_keys_eq

/-- info: 'IxCC.Anf.Defun.Proof.AccLe.refl' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.AccLe.refl

/-- info: 'IxCC.Anf.Defun.Proof.AccLe.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.AccLe.trans

/-- info: 'IxCC.Anf.Defun.Proof.Grows.le' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.Grows.le

/-- info: 'IxCC.Anf.Defun.Proof.global_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.global_le

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_out' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_out

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_le

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_mem

/-- info: 'IxCC.Anf.Defun.Proof.map_fst_eq' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.map_fst_eq

/-- info: 'IxCC.Anf.Defun.Proof.numbered_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.numbered_nodup

/-- info: 'IxCC.Anf.Defun.Proof.assemble_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_get

/-- info: 'IxCC.Anf.Defun.Proof.assemble_old' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_old

/-- info: 'IxCC.Anf.Defun.Proof.assemble_disp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_disp

/-- info: 'IxCC.Anf.Defun.Proof.assemble_lifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_lifted

/-- info: 'IxCC.Anf.Defun.Proof.assemble_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_absent

/-- info: 'IxCC.Anf.Defun.Proof.sources_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.sources_global

/-- info: 'IxCC.Anf.Defun.Proof.split_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.split_nodup

/-- info: 'IxCC.Anf.Defun.Proof.ren_zero_base' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ren_zero_base

/-- info: 'IxCC.Anf.Defun.Proof.ren_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ren_lt

/-- info: 'IxCC.Anf.Defun.Proof.ren_ge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ren_ge

/-- info: 'IxCC.Anf.Defun.Proof.ren_push' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ren_push

/-- info: 'IxCC.Anf.Defun.Proof.atom_rename_eval' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.atom_rename_eval

/-- info: 'IxCC.Anf.Defun.Proof.atoms_rename_eval' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.atoms_rename_eval

/-- info: 'IxCC.Anf.Defun.Proof.JRen.get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.JRen.get

/-- info: 'IxCC.Anf.Defun.Proof.later_congr' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.later_congr

/-- info: 'IxCC.Anf.Defun.Proof.ren_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ren_bind

/-- info: 'IxCC.Anf.Defun.Proof.ren_exp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ren_exp

/-- info: 'IxCC.Anf.Defun.Proof.ren_opt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ren_opt

/-- info: 'IxCC.Anf.Defun.Proof.ren_alts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.ren_alts

/-- info: 'IxCC.Anf.Defun.Proof.captures_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.captures_lt

/-- info: 'IxCC.Anf.Defun.Proof.captures_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.captures_nodup

/-- info: 'IxCC.Anf.Defun.Proof.capMap_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.capMap_get

/-- info: 'IxCC.Anf.Defun.Proof.natSet_contains_insert_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.natSet_contains_insert_self

/-- info: 'IxCC.Anf.Defun.Proof.wsList_vars' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.wsList_vars

/-- info: 'IxCC.Anf.Defun.Proof.projOk_mono' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.projOk_mono

/-- info: 'IxCC.Anf.Defun.Proof.trAlts_keys' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.trAlts_keys

/-- info: 'IxCC.Anf.Defun.Proof.tr_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.tr_ws

/-- info: 'IxCC.Anf.Defun.Proof.trB_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.trB_ws

/-- info: 'IxCC.Anf.Defun.Proof.trAlts_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.trAlts_ws

/-- info: 'IxCC.Anf.Defun.Proof.trOpt_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.trOpt_ws

/-- info: 'IxCC.Anf.Defun.Proof.exp_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.exp_tr

/-- info: 'IxCC.Anf.Defun.Proof.bind_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.bind_tr

/-- info: 'IxCC.Anf.Defun.Proof.alts_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.alts_tr

/-- info: 'IxCC.Anf.Defun.Proof.opt_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.opt_tr

/-- info: 'IxCC.Anf.Defun.Proof.global_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.global_tr

/-- info: 'IxCC.Anf.Defun.Proof.mem_numbered_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.mem_numbered_of

/-- info: 'IxCC.Anf.Defun.Proof.final_ran' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.final_ran

/-- info: 'IxCC.Anf.Defun.Proof.find?_of_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.find?_of_nodup

/-- info: 'IxCC.Anf.Defun.Proof.rows_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.rows_mem

/-- info: 'IxCC.Anf.Defun.Proof.mem_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.mem_rows

/-- info: 'IxCC.Anf.Defun.Proof.rows_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.rows_nodup

/-- info: 'IxCC.Anf.Defun.Proof.assemble_ctor?' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_ctor?

/-- info: 'IxCC.Anf.Defun.Proof.assemble_ctorArity_src' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_ctorArity_src

/-- info: 'IxCC.Anf.Defun.Proof.sigOk_ran' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.sigOk_ran

/-- info: 'IxCC.Anf.Defun.Proof.wsList_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.wsList_append

/-- info: 'IxCC.Anf.Defun.Proof.wsList_downFrom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.wsList_downFrom

/-- info: 'IxCC.Anf.Defun.Proof.downFrom_length' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.downFrom_length

/-- info: 'IxCC.Anf.Defun.Proof.altsWS_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.altsWS_append

/-- info: 'IxCC.Anf.Defun.Proof.altKeys_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.altKeys_append

/-- info: 'IxCC.Anf.Defun.Proof.altKeys_dispAlts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.altKeys_dispAlts

/-- info: 'IxCC.Anf.Defun.Proof.altBody_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.altBody_ws

/-- info: 'IxCC.Anf.Defun.Proof.keyAlts_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.keyAlts_ws

/-- info: 'IxCC.Anf.Defun.Proof.dispAlts_ws' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dispAlts_ws

/-- info: 'IxCC.Anf.Defun.Proof.dispatcher_ws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dispatcher_ws

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_lws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_lws

/-- info: 'IxCC.Anf.Defun.Proof.globalsGo_key' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globalsGo_key

/-- info: 'IxCC.Anf.Defun.Proof.numbered_map_snd' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.numbered_map_snd

/-- info: 'IxCC.Anf.Defun.Proof.numbered_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.numbered_get

/-- info: 'IxCC.Anf.Defun.Proof.assemble_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.assemble_cases

/-- info: 'IxCC.Anf.Defun.Proof.nodup_map_of_fst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.nodup_map_of_fst

/-! The fundamental lemma of the translation (`Anf.Defun.Proof.Fund`): the headline theorems, then every
other public theorem of the module. -/

/-- info: 'IxCC.Anf.Defun.Proof.fund' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.fund

/-- info: 'IxCC.Anf.Defun.Proof.dispatch_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dispatch_sim

/-- info: 'IxCC.Anf.Defun.Proof.call_sim' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.call_sim

/-- info: 'IxCC.Anf.Defun.Proof.clo_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.clo_step

/-- info: 'IxCC.Anf.Defun.Proof.pw_of_dvs' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.pw_of_dvs

/-- info: 'IxCC.Anf.Defun.Proof.dvs_of_pw' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dvs_of_pw

/-- info: 'IxCC.Anf.Defun.Proof.dv_atom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dv_atom

/-- info: 'IxCC.Anf.Defun.Proof.dv_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.dv_atoms

/-- info: 'IxCC.Anf.Defun.Proof.natArgs_dv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.natArgs_dv

/-- info: 'IxCC.Anf.Defun.Proof.prim_dv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.prim_dv

/-- info: 'IxCC.Anf.Defun.Proof.proj_dv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.proj_dv

/-- info: 'IxCC.Anf.Defun.Proof.asCtor_dv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.asCtor_dv

/-- info: 'IxCC.Anf.Defun.Proof.tr_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.tr_fo

/-- info: 'IxCC.Anf.Defun.Proof.trB_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.trB_fo

/-- info: 'IxCC.Anf.Defun.Proof.trAlts_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.trAlts_fo

/-- info: 'IxCC.Anf.Defun.Proof.trOpt_fo' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.trOpt_fo

/-- info: 'IxCC.Anf.Defun.Proof.JRel.get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.JRel.get

/-- info: 'IxCC.Anf.Defun.Proof.later_bind' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.later_bind

/-- info: 'IxCC.Anf.Defun.Proof.bind_ok_right' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.bind_ok_right

/-- info: 'IxCC.Anf.Defun.Proof.clockMono_shift' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.clockMono_shift

/-- info: 'IxCC.Anf.Defun.Proof.callVal_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.callVal_mono

/-- info: 'IxCC.Anf.Defun.Proof.simUpTo_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.simUpTo_shift

/-- info: 'IxCC.Anf.Defun.Proof.callVal_dispatcher' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.callVal_dispatcher

/-- info: 'IxCC.Anf.Defun.Proof.eval_altBody_exact_later' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eval_altBody_exact_later

/-- info: 'IxCC.Anf.Defun.Proof.evalAtoms_alt_take' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAtoms_alt_take

/-- info: 'IxCC.Anf.Defun.Proof.evalAtoms_alt_drop' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAtoms_alt_drop

/-- info: 'IxCC.Anf.Defun.Proof.eval_altBody_over_later' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.eval_altBody_over_later

/-- info: 'IxCC.Anf.Defun.Proof.evalAtoms_vars' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.evalAtoms_vars

/-- info: 'IxCC.Anf.Defun.Proof.fund_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.fund_bind

/-- info: 'IxCC.Anf.Defun.Proof.fund_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.fund_exp

/-- info: 'IxCC.Anf.Defun.Proof.fund_opt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.fund_opt

/-- info: 'IxCC.Anf.Defun.Proof.fund_alts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.fund_alts

/-! P8 is correct (`Anf.Defun.Proof.Correct`): the headline theorems, then every other public theorem of
the module. -/

/-- info: 'IxCC.Anf.Defun.Proof.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.correct

/-- info: 'IxCC.Anf.Defun.Proof.run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_refines

/-- info: 'IxCC.Anf.Defun.Proof.step_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.step_correct

/-- info: 'IxCC.Anf.Defun.Proof.defun_lower_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.defun_lower_refines

/-- info: 'IxCC.Anf.Defun.Proof.defun_lower_ne_closures' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.defun_lower_ne_closures

/-- info: 'IxCC.Anf.Defun.Proof.run_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.run_wf

/-- info: 'IxCC.Anf.Defun.Proof.lits_dv' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.lits_dv

/-- info: 'IxCC.Anf.Defun.Proof.globVal_fn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globVal_fn

/-- info: 'IxCC.Anf.Defun.Proof.globVal_caf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.globVal_caf

/-- info: 'IxCC.Anf.Defun.Proof.applyN_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.applyN_exact

/-- info: 'IxCC.Anf.Defun.Proof.root_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.root_sim

/-- info: 'IxCC.Anf.Defun.Proof.defun_run' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.defun_run

/-- info: 'IxCC.Anf.Defun.Proof.mem_numbered_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.mem_numbered_lt

/-- info: 'IxCC.Anf.Defun.Proof.exactArity_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.exactArity_run

/-- info: 'IxCC.Anf.Defun.Proof.exactArity_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Anf.Defun.Proof.exactArity_of_run
