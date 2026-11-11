import IxCC.Anf.Proof.Defun.FirstOrder
import IxCC.Anf.Proof.Defun.Rel
import IxCC.Fir.Proof.FirstOrder
import IxCC.Anf.Proof.Defun.Scope
import IxCC.Anf.Proof.Defun.Dispatch
import IxCC.Recheck.RootArity
import IxCC.Anf.Proof.Defun.Keys

/-! Required axiom fences for P8 (closed-world defunctionalisation, not yet in
the pipeline): its output is first order (`Anf.Defun.Proof.run_firstOrder`),
`Fir.lower` declines no first-order program for closures
(`Fir.Proof.lower_firstOrder`), and the value relation is the identity on
first-order values and keeps observations (`Anf.Defun.Proof.Rel`), the
dispatchers compute `applyN` (`Anf.Defun.Proof.Dispatch`), P8 keeps the roots
and their arities, and the root-arity guard pins a compiled root to its
declared count (`Recheck.RootArity`). The headline theorems come first, then
every other public theorem of these modules. -/

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
