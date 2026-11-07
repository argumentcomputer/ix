import IxCC.Own.Plain.Check
import IxCC.Own.Plain.Proof.Actions
import IxCC.Own.Plain.Proof.Admission
import IxCC.Own.Plain.Proof.Bindings
import IxCC.Own.Plain.Proof.Bounds
import IxCC.Own.Plain.Proof.Call
import IxCC.Own.Plain.Proof.CallBind
import IxCC.Own.Plain.Proof.Candidate
import IxCC.Own.Plain.Proof.CaptureIdentity
import IxCC.Own.Plain.Proof.CaptureRoots
import IxCC.Own.Plain.Proof.Captures
import IxCC.Own.Plain.Proof.Checked
import IxCC.Own.Plain.Proof.CheckedShape
import IxCC.Own.Plain.Proof.CtorStep
import IxCC.Own.Plain.Proof.Drops
import IxCC.Own.Plain.Proof.Environment
import IxCC.Own.Plain.Proof.EvalShape
import IxCC.Own.Plain.Proof.Frames
import IxCC.Own.Plain.Proof.JoinLookup
import IxCC.Own.Plain.Proof.Jump
import IxCC.Own.Plain.Proof.JumpState
import IxCC.Own.Plain.Proof.Mono
import IxCC.Own.Plain.Proof.NonCall
import IxCC.Own.Plain.Proof.Prefixes
import IxCC.Own.Plain.Proof.Program
import IxCC.Own.Plain.Proof.Projection
import IxCC.Own.Plain.Proof.ResultCompose
import IxCC.Own.Plain.Proof.Results
import IxCC.Own.Plain.Proof.RhsShape
import IxCC.Own.Plain.Proof.RhsSteps
import IxCC.Own.Plain.Proof.Scalars
import IxCC.Own.Plain.Proof.Scope
import IxCC.Own.Plain.Proof.Selected
import IxCC.Own.Plain.Proof.ShapeOps
import IxCC.Own.Plain.Proof.ShapeResult
import IxCC.Own.Plain.Proof.Simulation
import IxCC.Own.Plain.Proof.StackIdentity
import IxCC.Own.Plain.Proof.StackRetain
import IxCC.Own.Plain.Proof.StackScope
import IxCC.Own.Plain.Proof.State
import IxCC.Own.Plain.Proof.TailCall
import IxCC.Own.Plain.Proof.Terminals
import IxCC.Own.Plain.Proof.Transfers
import IxCC.Own.Plain.Proof.Unfold
import IxCC.Own.Plain.Proof.ValidRoots
import IxCC.Own.Plain.Proof.Values
import IxCC.Own.Plain.Semantics
import IxCC.Own.Plain.Syntax

/-! Exact axiom fences for the checked plain-RC foundation. -/

/-- info: 'IxCC.Own.Plain.action_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.action_shape

/-- info: 'IxCC.Own.Plain.altsEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.altsEq_iff

/-- info: 'IxCC.Own.Plain.arg_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.arg_den

/-- info: 'IxCC.Own.Plain.argsOwned_of_scope' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.argsOwned_of_scope

/-- info: 'IxCC.Own.Plain.args_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.args_den

/-- info: 'IxCC.Own.Plain.argument_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.argument_step

/-- info: 'IxCC.Own.Plain.asCtor_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.asCtor_bounded

/-- info: 'IxCC.Own.Plain.asCtor_field_canDup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.asCtor_field_canDup

/-- info: 'IxCC.Own.Plain.balance_append_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.balance_append_comm

/-- info: 'IxCC.Own.Plain.balance_immediate' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.balance_immediate

/-- info: 'IxCC.Own.Plain.balance_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.balance_resume

/-- info: 'IxCC.Own.Plain.balance_rotate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.balance_rotate

/-- info: 'IxCC.Own.Plain.bodyMapEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.bodyMapEq_iff

/-- info: 'IxCC.Own.Plain.boolPinOk_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.boolPinOk_sound

/-- info: 'IxCC.Own.Plain.callFun_agrees_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.callFun_agrees_of

/-- info: 'IxCC.Own.Plain.call_bind_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.call_bind_refines

/-- info: 'IxCC.Own.Plain.call_heap_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.call_heap_shape

/-- info: 'IxCC.Own.Plain.call_of_smaller_clocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.call_of_smaller_clocks

/-- info: 'IxCC.Own.Plain.call_shape_of_smaller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.call_shape_of_smaller

/-- info: 'IxCC.Own.Plain.canDup_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canDup_member

/-- info: 'IxCC.Own.Plain.canonical_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canonical_body

/-- info: 'IxCC.Own.Plain.canonical_body_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canonical_body_of

/-- info: 'IxCC.Own.Plain.canonical_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canonical_call

/-- info: 'IxCC.Own.Plain.canonical_call_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canonical_call_refines

/-- info: 'IxCC.Own.Plain.canonical_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.canonical_refines

/-- info: 'IxCC.Own.Plain.checkBody_erases' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkBody_erases

/-- info: 'IxCC.Own.Plain.checkBody_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkBody_iff

/-- info: 'IxCC.Own.Plain.checkBoolPins_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkBoolPins_sound

/-- info: 'IxCC.Own.Plain.checkFunction_domain' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkFunction_domain

/-- info: 'IxCC.Own.Plain.checkFunction_parts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkFunction_parts

/-- info: 'IxCC.Own.Plain.checkPlainMap_parts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checkPlainMap_parts

/-- info: 'IxCC.Own.Plain.checked_body_is_canonical' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checked_body_is_canonical

/-- info: 'IxCC.Own.Plain.checked_body_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checked_body_refines

/-- info: 'IxCC.Own.Plain.checked_program_reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checked_program_reclaims

/-- info: 'IxCC.Own.Plain.checked_program_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checked_program_refines

/-- info: 'IxCC.Own.Plain.checked_program_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.checked_program_shape

/-- info: 'IxCC.Own.Plain.codeEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.codeEq_iff

/-- info: 'IxCC.Own.Plain.constructor_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.constructor_step

/-- info: 'IxCC.Own.Plain.copies_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.copies_sound

/-- info: 'IxCC.Own.Plain.den_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.den_bounded

/-- info: 'IxCC.Own.Plain.den_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.den_member

/-- info: 'IxCC.Own.Plain.dens_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.dens_bounded

/-- info: 'IxCC.Own.Plain.dens_preserve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.dens_preserve

/-- info: 'IxCC.Own.Plain.dens_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.dens_transport

/-- info: 'IxCC.Own.Plain.drops_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.drops_sound

/-- info: 'IxCC.Own.Plain.entryDen_declare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.entryDen_declare

/-- info: 'IxCC.Own.Plain.envBounded_empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.envBounded_empty

/-- info: 'IxCC.Own.Plain.envRoots_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.envRoots_cons

/-- info: 'IxCC.Own.Plain.erase_lowerAlts' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.erase_lowerAlts

/-- info: 'IxCC.Own.Plain.erase_lowerCode' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.erase_lowerCode

/-- info: 'IxCC.Own.Plain.erase_lowerOpt' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.erase_lowerOpt

/-- info: 'IxCC.Own.Plain.erase_prefix' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.Plain.erase_prefix

/-- info: 'IxCC.Own.Plain.erase_transfer' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.erase_transfer

/-- info: 'IxCC.Own.Plain.evalAction_dec_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalAction_dec_owned

/-- info: 'IxCC.Own.Plain.evalAction_inc_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalAction_inc_field

/-- info: 'IxCC.Own.Plain.evalAction_inc_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalAction_inc_owned

/-- info: 'IxCC.Own.Plain.evalActions_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalActions_append

/-- info: 'IxCC.Own.Plain.evalAlts_agrees_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalAlts_agrees_of

/-- info: 'IxCC.Own.Plain.evalAlts_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalAlts_cons

/-- info: 'IxCC.Own.Plain.evalAlts_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalAlts_nil

/-- info: 'IxCC.Own.Plain.evalAlts_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalAlts_refines

/-- info: 'IxCC.Own.Plain.evalAlts_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalAlts_shape

/-- info: 'IxCC.Own.Plain.evalArgs_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalArgs_append

/-- info: 'IxCC.Own.Plain.evalCall_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalCall_agrees

/-- info: 'IxCC.Own.Plain.evalCall_agrees_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalCall_agrees_of

/-- info: 'IxCC.Own.Plain.evalCall_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalCall_eq

/-- info: 'IxCC.Own.Plain.evalCall_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalCall_of

/-- info: 'IxCC.Own.Plain.evalRhs_alloc_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalRhs_alloc_owned

/-- info: 'IxCC.Own.Plain.evalVars_congr' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.evalVars_congr

/-- info: 'IxCC.Own.Plain.eval_act' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_act

/-- info: 'IxCC.Own.Plain.eval_actionPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_actionPrefix

/-- info: 'IxCC.Own.Plain.eval_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_agrees

/-- info: 'IxCC.Own.Plain.eval_agrees_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_agrees_of

/-- info: 'IxCC.Own.Plain.eval_bindCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_bindCall

/-- info: 'IxCC.Own.Plain.eval_bindRhs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_bindRhs

/-- info: 'IxCC.Own.Plain.eval_case' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_case

/-- info: 'IxCC.Own.Plain.eval_heap_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_heap_shape

/-- info: 'IxCC.Own.Plain.eval_jmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_jmp

/-- info: 'IxCC.Own.Plain.eval_jp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_jp

/-- info: 'IxCC.Own.Plain.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_mono

/-- info: 'IxCC.Own.Plain.eval_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_refines

/-- info: 'IxCC.Own.Plain.eval_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_ret

/-- info: 'IxCC.Own.Plain.eval_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_shape

/-- info: 'IxCC.Own.Plain.eval_tcall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_tcall

/-- info: 'IxCC.Own.Plain.eval_trap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.eval_trap

/-- info: 'IxCC.Own.Plain.fir_primitive_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.fir_primitive_pure

/-- info: 'IxCC.Own.Plain.fir_rhs_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.fir_rhs_pure

/-- info: 'IxCC.Own.Plain.fresh_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.fresh_avoids

/-- info: 'IxCC.Own.Plain.fresh_nodup_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.fresh_nodup_append

/-- info: 'IxCC.Own.Plain.get_bindAll_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.get_bindAll_untouched

/-- info: 'IxCC.Own.Plain.jump_measure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.jump_measure

/-- info: 'IxCC.Own.Plain.jump_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.jump_progress

/-- info: 'IxCC.Own.Plain.jump_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.jump_state

/-- info: 'IxCC.Own.Plain.lookupJ_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.lookupJ_weight

/-- info: 'IxCC.Own.Plain.lookup_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.lookup_ready

/-- info: 'IxCC.Own.Plain.nonCall_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.nonCall_refines

/-- info: 'IxCC.Own.Plain.nonCall_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.nonCall_step

/-- info: 'IxCC.Own.Plain.ofOption_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ofOption_pure

/-- info: 'IxCC.Own.Plain.optEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.optEq_iff

/-- info: 'IxCC.Own.Plain.primResult_immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.primResult_immediate

/-- info: 'IxCC.Own.Plain.prim_bounded' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.prim_bounded

/-- info: 'IxCC.Own.Plain.primitive_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.primitive_owned

/-- info: 'IxCC.Own.Plain.primitive_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.primitive_step

/-- info: 'IxCC.Own.Plain.programDomain_function' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.programDomain_function

/-- info: 'IxCC.Own.Plain.projection_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.projection_owned

/-- info: 'IxCC.Own.Plain.projection_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.projection_step

/-- info: 'IxCC.Own.Plain.retained_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.retained_empty

/-- info: 'IxCC.Own.Plain.retained_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.retained_eq

/-- info: 'IxCC.Own.Plain.return_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.return_refines

/-- info: 'IxCC.Own.Plain.rhs_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.rhs_shape

/-- info: 'IxCC.Own.Plain.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.run_mono

/-- info: 'IxCC.Own.Plain.shape_bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.shape_bind

/-- info: 'IxCC.Own.Plain.shape_later' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.shape_later

/-- info: 'IxCC.Own.Plain.shape_ofOption' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.shape_ofOption

/-- info: 'IxCC.Own.Plain.signatures_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.signatures_lookup

/-- info: 'IxCC.Own.Plain.stackArities_after' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.stackArities_after

/-- info: 'IxCC.Own.Plain.state_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.state_empty

/-- info: 'IxCC.Own.Plain.state_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.state_entry

/-- info: 'IxCC.Own.Plain.tailCall_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.tailCall_transfer

/-- info: 'IxCC.Own.Plain.transfer_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.transfer_sound

/-- info: 'IxCC.Own.Plain.trap_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.trap_refines

/-- info: 'IxCC.Own.Rc.changeCount_heapOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.changeCount_heapOk

/-- info: 'IxCC.Own.Rc.dropAll_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Rc.dropAll_shape

/-- info: 'IxCC.Own.Rc.releaseOne_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Rc.releaseOne_size

/-- info: 'IxCC.Own.Plain.Agrees.later' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Agrees.later

/-- info: 'IxCC.Own.Plain.Agrees.ofOption' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.Plain.Agrees.ofOption

/-- info: 'IxCC.Own.Plain.Bounded.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Bounded.mono

/-- info: 'IxCC.Own.Plain.CaptureView.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.CaptureView.bind

/-- info: 'IxCC.Own.Plain.CaptureView.captured_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.Plain.CaptureView.captured_nodup

/-- info: 'IxCC.Own.Plain.CaptureView.declare' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.Plain.CaptureView.declare

/-- info: 'IxCC.Own.Plain.CaptureView.rebind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.CaptureView.rebind

/-- info: 'IxCC.Own.Plain.CaptureView.retained_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.CaptureView.retained_roots

/-- info: 'IxCC.Own.Plain.CaptureView.roots' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.CaptureView.roots

/-- info: 'IxCC.Own.Plain.CaptureView.trans' does not depend on any axioms -/
#guard_msgs in #print axioms IxCC.Own.Plain.CaptureView.trans

/-- info: 'IxCC.Own.Plain.Code.size_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Code.size_pos

/-- info: 'IxCC.Own.Plain.EntryDen.charge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EntryDen.charge

/-- info: 'IxCC.Own.Plain.EntryDen.reframe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EntryDen.reframe

/-- info: 'IxCC.Own.Plain.EntryDen.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EntryDen.transport

/-- info: 'IxCC.Own.Plain.EnvBounded.arg' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvBounded.arg

/-- info: 'IxCC.Own.Plain.EnvBounded.args' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvBounded.args

/-- info: 'IxCC.Own.Plain.EnvBounded.bindAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvBounded.bindAll

/-- info: 'IxCC.Own.Plain.EnvBounded.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvBounded.insert

/-- info: 'IxCC.Own.Plain.EnvBounded.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvBounded.mono

/-- info: 'IxCC.Own.Plain.EnvDen.bindAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvDen.bindAll

/-- info: 'IxCC.Own.Plain.EnvDen.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvDen.insert

/-- info: 'IxCC.Own.Plain.EnvDen.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvDen.transport

/-- info: 'IxCC.Own.Plain.EnvRoots.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvRoots.append

/-- info: 'IxCC.Own.Plain.EnvRoots.bindAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvRoots.bindAll

/-- info: 'IxCC.Own.Plain.EnvRoots.den_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvRoots.den_member

/-- info: 'IxCC.Own.Plain.EnvRoots.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvRoots.insert

/-- info: 'IxCC.Own.Plain.EnvRoots.member' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvRoots.member

/-- info: 'IxCC.Own.Plain.EnvRoots.restrict' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.EnvRoots.restrict

/-- info: 'IxCC.Own.Plain.ExternalPreserved.of_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ExternalPreserved.of_values

/-- info: 'IxCC.Own.Plain.JEntry.jweight_after' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.JEntry.jweight_after

/-- info: 'IxCC.Own.Plain.ResultRel.bind_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ResultRel.bind_frame

/-- info: 'IxCC.Own.Plain.ResultRel.later' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ResultRel.later

/-- info: 'IxCC.Own.Plain.ResultRel.ofOption' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ResultRel.ofOption

/-- info: 'IxCC.Own.Plain.ResultRel.preheap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ResultRel.preheap

/-- info: 'IxCC.Own.Plain.ResultRel.success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ResultRel.success

/-- info: 'IxCC.Own.Plain.ShapeResult.preheap' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.ShapeResult.preheap

/-- info: 'IxCC.Own.Plain.StackBounded.after' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackBounded.after

/-- info: 'IxCC.Own.Plain.StackBounded.lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackBounded.lookup

/-- info: 'IxCC.Own.Plain.StackBounded.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackBounded.mono

/-- info: 'IxCC.Own.Plain.StackDen.after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackDen.after

/-- info: 'IxCC.Own.Plain.StackDen.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackDen.lookup

/-- info: 'IxCC.Own.Plain.StackDen.reframe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackDen.reframe

/-- info: 'IxCC.Own.Plain.StackDen.retain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackDen.retain

/-- info: 'IxCC.Own.Plain.StackDen.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackDen.transport

/-- info: 'IxCC.Own.Plain.StackScope.after' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackScope.after

/-- info: 'IxCC.Own.Plain.StackScope.bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackScope.bind

/-- info: 'IxCC.Own.Plain.StackScope.head' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackScope.head

/-- info: 'IxCC.Own.Plain.StackScope.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackScope.lookup

/-- info: 'IxCC.Own.Plain.StackScope.rebind' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackScope.rebind

/-- info: 'IxCC.Own.Plain.StackViews.after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackViews.after

/-- info: 'IxCC.Own.Plain.StackViews.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackViews.bind

/-- info: 'IxCC.Own.Plain.StackViews.head' depends on axioms: [propext] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackViews.head

/-- info: 'IxCC.Own.Plain.StackViews.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackViews.lookup

/-- info: 'IxCC.Own.Plain.StackViews.rebind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.StackViews.rebind

/-- info: 'IxCC.Own.Plain.State.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.State.bind

/-- info: 'IxCC.Own.Plain.State.bind_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.State.bind_den

/-- info: 'IxCC.Own.Plain.State.declare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.State.declare

/-- info: 'IxCC.Own.Plain.State.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.State.resume

/-- info: 'IxCC.Own.Plain.Values.asCtor_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Values.asCtor_den

/-- info: 'IxCC.Own.Plain.Values.den_erased_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Values.den_erased_inv

/-- info: 'IxCC.Own.Plain.Values.den_lit_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Values.den_lit_inv

/-- info: 'IxCC.Own.Plain.Values.dens_of_toFirList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Values.dens_of_toFirList

/-- info: 'IxCC.Own.Plain.Values.natArgs_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms IxCC.Own.Plain.Values.natArgs_den
