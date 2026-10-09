import Compilatrix.Own.Plain.Check
import Compilatrix.Own.Plain.Proof.Actions
import Compilatrix.Own.Plain.Proof.Admission
import Compilatrix.Own.Plain.Proof.Bindings
import Compilatrix.Own.Plain.Proof.Bounds
import Compilatrix.Own.Plain.Proof.Call
import Compilatrix.Own.Plain.Proof.CallBind
import Compilatrix.Own.Plain.Proof.Candidate
import Compilatrix.Own.Plain.Proof.CaptureIdentity
import Compilatrix.Own.Plain.Proof.CaptureRoots
import Compilatrix.Own.Plain.Proof.Captures
import Compilatrix.Own.Plain.Proof.Checked
import Compilatrix.Own.Plain.Proof.CheckedShape
import Compilatrix.Own.Plain.Proof.CtorStep
import Compilatrix.Own.Plain.Proof.Drops
import Compilatrix.Own.Plain.Proof.Environment
import Compilatrix.Own.Plain.Proof.EvalShape
import Compilatrix.Own.Plain.Proof.Frames
import Compilatrix.Own.Plain.Proof.JoinLookup
import Compilatrix.Own.Plain.Proof.Jump
import Compilatrix.Own.Plain.Proof.JumpState
import Compilatrix.Own.Plain.Proof.Mono
import Compilatrix.Own.Plain.Proof.NonCall
import Compilatrix.Own.Plain.Proof.Prefixes
import Compilatrix.Own.Plain.Proof.Program
import Compilatrix.Own.Plain.Proof.Projection
import Compilatrix.Own.Plain.Proof.ResultCompose
import Compilatrix.Own.Plain.Proof.Results
import Compilatrix.Own.Plain.Proof.RhsShape
import Compilatrix.Own.Plain.Proof.RhsSteps
import Compilatrix.Own.Plain.Proof.Scalars
import Compilatrix.Own.Plain.Proof.Scope
import Compilatrix.Own.Plain.Proof.Selected
import Compilatrix.Own.Plain.Proof.ShapeOps
import Compilatrix.Own.Plain.Proof.ShapeResult
import Compilatrix.Own.Plain.Proof.Simulation
import Compilatrix.Own.Plain.Proof.StackIdentity
import Compilatrix.Own.Plain.Proof.StackRetain
import Compilatrix.Own.Plain.Proof.StackScope
import Compilatrix.Own.Plain.Proof.State
import Compilatrix.Own.Plain.Proof.TailCall
import Compilatrix.Own.Plain.Proof.Terminals
import Compilatrix.Own.Plain.Proof.Transfers
import Compilatrix.Own.Plain.Proof.Unfold
import Compilatrix.Own.Plain.Proof.ValidRoots
import Compilatrix.Own.Plain.Proof.Values
import Compilatrix.Own.Plain.Semantics
import Compilatrix.Own.Plain.Syntax

/-! Exact axiom fences for the checked plain-RC foundation. -/

/-- info: 'Compilatrix.Own.Plain.action_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.action_shape

/-- info: 'Compilatrix.Own.Plain.altsEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.altsEq_iff

/-- info: 'Compilatrix.Own.Plain.arg_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.arg_den

/-- info: 'Compilatrix.Own.Plain.argsOwned_of_scope' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.argsOwned_of_scope

/-- info: 'Compilatrix.Own.Plain.args_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.args_den

/-- info: 'Compilatrix.Own.Plain.argument_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.argument_step

/-- info: 'Compilatrix.Own.Plain.asCtor_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.asCtor_bounded

/-- info: 'Compilatrix.Own.Plain.asCtor_field_canDup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.asCtor_field_canDup

/-- info: 'Compilatrix.Own.Plain.balance_append_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.balance_append_comm

/-- info: 'Compilatrix.Own.Plain.balance_immediate' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.balance_immediate

/-- info: 'Compilatrix.Own.Plain.balance_resume' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.balance_resume

/-- info: 'Compilatrix.Own.Plain.balance_rotate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.balance_rotate

/-- info: 'Compilatrix.Own.Plain.bodyMapEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.bodyMapEq_iff

/-- info: 'Compilatrix.Own.Plain.boolPinOk_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.boolPinOk_sound

/-- info: 'Compilatrix.Own.Plain.callFun_agrees_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.callFun_agrees_of

/-- info: 'Compilatrix.Own.Plain.call_bind_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.call_bind_refines

/-- info: 'Compilatrix.Own.Plain.call_heap_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.call_heap_shape

/-- info: 'Compilatrix.Own.Plain.call_of_smaller_clocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.call_of_smaller_clocks

/-- info: 'Compilatrix.Own.Plain.call_shape_of_smaller' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.call_shape_of_smaller

/-- info: 'Compilatrix.Own.Plain.canDup_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.canDup_member

/-- info: 'Compilatrix.Own.Plain.canonical_body' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.canonical_body

/-- info: 'Compilatrix.Own.Plain.canonical_body_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.canonical_body_of

/-- info: 'Compilatrix.Own.Plain.canonical_call' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.canonical_call

/-- info: 'Compilatrix.Own.Plain.canonical_call_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.canonical_call_refines

/-- info: 'Compilatrix.Own.Plain.canonical_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.canonical_refines

/-- info: 'Compilatrix.Own.Plain.checkBody_erases' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checkBody_erases

/-- info: 'Compilatrix.Own.Plain.checkBody_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checkBody_iff

/-- info: 'Compilatrix.Own.Plain.checkBoolPins_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checkBoolPins_sound

/-- info: 'Compilatrix.Own.Plain.checkFunction_domain' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checkFunction_domain

/-- info: 'Compilatrix.Own.Plain.checkFunction_parts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checkFunction_parts

/-- info: 'Compilatrix.Own.Plain.checkPlainMap_parts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checkPlainMap_parts

/-- info: 'Compilatrix.Own.Plain.checked_body_is_canonical' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checked_body_is_canonical

/-- info: 'Compilatrix.Own.Plain.checked_body_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checked_body_refines

/-- info: 'Compilatrix.Own.Plain.checked_program_reclaims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checked_program_reclaims

/-- info: 'Compilatrix.Own.Plain.checked_program_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checked_program_refines

/-- info: 'Compilatrix.Own.Plain.checked_program_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.checked_program_shape

/-- info: 'Compilatrix.Own.Plain.codeEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.codeEq_iff

/-- info: 'Compilatrix.Own.Plain.constructor_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.constructor_step

/-- info: 'Compilatrix.Own.Plain.copies_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.copies_sound

/-- info: 'Compilatrix.Own.Plain.den_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.den_bounded

/-- info: 'Compilatrix.Own.Plain.den_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.den_member

/-- info: 'Compilatrix.Own.Plain.dens_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.dens_bounded

/-- info: 'Compilatrix.Own.Plain.dens_preserve' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.dens_preserve

/-- info: 'Compilatrix.Own.Plain.dens_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.dens_transport

/-- info: 'Compilatrix.Own.Plain.drops_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.drops_sound

/-- info: 'Compilatrix.Own.Plain.entryDen_declare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.entryDen_declare

/-- info: 'Compilatrix.Own.Plain.envBounded_empty' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.envBounded_empty

/-- info: 'Compilatrix.Own.Plain.envRoots_cons' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.envRoots_cons

/-- info: 'Compilatrix.Own.Plain.erase_lowerAlts' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.erase_lowerAlts

/-- info: 'Compilatrix.Own.Plain.erase_lowerCode' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.erase_lowerCode

/-- info: 'Compilatrix.Own.Plain.erase_lowerOpt' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.erase_lowerOpt

/-- info: 'Compilatrix.Own.Plain.erase_prefix' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.erase_prefix

/-- info: 'Compilatrix.Own.Plain.erase_transfer' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.erase_transfer

/-- info: 'Compilatrix.Own.Plain.evalAction_dec_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalAction_dec_owned

/-- info: 'Compilatrix.Own.Plain.evalAction_inc_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalAction_inc_field

/-- info: 'Compilatrix.Own.Plain.evalAction_inc_owned' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalAction_inc_owned

/-- info: 'Compilatrix.Own.Plain.evalActions_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalActions_append

/-- info: 'Compilatrix.Own.Plain.evalAlts_agrees_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalAlts_agrees_of

/-- info: 'Compilatrix.Own.Plain.evalAlts_cons' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalAlts_cons

/-- info: 'Compilatrix.Own.Plain.evalAlts_nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalAlts_nil

/-- info: 'Compilatrix.Own.Plain.evalAlts_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalAlts_refines

/-- info: 'Compilatrix.Own.Plain.evalAlts_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalAlts_shape

/-- info: 'Compilatrix.Own.Plain.evalArgs_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalArgs_append

/-- info: 'Compilatrix.Own.Plain.evalCall_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalCall_agrees

/-- info: 'Compilatrix.Own.Plain.evalCall_agrees_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalCall_agrees_of

/-- info: 'Compilatrix.Own.Plain.evalCall_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalCall_eq

/-- info: 'Compilatrix.Own.Plain.evalCall_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalCall_of

/-- info: 'Compilatrix.Own.Plain.evalRhs_alloc_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalRhs_alloc_owned

/-- info: 'Compilatrix.Own.Plain.evalVars_congr' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.evalVars_congr

/-- info: 'Compilatrix.Own.Plain.eval_act' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_act

/-- info: 'Compilatrix.Own.Plain.eval_actionPrefix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_actionPrefix

/-- info: 'Compilatrix.Own.Plain.eval_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_agrees

/-- info: 'Compilatrix.Own.Plain.eval_agrees_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_agrees_of

/-- info: 'Compilatrix.Own.Plain.eval_bindCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_bindCall

/-- info: 'Compilatrix.Own.Plain.eval_bindRhs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_bindRhs

/-- info: 'Compilatrix.Own.Plain.eval_case' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_case

/-- info: 'Compilatrix.Own.Plain.eval_heap_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_heap_shape

/-- info: 'Compilatrix.Own.Plain.eval_jmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_jmp

/-- info: 'Compilatrix.Own.Plain.eval_jp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_jp

/-- info: 'Compilatrix.Own.Plain.eval_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_mono

/-- info: 'Compilatrix.Own.Plain.eval_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_refines

/-- info: 'Compilatrix.Own.Plain.eval_ret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_ret

/-- info: 'Compilatrix.Own.Plain.eval_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_shape

/-- info: 'Compilatrix.Own.Plain.eval_tcall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_tcall

/-- info: 'Compilatrix.Own.Plain.eval_trap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.eval_trap

/-- info: 'Compilatrix.Own.Plain.fir_primitive_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.fir_primitive_pure

/-- info: 'Compilatrix.Own.Plain.fir_rhs_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.fir_rhs_pure

/-- info: 'Compilatrix.Own.Plain.fresh_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.fresh_avoids

/-- info: 'Compilatrix.Own.Plain.fresh_nodup_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.fresh_nodup_append

/-- info: 'Compilatrix.Own.Plain.get_bindAll_untouched' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.get_bindAll_untouched

/-- info: 'Compilatrix.Own.Plain.jump_measure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.jump_measure

/-- info: 'Compilatrix.Own.Plain.jump_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.jump_progress

/-- info: 'Compilatrix.Own.Plain.jump_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.jump_state

/-- info: 'Compilatrix.Own.Plain.lookupJ_weight' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.lookupJ_weight

/-- info: 'Compilatrix.Own.Plain.lookup_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.lookup_ready

/-- info: 'Compilatrix.Own.Plain.nonCall_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.nonCall_refines

/-- info: 'Compilatrix.Own.Plain.nonCall_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.nonCall_step

/-- info: 'Compilatrix.Own.Plain.ofOption_pure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.ofOption_pure

/-- info: 'Compilatrix.Own.Plain.optEq_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.optEq_iff

/-- info: 'Compilatrix.Own.Plain.primResult_immediate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.primResult_immediate

/-- info: 'Compilatrix.Own.Plain.prim_bounded' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.prim_bounded

/-- info: 'Compilatrix.Own.Plain.primitive_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.primitive_owned

/-- info: 'Compilatrix.Own.Plain.primitive_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.primitive_step

/-- info: 'Compilatrix.Own.Plain.programDomain_function' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.programDomain_function

/-- info: 'Compilatrix.Own.Plain.projection_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.projection_owned

/-- info: 'Compilatrix.Own.Plain.projection_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.projection_step

/-- info: 'Compilatrix.Own.Plain.retained_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.retained_empty

/-- info: 'Compilatrix.Own.Plain.retained_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.retained_eq

/-- info: 'Compilatrix.Own.Plain.return_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.return_refines

/-- info: 'Compilatrix.Own.Plain.rhs_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.rhs_shape

/-- info: 'Compilatrix.Own.Plain.run_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.run_mono

/-- info: 'Compilatrix.Own.Plain.shape_bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.shape_bind

/-- info: 'Compilatrix.Own.Plain.shape_later' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.shape_later

/-- info: 'Compilatrix.Own.Plain.shape_ofOption' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.shape_ofOption

/-- info: 'Compilatrix.Own.Plain.signatures_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.signatures_lookup

/-- info: 'Compilatrix.Own.Plain.stackArities_after' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.stackArities_after

/-- info: 'Compilatrix.Own.Plain.state_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.state_empty

/-- info: 'Compilatrix.Own.Plain.state_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.state_entry

/-- info: 'Compilatrix.Own.Plain.tailCall_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.tailCall_transfer

/-- info: 'Compilatrix.Own.Plain.transfer_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.transfer_sound

/-- info: 'Compilatrix.Own.Plain.trap_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.trap_refines

/-- info: 'Compilatrix.Own.Rc.changeCount_heapOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.changeCount_heapOk

/-- info: 'Compilatrix.Own.Rc.dropAll_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.dropAll_shape

/-- info: 'Compilatrix.Own.Rc.releaseOne_size' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Rc.releaseOne_size

/-- info: 'Compilatrix.Own.Plain.Agrees.later' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Agrees.later

/-- info: 'Compilatrix.Own.Plain.Agrees.ofOption' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Agrees.ofOption

/-- info: 'Compilatrix.Own.Plain.Bounded.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Bounded.mono

/-- info: 'Compilatrix.Own.Plain.CaptureView.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.CaptureView.bind

/-- info: 'Compilatrix.Own.Plain.CaptureView.captured_nodup' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.CaptureView.captured_nodup

/-- info: 'Compilatrix.Own.Plain.CaptureView.declare' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.CaptureView.declare

/-- info: 'Compilatrix.Own.Plain.CaptureView.rebind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.CaptureView.rebind

/-- info: 'Compilatrix.Own.Plain.CaptureView.retained_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.CaptureView.retained_roots

/-- info: 'Compilatrix.Own.Plain.CaptureView.roots' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.CaptureView.roots

/-- info: 'Compilatrix.Own.Plain.CaptureView.trans' does not depend on any axioms -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.CaptureView.trans

/-- info: 'Compilatrix.Own.Plain.Code.size_pos' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Code.size_pos

/-- info: 'Compilatrix.Own.Plain.EntryDen.charge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EntryDen.charge

/-- info: 'Compilatrix.Own.Plain.EntryDen.reframe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EntryDen.reframe

/-- info: 'Compilatrix.Own.Plain.EntryDen.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EntryDen.transport

/-- info: 'Compilatrix.Own.Plain.EnvBounded.arg' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvBounded.arg

/-- info: 'Compilatrix.Own.Plain.EnvBounded.args' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvBounded.args

/-- info: 'Compilatrix.Own.Plain.EnvBounded.bindAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvBounded.bindAll

/-- info: 'Compilatrix.Own.Plain.EnvBounded.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvBounded.insert

/-- info: 'Compilatrix.Own.Plain.EnvBounded.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvBounded.mono

/-- info: 'Compilatrix.Own.Plain.EnvDen.bindAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvDen.bindAll

/-- info: 'Compilatrix.Own.Plain.EnvDen.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvDen.insert

/-- info: 'Compilatrix.Own.Plain.EnvDen.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvDen.transport

/-- info: 'Compilatrix.Own.Plain.EnvRoots.append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvRoots.append

/-- info: 'Compilatrix.Own.Plain.EnvRoots.bindAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvRoots.bindAll

/-- info: 'Compilatrix.Own.Plain.EnvRoots.den_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvRoots.den_member

/-- info: 'Compilatrix.Own.Plain.EnvRoots.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvRoots.insert

/-- info: 'Compilatrix.Own.Plain.EnvRoots.member' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvRoots.member

/-- info: 'Compilatrix.Own.Plain.EnvRoots.restrict' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.EnvRoots.restrict

/-- info: 'Compilatrix.Own.Plain.ExternalPreserved.of_values' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.ExternalPreserved.of_values

/-- info: 'Compilatrix.Own.Plain.JEntry.jweight_after' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.JEntry.jweight_after

/-- info: 'Compilatrix.Own.Plain.ResultRel.bind_frame' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.ResultRel.bind_frame

/-- info: 'Compilatrix.Own.Plain.ResultRel.later' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.ResultRel.later

/-- info: 'Compilatrix.Own.Plain.ResultRel.ofOption' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.ResultRel.ofOption

/-- info: 'Compilatrix.Own.Plain.ResultRel.preheap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.ResultRel.preheap

/-- info: 'Compilatrix.Own.Plain.ResultRel.success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.ResultRel.success

/-- info: 'Compilatrix.Own.Plain.ShapeResult.preheap' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.ShapeResult.preheap

/-- info: 'Compilatrix.Own.Plain.StackBounded.after' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackBounded.after

/-- info: 'Compilatrix.Own.Plain.StackBounded.lookup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackBounded.lookup

/-- info: 'Compilatrix.Own.Plain.StackBounded.mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackBounded.mono

/-- info: 'Compilatrix.Own.Plain.StackDen.after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackDen.after

/-- info: 'Compilatrix.Own.Plain.StackDen.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackDen.lookup

/-- info: 'Compilatrix.Own.Plain.StackDen.reframe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackDen.reframe

/-- info: 'Compilatrix.Own.Plain.StackDen.retain' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackDen.retain

/-- info: 'Compilatrix.Own.Plain.StackDen.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackDen.transport

/-- info: 'Compilatrix.Own.Plain.StackScope.after' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackScope.after

/-- info: 'Compilatrix.Own.Plain.StackScope.bind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackScope.bind

/-- info: 'Compilatrix.Own.Plain.StackScope.head' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackScope.head

/-- info: 'Compilatrix.Own.Plain.StackScope.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackScope.lookup

/-- info: 'Compilatrix.Own.Plain.StackScope.rebind' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackScope.rebind

/-- info: 'Compilatrix.Own.Plain.StackViews.after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackViews.after

/-- info: 'Compilatrix.Own.Plain.StackViews.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackViews.bind

/-- info: 'Compilatrix.Own.Plain.StackViews.head' depends on axioms: [propext] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackViews.head

/-- info: 'Compilatrix.Own.Plain.StackViews.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackViews.lookup

/-- info: 'Compilatrix.Own.Plain.StackViews.rebind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.StackViews.rebind

/-- info: 'Compilatrix.Own.Plain.State.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.State.bind

/-- info: 'Compilatrix.Own.Plain.State.bind_den' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.State.bind_den

/-- info: 'Compilatrix.Own.Plain.State.declare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.State.declare

/-- info: 'Compilatrix.Own.Plain.State.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.State.resume

/-- info: 'Compilatrix.Own.Plain.Values.asCtor_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Values.asCtor_den

/-- info: 'Compilatrix.Own.Plain.Values.den_erased_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Values.den_erased_inv

/-- info: 'Compilatrix.Own.Plain.Values.den_lit_inv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Values.den_lit_inv

/-- info: 'Compilatrix.Own.Plain.Values.dens_of_toFirList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Values.dens_of_toFirList

/-- info: 'Compilatrix.Own.Plain.Values.natArgs_den' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Compilatrix.Own.Plain.Values.natArgs_den
