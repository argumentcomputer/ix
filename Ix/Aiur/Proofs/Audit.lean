/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean
import Ix.Aiur.BoundVerifier
import Ix.Aiur.Proofs.Activity
import Ix.Aiur.Proofs.CallOrder
import Ix.Aiur.Proofs.Lookup
import Ix.Aiur.Proofs.Execution
import Ix.Aiur.Proofs.Memory
import Ix.Aiur.Proofs.LocalConstraints
import Ix.Aiur.Proofs.ByteLookups
import Ix.Aiur.Proofs.LookupMessages
import Ix.Aiur.Proofs.LookupShapes
import Ix.Aiur.Proofs.GlobalLookups
import Ix.Aiur.Proofs.LookupBudget
import Ix.Aiur.Proofs.ReturnGates
import Ix.Aiur.Proofs.BranchSelection
import Ix.Aiur.Proofs.CallInventory
import Ix.Aiur.Proofs.FunctionRows
import Ix.Aiur.Proofs.BlockQueryPool
import Ix.Aiur.Proofs.CircuitRowExecution
import Ix.Aiur.Proofs.CircuitRowCounts
import Ix.Aiur.Proofs.PublicCircuitExecution
import Ix.Aiur.Proofs.EncodedCircuitExecution
import Ix.Aiur.Proofs.CircuitTraces
import Ix.Aiur.Proofs.CircuitMembership
import Ix.Aiur.Proofs.LookupLayout
import Ix.Aiur.Proofs.MemoryColumns
import Ix.Aiur.Proofs.ByteColumns
import Ix.Aiur.Proofs.ExpressionGraph
import Ix.Aiur.Proofs.Grouping
import Ix.Aiur.Proofs.TailMatches
import Ix.Aiur.Proofs.NormalizationFrames

/-! Exact proof and execution inventory for the implemented C8 components.
The compiler and proof-system runtime are inventoried here; their presence
is not a proof of runtime refinement or public certified semantic soundness.
-/

open Lean Lean.Elab Command

namespace Aiur.Proofs.Audit

def callOrderRoots : Array Lean.Name := #[
  `Aiur.G.n_ofNat, `Aiur.G.sub_eq_zero_iff, `Aiur.G.n_add, `Aiur.G.n_mul,
  `Aiur.AIR.packRank_lt, `Aiur.AIR.call_order_strict, `Aiur.AIR.call_order_irrefl,
  `Aiur.AIR.active_call_order_strict, `Aiur.AIR.packed_call_order_strict,
  `Aiur.AIR.call_relation_wellFounded]

def lookupRoots : Array Lean.Name := #[
  `Aiur.G.zero_add, `Aiur.G.ofNat_ne_zero_of_lt,
  `Aiur.AIR.characteristic_queries_balance, `Aiur.AIR.suppliedWeight_nonzero_provider,
  `Aiur.AIR.exactLookupBalance_provider, `Aiur.AIR.byteRangeMessage_bounded,
  `Aiur.AIR.exactLookupBalance_byteRange, `Aiur.AIR.exactLookupBalance_rankBytes,
  `Aiur.AIR.exactLookupBalance_call_order]

def executionRoots : Array Lean.Name := #[
  `Aiur.AIR.FunctionRow.Valid.active_of_nonzero,
  `Aiur.AIR.functionQueries_provider,
  `Aiur.AIR.balancedRows_execute,
  `Aiur.AIR.balancedRoots_execute]

def memoryRoots : Array Lean.Name := #[
  `Aiur.AIR.MemoryRowsValid.pointer_injective,
  `Aiur.AIR.memoryFacts_functional,
  `Aiur.AIR.memoryQueries_provider,
  `Aiur.AIR.memoryQueries_width,
  `Aiur.AIR.memoryQueries_consistent,
  `Aiur.AIR.memoryQueries_fact]

def fieldRoots : Array Lean.Name := #[
  `Aiur.gSize_prime,
  `Aiur.G.mul_eq_zero_iff,
  `Aiur.G.boolean_of_constraint,
  `Aiur.G.boolean_of_one_sub_constraint,
  `Aiur.G.eqZero_of_constraints]

def localConstraintRoots : Array Lean.Name := #[
  `Aiur.AIR.selectorSum_count_le_one,
  `Aiur.AIR.selectorSum_inactive,
  `Aiur.AIR.selectorSum_active_split,
  `Aiur.AIR.selectorSum_characteristic_cancel,
  `Aiur.AIR.nonzero_multiplicity_selector_one,
  `Aiur.AIR.active_eqZero,
  `Aiur.AIR.active_case,
  `Aiur.AIR.active_default,
  `Aiur.AIR.MemoryRowsPolynomials.valid,
  `Aiur.AIR.MemoryRowsPolynomials.functional]

def byteArithmeticRoots : Array Lean.Name := #[
  `Aiur.AIR.inverse256_correct,
  `Aiur.AIR.byte_add_carry,
  `Aiur.AIR.byte_sub_borrow,
  `Aiur.AIR.byte_carry_relation,
  `Aiur.AIR.pack4_n,
  `Aiur.AIR.u32Carry_relation,
  `Aiur.AIR.u32_less_than,
  `Aiur.AIR.active_u32_less_than]

def byteLookupRoots : Array Lean.Name := #[
  `Aiur.AIR.exactLookupBalance_byte1,
  `Aiur.AIR.exactLookupBalance_byte2,
  `Aiur.AIR.exactLookupBalance_byte1_step,
  `Aiur.AIR.exactLookupBalance_byte2_step,
  `Aiur.AIR.active_u32_less_than_step]

def lookupMessageRoots : Array Lean.Name := #[
  `Aiur.AIR.padMessage_injective_of_shape,
  `Aiur.AIR.exactLookupBalance_of_injective_on,
  `Aiur.AIR.ExactLookupBalance.filter,
  `Aiur.AIR.paddedLookupBalance_provider,
  `Aiur.AIR.paddedLookupBalance_exact,
  `Aiur.AIR.functionMessage_shape,
  `Aiur.AIR.memoryMessage_shape,
  `Aiur.AIR.byte1Request_shape,
  `Aiur.AIR.byte2Request_shape,
  `Aiur.AIR.functionMessage_injective,
  `Aiur.AIR.exactLookupBalance_functionMessages,
  `Aiur.AIR.memoryMessage_injective,
  `Aiur.AIR.exactLookupBalance_memoryMessages,
  `Aiur.AIR.padMessage_append_zero,
  `Aiur.AIR.functionMessage_rank_alias]

def lookupShapeRoots : Array Lean.Name := #[
  `Aiur.Bytecode.AIR.RunBlock.return_size,
  `Aiur.Bytecode.AIR.RunFunction.return_size,
  `Aiur.Bytecode.AIR.Step.calls_lookupShape,
  `Aiur.Bytecode.AIR.RunOps.calls_lookupShape,
  `Aiur.Bytecode.AIR.RunBlock.calls_lookupShape,
  `Aiur.Bytecode.AIR.RunFunction.calls_lookupShape,
  `Aiur.BoundVerifier.Backend.air_return_size,
  `Aiur.BoundVerifier.Backend.claim_shape]

def globalLookupRoots : Array Lean.Name := #[
  `Aiur.AIR.padded_functionMessage_reflects,
  `Aiur.AIR.GlobalLookups.function_provider,
  `Aiur.AIR.GlobalLookups.byte1,
  `Aiur.AIR.GlobalLookups.byte2,
  `Aiur.AIR.GlobalLookups.memory_fact,
  `Aiur.AIR.GlobalLookups.memory_consistent,
  `Aiur.AIR.GlobalLookups.byte1_step,
  `Aiur.AIR.GlobalLookups.byte2_step,
  `Aiur.AIR.GlobalLookups.rank_bytes,
  `Aiur.AIR.GlobalLookups.rows_execute,
  `Aiur.AIR.GlobalLookups.roots_execute,
  `Aiur.BoundVerifier.Backend.root_lookupShape,
  `Aiur.BoundVerifier.claim_padding,
  `Aiur.BoundVerifier.Backend.global_execution]

def lookupBudgetRoots : Array Lean.Name := #[
  `Aiur.lookupQueryBound_sound,
  `Aiur.lookupQueryBound_consumer_count,
  `Aiur.lookupQueryBound_shape,
  `Aiur.lookupQueryBound_step_no_overflow,
  `Aiur.lookupQueryBound_complete,
  `Aiur.lookupSlotSum_bounded,
  `Aiur.lookupQueryBound_encodedKey,
  `Aiur.AIR.GlobalLookups.of_budget]

def selectorControlRoots : Array Lean.Name := #[
  `Aiur.AIR.weightedMessage_active,
  `Aiur.AIR.weightedMessage_inactive,
  `Aiur.AIR.slotMessage_active,
  `Aiur.AIR.continuation_merge,
  `Aiur.Bytecode.Block.selectorFlow_sound,
  `Aiur.Bytecode.Block.selectorFlow_yields_empty,
  `Aiur.Bytecode.Block.selectorFlow_active_return,
  `Aiur.Bytecode.Block.selectorFlow_provider_return,
  `Aiur.AIR.SelectorFlow.Sound.inactive_terminal,
  `Aiur.AIR.SelectorFlow.Sound.return_stops_continuation,
  `Aiur.AIR.SelectorFlow.Sound.yield_starts_continuation,
  `Aiur.Bytecode.Block.returnGates_reflects,
  `Aiur.Bytecode.Block.return_message]

def operationRowRoots : Array Lean.Name := #[
  `Aiur.AIR.emitOp_step,
  `Aiur.AIR.emitOps_run,
  `Aiur.AIR.emitOp_calls,
  `Aiur.AIR.emitOps_calls,
  `Aiur.AIR.CallsEmitted.ordered,
  `Aiur.AIR.active_array_equality,
  `Aiur.Bytecode.Block.selectorFlow_boolean,
  `Aiur.Bytecode.MatchPolynomials.active_branch,
  `Aiur.Bytecode.MatchPolynomials.active_match,
  `Aiur.Bytecode.MatchPolynomials.active_matchContinue]

def blockRowRoots : Array Lean.Name := #[
  `Aiur.Bytecode.Block.emitRow_projection,
  `Aiur.Bytecode.Block.emitRow_selectors,
  `Aiur.AIR.mergeEquations_chosen,
  `Aiur.Bytecode.branchRows_selected,
  `Aiur.Bytecode.Block.emitRow_run,
  `Aiur.Bytecode.Block.emitRow_tracks_calls,
  `Aiur.Bytecode.Block.emitRow_inputs,
  `Aiur.Bytecode.Function.emitRow_run,
  `Aiur.Bytecode.Function.emitRow_valid,
  `Aiur.AIR.slotMessage_chosen,
  `Aiur.Bytecode.Function.emitRow_message]

def querySlotRoots : Array Lean.Name := #[
  `Aiur.Bytecode.Block.emitRow_equation_querySlots,
  `Aiur.AIR.QuerySlots.slot_multiplicity,
  `Aiur.AIR.QuerySlots.multiplicity_boolean,
  `Aiur.AIR.QuerySlots.active_singleton,
  `Aiur.AIR.QuerySlots.slot_message,
  `Aiur.AIR.QuerySlots.queries_reflect,
  `Aiur.AIR.QuerySlots.padded_balance,
  `Aiur.AIR.decodedQueries_length,
  `Aiur.Bytecode.Block.emitRow_queried_pool,
  `Aiur.Bytecode.Function.emitRow_pool_valid]

def circuitRowRoots : Array Lean.Name := #[
  `Aiur.AIR.emitMembers_spec,
  `Aiur.Bytecode.Circuit.emitRow_spec,
  `Aiur.Bytecode.Circuit.emitRow_boolean,
  `Aiur.Bytecode.Circuit.emitRow_active_member,
  `Aiur.Bytecode.Circuit.emitRow_querySlots,
  `Aiur.AIR.circuitEmission_rank_queried,
  `Aiur.AIR.MemberEmission.FromProgram.return_count,
  `Aiur.AIR.circuitEmission_return_count,
  `Aiur.AIR.circuitEmission_return_message,
  `Aiur.Bytecode.Circuit.emitRow_valid]

def rowCountRoots : Array Lean.Name := #[
  `Aiur.Bytecode.Ctrl.controlCounts_spec,
  `Aiur.Bytecode.Block.controlCounts_spec,
  `Aiur.Bytecode.Block.rowBounds_of_controlCounts,
  `Aiur.Bytecode.Block.return_bound_of_controlCounts,
  `Aiur.Bytecode.Block.returns_le_selectors,
  `Aiur.Bytecode.Toplevel.validateRowCounts_circuit,
  `Aiur.Bytecode.Circuit.validateRowCounts_spec,
  `Aiur.Bytecode.Circuit.emitRow_count_bounds,
  `Aiur.Bytecode.Circuit.emitRow_valid_checked,
  `Aiur.BoundVerifier.Backend.circuit_row_counts]

def circuitTableRoots : Array Lean.Name := #[
  `Aiur.Bytecode.Circuit.emitRow_valid_in_pool,
  `Aiur.AIR.suppliedWeight_padded_congr,
  `Aiur.AIR.PaddedLookupBalance.congr_providers,
  `Aiur.Bytecode.Circuit.emitRow_provider,
  `Aiur.AIR.AuxiliaryTables.global_of_circuit_balance,
  `Aiur.AIR.FunctionRow.inactive_valid,
  `Aiur.AIR.CircuitWitness.provider_row,
  `Aiur.AIR.CircuitWitness.interpreted_row,
  `Aiur.AIR.circuitWitnesses_interpret,
  `Aiur.AIR.circuitWitnesses_execute,
  `Aiur.AIR.PaddedLookupBalance.congr_queries,
  `Aiur.BoundVerifier.Backend.public_circuit_execution]

def branchlessRoots : Array Lean.Name := #[
  `Aiur.AIR.QueryWriters.single,
  `Aiur.Bytecode.Function.emitRow_terminal_writers,
  `Aiur.AIR.circuitEmission_queryWriters,
  `Aiur.Bytecode.Circuit.emitRow_queryWriters,
  `Aiur.Bytecode.Circuit.emitRow_queries_reflect,
  `Aiur.AIR.slotMessage_member_length,
  `Aiur.AIR.QuerySlots.decoded_widths,
  `Aiur.AIR.circuitWitnesses_queries_reflect,
  `Aiur.AIR.circuitWitnesses_decoded_widths,
  `Aiur.BoundVerifier.Backend.encoded_circuit_execution]

def circuitTraceRoots : Array Lean.Name := #[
  `Aiur.AIR.CircuitTraces.slot_sum_append,
  `Aiur.AIR.CircuitTraces.capacity_bounded,
  `Aiur.AIR.emitCircuitWitness_spec,
  `Aiur.AIR.encodedQueries_length,
  `Aiur.AIR.encodedCircuitQueryPool_uniform_bound,
  `Aiur.AIR.emitCircuitWitnesses_spec,
  `Aiur.AIR.CircuitTraces.emitWitnesses_spec,
  `Aiur.BoundVerifier.Backend.trace_circuit_execution]

def circuitMembershipRoots : Array Lean.Name := #[
  `Aiur.Bytecode.singletonCircuits_constrained,
  `Aiur.CompiledToplevel.groupFunctions_constrained,
  `Aiur.finishCompilation_circuits_constrained,
  `Aiur.Source.Toplevel.compile_circuits_constrained,
  `Aiur.BoundVerifier.Backend.circuits_constrained,
  `Aiur.Bytecode.Toplevel.validateLookupShapes_function,
  `Aiur.AIR.CircuitWitness.shapes_of_compiled,
  `Aiur.BoundVerifier.Backend.witness_shapes,
  `Aiur.BoundVerifier.Backend.compiled_trace_execution]

def lookupLayoutRoots : Array Lean.Name := #[
  `Aiur.Concrete.Bytecode.opLayout_lookupUsage,
  `Aiur.Concrete.Bytecode.opsLayout_lookupUsage,
  `Aiur.AIR.emitOp_lookupUsage,
  `Aiur.AIR.emitOps_lookupUsage,
  `Aiur.Bytecode.branchRows_lookupUsage,
  `Aiur.Bytecode.Ctrl.emitRow_lookupUsage,
  `Aiur.Bytecode.Block.emitRow_lookupUsage,
  `Aiur.Concrete.Bytecode.ctrlLayout_lookupUsage,
  `Aiur.Concrete.Bytecode.blockLayout_lookupUsage,
  `Aiur.Concrete.Function.compile_lookupLayout,
  `Aiur.Concrete.Decls.toBytecode_lookupLayout,
  `Aiur.Bytecode.rewriteCtrl_lookupUsage,
  `Aiur.Bytecode.rewriteBlock_lookupUsage,
  `Aiur.Bytecode.Toplevel.deduplicate_lookupLayout,
  `Aiur.finishCompilation_lookupLayout,
  `Aiur.Source.Toplevel.compile_lookupLayout,
  `Aiur.BoundVerifier.Backend.functions_lookupLayout,
  `Aiur.Bytecode.singletonCircuits_lookupBound,
  `Aiur.Bytecode.merged_lookupBound,
  `Aiur.CompiledToplevel.groupFunctions_lookupBound,
  `Aiur.finishCompilation_lookupBound,
  `Aiur.Source.Toplevel.compile_lookupBound,
  `Aiur.BoundVerifier.Backend.circuits_lookupBound,
  `Aiur.AIR.CircuitWitness.lookupBounds_of_compiled,
  `Aiur.BoundVerifier.Backend.witness_lookupBounds,
  `Aiur.BoundVerifier.Backend.bounded_trace_execution]

def memoryColumnRoots : Array Lean.Name := #[
  `Aiur.AIR.decodeMemoryRow_width,
  `Aiur.AIR.decodeMemoryRows_size,
  `Aiur.AIR.memoryColumnProvider_reflect,
  `Aiur.AIR.decodeMemoryRows_polynomials,
  `Aiur.AIR.decodeMemoryRows_valid,
  `Aiur.AIR.decodeMemoryRows_providers,
  `Aiur.AIR.memoryMatrixProviders_reflect,
  `Aiur.Concrete.Decls.toBytecode_memorySizes_distinct,
  `Aiur.Bytecode.Toplevel.deduplicate_memorySizes,
  `Aiur.finishCompilation_memorySizes,
  `Aiur.Source.Toplevel.compile_memorySizes_distinct,
  `Aiur.BoundVerifier.Backend.memorySizes_distinct,
  `Aiur.BoundVerifier.Backend.memorySizes_canonical,
  `Aiur.AIR.MemoryTraces.slot_sum_append,
  `Aiur.AIR.MemoryTraces.rows_valid,
  `Aiur.AIR.MemoryTraces.rows_size_le,
  `Aiur.AIR.MemoryTraces.providers_reflect,
  `Aiur.AIR.MemoryTraces.capacity_bounded,
  `Aiur.AIR.MemoryTraces.functional,
  `Aiur.AIR.MemoryTraces.functional_of_budget,
  `Aiur.AIR.MemoryTraces.circuitProviders_reflect,
  `Aiur.BoundVerifier.Backend.memory_trace_execution]

def byteColumnRoots : Array Lean.Name := #[
  `Aiur.fixedTraceHeights_sound,
  `Aiur.fixedTraceHeights_complete,
  `Aiur.FixedTraceHeights.alignment,
  `Aiur.fixedTraceHeights_bytes,
  `Aiur.AIR.byte1ColumnProvider_reflect,
  `Aiur.AIR.byte2ColumnProvider_reflect,
  `Aiur.AIR.CircuitTraces.fixed_heights_append,
  `Aiur.AIR.MemoryTraces.fixed_heights_append,
  `Aiur.AIR.canonical_byte_metadata,
  `Aiur.AIR.suppliedWeight_perm,
  `Aiur.AIR.PaddedLookupBalance.perm_providers,
  `Aiur.AIR.flatMap_map_swap,
  `Aiur.AIR.byte1MatrixProviders_reflect,
  `Aiur.AIR.byte2MatrixProviders_reflect,
  `Aiur.AIR.ByteTraces.providers_reflect,
  `Aiur.AIR.SystemTraces.fixed_heights,
  `Aiur.AIR.SystemTraces.memory_functional,
  `Aiur.BoundVerifier.Backend.column_trace_execution]

def expressionGraphRoots : Array Lean.Name := #[
  `Aiur.NativeAIR.Node.check_iff,
  `Aiur.NativeAIR.checkNodes_iff,
  `Aiur.NativeAIR.checkedGraphPrefix_iff,
  `Aiur.NativeAIR.roots_below_prefix,
  `Aiur.NativeAIR.prefix_bounded,
  `Aiur.NativeAIR.Graph.Valid.prefix_bounded,
  `Aiur.NativeAIR.Node.eval_defined,
  `Aiur.NativeAIR.sweepFrom_defined,
  `Aiur.NativeAIR.Graph.Valid.sweep_defined,
  `Aiur.NativeAIR.ValidNodes.take,
  `Aiur.NativeAIR.Node.eval_withoutStage2,
  `Aiur.NativeAIR.sweepFrom_withoutStage2,
  `Aiur.NativeAIR.sweepFrom_append,
  `Aiur.NativeAIR.sweepFrom_preserves,
  `Aiur.NativeAIR.Graph.Valid.lookup_sweep_defined,
  `Aiur.NativeAIR.Graph.Valid.lookup_sweep_agrees,
  `Aiur.NativeAIR.Node.unfold_eval,
  `Aiur.NativeAIR.Reflects.push,
  `Aiur.NativeAIR.Node.unfold_defined,
  `Aiur.NativeAIR.unfoldFrom_defined,
  `Aiur.NativeAIR.unfoldFrom_reflects,
  `Aiur.NativeAIR.Graph.Valid.unfold_defined,
  `Aiur.NativeAIR.Graph.sweep_reflects,
  `Aiur.NativeAIR.Reflects.readNodes,
  `Aiur.NativeAIR.Reflects.readLookup,
  `Aiur.NativeAIR.readNodes_congr,
  `Aiur.NativeAIR.readNodes_defined,
  `Aiur.NativeAIR.readLookup_defined,
  `Aiur.NativeAIR.Graph.Valid.lookup_values_agree,
  `Aiur.NativeAIR.Graph.Valid.lookup_values_reflect]

def graphAxiomFreeRoots : Array Lean.Name := #[
  `Aiur.NativeAIR.ValidNodes.take,
  `Aiur.NativeAIR.sweepFrom_append]

def graphPropextRoots : Array Lean.Name := #[
  `Aiur.NativeAIR.Node.check_iff,
  `Aiur.NativeAIR.checkNodes_iff,
  `Aiur.NativeAIR.roots_below_prefix,
  `Aiur.NativeAIR.prefix_bounded,
  `Aiur.NativeAIR.Graph.Valid.prefix_bounded,
  `Aiur.NativeAIR.Node.eval_withoutStage2]

def graphClassicalRoots : Array Lean.Name := #[
  `Aiur.NativeAIR.Reflects.push,
  `Aiur.NativeAIR.unfoldFrom_reflects,
  `Aiur.NativeAIR.Graph.sweep_reflects,
  `Aiur.NativeAIR.Graph.Valid.lookup_values_reflect]

def roots : Array Lean.Name := #[
  `Aiur.G.ofNat_n, `Aiur.G.mul_one, `Aiur.G.mul_zero,
  `Aiur.AIR.inactive_multiplicity_zero,
  `Aiur.AIR.nonzero_multiplicity_active, `Aiur.AIR.active_satisfies,
  `Aiur.Bytecode.Eval.runFunction_sameCode,
  `Aiur.finishCompilation_sameCode, `Aiur.finishCompilation_reflects,
  `Aiur.Source.Toplevel.compile_artifact_of_ok,
  `Aiur.BoundVerifier.build, `Aiur.BoundVerifier.verify_success,
  `Aiur.BoundVerifier.Backend.compilation_stages,
  `Aiur.CompiledToplevel.groupFunctions_preserves_code,
  `Aiur.CompiledToplevel.groupFunctions_sameCode,
  `Aiur.CompiledToplevel.groupFunctions_preserves_execution,
  `Aiur.BoundVerifier.Backend.reference_execution,
  `Aiur.BoundVerifier.Backend.execution_reflects,
  `Aiur.Bytecode.Ctrl.beq_eq_true_iff,
  `Aiur.Bytecode.Block.beq_eq_true_iff,
  `Aiur.Bytecode.Eval.runFunction_renamed_iff,
  `Aiur.Bytecode.Eval.deduplicate_preserves_execution,
  `Aiur.finishCompilation_preserves_execution,
  `Aiur.finishCompilation_nameMap_image,
  `Aiur.BoundVerifier.Backend.execution_reflects_raw,
  `Aiur.Source.Eval.interp_restoreTailMatches,
  `Aiur.Source.Eval.interp_wrapLets,
  `Aiur.Source.Eval.evalFrames_append,
  `Aiur.Source.Eval.interp_peelLets,
  `Aiur.Source.Eval.interp_ret_wrapLets,
  `Aiur.Source.Eval.interp_ioWrite_sequence,
  `Aiur.Source.Eval.interp_debug_sequence,
  `Aiur.Source.Eval.interp_assertEq_sequence,
  `Aiur.Source.Eval.interp_ioSetInfo_sequence,
  `Aiur.Source.Eval.interp_app_mode,
  `Aiur.AIR.memoryPointerCycle_valid,
  `Aiur.AIR.memoryPointerCycle_inconsistent] ++ callOrderRoots ++ lookupRoots ++ executionRoots ++ memoryRoots ++
    fieldRoots ++ localConstraintRoots ++ byteArithmeticRoots ++ byteLookupRoots ++
    lookupMessageRoots ++ lookupShapeRoots ++ globalLookupRoots ++ lookupBudgetRoots ++
    selectorControlRoots ++ operationRowRoots ++ blockRowRoots ++ querySlotRoots ++ circuitRowRoots ++
    rowCountRoots ++ circuitTableRoots ++ branchlessRoots ++ circuitTraceRoots ++ circuitMembershipRoots ++ lookupLayoutRoots ++ memoryColumnRoots ++ byteColumnRoots ++ expressionGraphRoots

def premises : Array Lean.Name := #[
  `Aiur.AIR.activityConstraint,
  `Aiur.Bytecode.Eval.SameCode.mk,
  `Aiur.finishCompilation,
  `Aiur.BoundVerifier.Selection.mk,
  `Aiur.BoundVerifier.Selection.compile,
  `Aiur.BoundVerifier.Selection.system,
  `Aiur.BoundVerifier.Backend.mk,
  `Aiur.BoundVerifier.verify,
  `Aiur.CompiledToplevel.groupFunctions,
  `Aiur.AIR.callRankBound, `Aiur.AIR.packRank, `Aiur.AIR.callOrderConstraint,
  `Aiur.Concrete.Bytecode.LayoutMState.new, `Aiur.Concrete.Bytecode.opLayout,
  `Aiur.AIR.suppliedWeight, `Aiur.AIR.ExactLookupBalance,
  `Aiur.AIR.byteRangeMessage, `Aiur.AIR.byteRangeProviders, `Aiur.AIR.rankByteQueries,
  `Aiur.Bytecode.instBEqCtrl, `Aiur.Bytecode.instBEqBlock,
  `Aiur.Bytecode.instHashableCtrl, `Aiur.Bytecode.instHashableBlock,
  `Aiur.Bytecode.Eval.RenamedCode.mk,
  `Aiur.Bytecode.boundedRenaming, `Aiur.Bytecode.validatesRenaming,
  `Aiur.Bytecode.checkedRenaming, `Aiur.Bytecode.Toplevel.deduplicate,
  `Aiur.Bytecode.Toplevel.deduplicateCandidate,
  `Aiur.Source.Term.restoreTailMatches, `Aiur.instHashableValue,
  `Aiur.Source.Term.hoistLets, `Aiur.Source.Term.bindArguments, `Aiur.Source.Toplevel.inlineCalls,
  `Aiur.Bytecode.AIR.Memory, `Aiur.Bytecode.AIR.Call.mk, `Aiur.Bytecode.AIR.primitive,
  `Aiur.Bytecode.AIR.readValues, `Aiur.Bytecode.AIR.packWord, `Aiur.Bytecode.AIR.adviceOfSize,
  `Aiur.Bytecode.AIR.unaryByte, `Aiur.Bytecode.AIR.binaryByte,
  `Aiur.Bytecode.AIR.pairValues, `Aiur.Bytecode.AIR.readWord,
  `Aiur.Bytecode.AIR.Step.primitive, `Aiur.Bytecode.AIR.Step.call,
  `Aiur.Bytecode.AIR.Step.store, `Aiur.Bytecode.AIR.Step.load,
  `Aiur.Bytecode.AIR.RunOps.nil, `Aiur.Bytecode.AIR.RunOps.cons,
  `Aiur.Bytecode.AIR.SelectArm.case, `Aiur.Bytecode.AIR.SelectArm.fallback,
  `Aiur.Bytecode.AIR.RunBlock.block,
  `Aiur.Bytecode.AIR.RunCtrl.returned, `Aiur.Bytecode.AIR.RunCtrl.yielded,
  `Aiur.Bytecode.AIR.RunCtrl.match, `Aiur.Bytecode.AIR.RunCtrl.matchContinueReturn,
  `Aiur.Bytecode.AIR.RunCtrl.matchContinueYield,
  `Aiur.Bytecode.AIR.RunFunction.function, `Aiur.Bytecode.AIR.Execution.function,
  `Aiur.AIR.FunctionRow.mk, `Aiur.AIR.FunctionRow.Valid.mk,
  `Aiur.AIR.FunctionRow.requests, `Aiur.AIR.FunctionRow.byteQueries,
  `Aiur.AIR.functionProviders, `Aiur.AIR.functionQueries, `Aiur.AIR.functionByteQueries,
  `Aiur.AIR.MemoryRow.mk, `Aiur.AIR.memoryActivityTransition,
  `Aiur.AIR.memoryPointerTransition, `Aiur.AIR.MemoryRowsValid.mk,
  `Aiur.AIR.memoryFacts, `Aiur.AIR.memoryProviders, `Aiur.AIR.memoryPointerCycle,
  `Aiur.GoldilocksProof.squareMod, `Aiur.AIR.booleanConstraint,
  `Aiur.AIR.oneSubBooleanConstraint, `Aiur.AIR.selectorSum,
  `Aiur.AIR.MemoryRowsPolynomials.mk,
  `Aiur.AIR.inverse256, `Aiur.AIR.pack4, `Aiur.AIR.pack4Nat,
  `Aiur.AIR.carryStep, `Aiur.AIR.u32Carries,
  `Aiur.AIR.Byte1Kind.all, `Aiur.AIR.Byte1Kind.channel, `Aiur.AIR.Byte1Kind.result,
  `Aiur.AIR.byte1Outputs, `Aiur.AIR.byte1Request, `Aiur.AIR.byte1Providers,
  `Aiur.AIR.Byte1Kind.op,
  `Aiur.AIR.Byte2Kind.all, `Aiur.AIR.Byte2Kind.channel, `Aiur.AIR.Byte2Kind.result,
  `Aiur.AIR.byte2Outputs, `Aiur.AIR.byte2Request, `Aiur.AIR.byte2Providers,
  `Aiur.AIR.Byte2Kind.op, `Aiur.AIR.Byte2Kind.extendOutputs,
  `Aiur.AIR.byte1Preprocessed, `Aiur.AIR.byte2Preprocessed,
  `Aiur.AIR.padMessage, `Aiur.AIR.HasMessageShape, `Aiur.AIR.mapProviders,
  `Aiur.AIR.PaddedLookupBalance, `Aiur.AIR.functionMessage, `Aiur.AIR.memoryMessage,
  `Aiur.AIR.Byte1Kind.outputSize, `Aiur.AIR.Byte2Kind.outputSize,
  `Aiur.AIR.lookupMessageWidth, `Aiur.AIR.FunctionMessageValid,
  `Aiur.Bytecode.Ctrl.returnsHaveSize, `Aiur.Bytecode.Block.returnsHaveSize,
  `Aiur.Bytecode.Op.lookupShape, `Aiur.Bytecode.Ctrl.lookupShapes,
  `Aiur.Bytecode.Block.lookupShapes, `Aiur.Bytecode.Toplevel.validateLookupShapes,
  `Aiur.Bytecode.Toplevel.validClaimShape, `Aiur.Bytecode.AIR.Call.LookupShape,
  `Aiur.Bytecode.AIR.Outcome.ReturnSize,
  `Aiur.AIR.LookupTables.mk, `Aiur.AIR.LookupTables.providers,
  `Aiur.AIR.GlobalLookups.mk, `Aiur.AIR.rangeMessage,
  `Aiur.lookupSlotSum, `Aiur.lookupQueryBoundAux, `Aiur.lookupQueryBound,
  `Aiur.AIR.addMessages, `Aiur.AIR.scaleMessage, `Aiur.AIR.weightedMessage,
  `Aiur.AIR.gateMessage, `Aiur.AIR.slotMessage,
  `Aiur.AIR.SelectorFlow.mk, `Aiur.AIR.SelectorFlow.guard,
  `Aiur.AIR.SelectorFlow.join, `Aiur.AIR.SelectorFlow.continue,
  `Aiur.AIR.SelectorFlow.Satisfied, `Aiur.AIR.SelectorFlow.Sound.mk,
  `Aiur.Bytecode.Ctrl.selectorFlow, `Aiur.Bytecode.Block.selectorFlow,
  `Aiur.Bytecode.branchSelectorFlows, `Aiur.Bytecode.Ctrl.returnGates,
  `Aiur.Bytecode.Block.returnGates, `Aiur.Bytecode.branchReturnGates,
  `Aiur.AIR.RowValue.mk, `Aiur.AIR.RowValue.variable, `Aiur.AIR.RowValue.konst,
  `Aiur.AIR.rowValues, `Aiur.AIR.RowValue.add, `Aiur.AIR.RowValue.sub,
  `Aiur.AIR.RowValue.mul, `Aiur.AIR.rowAdvice, `Aiur.AIR.RowValue.pack,
  `Aiur.AIR.readRowWord, `Aiur.AIR.OpEmission.mk, `Aiur.AIR.emitAdvice,
  `Aiur.AIR.emitByte1, `Aiur.AIR.Byte2Kind.extendRowOutputs, `Aiur.AIR.emitByte2,
  `Aiur.AIR.range4Queries, `Aiur.AIR.emitU32LessThan, `Aiur.AIR.emitU32Add,
  `Aiur.AIR.emitOp, `Aiur.AIR.OpsEmission.mk, `Aiur.AIR.emitOps,
  `Aiur.AIR.CallsEmitted, `Aiur.Bytecode.MatchPolynomials.mk,
  `Aiur.AIR.RowContext.mk, `Aiur.AIR.QueryPart.mk, `Aiur.AIR.queryParts,
  `Aiur.AIR.BlockEmission.mk, `Aiur.AIR.BlockEmission.prefix,
  `Aiur.AIR.BlockEmission.afterOps, `Aiur.AIR.joinBlockEmissions,
  `Aiur.AIR.mergeEquations, `Aiur.AIR.BlockEmission.continued,
  `Aiur.Bytecode.Ctrl.emitRow, `Aiur.Bytecode.Block.emitRow,
  `Aiur.AIR.SelectorFlow.unguard, `Aiur.AIR.EmissionProjection.mk,
  `Aiur.Bytecode.caseRow, `Aiur.Bytecode.defaultRow, `Aiur.Bytecode.branchRows,
  `Aiur.Bytecode.continueRow, `Aiur.AIR.BlockEmission.QueriesIn,
  `Aiur.AIR.BlockEmission.CallsAt, `Aiur.AIR.BlockEmission.TerminalAt,
  `Aiur.AIR.EmissionIncluded.mk, `Aiur.Bytecode.Ctrl.rowBounds,
  `Aiur.Bytecode.Block.rowBounds, `Aiur.AIR.BlockEmission.HasQuery,
  `Aiur.AIR.BlockEmission.TracksCalls, `Aiur.AIR.RowInputs,
  `Aiur.AIR.InputPreservation.mk, `Aiur.Bytecode.Function.emitRow,
  `Aiur.AIR.gateCount, `Aiur.AIR.queryCount, `Aiur.AIR.QuerySlots.mk,
  `Aiur.AIR.activeQuerySlot, `Aiur.AIR.querySlotParts, `Aiur.AIR.querySlotMultiplicity,
  `Aiur.AIR.decodedQuery, `Aiur.AIR.encodedQuery, `Aiur.AIR.decodedQueries,
  `Aiur.AIR.encodedQueries, `Aiur.AIR.blockQueryPool,
  `Aiur.AIR.MemberEmission.mk, `Aiur.AIR.MemberEmission.selector, `Aiur.AIR.MemberEmission.entry,
  `Aiur.AIR.emitMember, `Aiur.AIR.emitMembers, `Aiur.AIR.CircuitEmission.mk,
  `Aiur.AIR.circuitRankBytes, `Aiur.AIR.circuitEmission, `Aiur.AIR.CircuitEmission.lookup,
  `Aiur.Bytecode.Circuit.emitRow, `Aiur.AIR.MemberEmission.FromProgram.mk,
  `Aiur.AIR.CircuitEmission.QueriesIn, `Aiur.AIR.circuitQueryPool,
  `Aiur.Bytecode.FunctionLayout.width,
  `Aiur.Bytecode.ControlCounts.mk, `Aiur.Bytecode.ControlCounts.sum,
  `Aiur.Bytecode.ControlCounts.branch, `Aiur.Bytecode.ControlCounts.continue,
  `Aiur.Bytecode.Ctrl.controlCounts, `Aiur.Bytecode.Block.controlCounts,
  `Aiur.Bytecode.branchControlCounts, `Aiur.Bytecode.Circuit.validateRowCounts,
  `Aiur.Bytecode.Toplevel.validateRowCounts, `Aiur.Bytecode.ControlCounts.Describes.mk,
  `Aiur.BoundVerifier.build,
  `Aiur.AIR.Provider.PaddedEq, `Aiur.AIR.CircuitEmission.provider,
  `Aiur.AIR.AuxiliaryTables.mk, `Aiur.AIR.AuxiliaryTables.withFunctions,
  `Aiur.AIR.AuxiliaryTables.providers, `Aiur.AIR.AuxiliaryTables.circuitProviders,
  `Aiur.AIR.circuitProviders, `Aiur.AIR.FunctionRow.Provides,
  `Aiur.AIR.FunctionRow.inactive, `Aiur.AIR.FunctionRow.QueriesIn,
  `Aiur.AIR.CircuitWitness.mk, `Aiur.AIR.CircuitWitness.Emitted,
  `Aiur.AIR.CircuitWitness.Satisfied, `Aiur.AIR.CircuitWitness.Shapes,
  `Aiur.AIR.CircuitWitness.LookupBounds,
  `Aiur.Bytecode.Function.hasTerminalControl, `Aiur.Bytecode.circuitBranchless,
  `Aiur.AIR.unitQuerySelectors, `Aiur.AIR.QueryWriters,
  `Aiur.AIR.encodedCircuitQueryPool,
  `Aiur.AIR.CircuitTraces.nil, `Aiur.AIR.CircuitTraces.inactive, `Aiur.AIR.CircuitTraces.active,
  `Aiur.AIR.CircuitTraces.bitmap, `Aiur.AIR.CircuitTraces.degrees, `Aiur.AIR.CircuitTraces.capacity,
  `Aiur.AIR.emitCircuitWitness, `Aiur.AIR.CircuitTraces.emitWitnesses,
  `Aiur.Bytecode.Toplevel.singletonCircuits,
  `Aiur.Bytecode.MembersConstrained, `Aiur.Bytecode.CircuitsConstrained,
  `Aiur.Bytecode.Op.lookupUsage,
  `Aiur.Bytecode.Ctrl.lookupUsage,
  `Aiur.Bytecode.Block.lookupUsage,
  `Aiur.Bytecode.branchLookupUsage,
  `Aiur.Bytecode.Function.LookupLayout,
  `Aiur.Bytecode.FunctionsLookupLayout,
  `Aiur.Bytecode.MembersLookupBound,
  `Aiur.Bytecode.CircuitsLookupBound,
  `Aiur.AIR.MemoryColumns,
  `Aiur.AIR.decodeMemoryRow,
  `Aiur.AIR.memoryColumnEquations,
  `Aiur.AIR.memoryColumnLookup,
  `Aiur.AIR.memoryColumnProvider,
  `Aiur.AIR.memoryNextIndex,
  `Aiur.AIR.memoryMatrixEquations,
  `Aiur.AIR.MemoryMatrixSatisfied,
  `Aiur.AIR.decodeMemoryRows,
  `Aiur.AIR.memoryMatrixProviders,
  `Aiur.AIR.MemoryTraces.nil, `Aiur.AIR.MemoryTraces.inactive, `Aiur.AIR.MemoryTraces.active,
  `Aiur.AIR.MemoryTraces.bitmap,
  `Aiur.AIR.MemoryTraces.degrees,
  `Aiur.AIR.MemoryTraces.capacity,
  `Aiur.AIR.MemoryTraces.rows,
  `Aiur.AIR.MemoryTraces.providers,
  `Aiur.AIR.MemoryTraces.Satisfied,
  `Aiur.AIR.memoryTableProviders,
  `Aiur.AIR.MemoryTraces.auxiliary,
  `Aiur.fixedTraceHeights,
  `Aiur.FixedTraceHeights.nil,
  `Aiur.FixedTraceHeights.inactive,
  `Aiur.FixedTraceHeights.active,
  `Aiur.AIR.Byte1Columns,
  `Aiur.AIR.Byte2Columns,
  `Aiur.AIR.Byte1Kind.column,
  `Aiur.AIR.Byte2Kind.column,
  `Aiur.AIR.byte1PreprocessedColumns,
  `Aiur.AIR.byte2PreprocessedColumns,
  `Aiur.AIR.byte1ColumnLookup,
  `Aiur.AIR.byte2ColumnLookup,
  `Aiur.AIR.byte1ColumnProvider,
  `Aiur.AIR.byte2ColumnProvider,
  `Aiur.AIR.byte1MatrixProviders,
  `Aiur.AIR.byte2MatrixProviders,
  `Aiur.AIR.ByteTraces.mk,
  `Aiur.AIR.ByteTraces.providers,
  `Aiur.AIR.ByteTraces.byte1Weights,
  `Aiur.AIR.ByteTraces.byte2Weights,
  `Aiur.AIR.SystemTraces.mk,
  `Aiur.AIR.SystemTraces.bitmap,
  `Aiur.AIR.SystemTraces.degrees,
  `Aiur.AIR.SystemTraces.queryBound,
  `Aiur.AIR.SystemTraces.providers,
  `Aiur.AIR.systemFixedHeights,
  `Aiur.AIR.systemLookupSlots,
  `Aiur.NativeAIR.Source.preprocessed,
  `Aiur.NativeAIR.Source.main,
  `Aiur.NativeAIR.Source.stage2,
  `Aiur.NativeAIR.RowOffset.current,
  `Aiur.NativeAIR.RowOffset.next,
  `Aiur.NativeAIR.ColRef.mk,
  `Aiur.NativeAIR.Node.konst,
  `Aiur.NativeAIR.Node.var,
  `Aiur.NativeAIR.Node.publicInput,
  `Aiur.NativeAIR.Node.isFirstRow,
  `Aiur.NativeAIR.Node.isLastRow,
  `Aiur.NativeAIR.Node.isTransition,
  `Aiur.NativeAIR.Node.add,
  `Aiur.NativeAIR.Node.sub,
  `Aiur.NativeAIR.Node.mul,
  `Aiur.NativeAIR.Node.neg,
  `Aiur.NativeAIR.GraphWidths.mk,
  `Aiur.NativeAIR.GraphWidths.width,
  `Aiur.NativeAIR.Lookup.mk,
  `Aiur.NativeAIR.Graph.mk,
  `Aiur.NativeAIR.Lookup.roots,
  `Aiur.NativeAIR.Graph.lookupRoots,
  `Aiur.NativeAIR.Graph.lookupPrefix,
  `Aiur.NativeAIR.Node.Valid,
  `Aiur.NativeAIR.Node.check,
  `Aiur.NativeAIR.checkNodes,
  `Aiur.NativeAIR.ValidNodes.nil,
  `Aiur.NativeAIR.ValidNodes.cons,
  `Aiur.NativeAIR.checkedGraphPrefix,
  `Aiur.NativeAIR.Graph.Valid.mk,
  `Aiur.NativeAIR.EvalOps.mk,
  `Aiur.NativeAIR.Values.mk,
  `Aiur.NativeAIR.Values.Fits,
  `Aiur.NativeAIR.Node.eval,
  `Aiur.NativeAIR.sweepFrom,
  `Aiur.NativeAIR.Graph.sweep,
  `Aiur.NativeAIR.Values.withoutStage2,
  `Aiur.NativeAIR.Graph.sweepLookupPrefix,
  `Aiur.NativeAIR.Expr.konst,
  `Aiur.NativeAIR.Expr.var,
  `Aiur.NativeAIR.Expr.publicInput,
  `Aiur.NativeAIR.Expr.isFirstRow,
  `Aiur.NativeAIR.Expr.isLastRow,
  `Aiur.NativeAIR.Expr.isTransition,
  `Aiur.NativeAIR.Expr.add,
  `Aiur.NativeAIR.Expr.sub,
  `Aiur.NativeAIR.Expr.mul,
  `Aiur.NativeAIR.Expr.neg,
  `Aiur.NativeAIR.Expr.eval,
  `Aiur.NativeAIR.Node.unfold,
  `Aiur.NativeAIR.Reflects,
  `Aiur.NativeAIR.unfoldFrom,
  `Aiur.NativeAIR.Graph.unfold,
  `Aiur.NativeAIR.readNodes,
  `Aiur.NativeAIR.evalRoots,
  `Aiur.NativeAIR.readLookup,
  `Aiur.NativeAIR.evalLookup,
  `Aiur.NativeAIR.goldilocksOps]

private def constants (info : Lean.ConstantInfo) : Array Lean.Name :=
  info.type.getUsedConstants ++ match info with
  | .thmInfo value => value.value.getUsedConstants
  | .defnInfo value => value.value.getUsedConstants
  | .opaqueInfo value => value.value.getUsedConstants
  | .inductInfo value => value.ctors.toArray
  | _ => #[]

private partial def closure (env : Lean.Environment) (runtime : Bool) (pending : List Lean.Name)
    (seen : NameSet := {}) : NameSet :=
  match pending with
  | [] => seen
  | name :: rest =>
    if seen.contains name then closure env runtime rest seen
    else match env.checked.get.find? name with
    | none => closure env runtime rest (seen.insert name)
    | some info =>
      let extras := if runtime then Id.run do
        let mut names := #[]
        let worker := Lean.Compiler.mkUnsafeRecName name
        if (env.checked.get.find? worker).isSome then names := names.push worker
        if let some other := Lean.Compiler.getImplementedBy? env name then
          names := names.push other
        if let some other := (Lean.Compiler.CSimp.ext.getState env).map.find? name then
          names := names.push other.toDeclName
        return names
      else #[]
      closure env runtime ((constants info ++ extras).toList ++ rest) (seen.insert name)

private def projectConstant (env : Lean.Environment) (name : Lean.Name) : Bool :=
  match env.getModuleIdxFor? name with
  | none => false
  | some idx => (`Ix).isPrefixOf env.allImportedModuleNames[idx.toNat]!

private def sortedNames (names : Array Name) : Array Name := names.qsort Name.lt

/-- Read checked types, bodies and constructors; imported cached axiom
summaries can omit constructor dependencies. -/
private def checkAxioms (env : Environment) (root : Name) (expected : Array Name) :
    CommandElabM (Array Name) := do
  let reachable := closure env false [root]
  let mut actual := #[]
  for name in reachable do
    let some info := env.checked.get.find? name
      | throwError "C8 component has an unavailable checked dependency: {name}"
    if info.isAxiom then actual := actual.push name
  let sorted := sortedNames actual
  unless sorted == sortedNames expected do
    throwError "C8 axiom boundary changed for {root}: expected {sortedNames expected}, actual {sorted}"
  return sorted

-- Constructor closure and exact-set failure paths are part of the audit.
private inductive ConstructorAuditFixture where
  | plain
  | withProof (proof : propext (Iff.refl True) = rfl)

run_cmd do
  let _ ← checkAxioms (← getEnv) ``ConstructorAuditFixture.plain #[``propext]
  let _ ← checkAxioms (← getEnv) ``Eq.refl #[]

/-- error: C8 axiom boundary changed for Eq.refl: expected [propext], actual [] -/
#guard_msgs in
run_cmd do
  let _ ← checkAxioms (← getEnv) ``Eq.refl #[``propext]

/-- error: C8 axiom boundary changed for propext: expected [], actual [propext] -/
#guard_msgs in
run_cmd do
  let _ ← checkAxioms (← getEnv) ``propext #[]

end Aiur.Proofs.Audit

open Aiur.Proofs.Audit in
run_cmd do
  let env ← getEnv
  for root in roots do
    let some info := env.checked.get.find? root | throwError "C8 component audit: missing root {root}"
    let expected := if graphAxiomFreeRoots.contains root then #[]
      else if graphPropextRoots.contains root || (roots.extract 0 6).contains root ||
        #[`Aiur.G.n_ofNat, `Aiur.G.n_add, `Aiur.G.n_mul, `Aiur.G.zero_add,
          `Aiur.AIR.suppliedWeight_nonzero_provider, `Aiur.AIR.inverse256_correct,
          `Aiur.AIR.byte1Request_shape, `Aiur.AIR.byte2Request_shape,
          `Aiur.AIR.functionMessage_injective, `Aiur.AIR.memoryMessage_injective,
          `Aiur.AIR.decodedQueries_length,
          `Aiur.AIR.encodedQueries_length,
          `Aiur.AIR.slotMessage_member_length,
          `Aiur.AIR.suppliedWeight_padded_congr,
          `Aiur.AIR.PaddedLookupBalance.congr_providers,
          `Aiur.FixedTraceHeights.alignment,
          `Aiur.AIR.PaddedLookupBalance.congr_queries].contains root
      then #[``propext]
      else if (expressionGraphRoots.contains root && !graphClassicalRoots.contains root) ||
          callOrderRoots.contains root || lookupRoots.contains root ||
          executionRoots.contains root || memoryRoots.contains root ||
          #[`Aiur.AIR.selectorSum_characteristic_cancel, `Aiur.AIR.active_case,
            `Aiur.AIR.active_default, `Aiur.AIR.byte_add_carry, `Aiur.AIR.byte_sub_borrow,
            `Aiur.AIR.byte_carry_relation, `Aiur.AIR.pack4_n,
            `Aiur.AIR.exactLookupBalance_byte1, `Aiur.AIR.exactLookupBalance_byte2,
            `Aiur.AIR.exactLookupBalance_byte1_step, `Aiur.AIR.exactLookupBalance_byte2_step,
            `Aiur.AIR.padMessage_injective_of_shape, `Aiur.AIR.ExactLookupBalance.filter,
            `Aiur.AIR.paddedLookupBalance_provider, `Aiur.AIR.padMessage_append_zero,
            `Aiur.AIR.functionMessage_rank_alias,
            `Aiur.AIR.GlobalLookups.byte1, `Aiur.AIR.GlobalLookups.byte2,
            `Aiur.AIR.GlobalLookups.byte1_step, `Aiur.AIR.GlobalLookups.byte2_step,
            `Aiur.AIR.GlobalLookups.rank_bytes, `Aiur.BoundVerifier.claim_padding,
            `Aiur.lookupQueryBound_sound, `Aiur.lookupQueryBound_consumer_count,
            `Aiur.AIR.CircuitTraces.slot_sum_append, `Aiur.AIR.CircuitTraces.capacity_bounded,
            `Aiur.AIR.decodeMemoryRow_width, `Aiur.AIR.decodeMemoryRows_size,
            `Aiur.AIR.MemoryTraces.slot_sum_append, `Aiur.AIR.MemoryTraces.rows_size_le,
            `Aiur.AIR.MemoryTraces.capacity_bounded,
            `Aiur.fixedTraceHeights_sound, `Aiur.fixedTraceHeights_complete,
            `Aiur.AIR.byte2ColumnProvider_reflect, `Aiur.AIR.suppliedWeight_perm,
            `Aiur.AIR.PaddedLookupBalance.perm_providers, `Aiur.AIR.flatMap_map_swap,
            `Aiur.AIR.byte2MatrixProviders_reflect,
            `Aiur.AIR.encodedCircuitQueryPool_uniform_bound,
            `Aiur.lookupQueryBound_shape, `Aiur.lookupQueryBound_complete,
            `Aiur.lookupSlotSum_bounded, `Aiur.lookupQueryBound_encodedKey,
            `Aiur.AIR.GlobalLookups.of_budget,
            `Aiur.AIR.emitOp_calls, `Aiur.AIR.emitOps_calls,
            `Aiur.AIR.emitOp_lookupUsage, `Aiur.AIR.emitOps_lookupUsage,
            `Aiur.AIR.AuxiliaryTables.global_of_circuit_balance,
            `Aiur.AIR.FunctionRow.inactive_valid,
            `Aiur.AIR.CallsEmitted.ordered, `Aiur.AIR.active_array_equality,
            `Aiur.AIR.QuerySlots.active_singleton].contains root
        then #[``propext, ``Quot.sound]
      else #[``propext, ``Classical.choice, ``Quot.sound]
    let axioms ← checkAxioms env root expected
    liftTermElabM do logInfo m!"ROOT {root}\n{← Meta.ppExpr info.type}\nAXIOMS {axioms}"
  for name in premises do
    let some info := env.checked.get.find? name | throwError "C8 component audit: missing premise {name}"
    liftTermElabM do
      logInfo m!"PREMISE {name}\n{← Meta.ppExpr info.type}"
      if let .defnInfo value := info then logInfo m!"DEFINITION\n{← Meta.ppExpr value.value}"
  let logical := closure env false roots.toList
  -- Also follow compiler workers and replacements transitively. They need
  -- not occur in the logical body, especially for partial opaque functions.
  let reachable := (closure env true roots.toList).toList.mergeSort (fun a b => a.toString < b.toString)
  let mut workers : Array Lean.Name := #[]
  let mut partials : Array Lean.Name := #[]
  let mut externs : Array Lean.Name := #[]
  let mut replacements : Array (Lean.Name × Lean.Name) := #[]
  let mut runtime : Array Lean.Name := #[]
  for name in reachable do
    unless (env.checked.get.find? name).isSome do
      throwError "C8 component has an unavailable checked runtime dependency: {name}"
    if projectConstant env name then
      if let some parent := Lean.Compiler.isUnsafeRecName? name then
        match env.checked.get.find? parent with
        | some (.defnInfo original) =>
          unless original.safety == .safe do
            throwError "C8 recursion worker source is not safe: {name}"
        | some (.opaqueInfo original) =>
          if original.isUnsafe then throwError "C8 recursion worker source is unsafe: {name}"
          partials := partials.push parent
        | _ => throwError "C8 recursion worker has no source definition: {name}"
        workers := workers.push name
      if Lean.isExtern env name then externs := externs.push name
      if let some other := Lean.Compiler.getImplementedBy? env name then
        replacements := replacements.push (name, other)
      if let some other := (Lean.Compiler.CSimp.ext.getState env).map.find? name then
        replacements := replacements.push (name, other.toDeclName)
      if let some (.defnInfo definition) := env.checked.get.find? name then
        unless definition.safety == .safe || (Lean.Compiler.isUnsafeRecName? name).isSome do
          runtime := runtime.push name
      if let some (.opaqueInfo definition) := env.checked.get.find? name then
        if definition.isUnsafe then runtime := runtime.push name
      if Lean.Elab.ComputedFields.computedFieldAttr.hasTag env name then
        throwError "C8 component has an unreviewed computed field: {name}"
  unless externs == #[`Aiur.AiurSystem.build, `Aiur.AiurSystem.verify,
      `Aiur.AiurSystem.vkBytes, `Aiur.Proof.ofBytesChecked] do
    throwError "C8 component runtime extern inventory changed: {externs}"
  unless replacements.isEmpty do throwError "C8 component runtime replacements changed: {replacements}"
  unless runtime.isEmpty do throwError "C8 component has an unreviewed unsafe runtime: {runtime}"
  unless partials == #[`Aiur.instHashableTyp.hash,
      `Aiur.instReprPattern.repr, `Aiur.instReprTyp.repr] do
    throwError "C8 component partial opaque inventory changed: {partials}"
  if reachable.contains `Aiur.functionGroupsDisabledImpl then
    throwError "C8 selected program must not depend on the environment grouping override"
  for name in workers.qsort Name.lt do
    let some (.defnInfo value) := env.checked.get.find? name
      | throwError "C8 recursion worker is missing: {name}"
    liftTermElabM do
      logInfo m!"RECURSION WORKER {name}\n{← Meta.ppExpr value.type}\nIMPLEMENTATION\n{← Meta.ppExpr value.value}"
  logInfo m!"C8 component ROOTS {roots.size}; LOGICAL DECLARATIONS {logical.size}; WITH RUNTIME {reachable.length}"
  logInfo m!"IX RUNTIME EXTERNS {externs}\nPARTIAL OPAQUE SOURCES {partials}\nOTHER UNSAFE RUNTIME {runtime}\nRECURSION WORKERS {workers.size}"
  logInfo "Runtime diagnostics cover Ix modules, including private constants. Lean/Std runtime primitives remain an external execution boundary. Partial opaque implementations are inventoried, not proved to refine their logical defaults."
  logInfo "The runtime inventory and theorem premises are frozen separately. These roots do not establish full compiler/AIR reflection or public certified claim semantics."
