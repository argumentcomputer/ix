# Theorem dependency analysis

Generated from `Ix/Aiur/Proofs/*.lean`. Root: `Toplevel.compile_correct`.

## Summary

- **838 theorems** across 17 files.
- **25 red** (own sorry), **27 yellow** (transitive sorry), **786 green** (clean).
- **398 reachable** from `compile_correct` (440 unreached).
- **Total sorry occurrences**: 28.

## Distance from `compile_correct` (forward edges)

| d | count | red | yellow | green |
|---|---|---|---|---|
| 0 | 1 | 0 | 1 | 0 |
| 1 | 7 | 1 | 4 | 2 |
| 2 | 42 | 3 | 7 | 32 |
| 3 | 51 | 3 | 4 | 44 |
| 4 | 55 | 3 | 2 | 50 |
| 5 | 67 | 1 | 1 | 65 |
| 6 | 85 | 1 | 2 | 82 |
| 7 | 42 | 0 | 0 | 42 |
| 8 | 26 | 0 | 0 | 26 |
| 9 | 13 | 0 | 0 | 13 |
| 10 | 9 | 0 | 0 | 9 |

## Sorry hot-spots (by leverage = transitive ancestors that depend on closure)

Closing a high-leverage red unblocks the largest sub-tree of dependents.

| Rank | Theorem | File | LoC | Sorries | Ancestors | d | Reaches root |
|---|---|---|---|---|---|---|---|
| 1 | `FnFreeBody.interp_FnFree` | `ConcretizeSound.lean` | 620 | 2 | 7 | 5 | ✓ |
| 2 | `concretizeDrainEntry_preserves_NewFunctionsFO` | `ConcretizeSound.lean` | 39 | 1 | 6 | 6 | ✓ |
| 3 | `compile_ok_input_layout_matches_entry` | `StructCompatible.lean` | 14 | 1 | 5 | 4 | ✓ |
| 4 | `Simulation.step_R_preservation_applyGlobal` | `Simulation.lean` | 36 | 1 | 5 | 4 | ✓ |
| 5 | `Simulation.ValueR_implies_flatten_eq` | `Simulation.lean` | 116 | 1 | 5 | 4 | ✓ |
| 6 | `Function_body_preservation_succ_fuel` | `LowerSoundControl.lean` | 51 | 1 | 4 | 3 | ✓ |
| 7 | `namespace_preservation_entry` | `CompilerPreservation.lean` | 25 | 1 | 3 | 2 | ✓ |
| 8 | `Toplevel.concretize_produces_refClosed_entry` | `ConcretizeSound.lean` | 34 | 3 | 3 | 3 | ✓ |
| 9 | `concretize_produces_ctorPresent_entry` | `CompilerProgress.lean` | 48 | 1 | 3 | 2 | ✓ |
| 10 | `concretizeBuild_preserves_TermRefsDt` | `ConcretizeSound.lean` | 12 | 1 | 3 | 3 | ✓ |
| 11 | `flatten_agree_entry` | `CompilerPreservation.lean` | 54 | 1 | 3 | 2 | ✓ |
| 12 | `DirectDagBody.spine_transfer` | `ConcretizeSound.lean` | 24 | 1 | 3 | — |   |
| 13 | `concretize_extract_function_at_name` | `ConcretizeSound.lean` | 20 | 1 | 3 | — |   |
| 14 | `Lower.compile_progress_entry` | `CompilerProgress.lean` | 33 | 1 | 2 | 1 | ✓ |
| 15 | `term_compile_delta_letWild_match_continue` | `LowerCalleesFromLayout.lean` | 138 | 1 | 0 | — |   |
| 16 | `Scratch.body_compile_ok` | `Scratch.lean` | 59 | 1 | 0 | — |   |
| 17 | `Scratch.concretize_preserves_entry_inputs` | `Scratch.lean` | 23 | 1 | 0 | — |   |
| 18 | `Scratch.concretize_produces_ctorPresent` | `Scratch.lean` | 16 | 1 | 0 | — |   |
| 19 | `Scratch.flattenValue_slice_at_offset` | `Scratch.lean` | 18 | 1 | 0 | — |   |
| 20 | `Scratch.concretize_preserves_function_kind_fwd` | `Scratch.lean` | 26 | 1 | 0 | — |   |
| 21 | `concretize_under_fullymono_dt_flat_size_agree` | `ConcretizeSound.lean` | 21 | 1 | 0 | — |   |
| 22 | `concretize_preserves_runFunction` | `ConcretizeSound.lean` | 91 | 1 | 0 | — |   |
| 23 | `Scratch.Function_compile_progress` | `Scratch.lean` | 30 | 1 | 0 | — |   |
| 24 | `Scratch.interp_preserves_ValueHasTyp` | `Scratch.lean` | 21 | 1 | 0 | — |   |
| 25 | `Scratch.flattenValue_size_of_ValueHasTyp` | `Scratch.lean` | 292 | 1 | 0 | — |   |

## Sorry depth (forward reach — how much further the proof obligation extends)

| Theorem | Descendants | Red descendants |
|---|---|---|
| `Lower.compile_progress_entry` | 67 | 1 |
| `FnFreeBody.interp_FnFree` | 44 | 0 |
| `term_compile_delta_letWild_match_continue` | 19 | 0 |
| `Scratch.flattenValue_size_of_ValueHasTyp` | 6 | 0 |
| `concretizeDrainEntry_preserves_NewFunctionsFO` | 2 | 0 |
| `Simulation.ValueR_implies_flatten_eq` | 2 | 0 |
| `concretize_preserves_runFunction` | 1 | 0 |
| `concretizeBuild_preserves_TermRefsDt` | 1 | 0 |
| `namespace_preservation_entry` | 0 | 0 |
| `compile_ok_input_layout_matches_entry` | 0 | 0 |
| `Scratch.body_compile_ok` | 0 | 0 |
| `Scratch.concretize_preserves_entry_inputs` | 0 | 0 |
| `Simulation.step_R_preservation_applyGlobal` | 0 | 0 |
| `Scratch.concretize_produces_ctorPresent` | 0 | 0 |
| `Toplevel.concretize_produces_refClosed_entry` | 0 | 0 |
| `Scratch.flattenValue_slice_at_offset` | 0 | 0 |
| `concretize_produces_ctorPresent_entry` | 0 | 0 |
| `Scratch.concretize_preserves_function_kind_fwd` | 0 | 0 |
| `concretize_under_fullymono_dt_flat_size_agree` | 0 | 0 |
| `Scratch.Function_compile_progress` | 0 | 0 |
| `Function_body_preservation_succ_fuel` | 0 | 0 |
| `flatten_agree_entry` | 0 | 0 |
| `DirectDagBody.spine_transfer` | 0 | 0 |
| `Scratch.interp_preserves_ValueHasTyp` | 0 | 0 |
| `concretize_extract_function_at_name` | 0 | 0 |

## Critical reach — red/yellow nodes reachable forward from each red

| Theorem | Reachable red+yellow |
|---|---|
| `FnFreeBody.interp_FnFree` | 3 |
| `Lower.compile_progress_entry` | 2 |
| `namespace_preservation_entry` | 0 |
| `concretizeDrainEntry_preserves_NewFunctionsFO` | 0 |
| `term_compile_delta_letWild_match_continue` | 0 |
| `compile_ok_input_layout_matches_entry` | 0 |
| `Scratch.body_compile_ok` | 0 |
| `Scratch.concretize_preserves_entry_inputs` | 0 |
| `Simulation.step_R_preservation_applyGlobal` | 0 |
| `Scratch.concretize_produces_ctorPresent` | 0 |
| `Toplevel.concretize_produces_refClosed_entry` | 0 |
| `Scratch.flattenValue_slice_at_offset` | 0 |
| `concretize_produces_ctorPresent_entry` | 0 |
| `Scratch.concretize_preserves_function_kind_fwd` | 0 |
| `concretize_under_fullymono_dt_flat_size_agree` | 0 |
| `concretize_preserves_runFunction` | 0 |
| `concretizeBuild_preserves_TermRefsDt` | 0 |
| `Scratch.Function_compile_progress` | 0 |
| `Function_body_preservation_succ_fuel` | 0 |
| `flatten_agree_entry` | 0 |
| `DirectDagBody.spine_transfer` | 0 |
| `Scratch.interp_preserves_ValueHasTyp` | 0 |
| `Simulation.ValueR_implies_flatten_eq` | 0 |
| `Scratch.flattenValue_size_of_ValueHasTyp` | 0 |
| `concretize_extract_function_at_name` | 0 |

## Per-file breakdown

| File | Theorems | Red | Yellow | Sorries | LoC |
|---|---|---|---|---|---|
| `ConcretizeSound.lean` | 251 | 8 | 13 | 11 | 12765 |
| `Scratch.lean` | 154 | 8 | 3 | 8 | 6388 |
| `CompilerPreservation.lean` | 15 | 2 | 4 | 2 | 741 |
| `CompilerProgress.lean` | 58 | 2 | 1 | 2 | 3312 |
| `CompilerCorrect.lean` | 3 | 0 | 3 | 0 | 125 |
| `Simulation.lean` | 13 | 2 | 1 | 2 | 462 |
| `LowerSoundControl.lean` | 3 | 1 | 1 | 1 | 99 |
| `StructCompatible.lean` | 9 | 1 | 1 | 1 | 229 |
| `LowerCalleesFromLayout.lean` | 34 | 1 | 0 | 1 | 3261 |

## Cycles (non-trivial SCCs)

- 3-cycle: `RefClosedBody.DrainState.NewDeclTypesRefsOk.init`, `DrainState.NewFunctionsTermRefsDt.init`, `DrainState.NewFunctionsFO.init`
- 2-cycle: `List.mem_mapM_ok_forall`, `Array.mem_mapM_ok_forall`
- 4-cycle: `FnFreeBody.evalMatchCases_FnFree`, `FnFreeBody.evalList_FnFree`, `FnFreeBody.interp_FnFree`, `FnFreeBody.applyGlobal_FnFree`
- 3-cycle: `expectIdx_delta`, `buildArgs_delta`, `toIndex_delta`
- 3-cycle: `addCase_delta_inlined`, `addCases_fold_delta_inlined`, `term_compile_delta`
- 2-cycle: `Scratch.concretizeDrainEntry_preserves_StrongNewNameShape`, `concretizeDrainEntry_preserves_StrongNewNameShape`
- 2-cycle: `Scratch.concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape`, `concretizeDrainEntry_list_foldlM_preserves_StrongNewNameShape`
- 2-cycle: `Scratch.concretizeDrainIter_preserves_StrongNewNameShape`, `concretizeDrainIter_preserves_StrongNewNameShape`
- 2-cycle: `concretize_drain_preserves_StrongNewNameShape`, `Scratch.concretize_drain_preserves_StrongNewNameShape`
- 2-cycle: `IOBuffer.equiv_trans`, `InterpResultEq.trans`
- 2-cycle: `Scratch.preNameMap_in_range`, `preNameMap_in_range`
- 2-cycle: `compile_ok_funIdx_valid`, `Scratch.compile_ok_funIdx_valid`
- 2-cycle: `Scratch.compile_ok_total_on_reachable`, `compile_ok_total_on_reachable`
- 2-cycle: `needsCircuit_preserves_body`, `Scratch.needsCircuit_preserves_body`
- 2-cycle: `compile_ct_functions_shape`, `Scratch.compile_ct_functions_shape`
- 2-cycle: `list_foldl_attachWith_eq`, `list_foldl_attachWith_eq`
- 2-cycle: `sizeOf_ctrl_lt`, `Block.sizeOf_ctrl_lt`
- 2-cycle: `rewriteBlock_callee_mem_aux`, `rewriteCtrl_callee_mem_aux`
- 2-cycle: `compile_ok_call_graph_closed`, `Scratch.compile_ok_call_graph_closed`
- 2-cycle: `Lower.compile_preservation_entry`, `Toplevel.compile_preservation_entry`
- 2-cycle: `Lower.compile_progress_entry`, `Toplevel.compile_progress_entry`
- 2-cycle: `concretize_produces_refClosed`, `RefClosedBody.concretize_produces_refClosed`
- 2-cycle: `T3Private.blockLayout_preserves_inputSize`, `T3Private.ctrlLayout_preserves_inputSize`
- 2-cycle: `Scratch.InterpResultEq.transport_remap`, `Scratch.ValueEq.transport_remap`

## Red list (compact)

- `DirectDagBody.spine_transfer` (ConcretizeSound.lean, 1× sorry, d=—)
- `FnFreeBody.interp_FnFree` (ConcretizeSound.lean, 2× sorry, d=5)
- `Function_body_preservation_succ_fuel` (LowerSoundControl.lean, 1× sorry, d=3)
- `Lower.compile_progress_entry` (CompilerProgress.lean, 1× sorry, d=1)
- `Scratch.Function_compile_progress` (Scratch.lean, 1× sorry, d=—)
- `Scratch.body_compile_ok` (Scratch.lean, 1× sorry, d=—)
- `Scratch.concretize_preserves_entry_inputs` (Scratch.lean, 1× sorry, d=—)
- `Scratch.concretize_preserves_function_kind_fwd` (Scratch.lean, 1× sorry, d=—)
- `Scratch.concretize_produces_ctorPresent` (Scratch.lean, 1× sorry, d=—)
- `Scratch.flattenValue_size_of_ValueHasTyp` (Scratch.lean, 1× sorry, d=—)
- `Scratch.flattenValue_slice_at_offset` (Scratch.lean, 1× sorry, d=—)
- `Scratch.interp_preserves_ValueHasTyp` (Scratch.lean, 1× sorry, d=—)
- `Simulation.ValueR_implies_flatten_eq` (Simulation.lean, 1× sorry, d=4)
- `Simulation.step_R_preservation_applyGlobal` (Simulation.lean, 1× sorry, d=4)
- `Toplevel.concretize_produces_refClosed_entry` (ConcretizeSound.lean, 3× sorry, d=3)
- `compile_ok_input_layout_matches_entry` (StructCompatible.lean, 1× sorry, d=4)
- `concretizeBuild_preserves_TermRefsDt` (ConcretizeSound.lean, 1× sorry, d=3)
- `concretizeDrainEntry_preserves_NewFunctionsFO` (ConcretizeSound.lean, 1× sorry, d=6)
- `concretize_extract_function_at_name` (ConcretizeSound.lean, 1× sorry, d=—)
- `concretize_preserves_runFunction` (ConcretizeSound.lean, 1× sorry, d=—)
- `concretize_produces_ctorPresent_entry` (CompilerProgress.lean, 1× sorry, d=2)
- `concretize_under_fullymono_dt_flat_size_agree` (ConcretizeSound.lean, 1× sorry, d=—)
- `flatten_agree_entry` (CompilerPreservation.lean, 1× sorry, d=2)
- `namespace_preservation_entry` (CompilerPreservation.lean, 1× sorry, d=2)
- `term_compile_delta_letWild_match_continue` (LowerCalleesFromLayout.lean, 1× sorry, d=—)

## Yellow list (compact)

- `Concrete.Eval.runFunction_preserves_FnFree` (ConcretizeSound.lean, d=2)
- `FnFreeBody.applyGlobal_FnFree` (ConcretizeSound.lean, d=4)
- `FnFreeBody.evalList_FnFree` (ConcretizeSound.lean, d=6)
- `FnFreeBody.evalMatchCases_FnFree` (ConcretizeSound.lean, d=6)
- `Function_body_preservation` (LowerSoundControl.lean, d=2)
- `Lower.compile_preservation_entry` (CompilerPreservation.lean, d=1)
- `Scratch.compile_ok_implies_struct_compatible` (Scratch.lean, d=—)
- `Scratch.compile_ok_input_layout_matches` (Scratch.lean, d=—)
- `Scratch.concretize_extract_concrete_function` (Scratch.lean, d=—)
- `Simulation.concretize_runFunction_simulation` (Simulation.lean, d=3)
- `Toplevel.compile_correct` (CompilerCorrect.lean, d=0)
- `Toplevel.compile_correct_concRetFnFree_entry` (CompilerCorrect.lean, d=1)
- `Toplevel.compile_preservation_entry` (CompilerPreservation.lean, d=1)
- `Toplevel.compile_progress_entry` (CompilerProgress.lean, d=1)
- `Toplevel.concretize_refClosed_entry` (CompilerCorrect.lean, d=2)
- `compile_ok_implies_struct_compatible_entry` (CompilerPreservation.lean, d=2)
- `compile_ok_implies_struct_compatible_of_entry` (StructCompatible.lean, d=3)
- `concretizeDrainEntry_list_foldlM_preserves_NewFunctionsFO` (ConcretizeSound.lean, d=5)
- `concretizeDrainIter_preserves_NewFunctionsFO` (ConcretizeSound.lean, d=4)
- `concretize_drain_preserves_NewFunctionsFO` (ConcretizeSound.lean, d=3)
- `concretize_layoutMap_progress` (ConcretizeSound.lean, d=—)
- `concretize_preserves_FirstOrderReturn` (ConcretizeSound.lean, d=2)
- `concretize_preserves_TermRefsDt` (ConcretizeSound.lean, d=2)
- `concretize_preserves_direct_dag` (ConcretizeSound.lean, d=—)
- `concretize_preserves_runFunction_entry` (CompilerPreservation.lean, d=2)
- `concretize_produces_sizeBoundOk` (ConcretizeSound.lean, d=—)
- `runFunction_preserves_FnFree_body` (ConcretizeSound.lean, d=3)
