/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.GraphLookupTraces

/-! Physical memory and byte graph lookups have the provider interpretation
used by the single global pool. Byte preprocessing is the canonical fixed
matrix; binding the committed preprocessing to this matrix is a separate
PCS obligation. -/

namespace Aiur.NativeAIR
open AIR Compiler OpEmitter

def graphLookupProvider (lookup : G × List G) : Provider (List G) := (lookup.2, 0 - lookup.1)

def graphTableProviders (rows : List LookupRow) : List (Provider (List G)) :=
  rows.flatMap fun row => row.map graphLookupProvider

theorem graphTableProviders_append (first rest : List LookupRow) :
    graphTableProviders (first ++ rest) = graphTableProviders first ++ graphTableProviders rest :=
  List.flatMap_append

theorem graphLookupProvider_memory (width : Nat) (columns : MemoryColumns width) :
    graphLookupProvider (memoryColumnLookup width columns) = memoryColumnProvider width columns := by
  simp only [graphLookupProvider, memoryColumnProvider, memoryColumnLookup, G.neg_neg]

theorem graphTableProviders_memory (width height : Nat) (matrix : Fin height → MemoryColumns width) :
    graphTableProviders (List.ofFn fun index => [memoryColumnLookup width (matrix index)]) =
      memoryMatrixProviders width height matrix := by
  induction height with
  | zero => rfl
  | succ height ih =>
    simp only [graphTableProviders, List.ofFn_succ, List.flatMap_cons, List.map_cons, List.map_nil,
      List.singleton_append, memoryMatrixProviders, graphLookupProvider_memory]
    exact congrArg (_ :: ·) (ih (fun index => matrix index.succ))

theorem CompiledKey.memoryCircuit_matrix_lookups {logBlowup width : Nat} {artifact : KeyCodec.Circuit}
    (built : CompiledKey.memoryCircuit logBlowup width = some artifact) {height : Nat}
    (matrix : Fin height → MemoryColumns width) :
    artifact.graph.readTraceLookups artifact.widths (finiteTraceMatrix matrix) =
      some (List.ofFn fun index => [memoryColumnLookup width (matrix index)]) := by
  apply list_mapM_ofFn id _ _
  intro index
  obtain ⟨buffer, swept, _, lookups⟩ := CompiledKey.memoryCircuit_trace_reflects built matrix index
  simp only [id_eq, Graph.readLookups, swept, bind, Option.bind_some, lookups]

def traceRowValuesWithPreprocessed (widths : GraphWidths) {height : Nat}
    (matrix preprocessed : Fin height → Nat → G) (index : Fin height) : Values G :=
  { traceRowValues widths matrix index with
    columns := fun source offset => match source, offset with
      | .preprocessed, .current => Array.ofFn fun column : Fin widths.preprocessed => preprocessed index column.val
      | .preprocessed, .next => Array.ofFn fun column : Fin widths.preprocessed => preprocessed (memoryNextIndex index) column.val
      | source, offset => (traceRowValues widths matrix index).columns source offset }

theorem traceRowValuesWithPreprocessed_fits (widths : GraphWidths) {height : Nat}
    (matrix preprocessed : Fin height → Nat → G) (index : Fin height) :
    (traceRowValuesWithPreprocessed widths matrix preprocessed index).Fits widths := by
  refine ⟨?_, Array.size_replicate⟩
  intro source offset
  cases source <;> cases offset <;>
    simp only [traceRowValuesWithPreprocessed, traceRowValues, GraphWidths.width, Array.size_ofFn, Array.size_replicate]

theorem traceRowValuesWithPreprocessed_columns {widths : GraphWidths} {height mainWidth preprocessedWidth : Nat}
    (matrix : Fin height → Fin mainWidth → G) (preprocessed : Fin height → Fin preprocessedWidth → G)
    (index : Fin height) (mainBound : mainWidth ≤ widths.main) (preprocessedBound : preprocessedWidth ≤ widths.preprocessed) :
    CompiledKey.columns (traceRowValuesWithPreprocessed widths (finiteTraceMatrix matrix) (finiteTraceMatrix preprocessed) index)
      .main .current mainWidth = matrix index ∧
    CompiledKey.columns (traceRowValuesWithPreprocessed widths (finiteTraceMatrix matrix) (finiteTraceMatrix preprocessed) index)
      .preprocessed .current preprocessedWidth = preprocessed index := by
  refine ⟨(traceRowValues_finite_columns matrix index mainBound).1, ?_⟩
  funext column
  have inside := Nat.lt_of_lt_of_le column.isLt preprocessedBound
  simp only [CompiledKey.columns, traceRowValuesWithPreprocessed, finiteTraceMatrix,
    Array.getElem?_ofFn, inside, column.isLt, dif_pos, Option.getD_some]

def Graph.readPreprocessedTraceLookups (graph : Graph) (widths : GraphWidths) {height : Nat}
    (matrix preprocessed : Fin height → Nat → G) : Option (List LookupRow) :=
  (List.ofFn id).mapM fun index => graph.readLookups (traceRowValuesWithPreprocessed widths matrix preprocessed index)

theorem CompiledKey.byte1Circuit_matrix_lookups {logBlowup : Nat} {artifact : KeyCodec.Circuit}
    (built : CompiledKey.byte1Circuit logBlowup = some artifact) (matrix : Fin 256 → Byte1Columns) :
    artifact.graph.readPreprocessedTraceLookups artifact.widths (finiteTraceMatrix matrix)
        (finiteTraceMatrix byte1PreprocessedColumns) =
      some (List.ofFn fun index => Byte1Kind.all.map fun kind =>
        byte1ColumnLookup kind (byte1PreprocessedColumns index) (matrix index)) := by
  obtain ⟨_, _, _, mainWidth, preWidth, _⟩ := CompiledKey.byte1Circuit_success built
  apply list_mapM_ofFn id _ _
  intro index
  obtain ⟨buffer, swept, _, lookups⟩ := CompiledKey.byte1Circuit_reflects built
    (traceRowValuesWithPreprocessed_fits artifact.widths (finiteTraceMatrix matrix)
      (finiteTraceMatrix byte1PreprocessedColumns) index)
  have columns := traceRowValuesWithPreprocessed_columns matrix byte1PreprocessedColumns index
    (show 3 ≤ artifact.widths.main from Nat.le_of_eq mainWidth.symm)
    (show 11 ≤ artifact.widths.preprocessed from Nat.le_of_eq preWidth.symm)
  rw [columns.1, columns.2] at lookups
  simp only [id_eq, Graph.readLookups, swept, bind, Option.bind_some, lookups]

theorem CompiledKey.byte2Circuit_matrix_lookups {logBlowup : Nat} {artifact : KeyCodec.Circuit}
    (built : CompiledKey.byte2Circuit logBlowup = some artifact) (matrix : Fin 65536 → Byte2Columns) :
    artifact.graph.readPreprocessedTraceLookups artifact.widths (finiteTraceMatrix matrix)
        (finiteTraceMatrix byte2PreprocessedColumns) =
      some (List.ofFn fun index => Byte2Kind.all.map fun kind =>
        byte2ColumnLookup kind (byte2PreprocessedColumns index) (matrix index)) := by
  obtain ⟨_, _, _, mainWidth, preWidth, _⟩ := CompiledKey.byte2Circuit_success built
  apply list_mapM_ofFn id _ _
  intro index
  obtain ⟨buffer, swept, _, lookups⟩ := CompiledKey.byte2Circuit_reflects built
    (traceRowValuesWithPreprocessed_fits artifact.widths (finiteTraceMatrix matrix)
      (finiteTraceMatrix byte2PreprocessedColumns) index)
  have columns := traceRowValuesWithPreprocessed_columns matrix byte2PreprocessedColumns index
    (show 10 ≤ artifact.widths.main from Nat.le_of_eq mainWidth.symm)
    (show 14 ≤ artifact.widths.preprocessed from Nat.le_of_eq preWidth.symm)
  rw [columns.1, columns.2] at lookups
  simp only [id_eq, Graph.readLookups, swept, bind, Option.bind_some, lookups]

theorem graphLookupProvider_byte1 (kind : Byte1Kind) (index : Fin 256) (columns : Byte1Columns) :
    graphLookupProvider (byte1ColumnLookup kind (byte1PreprocessedColumns index) columns) =
      byte1ColumnProvider kind index columns := by
  simp only [graphLookupProvider, byte1ColumnProvider, byte1ColumnLookup, G.neg_neg]

theorem graphLookupProvider_byte2 (kind : Byte2Kind) (index : Fin 65536) (columns : Byte2Columns) :
    graphLookupProvider (byte2ColumnLookup kind (byte2PreprocessedColumns index) columns) =
      byte2ColumnProvider kind index columns := by
  simp only [graphLookupProvider, byte2ColumnProvider, byte2ColumnLookup, G.neg_neg]

theorem graphTableProviders_byte1 (matrix : Fin 256 → Byte1Columns) :
    graphTableProviders (List.ofFn fun index => Byte1Kind.all.map fun kind =>
      byte1ColumnLookup kind (byte1PreprocessedColumns index) (matrix index)) = byte1MatrixProviders matrix := by
  have mapped := List.map_ofFn (f := id (α := Fin 256)) (g := fun index => Byte1Kind.all.map fun kind =>
    byte1ColumnLookup kind (byte1PreprocessedColumns index) (matrix index))
  simp only [Function.comp_id] at mapped
  rw [← mapped]
  simp only [graphTableProviders, List.flatMap_map, Function.comp_def, List.map_map,
    graphLookupProvider_byte1, byte1MatrixProviders, List.finRange]
  rfl

theorem graphTableProviders_byte2 (matrix : Fin 65536 → Byte2Columns) :
    graphTableProviders (List.ofFn fun index => Byte2Kind.all.map fun kind =>
      byte2ColumnLookup kind (byte2PreprocessedColumns index) (matrix index)) = byte2MatrixProviders matrix := by
  have mapped := List.map_ofFn (f := id (α := Fin 65536)) (g := fun index => Byte2Kind.all.map fun kind =>
    byte2ColumnLookup kind (byte2PreprocessedColumns index) (matrix index))
  simp only [Function.comp_id] at mapped
  rw [← mapped]
  simp only [graphTableProviders, List.flatMap_map, Function.comp_def, List.map_map,
    graphLookupProvider_byte2, byte2MatrixProviders, List.finRange]
  rfl

end Aiur.NativeAIR

namespace Aiur.AIR
open NativeAIR

def MemoryTraces.graphLookups {widths : List Nat} : MemoryTraces widths → List KeyCodec.Circuit → Option (List LookupRow)
  | .nil, [] => some []
  | .inactive _ rest, _ :: keys => rest.graphLookups keys
  | .active _ _ matrix rest, key :: keys => do
    let first ← key.graph.readTraceLookups key.widths (finiteTraceMatrix matrix)
    let later ← rest.graphLookups keys
    return first ++ later
  | _, _ => none

theorem MemoryTraces.graph_providers {widths : List Nat} (traces : MemoryTraces widths)
    {logBlowup : Nat} {keys : List KeyCodec.Circuit}
    (built : widths.mapM (CompiledKey.memoryCircuit logBlowup) = some keys) :
    ∃ rows, traces.graphLookups keys = some rows ∧ graphTableProviders rows = traces.providers := by
  induction traces generalizing keys with
  | nil =>
    have empty : keys = [] := (Option.some.inj built).symm
    subst keys
    exact ⟨[], rfl, rfl⟩
  | inactive width rest ih =>
    obtain ⟨key, keys, _, tail, equal⟩ := list_mapM_cons_parts built
    subst equal
    exact ih tail
  | active width degree matrix rest ih =>
    obtain ⟨key, keys, head, tail, equal⟩ := list_mapM_cons_parts built
    subst equal
    obtain ⟨later, laterEq, laterProviders⟩ := ih tail
    have firstEq := CompiledKey.memoryCircuit_matrix_lookups head matrix
    refine ⟨(List.ofFn fun index => [memoryColumnLookup width (matrix index)]) ++ later, ?_, ?_⟩
    · simp only [graphLookups, firstEq, laterEq, bind, Option.bind_some, pure]
    · rw [graphTableProviders_append, graphTableProviders_memory, laterProviders]
      rfl

end Aiur.AIR
