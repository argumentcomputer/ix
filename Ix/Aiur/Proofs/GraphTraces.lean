/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.NativeTraceExecution

/-! Base graphs evaluated on the physical main rows supply the witnesses,
equations and lookup slots used by execution extraction. Unused stage-two,
public and preprocessing columns are zero here; these graphs are the base
graphs reconstructed by `CompiledKey`, before LogUp constraints are added. -/

namespace Aiur.NativeAIR
open AIR Compiler

def traceRowValues (widths : GraphWidths) {height : Nat} (matrix : Fin height → Nat → G)
    (index : Fin height) : Values G where
  columns
    | .main, .current => Array.ofFn fun column : Fin widths.main => matrix index column.val
    | .main, .next => Array.ofFn fun column : Fin widths.main => matrix (memoryNextIndex index) column.val
    | .preprocessed, _ => Array.replicate widths.preprocessed 0
    | .stage2, _ => Array.replicate widths.stage2 0
  publics := Array.replicate widths.publics 0
  isFirstRow := if index.val = 0 then 1 else 0
  isLastRow := if index.val + 1 = height then 1 else 0
  isTransition := if index.val + 1 < height then 1 else 0

theorem traceRowValues_fits (widths : GraphWidths) {height : Nat} (matrix : Fin height → Nat → G)
    (index : Fin height) : (traceRowValues widths matrix index).Fits widths := by
  refine ⟨?_, ?_⟩
  · intro source offset
    cases source <;> cases offset <;> simp only [traceRowValues, GraphWidths.width, Array.size_ofFn, Array.size_replicate]
  · exact Array.size_replicate

theorem traceRowValues_current (widths : GraphWidths) {height : Nat} (matrix : Fin height → Nat → G)
    (index : Fin height) :
    (fun column => ((traceRowValues widths matrix index).columns .main .current)[column]?.getD 0) =
      boundedTraceRow widths.main (matrix index) := rfl

def finiteTraceMatrix {height width : Nat} (matrix : Fin height → Fin width → G) : Fin height → Nat → G :=
  fun row column => (Array.ofFn (matrix row))[column]?.getD 0

theorem traceRowValues_finite_columns {widths : GraphWidths} {height width : Nat}
    (matrix : Fin height → Fin width → G) (index : Fin height) (bound : width ≤ widths.main) :
    CompiledKey.columns (traceRowValues widths (finiteTraceMatrix matrix) index) .main .current width = matrix index ∧
      CompiledKey.columns (traceRowValues widths (finiteTraceMatrix matrix) index) .main .next width =
        matrix (memoryNextIndex index) := by
  constructor <;> funext column
  all_goals
    have inside := Nat.lt_of_lt_of_le column.isLt bound
    simp only [CompiledKey.columns, traceRowValues, finiteTraceMatrix, Array.getElem?_ofFn,
      inside, column.isLt, dif_pos, Option.getD_some]

def Graph.RowSatisfied (graph : Graph) (values : Values G) : Prop :=
  ∃ buffer, graph.sweep goldilocksOps values = some buffer ∧ Vanishes goldilocksOps buffer graph.zeros

def Graph.TraceSatisfied (graph : Graph) (widths : GraphWidths) {height : Nat}
    (matrix : Fin height → Nat → G) : Prop :=
  ∀ index, graph.RowSatisfied (traceRowValues widths matrix index)

theorem CompiledKey.functionCircuit_trace_witness {logBlowup : Nat} {program : Bytecode.Toplevel}
    {source : Bytecode.Circuit} {artifact : KeyCodec.Circuit}
    (built : CompiledKey.functionCircuit logBlowup program source = some artifact)
    {height : Nat} (matrix : Fin height → Nat → G) (index : Fin height)
    (satisfied : artifact.graph.RowSatisfied (traceRowValues artifact.widths matrix index)) :
    ∃ witness : CircuitWitness, ∃ buffer,
      emitNativeCircuitWitness program source (matrix index) = some witness ∧
      witness.Satisfied ∧ witness.NativeBounds program ∧
      artifact.graph.sweep goldilocksOps (traceRowValues artifact.widths matrix index) = some buffer ∧
      artifact.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin witness.emission.lookupCount => witness.emission.lookup slot.val) := by
  obtain ⟨witness, buffer, circuit, row, emitted, bounds, swept, equations, lookups⟩ :=
    CompiledKey.functionCircuit_witness built (traceRowValues_fits artifact.widths matrix index)
  have mainWidth := (CompiledKey.functionCircuit_success built).choose_spec.2.2.1
  have physical : artifact.widths.main = source.layout.width := mainWidth
  rw [traceRowValues_current, physical] at row
  have witnessEq : witness = ⟨source, boundedTraceRow source.layout.width (matrix index), witness.emission⟩ := by
    cases witness
    simp only [CircuitWitness.mk.injEq] at *
    exact ⟨circuit, row, trivial⟩
  have produced : emitNativeCircuitWitness program source (matrix index) = some witness := by
    have step := emitted
    change witness.circuit.emitNativeRow witness.values program = some witness.emission at step
    rw [circuit, row] at step
    simp only [emitNativeCircuitWitness, step, bind, Option.bind_some, pure]
    exact congrArg some witnessEq.symm
  obtain ⟨actual, read, zeros⟩ := satisfied
  have equal := Option.some.inj (swept.symm.trans read)
  subst actual
  exact ⟨witness, buffer, produced, equations.mp zeros, bounds, swept, lookups⟩

theorem CompiledKey.memoryCircuit_trace_reflects {logBlowup width : Nat} {artifact : KeyCodec.Circuit}
    (built : CompiledKey.memoryCircuit logBlowup width = some artifact) {height : Nat}
    (matrix : Fin height → MemoryColumns width) (index : Fin height) :
    ∃ buffer, artifact.graph.sweep goldilocksOps
        (traceRowValues artifact.widths (finiteTraceMatrix matrix) index) = some buffer ∧
      (Vanishes goldilocksOps buffer artifact.graph.zeros ↔
        ∀ equation ∈ memoryMatrixEquations width height matrix index, equation = 0) ∧
      artifact.graph.lookups.mapM (readLookup buffer) = some [memoryColumnLookup width (matrix index)] := by
  obtain ⟨buffer, swept, equations, lookups⟩ :=
    CompiledKey.memoryCircuit_reflects built (traceRowValues_fits artifact.widths (finiteTraceMatrix matrix) index)
  have mainWidth := (CompiledKey.memoryCircuit_success built).choose_spec.2.2.1
  have physical : artifact.widths.main = 3 + width := mainWidth
  have columns := traceRowValues_finite_columns matrix index (Nat.le_of_eq physical.symm)
  rw [columns.1, columns.2] at equations
  rw [columns.1] at lookups
  exact ⟨buffer, swept, equations, lookups⟩

theorem CompiledKey.memoryCircuit_trace_satisfied {logBlowup width : Nat} {artifact : KeyCodec.Circuit}
    (built : CompiledKey.memoryCircuit logBlowup width = some artifact) {height : Nat}
    (matrix : Fin height → MemoryColumns width)
    (satisfied : artifact.graph.TraceSatisfied artifact.widths (finiteTraceMatrix matrix)) :
    MemoryMatrixSatisfied width height matrix := by
  intro index
  obtain ⟨buffer, swept, equations, _⟩ := CompiledKey.memoryCircuit_trace_reflects built matrix index
  obtain ⟨actual, read, zeros⟩ := satisfied index
  have equal := Option.some.inj (swept.symm.trans read)
  subst actual
  exact equations.mp zeros

end Aiur.NativeAIR

namespace Aiur.AIR
open Bytecode NativeAIR NativeAIR.OpEmitter

def CircuitTraces.GraphSatisfied {circuits : List Circuit} : CircuitTraces circuits → List KeyCodec.Circuit → Prop
  | .nil, keys => keys = []
  | .inactive _ rest, _ :: keys => rest.GraphSatisfied keys
  | .active _ _ matrix rest, key :: keys =>
    key.graph.TraceSatisfied key.widths matrix ∧ rest.GraphSatisfied keys
  | .inactive _ _, [] => False
  | .active _ _ _ _, [] => False

theorem list_mapM_cons_parts {read : α → Option β} {input : α} {inputs : List α} {outputs : List β}
    (built : (input :: inputs).mapM read = some outputs) :
    ∃ first rest, read input = some first ∧ inputs.mapM read = some rest ∧ outputs = first :: rest := by
  simp only [List.mapM_cons, bind, Option.bind] at built
  split at built
  · cases built
  rename_i first head
  dsimp only at built
  split at built
  · cases built
  rename_i rest tail
  exact ⟨first, rest, head, tail, (Option.some.inj built).symm⟩

theorem CircuitTraces.graph_emits {circuits : List Circuit} (traces : CircuitTraces circuits)
    {logBlowup : Nat} {program : Toplevel} {keys : List KeyCodec.Circuit}
    (built : circuits.mapM (CompiledKey.functionCircuit logBlowup program) = some keys)
    (satisfied : traces.GraphSatisfied keys) :
    ∃ witnesses, traces.emitNativeWitnesses program = some witnesses ∧
      ∀ witness ∈ witnesses, witness.Satisfied ∧ witness.NativeBounds program := by
  induction traces generalizing keys with
  | nil => exact ⟨[], rfl, fun _ member => nomatch member⟩
  | inactive circuit rest ih =>
    obtain ⟨key, keys, _, tail, equal⟩ := list_mapM_cons_parts built
    subst equal
    exact ih tail satisfied
  | active circuit degree matrix rest ih =>
    obtain ⟨key, keys, head, tail, equal⟩ := list_mapM_cons_parts built
    subst equal
    obtain ⟨later, laterEq, laterValid⟩ := ih tail satisfied.2
    have each : ∀ values ∈ List.ofFn matrix, ∃ witness,
        emitNativeCircuitWitness program circuit values = some witness ∧
          witness.Satisfied ∧ witness.NativeBounds program := by
      intro values member
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
      obtain ⟨witness, _, produced, valid, bounds, _⟩ :=
        CompiledKey.functionCircuit_trace_witness head matrix index (satisfied.1 index)
      exact ⟨witness, produced, valid, bounds⟩
    obtain ⟨first, firstEq⟩ := list_mapM_defined (List.ofFn matrix) (fun values member => by
      obtain ⟨witness, produced, _⟩ := each values member
      exact ⟨witness, produced⟩)
    have valid := mapM_forall₂ firstEq (fun values member witness produced => by
      obtain ⟨actual, emitted, valid⟩ := each values member
      have equal := Option.some.inj (produced.symm.trans emitted)
      exact equal ▸ valid)
    refine ⟨first ++ later, ?_, ?_⟩
    · simp only [emitNativeWitnesses, firstEq, laterEq, bind, Option.bind_some, pure]
    · intro witness member
      rcases List.mem_append.mp member with before | after
      · exact (forall₂_right_member valid before).choose_spec.2
      · exact laterValid witness after

def MemoryTraces.GraphSatisfied {widths : List Nat} : MemoryTraces widths → List KeyCodec.Circuit → Prop
  | .nil, keys => keys = []
  | .inactive _ rest, _ :: keys => rest.GraphSatisfied keys
  | .active _ _ matrix rest, key :: keys =>
    key.graph.TraceSatisfied key.widths (finiteTraceMatrix matrix) ∧ rest.GraphSatisfied keys
  | .inactive _ _, [] => False
  | .active _ _ _ _, [] => False

theorem MemoryTraces.graph_satisfied {widths : List Nat} (traces : MemoryTraces widths)
    {logBlowup : Nat} {keys : List KeyCodec.Circuit}
    (built : widths.mapM (CompiledKey.memoryCircuit logBlowup) = some keys)
    (satisfied : traces.GraphSatisfied keys) : traces.Satisfied := by
  induction traces generalizing keys with
  | nil => trivial
  | inactive width rest ih =>
    obtain ⟨key, keys, _, tail, equal⟩ := list_mapM_cons_parts built
    subst equal
    exact ih tail satisfied
  | active width degree matrix rest ih =>
    obtain ⟨key, keys, head, tail, equal⟩ := list_mapM_cons_parts built
    subst equal
    exact ⟨CompiledKey.memoryCircuit_trace_satisfied head matrix satisfied.1, ih tail satisfied.2⟩

end Aiur.AIR
