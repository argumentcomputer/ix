/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.CompiledVerifier
import Ix.Aiur.Proofs.GraphWidths
import Ix.Aiur.Proofs.TableExpressions
import Ix.Aiur.Proofs.KeyArtifact

/-! The enforced compiled-key comparison supplies graph equality and native
dimensions. Every function, memory and byte circuit in the selected key has
the corresponding physical row meaning, without a graph-equality premise. -/

namespace Aiur.NativeAIR.CompiledKey
open Compiler CircuitEmitter OpEmitter

theorem circuit_success {mainWidth preprocessedWidth preprocessedHeight groupSize : Nat}
    {base : BaseCompilation} {result : KeyCodec.Circuit}
    (built : circuit mainWidth preprocessedWidth preprocessedHeight groupSize base = some result) :
    result.graph = base.graph ∧ result.mainWidth = mainWidth ∧
      result.preprocessedWidth = preprocessedWidth ∧ result.preprocessedHeight = preprocessedHeight ∧
      result.lookupGroupSize = groupSize ∧ result.valid = true := by
  simp only [circuit, bind, Option.bind] at built
  split at built
  · cases built
  · dsimp only at built
    split at built
    · cases built
      exact ⟨rfl, rfl, rfl, rfl, rfl, ‹_›⟩
    · cases built

theorem functionCircuit_success {program : Bytecode.Toplevel} {source : Bytecode.Circuit}
    {result : KeyCodec.Circuit} (built : functionCircuit program source = some result) :
    ∃ compiled, compileCircuit (circuitWidths source) program source = some compiled ∧
      result.graph = compiled.base.graph ∧ result.mainWidth = source.layout.width ∧
      result.preprocessedWidth = 0 ∧ result.preprocessedHeight = 0 ∧
      result.lookupGroupSize = (if compiled.emission.branchless && 2 ≤ compiled.emission.lookups.length then 2 else 1) := by
  cases compiled : compileCircuit (circuitWidths source) program source with
  | none => simp only [functionCircuit, compiled, bind, Option.bind_none, reduceCtorEq] at built
  | some output =>
    simp only [functionCircuit, compiled, bind, Option.bind_some] at built
    have fields := circuit_success built
    exact ⟨output, rfl, fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1⟩

theorem memoryCircuit_success {width : Nat} {result : KeyCodec.Circuit}
    (built : memoryCircuit width = some result) :
    ∃ base, compileBase ⟨0, 3 + width, 0, 0⟩ [memoryLookup width] memoryEquations = some base ∧
      result.graph = base.graph ∧ result.mainWidth = 3 + width ∧
      result.preprocessedWidth = 0 ∧ result.preprocessedHeight = 0 ∧ result.lookupGroupSize = 1 := by
  cases compiled : compileBase ⟨0, 3 + width, 0, 0⟩ [memoryLookup width] memoryEquations with
  | none => simp only [memoryCircuit, compiled, bind, Option.bind_none, reduceCtorEq] at built
  | some base =>
    simp only [memoryCircuit, compiled, bind, Option.bind_some] at built
    have fields := circuit_success built
    exact ⟨base, rfl, fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1⟩

theorem byte1Circuit_success {result : KeyCodec.Circuit} (built : byte1Circuit = some result) :
    ∃ base, compileBase ⟨11, 3, 0, 0⟩ (AIR.Byte1Kind.all.map byte1Lookup) [] = some base ∧
      result.graph = base.graph ∧ result.mainWidth = 3 ∧ result.preprocessedWidth = 11 ∧
      result.preprocessedHeight = 256 ∧ result.lookupGroupSize = 2 := by
  cases compiled : compileBase ⟨11, 3, 0, 0⟩ (AIR.Byte1Kind.all.map byte1Lookup) [] with
  | none => simp only [byte1Circuit, compiled, bind, Option.bind_none, reduceCtorEq] at built
  | some base =>
    simp only [byte1Circuit, compiled, bind, Option.bind_some] at built
    have fields := circuit_success built
    exact ⟨base, rfl, fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1⟩

theorem byte2Circuit_success {result : KeyCodec.Circuit} (built : byte2Circuit = some result) :
    ∃ base, compileBase ⟨14, 10, 0, 0⟩ (AIR.Byte2Kind.all.map byte2Lookup) [] = some base ∧
      result.graph = base.graph ∧ result.mainWidth = 10 ∧ result.preprocessedWidth = 14 ∧
      result.preprocessedHeight = 65536 ∧ result.lookupGroupSize = 2 := by
  cases compiled : compileBase ⟨14, 10, 0, 0⟩ (AIR.Byte2Kind.all.map byte2Lookup) [] with
  | none => simp only [byte2Circuit, compiled, bind, Option.bind_none, reduceCtorEq] at built
  | some base =>
    simp only [byte2Circuit, compiled, bind, Option.bind_some] at built
    have fields := circuit_success built
    exact ⟨base, rfl, fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2.1⟩

theorem circuits_parts {program : Bytecode.Toplevel} {result : List KeyCodec.Circuit}
    (built : circuits program = some result) :
    ∃ functions memories byte1 byte2,
      program.circuits.toList.mapM (functionCircuit program) = some functions ∧
      program.memorySizes.toList.mapM memoryCircuit = some memories ∧
      byte1Circuit = some byte1 ∧ byte2Circuit = some byte2 ∧
      result = functions ++ memories ++ [byte1, byte2] := by
  cases functionsBuilt : program.circuits.toList.mapM (functionCircuit program) with
  | none => simp only [circuits, functionsBuilt, bind, Option.bind_none, reduceCtorEq] at built
  | some functions =>
    cases memoriesBuilt : program.memorySizes.toList.mapM memoryCircuit with
    | none => simp only [circuits, functionsBuilt, memoriesBuilt, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at built
    | some memories =>
      cases first : byte1Circuit with
      | none => simp only [circuits, functionsBuilt, memoriesBuilt, first, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at built
      | some byte1 =>
        cases second : byte2Circuit with
        | none => simp only [circuits, functionsBuilt, memoriesBuilt, first, second, bind, Option.bind_some, Option.bind_none, reduceCtorEq] at built
        | some byte2 =>
          simp only [circuits, functionsBuilt, memoriesBuilt, first, second, bind, Option.bind_some, pure, Option.some.injEq] at built
          exact ⟨functions, memories, byte1, byte2, rfl, rfl, rfl, rfl, built.symm⟩

theorem circuits_length {program : Bytecode.Toplevel} {result : List KeyCodec.Circuit}
    (built : circuits program = some result) :
    result.length = program.circuits.size + program.memorySizes.size + 2 := by
  obtain ⟨functions, memories, _, _, functionsBuilt, memoriesBuilt, _, _, equal⟩ := circuits_parts built
  have fl := Bytecode.AIR.list_mapM_some_length _ _ _ functionsBuilt
  have ml := Bytecode.AIR.list_mapM_some_length _ _ _ memoriesBuilt
  simp only [equal, List.length_append, fl, ml, Array.length_toList, List.length_cons, List.length_nil]

theorem circuits_function {program : Bytecode.Toplevel} {result : List KeyCodec.Circuit}
    (built : circuits program = some result) {index : Nat} {source : Bytecode.Circuit} {artifact : KeyCodec.Circuit}
    (present : program.circuits[index]? = some source) (selected : result[index]? = some artifact) :
    functionCircuit program source = some artifact := by
  obtain ⟨functions, memories, byte1, byte2, functionsBuilt, _, _, _, equal⟩ := circuits_parts built
  have length := Bytecode.AIR.list_mapM_some_length _ _ _ functionsBuilt
  have bound : index < functions.length := by
    rw [length, Array.length_toList]
    exact (Array.getElem?_eq_some_iff.mp present).1
  rw [equal, List.append_assoc, List.getElem?_append_left bound] at selected
  have read := list_mapM_read functionsBuilt index
  simpa only [Array.getElem?_toList, present, Option.bind_some, selected, bind] using read

theorem circuits_memory {program : Bytecode.Toplevel} {result : List KeyCodec.Circuit}
    (built : circuits program = some result) {index width : Nat} {artifact : KeyCodec.Circuit}
    (present : program.memorySizes[index]? = some width)
    (selected : result[program.circuits.size + index]? = some artifact) :
    memoryCircuit width = some artifact := by
  obtain ⟨functions, memories, byte1, byte2, functionsBuilt, memoriesBuilt, _, _, equal⟩ := circuits_parts built
  have fl := Bytecode.AIR.list_mapM_some_length _ _ _ functionsBuilt
  have ml := Bytecode.AIR.list_mapM_some_length _ _ _ memoriesBuilt
  have first : functions.length ≤ program.circuits.size + index := by simp only [fl, Array.length_toList]; omega
  have inside : index < memories.length := by
    rw [ml, Array.length_toList]
    exact (Array.getElem?_eq_some_iff.mp present).1
  rw [equal, List.append_assoc, List.getElem?_append_right first] at selected
  simp only [fl, Array.length_toList, Nat.add_sub_cancel_left, List.getElem?_append_left inside] at selected
  have read := list_mapM_read memoriesBuilt index
  simpa only [Array.getElem?_toList, present, Option.bind_some, selected, bind] using read

theorem circuits_bytes {program : Bytecode.Toplevel} {result : List KeyCodec.Circuit}
    (built : circuits program = some result) :
    ∃ byte1 byte2, byte1Circuit = some byte1 ∧ byte2Circuit = some byte2 ∧
      result[program.circuits.size + program.memorySizes.size]? = some byte1 ∧
      result[program.circuits.size + program.memorySizes.size + 1]? = some byte2 := by
  obtain ⟨functions, memories, byte1, byte2, functionsBuilt, memoriesBuilt, first, second, equal⟩ := circuits_parts built
  have fl := Bytecode.AIR.list_mapM_some_length _ _ _ functionsBuilt
  have ml := Bytecode.AIR.list_mapM_some_length _ _ _ memoriesBuilt
  have length : (functions ++ memories).length = program.circuits.size + program.memorySizes.size := by
    simp only [List.length_append, fl, ml, Array.length_toList]
  refine ⟨byte1, byte2, first, second, ?_, ?_⟩
  · rw [equal, List.getElem?_append_right (by omega), length, Nat.sub_self]
    rfl
  · rw [equal, List.getElem?_append_right (by omega), length]
    simp only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.getElem?_cons_zero]

theorem memoryCircuit_reflects {width : Nat} {artifact : KeyCodec.Circuit}
    (built : memoryCircuit width = some artifact) {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ buffer, artifact.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer artifact.graph.zeros ↔
        ∀ equation ∈ AIR.memoryColumnEquations width (columns values .main .current (3 + width))
          (columns values .main .next (3 + width)) values.isTransition, equation = 0) ∧
      artifact.graph.lookups.mapM (readLookup buffer) =
        some [AIR.memoryColumnLookup width (columns values .main .current (3 + width))] := by
  obtain ⟨base, compiled, graph, mainWidth, _, _, _⟩ := memoryCircuit_success built
  have widths : (GraphWidths.mk 0 (3 + width) 0 0).Le artifact.widths := by
    refine ⟨?_, Nat.zero_le _⟩
    intro source
    cases source <;> simp only [GraphWidths.width, KeyCodec.Circuit.widths, mainWidth, Nat.le_refl, Nat.zero_le]
  have wide := compileBase_widen widths _ _ compiled
  obtain ⟨buffer, swept, lookups, equations⟩ := compileBase_reflects goldilocksGraphLaws fits _ _ wide
  have mainBound : 3 + width ≤ artifact.widths.main := by simp only [KeyCodec.Circuit.widths, mainWidth, Nat.le_refl]
  have eqs := memoryEquations_eval fits width mainBound
  have lookup := memoryLookup_eval fits width mainBound
  obtain ⟨results, exprReads, graphReads⟩ := lookups.read
  refine ⟨buffer, graph ▸ swept, ?_, ?_⟩
  · rw [graph]
    exact equations.trans (equations_vanish eqs)
  · rw [graph]
    exact graphReads.trans (exprReads.symm.trans (by
      simp only [List.mapM_cons, List.mapM_nil, lookup, bind, Option.bind_some, pure]))

theorem byte1Circuit_reflects {artifact : KeyCodec.Circuit} (built : byte1Circuit = some artifact)
    {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ buffer, artifact.graph.sweep goldilocksOps values = some buffer ∧
      Vanishes goldilocksOps buffer artifact.graph.zeros ∧
      artifact.graph.lookups.mapM (readLookup buffer) = some
        (AIR.Byte1Kind.all.map fun kind => AIR.byte1ColumnLookup kind
          (columns values .preprocessed .current 11) (columns values .main .current 3)) := by
  obtain ⟨base, compiled, graph, mainWidth, preWidth, _, _⟩ := byte1Circuit_success built
  have widths : (GraphWidths.mk 11 3 0 0).Le artifact.widths := by
    refine ⟨?_, Nat.zero_le _⟩
    intro source
    cases source <;> simp only [GraphWidths.width, KeyCodec.Circuit.widths, mainWidth, preWidth, Nat.le_refl, Nat.zero_le]
  have wide := compileBase_widen widths _ _ compiled
  obtain ⟨buffer, swept, lookups, equations⟩ := compileBase_reflects goldilocksGraphLaws fits _ _ wide
  have mainBound : 3 ≤ artifact.widths.main := by simp only [KeyCodec.Circuit.widths, mainWidth, Nat.le_refl]
  have preBound : 11 ≤ artifact.widths.preprocessed := by simp only [KeyCodec.Circuit.widths, preWidth, Nat.le_refl]
  have evaluated := list_mapM_of_map AIR.Byte1Kind.all byte1Lookup _ (ExprLookup.eval goldilocksOps values)
    (fun kind _ => byte1Lookup_eval fits mainBound preBound kind)
  obtain ⟨results, exprReads, graphReads⟩ := lookups.read
  refine ⟨buffer, graph ▸ swept, ?_, ?_⟩
  · rw [graph]
    exact equations.mpr (fun _ member => nomatch member)
  · rw [graph]
    exact graphReads.trans (exprReads.symm.trans evaluated)

theorem byte2Circuit_reflects {artifact : KeyCodec.Circuit} (built : byte2Circuit = some artifact)
    {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ buffer, artifact.graph.sweep goldilocksOps values = some buffer ∧
      Vanishes goldilocksOps buffer artifact.graph.zeros ∧
      artifact.graph.lookups.mapM (readLookup buffer) = some
        (AIR.Byte2Kind.all.map fun kind => AIR.byte2ColumnLookup kind
          (columns values .preprocessed .current 14) (columns values .main .current 10)) := by
  obtain ⟨base, compiled, graph, mainWidth, preWidth, _, _⟩ := byte2Circuit_success built
  have widths : (GraphWidths.mk 14 10 0 0).Le artifact.widths := by
    refine ⟨?_, Nat.zero_le _⟩
    intro source
    cases source <;> simp only [GraphWidths.width, KeyCodec.Circuit.widths, mainWidth, preWidth, Nat.le_refl, Nat.zero_le]
  have wide := compileBase_widen widths _ _ compiled
  obtain ⟨buffer, swept, lookups, equations⟩ := compileBase_reflects goldilocksGraphLaws fits _ _ wide
  have mainBound : 10 ≤ artifact.widths.main := by simp only [KeyCodec.Circuit.widths, mainWidth, Nat.le_refl]
  have preBound : 14 ≤ artifact.widths.preprocessed := by simp only [KeyCodec.Circuit.widths, preWidth, Nat.le_refl]
  have evaluated := list_mapM_of_map AIR.Byte2Kind.all byte2Lookup _ (ExprLookup.eval goldilocksOps values)
    (fun kind _ => byte2Lookup_eval fits mainBound preBound kind)
  obtain ⟨results, exprReads, graphReads⟩ := lookups.read
  refine ⟨buffer, graph ▸ swept, ?_, ?_⟩
  · rw [graph]
    exact equations.mpr (fun _ member => nomatch member)
  · rw [graph]
    exact graphReads.trans (exprReads.symm.trans evaluated)

end Aiur.NativeAIR.CompiledKey

namespace Aiur.BoundVerifier
open NativeAIR NativeAIR.CircuitEmitter NativeAIR.Compiler

theorem CompiledBackend.circuit_count {selection : Selection} (backend : CompiledBackend selection) :
    backend.keyData.circuits.length =
      backend.compiled.bytecode.circuits.size + backend.compiled.bytecode.memorySizes.size + 2 :=
  CompiledKey.circuits_length backend.circuits_bound

theorem CompiledBackend.function_graph_reflects {selection : Selection} (backend : CompiledBackend selection)
    {index : Nat} {source : Bytecode.Circuit} {artifact : KeyCodec.Circuit}
    (present : backend.compiled.bytecode.circuits[index]? = some source)
    (selected : backend.keyData.circuits[index]? = some artifact)
    {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ result buffer,
      source.emitRow (fun index => (values.columns .main .current)[index]?.getD 0) backend.compiled.bytecode = some result ∧
      artifact.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer artifact.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      artifact.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) := by
  have bound := CompiledKey.circuits_function backend.circuits_bound present selected
  obtain ⟨compiled, built, graph, mainWidth, _, _, _⟩ := CompiledKey.functionCircuit_success bound
  have physical : artifact.widths.main = source.layout.width := mainWidth
  have wide := compileCircuit_widen (circuitWidths_le (Nat.le_of_eq physical.symm)) _ _ built
  obtain ⟨result, buffer, emitted, swept, satisfied, lookups⟩ := backend.toBackend.compileCircuit_reflects
    fits (Array.mem_of_getElem? present) physical wide
  exact ⟨result, buffer, emitted, graph ▸ swept, graph ▸ satisfied, graph ▸ lookups⟩

theorem CompiledBackend.memory_graph_reflects {selection : Selection} (backend : CompiledBackend selection)
    {index width : Nat} {artifact : KeyCodec.Circuit}
    (present : backend.compiled.bytecode.memorySizes[index]? = some width)
    (selected : backend.keyData.circuits[backend.compiled.bytecode.circuits.size + index]? = some artifact)
    {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ buffer, artifact.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer artifact.graph.zeros ↔
        ∀ equation ∈ AIR.memoryColumnEquations width (CompiledKey.columns values .main .current (3 + width))
          (CompiledKey.columns values .main .next (3 + width)) values.isTransition, equation = 0) ∧
      artifact.graph.lookups.mapM (readLookup buffer) =
        some [AIR.memoryColumnLookup width (CompiledKey.columns values .main .current (3 + width))] :=
  CompiledKey.memoryCircuit_reflects (CompiledKey.circuits_memory backend.circuits_bound present selected) fits

theorem CompiledBackend.byte_graphs {selection : Selection} (backend : CompiledBackend selection) :
    ∃ byte1 byte2, CompiledKey.byte1Circuit = some byte1 ∧ CompiledKey.byte2Circuit = some byte2 ∧
      backend.keyData.circuits[backend.compiled.bytecode.circuits.size + backend.compiled.bytecode.memorySizes.size]? = some byte1 ∧
      backend.keyData.circuits[backend.compiled.bytecode.circuits.size + backend.compiled.bytecode.memorySizes.size + 1]? = some byte2 :=
  CompiledKey.circuits_bytes backend.circuits_bound

theorem CompiledBackend.byte1_graph_reflects {selection : Selection} (backend : CompiledBackend selection)
    {artifact : KeyCodec.Circuit}
    (selected : backend.keyData.circuits[backend.compiled.bytecode.circuits.size + backend.compiled.bytecode.memorySizes.size]? = some artifact)
    {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ buffer, artifact.graph.sweep goldilocksOps values = some buffer ∧
      Vanishes goldilocksOps buffer artifact.graph.zeros ∧
      artifact.graph.lookups.mapM (readLookup buffer) = some
        (AIR.Byte1Kind.all.map fun kind => AIR.byte1ColumnLookup kind
          (CompiledKey.columns values .preprocessed .current 11) (CompiledKey.columns values .main .current 3)) := by
  obtain ⟨byte1, _, built, _, present, _⟩ := backend.byte_graphs
  have equal := Option.some.inj (present.symm.trans selected)
  subst artifact
  exact CompiledKey.byte1Circuit_reflects built fits

theorem CompiledBackend.byte2_graph_reflects {selection : Selection} (backend : CompiledBackend selection)
    {artifact : KeyCodec.Circuit}
    (selected : backend.keyData.circuits[backend.compiled.bytecode.circuits.size + backend.compiled.bytecode.memorySizes.size + 1]? = some artifact)
    {values : Values G} (fits : values.Fits artifact.widths) :
    ∃ buffer, artifact.graph.sweep goldilocksOps values = some buffer ∧
      Vanishes goldilocksOps buffer artifact.graph.zeros ∧
      artifact.graph.lookups.mapM (readLookup buffer) = some
        (AIR.Byte2Kind.all.map fun kind => AIR.byte2ColumnLookup kind
          (CompiledKey.columns values .preprocessed .current 14) (CompiledKey.columns values .main .current 10)) := by
  obtain ⟨_, byte2, _, built, _, present⟩ := backend.byte_graphs
  have equal := Option.some.inj (present.symm.trans selected)
  subst artifact
  exact CompiledKey.byte2Circuit_reflects built fits

end Aiur.BoundVerifier
