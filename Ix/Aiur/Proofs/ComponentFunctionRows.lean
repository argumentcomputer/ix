/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentExecution
import Ix.Aiur.Proofs.FunctionRows

/-! Component row obligations derived from the valued function emitter.
The checked call collector determines the mode of every executed edge. -/

namespace Aiur.Bytecode
open Aiur.AIR

def Toplevel.componentRowRank (program : Toplevel) (functionIndex : FunIdx)
    (rankBytes : Fin 6 → G) : G :=
  if (program.componentFor functionIndex).ranked then packRank rankBytes else 0

theorem Function.emitRow_componentValid {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (program : Toplevel) (components : program.validCallComponents = true)
    (row : Nat → G) (selector : SelIdx → G)
    (functionIndex : FunIdx) (rankBytes : Fin 6 → G) (values : Array RowValue) (column lookup : Nat)
    (function : Function) (present : program.functions[functionIndex]? = some function)
    (constrained : function.constrained = true)
    (arity : values.size = function.layout.inputSize)
    (shape : function.body.lookupShapes program none = true) (bounds : function.body.rowBounds selector)
    {emission : BlockEmission}
    (emitted : function.emitRow row selector functionIndex (program.componentRowRank functionIndex rankBytes)
      values column lookup (program.callRanksFor functionIndex) = some emission)
    (multiplicity : G) (nonzero : multiplicity ≠ 0)
    (activity : activityConstraint multiplicity (function.body.selectorFlow selector).entry = 0)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) (queried : emission.QueriesIn queries) :
    ∃ interpreted : FunctionRow, interpreted.ComponentValid program (memoryFacts tables.memory) ∧
      (1, interpreted.request) ∈ emission.returns ∧
      interpreted.request.function = functionIndex ∧ interpreted.request.inputs = rowValues values ∧
      interpreted.request.rank = program.componentRowRank functionIndex rankBytes ∧
      interpreted.rankBytes = rankBytes ∧
      interpreted.selector = (function.body.selectorFlow selector).entry ∧
      interpreted.multiplicity = multiplicity ∧ emission.CallsAt interpreted.calls ∧
      CallsEmitted (program.componentRowRank functionIndex rankBytes) 1 emission.equations queries
        interpreted.calls (program.callRanksFor functionIndex) := by
  have active := nonzero_multiplicity_selector_one activity nonzero
  obtain ⟨request, calls, member, functionEq, inputsEq, rankEq, execution, called, inventory⟩ :=
    function.emitRow_run global memoryValid canonical program row selector functionIndex
      (program.componentRowRank functionIndex rankBytes) values column lookup
      present arity shape bounds emitted active satisfied queried
  let interpreted : FunctionRow := ⟨request, calls, rankBytes, 1, multiplicity⟩
  refine ⟨interpreted, ?_, member, functionEq, inputsEq, rankEq, rfl, active.symm, rfl, called, inventory⟩
  have selected : program.functions[request.function]? = some function := by
    rw [functionEq]
    exact present
  refine ⟨Or.inr rfl, ?_, fun _ => ⟨function, selected, constrained⟩, ?_, fun _ => execution, ?_⟩
  · rw [active] at activity
    exact activity
  · intro _
    change request.rank = if (program.componentFor request.function).ranked then packRank rankBytes else 0
    rw [functionEq]
    exact rankEq
  · intro edge edgeMember same
    have componentEdge := execution.calls_components components selected constrained edge.1
      (List.mem_map.mpr ⟨edge, edgeMember, rfl⟩)
    have mode := componentEdge.rankMode same
    rw [functionEq] at mode
    change 1 * callOrderConstraint request.rank edge.1.rank (packRank edge.2) = 0
    rw [rankEq]
    exact ((inventory edge edgeMember).2.ordered mode).2.satisfied satisfied

end Aiur.Bytecode
