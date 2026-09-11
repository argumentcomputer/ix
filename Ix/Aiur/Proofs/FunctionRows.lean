/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockRowInputs

/-!
Whole-function execution and local function-row validity derived from the
valued emitter. The same semantic return determines the combined provider
message, including shared slots with differing raw message lengths.

Lookup membership, count bounds, function layout and activity premises are
explicit. These theorems do not yet extract rows from the Rust verifier or
establish public acceptance-to-certified-claim soundness.
-/

namespace Aiur.AIR

theorem slotMessage_chosen (width : Nat) (branchless : Bool) {parts : List (G × List G)}
    (single : branchless = true → parts.length = 1)
    (individual : ∀ part ∈ parts, booleanConstraint part.1 = 0)
    (bounded : parts.length < gSize.toNat)
    (active : selectorSum (parts.map Prod.fst) = 1)
    {chosen : G × List G} (member : chosen ∈ parts) (selected : chosen.1 = 1) :
    padMessage width (slotMessage branchless parts) = padMessage width chosen.2 := by
  cases branchless with
  | false =>
    obtain ⟨before, after, equal, zero⟩ := selector_pair_chosen individual bounded active member selected
    rw [equal]
    exact weightedMessage_split width before after chosen selected zero
  | true =>
    obtain ⟨part, equal⟩ := List.length_eq_one_iff.mp (single rfl)
    subst parts
    have same := List.mem_singleton.mp member
    subst chosen
    rfl

end Aiur.AIR

namespace Aiur.Bytecode
open Aiur.AIR

def Function.emitRow (row : Nat → G) (selector : SelIdx → G) (functionIndex : FunIdx) (rank : G)
    (values : Array RowValue) (column lookup : Nat) (function : Function) : Option BlockEmission :=
  function.body.emitRow row selector ⟨functionIndex, function.layout.inputSize, rank⟩
    (function.body.selectorFlow selector).entry values column lookup

theorem Function.emitRow_run {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (program : Toplevel) (row : Nat → G) (selector : SelIdx → G)
    (functionIndex : FunIdx) (rank : G) (values : Array RowValue) (column lookup : Nat)
    (function : Function) (present : program.functions[functionIndex]? = some function)
    (arity : values.size = function.layout.inputSize)
    (shape : function.body.lookupShapes program none = true) (bounds : function.body.rowBounds selector)
    {emission : BlockEmission}
    (emitted : function.emitRow row selector functionIndex rank values column lookup = some emission)
    (active : (function.body.selectorFlow selector).entry = 1)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) (queried : emission.QueriesIn queries) :
    ∃ request calls, (1, request) ∈ emission.returns ∧
      request.function = functionIndex ∧ request.inputs = rowValues values ∧ request.rank = rank ∧
      AIR.RunFunction program (memoryFacts tables.memory) request (calls.map Prod.fst) ∧
      emission.CallsAt calls ∧ CallsEmitted rank 1 emission.equations queries calls := by
  have bodyEmitted := emitted
  rw [Function.emitRow] at bodyEmitted
  have initial : RowInputs function.layout.inputSize (rowValues values) values := by
    rw [← arity]
    exact RowInputs.full values
  have preserved := function.body.emitRow_inputs row selector _ _ _ _ _ initial bodyEmitted
  have tracked := function.body.emitRow_tracks_calls row selector _ _ _ _ _ bodyEmitted
  obtain ⟨outcome, calls, execution, terminal, called⟩ := function.body.emitRow_run global memoryValid canonical
    program none row selector _ _ _ _ _ shape bounds bodyEmitted active rfl satisfied queried
  cases outcome with
  | returned outputs =>
    obtain ⟨request, member, outputsEq⟩ := terminal
    obtain ⟨functionEq, inputsEq, rankEq⟩ := preserved.returned (1, request) member
    refine ⟨request, calls, member, functionEq, inputsEq, rankEq, ?_, called, tracked.active queried called⟩
    apply AIR.RunFunction.function
    · rw [functionEq]
      exact present
    · rw [inputsEq]
      simpa only [rowValues, Array.size_map] using arity.symm
    · rw [inputsEq, outputsEq]
      exact execution
  | yielded outputs =>
    obtain ⟨yielded, member, _⟩ := terminal
    have empty := function.body.selectorFlow_yields_empty selector program shape
    have projected := function.body.emitRow_projection row selector _ _ _ _ _ bodyEmitted
    have one : (1 : G) ∈ emission.yields.map Prod.fst :=
      List.mem_map.mpr ⟨(1, yielded), member, rfl⟩
    rw [projected.yielded, empty] at one
    cases one

theorem Function.emitRow_valid {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (program : Toplevel) (row : Nat → G) (selector : SelIdx → G)
    (functionIndex : FunIdx) (rankBytes : Fin 6 → G) (values : Array RowValue) (column lookup : Nat)
    (function : Function) (present : program.functions[functionIndex]? = some function)
    (arity : values.size = function.layout.inputSize)
    (shape : function.body.lookupShapes program none = true) (bounds : function.body.rowBounds selector)
    {emission : BlockEmission}
    (emitted : function.emitRow row selector functionIndex (packRank rankBytes) values column lookup = some emission)
    (multiplicity : G) (nonzero : multiplicity ≠ 0)
    (activity : activityConstraint multiplicity (function.body.selectorFlow selector).entry = 0)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0) (queried : emission.QueriesIn queries) :
    ∃ interpreted : FunctionRow, interpreted.Valid program (memoryFacts tables.memory) ∧
      (1, interpreted.request) ∈ emission.returns ∧
      interpreted.request.function = functionIndex ∧ interpreted.request.inputs = rowValues values ∧
      interpreted.request.rank = packRank rankBytes ∧ interpreted.rankBytes = rankBytes ∧
      interpreted.selector = (function.body.selectorFlow selector).entry ∧
      interpreted.multiplicity = multiplicity ∧ emission.CallsAt interpreted.calls ∧
      CallsEmitted (packRank rankBytes) 1 emission.equations queries interpreted.calls := by
  have active := nonzero_multiplicity_selector_one activity nonzero
  obtain ⟨request, calls, member, functionEq, inputsEq, rankEq, execution, called, inventory⟩ :=
    function.emitRow_run global memoryValid canonical program row selector functionIndex (packRank rankBytes)
      values column lookup present arity shape bounds emitted active satisfied queried
  let interpreted : FunctionRow := ⟨request, calls, rankBytes, 1, multiplicity⟩
  refine ⟨interpreted, ?_, member, functionEq, inputsEq, rankEq, rfl, active.symm, rfl, called, inventory⟩
  refine ⟨Or.inr rfl, ?_, fun _ => rankEq, fun _ => execution, ?_⟩
  · rw [active] at activity
    exact activity
  · intro edge edgeMember
    change 1 * callOrderConstraint request.rank edge.1.rank (packRank edge.2) = 0
    rw [rankEq]
    exact satisfied _ (inventory edge edgeMember).2.2

theorem Function.emitRow_message (row : Nat → G) (selector : SelIdx → G)
    (functionIndex : FunIdx) (rank : G) (values : Array RowValue) (column lookup : Nat)
    (function : Function) (program : Toplevel)
    (shape : function.body.lookupShapes program none = true)
    {emission : BlockEmission}
    (emitted : function.emitRow row selector functionIndex rank values column lookup = some emission)
    (active : (function.body.selectorFlow selector).entry = 1)
    (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (bounded : emission.returns.length < gSize.toNat)
    (width : Nat) (branchless : Bool) (single : branchless = true → emission.returns.length = 1)
    {request : AIR.Call} (member : (1, request) ∈ emission.returns) :
    padMessage width (slotMessage branchless
      (emission.returns.map fun part => (part.1, functionMessage part.2))) =
      padMessage width (functionMessage request) := by
  have bodyEmitted := emitted
  rw [Function.emitRow] at bodyEmitted
  have projection := function.body.emitRow_projection row selector _ _ _ _ _ bodyEmitted
  have valid := function.body.emitRow_selectors row selector _ _ _ _ _ bodyEmitted satisfied
  have gates := projection.returned.trans (function.body.returnGates_reflects selector _ valid rfl)
  have empty := function.body.selectorFlow_yields_empty selector program shape
  have sound := function.body.selectorFlow_sound selector valid
  have conservation := sound.conservation
  rw [empty] at conservation
  change _ = selectorSum (function.body.selectorFlow selector).returns + 0 at conservation
  rw [G.add_zero, active] at conservation
  apply slotMessage_chosen width branchless
    (by simpa only [List.length_map] using single)
    (fun part present => ?_)
    (by simpa only [List.length_map] using bounded)
    (by simpa only [List.map_map, Function.comp_def, gates] using conservation.symm)
    (List.mem_map.mpr ⟨(1, request), member, rfl⟩) rfl
  obtain ⟨returned, returnMember, equal⟩ := List.mem_map.mp present
  subst part
  apply sound.returned returned.1
  rw [← gates]
  exact List.mem_map.mpr ⟨returned, returnMember, rfl⟩

end Aiur.Bytecode
