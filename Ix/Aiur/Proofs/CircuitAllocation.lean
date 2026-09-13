/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitLayout
import Ix.Aiur.Proofs.BlockAllocation
import Ix.Aiur.Proofs.CompiledCircuitRows

/-! Compiled layouts and checked row counts bound every symbolic circuit
read by the actual main-trace width, including grouped selector regions. -/

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter BlockEmitter Compiler Aiur.Bytecode

theorem emitMember_layout {rank : Expr} {column lookup selectorBase base : Nat}
    {program : Toplevel} {functionIndex : Nat} {member : Member}
    (functions : FunctionsComputedLayout program.functions) (cursor : column = base + 7)
    (emitted : emitMember rank column lookup selectorBase program functionIndex = some member) :
    member.functionIndex = functionIndex ∧ program.functions[functionIndex]? = some member.function ∧
    member.selectorBase = selectorBase ∧ member.body.column = base + member.function.layout.auxiliaries := by
  simp only [emitMember, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i function functionRead
  dsimp only at emitted
  split at emitted
  · cases emitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i body bodyEmitted
  cases emitted
  have layout := BlockEmitter.emitBlock_layout function.body (.new function.layout.inputSize) base
    (advice_degreeValid _ _) (advice_degrees _ _) cursor bodyEmitted
  have valid := functions function (Array.mem_of_getElem? functionRead)
  exact ⟨rfl, functionRead, rfl, layout.2.trans (congrArg (base + ·) valid.auxiliaries.symm)⟩

theorem emitMembers_layout {rank : Expr} (column lookup selectorBase base : Nat)
    (program : Toplevel) (indices : List Nat) {members : List Member}
    (functions : FunctionsComputedLayout program.functions) (cursor : column = base + 7)
    (emitted : emitMembers rank column lookup selectorBase program indices = some members) :
    members.map Member.functionIndex = indices ∧
    (∀ member ∈ members, program.functions[member.functionIndex]? = some member.function ∧
      member.body.column = base + member.function.layout.auxiliaries ∧
      member.selectorBase + member.function.layout.selectors ≤
        selectorBase + (members.map (fun part => part.function.layout.selectors)).sum) := by
  induction indices generalizing selectorBase members with
  | nil =>
    cases emitted
    exact ⟨rfl, by simp⟩
  | cons index indices ih =>
    simp only [emitMembers, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i member memberEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i rest restEmitted
    cases emitted
    obtain ⟨indexEq, present, selectorEq, columnEq⟩ := emitMember_layout functions cursor memberEmitted
    obtain ⟨indicesEq, tail⟩ := ih _ restEmitted
    refine ⟨by simp only [List.map_cons, indexEq, indicesEq], ?_⟩
    intro chosen memberOf
    rcases List.mem_cons.mp memberOf with equal | later
    · subst chosen
      refine ⟨by rw [indexEq]; exact present, columnEq, ?_⟩
      simp only [List.map_cons, List.sum_cons, selectorEq]
      omega
    · obtain ⟨present, columnEq, bounded⟩ := tail chosen later
      refine ⟨present, columnEq, ?_⟩
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using bounded

private theorem member_functions_read (program : Toplevel) (members : List Member)
    (present : ∀ member ∈ members, program.functions[member.functionIndex]? = some member.function) :
    (members.map Member.functionIndex).mapM (fun index => program.functions[index]?) =
      some (members.map Member.function) := by
  induction members with
  | nil => rfl
  | cons member members ih =>
    simp only [List.map_cons, List.mapM_cons, present member List.mem_cons_self,
      ih (fun member present' => present member (List.mem_cons_of_mem _ present'))]
    rfl

theorem emitMembers_selectors {rank : Expr} (column lookup selectorBase base : Nat)
    (program : Toplevel) (circuit : Circuit) {members : List Member}
    (functions : FunctionsComputedLayout program.functions) (cursor : column = base + 7)
    (validated : circuit.validateRowCounts program = true)
    (emitted : emitMembers rank column lookup selectorBase program circuit.members.toList = some members) :
    (members.map (fun member => member.function.layout.selectors)).sum ≤ circuit.layout.selectors := by
  obtain ⟨indices, layout⟩ := emitMembers_layout column lookup selectorBase base program circuit.members.toList
    functions cursor emitted
  have present := member_functions_read program members (fun member memberOf => (layout member memberOf).1)
  rw [indices] at present
  rw [Circuit.validateRowCounts, present] at validated
  simp only [Bool.and_eq_true, decide_eq_true_eq] at validated
  have leaves : members.map (fun member => member.function.layout.selectors) =
      (members.map Member.function).map (fun function => function.body.controlCounts.leaves) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro member memberOf
    exact (functions member.function (Array.mem_of_getElem? (layout member memberOf).1)).selectors
  rw [leaves]
  exact validated.2.2

private theorem fold_max_le {α : Type} (measure : α → Nat) (items : List α) (initial bound : Nat)
    (before : initial ≤ bound) (members : ∀ item ∈ items, measure item ≤ bound) :
    items.foldl (fun acc item => max acc (measure item)) initial ≤ bound := by
  induction items generalizing initial with
  | nil => exact before
  | cons item items ih =>
    exact ih (max initial (measure item)) (Nat.max_le.mpr ⟨before, members item List.mem_cons_self⟩)
      (fun item member => members item (List.mem_cons_of_mem _ member))

theorem emitCircuit_readBound (program : Toplevel) (circuit : Circuit) {emission : Emission}
    (functions : FunctionsComputedLayout program.functions)
    (columns : MembersColumnBound program.functions circuit.members circuit.layout)
    (validated : circuit.validateRowCounts program = true)
    (emitted : emitCircuit program circuit = some emission) :
    emission.readBound ≤ circuit.layout.width := by
  simp only [emitCircuit, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i members membersEmitted
  cases emitted
  let base := circuit.layout.inputSize + circuit.layout.selectors
  have cursor : circuit.layout.inputSize + circuit.layout.selectors + 1 + 6 = base + 7 := by omega
  obtain ⟨indices, layout⟩ := emitMembers_layout _ _ _ base program circuit.members.toList functions cursor membersEmitted
  have selectors := emitMembers_selectors _ _ _ base program circuit functions cursor validated membersEmitted
  apply fold_max_le Member.readBound
  · change circuit.layout.inputSize + circuit.layout.selectors + 1 + 6 ≤
      circuit.layout.inputSize + circuit.layout.selectors + circuit.layout.auxiliaries
    have reserved := columns.1
    omega
  · intro member memberOf
    obtain ⟨present, bodyColumn, selectorBound⟩ := layout member memberOf
    have memberIndex : member.functionIndex ∈ circuit.members := by
      apply Array.mem_toList_iff.mp
      rw [← indices]
      exact List.mem_map.mpr ⟨member, memberOf, rfl⟩
    have bound := columns.2 member.functionIndex memberIndex
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, present] at bound
    change member.function.layout.inputSize ≤ circuit.layout.inputSize ∧
      member.function.layout.auxiliaries ≤ circuit.layout.auxiliaries at bound
    change max member.function.layout.inputSize
      (max (member.selectorBase + member.function.layout.selectors) member.body.column) ≤
        circuit.layout.inputSize + circuit.layout.selectors + circuit.layout.auxiliaries
    dsimp only [base] at bodyColumn
    omega

theorem compileCircuit_readBound {widths : GraphWidths} (program : Toplevel) (circuit : Circuit)
    {compiled : Compiled} (functions : FunctionsComputedLayout program.functions)
    (columns : MembersColumnBound program.functions circuit.members circuit.layout)
    (validated : circuit.validateRowCounts program = true)
    (built : compileCircuit widths program circuit = some compiled) :
    compiled.emission.readBound ≤ circuit.layout.width := by
  simp only [compileCircuit, bind, Option.bind] at built
  split at built
  · cases built
  rename_i emission emitted
  dsimp only at built
  split at built
  · cases built
  cases built
  exact emitCircuit_readBound program circuit functions columns validated emitted

theorem compileCircuit_physical_reflects {values : Values G} {widths : GraphWidths}
    (fits : values.Fits widths) (program : Toplevel) (circuit : Circuit) {compiled : Compiled}
    (functions : FunctionsComputedLayout program.functions)
    (columns : MembersColumnBound program.functions circuit.members circuit.layout)
    (validated : circuit.validateRowCounts program = true) (physical : widths.main = circuit.layout.width)
    (built : compileCircuit widths program circuit = some compiled) :
    ∃ result buffer,
      circuit.emitRow (fun index => (values.columns .main .current)[index]?.getD 0) program = some result ∧
      compiled.base.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer compiled.base.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      compiled.base.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) := by
  have bound := compileCircuit_readBound program circuit functions columns validated built
  apply compileCircuit_reflects _ fits program circuit built
  intro index indexBound
  have size : index < (values.columns .main .current).size := by
    rw [fits.1, GraphWidths.width, physical]
    exact Nat.lt_of_lt_of_le indexBound bound
  simp only [Array.getElem?_eq_getElem size, Option.getD_some]

end Aiur.NativeAIR.CircuitEmitter

namespace Aiur.BoundVerifier
open NativeAIR NativeAIR.CircuitEmitter

theorem Backend.circuit_readBound {selection : Selection} (backend : Backend selection)
    {circuit : Bytecode.Circuit} (member : circuit ∈ backend.compiled.bytecode.circuits) {emission : Emission}
    (emitted : emitCircuit backend.compiled.bytecode circuit = some emission) :
    emission.readBound ≤ circuit.layout.width :=
  emitCircuit_readBound backend.compiled.bytecode circuit backend.functions_computedLayout
    (backend.circuits_columnBound circuit member) (backend.circuit_row_counts member) emitted

theorem Backend.compileCircuit_reflects {selection : Selection} (backend : Backend selection)
    {values : Values G} {widths : GraphWidths} (fits : values.Fits widths)
    {circuit : Bytecode.Circuit} (member : circuit ∈ backend.compiled.bytecode.circuits) {compiled : Compiled}
    (physical : widths.main = circuit.layout.width)
    (built : compileCircuit widths backend.compiled.bytecode circuit = some compiled) :
    ∃ result buffer,
      circuit.emitRow (fun index => (values.columns .main .current)[index]?.getD 0) backend.compiled.bytecode = some result ∧
      compiled.base.graph.sweep goldilocksOps values = some buffer ∧
      (Compiler.Vanishes goldilocksOps buffer compiled.base.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      compiled.base.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) :=
  compileCircuit_physical_reflects fits backend.compiled.bytecode circuit backend.functions_computedLayout
    (backend.circuits_columnBound circuit member) (backend.circuit_row_counts member) physical built

end Aiur.BoundVerifier
