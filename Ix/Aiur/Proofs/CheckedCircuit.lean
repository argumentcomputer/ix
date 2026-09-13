/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockCompletion
import Ix.Aiur.Proofs.CircuitCompletion

/-! Checked backend construction supplies circuit emission and a physical graph. -/

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter BlockEmitter Bytecode

theorem emitMember_defined (rank : Expr) (column lookup selectorBase : Nat)
    (program : Toplevel) (index : Nat) {function : Function}
    (present : program.functions[index]? = some function) (checked : function.emissionChecks = true) :
    ∃ member, emitMember rank column lookup selectorBase program index = some member := by
  rw [Function.emissionChecks, Bool.and_eq_true] at checked
  have bodyChecks : function.body.emissionChecks (advice 0 function.layout.inputSize).size
      (selectorExprs selectorBase function.layout.selectors).size none = true := by
    simpa only [advice, selectorExprs, Array.size_ofFn] using checked.2
  obtain ⟨entry, selected⟩ := blockSelector_defined (selectorExprs selectorBase function.layout.selectors) function.body bodyChecks
  obtain ⟨body, emitted, _⟩ := emitBlock_defined (selectorExprs selectorBase function.layout.selectors)
    ⟨index, function.layout.inputSize, rank⟩ entry (advice 0 function.layout.inputSize) column lookup function.body
    (advice_degreeValid _ _) (by simp only [advice, Array.size_ofFn, Nat.le_refl]) bodyChecks
  refine ⟨⟨index, function, selectorBase, entry, body⟩, ?_⟩
  simp only [emitMember, present, selected, emitted, bind, Option.bind_some, pure]

theorem emitMembers_defined (rank : Expr) (column lookup selectorBase : Nat) (program : Toplevel) (indices : List Nat)
    (checked : ∀ index ∈ indices, ∃ function, program.functions[index]? = some function ∧ function.emissionChecks = true) :
    ∃ members, emitMembers rank column lookup selectorBase program indices = some members := by
  induction indices generalizing selectorBase with
  | nil => exact ⟨[], rfl⟩
  | cons index indices ih =>
    obtain ⟨function, present, valid⟩ := checked index List.mem_cons_self
    obtain ⟨member, memberEmitted⟩ := emitMember_defined rank column lookup selectorBase program index present valid
    obtain ⟨members, membersEmitted⟩ := ih (selectorBase + member.function.layout.selectors)
      (fun index present => checked index (List.mem_cons_of_mem _ present))
    exact ⟨member :: members, by simp only [emitMembers, memberEmitted, membersEmitted, bind, Option.bind_some, pure]⟩

theorem emitCircuit_defined (program : Toplevel) (circuit : Circuit)
    (checked : program.validateEmission = true) (members : MembersConstrained program.functions circuit.members) :
    ∃ emission, emitCircuit program circuit = some emission := by
  have valid : ∀ index ∈ circuit.members.toList,
      ∃ function, program.functions[index]? = some function ∧ function.emissionChecks = true := by
    intro index member
    obtain ⟨function, present, constrained⟩ := members index (by simpa using member)
    exact ⟨function, present, Toplevel.validateEmission_function checked (Array.mem_of_getElem? present) constrained⟩
  obtain ⟨emissions, emitted⟩ := emitMembers_defined (packSix (rankBytes circuit.layout))
    (circuit.layout.inputSize + circuit.layout.selectors + 1 + 6) 4 circuit.layout.inputSize
    program circuit.members.toList valid
  refine ⟨circuitEmission circuit emissions, ?_⟩
  simp only [emitCircuit, emitted, bind, Option.bind_some, pure]

end Aiur.NativeAIR.CircuitEmitter

namespace Aiur.BoundVerifier
open NativeAIR NativeAIR.CircuitEmitter

theorem Backend.circuit_emits {selection : Selection} (backend : Backend selection)
    {circuit : Bytecode.Circuit} (member : circuit ∈ backend.compiled.bytecode.circuits) :
    ∃ emission, emitCircuit backend.compiled.bytecode circuit = some emission :=
  emitCircuit_defined backend.compiled.bytecode circuit backend.emissionChecks (backend.circuits_constrained circuit member)

theorem Backend.circuit_compiles {selection : Selection} (backend : Backend selection)
    {circuit : Bytecode.Circuit} (member : circuit ∈ backend.compiled.bytecode.circuits) :
    ∃ compiled, compileCircuit (circuitWidths circuit) backend.compiled.bytecode circuit = some compiled := by
  obtain ⟨emission, emitted⟩ := backend.circuit_emits member
  obtain ⟨compiled, built, _⟩ := backend.emitCircuit_compiles member emitted
  exact ⟨compiled, built⟩

theorem Backend.circuit_graph_reflects {selection : Selection} (backend : Backend selection)
    {circuit : Bytecode.Circuit} (member : circuit ∈ backend.compiled.bytecode.circuits)
    {values : Values G} (fits : values.Fits (circuitWidths circuit)) :
    ∃ compiled result buffer,
      compileCircuit (circuitWidths circuit) backend.compiled.bytecode circuit = some compiled ∧
      circuit.emitRow (fun index => (values.columns .main .current)[index]?.getD 0) backend.compiled.bytecode = some result ∧
      compiled.base.graph.sweep goldilocksOps values = some buffer ∧
      (Compiler.Vanishes goldilocksOps buffer compiled.base.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      compiled.base.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) := by
  obtain ⟨emission, emitted⟩ := backend.circuit_emits member
  obtain ⟨compiled, result, buffer, built, _, resultEmitted, swept, satisfied, lookups⟩ :=
    backend.emittedCircuit_reflects member fits emitted
  exact ⟨compiled, result, buffer, built, resultEmitted, swept, satisfied, lookups⟩

end Aiur.BoundVerifier
