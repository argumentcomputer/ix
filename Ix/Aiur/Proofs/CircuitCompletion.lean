/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitAllocation
import Ix.Aiur.Proofs.GraphCompletion
import Ix.Aiur.Proofs.InactiveRows

/-! A successfully emitted compiled circuit always has a base graph at its
physical width. Its zero row satisfies the equations, excluding rejection of
nonzero constant constraints without assuming an active execution. -/

namespace Aiur.NativeAIR.CircuitEmitter
open Compiler Aiur.Bytecode

def circuitWidths (circuit : Circuit) : GraphWidths := ⟨0, circuit.layout.width, 0, 0⟩

def zeroValues (width : Nat) : Values G where
  columns := fun source _ => match source with
    | .main => Array.replicate width 0
    | _ => #[]
  publics := #[]
  isFirstRow := 0
  isLastRow := 0
  isTransition := 0

theorem zeroValues_fits (circuit : Circuit) : (zeroValues circuit.layout.width).Fits (circuitWidths circuit) := by
  refine ⟨?_, rfl⟩
  intro source offset
  cases source <;> simp only [zeroValues, circuitWidths, GraphWidths.width, Array.size_replicate, Array.size_empty]

theorem zeroValues_read (width index : Nat) (bound : index < width) :
    ((zeroValues width).columns .main .current)[index]? = some 0 := by
  simp only [zeroValues, Array.getElem?_replicate, bound, if_true]

theorem emitCircuit_zero_eval (program : Toplevel) (circuit : Circuit) {emission : Emission}
    (functions : FunctionsComputedLayout program.functions)
    (columns : MembersColumnBound program.functions circuit.members circuit.layout)
    (validated : circuit.validateRowCounts program = true)
    (emitted : emitCircuit program circuit = some emission) :
    ∃ result, emission.eval (zeroValues circuit.layout.width) = some result ∧
      (∀ equation ∈ result.equations, equation = 0) := by
  have bound := emitCircuit_readBound program circuit functions columns validated emitted
  obtain ⟨result, resultEmitted, evaluated⟩ := emitCircuit_reflects (fun _ => 0) program circuit emitted
    (fun index indexBound => zeroValues_read _ _ (Nat.lt_of_lt_of_le indexBound bound))
  exact ⟨result, evaluated, circuit.emitRow_zero program resultEmitted⟩

theorem emitCircuit_compiles (program : Toplevel) (circuit : Circuit) {emission : Emission}
    (functions : FunctionsComputedLayout program.functions)
    (columns : MembersColumnBound program.functions circuit.members circuit.layout)
    (validated : circuit.validateRowCounts program = true)
    (emitted : emitCircuit program circuit = some emission) :
    ∃ compiled, compileCircuit (circuitWidths circuit) program circuit = some compiled ∧
      compiled.emission = emission := by
  obtain ⟨result, evaluated, satisfied⟩ := emitCircuit_zero_eval program circuit functions columns validated emitted
  have equations := (Emission.eval_components evaluated).2.2.2.2.2.2.2.2.2.1
  have zeros := (equations_vanish equations).mpr satisfied
  obtain ⟨base, baseCompiled⟩ := compileBase_defined goldilocksGraphLaws
    (show Function.Injective goldilocksOps.konst from fun _ _ equal => equal)
    (zeroValues_fits circuit) rfl emission.lookups emission.equations (Emission.lookups_eval evaluated) zeros
  refine ⟨⟨emission, base⟩, ?_, rfl⟩
  simp only [compileCircuit, emitted, baseCompiled, bind, Option.bind_some, pure]

theorem compileCircuit_defined_iff (program : Toplevel) (circuit : Circuit)
    (functions : FunctionsComputedLayout program.functions)
    (columns : MembersColumnBound program.functions circuit.members circuit.layout)
    (validated : circuit.validateRowCounts program = true) :
    (compileCircuit (circuitWidths circuit) program circuit).isSome = true ↔
      (emitCircuit program circuit).isSome = true := by
  constructor
  · intro compiled
    cases emitted : emitCircuit program circuit with
    | none => simp only [compileCircuit, emitted, bind, Option.bind_none, Option.isSome_none, Bool.false_eq_true] at compiled
    | some emission => rfl
  · intro emitted
    obtain ⟨emission, emitted⟩ := Option.isSome_iff_exists.mp emitted
    obtain ⟨compiled, built, _⟩ := emitCircuit_compiles program circuit functions columns validated emitted
    rw [built]
    rfl

end Aiur.NativeAIR.CircuitEmitter

namespace Aiur.BoundVerifier
open NativeAIR NativeAIR.CircuitEmitter

theorem Backend.emitCircuit_compiles {selection : Selection} (backend : Backend selection)
    {circuit : Bytecode.Circuit} (member : circuit ∈ backend.compiled.bytecode.circuits) {emission : Emission}
    (emitted : emitCircuit backend.compiled.bytecode circuit = some emission) :
    ∃ compiled, compileCircuit (circuitWidths circuit) backend.compiled.bytecode circuit = some compiled ∧
      compiled.emission = emission :=
  CircuitEmitter.emitCircuit_compiles backend.compiled.bytecode circuit backend.functions_computedLayout
    (backend.circuits_columnBound circuit member) (backend.circuit_row_counts member) emitted

theorem Backend.emittedCircuit_reflects {selection : Selection} (backend : Backend selection)
    {circuit : Bytecode.Circuit} (member : circuit ∈ backend.compiled.bytecode.circuits)
    {values : Values G} (fits : values.Fits (circuitWidths circuit)) {emission : Emission}
    (emitted : emitCircuit backend.compiled.bytecode circuit = some emission) :
    ∃ compiled result buffer,
      compileCircuit (circuitWidths circuit) backend.compiled.bytecode circuit = some compiled ∧
      compiled.emission = emission ∧
      circuit.emitRow (fun index => (values.columns .main .current)[index]?.getD 0) backend.compiled.bytecode = some result ∧
      compiled.base.graph.sweep goldilocksOps values = some buffer ∧
      (Compiler.Vanishes goldilocksOps buffer compiled.base.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      compiled.base.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) := by
  obtain ⟨compiled, built, same⟩ := backend.emitCircuit_compiles member emitted
  obtain ⟨result, buffer, resultEmitted, swept, satisfied, lookups⟩ :=
    backend.compileCircuit_reflects fits member rfl built
  exact ⟨compiled, result, buffer, built, same, resultEmitted, swept, satisfied, lookups⟩

end Aiur.BoundVerifier
