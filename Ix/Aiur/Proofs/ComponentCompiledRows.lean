/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCircuitReflection
import Ix.Aiur.Proofs.GraphWidths

/-! The reconstructed component artifact checks its own column and slot
extents. Successful graph compilation supplies physical reflection without
an external layout-equality or read-bound premise. -/

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter LookupEmitter BlockEmitter Compiler Bytecode

def compileComponentCircuit (widths : GraphWidths) (program : Toplevel) (circuit : Circuit) :
    Option Compiled :=
  if program.validCallComponents then do
    let emission ← emitComponentCircuit program circuit
    if emission.componentFootprint program widths.main then do
      let base ← compileBase widths emission.lookups emission.equations
      return ⟨emission, base⟩
    else none
  else none

theorem compileComponentCircuit_parts {widths : GraphWidths} {program : Toplevel} {circuit : Circuit}
    {compiled : Compiled} (built : compileComponentCircuit widths program circuit = some compiled) :
    program.validCallComponents = true ∧
      emitComponentCircuit program circuit = some compiled.emission ∧
      compiled.emission.componentFootprint program widths.main = true ∧
      compileBase widths compiled.emission.lookups compiled.emission.equations = some compiled.base := by
  simp only [compileComponentCircuit, bind, Option.bind] at built
  split at built
  · rename_i components
    split at built
    · cases built
    rename_i emission emitted
    dsimp only at built
    split at built
    · rename_i footprint
      split at built
      · cases built
      rename_i base compiled
      cases built
      exact ⟨components, emitted, footprint, compiled⟩
    · cases built
  · cases built

theorem Emission.componentFootprint_slots_eval {program : Toplevel} {width : Nat}
    {emission : Emission} {values : Values G} {result : AIR.CircuitEmission}
    (checked : emission.componentFootprint program width = true)
    (evaluated : emission.eval values = some result) :
    ∀ part ∈ result.queries, 0 < part.slot ∧ part.slot < result.lookupCount := by
  obtain ⟨_, _, _, _, _, _, _, count, _, _, queries, _⟩ := Emission.eval_components evaluated
  apply AIR.forall₂_right_property
  apply AIR.mapM_forall₂ queries
  intro query present part partEval
  have bounded := Emission.componentFootprint_slots checked query present
  rw [(QueryExpr.eval_components partEval).1, count] at bounded
  exact bounded

theorem Emission.componentFootprint_count_eval {program : Toplevel} {width : Nat}
    {emission : Emission} {values : Values G} {result : AIR.CircuitEmission}
    (checked : emission.componentFootprint program width = true)
    (evaluated : emission.eval values = some result) : 0 < result.lookupCount := by
  have count := (Emission.eval_components evaluated).2.2.2.2.2.2.2.1
  simp only [Emission.componentFootprint, Bool.and_eq_true, decide_eq_true_eq] at checked
  rw [← count]
  exact checked.2.1

theorem compileComponentCircuit_reflects {values : Values G} {widths : GraphWidths}
    (fits : values.Fits widths) {program : Toplevel} {circuit : Circuit} {compiled : Compiled}
    (built : compileComponentCircuit widths program circuit = some compiled) :
    ∃ result buffer,
      circuit.emitComponentRow (fun index => (values.columns .main .current)[index]?.getD 0) program = some result ∧
      compiled.base.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer compiled.base.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      compiled.base.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) ∧
      0 < result.lookupCount ∧
      (∀ part ∈ result.queries, 0 < part.slot ∧ part.slot < result.lookupCount) := by
  obtain ⟨_, emitted, footprint, baseCompiled⟩ := compileComponentCircuit_parts built
  have bound := Emission.componentFootprint_read footprint
  obtain ⟨result, resultEmitted, evaluated⟩ := emitComponentCircuit_reflects (values := values)
    (fun index => (values.columns .main .current)[index]?.getD 0) program circuit emitted (by
      intro index indexBound
      have size : index < (values.columns .main .current).size := by
        rw [fits.1, GraphWidths.width]
        exact Nat.lt_of_lt_of_le indexBound bound
      simp only [Array.getElem?_eq_getElem size, Option.getD_some])
  obtain ⟨buffer, swept, lookups, zeros⟩ := compileBase_reflects goldilocksGraphLaws fits
    compiled.emission.lookups compiled.emission.equations baseCompiled
  have equations := (Emission.eval_components evaluated).2.2.2.2.2.2.2.2.2.1
  obtain ⟨messages, exprReads, graphReads⟩ := lookups.read
  exact ⟨result, buffer, resultEmitted, swept, zeros.trans (equations_vanish equations),
    graphReads.trans (exprReads.symm.trans (Emission.lookups_eval evaluated)),
    Emission.componentFootprint_count_eval footprint evaluated,
    Emission.componentFootprint_slots_eval footprint evaluated⟩

theorem compileComponentCircuit_widen {small large : GraphWidths} (widths : small.Le large)
    {program : Toplevel} {circuit : Circuit} {compiled : Compiled}
    (built : compileComponentCircuit small program circuit = some compiled) :
    compileComponentCircuit large program circuit = some compiled := by
  obtain ⟨components, emitted, footprint, baseCompiled⟩ := compileComponentCircuit_parts built
  have bounded : compiled.emission.componentFootprint program large.main = true := by
    simp only [Emission.componentFootprint, Bool.and_eq_true, decide_eq_true_eq] at footprint ⊢
    exact ⟨Nat.le_trans footprint.1 (widths.1 .main), footprint.2⟩
  simp only [compileComponentCircuit, components, if_true, emitted, bounded,
    compileBase_widen widths _ _ baseCompiled, bind, Option.bind_some, pure]

end Aiur.NativeAIR.CircuitEmitter
