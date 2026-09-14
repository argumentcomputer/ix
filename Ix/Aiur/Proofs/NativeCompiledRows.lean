/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ComponentCompiledRows

/-! Select the native rank policy from the transported component table.
Both branches check the read and lookup extents needed by physical row
extraction, including reads eliminated by expression folding. -/

namespace Aiur.Bytecode

def Circuit.emitNativeRow (row : Nat → G) (program : Toplevel) (circuit : Circuit) :
    Option AIR.CircuitEmission :=
  if program.callComponents.isEmpty then circuit.emitRow row program
  else circuit.emitComponentRow row program

end Aiur.Bytecode

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter LookupEmitter BlockEmitter Compiler Bytecode

def Emission.footprint (width : Nat) (emission : Emission) : Bool :=
  emission.readBound ≤ width &&
    (0 < emission.lookupCount &&
      emission.queries.all (fun part => 0 < part.slot && part.slot < emission.lookupCount))

def Emission.genericLimits (emission : Emission) : Bool :=
  4 ≤ emission.lookupCount && emission.members.all (fun member => member.body.lookup ≤ emission.lookupCount)

def compileCheckedCircuit (widths : GraphWidths) (program : Toplevel) (circuit : Circuit) :
    Option Compiled := do
  let compiled ← compileCircuit widths program circuit
  if compiled.emission.footprint widths.main && compiled.emission.genericLimits then some compiled else none

theorem compileCheckedCircuit_parts {widths : GraphWidths} {program : Toplevel} {circuit : Circuit}
    {compiled : Compiled} (built : compileCheckedCircuit widths program circuit = some compiled) :
    compileCircuit widths program circuit = some compiled ∧
      compiled.emission.footprint widths.main = true ∧ compiled.emission.genericLimits = true := by
  simp only [compileCheckedCircuit, bind, Option.bind] at built
  split at built
  · cases built
  rename_i result compiled
  dsimp only at built
  split at built
  · rename_i bounds
    cases built
    refine ⟨compiled, ?_⟩
    simpa only [Bool.and_eq_true] using bounds
  · cases built

theorem Emission.footprint_read {width : Nat} {emission : Emission}
    (checked : emission.footprint width = true) : emission.readBound ≤ width := by
  simp only [footprint, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1

theorem Emission.footprint_slots_eval {width : Nat} {emission : Emission}
    {values : Values G} {result : AIR.CircuitEmission}
    (checked : emission.footprint width = true) (evaluated : emission.eval values = some result) :
    ∀ part ∈ result.queries, 0 < part.slot ∧ part.slot < result.lookupCount := by
  obtain ⟨_, _, _, _, _, _, _, count, _, _, queries, _⟩ := Emission.eval_components evaluated
  simp only [footprint, Bool.and_eq_true, decide_eq_true_eq] at checked
  apply AIR.forall₂_right_property
  apply AIR.mapM_forall₂ queries
  intro query present part partEval
  have bounded := List.all_eq_true.mp checked.2.2 query present
  simp only [Bool.and_eq_true, decide_eq_true_eq] at bounded
  rw [(QueryExpr.eval_components partEval).1, count] at bounded
  exact bounded

theorem Emission.footprint_count_eval {width : Nat} {emission : Emission}
    {values : Values G} {result : AIR.CircuitEmission}
    (checked : emission.footprint width = true) (evaluated : emission.eval values = some result) :
    0 < result.lookupCount := by
  have count := (Emission.eval_components evaluated).2.2.2.2.2.2.2.1
  simp only [footprint, Bool.and_eq_true, decide_eq_true_eq] at checked
  rw [← count]
  exact checked.2.1

theorem Emission.genericLimits_eval {emission : Emission} {values : Values G} {result : AIR.CircuitEmission}
    (checked : emission.genericLimits = true) (evaluated : emission.eval values = some result) :
    4 ≤ result.lookupCount ∧ ∀ member ∈ result.members, member.body.lookup ≤ result.lookupCount := by
  obtain ⟨members, _, _, _, _, _, _, count, _⟩ := Emission.eval_components evaluated
  simp only [genericLimits, Bool.and_eq_true, decide_eq_true_eq] at checked
  refine ⟨count ▸ checked.1, ?_⟩
  apply AIR.forall₂_right_property
  apply AIR.mapM_forall₂ members
  intro member present part partEval
  have bound := List.all_eq_true.mp checked.2 member present
  simp only [decide_eq_true_eq] at bound
  have body := (Member.eval_components partEval).2.2.2
  rw [(BlockEmitter.Emission.eval_components body).2.2.1, count] at bound
  exact bound

theorem compileCheckedCircuit_reflects {values : Values G} {widths : GraphWidths}
    (fits : values.Fits widths) {program : Toplevel} {circuit : Circuit} {compiled : Compiled}
    (built : compileCheckedCircuit widths program circuit = some compiled) :
    ∃ result buffer,
      circuit.emitRow (fun index => (values.columns .main .current)[index]?.getD 0) program = some result ∧
      compiled.base.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer compiled.base.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      compiled.base.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) ∧
      0 < result.lookupCount ∧
      (∀ part ∈ result.queries, 0 < part.slot ∧ part.slot < result.lookupCount) ∧
      4 ≤ result.lookupCount ∧ (∀ member ∈ result.members, member.body.lookup ≤ result.lookupCount) := by
  obtain ⟨compiled, footprint, limits⟩ := compileCheckedCircuit_parts built
  have bound := Emission.footprint_read footprint
  simp only [compileCircuit, bind, Option.bind] at compiled
  split at compiled
  · cases compiled
  rename_i emission emitted
  dsimp only at compiled
  split at compiled
  · cases compiled
  rename_i base baseCompiled
  cases compiled
  obtain ⟨result, resultEmitted, evaluated⟩ := emitCircuit_reflects (values := values)
    (fun index => (values.columns .main .current)[index]?.getD 0) program circuit emitted (by
      intro index indexBound
      have size : index < (values.columns .main .current).size := by
        rw [fits.1, GraphWidths.width]
        exact Nat.lt_of_lt_of_le indexBound bound
      simp only [Array.getElem?_eq_getElem size, Option.getD_some])
  obtain ⟨buffer, swept, lookups, zeros⟩ := compileBase_reflects goldilocksGraphLaws fits
    emission.lookups emission.equations baseCompiled
  have equations := (Emission.eval_components evaluated).2.2.2.2.2.2.2.2.2.1
  obtain ⟨messages, exprReads, graphReads⟩ := lookups.read
  exact ⟨result, buffer, resultEmitted, swept, zeros.trans (equations_vanish equations),
    graphReads.trans (exprReads.symm.trans (Emission.lookups_eval evaluated)),
    Emission.footprint_count_eval footprint evaluated,
    Emission.footprint_slots_eval footprint evaluated, Emission.genericLimits_eval limits evaluated⟩

theorem compileCheckedCircuit_widen {small large : GraphWidths} (widths : small.Le large)
    {program : Toplevel} {circuit : Circuit} {compiled : Compiled}
    (built : compileCheckedCircuit small program circuit = some compiled) :
    compileCheckedCircuit large program circuit = some compiled := by
  obtain ⟨baseBuilt, footprint, limits⟩ := compileCheckedCircuit_parts built
  have bounded : _ := footprint
  simp only [Emission.footprint, Bool.and_eq_true, decide_eq_true_eq] at bounded
  have wide : compiled.emission.footprint large.main = true := by
    simp only [Emission.footprint, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.le_trans bounded.1 (widths.1 .main), bounded.2⟩
  simp only [compileCheckedCircuit, compileCircuit_widen widths _ _ baseBuilt,
    wide, limits, Bool.true_and, if_true, bind, Option.bind_some]

def compileNativeCircuit (widths : GraphWidths) (program : Toplevel) (circuit : Circuit) :
    Option Compiled :=
  if program.callComponents.isEmpty then compileCheckedCircuit widths program circuit
  else compileComponentCircuit widths program circuit

theorem compileNativeCircuit_components {widths : GraphWidths} {program : Toplevel} {circuit : Circuit}
    {compiled : Compiled} (built : compileNativeCircuit widths program circuit = some compiled) :
    program.callComponents.isEmpty = true ∨ program.validCallComponents = true := by
  simp only [compileNativeCircuit] at built
  split at built
  · exact Or.inl ‹_›
  · exact Or.inr (compileComponentCircuit_parts built).1

theorem compileNativeCircuit_reflects {values : Values G} {widths : GraphWidths}
    (fits : values.Fits widths) {program : Toplevel} {circuit : Circuit} {compiled : Compiled}
    (built : compileNativeCircuit widths program circuit = some compiled) :
    ∃ result buffer,
      circuit.emitNativeRow (fun index => (values.columns .main .current)[index]?.getD 0) program = some result ∧
      compiled.base.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer compiled.base.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      compiled.base.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) ∧
      0 < result.lookupCount ∧
      (∀ part ∈ result.queries, 0 < part.slot ∧ part.slot < result.lookupCount) ∧
      (program.callComponents.isEmpty = true → 4 ≤ result.lookupCount ∧
        ∀ member ∈ result.members, member.body.lookup ≤ result.lookupCount) := by
  simp only [compileNativeCircuit] at built
  split at built
  · rename_i generic
    obtain ⟨result, buffer, emitted, swept, zeros, lookups, count, ranges, limits⟩ := compileCheckedCircuit_reflects fits built
    exact ⟨result, buffer, by simpa only [Circuit.emitNativeRow, generic, if_true] using emitted,
      swept, zeros, lookups, count, ranges, fun _ => limits⟩
  · rename_i components
    obtain ⟨result, buffer, emitted, swept, zeros, lookups, count, ranges⟩ := compileComponentCircuit_reflects fits built
    refine ⟨result, buffer, by simpa only [Circuit.emitNativeRow, components, Bool.false_eq_true, if_false] using emitted,
      swept, zeros, lookups, count, ranges, ?_⟩
    intro generic
    simp only [components, Bool.false_eq_true] at generic

theorem compileNativeCircuit_widen {small large : GraphWidths} (widths : small.Le large)
    {program : Toplevel} {circuit : Circuit} {compiled : Compiled}
    (built : compileNativeCircuit small program circuit = some compiled) :
    compileNativeCircuit large program circuit = some compiled := by
  simp only [compileNativeCircuit] at built ⊢
  split at built
  · rename_i generic
    simpa only [generic, if_true] using compileCheckedCircuit_widen widths built
  · rename_i components
    simpa only [components, Bool.false_eq_true, if_false] using compileComponentCircuit_widen widths built

end Aiur.NativeAIR.CircuitEmitter
