/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitTraces
import Ix.Aiur.Proofs.Grouping
import Std.Tactic.Do

/-! The actual compiler and successful grouping produce only constrained
circuit members. The selected backend's program shape check therefore
discharges the shape condition for every successfully emitted trace row.
Physical lookup bounds, native extraction and the cryptographic and
source-semantic endpoint remain separate proof obligations. -/

open Std.Do
namespace Aiur.Bytecode

def MembersConstrained (functions : Array Function) (members : Array FunIdx) : Prop :=
  ∀ index ∈ members, ∃ function, functions[index]? = some function ∧ function.constrained = true

def CircuitsConstrained (functions : Array Function) (circuits : Array Circuit) : Prop :=
  ∀ circuit ∈ circuits, MembersConstrained functions circuit.members

private theorem circuits_empty (functions : Array Function) : CircuitsConstrained functions #[] := by
  simp [CircuitsConstrained]

private theorem circuits_push {functions : Array Function} {circuits : Array Circuit} {circuit : Circuit}
    (before : CircuitsConstrained functions circuits) (member : MembersConstrained functions circuit.members) :
    CircuitsConstrained functions (circuits.push circuit) := by
  intro c present
  rcases Array.mem_push.mp present with prior | equal
  · exact before c prior
  · subst c; exact member

private theorem member_singleton {functions : Array Function} {index : FunIdx} {function : Function}
    (present : functions[index]? = some function) (constrained : function.constrained = true) :
    MembersConstrained functions #[index] := by
  intro i member
  have equal : i = index := by simpa using member
  subst i
  exact ⟨function, present, constrained⟩

private theorem members_empty (functions : Array Function) : MembersConstrained functions #[] := by
  simp [MembersConstrained]

private theorem members_push {functions : Array Function} {members : Array FunIdx} {index : FunIdx}
    (before : MembersConstrained functions members) (constrained : functions[index]!.constrained = true) :
    MembersConstrained functions (members.push index) := by
  intro i member
  rcases Array.mem_push.mp member with prior | equal
  · exact before i prior
  · subst i
    by_cases bound : index < functions.size
    · exact ⟨functions[index], Array.getElem?_eq_getElem bound,
        by simpa only [getElem!_pos functions index bound] using constrained⟩
    · rw [getElem!_neg functions index bound] at constrained
      contradiction

private theorem array_bang_valid {α : Type} [Inhabited α] (property : α → Prop)
    {array : Array α} (valid : ∀ value ∈ array, property value) (fallback : property default) (index : Nat) :
    property array[index]! := by
  by_cases bound : index < array.size
  · rw [getElem!_pos array index bound]
    exact valid _ (Array.getElem_mem bound)
  · rw [getElem!_neg array index bound]
    exact fallback

private theorem array_split_member {α : Type} {array : Array α} {pref suff : List α} {value : α}
    (split : array.toList = pref ++ value :: suff) : value ∈ array := by
  apply Array.mem_toList_iff.mp
  rw [split]
  simp

set_option mvcgen.warning false in
theorem singletonCircuits_constrained (program : Toplevel) (nameOf : FunIdx → String) :
    CircuitsConstrained program.functions (program.singletonCircuits nameOf) := by
  have spec : Triple (m := Id) (program.singletonCircuits nameOf) ⌜True⌝
      (⇓ circuits => ⌜CircuitsConstrained program.functions circuits⌝) := by
    mvcgen [Toplevel.singletonCircuits, Id.run] invariants
    · ⇓⟨_, circuits⟩ => ⌜CircuitsConstrained program.functions circuits⌝
    case vc1.step.isTrue =>
      apply circuits_push (by assumption)
      apply member_singleton (Array.getElem?_eq_getElem _)
      assumption
    case vc3.pre => exact circuits_empty _
  exact Id.of_wp_run_eq rfl _ spec

end Aiur.Bytecode

namespace Aiur
open Bytecode

-- The library's corresponding specification has unused monad parameters.
-- This specialization keeps loop verification conditions fully determined.
private theorem throw_except {ε α : Type} {error : ε} {post : PostCond α (.except ε .pure)} :
    Triple (ps := .except ε .pure) (throw error : Except ε α) (spred(post.2.1 error)) post := by
  simp [Triple.iff]

set_option mvcgen.warning false in
theorem CompiledToplevel.groupFunctions_constrained {before after : CompiledToplevel}
    {groups : Array (String × Array String)}
    (valid : CircuitsConstrained before.bytecode.functions before.bytecode.circuits)
    (accepted : before.groupFunctions groups = .ok after) :
    CircuitsConstrained after.bytecode.functions after.bytecode.circuits := by
  have spec : ⦃⌜True⌝⦄ before.groupFunctions groups
      ⦃post⟨fun compiled => ⌜CircuitsConstrained compiled.bytecode.functions compiled.bytecode.circuits⌝,
        fun _ => ⌜True⌝⟩⦄ := by
    mvcgen [CompiledToplevel.groupFunctions, -Spec.throw_Except, throw_except] invariants
    · post⟨fun ⟨_, _, resolved⟩ => ⌜∀ pair ∈ resolved,
        MembersConstrained before.bytecode.functions pair.2⌝, fun _ => ⌜True⌝⟩
    · post⟨fun ⟨_, _, members⟩ => ⌜MembersConstrained before.bytecode.functions members⌝,
        fun _ => ⌜True⌝⟩
    · post⟨fun ⟨_, circuits, _⟩ => ⌜CircuitsConstrained before.bytecode.functions circuits⌝,
        fun _ => ⌜True⌝⟩
    case vc4.step.h_1.isTrue.isFalse.isFalse => exact members_push (by assumption) (by assumption)
    case vc7.step.isFalse.pre => exact members_empty _
    case vc8.step.isFalse.post.success =>
      intro pair member
      rcases Array.mem_push.mp member with prior | equal
      · apply_assumption; exact prior
      · subst pair; assumption
    case vc10.pre =>
      change ∀ pair ∈ (#[] : Array (String × Array FunIdx)), _
      simp
    case vc11.step.isTrue.h_1 =>
      apply circuits_push (by assumption)
      apply valid
      exact array_split_member (by assumption)
    case vc13.step.isTrue.h_2.isFalse =>
      apply circuits_push (by assumption)
      exact array_bang_valid (fun pair : String × Array FunIdx =>
        MembersConstrained before.bytecode.functions pair.2) (by assumption) (members_empty _) _
    case vc15.post.success.pre => exact circuits_empty _
  exact Except.of_wp_eq accepted (fun result => match result with
    | .error _ => True
    | .ok compiled => CircuitsConstrained compiled.bytecode.functions compiled.bytecode.circuits) spec

theorem finishCompilation_circuits_constrained (source : Source.Toplevel) (raw : Bytecode.Toplevel)
    (names : Std.HashMap Global Bytecode.FunIdx) :
    CircuitsConstrained (finishCompilation source raw names).bytecode.functions
      (finishCompilation source raw names).bytecode.circuits := by
  unfold finishCompilation
  exact singletonCircuits_constrained _ _

theorem Source.Toplevel.compile_circuits_constrained {source : Source.Toplevel} {compiled : CompiledToplevel}
    (accepted : source.compile = .ok compiled) :
    CircuitsConstrained compiled.bytecode.functions compiled.bytecode.circuits := by
  obtain ⟨inlined, typed, concrete, raw, names, _, _, _, _, artifact⟩ :=
    source.compile_artifact_of_ok accepted
  rw [artifact]
  exact finishCompilation_circuits_constrained inlined raw names

theorem BoundVerifier.Backend.circuits_constrained {selection : BoundVerifier.Selection}
    (backend : BoundVerifier.Backend selection) :
    CircuitsConstrained backend.compiled.bytecode.functions backend.compiled.bytecode.circuits := by
  obtain ⟨initial, compiled, grouped⟩ := backend.compilation_stages
  have valid := Source.Toplevel.compile_circuits_constrained compiled
  split at grouped
  · cases grouped
    exact valid
  · exact CompiledToplevel.groupFunctions_constrained valid grouped

end Aiur

namespace Aiur.Bytecode

theorem Toplevel.validateLookupShapes_function {program : Toplevel}
    (valid : program.validateLookupShapes = true) {function : Function} {index : FunIdx}
    (present : program.functions[index]? = some function) (constrained : function.constrained = true) :
    function.body.lookupShapes program none = true := by
  simp only [Toplevel.validateLookupShapes, Bool.and_eq_true] at valid
  have checked := Array.all_eq_true'.mp valid.2.2 function (Array.mem_of_getElem? present)
  simpa only [constrained, Bool.not_true, Bool.false_or] using checked

end Aiur.Bytecode

namespace Aiur.AIR
open Bytecode

theorem CircuitWitness.shapes_of_compiled {program : Toplevel}
    (shapes : program.validateLookupShapes = true)
    (constrained : CircuitsConstrained program.functions program.circuits)
    (witness : CircuitWitness) (circuit : witness.circuit ∈ program.circuits)
    (emitted : witness.Emitted program) : witness.Shapes program := by
  obtain ⟨_, indices, source⟩ := witness.circuit.emitRow_spec witness.values program emitted
  intro part member
  have index : part.functionIndex ∈ witness.circuit.members := by
    apply Array.mem_toList_iff.mp
    rw [← indices]
    exact List.mem_map.mpr ⟨part, member, rfl⟩
  obtain ⟨function, present, isConstrained⟩ := constrained witness.circuit circuit part.functionIndex index
  have equal := Option.some.inj (present.symm.trans (source part member).present)
  subst function
  exact Toplevel.validateLookupShapes_function shapes present isConstrained

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem Backend.witness_shapes {selection : Selection} (backend : Backend selection)
    (witness : CircuitWitness) (circuit : witness.circuit ∈ backend.compiled.bytecode.circuits)
    (emitted : witness.Emitted backend.compiled.bytecode) : witness.Shapes backend.compiled.bytecode :=
  witness.shapes_of_compiled backend.lookupShapes backend.circuits_constrained circuit emitted

theorem Backend.compiled_trace_execution {selection : Selection} (backend : Backend selection)
    (tables : AuxiliaryTables) (traces : CircuitTraces backend.compiled.bytecode.circuits.toList)
    {witnesses : List CircuitWitness}
    (emitted : traces.emitWitnesses backend.compiled.bytecode = some witnesses)
    {otherSlots : List Nat} {otherActive : List Bool} {otherDegrees : List Nat} {result : Nat}
    (budget : lookupQueryBound
      (backend.compiled.bytecode.circuits.toList.map (·.layout.lookups) ++ otherSlots)
      (traces.bitmap ++ otherActive) (traces.degrees ++ otherDegrees) = some result)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList ::
        encodedCircuitQueryPool (witnesses.map (·.emission)))
      (tables.circuitProviders (witnesses.map (·.emission))))
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied)
    (limits : ∀ witness ∈ witnesses, witness.LookupBounds) :
    Execution backend.compiled.bytecode (memoryFacts tables.memory)
      ⟨selection.function, input, selection.success, 0⟩ := by
  have valid := (traces.emitWitnesses_spec emitted).1
  apply backend.trace_circuit_execution tables traces emitted budget width input arity balanced
    publicWidth queryWidths memoryValid canonical satisfied _ limits
  intro witness member
  exact backend.witness_shapes witness (by simpa using (valid witness member).1) (valid witness member).2

end Aiur.BoundVerifier
