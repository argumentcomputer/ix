/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Compilation
import Ix.Aiur.LookupShapes
import Ix.Aiur.RowCounts
import Ix.Aiur.EmissionChecks
import Ix.Aiur.Protocol

/-! A verifier whose caller selects the source, entrypoint, parameters and
complete allowed key bytes. Untrusted proof bytes cannot select any of them.

This is a program/statement/key binding component. It does not assert that
the selected source implements the certified checker, that compilation or
AIR constraints reflect source execution, or that the proof-system FFI is
sound. Those are distinct C8 obligations. In particular, no certified release
is instantiated here for the legacy `verify_claim` or the C2 pilot.
-/

namespace Aiur.BoundVerifier

/-- Trusted deployment selection, independent of the proof being verified.
Circuit grouping is explicit; environment-variable overrides are not used. -/
structure Selection where
  source : Source.Toplevel
  groups : Array (String × Array String) := #[]
  entrypoint : Lean.Name
  function : Bytecode.FunIdx
  inputSize : Nat
  success : Array G
  commitment : CommitmentParameters
  fri : FriParameters
  key : ByteArray

def Selection.compile (selection : Selection) : Except String CompiledToplevel := do
  let compiled ← selection.source.compile
  if selection.groups.isEmpty then return compiled
  compiled.groupFunctions selection.groups

/-- The system is built from exactly the selected compilation and parameters.
It is derived, rather than accepted as a second independent caller argument. -/
def Selection.system (selection : Selection) (compiled : CompiledToplevel) : AiurSystem :=
  AiurSystem.build compiled.bytecode selection.commitment selection.fri

structure Backend (selection : Selection) where
  compiled : CompiledToplevel
  compilation : selection.compile = .ok compiled
  system : AiurSystem
  systemBuilt : system = selection.system compiled
  selected : compiled.getFuncIdx selection.entrypoint = some selection.function
  functionRange : selection.function < gSize.toNat
  entry : Bytecode.Function
  present : compiled.bytecode.functions[selection.function]? = some entry
  publicEntry : entry.entry = true
  constrained : entry.constrained = true
  arity : entry.layout.inputSize = selection.inputSize
  returnArity : entry.body.returnsHaveSize selection.success.size = true
  lookupShapes : compiled.bytecode.validateLookupShapes = true
  rowCounts : compiled.bytecode.validateRowCounts = true
  emissionChecks : compiled.bytecode.validateEmission = true
  keyBound : system.vkBytes = selection.key

def build (selection : Selection) : Except String (Backend selection) :=
  match hc : selection.compile with
  | .error e => .error e
  | .ok compiled =>
    if hs : compiled.getFuncIdx selection.entrypoint = some selection.function then
      if hr : selection.function < gSize.toNat then
        match hp : compiled.bytecode.functions[selection.function]? with
        | none => .error "selected function is absent"
        | some entry =>
          if he : entry.entry = true ∧ entry.constrained = true ∧
              entry.layout.inputSize = selection.inputSize then
            if ho : entry.body.returnsHaveSize selection.success.size = true then
              if hl : compiled.bytecode.validateLookupShapes = true then
                if hn : compiled.bytecode.validateRowCounts = true then
                  if hi : compiled.bytecode.validateEmission = true then
                    let system := selection.system compiled
                    if hk : system.vkBytes = selection.key then
                      .ok ⟨compiled, hc, system, rfl, hs, hr, entry, hp, he.1, he.2.1, he.2.2, ho, hl, hn, hi, hk⟩
                    else .error "verification key differs from the selected key"
                  else .error "compiled circuit reads an invalid logical value or selector"
                else .error "compiled circuit control counts exceed their bounds"
              else .error "compiled lookup message arities differ"
            else .error "selected success result has the wrong output arity"
          else .error "selected function is not a constrained public entry of the expected arity"
      else .error "function index is not a canonical field element"
    else .error "entrypoint differs from the selected function"

/-- `input` is the statement the caller expects. A serialized proof supplies
neither a different statement nor an alternative key or success result. -/
def verify {selection : Selection} (backend : Backend selection) (input : Array G)
    (bytes : ByteArray) : Except String Unit := do
  if input.size != selection.inputSize then throw "public input arity differs"
  let proof ← Proof.ofBytesChecked bytes
  backend.system.verify
    (buildClaim selection.function input selection.success) proof

theorem verify_success {selection : Selection} {backend : Backend selection}
    {input : Array G} {bytes : ByteArray} (h : verify backend input bytes = .ok ()) :
    input.size = selection.inputSize ∧
      ∃ proof, Proof.ofBytesChecked bytes = .ok proof ∧
        backend.system.verify
          (buildClaim selection.function input selection.success) proof = .ok () := by
  unfold verify at h
  split at h
  · cases h
  · rename_i ha
    refine ⟨by simpa using ha, ?_⟩
    cases hp : Proof.ofBytesChecked bytes with
    | error e => simp [hp, bind, Except.bind] at h
    | ok proof => exact ⟨proof, rfl, by simpa [hp, bind, Except.bind] using h⟩

/-- Every produced backend retains the actual compiler artifact, including
the grouping result. No compiler-semantic claim is packed into this result. -/
theorem Backend.compilation_stages {selection : Selection} (backend : Backend selection) :
    ∃ initial, selection.source.compile = .ok initial ∧
      (if selection.groups.isEmpty then .ok initial
        else initial.groupFunctions selection.groups) = .ok backend.compiled := by
  have h := backend.compilation
  unfold Selection.compile at h
  cases hc : selection.source.compile with
  | error e => simp [hc, bind, Except.bind] at h
  | ok initial => exact ⟨initial, rfl, by simpa [hc, bind, Except.bind, pure, Except.pure] using h⟩

end Aiur.BoundVerifier
