/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.BoundVerifier
import Ix.Aiur.CompiledKey

/-! Enforce equality between the selected native key and the complete checked
circuit model. This strengthens program/key binding; native acceptance,
preprocessed commitment meaning and certified source soundness remain open. -/

namespace Aiur.BoundVerifier

structure CompiledBackend (selection : Selection) extends Backend selection where
  graphsChecked : NativeAIR.CompiledKey.check compiled.bytecode keyData = true

def buildCompiled (selection : Selection) : Except String (CompiledBackend selection) := do
  let backend ← build selection
  if checked : NativeAIR.CompiledKey.check backend.compiled.bytecode backend.keyData = true then
    return ⟨backend, checked⟩
  else throw "verification key circuits differ from the checked compilation"

def verifyCompiled {selection : Selection} (backend : CompiledBackend selection) (input : Array G)
    (bytes : ByteArray) : Except String Unit :=
  verify backend.toBackend input bytes

theorem CompiledBackend.circuits_bound {selection : Selection} (backend : CompiledBackend selection) :
    NativeAIR.CompiledKey.circuits backend.keyData.parameters.logBlowup backend.compiled.bytecode =
      some backend.keyData.circuits := by
  have checked := backend.graphsChecked
  simp only [NativeAIR.CompiledKey.check, Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.1

theorem CompiledBackend.preprocessed_indices {selection : Selection} (backend : CompiledBackend selection) :
    backend.keyData.preprocessedIndices = NativeAIR.CompiledKey.preprocessedIndices backend.compiled.bytecode := by
  have checked := backend.graphsChecked
  simp only [NativeAIR.CompiledKey.check, Bool.and_eq_true, beq_iff_eq] at checked
  exact checked.2

theorem verifyCompiled_success {selection : Selection} {backend : CompiledBackend selection}
    {input : Array G} {bytes : ByteArray} (accepted : verifyCompiled backend input bytes = .ok ()) :
    input.size = selection.inputSize ∧
      ∃ proof, Proof.ofBytesChecked bytes = .ok proof ∧
        backend.system.verify (buildClaim selection.function input selection.success) proof = .ok () :=
  verify_success accepted

end Aiur.BoundVerifier
