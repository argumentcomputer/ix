/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ShapedVerifier
import Ix.Aiur.Proofs.ProofCodec
import Ix.Aiur.Proofs.ProofShape

/-! Shape and framing facts follow from the bytes accepted by the actual
checked wrapper. Native transcript/PCS/AIR correctness remains to be proved. -/

namespace Aiur.BoundVerifier

theorem CheckedProof.framing {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) :
    NativeAIR.ProofCodec.readData bytes.data.toList = some (checked.data, []) ∧
      NativeAIR.ProofCodec.encode checked.data = bytes := by
  obtain ⟨decoded, encoded⟩ := NativeAIR.ProofCodec.decodeCanonical_success checked.decoded
  exact ⟨NativeAIR.ProofCodec.decode_success decoded, encoded⟩

theorem CheckedProof.wire_bounds {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) : NativeAIR.ProofCodec.DataFits checked.data :=
  NativeAIR.ProofCodec.decode_fits (NativeAIR.ProofCodec.decodeCanonical_success checked.decoded).1

theorem CheckedProof.row {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) {position : Nat} {row : NativeAIR.ProofShape.Row}
    (present : checked.rows[position]? = some row) :
    checked.data.active[row.circuitIndex]? = some true ∧
      row.Sourced key checked.data row.circuitIndex position ∧ row.Fits key.parameters := by
  obtain ⟨index, _, sourced, fits⟩ := NativeAIR.ProofShape.check_row checked.shape present
  exact ⟨NativeAIR.ProofShape.check_row_active checked.shape present, sourced.index_eq ▸ sourced, fits⟩

theorem CheckedProof.nonempty {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) : checked.rows ≠ [] :=
  NativeAIR.ProofShape.check_nonempty checked.shape

theorem CheckedProof.fixed_heights {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) :
    FixedTraceHeights (key.circuits.map (·.preprocessedHeight)) checked.data.active
      (checked.data.logDegrees.map UInt8.toNat) :=
  NativeAIR.ProofShape.fixedHeights_sound checked.fixed

theorem CheckedProof.lookup_budget {key : NativeAIR.KeyCodec.Key} {bytes : ByteArray}
    (checked : CheckedProof key bytes) :
    ∃ total, lookupSlotSum (key.circuits.map (·.graph.lookups.length)) checked.data.active
      (checked.data.logDegrees.map UInt8.toNat) = some total ∧
      checked.bound = 1 + total ∧ checked.bound < gSize.toNat :=
  NativeAIR.ProofShape.queryBound_sound checked.budget

theorem verifyShaped_acceptance {selection : Selection} {backend : CompiledBackend selection}
    {input : Array G} {bytes : ByteArray} (accepted : verifyShaped backend input bytes = .ok ()) :
    input.size = selection.inputSize ∧
      ∃ (checked : CheckedProof backend.keyData bytes) (native : Proof),
        readProof backend.keyData bytes = .ok checked ∧ Proof.ofBytesChecked bytes = .ok native ∧
        backend.system.verify (buildClaim selection.function input selection.success) native = .ok () := by
  obtain ⟨checked, parsed, verified⟩ := verifyShaped_success accepted
  obtain ⟨arity, native, decoded, checkedNative⟩ := verifyCompiled_success verified
  exact ⟨arity, checked, native, parsed, decoded, checkedNative⟩

end Aiur.BoundVerifier
