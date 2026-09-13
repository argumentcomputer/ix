/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.CompiledVerifier
import Ix.Aiur.ProofShape

/-! The selected compiled key determines proof framing, active opening
dimensions, fixed trace heights and the lookup budget before native
verification. This still delegates the transcript/PCS/AIR acceptance checks
to the existing FFI and does not instantiate a certified checker release. -/

namespace Aiur.BoundVerifier

structure CheckedProof (key : NativeAIR.KeyCodec.Key) (bytes : ByteArray) where
  data : NativeAIR.ProofCodec.Data
  rows : List NativeAIR.ProofShape.Row
  bound : Nat
  decoded : NativeAIR.ProofCodec.decodeCanonical bytes = some data
  shape : NativeAIR.ProofShape.check key data = some rows
  fixed : NativeAIR.ProofShape.fixedHeights key data = true
  budget : NativeAIR.ProofShape.queryBound key data = some bound

def readProof (key : NativeAIR.KeyCodec.Key) (bytes : ByteArray) : Except String (CheckedProof key bytes) :=
  match parsed : NativeAIR.ProofCodec.decodeCanonical bytes with
  | none => .error "proof is not a canonical complete artifact"
  | some data =>
    match shape : NativeAIR.ProofShape.check key data with
    | none => .error "proof opening shape differs from the selected key"
    | some rows =>
      if fixed : NativeAIR.ProofShape.fixedHeights key data = true then
        match budget : NativeAIR.ProofShape.queryBound key data with
        | none => .error "proof lookup budget exceeds its bound"
        | some bound => .ok ⟨data, rows, bound, parsed, shape, fixed, budget⟩
      else .error "proof fixed table heights differ from the selected key"

def verifyShaped {selection : Selection} (backend : CompiledBackend selection)
    (input : Array G) (bytes : ByteArray) : Except String Unit := do
  let _ ← readProof backend.keyData bytes
  verifyCompiled backend input bytes

theorem verifyShaped_success {selection : Selection} {backend : CompiledBackend selection}
    {input : Array G} {bytes : ByteArray} (accepted : verifyShaped backend input bytes = .ok ()) :
    ∃ checked : CheckedProof backend.keyData bytes, readProof backend.keyData bytes = .ok checked ∧
      verifyCompiled backend input bytes = .ok () := by
  unfold verifyShaped at accepted
  cases parsed : readProof backend.keyData bytes with
  | error message => simp [parsed, bind, Except.bind] at accepted
  | ok checked => exact ⟨checked, rfl, by simpa [parsed, bind, Except.bind] using accepted⟩

end Aiur.BoundVerifier
