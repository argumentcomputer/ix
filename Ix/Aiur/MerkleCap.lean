/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ProofShape

/-! A binary MMCS cap must retain every matrix injection. Heights here are
logarithms of power-of-two row counts. Subtracting the common LDE blowup
before comparing avoids machine addition overflow in the native guard.
-/

namespace Aiur.NativeAIR.MerkleCap

def maxDegree (degrees : List Nat) : Nat := degrees.foldr max 0

def coverage (logBlowup capHeight : Nat) (degrees : List Nat) : Bool :=
  let effective := min (capHeight - logBlowup) (maxDegree degrees)
  degrees.all fun degree => effective ≤ degree

def check (key : KeyCodec.Key) (proof : ProofCodec.Data) : Bool :=
  coverage key.parameters.logBlowup key.parameters.capHeight (proof.logDegrees.map UInt8.toNat)

end Aiur.NativeAIR.MerkleCap
