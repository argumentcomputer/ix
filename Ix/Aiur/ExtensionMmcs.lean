/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.PrunedMerkle
import Ix.Aiur.ProofCodec

/-! The native quadratic-extension MMCS adapter. Coordinates are flattened
in basis order, and dimensions retain their heights. Width multiplication
models release-mode machine arithmetic; `WidthsFit` states when it agrees
with mathematical doubling and the original extension-row shape.
-/

namespace Aiur.NativeAIR.ExtensionMmcs

open Merkle (Digest Hash Dimensions)
open ProofCodec (Extension)

def baseRow (values : List Extension) : List G :=
  values.flatMap fun value => [value.c0, value.c1]

def baseRows (rows : List (List Extension)) : List (List G) := rows.map baseRow

def baseDimensions (wordBits : Nat) (dimensions : List Dimensions) : List Dimensions :=
  dimensions.map fun dimension =>
    { dimension with width := (dimension.width * 2) % 2^wordBits }

def WidthsFit (wordBits : Nat) (dimensions : List Dimensions) : Prop :=
  ∀ dimension ∈ dimensions, dimension.width * 2 < 2^wordBits

def shape : List Dimensions → List (List Extension) → Bool
  | [], [] => true
  | dimension :: dimensions, row :: rows => row.length == dimension.width && shape dimensions rows
  | _, _ => false

def replay (hash : Hash) (wordBits : Nat) (dimensions : List Dimensions) (capHeight index : Nat)
    (rows : List (List Extension)) (proof : List Digest) : Option Merkle.Replay :=
  Merkle.replay hash (baseDimensions wordBits dimensions) capHeight index (baseRows rows) proof

def verify (hash : Hash) (wordBits : Nat) (dimensions : List Dimensions) (capHeight index : Nat)
    (cap : List Digest) (rows : List (List Extension)) (proof : List Digest) : Bool :=
  Merkle.verify hash (baseDimensions wordBits dimensions) capHeight index cap (baseRows rows) proof

def verifyCovered (hash : Hash) (wordBits : Nat) (dimensions : List Dimensions) (capHeight index : Nat)
    (cap : List Digest) (rows : List (List Extension)) (proof : List Digest) : Bool :=
  Merkle.covered dimensions capHeight && verify hash wordBits dimensions capHeight index cap rows proof

def replayMulti (hash : Hash) (wordBits : Nat) (dimensions : List Dimensions) (capHeight : Nat)
    (indices : List Nat) (rows : List (List (List Extension))) (proof : List Digest) :
    PrunedMerkle.Logged (List PrunedMerkle.Node) :=
  PrunedMerkle.replay hash (baseDimensions wordBits dimensions) capHeight indices (rows.map baseRows) proof

def verifyMulti (hash : Hash) (wordBits : Nat) (dimensions : List Dimensions) (capHeight : Nat)
    (indices : List Nat) (cap : List Digest) (rows : List (List (List Extension))) (proof : List Digest) : Bool :=
  PrunedMerkle.verify hash (baseDimensions wordBits dimensions) capHeight indices cap (rows.map baseRows) proof

def verifyMultiCovered (hash : Hash) (wordBits : Nat) (dimensions : List Dimensions) (capHeight : Nat)
    (indices : List Nat) (cap : List Digest) (rows : List (List (List Extension))) (proof : List Digest) : Bool :=
  Merkle.covered dimensions capHeight && verifyMulti hash wordBits dimensions capHeight indices cap rows proof

end Aiur.NativeAIR.ExtensionMmcs
