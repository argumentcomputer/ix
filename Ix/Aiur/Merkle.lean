/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Blake3
import Ix.Aiur.MerkleCap

/-! Binary MMCS paths for verifier-selected power-of-two matrix heights.
Rows at the same height retain their original matrix order. Every ordinary
BLAKE3 input is retained, including both hashes around a shorter-row
injection. Shared, pruned openings are a separate verification algorithm.
-/

namespace Aiur.NativeAIR.Merkle

abbrev Digest := Blake3.Digest
abbrev Hash := List UInt8 → Digest

structure Dimensions where
  width : Nat
  logHeight : Nat
  deriving DecidableEq, Repr

def maxHeight (dimensions : List Dimensions) : Nat :=
  MerkleCap.maxDegree (dimensions.map Dimensions.logHeight)

def shape : List Dimensions → List (List G) → Bool
  | [], [] => true
  | dimension :: dimensions, row :: rows => row.length == dimension.width && shape dimensions rows
  | _, _ => false

def hasHeight (dimensions : List Dimensions) (height : Nat) : Bool :=
  dimensions.any fun dimension => dimension.logHeight == height

def rowsAt : List Dimensions → List (List G) → Nat → List (List G)
  | dimension :: dimensions, row :: rows, height =>
    if dimension.logHeight = height then row :: rowsAt dimensions rows height
    else rowsAt dimensions rows height
  | _, _, _ => []

def rowBytes (dimensions : List Dimensions) (rows : List (List G)) (height : Nat) : List UInt8 :=
  Transcript.fieldsBytes (rowsAt dimensions rows height).flatten

def pairBytes (left right : Digest) : List UInt8 := left.toList ++ right.toList

def branchBytes (index : Nat) (current sibling : Digest) : List UInt8 :=
  if index % 2 = 0 then pairBytes current sibling else pairBytes sibling current

structure Hashing where
  digest : Digest
  inputs : List (List UInt8)
  deriving DecidableEq, Repr

/-- `height` is the next layer, after pairing the current node and sibling. -/
def step (hash : Hash) (dimensions : List Dimensions) (rows : List (List G))
    (height index : Nat) (current sibling : Digest) : Hashing :=
  let input := branchBytes index current sibling
  let parent := hash input
  if hasHeight dimensions height then
    let leaf := rowBytes dimensions rows height
    let inject := pairBytes parent (hash leaf)
    ⟨hash inject, [input, leaf, inject]⟩
  else ⟨parent, [input]⟩

def walk (hash : Hash) (dimensions : List Dimensions) (rows : List (List G))
    (height index : Nat) (current : Digest) : List Digest → Hashing
  | [] => ⟨current, []⟩
  | sibling :: proof =>
    let first := step hash dimensions rows (height - 1) index current sibling
    let rest := walk hash dimensions rows (height - 1) (index / 2) first.digest proof
    ⟨rest.digest, first.inputs ++ rest.inputs⟩

structure Replay where
  logHeight : Nat
  index : Nat
  hashing : Hashing
  deriving DecidableEq, Repr

/-- Structural failure precedes hashing, as in native individual verification.
The raw replay preserves the native omission of rows below the cap. -/
def replay (hash : Hash) (dimensions : List Dimensions) (capHeight index : Nat)
    (rows : List (List G)) (proof : List Digest) : Option Replay :=
  let height := maxHeight dimensions
  if dimensions.isEmpty || !shape dimensions rows ||
      proof.length != height - capHeight || !(index < 2^height) then none
  else
    let leaf := rowBytes dimensions rows height
    let result := walk hash dimensions rows height index (hash leaf) proof
    some ⟨height - proof.length, index / 2^proof.length, ⟨result.digest, leaf :: result.inputs⟩⟩

def accepts (cap : List Digest) (result : Replay) : Bool :=
  cap[result.index]? == some result.hashing.digest

def verify (hash : Hash) (dimensions : List Dimensions) (capHeight index : Nat)
    (cap : List Digest) (rows : List (List G)) (proof : List Digest) : Bool :=
  match replay hash dimensions capHeight index rows proof with
  | none => false
  | some result => accepts cap result

def covered (dimensions : List Dimensions) (capHeight : Nat) : Bool :=
  MerkleCap.coverage 0 capHeight (dimensions.map Dimensions.logHeight)

def verifyCovered (hash : Hash) (dimensions : List Dimensions) (capHeight index : Nat)
    (cap : List Digest) (rows : List (List G)) (proof : List Digest) : Bool :=
  covered dimensions capHeight && verify hash dimensions capHeight index cap rows proof

/-- A collision among the inputs actually queried by these replays. This is
finite and gives an explicit witness; it does not assert global injectivity. -/
def CollisionOn (hash : Hash) (inputs : List (List UInt8)) : Prop :=
  ∃ left ∈ inputs, ∃ right ∈ inputs, left ≠ right ∧ hash left = hash right

end Aiur.NativeAIR.Merkle
