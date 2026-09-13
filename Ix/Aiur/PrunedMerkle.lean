/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Merkle

/-! Binary shared MMCS replay. The verifier-selected indices determine the
sorted frontier and the exact boundary proof length. Logs survive rejection:
native group-consistency checks can fail after earlier hashes in the layer.
Reconstructed individual paths are retained for authentication proofs.
-/

namespace Aiur.NativeAIR.PrunedMerkle

open Merkle (Digest Hash Dimensions)

structure Logged (α : Type) where
  result : Option α
  inputs : List (List UInt8)
  deriving DecidableEq, Repr

def Logged.pure (value : α) : Logged α := ⟨some value, []⟩

def Logged.bind (first : Logged α) (next : α → Logged β) : Logged β :=
  match first.result with
  | none => ⟨none, first.inputs⟩
  | some value =>
    let rest := next value
    ⟨rest.result, first.inputs ++ rest.inputs⟩

instance : Monad Logged where
  pure := Logged.pure
  bind := Logged.bind

def reject : Logged α := ⟨none, []⟩

def ofOption (value : Option α) : Logged α := ⟨value, []⟩

def hashInput (hash : Hash) (input : List UInt8) : Logged Digest := ⟨some (hash input), [input]⟩

structure Ticket where
  index : Nat
  rows : List (List G)
  proof : List Digest
  deriving DecidableEq, Repr

def Ticket.extend (sibling : Digest) (ticket : Ticket) : Ticket :=
  { ticket with proof := ticket.proof ++ [sibling] }

structure Node where
  index : Nat
  digest : Digest
  tickets : List Ticket
  deriving DecidableEq, Repr

def uniqueIndices (indices : List Nat) : List Nat := (indices.mergeSort (· ≤ ·)).eraseDups

def parentIndices (indices : List Nat) : List Nat := (indices.map (· / 2)).eraseDups

/-- Each binary parent has two children; only uncovered children are sent. -/
def boundaryCount : Nat → List Nat → Nat
  | 0, _ => 0
  | steps + 1, indices =>
    let parents := parentIndices indices
    (2 * parents.length - indices.length) + boundaryCount steps parents

def representatives (indices : List Nat) (rows : List (List (List G))) : Option (List Ticket) :=
  let originals := indices.zip rows
  (uniqueIndices indices).mapM fun index => do
    let (_, values) ← originals.find? fun entry => entry.1 == index
    if originals.all (fun entry => entry.1 != index || entry.2 == values) then
      some ⟨index, values, []⟩
    else none

def initial (hash : Hash) (dimensions : List Dimensions) (height : Nat) : List Ticket → Logged (List Node)
  | [] => pure []
  | ticket :: tickets => do
    let digest ← hashInput hash (Merkle.rowBytes dimensions ticket.rows height)
    let rest ← initial hash dimensions height tickets
    return ⟨ticket.index, digest, [ticket]⟩ :: rest

/-- Pair every parent before injecting any shorter rows at this layer. -/
def combine (hash : Hash) : List Node → List Digest → Logged (List Node × List Digest)
  | [], proof => pure ([], proof)
  | first :: rest, proof =>
    match rest with
    | second :: tail =>
      if first.index % 2 = 0 ∧ second.index = first.index + 1 then do
        let digest ← hashInput hash (Merkle.pairBytes first.digest second.digest)
        let (nodes, remaining) ← combine hash tail proof
        let tickets := first.tickets.map (Ticket.extend second.digest) ++
          second.tickets.map (Ticket.extend first.digest)
        return (⟨first.index / 2, digest, tickets⟩ :: nodes, remaining)
      else do
        let sibling :: remaining := proof | reject
        let digest ← hashInput hash (Merkle.branchBytes first.index first.digest sibling)
        let (nodes, remaining) ← combine hash rest remaining
        return (⟨first.index / 2, digest, first.tickets.map (Ticket.extend sibling)⟩ :: nodes, remaining)
    | [] => do
      let sibling :: remaining := proof | reject
      let digest ← hashInput hash (Merkle.branchBytes first.index first.digest sibling)
      return ([⟨first.index / 2, digest, first.tickets.map (Ticket.extend sibling)⟩], remaining)

def inject (hash : Hash) (dimensions : List Dimensions) (height : Nat) : List Node → Logged (List Node)
  | [] => pure []
  | node :: nodes => do
    let lead :: members := node.tickets | reject
    if !(members.all fun ticket =>
        Merkle.rowsAt dimensions ticket.rows height == Merkle.rowsAt dimensions lead.rows height) then reject
    else
      let leaf ← hashInput hash (Merkle.rowBytes dimensions lead.rows height)
      let digest ← hashInput hash (Merkle.pairBytes node.digest leaf)
      let rest ← inject hash dimensions height nodes
      return { node with digest } :: rest

def walk (hash : Hash) (dimensions : List Dimensions) :
    Nat → Nat → List Node → List Digest → Logged (List Node × List Digest)
  | 0, _, nodes, proof => pure (nodes, proof)
  | steps + 1, height, nodes, proof => do
    let (parents, remaining) ← combine hash nodes proof
    let next ← if Merkle.hasHeight dimensions (height - 1) then
      inject hash dimensions (height - 1) parents else pure parents
    walk hash dimensions steps (height - 1) next remaining

def replay (hash : Hash) (dimensions : List Dimensions) (capHeight : Nat)
    (indices : List Nat) (rows : List (List (List G))) (proof : List Digest) : Logged (List Node) := do
  if dimensions.isEmpty || rows.length != indices.length then reject
  else
    let height := Merkle.maxHeight dimensions
    let steps := height - capHeight
    if !(indices.all fun index => index < 2^height) then reject
    else
      let tickets ← ofOption (representatives indices rows)
      if proof.length != boundaryCount steps (uniqueIndices indices) ||
          !(tickets.all fun ticket => Merkle.shape dimensions ticket.rows) then reject
      else
        let leaves ← initial hash dimensions height tickets
        let (nodes, remaining) ← walk hash dimensions steps height leaves proof
        if remaining.isEmpty then pure nodes else reject

def accepts (cap : List Digest) (nodes : List Node) : Bool :=
  nodes.all fun node => cap[node.index]? == some node.digest

def verify (hash : Hash) (dimensions : List Dimensions) (capHeight : Nat)
    (indices : List Nat) (cap : List Digest) (rows : List (List (List G))) (proof : List Digest) : Bool :=
  match (replay hash dimensions capHeight indices rows proof).result with
  | none => false
  | some nodes => accepts cap nodes

def verifyCovered (hash : Hash) (dimensions : List Dimensions) (capHeight : Nat)
    (indices : List Nat) (cap : List Digest) (rows : List (List (List G))) (proof : List Digest) : Bool :=
  Merkle.covered dimensions capHeight && verify hash dimensions capHeight indices cap rows proof

end Aiur.NativeAIR.PrunedMerkle
