/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ProofCodec

/-! Total replay of the pinned byte-hash / serializing Goldilocks challenger.
The hash is an explicit 32-byte function. The pending buffer is stored in
sampling order, the reverse of the native vector. Rejection sampling uses
explicit fuel; exhaustion rejects without returning a fabricated sample.
-/

namespace Aiur.NativeAIR.Challenger

abbrev Hash32 := List UInt8 → Fin 32 → UInt8

structure State where
  input : List UInt8
  pending : List UInt8
  deriving DecidableEq, Repr

def initial (seed : List UInt8) : State := ⟨seed, []⟩

def observeByte (state : State) (byte : UInt8) : State :=
  ⟨state.input ++ [byte], []⟩

/-- Empty slices perform no byte observations and preserve pending output. -/
def observeBytes (state : State) (bytes : List UInt8) : State :=
  if bytes.isEmpty then state else ⟨state.input ++ bytes, []⟩

def observeField (state : State) (value : G) : State :=
  observeBytes state (ProofCodec.encodeField value)

def observeExtension (state : State) (value : ProofCodec.Extension) : State :=
  observeField (observeField state value.c0) value.c1

/-- Caps are observed as digest bytes, without a vector length prefix. -/
def observeCap (state : State) (cap : KeyCodec.MerkleCap) : State :=
  observeBytes state cap.flatten

def sampleByte (hash : Hash32) (state : State) : UInt8 × State :=
  match state.pending with
  | byte :: rest => (byte, ⟨state.input, rest⟩)
  | [] =>
    let digest := hash state.input
    (digest 31, ⟨List.ofFn digest, (List.ofFn digest).reverse.drop 1⟩)

def sampleBytes (hash : Hash32) : Nat → State → List UInt8 × State
  | 0, state => ([], state)
  | count + 1, state =>
    let (byte, next) := sampleByte hash state
    let (rest, final) := sampleBytes hash count next
    (byte :: rest, final)

def littleEndian (bytes : List UInt8) : Nat :=
  bytes.foldr (fun byte rest => byte.toNat + 256 * rest) 0

def sampleWord (hash : Hash32) (state : State) : Nat × State :=
  let (bytes, next) := sampleBytes hash 8 state
  (littleEndian bytes, next)

def sampleField (hash : Hash32) : Nat → State → Option (G × State)
  | 0, _ => none
  | fuel + 1, state =>
    let (word, next) := sampleWord hash state
    if word < gSize.toNat then some (G.ofNat word, next)
    else sampleField hash fuel next

/-- Each basis coordinate has its own rejection-sampling budget. -/
def sampleExtension (hash : Hash32) (fuel : Nat) (state : State) :
    Option (ProofCodec.Extension × State) := do
  let (c0, next) ← sampleField hash fuel state
  let (c1, final) ← sampleField hash fuel next
  return (⟨c0, c1⟩, final)

def sampleBits (hash : Hash32) (bits : Nat) (state : State) : Option (Nat × State) :=
  if bits < 64 ∧ 2^bits < gSize.toNat then
    let (word, next) := sampleWord hash state
    some (word % 2^bits, next)
  else none

/-- Unlike zero-bit sampling, a zero-bit witness check consumes nothing. -/
def checkWitness (hash : Hash32) (bits : Nat) (witness : G) (state : State) :
    Option (Bool × State) := do
  if bits = 0 then return (true, state)
  else
    let (value, next) ← sampleBits hash bits (observeField state witness)
    return (value == 0, next)

end Aiur.NativeAIR.Challenger
