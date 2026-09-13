/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Interpolation

/-! The native FRI query pass: reconstruct a row, fold it, then add at most
one reduced opening at the new height. Captured rows precede this addition.
The guards make the private native routine's caller preconditions explicit.
-/

namespace Aiur.NativeAIR.FriQuery

open ProofCodec (Extension)
open _root_.Aiur.NativeAIR.Quotient (horner)

def reconstruct (arity : Domain.Subgroup) (index : Nat) (value : R) (siblings : List R) : Option (List R) :=
  if siblings.length + 1 == Domain.size arity then
    some (siblings.insertIdx (index % Domain.size arity) value)
  else none

structure State where
  domain : Domain.Subgroup
  index : Nat
  value : Extension
  deriving DecidableEq, Repr

structure Round where
  arity : Domain.Subgroup
  challenge : Extension
  siblings : List Extension
  deriving DecidableEq, Repr

structure Row where
  domain : Domain.Subgroup
  index : Nat
  values : List Extension
  deriving DecidableEq, Repr

def roll (height : Nat) (factor value : Extension) : List (Nat × Extension) →
    Extension × List (Nat × Extension)
  | [] => (value, [])
  | (nextHeight, next) :: rest =>
    if nextHeight == height then (value + factor * next, rest)
    else (value, (nextHeight, next) :: rest)

structure StepResult where
  state : State
  remaining : List (Nat × Extension)
  row : Row
  deriving DecidableEq, Repr

def step (state : State) (round : Round) (openings : List (Nat × Extension)) : Option StepResult := do
  if round.arity.val == 0 || round.arity.val > state.domain.val then none
  else
    let child ← Domain.ofLogSize (state.domain.val - round.arity.val)
    let values ← reconstruct round.arity state.index state.value round.siblings
    let index := state.index / Domain.size round.arity
    let folded ← Interpolation.foldRow state.domain round.arity index values round.challenge
    let (value, remaining) := roll child.val (round.challenge.power (Domain.size round.arity)) folded openings
    return ⟨⟨child, index, value⟩, remaining, ⟨child, index, values⟩⟩

structure Result where
  state : State
  rows : List Row
  deriving DecidableEq, Repr

def walk (final : Domain.Subgroup) (state : State) (openings : List (Nat × Extension)) :
    List Round → Option Result
  | [] => if state.domain == final && openings.isEmpty then some ⟨state, []⟩ else none
  | round :: rest => do
    let result ← step state round openings
    let tail ← walk final result.state result.remaining rest
    return ⟨tail.state, result.row :: tail.rows⟩

def run (initial final : Domain.Subgroup) (index : Nat) (openings : List (Nat × Extension))
    (rounds : List Round) : Option Result := do
  if index ≥ Domain.size initial then none
  else match openings with
    | [] => none
    | (height, value) :: rest =>
      if height == initial.val then walk final ⟨initial, index, value⟩ rest rounds else none

def check (initial final : Domain.Subgroup) (index : Nat) (openings : List (Nat × Extension))
    (rounds : List Round) (finalPolynomial : List Extension) : Option Result := do
  let result ← run initial final index openings rounds
  if horner (Extension.ofBase (FriDomain.queryPoint initial result.state.index)) finalPolynomial == result.state.value then
    some result
  else none

end Aiur.NativeAIR.FriQuery
