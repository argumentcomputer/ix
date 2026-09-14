/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Compiler.Dedup

namespace AiurTests.Dedup

open Aiur Aiur.Bytecode

def layout (inputs : Nat := 0) : FunctionLayout := ⟨inputs, 2, 8, 5⟩

def constant (n : Nat) (entry : Bool := false) : Function :=
  ⟨⟨#[.const (G.ofNat n)], .return 0 #[0]⟩, layout, entry, false⟩

def caller (target : Nat) (entry : Bool := false) : Function :=
  ⟨⟨#[.call target #[] 1 false], .return 0 #[0]⟩, layout, entry, false⟩

def program (functions : Array Function) : Toplevel := ⟨functions, #[1, 2, 10], #[], #[]⟩

/-- Two recursive functions form the same bisimulation class. Neither has
a finite successful execution; validation must still handle this syntax. -/
def mutualCycle : Toplevel := program #[caller 1 true, caller 0]

/-- A leaf difference propagates through successive refinement rounds. -/
def chains (depth : Nat) : Toplevel := Id.run do
  let mut functions := #[]
  for i in [:depth] do
    functions := functions ++ #[caller (2 * i + 2) (i == 0), caller (2 * i + 3) (i == 0)]
  return program (functions ++ #[constant 7, constant 9])

def continuation (target : Nat) (entry : Bool) : Function :=
  let yielded : Block := ⟨#[], .yield 0 #[1]⟩
  let returned : Block := ⟨#[], .return 0 #[0]⟩
  let cont : Block := ⟨#[.call target #[2] 1 false], .return 0 #[3]⟩
  ⟨⟨#[.const 7], .matchContinue 0 #[(0, yielded)] (some returned) 1 3 2 cont⟩,
    layout 1, entry, false⟩

/-- Zero takes a yielding arm and calls the continuation. Nonzero returns
from the function directly and must bypass that continuation. -/
def withContinuations : Toplevel :=
  let identity : Function := ⟨⟨#[], .return 0 #[0]⟩, layout 1, false, false⟩
  program #[continuation 2 true, continuation 3 false, identity, identity]

def fixtures : Array (String × Toplevel) := Id.run do
  let same := constant 7
  let mut cases := #[
    ("empty", program #[]),
    ("entry-union", program #[same, constant 7 true, same]),
    ("different-layouts", program #[same, { same with layout := layout 1 },
      { same with layout := { layout with auxiliaries := 9 } }]),
    ("mutual-cycle", mutualCycle),
    ("invalid-callee", program #[caller 999 true, caller 999]),
    ("continuations", withContinuations)]
  for depth in [:17] do cases := cases.push (s!"refinement-chain-{depth}", chains depth)
  return cases

end AiurTests.Dedup
