/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

module
public import Ix.Aiur.Stages.Bytecode

/-! Ungated lookup messages require one writer per physical slot. A single
selector does not ensure that: a branch with no terminal can still emit
lookups. Restrict the optimization to one function with terminal control. -/

public section
@[expose] section
namespace Aiur.Bytecode

def Function.hasTerminalControl (function : Function) : Bool :=
  match function.body.ctrl with
  | .«return» .. | .yield .. => true
  | _ => false

def circuitBranchless (selectors : Nat) (functions : List Function) : Bool :=
  selectors == 1 && match functions with
    | [function] => function.hasTerminalControl
    | _ => false

end Aiur.Bytecode
