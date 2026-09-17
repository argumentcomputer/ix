/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Env
import Ix.Kernel.Const

/-! # The declaration checker

The executable entry points of the kernel. `checkDecl` checks one declaration
against the environment; `checkDecls` folds it over a list in the supplied
order; `check` starts from the empty environment. Every accepting run has the
model constructed in `Ix.Kernel.Consistency`.

Outcomes are accept (`.ok`), reject (`Error.rejected`: the input is wrong),
and decline (`Error.declined`: the kernel does not support the input and says
why). Only accept carries the theorems.

At milestone K0 the kernel supports no declaration form: `checkDecl` declines
every input. Each later milestone adds forms while the public theorems keep
their statements. -/

namespace Ix.Kernel

universe u

/-- Kernel configuration. -/
structure Config where
  /-- Fuel for reduction, inference, and conversion; exhaustion declines. -/
  fuel : Nat := 100000
  deriving Repr

/-- Non-accepting outcomes. -/
inductive Error where
  /-- The input is wrong. -/
  | rejected (reason : String)
  /-- The kernel does not support the input. -/
  | declined (reason : String)
  deriving Repr, DecidableEq

/-- An input declaration: a block of constants at its address. -/
structure Decl (β : Type u) where
  address : β
  block : Block β

variable {β : Type u} [DecidableEq β]

/-- Check one declaration against the environment. -/
def checkDecl (_cfg : Config) (_env : Env β) (_d : Decl β) : Except Error (Env β) :=
  .error (.declined "no declaration form is supported yet")

/-- The closed fold: check declarations in the supplied order, each against the
environment the earlier ones built. -/
def checkDecls (cfg : Config) (env : Env β) : List (Decl β) → Except Error (Env β)
  | [] => .ok env
  | d :: ds => do
    let env ← checkDecl cfg env d
    checkDecls cfg env ds

/-- The closed entry point: check declarations from the empty environment. -/
def check (cfg : Config) (decls : List (Decl β)) : Except Error (Env β) :=
  checkDecls cfg Env.empty decls

end Ix.Kernel
