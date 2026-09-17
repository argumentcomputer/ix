/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Address.Core
import Ix.Kernel.Model
import Ix.Kernel.Env
import Ix.Kernel.Check
import Ix.Kernel.Consistency

/-! # Ix.Kernel

The certified kernel: a reference type checker for Ixon-shaped declarations
with a machine-checked theorem that every environment it accepts has a model
in an explicit set theory, and therefore contains no proof of `False`.

* `Ix.Kernel.check` and `Ix.Kernel.checkDecls` (`Ix.Kernel.Check`) are the
  executable entry points.
* `Ix.Kernel.check_has_model`, `Ix.Kernel.checkDecls_has_model`, and
  `Ix.Kernel.no_proof_of_False` (`Ix.Kernel.Consistency`) are the public
  theorems.
* `Ix.Kernel.Model` is the set-theoretic model those theorems are stated in.

The kernel is parametric in the reference type `β`; the public instantiation
uses `Address` (`Ix.Address.Core`), an opaque 32-byte key. The kernel never
hashes: the binding between bytes and addresses is a host property, stated
explicitly where a claim needs it.

The executables carry their model extension as an erased proof component,
so they take the universe `v` of the set theories the attached theorems
speak about (`check.{u,v}`). The computation does not depend on `v`; a use
site that is not a theorem instantiates it. `checkAddressed` fixes `v := 1`,
the universe of the `ZFSet.{0}` model supplied by `Models/SetTheory`.

Roadmap: `plans/ix-certified-roadmap.md`. -/

namespace Ix.Kernel

/-- The public instantiation of the closed check at content addresses. -/
abbrev checkAddressed (cfg : Config) (decls : List (Decl Address)) : Except Error (Env Address) :=
  check.{0,1} cfg decls

end Ix.Kernel
