/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Model.Environment

/-! # The checked environment

`Env β` is the environment the kernel builds: installed entries in
installation order, keyed by `ConstRef β`. The semantic model reads it through
`Env.toEnvironment`, the `Model.Environment β` view (a partial function from
references to entries). `β` is the reference type; the public API fixes it to
`Address`, where an address is an opaque key: the kernel never hashes.

Installation order is the host-supplied dependency order. The checker rejects
a reference to an entry that is not yet installed and rejects a duplicate
reference, so acceptance needs neither an acyclicity proof nor a collision
assumption about addresses. -/

namespace Ix.Kernel

universe u

/-- The checked environment: entries in installation order, newest last. -/
structure Env (β : Type u) where
  entries : List (ConstRef β × Model.ConstantEntry β)

namespace Env

variable {β : Type u} [DecidableEq β]

/-- The empty environment, the starting point of the closed check. -/
def empty : Env β := ⟨[]⟩

/-- Look up an installed entry. Installation rejects duplicate references, so
the first match is the only match. -/
def lookup (env : Env β) (r : ConstRef β) : Option (Model.ConstantEntry β) :=
  (env.entries.find? fun e => e.1 == r).map (·.2)

/-- The semantic view of the environment read by the model. -/
def toEnvironment (env : Env β) : Model.Environment β := env.lookup

@[simp] theorem lookup_empty (r : ConstRef β) : (empty : Env β).lookup r = none := rfl

@[simp] theorem toEnvironment_empty (r : ConstRef β) :
    (empty : Env β).toEnvironment r = none := rfl

end Env

end Ix.Kernel
