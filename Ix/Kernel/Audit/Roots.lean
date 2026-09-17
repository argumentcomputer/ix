/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel
import Ix.Kernel.Audit.Axioms
import Ix.Kernel.Audit.Imports
import Ix.Kernel.Audit.Runtime

/-! # The required roots and their frozen boundaries

This module is the certified gate's manifest. It fails elaboration when

* a public root is missing or its exact axiom set differs from the standard
  logical axioms (`propext`, `Classical.choice`, `Quot.sound`);
* the executable entry points depend on any axiom at all;
* the import closure of `Ix.Kernel` leaves the allowlisted module prefixes;
* execution of the public operations reaches an `@[extern]`,
  `implemented_by`, `unsafe`, or `csimp` replacement outside Lean's own
  runtime modules;
* the statement of a public theorem changes, since the expected `#check`
  output is frozen below.

Expected values were measured before being frozen (K0, 2026-09-17). Every
change to a frozen value is a deliberate, explained update. The one inherited
extern reached at K0 is `Nat.decEq`, through decidable equality of member
indices in `ConstRef`. -/

open Lean

namespace Ix.Kernel.Audit

/-- The public theorems. -/
def publicRoots : Array Name :=
  #[``Ix.Kernel.check_has_model, ``Ix.Kernel.checkDecls_has_model, ``Ix.Kernel.no_proof_of_False]

/-- The executable operations whose runtime closure is audited. -/
def publicOperations : Array Name :=
  #[``Ix.Kernel.check, ``Ix.Kernel.checkDecls, ``Ix.Kernel.checkDecl,
    ``Ix.Kernel.Env.lookup, ``Ix.Kernel.Env.toEnvironment]

/-- Module prefixes the certified import closure may use. `Lean` and
`Batteries` are reached through `Batteries.Data.List.Basic` (for
`List.Forall₂`) and the `Lean.Level` import of `VLevelLemmas`; trimming them is
a recorded follow-up. Nothing else under `Ix`, and no `Blake3`, `LSpec`, `Cli`,
or `lean4lean` module, may enter. -/
def importAllowlist : Array Name :=
  #[`Init, `Std, `Lean, `Batteries, `Ix.Kernel, `Ix.Address.Core]

/-- Modules whose execution replacements are inherited Lean runtime. -/
def runtimeAllowlist : Array Name := #[`Init, `Std]

end Ix.Kernel.Audit

/-! ## Axiom boundaries -/

#guard_kernel_axioms Ix.Kernel.check_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.check []
#guard_kernel_axioms Ix.Kernel.checkDecls []
#guard_kernel_axioms Ix.Kernel.Env.toEnvironment []

/-! ## Import and runtime closures -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Kernel] Ix.Kernel.Audit.importAllowlist

/-- info: runtime closure of [Ix.Kernel.check, Ix.Kernel.checkDecls, Ix.Kernel.checkDecl,
Ix.Kernel.Env.lookup, Ix.Kernel.Env.toEnvironment]: 110 constants; inherited externs 1,
implemented_by 0, unsafe 0, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.publicOperations Ix.Kernel.Audit.runtimeAllowlist

/-! ## Frozen statements -/

/-- info: @Ix.Kernel.check_has_model : ∀ {β : Type u_1} [inst : DecidableEq β] (V : Type u_2)
  [inst_1 : Ix.Kernel.Model.SetTheory V] {cfg : Ix.Kernel.Config} {decls : List (Ix.Kernel.Decl β)}
  {env : Ix.Kernel.Env β}, Ix.Kernel.check cfg decls = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.check_has_model

/-- info: @Ix.Kernel.checkDecls_has_model : ∀ {β : Type u_1} [inst : DecidableEq β] (V : Type u_2)
  [inst_1 : Ix.Kernel.Model.SetTheory V] {cfg : Ix.Kernel.Config} {env env' : Ix.Kernel.Env β}
  {decls : List (Ix.Kernel.Decl β)} (m : Ix.Kernel.Model V env),
  Ix.Kernel.checkDecls cfg env decls = Except.ok env' → Nonempty (Ix.Kernel.Model V env') -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.checkDecls_has_model

/-- info: @Ix.Kernel.no_proof_of_False : ∀ {β : Type u_1} [inst : DecidableEq β] (V : Type u_2) [Ix.Kernel.Model.SetTheory V]
  {cfg : Ix.Kernel.Config} {decls : List (Ix.Kernel.Decl β)} {env : Ix.Kernel.Env β},
  Ix.Kernel.check cfg decls = Except.ok env →
    ∀ {r : Ix.Kernel.ConstRef β} {entry : Ix.Kernel.Model.ConstantEntry β},
      env.toEnvironment r = some entry → env.EmptyType entry.universes entry.type → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.no_proof_of_False
