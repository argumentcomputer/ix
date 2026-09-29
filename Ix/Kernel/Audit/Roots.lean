/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel
import Ix.Ixon.Types
import Ix.Kernel.Audit.Axioms
import Ix.Kernel.Audit.Imports
import Ix.Kernel.Audit.Runtime

/-! # The required roots and their frozen boundaries

This module is the certified gate's manifest. It fails elaboration when

* a public root is missing or its exact axiom set differs from the standard
  logical axioms (`propext`, `Classical.choice`, `Quot.sound`);
* an executable entry point depends on any axiom beyond those three, which
  enter it only through the erased proof components it carries (the model
  extension of each accepted declaration); Lean's compiler separately
  guarantees that no axiom sits in a computational position, since the
  entry points compile;
* the import closure of `Ix.Kernel` leaves the allowlisted module prefixes;
* the compiled code of the public operations reaches an `@[extern]`,
  `implemented_by`, `unsafe`, or `csimp` replacement outside Lean's own
  runtime modules;
* the statement of a public theorem changes, since the expected `#check`
  output is frozen below.

Expected values were measured before being frozen (K0 to K2, 2026-09-17).
Every change to a frozen value is a deliberate, explained update. The
inherited replacements reached at K2 are `Nat` arithmetic and comparison
(`Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.decEq`, `Nat.decLt`) on fuel, de Bruijn
indices, universe parameter indices, level normal forms, and rule positions,
and the `Array`-backed tail-recursive implementations Lean substitutes for
`List.zipIdx` and `List.flatMap` (`Array.mk`, `Array.mkEmpty`, `Array.push`,
`Array.size`, `Array.toList`, `USize.decEq`, `USize.ofNat`, `USize.sub`, and
the one `unsafe` declaration, `Array.ugetBorrowed`), which the inductive
route uses to number constructors and publish rule facts. The quotient and
standard-axiom routes (K2) grow the closure with the decidable interface
checks, the generated primitive types, and the derived rule endpoints, and
reach no further replacement. P01 (2026-09-29) retains structured failure
causes and adds `String.append` for contextual diagnostics and `Nat.decLe`
for an out-of-range projection diagnostic. Both are inherited from `Init`;
the axiom, import, and replacement allowlists are unchanged. P03 adds the
`checkAgainst` helper to the compiled closure (899 → 900 functions), reusing
expected-type formation while keeping the same inherited replacements. K3
adds family-only admission and a shared optional-recursor stage for Nat and
structure facts (900 → 920 functions), with the same replacements. -/

open Lean

namespace Ix.Kernel.Audit

/-- The public theorems. -/
def publicRoots : Array Name :=
  #[``Ix.Kernel.check_has_model, ``Ix.Kernel.checkDecls_has_model, ``Ix.Kernel.no_proof_of_False]

/-- Fidelity complements the frozen model-existence roots. -/
def fidelityRoots : Array Name :=
  #[``Ix.Kernel.annotate_erase, ``Ix.Kernel.checkDecl_installed, ``Ix.Kernel.checkDecls_installed,
    ``Ix.Kernel.check_installed, ``Ix.Kernel.checkDecl_preserves, ``Ix.Kernel.checkDecls_preserves]

/-- The executable operations whose runtime closure is audited. -/
def publicOperations : Array Name :=
  #[``Ix.Kernel.check, ``Ix.Kernel.checkDecls, ``Ix.Kernel.checkDecl,
    ``Ix.Kernel.Env.lookup, ``Ix.Kernel.Env.toEnvironment]

/-- K3's Ixon entry points additionally reach Lean's byte/array access and
UInt conversions and physical declaration association. Their separate closure
is frozen below: 961 functions,
23 inherited externs, and two inherited unsafe array accessors. -/
def ingressOperations : Array Name :=
  #[``Ix.Kernel.checkEnv, ``Ix.Kernel.Ingress.readExpr,
    ``Ix.Kernel.Ingress.readBlock, ``Ix.Kernel.Ingress.reference]

/-- Module prefixes the certified import closure may use: Lean core, the
kernel itself, the pure address key, and the pure Ixon types. Measured after the K0 import trim,
the closure of `Ix.Kernel` has 690 modules, all under `Init` except the
kernel's own and `Ix.Address.Core`. K3 also checks the pure Ixon types independently. No `Std`, `Lean`, or `Batteries` module,
nothing else under `Ix`, and no `Blake3`, `LSpec`, `Cli`, or `lean4lean`
module may enter. -/
def importAllowlist : Array Name := #[`Init, `Ix.Kernel, `Ix.Address.Core, `Ix.Ixon.Types]

/-- Modules whose execution replacements are inherited Lean runtime. -/
def runtimeAllowlist : Array Name := #[`Init, `Std]

end Ix.Kernel.Audit

/-! ## Axiom boundaries -/

#guard_kernel_axioms Ix.Kernel.check_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.check [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Env.toEnvironment []
#guard_kernel_axioms Ix.Kernel.annotate_erase [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecl_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.check_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecl_preserves [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls_preserves [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.readExpr_reading [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.readBlock_reading [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.ExprReads.deterministic [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.readExpr_agree [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.Installed.primary [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkFamilyC [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv [propext, Classical.choice, Quot.sound]

/-! ## Import and runtime closures -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Kernel, `Ix.Ixon.Types] Ix.Kernel.Audit.importAllowlist

/-- info: runtime closure of [Ix.Kernel.check, Ix.Kernel.checkDecls, Ix.Kernel.checkDecl,
Ix.Kernel.Env.lookup, Ix.Kernel.Env.toEnvironment]: 920 compiled functions; inherited externs 16,
implemented_by 0, unsafe 1, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.publicOperations Ix.Kernel.Audit.runtimeAllowlist

/-- info: runtime closure of [Ix.Kernel.checkEnv, Ix.Kernel.Ingress.readExpr,
Ix.Kernel.Ingress.readBlock, Ix.Kernel.Ingress.reference]: 961 compiled functions;
inherited externs 23, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.ingressOperations Ix.Kernel.Audit.runtimeAllowlist

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
