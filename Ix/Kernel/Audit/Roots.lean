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
is frozen below: 962 functions,
23 inherited externs, and two inherited unsafe array accessors. Factoring
`referenceSource` for the egress projection check adds one function. -/
def ingressOperations : Array Name :=
  #[``Ix.Kernel.checkEnv, ``Ix.Kernel.Ingress.readExpr,
    ``Ix.Kernel.Ingress.readBlock, ``Ix.Kernel.Ingress.reference]

/-- Exact layout-preserving readers/writers, independent of admission.
The measured closure has 202 functions, 21 inherited externs, and two
inherited unsafe array accessors. It additionally uses `UInt64.ofNat` to
reconstruct bounded indexes and metadata, with an explicit overflow check.
It reaches no project execution replacement, hashing, or host codec. -/
def egressOperations : Array Name :=
  #[``Ix.Kernel.Egress.readRecords, ``Ix.Kernel.Egress.writeRecords,
    ``Ix.Kernel.Egress.writeExpr, ``Ix.Kernel.Egress.writeProjection]

/-- Module prefixes the certified import closure may use: Lean core (`Init`
and `Std`, which ships with the toolchain), the kernel itself, the pure address
key, and the pure Ixon types. `Std` was admitted by the user's decision of
2026-09-30 (`plans/ix-kernel-competitive.md`) for its maps and their lemmas, as
con-leche's kernel uses them; `Classical.choice` reaching kernel definitions
through it is accepted, and the axiom guards below record where. Measured after
the K0 import trim, the closure of `Ix.Kernel` had 690 modules, all under `Init`
except the kernel's own and `Ix.Address.Core`. K3 also checks the pure Ixon
types independently. No `Lean` or `Batteries` module, nothing else under `Ix`,
and no `Blake3`, `LSpec`, `Cli`, or `lean4lean` module may enter. -/
def importAllowlist : Array Name :=
  #[`Init, `Std, `Ix.Kernel, `Ix.Address.Core, `Ix.Ixon.Types]

/-- Modules whose execution replacements are inherited Lean runtime. -/
def runtimeAllowlist : Array Name := #[`Init, `Std]

end Ix.Kernel.Audit

/-! ## Axiom boundaries -/

#guard_kernel_axioms Ix.Kernel.check_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.check [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Env.toEnvironment [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.annotate_erase [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecl_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.check_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecl_preserves [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDecls_preserves [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.readExpr_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.readBlock_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.ExprReads.deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.readExpr_agree [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.Installed.primary [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkFamilyC [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv_no_inhabitant_of_empty [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Env.emptyType_of_empty [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.no_inhabitant_of_empty [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkEnv_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.DeclarationsRead.deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Ingress.BlockReads.deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeExpr_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeExpr_roundtrip [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeBlock_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeBlock_roundtrip [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeProjection_reading [propext]
#guard_kernel_axioms Ix.Kernel.Egress.writeProjection_roundtrip [propext]
#guard_kernel_axioms Ix.Kernel.Egress.readRecord_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeRecord_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeRecord_source [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.record_roundtrip [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.readRecords_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeRecords_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.records_roundtrip [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.readRecords [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Egress.writeRecords [propext, Classical.choice, Quot.sound]

/-! ## Import and runtime closures -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Kernel, `Ix.Ixon.Types] Ix.Kernel.Audit.importAllowlist

-- `Std` is admitted; the compiler frontend and third-party libraries are not.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Std.Data.TreeMap
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Command
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Batteries.Data.RBMap

/-- info: runtime closure of [Ix.Kernel.check, Ix.Kernel.checkDecls, Ix.Kernel.checkDecl,
Ix.Kernel.Env.lookup, Ix.Kernel.Env.toEnvironment]: 1153 compiled functions; inherited externs 29,
implemented_by 0, unsafe 1, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.publicOperations Ix.Kernel.Audit.runtimeAllowlist

/-- info: runtime closure of [Ix.Kernel.checkEnv, Ix.Kernel.Ingress.readExpr,
Ix.Kernel.Ingress.readBlock, Ix.Kernel.Ingress.reference]: 1213 compiled functions;
inherited externs 42, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.ingressOperations Ix.Kernel.Audit.runtimeAllowlist

/-- info: runtime closure of [Ix.Kernel.Egress.readRecords, Ix.Kernel.Egress.writeRecords,
Ix.Kernel.Egress.writeExpr, Ix.Kernel.Egress.writeProjection]: 221 compiled functions;
inherited externs 26, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.egressOperations Ix.Kernel.Audit.runtimeAllowlist

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

/-! ## Frozen statements added with the Ixon v3 takeover (R3)

`checkEnv` is the Ixon entry point over the same admission fold as `check`;
its reading, model, and no-False statements are frozen like the K0 ones, as is
the syntactic `EmptyType` corollary for constructor-free families. -/

/-- info: @Ix.Kernel.checkEnv_reading : ∀ {cfg : Ix.Kernel.Config} {constants : Ix.Kernel.Ingress.Constants}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)}
  {strings : Option (Ix.Kernel.StringRefs Address)} {env : Ix.Kernel.Env Address},
  Ix.Kernel.checkEnv cfg constants blobs family strings = Except.ok env →
    Ix.Kernel.Ingress.Installed constants blobs family strings env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.checkEnv_reading

/-- info: Ix.Kernel.checkEnv_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.Model.SetTheory V] {cfg : Ix.Kernel.Config}
  {constants : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {strings : Option (Ix.Kernel.StringRefs Address)}
  {env : Ix.Kernel.Env Address},
  Ix.Kernel.checkEnv cfg constants blobs family strings = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.checkEnv_has_model

/-- info: Ix.Kernel.checkEnv_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.Model.SetTheory V] {cfg : Ix.Kernel.Config}
  {constants : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {strings : Option (Ix.Kernel.StringRefs Address)}
  {env : Ix.Kernel.Env Address},
  Ix.Kernel.checkEnv cfg constants blobs family strings = Except.ok env →
    ∀ {r : Ix.Kernel.ConstRef Address} {entry : Ix.Kernel.Model.ConstantEntry Address},
      env.toEnvironment r = some entry → env.EmptyType entry.universes entry.type → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.checkEnv_no_proof_of_False

/-- info: @Ix.Kernel.Env.emptyType_of_empty : ∀ {β : Type u_1} [inst : DecidableEq β] {env : Ix.Kernel.Env β} {source : β}
  {recursor : Ix.Kernel.ConstRef β},
  Ix.Kernel.Certified.Basis.Empty.Interface env.toEnvironment source recursor →
    env.EmptyType 0 (Ix.Kernel.Model.AExpr.const (Ix.Kernel.ConstRef.member source 0) []) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Env.emptyType_of_empty

/-- info: @Ix.Kernel.no_inhabitant_of_empty : ∀ {β : Type u_1} [inst : DecidableEq β] (V : Type u_2) [Ix.Kernel.Model.SetTheory V]
  {cfg : Ix.Kernel.Config} {decls : List (Ix.Kernel.Decl β)} {env : Ix.Kernel.Env β},
  Ix.Kernel.check cfg decls = Except.ok env →
    ∀ {source : β} {recursor : Ix.Kernel.ConstRef β},
      Ix.Kernel.Certified.Basis.Empty.Interface env.toEnvironment source recursor →
        ∀ {r : Ix.Kernel.ConstRef β} {entry : Ix.Kernel.Model.ConstantEntry β},
          env.toEnvironment r = some entry →
            entry.universes = 0 →
              entry.type = Ix.Kernel.Model.AExpr.const (Ix.Kernel.ConstRef.member source 0) [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.no_inhabitant_of_empty

/-- info: Ix.Kernel.checkEnv_no_inhabitant_of_empty : ∀ (V : Type u_1) [Ix.Kernel.Model.SetTheory V] {cfg : Ix.Kernel.Config}
  {constants : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {strings : Option (Ix.Kernel.StringRefs Address)}
  {env : Ix.Kernel.Env Address},
  Ix.Kernel.checkEnv cfg constants blobs family strings = Except.ok env →
    ∀ {source : Address} {recursor : Ix.Kernel.ConstRef Address},
      Ix.Kernel.Certified.Basis.Empty.Interface env.toEnvironment source recursor →
        ∀ {r : Ix.Kernel.ConstRef Address} {entry : Ix.Kernel.Model.ConstantEntry Address},
          env.toEnvironment r = some entry →
            entry.universes = 0 →
              entry.type = Ix.Kernel.Model.AExpr.const (Ix.Kernel.ConstRef.member source 0) [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.checkEnv_no_inhabitant_of_empty

/-- info: @Ix.Kernel.checkEnv_ok_iff : ∀ {cfg : Ix.Kernel.Config} {constants : Ix.Kernel.Ingress.Constants}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)}
  {strings : Option (Ix.Kernel.StringRefs Address)} {env : Ix.Kernel.Env Address},
  Ix.Kernel.checkEnv cfg constants blobs family strings = Except.ok env ↔
    (List.map Prod.fst constants).Nodup ∧
      (List.map Prod.fst blobs).Nodup ∧
        ∃ decls,
          Ix.Kernel.Ingress.readDeclarations constants blobs family strings cfg.fuel constants = Except.ok decls ∧
            Ix.Kernel.checkIndexed cfg decls = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.checkEnv_ok_iff

/-- info: @Ix.Kernel.Ingress.DeclarationsRead.deterministic : ∀ {constants : Ix.Kernel.Ingress.Constants}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)}
  {strings : Option (Ix.Kernel.StringRefs Address)} {inputs : Ix.Kernel.Ingress.Constants}
  {left right : List (Ix.Kernel.Decl Address)},
  Ix.Kernel.Ingress.DeclarationsRead constants blobs family strings inputs left →
    Ix.Kernel.Ingress.DeclarationsRead constants blobs family strings inputs right → left = right -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Ingress.DeclarationsRead.deterministic
