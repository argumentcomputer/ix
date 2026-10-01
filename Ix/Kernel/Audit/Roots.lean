/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel
import Ix.Ixon.Types
import Ix.Ixon.ConLecheConsistency
import Ix.Kernel.Audit.Axioms
import Ix.Kernel.Audit.Imports
import Ix.Kernel.Audit.Runtime

/-! # The required roots and their frozen boundaries

This module is the certified gate's manifest. From port step L5 (plan v4,
2026-09-30) its public roots are con-leche's verified checker behind the
Ixon reader: the entry `Ix.Ixon.ConLecheAdmission.checkBytes` (and its
pin-parametric form `checkBytesWith`, and `checkConstants`/`checkConstantsWith`
over decoded records) and the restated public theorems of
`Ix.Ixon.ConLecheConsistency` (model existence, no proof of the pinned
`False`, fidelity, resources). L0's rulings (`runtimeRulings`,
`elaborationImports`) are active on them. The intrinsic kernel's roots
(`Ix.Kernel.check`, `checkEnv`) stay audited below as the reference kernel:
they remain reachable through the renamed intrinsic entries
(`Ix.Ixon.Admission.checkBytesIntrinsic` and its projection and block-order
variants) until L6 retires them.

It fails elaboration when

* a public root is missing or its exact axiom set differs from the standard
  logical axioms (`propext`, `Classical.choice`, `Quot.sound`);
* an executable entry point depends on any axiom beyond those three, which
  enter it only through the erased proof components it carries (the model
  extension of each accepted declaration); Lean's compiler separately
  guarantees that no axiom sits in a computational position, since the
  entry points compile;
* the import closure of `Ix.Kernel` leaves the allowlisted module prefixes,
  or the elaboration-time closure below the ruled `meta import`s leaves
  `elaborationImports.allowed`;
* the compiled code of the public operations reaches an `@[extern]`,
  `implemented_by`, `unsafe`, or `csimp` replacement, or a `partial`
  definition, outside Lean's own runtime modules, unless `runtimeRulings`
  names it;
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
structure facts (900 → 920 functions), with the same replacements. B1
(2026-09-30) applies rule endpoints by infer-only fitting (`applyIOC`,
`applyTypedWC`, `fitArg`, `Witness.advance`; 1543 → 1560 functions, ingress
1519 → 1536, on the spine-form reduction) and projection iota at non-Prop
fields without endpoint inference (`applyNever`; 1560 → 1563, ingress
1536 → 1540), with the same replacements. L0 of the con-leche port
(2026-09-30) adds the ruled allowlists below as data (`runtimeRulings`,
`elaborationImports`, `ConLeche` in `importAllowlist`) and makes the runtime
audit see `partial` definitions and `csimp` replacements by their compiled
form; no `ConLeche` module is in this tree yet, and no frozen count
changed. L5 (2026-09-30) roots the gate at the con-leche entry: the fold
`ConLeche.Cached.checkDecls` (3010 compiled functions), the Ixon reader
and the entry are frozen with the rulings they use (18 computed-field
overrides, up to 21 proved csimps, the 10 `partial` definitions of the
in-model generator); `importAllowlist` gains the eight modules of the
entry's byte stage; the intrinsic kernel's audits are kept unchanged under
`intrinsicRoots`, `intrinsicFidelityRoots` and `intrinsicOperations`. Rebased
onto L4b/L4c at integration (int-4, 2026-10-01), the reader is 1856 (L5
alone: 1853; L4c's `safetyDecline` and its message constants, which replace
the inline checks of `readDefinition`) and the entry 5289 with 123 externs
(L5 alone: 33,408 with 115). The entry's committed Nat-operation pins were
upstream's JSON dumps spliced as one closed term, `ConLeche.natOpPinSets`,
whose compiled closure is 27,096 functions, 26,957 of them extracted closed
subterms; L4b's `builtinNatOpPins` decodes a string table at first use
(235 functions, and the eight string-scanning externs `String.decodeChar`,
`String.Pos.next`, `UInt32.decLe`, `String.toUTF8` and
`String.Pos.Raw.{extract, next, get, atEnd}`). -/

open Lean

namespace Ix.Kernel.Audit

/-- The public theorems (L5; roadmap section 2): model existence, no proof
of the pinned `False`, and resources for the con-leche entry, at the
committed tables and at every pin table, prelude and Nat-operation pin list,
and con-leche's own two letters they rest on. -/
def publicRoots : Array Name :=
  #[``Ix.Ixon.ConLecheAdmission.checkBytes_has_model, ``Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model,
    ``Ix.Ixon.ConLecheAdmission.checkConstants_has_model,
    ``Ix.Ixon.ConLecheAdmission.checkConstantsWith_has_model,
    ``Ix.Ixon.ConLecheAdmission.checkBytes_has_model_values,
    ``Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model_values,
    ``Ix.Ixon.ConLecheAdmission.checkBytes_no_proof_of_False,
    ``Ix.Ixon.ConLecheAdmission.checkBytesWith_no_proof_of_False,
    ``Ix.Ixon.ConLecheAdmission.checkBytes_no_False_theorem,
    ``Ix.Ixon.ConLecheAdmission.checkBytesWith_no_False_theorem,
    ``Ix.Ixon.ConLecheAdmission.checkBytesWith_no_False_reference,
    ``Ix.Ixon.ConLecheAdmission.checkBytes_resources, ``Ix.Ixon.ConLecheAdmission.checkBytesWith_resources,
    ``ConLeche.model_exists, ``ConLeche.no_False_theorem_accepted]

/-- Fidelity (the role of `Ingress.Installed`) and the facts it is built
from: the reading of accepted bytes, the record-by-record reading of the
reader, per-record installation, and the address encoding's injectivity. -/
def fidelityRoots : Array Name :=
  #[``Ix.Ixon.ConLecheAdmission.checkBytes_reading, ``Ix.Ixon.ConLecheAdmission.checkBytesWith_reading,
    ``Ix.Ixon.ConLecheAdmission.checkConstantsWith_installed, ``Ix.Ixon.ConLecheAdmission.Installed.skels,
    ``Ix.Ixon.ConLecheAdmission.Installed.singleton, ``Ix.Ixon.ConLecheAdmission.checkBytesWith_eq,
    ``Ix.Ixon.ConLecheAdmission.checkBytes_with, ``Ix.Ixon.ConLecheAdmission.checkConstants_with,
    ``Ix.Kernel.ConLecheReader.readRecords_spec, ``Ix.Kernel.ConLecheReader.readRecord_singleton,
    ``Ix.Kernel.ConLecheReader.StreamRead.singleton, ``Ix.Kernel.ConLecheReader.keyName_injective,
    ``Ix.Kernel.ConLecheFold.checkDecls_installs, ``Ix.Kernel.ConLecheFold.checkDecls_model_defn_values]

/-- The executable entry whose runtime closure is audited: con-leche's fold
behind the Ixon reader, over bytes and over decoded records. -/
def publicOperations : Array Name :=
  #[``Ix.Ixon.ConLecheAdmission.checkBytes, ``Ix.Ixon.ConLecheAdmission.checkBytesWith,
    ``Ix.Ixon.ConLecheAdmission.checkConstantsWith, ``Ix.Ixon.ConLecheAdmission.checkConstants]

/-- Con-leche's verified fold, the kernel of the entry. -/
def kernelOperations : Array Name := #[``ConLeche.Cached.checkDecls]

/-- The Ixon reader of the entry (the counterpart of `ingressOperations`). -/
def readerOperations : Array Name :=
  #[``Ix.Kernel.ConLecheReader.readRecords, ``Ix.Ixon.ConLecheAdmission.readStream]

/-- The entry's module, whose import closure is audited. -/
def publicModules : Array Name := #[`Ix.Ixon.ConLecheAdmission]

/-- The intrinsic kernel's public theorems (K0 to L4), kept as the
reference kernel's until L6. -/
def intrinsicRoots : Array Name :=
  #[``Ix.Kernel.check_has_model, ``Ix.Kernel.checkDecls_has_model, ``Ix.Kernel.no_proof_of_False]

/-- The intrinsic kernel's fidelity roots. -/
def intrinsicFidelityRoots : Array Name :=
  #[``Ix.Kernel.annotate_erase, ``Ix.Kernel.checkDecl_installed, ``Ix.Kernel.checkDecls_installed,
    ``Ix.Kernel.check_installed, ``Ix.Kernel.checkDecl_preserves, ``Ix.Kernel.checkDecls_preserves]

/-- The intrinsic kernel's executable operations. -/
def intrinsicOperations : Array Name :=
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

/-- Module prefixes the intrinsic kernel's import closure may use: Lean core
(`Init` and `Std`, which ships with the toolchain), the kernel itself, the
pure address key, and the pure Ixon types. `Std` was admitted by the user's
decision of 2026-09-30 (`plans/ix-kernel-competitive.md`) for its maps and
their lemmas, as con-leche's kernel uses them; `Classical.choice` reaching
kernel definitions through it is accepted, and the axiom guards below record
where. Measured after the K0 import trim, the closure of `Ix.Kernel` had 690
modules, all under `Init` except the kernel's own and `Ix.Address.Core`. K3
also checks the pure Ixon types independently. No `Lean` or `Batteries`
module, nothing else under `Ix`, and no `Blake3`, `LSpec`, `Cli`, or
`lean4lean` module may enter. `ConLeche` is the ported con-leche subtree
(plan v4, D4); `Lean` enters it only at elaboration time
(`elaborationImports`). -/
def kernelImportAllowlist : Array Name :=
  #[`Init, `Std, `Ix.Kernel, `Ix.Address.Core, `Ix.Ixon.Types, `ConLeche]

/-- Module prefixes the certified import closure may use (L5): the
intrinsic kernel's list, plus exactly the modules of the con-leche entry's
byte stage, as the int-3 probe of `Ix.Ixon.ConLecheAdmission` found them.
Each is pure Lean core and is audited on its own terms elsewhere:
* `Ix.Ixon.Codec`, `Ix.Ixon.Wire`, `Ix.Ixon.WireCheck`,
  `Ix.Ixon.Bounded.Constant`, `Ix.Ixon.Bounded.Universe`, `Ix.Ixon.Canonical`:
  the canonical per-record decoder and its readers (`Ix.Ixon.Audit`, whose
  `dataImports` is `Init` and these);
* `Ix.Ixon.Admission`: batch limits (`preflight`) and the decoding loop
  (`decodeRecords`), shared with the intrinsic entry
  (`Ix.Ixon.Admission.Audit`);
* `Ix.Ixon.ConLecheAdmission`: the entry itself.
Nothing else under `Ix.Ixon` (in particular no projection hashing,
`Ix.Address.Pure`, block order or proof module) and still no `Lean` outside
the ruled elaboration-time edges. -/
def importAllowlist : Array Name :=
  kernelImportAllowlist ++ #[`Ix.Ixon.Codec, `Ix.Ixon.Wire, `Ix.Ixon.WireCheck,
    `Ix.Ixon.Bounded.Constant, `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Canonical, `Ix.Ixon.Admission,
    `Ix.Ixon.ConLecheAdmission]

/-- The proofs of the public theorems may additionally use the Ixon codec's
proof modules (`Ix.Ixon.Verify`, `Ix.Ixon.Bounded.Size`, with their Lean
proof tooling) and the theorem module itself. -/
def proofImportAllowlist : Array Name :=
  importAllowlist ++ #[`Ix.Ixon.Bounded.Size, `Ix.Ixon.Verify, `Ix.Ixon.ConLecheConsistency, `Lean]

/-- Con-leche's elaboration-time imports (plan v4, "Audits"):
`ConLeche/Kernel/BasisGen.lean` (`public meta import Lean`) splices the
annotated basis and pins, and the `PinGen` generators meta-import
`ConLeche.Kernel.Expr` and each other. Below these edges only Lean core,
`Lean`, and `ConLeche` may appear. The transitional JSON exception,
`ConLeche/Kernel/NatOpPins.lean` meta-importing `ConLeche.PinGen.Dump` for
the committed Nat-op pin dumps, is gone since L4b: the pins come from Ixon
(`Ix/Kernel/ConLeche/NatOpPinData.lean`), `Dump` is deleted, and `NatOpPins`
is kept verbatim but not built. -/
def elaborationImports : ElaborationImports where
  importers := #[`ConLeche.Kernel.BasisGen, `ConLeche.PinGen]
  allowed := #[`Init, `Std, `Lean, `ConLeche]

/-- Modules whose execution replacements are inherited Lean runtime. -/
def runtimeAllowlist : Array Name := #[`Init, `Std]

/-- The ruled exceptions to the runtime audit (plan v4, "Audits"; roadmap
section 2, "Execution boundary"). Each names exactly what it admits:
* R-meta: the `@[computed_field]` overrides of con-leche's `Level`
  (`hashData`), `Expr` (`data`) and `Name` (`hashData`), and of Ix's `AExpr`
  (B2: `looseBound`, `structHash`);
* project `@[csimp]` replacements in `ConLeche` and `Ix.Kernel`, each only
  with a theorem on the standard axioms;
* R-ptr: `withPtrEq`, `withPtrAddr`, their `unsafe` implementations, and
  the pointer reads under them; and `isExclusiveUnsafe`, the reference-count
  read behind `withExclusive` (all `Init`, so already inherited);
* `ConLeche.withExclusive`, `implemented_by` `ConLeche.withExclusiveUnsafe`,
  whose type carries the obligation `k true = k false`;
* elaboration-time `meta` code in `BasisGen` and `PinGen`
  (`unsafe evalTerm` wrappers paired by `implemented_by`), which compiled
  non-`meta` code cannot call;
* `partial` definitions of the in-model generator,
  `ConLeche/Frontend/InModel*` (L4). -/
def runtimeRulings : RuntimeRulings where
  computedFieldTypes := #[`ConLeche.Level, `ConLeche.Expr, `ConLeche.Name, ``Ix.Kernel.Model.AExpr]
  csimpModules := #[`ConLeche, `Ix.Kernel]
  primitives := #[``withPtrEq, ``withPtrEqUnsafe, ``withPtrEqDecEq, ``withPtrAddr,
    ``withPtrAddrUnsafe, ``ptrEq, ``ptrAddrUnsafe, ``isExclusiveUnsafe]
  implementations := #[(`ConLeche.withExclusive, `ConLeche.withExclusiveUnsafe)]
  elaborationModules := #[`ConLeche.Kernel.BasisGen,
    `ConLeche.PinGen, `ConLeche.PinGen.Certs, `ConLeche.PinGen.Prelude]
  partialModules := #[`ConLeche.Frontend.InModel, `ConLeche.Frontend.InModelDump]

end Ix.Kernel.Audit

/-! ## The certified entry (L5): con-leche behind the Ixon reader

### Axiom boundaries

Every public, fidelity and executable root depends on exactly the three
standard axioms. The list guards below and `publicRoots`/`fidelityRoots`
name the same roots, so a missing root fails here. -/

run_cmd do
  let env ← Lean.getEnv
  for root in Ix.Kernel.Audit.publicRoots ++ Ix.Kernel.Audit.fidelityRoots ++
      Ix.Kernel.Audit.publicOperations ++ Ix.Kernel.Audit.kernelOperations ++
      Ix.Kernel.Audit.readerOperations do
    unless env.contains root do throwError m!"required root is missing: {root}"

#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstants_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstantsWith_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_no_False_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms ConLeche.model_exists [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms ConLeche.no_False_theorem_accepted [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstantsWith_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.Installed.skels [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.Installed.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_with [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstants_with [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.readRecords_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.readRecord_singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.StreamRead.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.keyName_injective [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheFold.checkDecls_installs [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheFold.checkDecls_model_defn_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstantsWith [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstants [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms ConLeche.Cached.checkDecls [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.readRecords [propext, Classical.choice, Quot.sound]

/-! ### Import and runtime closures

The entry's import closure stays inside `importAllowlist`, below the ruled
elaboration-time edges inside `elaborationImports.allowed`; the theorems'
closure inside `proofImportAllowlist`. The runtime closures are frozen with
the rulings they use, measured before freezing (int-3 probe, re-measured at
L5 and at int-4): the fold reaches con-leche's computed-field overrides of
`Level`, `Expr` and `Name` (18) and 20 project csimps; the reader adds the
in-model generator's 10 `partial` definitions; the entry adds the byte stage
and the committed tables. The pin-parametric forms (`checkBytesWith`,
`checkConstantsWith`) reach 4519 functions; the committed pin table, prelude
and Nat-operation pin decoder add the rest. -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith Ix.Kernel.Audit.publicModules Ix.Kernel.Audit.importAllowlist Ix.Kernel.Audit.elaborationImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Ixon.ConLecheConsistency] Ix.Kernel.Audit.proofImportAllowlist Ix.Kernel.Audit.elaborationImports

-- The entry's byte stage is admitted; projection hashing, block order, the
-- codec proofs and the intrinsic kernel's own boundary are not widened.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Canonical
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Admission
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Projection
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Verify
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.ConLecheConsistency
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Address.Pure
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Data.Json
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Ixon.Canonical
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Ixon.Admission

/-- info: runtime closure of [ConLeche.Cached.checkDecls]: 3010 compiled functions; inherited externs 83,
implemented_by 0, unsafe 22, csimp 4; ruled computed_field 18, csimp 20 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.ConLecheReader.readRecords,
 Ix.Ixon.ConLecheAdmission.readStream]: 1856 compiled functions; inherited externs 81, implemented_by 0,
unsafe 23, csimp 0; ruled computed_field 18, csimp 7, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.readerOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Ixon.ConLecheAdmission.checkBytes,
 Ix.Ixon.ConLecheAdmission.checkBytesWith,
 Ix.Ixon.ConLecheAdmission.checkConstantsWith,
 Ix.Ixon.ConLecheAdmission.checkConstants]: 5289 compiled functions; inherited externs 123, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.publicOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

-- Without the rulings the entry's closure fails: they are what admits it.
/-- error: project-level execution replacements reached from [ConLeche.Cached.checkDecls] -/
#guard_msgs (substring := true) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist

/-! ### Frozen statements -/

/-- info: Ix.Ixon.ConLecheAdmission.checkBytes_has_model : ∀ (V : Type u_1) [inst : ConLeche.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env → Nonempty (ConLeche.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_has_model

/-- info: Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model : ∀ (V : Type u_1) [inst : ConLeche.SetTheory V]
  {pins : Ix.Kernel.ConLecheReader.Pins} {pre : Ix.Kernel.ConLecheReader.Prelude} {natPins : List ConLeche.NatOpPinSet}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    Nonempty (ConLeche.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model

/-- info: Ix.Ixon.ConLecheAdmission.checkBytes_has_model_values : ∀ (V : Type u_1) [inst : ConLeche.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env →
    ∃ M,
      ∀ (cv : ConLeche.ConstantVal) (value : ConLeche.Expr) (hint' : ConLeche.ReducibilityHint),
        ConLeche.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
          ∀ (φ : ConLeche.LevelParam → Nat) (ρ : ConLeche.BVarIdx → V),
            ConLeche.Denotes M.cval env φ ρ value (M.cval cv.name φ) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_has_model_values

/-- info: Ix.Ixon.ConLecheAdmission.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [ConLeche.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env →
    ∀ (ci : ConLeche.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = ConLeche.Expr.const ConLeche.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_no_proof_of_False

/-- info: Ix.Ixon.ConLecheAdmission.checkBytesWith_no_False_theorem : ∀ (V : Type u_1) [ConLeche.SetTheory V]
  {pins : Ix.Kernel.ConLecheReader.Pins} {pre : Ix.Kernel.ConLecheReader.Prelude} {natPins : List ConLeche.NatOpPinSet}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    ∀ {constants : List (Address × Ixon.Constant)},
      Ix.Ixon.Verify.Admission.RecordsRead limits records constants →
        ∀ {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition},
          (owner, c) ∈ constants →
            c.info = Ixon.ConstantInfo.defn d →
              d.kind = Ix.DefKind.thm →
                (Ix.Kernel.ConLecheReader.definitionReader
                          (Ix.Ixon.ConLecheAdmission.streamContext pins pre constants blobs hint) owner c d).read
                      d.typ =
                    Except.ok (ConLeche.Expr.const ConLeche.falseName []) →
                  False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytesWith_no_False_theorem

/-- info: @Ix.Ixon.ConLecheAdmission.checkBytes_reading : ∀ {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env →
    ∃ pins pre natPins,
      Ix.Kernel.ConLecheReader.defaultPins = Except.ok pins ∧
        Ix.Kernel.ConLecheReader.builtinPrelude = Except.ok pre ∧
          Ix.Kernel.ConLecheReader.builtinNatOpPins = Except.ok natPins ∧
            Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
              ∃ constants,
                Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
                  Ix.Ixon.ConLecheAdmission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_reading

/-- info: @Ix.Ixon.ConLecheAdmission.checkBytesWith_reading : ∀ {pins : Ix.Kernel.ConLecheReader.Pins}
  {pre : Ix.Kernel.ConLecheReader.Prelude} {natPins : List ConLeche.NatOpPinSet} {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ constants,
        Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
          Ix.Ixon.ConLecheAdmission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytesWith_reading

/-- info: @Ix.Ixon.ConLecheAdmission.Installed.singleton : ∀ {pins : Ix.Kernel.ConLecheReader.Pins}
  {pre : Ix.Kernel.ConLecheReader.Prelude} {natPins : List ConLeche.NatOpPinSet}
  {constants : List (Address × Ixon.Constant)} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.Installed pins pre natPins constants blobs hint env →
    ∀ {owner : Address} {c : Ixon.Constant},
      (owner, c) ∈ constants →
        Ix.Kernel.ConLecheReader.isSingleton c.info = true →
          ∃ st decl ds,
            Ix.Kernel.ConLecheReader.SingletonRead
                (Ix.Ixon.ConLecheAdmission.streamContext pins pre constants blobs hint) st owner c decl ∧
              decl ∈ ds ∧
                ConLeche.Cached.checkDecls ConLeche.CheckMode.verified natPins ds = Except.ok env ∧
                  ∀ (s : ConLeche.Cached.InstallSkel),
                    Ix.Kernel.ConLecheFold.declSkel decl = some s →
                      ∃ ci, ci ∈ env.consts ∧ ConLeche.Cached.ciSkel ci = s -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.Installed.singleton

/-- info: @Ix.Ixon.ConLecheAdmission.checkBytes_resources : ∀ {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env →
    ∃ constants,
      Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
        Ix.Ixon.Verify.Admission.resourceUnits constants ≤
          2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_resources

/-- info: @Ix.Kernel.ConLecheReader.keyName_injective : ∀ {r s : Ix.Kernel.ConstRef Address},
  Ix.Kernel.ConLecheReader.keyName r = Ix.Kernel.ConLecheReader.keyName s → r = s -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.ConLecheReader.keyName_injective

/-- info: ConLeche.model_exists : ∀ (V : Type u_1) [inst : ConLeche.SetTheory V] (pins : List ConLeche.NatOpPinSet)
  (ds : Array ConLeche.Declaration) (env : ConLeche.Env),
  ConLeche.Cached.checkDecls ConLeche.CheckMode.verified pins ds = Except.ok env → Nonempty (ConLeche.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @ConLeche.model_exists

/-! ## The intrinsic reference kernel (until L6)

The intrinsic kernel's boundaries, unchanged from L0: its axiom guards,
import closure (under `kernelImportAllowlist`), runtime closures and frozen
statements. -/

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

/-! ### Import and runtime closures -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Kernel, `Ix.Ixon.Types] Ix.Kernel.Audit.kernelImportAllowlist Ix.Kernel.Audit.elaborationImports

-- `Std` is admitted; the compiler frontend and third-party libraries are not.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Std.Data.TreeMap
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Command
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Batteries.Data.RBMap
-- `ConLeche` is admitted; `Lean` only below the ruled elaboration-time imports.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `ConLeche.Kernel.Core
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Term
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed `Lean.Elab.Term
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.importers `ConLeche.Kernel.Core
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed `Ix.Tc

/-- info: runtime closure of [Ix.Kernel.check, Ix.Kernel.checkDecls, Ix.Kernel.checkDecl,
Ix.Kernel.Env.lookup, Ix.Kernel.Env.toEnvironment]: 1563 compiled functions; inherited externs 32,
implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.intrinsicOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.checkEnv, Ix.Kernel.Ingress.readExpr,
Ix.Kernel.Ingress.readBlock, Ix.Kernel.Ingress.reference]: 1540 compiled functions;
inherited externs 45, implemented_by 0, unsafe 3, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.ingressOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.Egress.readRecords, Ix.Kernel.Egress.writeRecords,
Ix.Kernel.Egress.writeExpr, Ix.Kernel.Egress.writeProjection]: 221 compiled functions;
inherited externs 26, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.egressOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-! ### Frozen statements -/

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

/-! ### Frozen statements added with the Ixon v3 takeover (R3)

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
