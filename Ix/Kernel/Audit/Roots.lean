/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel
import Ix.Ixon.Types
import Ix.Ixon.ConLecheConsistency
import Ix.Ixon.Consistency
import Ix.Kernel.Audit.Axioms
import Ix.Kernel.Audit.Imports
import Ix.Kernel.Audit.Runtime

/-! # The required roots and their frozen boundaries

This module is the certified gate's manifest. From port step L5 (plan v4,
2026-09-30) its public roots are con-leche's verified checker behind the
Ixon reader: the certified API `Ix.Ixon.Admission.checkBytes`, which runs
the entry `Ix.Ixon.ConLecheAdmission.checkBytes` (and its
pin-parametric form `checkBytesWith`, and `checkConstants`/`checkConstantsWith`
over decoded records) and the restated public theorems of
`Ix.Ixon.Consistency` and `Ix.Ixon.ConLecheConsistency` (model existence,
no proof of the pinned `False`, fidelity, resources). L0's rulings (`runtimeRulings`,
`elaborationImports`) are active on them. The intrinsic kernel's roots
(`Ix.Kernel.check`, `checkEnv`, Egress's record round trip), their frozen
runtime closures (kernel 1563, ingress 1540, egress 221 compiled functions)
and their frozen statements were retired with that kernel at L6 (plan v4).

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
`elaborationImports`, and the con-leche prefix, then `ConLeche`, in
`importAllowlist`) and makes the runtime audit see `partial` definitions and
`csimp` replacements by their compiled form; no con-leche module was in the
tree yet, and no frozen count changed. L5 (2026-09-30) roots the gate at the con-leche entry: the fold
`Ix.Kernel.Cached.checkDecls` (3010 compiled functions), the Ixon reader
and the entry are frozen with the rulings they use (18 computed-field
overrides, up to 21 proved csimps, the 10 `partial` definitions of the
in-model generator); `importAllowlist` gains the eight modules of the
entry's byte stage; the intrinsic kernel's audits are kept unchanged under
`intrinsicRoots`, `intrinsicFidelityRoots` and `intrinsicOperations`. Rebased
onto L4b/L4c at integration (int-4, 2026-10-01), the reader is 1856 (L5
alone: 1853; L4c's `safetyDecline` and its message constants, which replace
the inline checks of `readDefinition`) and the entry, with the certified API
`Ix.Ixon.Admission.checkBytes`, 5290 with 123 externs (L5 alone: 33,409 with
115). The entry's committed Nat-operation pins were upstream's JSON dumps
spliced as one closed term, `ConLeche.natOpPinSets`, whose compiled closure
is 27,096 functions, 26,957 of them extracted closed subterms; L4b's
`builtinNatOpPins` decodes a string table at first use (235 functions, and
the eight string-scanning externs `String.decodeChar`, `String.Pos.next`,
`UInt32.decLe`, `String.toUTF8` and `String.Pos.Raw.{extract, next, get,
atEnd}`). L6 (2026-10-01) retires the intrinsic kernel: its roots,
closures and statements leave this manifest, and the projection writer it
shared with the certified entries (`Ix.Kernel.Egress.writeProjection`) is
guarded in `Ix.Ixon.ProjectionAudit`. The entry falls from 5290 to 5280
functions: the byte stage's error lost its intrinsic `kernel` case, so
`ConLecheAdmission.Error.ofAdmission` no longer prints a `Kernel.Error`
(`Ix.Kernel.instReprError.repr` and its eight extracted closed terms, and the
closed message prefix). L6b (2026-10-01) adds the byte stage's key check
(`Ix.Ixon.Admission.uniqueKeys`: no two records and no two blobs under one
address, a reject): the entry grows from 5280 to 5290 functions with
`uniqueKeys`, its two closed empty-set terms, `firstDuplicate`, and six
`Std.HashSet Address` lookup and insertion specializations at
`firstDuplicate`; externs, unsafe and rulings are unchanged. The fidelity
statements gain `UniqueKeys`, and the reader's own duplicate-record check
is proved (`readRecords_nodup`, through `LawfulBEq Address` in
`Ix.Kernel.Ingress.Records`). cl-m1 (2026-10-01) adapts the in-process
modeller's `genNested` (`Ix/Kernel/Frontend/InModel/Nested.lean`): it forms
its container groups largest family first, by `List.mergeSort`, and
declines a group that shares a member with an earlier one. The reader grows
from 1856 to 1871 functions and the entry from 5290 to 5296: in both,
`genNested`'s three new lifted lambdas (the family size, the sort's order,
the overlap test), two `List.any` specializations for the overlap test, and
a net one closed term from re-specializing the group loop (+4, −3); in the
reader also the nine functions of Lean's `List.mergeSort` implementation
(`mergeSortTR₂` with `run` and `run'`, `mergeTR` with `go`, `splitRevAt`
with `go`, `splitRevInTwo`, `splitRevInTwo'`), which the entry already
reaches through `Frontend.preparePrelude`. Externs, unsafe and rulings are
unchanged. T1 (2026-10-01) builds the reader context's
record maps once (`Ix.Kernel.ConLecheReader.contextOf`; `storeOf` partially
applied rebuilt its map at every lookup): `storeOf`, its boxed form, its fold
specialization and the closed term `contextOf._closed_2` (the empty fallback
store) leave, and `recordMap` with its fold specialization enter, so the
reader falls from 1871 to 1869 functions and the entry from 5296 to 5294
(1856 to 1854 and 5290 to 5288 on T1's own base, before cl-m1; int-5);
externs, unsafe and rulings are unchanged. T1-4 computes the address
encodings ahead of reading (`KeyNames`, one name object per reference
instead of a hexadecimal spelling at every occurrence): `KeyNames.get`,
`KeyNames.insert`, `keyNamesOf` and its fold specialization enter, and the
two `Std.HashMap` lookup specializations that `Ctx.nameOf` emitted are now
emitted at `KeyNames.get` (the same map type): the reader grows from 1869 to
1873, the entry from 5294 to 5298 (1854 to 1858 and 5288 to 5292 on T1's own
base; int-5); externs, unsafe and rulings are unchanged. cl-level
(2026-10-01) adapts con-leche's level comparison
(`Ix/Kernel/Level.lean`): `rest`'s `(param, max)` case falls back on
Géran's sublevels (`Ix/Kernel/LevelGeran.lean`) when both branches of
the `max` fail. The fold grows from 3010 to 3022 functions and the entry from
5298 to 5310 (5296 to 5308 on cl-level's own base, before T1; rebased at
mergeability): `Level.Geran.decomposeAux`, `nzConds` with its closed `[[]]`,
`dominates`, `Sub.isZero`, `leq` with one closed term, the `List.all`,
`List.any`, `List.elem` and `List.foldl` specializations at `le`, `subset`
and `decomposeAux` (five), and one closed term that moves from `isEquiv` to
`rest`. The reader grows from 1873 to 1886 (1871 to 1884 on cl-level's own
base): the same twelve and `Int.natAbs` (an extern of Lean core, 81 to 82
externs), which the fold already reaches. No `unsafe`, `partial`,
`implemented_by` or csimp is added, and the rulings are unchanged. -/

open Lean

namespace Ix.Kernel.Audit

/-- The public theorems (L5; roadmap section 2): model existence, no proof
of the pinned `False`, and resources for the con-leche entry, at the
committed tables and at every pin table, prelude and Nat-operation pin list,
and con-leche's own two letters they rest on. -/
def publicRoots : Array Lean.Name :=
  #[``Ix.Ixon.Admission.checkBytes_has_model, ``Ix.Ixon.Admission.checkBytes_has_model_values,
    ``Ix.Ixon.Admission.checkBytes_no_proof_of_False, ``Ix.Ixon.Admission.checkBytes_no_False_theorem,
    ``Ix.Ixon.Admission.checkBytes_resources,
    ``Ix.Ixon.ConLecheAdmission.checkBytes_has_model, ``Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model,
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
    ``Ix.Kernel.model_exists, ``Ix.Kernel.no_False_theorem_accepted]

/-- Fidelity (the role of the intrinsic kernel's `Ingress.Installed`,
retired at L6) and the facts it is built
from: the reading of accepted bytes, the record-by-record reading of the
reader, per-record installation, and the address encoding's injectivity. -/
def fidelityRoots : Array Lean.Name :=
  #[``Ix.Ixon.Admission.checkBytes_reading, ``Ix.Ixon.ConLecheAdmission.checkBytes_reading, ``Ix.Ixon.ConLecheAdmission.checkBytesWith_reading,
    ``Ix.Ixon.ConLecheAdmission.checkConstantsWith_installed, ``Ix.Ixon.ConLecheAdmission.Installed.skels,
    ``Ix.Ixon.ConLecheAdmission.Installed.singleton, ``Ix.Ixon.ConLecheAdmission.checkBytesWith_eq,
    ``Ix.Ixon.ConLecheAdmission.checkBytes_with, ``Ix.Ixon.ConLecheAdmission.checkConstants_with,
    ``Ix.Kernel.ConLecheReader.readRecords_spec, ``Ix.Kernel.ConLecheReader.readRecords_nodup,
    ``Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff, ``Ix.Kernel.ConLecheReader.readRecord_singleton,
    ``Ix.Kernel.ConLecheReader.StreamRead.singleton, ``Ix.Kernel.ConLecheReader.keyName_injective,
    ``Ix.Kernel.ConLecheFold.checkDecls_installs, ``Ix.Kernel.ConLecheFold.checkDecls_model_defn_values]

/-- The executable entry whose runtime closure is audited: the certified API
`Ix.Ixon.Admission.checkBytes`, which runs con-leche's fold behind the Ixon
reader, and that entry over bytes and over decoded records. -/
def publicOperations : Array Lean.Name :=
  #[``Ix.Ixon.Admission.checkBytes, ``Ix.Ixon.ConLecheAdmission.checkBytes,
    ``Ix.Ixon.ConLecheAdmission.checkBytesWith,
    ``Ix.Ixon.ConLecheAdmission.checkConstantsWith, ``Ix.Ixon.ConLecheAdmission.checkConstants]

/-- Con-leche's verified fold, the kernel of the entry. -/
def kernelOperations : Array Lean.Name := #[``Ix.Kernel.Cached.checkDecls]

/-- The Ixon reader of the entry (L4; the intrinsic kernel's ingress, its
counterpart until L5, was retired at L6). -/
def readerOperations : Array Lean.Name :=
  #[``Ix.Kernel.ConLecheReader.readRecords, ``Ix.Ixon.ConLecheAdmission.readStream]

/-- The certified API's module, whose import closure is audited. -/
def publicModules : Array Lean.Name := #[`Ix.Ixon.Admission]

/-- Module prefixes the kernel-side modules may use: Lean core (`Init` and
`Std`, which ships with the toolchain), the kernel `Ix.Kernel` (con-leche's
vendored checker and Ix's boundary beside it), the pure address key and the
pure Ixon types. Through L5 this was the intrinsic kernel's list; from L6
it fences the Ixon reader, the record store, the projection writer and the
pure Ixon types (below), and is the base of `importAllowlist`. `Std` was admitted by the user's
decision of 2026-09-30 (`plans/ix-kernel-competitive.md`) for its maps and
their lemmas, as con-leche's kernel uses them; `Classical.choice` reaching
kernel definitions through it is accepted, and the axiom guards below record
where. Measured after the K0 import trim, the closure of `Ix.Kernel` had 690
modules, all under `Init` except the kernel's own and `Ix.Address.Core`. K3
also checks the pure Ixon types independently. No `Lean` or `Batteries`
module, nothing else under `Ix`, and no `Blake3`, `LSpec`, `Cli`, or
`lean4lean` module may enter. The vendored con-leche tree was a separate
prefix, `ConLeche`, until it moved under `Ix.Kernel` (2026-10-01; plan v4,
D4, kept its upstream paths until then); `Lean` enters it only at
elaboration time (`elaborationImports`). -/
def kernelImportAllowlist : Array Lean.Name :=
  #[`Init, `Std, `Ix.Kernel, `Ix.Address.Core, `Ix.Ixon.Types]

/-- Module prefixes the certified import closure may use (L5): the
kernel-side list (`kernelImportAllowlist`), plus exactly the modules of the con-leche entry's
byte stage, as the int-3 probe of `Ix.Ixon.ConLecheAdmission` found them.
Each is pure Lean core and is audited on its own terms elsewhere:
* `Ix.Ixon.Codec`, `Ix.Ixon.Wire`, `Ix.Ixon.WireCheck`,
  `Ix.Ixon.Bounded.Constant`, `Ix.Ixon.Bounded.Universe`, `Ix.Ixon.Canonical`:
  the canonical per-record decoder and its readers (`Ix.Ixon.Audit`, whose
  `dataImports` is `Init` and these);
* `Ix.Ixon.Admission`: the certified API module, and
  `Ix.Ixon.Admission.Bytes`, the batch limits (`preflight`) and the decoding
  loop (`decodeRecords`) (`Ix.Ixon.Admission.Audit`);
* `Ix.Ixon.ConLecheAdmission`: the con-leche entry the API runs.
Nothing else under `Ix.Ixon` (in particular no projection hashing,
`Ix.Address.Pure`, block order or proof module) and still no `Lean` outside
the ruled elaboration-time edges. -/
def importAllowlist : Array Lean.Name :=
  kernelImportAllowlist ++ #[`Ix.Ixon.Codec, `Ix.Ixon.Wire, `Ix.Ixon.WireCheck,
    `Ix.Ixon.Bounded.Constant, `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Canonical, `Ix.Ixon.Admission,
    `Ix.Ixon.ConLecheAdmission]

/-- The proofs of the public theorems may additionally use the Ixon codec's
proof modules (`Ix.Ixon.Verify`, `Ix.Ixon.Bounded.Size`, with their Lean
proof tooling) and the theorem module itself. -/
def proofImportAllowlist : Array Lean.Name :=
  importAllowlist ++ #[`Ix.Ixon.Bounded.Size, `Ix.Ixon.Verify, `Ix.Ixon.ConLecheConsistency,
    `Ix.Ixon.Consistency, `Lean]

/-- Con-leche's elaboration-time imports (plan v4, "Audits"):
`Ix/Kernel/BasisGen.lean` (`public meta import Lean`) splices the
annotated basis and pins, and the `PinGen` generators meta-import
`Ix.Kernel.Expr` and each other. Below these edges only Lean core,
`Lean`, and `Ix.Kernel` may appear. The transitional JSON exception,
upstream's `ConLeche/Kernel/NatOpPins.lean` meta-importing `ConLeche.PinGen.Dump` for
the committed Nat-op pin dumps, is gone since L4b: the pins come from Ixon
(`Ix/Kernel/Ixon/NatOpPinData.lean`), `Dump` is deleted, and `NatOpPins`
is not vendored (kept verbatim and unbuilt at L4b, deleted at int-4). -/
def elaborationImports : ElaborationImports where
  importers := #[`Ix.Kernel.BasisGen, `Ix.Kernel.PinGen]
  allowed := #[`Init, `Std, `Lean, `Ix.Kernel]

/-- Modules whose execution replacements are inherited Lean runtime. -/
def runtimeAllowlist : Array Lean.Name := #[`Init, `Std]

/-- The ruled exceptions to the runtime audit (plan v4, "Audits"; roadmap
section 2, "Execution boundary"). Each names exactly what it admits:
* R-meta: the `@[computed_field]` overrides of con-leche's `Level`
  (`hashData`), `Expr` (`data`) and `Name` (`hashData`) (until L6 also of
  the intrinsic kernel's `AExpr`, B2);
* project `@[csimp]` replacements in `Ix.Kernel`, each only with a theorem
  on the standard axioms (until L6 also in the intrinsic `Ix.Kernel`);
* R-ptr: `withPtrEq`, `withPtrAddr`, their `unsafe` implementations, and
  the pointer reads under them; and `isExclusiveUnsafe`, the reference-count
  read behind `withExclusive` (all `Init`, so already inherited);
* `Ix.Kernel.withExclusive`, `implemented_by` `Ix.Kernel.withExclusiveUnsafe`,
  whose type carries the obligation `k true = k false`;
* elaboration-time `meta` code in `BasisGen` and `PinGen`
  (`unsafe evalTerm` wrappers paired by `implemented_by`), which compiled
  non-`meta` code cannot call;
* `partial` definitions of the in-model generator,
  `Ix/Kernel/Frontend/InModel*` (L4). -/
def runtimeRulings : RuntimeRulings where
  computedFieldTypes := #[`Ix.Kernel.Level, `Ix.Kernel.Expr, `Ix.Kernel.Name]
  csimpModules := #[`Ix.Kernel]
  primitives := #[``withPtrEq, ``withPtrEqUnsafe, ``withPtrEqDecEq, ``withPtrAddr,
    ``withPtrAddrUnsafe, ``ptrEq, ``ptrAddrUnsafe, ``isExclusiveUnsafe]
  implementations := #[(`Ix.Kernel.withExclusive, `Ix.Kernel.withExclusiveUnsafe)]
  elaborationModules := #[`Ix.Kernel.BasisGen,
    `Ix.Kernel.PinGen, `Ix.Kernel.PinGen.Certs, `Ix.Kernel.PinGen.Prelude]
  partialModules := #[`Ix.Kernel.Frontend.InModel, `Ix.Kernel.Frontend.InModelDump]

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

#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes [propext, Classical.choice, Quot.sound]
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
#guard_kernel_axioms Ix.Kernel.model_exists [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.no_False_theorem_accepted [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstantsWith_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.Installed.skels [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.Installed.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes_with [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstants_with [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.readRecords_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.readRecords_nodup [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.readRecord_singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.StreamRead.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheReader.keyName_injective [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheFold.checkDecls_installs [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.ConLecheFold.checkDecls_model_defn_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkBytesWith [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstantsWith [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.ConLecheAdmission.checkConstants [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.checkDecls [propext, Classical.choice, Quot.sound]
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
`checkConstantsWith`) reach 4539 functions (4509 from L6, which did not
update this sentence, 4519 with L6b's `uniqueKeys`, 4517 with T1's record
maps on its own base, 4523 with cl-m1's `genNested` as well, +6 as in the
entry; int-5; 4527 with T1's address encodings; 4539 with cl-level's Géran
fallback, +12 as in the entry, measured when it was rebased onto int-5);
the committed pin table, prelude and Nat-operation pin decoder add the rest. -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith Ix.Kernel.Audit.publicModules Ix.Kernel.Audit.importAllowlist Ix.Kernel.Audit.elaborationImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Ixon.ConLecheConsistency, `Ix.Ixon.Consistency] Ix.Kernel.Audit.proofImportAllowlist Ix.Kernel.Audit.elaborationImports

-- The entry's byte stage is admitted; projection hashing, block order, the
-- codec proofs and `kernelImportAllowlist` are not widened.
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

/-- info: runtime closure of [Ix.Kernel.Cached.checkDecls]: 3022 compiled functions; inherited externs 83,
implemented_by 0, unsafe 22, csimp 4; ruled computed_field 18, csimp 20 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.ConLecheReader.readRecords,
 Ix.Ixon.ConLecheAdmission.readStream]: 1886 compiled functions; inherited externs 82, implemented_by 0,
unsafe 23, csimp 0; ruled computed_field 18, csimp 7, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.readerOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Ixon.Admission.checkBytes,
 Ix.Ixon.ConLecheAdmission.checkBytes,
 Ix.Ixon.ConLecheAdmission.checkBytesWith,
 Ix.Ixon.ConLecheAdmission.checkConstantsWith,
 Ix.Ixon.ConLecheAdmission.checkConstants]: 5310 compiled functions; inherited externs 123, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.publicOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

-- Without the rulings the entry's closure fails: they are what admits it.
/-- error: project-level execution replacements reached from [Ix.Kernel.Cached.checkDecls] -/
#guard_msgs (substring := true) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist

/-! ### Frozen statements -/

/-- info: Ix.Ixon.ConLecheAdmission.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_has_model

/-- info: Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {pins : Ix.Kernel.ConLecheReader.Pins} {pre : Ix.Kernel.ConLecheReader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.ConLecheAdmission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytesWith_has_model

/-- info: Ix.Ixon.ConLecheAdmission.checkBytes_has_model_values : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env →
    ∃ M,
      ∀ (cv : Ix.Kernel.ConstantVal) (value : Ix.Kernel.Expr) (hint' : Ix.Kernel.ReducibilityHint),
        Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
          ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
            Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_has_model_values

/-- info: Ix.Ixon.ConLecheAdmission.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_no_proof_of_False

/-- info: Ix.Ixon.ConLecheAdmission.checkBytesWith_no_False_theorem : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {pins : Ix.Kernel.ConLecheReader.Pins} {pre : Ix.Kernel.ConLecheReader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
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
                    Except.ok (Ix.Kernel.Expr.const Ix.Kernel.falseName []) →
                  False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytesWith_no_False_theorem

/-- info: @Ix.Ixon.ConLecheAdmission.checkBytes_reading : ∀ {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint = Except.ok env →
    ∃ pins pre natPins,
      Ix.Kernel.ConLecheReader.defaultPins = Except.ok pins ∧
        Ix.Kernel.ConLecheReader.builtinPrelude = Except.ok pre ∧
          Ix.Kernel.ConLecheReader.builtinNatOpPins = Except.ok natPins ∧
            Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
              Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
                ∃ constants,
                  Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
                    Ix.Ixon.ConLecheAdmission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytes_reading

/-- info: @Ix.Ixon.ConLecheAdmission.checkBytesWith_reading : ∀ {pins : Ix.Kernel.ConLecheReader.Pins}
  {pre : Ix.Kernel.ConLecheReader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet} {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.ConLecheAdmission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
        ∃ constants,
          Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
            Ix.Ixon.ConLecheAdmission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.checkBytesWith_reading

/-- info: Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff : ∀ (records : Ix.Ixon.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Ixon.Admission.uniqueKeys records blobs = Except.ok () ↔ Ix.Ixon.Verify.Admission.UniqueKeys records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff

/-- info: @Ix.Kernel.ConLecheReader.readRecords_nodup : ∀ {cx : Ix.Kernel.ConLecheReader.Ctx}
  {st st' : Ix.Kernel.ConLecheReader.State} {records : Array (Address × Ixon.Constant)}
  {out : Array Ix.Kernel.ConLecheReader.CDecl},
  Ix.Kernel.ConLecheReader.readRecords cx st records = Except.ok (st', out) →
    (List.map Prod.fst records.toList).Nodup -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.ConLecheReader.readRecords_nodup

/-- info: @Ix.Ixon.ConLecheAdmission.Installed.singleton : ∀ {pins : Ix.Kernel.ConLecheReader.Pins}
  {pre : Ix.Kernel.ConLecheReader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {constants : List (Address × Ixon.Constant)} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.ConLecheAdmission.Installed pins pre natPins constants blobs hint env →
    ∀ {owner : Address} {c : Ixon.Constant},
      (owner, c) ∈ constants →
        Ix.Kernel.ConLecheReader.isSingleton c.info = true →
          ∃ st decl ds,
            Ix.Kernel.ConLecheReader.SingletonRead
                (Ix.Ixon.ConLecheAdmission.streamContext pins pre constants blobs hint) st owner c decl ∧
              decl ∈ ds ∧
                Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified natPins ds = Except.ok env ∧
                  ∀ (s : Ix.Kernel.Cached.InstallSkel),
                    Ix.Kernel.ConLecheFold.declSkel decl = some s →
                      ∃ ci, ci ∈ env.consts ∧ Ix.Kernel.Cached.ciSkel ci = s -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.ConLecheAdmission.Installed.singleton

/-- info: @Ix.Ixon.ConLecheAdmission.checkBytes_resources : ∀ {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : List (Address × ByteArray)}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
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

/-- info: Ix.Kernel.model_exists : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] (pins : List Ix.Kernel.NatOpPinSet)
  (ds : Array Ix.Kernel.Declaration) (env : Ix.Kernel.Env),
  Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified pins ds = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.model_exists

/-! ## The kernel-side modules and the import allowlists

The `Ix.Kernel` umbrella (the kernel-side boundary, including the committed
pin table and prelude, which read records through the canonical decoder)
stays inside `importAllowlist`; the Ixon reader, the record store, the
projection writer, bounded search outcomes and the pure Ixon types stay
inside `kernelImportAllowlist`. The allowlists admit `Std` and `Ix.Kernel`,
and `Lean` only below the ruled elaboration-time imports. -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Kernel] Ix.Kernel.Audit.importAllowlist Ix.Kernel.Audit.elaborationImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Kernel.Ixon.Reader, `Ix.Kernel.Ixon.ReaderSpec,
  `Ix.Kernel.Ingress.Records, `Ix.Kernel.Egress.Projection, `Ix.Kernel.Search, `Ix.Kernel.Ref,
  `Ix.Ixon.Types] Ix.Kernel.Audit.kernelImportAllowlist Ix.Kernel.Audit.elaborationImports

-- `Std` is admitted; the compiler frontend and third-party libraries are not.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Std.Data.TreeMap
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Command
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Batteries.Data.RBMap
-- `Ix.Kernel` is admitted; `Lean` only below the ruled elaboration-time imports.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Kernel.Core
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Term
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed `Lean.Elab.Term
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.importers `Ix.Kernel.Core
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed `Ix.Tc
