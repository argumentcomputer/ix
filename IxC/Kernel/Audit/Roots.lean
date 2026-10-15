import IxC.Kernel
import IxC.Ixon.Types
import IxC.Kernel.Admission.Theorems
import IxC.Kernel.Audit.Axioms
import IxC.Kernel.Audit.Imports
import IxC.Kernel.Audit.Runtime

/-! # The required roots and their frozen boundaries

This module is the certified gate's manifest. Its public roots are the
verified checker `Ix.Kernel.Cached.checkDecls` behind the Ixon reader: the
certified entry `Ix.Kernel.Admission.checkBytes` (and its prelude-parametric
form `checkBytesWith`, and `checkConstants`/`checkConstantsWith` over decoded
records), and the public theorems of `Ix.Kernel.Admission.Theorems` (model
existence, no proof of `False` at its role key, authentication of the records
and of the role table's binding section, fidelity, resources), all at every
content hash `hash` and every role table. The rulings `runtimeRulings` and
`elaborationImports` apply to them.

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

Expected values were measured before being frozen, and every change to a
frozen value is a deliberate update whose cause is stated where it is made.
The closures, as frozen below: the fold `Ix.Kernel.Cached.checkDecls`
reaches 3352 compiled functions with 67 inherited externs, with the
computed-field overrides of `Level`, `Expr` and `Key` and 20 proved
csimps; the Ixon reader (`readRecords` with `Admission.readStream`) reaches
2134, adding the in-model generator's 9 `partial` definitions and the codec's
TagN writer twin; the entry (the four `publicOperations`) reaches 5788 with
113 inherited externs, adding the byte stage (`preflight`, `uniqueKeys`,
`authenticate`, `decodeRecords`), the binding section's admission
(`admitBinding`, `RoleTable.ofBytes`, `RoleTable.check`), the committed
default table and prelude, and the codec's two TagN twins. Step 6's
structured errors (`CheckError md`: a message is prose and keys, `Msg md`, and
the checker never spells a key) moved them from 3446 and 5570, and the
fold's and the entry's inherited externs from 92 and 115; the reader is
unchanged:
* the fold: 130 fewer functions and 36 more closed terms. Key rendering
  (`Key.toName`, `Mode.idName`, `Derived.spell`, `Role.leanName`'s 121 closed
  terms, `Name.toString` and `Name`'s three computed-field overrides, which
  the fold no longer reaches: unsafe 24 to 21, ruled computed_field 20 to
  17), the `Repr` of terms two messages printed (`reprStr`, `Std.Format`),
  and the 25 string and printing externs they used (`String.append`,
  `String.extract`, `ByteArray.get!`, `UInt8` shifts, `USize.repr`, ...)
  went; a fixed message is now a one-part list (`[.text s]`), two more
  closed objects per message site;
* the entry: 39 fewer functions and 257 more closed terms. The reader still
  spells keys in its own `ReadError` messages and the in-model generator's,
  so the key rendering stays reachable there; the term printing and two
  string externs (`String.Internal.foldl`, `String.Internal.isEmpty`) went,
  and every message site of the fold adds its two closed objects.
The IxC
performance series (PERF P16, P14, P3, P2) moved them from 3439, 2127 and
5552, and the fold's and the entry's inherited externs from 90 and 113 to 92
and 115:
* P16, the memo state reset at every step of the fold (LOCALITY §6(a)): 7
  fewer in the fold and the entry. The converted-constant cache
  (`recordCConst`, `storedTyIdxM`, `storedValIdxM`) and its map's
  specialisations went; `resetC` and the empty state's closed terms came in;
  the level memos' map specialisations are now named after `isEquivLM` (the
  uncalled `simplifyLM` had named them).
* P14, shared binder metadata: 2 more in the fold (`BinderMeta.leanAlways`
  and its closed datum), 3 in the reader (`BinderMeta.leanNever` and two
  closed terms), 5 in the entry.
* P3, TagN without `Nat` powers: 4 more in the reader (`putTagNFast`,
  `putTagN0`, `putTagN2`, `putTagN4`: the projection-record serializer's
  writer), 8 in the entry (the reader's `getTagNFast`, `getTagN0/2/4` too).
  The codec's two `@[csimp]` replacements (`putTagN_eq_fast`,
  `getTagN_eq_fast`) are ruled (`runtimeRulings`): the reader's ruled csimps
  go from 7 to 8 and the entry's from 21 to 23, and the references they
  replace are still reached, from the twins' fallback for a width other
  than 0, 2 and 4 (csimp 0 to 1 and 4 to 6).
* P2, phase B of the fold on pure tasks: 12 more in the fold and the entry
  (`checkPendingTasks`, `chunksOf`, `awaitInOrder`, their auxiliaries and the
  task closure), among them the two new inherited externs, `Init`'s
  `Task.spawn` (`lean_task_spawn`) and `Task.get` (`lean_task_get_own`). As
  Lean functions they are `⟨fn ()⟩` and its field, so every theorem reads
  the sequential walk (`checkPendingTasks_eq`); what execution adds is
  Lean's runtime running a pure closure on another thread, the same
  runtime every compiled closure already trusts. No `unsafe`,
  `implemented_by`, `csimp` or `partial` constant came with them.
Step 5b's address keys (an `.anon` input key is the address its references use) moved
them from 3412, 2030 and 5578, and their inherited externs from 82, 79 and
111 to 90, 89 and 113, all `Init`'s: the fold compares and hashes addresses
(`ByteArray.decEq`, `ByteArray.get!`, `ByteArray.size`) and prints them in
its messages as twelve hexadecimal digits (`UInt8` shifts and masks,
`String.extract`, `String.Pos.next`); the reader keys a block member whose
projection record the input omits by that record's address under the entry's
hash, so it serializes the record (`ByteArray.push`, `copySlice`,
`emptyWithCapacity`, `UInt64.toUInt8`, `UInt8` shifts and `lor`,
`String.utf8ByteSize`); the hexadecimal key spelling (`keyName` and its
table) and the recursors' spelled keys left. Step 5b's
mode index (the kernel's types take a `Mode`) moved them from 3364, 2066 and
5566: the pinned names and the basis declarations are generic in the mode, so
their closed terms are hoisted where they are used rather than where they are
defined (closed terms and specialisations renumbered), and `Key.id`'s
override left the fold, which never builds an input key (`Inhabited (Key md)`
is a role key). Step 5b's
walk change (it visits the source `f` of every arity-reduced `f._redArg` it
reaches, `reducedAritySource?`) moved them from 3303, 2025 and 5474: the code
generator calls `f._redArg` directly, and `f` is where an `unsafe`,
`implemented_by`, `csimp` or `partial` status is recorded. No extern,
`unsafe`, `csimp` or `partial` constant came in with them. Step 5b's
`LetMeta` (a `letE` keeps its Ixon let contract) moved them from 3274, 2021
and 5447: the let contract's equality and hash (`Ixon.LetContract`,
`Ixon.LetKind`) and its `Repr` for the terms printed in messages. Step 5a
(typed keys) moved the counts from 3350, 2018 and 5656: `Key` became an
inductive with a cached hash, whose three constructor overrides
(`Key.{id,role,aux}._override`) the rulings admit with `Key`; a role key is
now `.role r`, so the closed name terms that spelled the role and derived
names went (121 in `evidenceDepKeys`, 121 in the reader's `bindingsOf`, one
to three per pinned-name constant and per derived-name helper), and the
rendering that prints keys in messages came in (`Key.toName`, with
`Role.leanName`'s 121 closed terms and `Derived.spell`'s 19), with `Key`'s,
`Role`'s and `Derived`'s derived instances; the rest are the compiler's
specialisations renumbered. Step 4
(primitives by specification) moved the counts from 3086, 1886 and 5224 with
120 externs: the fold gained the specification set (`IxC/Kernel/Roles.lean`)
and the evidence checks with their closure condition (`evidenceLocal`), the
reader the role bindings and the evidence resolution (`bindingsOf`,
`evidenceOf`), and the entry the binding section's decoder and
well-formedness check; the retired Nat-operation pin decoder took its string
scanning with it. The content hash is the entry's parameter, so no
hasher is in the closure. The byte stage reads and re-encodes Ixon v4's TagN integers
(`Ixon.getTagN`, `getTagNWide`, `getTagN0Values`, `putTagN`, `tagNHeader`,
`tagNEnd1..6`), and no other integer code. The committed default table and
prelude are hex strings decoded at first use (`bytesOfHex`). The eight
string-scanning externs the retired Nat-operation pin decoder brought in
(`String.decodeChar`, `String.Pos.next`, `UInt32.decLe`, `String.toUTF8` and
`String.Pos.Raw.{extract, next, get, atEnd}`) are no longer reached, nor is
`String.Slice.Pattern.Internal.memcmpStr`, which the retired pin table's
derived-shape check reached through `String.startsWith`: nine, 120 to 111
(the list is `Ix.Kernel.Admission.Audit`'s). No `unsafe`, `partial`,
`implemented_by` or csimp outside the rulings is reached. -/

open Lean

namespace Ix.Kernel.Audit

/-- The public theorems (`docs/kernel.md`, "The theorems"): model
existence, no proof of `False`, authentication (of the records and of the role
table's binding section) and resources for the kernel entry, at every hash,
at every role table and prelude, and the two con-leche-derived theorems they
rest on (`model_exists`, `no_False_theorem_accepted`). -/
def publicRoots : Array Lean.Name :=
  #[``Ix.Kernel.Admission.checkBytes_has_model, ``Ix.Kernel.Admission.checkBytesWith_has_model,
    ``Ix.Kernel.Admission.checkConstants_has_model,
    ``Ix.Kernel.Admission.checkConstantsWith_has_model,
    ``Ix.Kernel.Admission.checkBytes_has_model_values,
    ``Ix.Kernel.Admission.checkBytesWith_has_model_values,
    ``Ix.Kernel.Admission.checkBytes_no_proof_of_False,
    ``Ix.Kernel.Admission.checkBytesWith_no_proof_of_False,
    ``Ix.Kernel.Admission.checkBytes_no_False_theorem,
    ``Ix.Kernel.Admission.checkBytesWith_no_False_theorem,
    ``Ix.Kernel.Admission.checkBytesWith_no_False_reference,
    ``Ix.Kernel.Admission.checkBytes_authentic, ``Ix.Kernel.Admission.checkBytesWith_authentic,
    ``Ix.Kernel.Admission.checkBytes_binding, ``Ix.Kernel.Admission.checkBytesWith_binding,
    ``Ix.Kernel.Admission.checkConstantsAt_has_model,
    ``Ix.Kernel.Admission.checkBytes_resources, ``Ix.Kernel.Admission.checkBytesWith_resources,
    ``Ix.Kernel.model_exists, ``Ix.Kernel.no_False_theorem_accepted]

/-- Fidelity and the facts it is built from: the reading of accepted bytes,
key uniqueness and authentication, the binding section's admission and
canonical decoding, the record-by-record reading of the reader, per-record
installation, and the keys the reader gives a reference and a member: the
address it is keyed by, or its role (`Ctx.keyAt_eq_ok`,
`Ctx.memberKey_of_unbound`). -/
def fidelityRoots : Array Lean.Name :=
  #[``Ix.Kernel.Admission.checkBytes_reading, ``Ix.Kernel.Admission.checkBytesWith_reading,
    ``Ix.Kernel.Admission.checkConstantsWith_installed, ``Ix.Kernel.Admission.Installed.skels,
    ``Ix.Kernel.Admission.Installed.singleton, ``Ix.Kernel.Admission.checkBytesWith_eq,
    ``Ix.Kernel.Admission.checkBytes_with, ``Ix.Kernel.Admission.checkConstants_with,
    ``Ix.Kernel.Reader.readRecords_spec, ``Ix.Kernel.Reader.readRecords_nodup,
    ``Ix.Kernel.Admission.uniqueKeys_ok_iff, ``Ix.Kernel.Admission.authenticate_ok_iff,
    ``Ix.Kernel.Admission.admitBinding_ok_iff, ``Ix.Kernel.RoleTable.ofBytes_eq_some_iff,
    ``Ix.Kernel.RoleTable.ofBytes_toBytes, ``Ix.Kernel.Admission.readStream_spec,
    ``Ix.Kernel.Reader.readRecord_singleton,
    ``Ix.Kernel.Reader.StreamRead.singleton, ``Ix.Kernel.Reader.Ctx.keyAt_eq_ok,
    ``Ix.Kernel.Reader.Ctx.memberKey_of_unbound,
    ``Ix.Kernel.Cached.checkDecls_installs, ``Ix.Kernel.Cached.checkDecls_model_defn_values]

/-- The executable entry whose runtime closure is audited: the certified entry
`Ix.Kernel.Admission.checkBytes`, which runs the verified fold behind the Ixon
reader, and that entry over explicit tables and over decoded records. -/
def publicOperations : Array Lean.Name :=
  #[``Ix.Kernel.Admission.checkBytes, ``Ix.Kernel.Admission.checkBytesWith,
    ``Ix.Kernel.Admission.checkConstantsWith, ``Ix.Kernel.Admission.checkConstants]

/-- The verified fold, the kernel of the entry. -/
def kernelOperations : Array Lean.Name := #[``Ix.Kernel.Cached.checkDecls]

/-- The Ixon reader of the entry. -/
def readerOperations : Array Lean.Name :=
  #[``Ix.Kernel.Reader.readRecords, ``Ix.Kernel.Admission.readStream]

/-- The certified entry's module, whose import closure is audited. -/
def publicModules : Array Lean.Name := #[`IxC.Kernel.Admission]

/-- Module prefixes the kernel-side modules may use: Lean core (`Init` and
`Std`, which ships with the toolchain), the kernel `Ix.Kernel` (the checker
and Ix's Ixon boundary beside it), the pure address key and the pure Ixon
types. It fences the Ixon reader, the record store, the projection writer
and the pure Ixon types (below), and is the base of `importAllowlist`. `Std`
is admitted for its maps and their lemmas, which the kernel uses;
`Classical.choice` reaching kernel definitions through it is accepted, and
the axiom guards below record where. No `Lean` or `Batteries` module,
nothing else under `Ix`, and no `Blake3`, `LSpec`, `Cli`, or `lean4lean`
module may enter; `Lean` enters `Ix.Kernel` only at elaboration time
(`elaborationImports`). -/
def kernelImportAllowlist : Array Lean.Name :=
  #[`Init, `Std, `IxC.Kernel, `IxC.Address.Core, `IxC.Ixon.Types]

/-- The modules under `Ix.Kernel` that the kernel-side modules may not use:
the certified entry, which runs the kernel and the byte stage beside it, and
the audits. -/
def kernelImportDenylist : Array Lean.Name := #[`IxC.Kernel.Admission, `IxC.Kernel.Audit]

/-- Module prefixes the certified import closure may use: the kernel-side
list (`kernelImportAllowlist`), plus exactly the modules of the entry's byte
stage, as the import closure of `Ix.Kernel.Admission` has them.
Each is pure Lean core and is audited on its own terms elsewhere:
* `Ix.Ixon.Codec`, `Ix.Ixon.Wire`, `Ix.Ixon.WireCheck`,
  `Ix.Ixon.Bounded.Constant`, `Ix.Ixon.Bounded.Universe`, `Ix.Ixon.Canonical`:
  the canonical per-record decoder and its readers (`Ixon.Audit`, whose
  `dataImports` is `Init` and these);
* `Ix.Kernel.Admission`: the certified entry, and `Ix.Kernel.Admission.Bytes`,
  the batch limits (`preflight`) and the decoding loop (`decodeRecords`)
  (`Ix.Kernel.Admission.Audit`).
Nothing else under `Ix.Ixon` (in particular no projection hashing,
`Ix.Address.Pure`, block order or proof module: `importDenylist` carves the
entry's theorem and audit modules out of `Ix.Kernel.Admission`) and still no
`Lean` outside the ruled elaboration-time edges. -/
def importAllowlist : Array Lean.Name :=
  kernelImportAllowlist ++ #[`IxC.Ixon.Codec, `IxC.Ixon.Wire, `IxC.Ixon.WireCheck,
    `IxC.Ixon.Bounded.Constant, `IxC.Ixon.Bounded.Universe, `IxC.Ixon.Canonical, `IxC.Kernel.Admission]

/-- The modules under `importAllowlist`'s prefixes that the certified import
closure may not use: the entry's theorems and audit. -/
def importDenylist : Array Lean.Name :=
  #[`IxC.Kernel.Admission.Theorems, `IxC.Kernel.Admission.Bytes.Theorems, `IxC.Kernel.Admission.Audit,
    `IxC.Kernel.Audit]

/-- The proofs of the public theorems may additionally use the Ixon codec's
proof modules (`Ix.Ixon.Verify`, `Ix.Ixon.Bounded.Size`, with their Lean
proof tooling) and the theorem module itself. -/
def proofImportAllowlist : Array Lean.Name :=
  importAllowlist ++ #[`IxC.Ixon.Bounded.Size, `IxC.Ixon.Verify, `IxC.Kernel.Admission.Theorems, `Lean]

/-- The kernel's elaboration-time imports:
`IxC/Kernel/BasisGen.lean` (`public meta import Lean`) splices the
annotated basis and pins. Below these edges only Lean core, `Lean`, and
`Ix.Kernel` may appear. Upstream's pin generators and JSON pin dumps
(`PinGen*.lean`, `NatOpPins.lean`) are not carried here: the operations'
evidence comes with the role table, and the default table's from Ixon
(`IxC/Kernel/Ixon/RoleData.lean`). -/
def elaborationImports : ElaborationImports where
  importers := #[`IxC.Kernel.BasisGen]
  allowed := #[`Init, `Std, `Lean, `IxC.Kernel]

/-- Modules whose execution replacements are inherited Lean runtime. -/
def runtimeAllowlist : Array Lean.Name := #[`Init, `Std]

/-- The ruled exceptions to the runtime audit (`docs/kernel.md`, "Trust
surface"). Each names exactly what it admits:
* the `@[computed_field]` overrides of the kernel's `Level` (`hashData`),
  `Expr` (`data`), `Name` (`hashData`) and `Key` (`hashData`);
* project `@[csimp]` replacements in `Ix.Kernel`, each only with a theorem
  on the standard axioms;
* the Ixon codec's two `@[csimp]` replacements (`IxC/Ixon/Codec.lean`):
  `getTagN_eq_fast` and `putTagN_eq_fast`, the TagN reader and writer at a
  fixed flag width with their powers folded (PERF P3), again each only with a
  theorem on the standard axioms;
* `withPtrEq`, `withPtrAddr`, their `unsafe` implementations, and
  the pointer reads under them; and `isExclusiveUnsafe`, the reference-count
  read behind `withExclusive` (all `Init`, so already inherited);
* `Ix.Kernel.withExclusive`, `implemented_by` `Ix.Kernel.withExclusiveUnsafe`,
  whose type carries the obligation `k true = k false`;
* elaboration-time `meta` code in `BasisGen`
  (`unsafe evalTerm` wrappers paired by `implemented_by`), which compiled
  non-`meta` code cannot call;
* `partial` definitions of the in-model generator,
  `IxC/Kernel/Frontend/InModel*`.

No substitution is admitted on an assumption (`assumed` is empty): the
kernel's closures take their content hash as a parameter. -/
def runtimeRulings : RuntimeRulings where
  computedFieldTypes := #[`Ix.Kernel.Level, `Ix.Kernel.Expr, `Ix.Kernel.Name, `Ix.Kernel.Key]
  csimpModules := #[`IxC.Kernel, `IxC.Ixon.Codec]
  primitives := #[``withPtrEq, ``withPtrEqUnsafe, ``withPtrEqDecEq, ``withPtrAddr,
    ``withPtrAddrUnsafe, ``ptrEq, ``ptrAddrUnsafe, ``isExclusiveUnsafe]
  implementations := #[(`Ix.Kernel.withExclusive, `Ix.Kernel.withExclusiveUnsafe)]
  elaborationModules := #[`IxC.Kernel.BasisGen]
  partialModules := #[`IxC.Kernel.Frontend.InModel]

/-- The one execution substitution admitted on an assumption rather than a
proof (owner, 2026-10-13; `docs/kernel.md`, "Trust surface"): the root
library's admission hash `Address.admissionHash`
(`Ix/Address/Admission.lean`), defined as pure BLAKE3 (`Address.blake3Pure`),
executes as the Rust BLAKE3 `Address.blake3` (`@[implemented_by]`), on the
explicit assumption that the two agree on every input
(`Tests.Ix.Kernel.AddressPure` compares them on fixture inputs); with it, the
Rust backend's foreign primitives. The root library's authenticated entries
(`Ixon.Authenticated`) are audited with `runtimeRulings` and exactly this
list; no kernel closure admits it. -/
def assumedSubstitutions : Array AssumedSubstitution :=
  #[{ source := `Address.admissionHash, target := `Address.blake3,
      externs := #[`Blake3.Rust.hasherInit, `Blake3.Rust.hasherUpdate, `Blake3.Rust.hasherFinalize] }]

end Ix.Kernel.Audit

/-! ## The certified entry: the verified fold behind the Ixon reader

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

#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkConstants_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkConstantsWith_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_no_False_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_binding [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_binding [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkConstantsAt_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.admitBinding_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.RoleTable.ofBytes_eq_some_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.RoleTable.ofBytes_toBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.readStream_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.model_exists [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.no_False_theorem_accepted [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkConstantsWith_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.Installed.skels [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.Installed.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_with [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkConstants_with [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.readRecords_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.readRecords_nodup [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.uniqueKeys_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.authenticate_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith_authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.readRecord_singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.StreamRead.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.Ctx.keyAt_eq_ok [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.Ctx.memberKey_of_unbound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.checkDecls_installs [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.checkDecls_model_defn_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytesWith [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkConstantsWith [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkConstants [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.checkDecls [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.readRecords [propext, Classical.choice, Quot.sound]

/-! ### Import and runtime closures

The entry's import closure stays inside `importAllowlist`, below the ruled
elaboration-time edges inside `elaborationImports.allowed`; the theorems'
closure inside `proofImportAllowlist`. The runtime closures are frozen with
the rulings they use: the fold reaches the kernel's computed-field
overrides of `Level`, `Expr`, `Name` and `Key` (21) and 20 project csimps; the
reader adds the in-model generator's 9 `partial` definitions and the codec's
TagN writer twin (a ruled csimp); the entry adds the byte stage, the binding
section's admission, the committed default table and prelude and the codec's
TagN reader twin. -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith Ix.Kernel.Audit.publicModules Ix.Kernel.Audit.importAllowlist Ix.Kernel.Audit.elaborationImports Ix.Kernel.Audit.importDenylist

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`IxC.Kernel.Admission.Theorems] Ix.Kernel.Audit.proofImportAllowlist Ix.Kernel.Audit.elaborationImports

-- The entry's byte stage is admitted; projection hashing, block order, the
-- codec proofs and `kernelImportAllowlist` are not widened.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `IxC.Ixon.Canonical Ix.Kernel.Audit.importDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `IxC.Kernel.Admission Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Projection Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.BlockOrder Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `IxC.Ixon.Verify Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `IxC.Kernel.Admission.Theorems Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `IxC.Kernel.Admission.Bytes.Theorems Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `IxC.Kernel.Admission.Audit Ix.Kernel.Audit.importDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `IxC.Kernel.Admission.Bytes Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Address.Pure Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Data.Json Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `IxC.Ixon.Canonical Ix.Kernel.Audit.kernelImportDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `IxC.Kernel.Admission Ix.Kernel.Audit.kernelImportDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `IxC.Kernel.Admission.Bytes Ix.Kernel.Audit.kernelImportDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `IxC.Kernel.Audit.Roots Ix.Kernel.Audit.kernelImportDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `IxC.Kernel.Ixon.Reader Ix.Kernel.Audit.kernelImportDenylist

/-- info: runtime closure of [Ix.Kernel.Cached.checkDecls]: 3352 compiled functions; inherited externs 67, implemented_by 0, unsafe 21, csimp 4; ruled computed_field 17, csimp 20 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.Reader.readRecords,
 Ix.Kernel.Admission.readStream]: 2134 compiled functions; inherited externs 89, implemented_by 0, unsafe 26, csimp 1; ruled computed_field 21, csimp 8, partial 9 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.readerOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.Admission.checkBytes,
 Ix.Kernel.Admission.checkBytesWith,
 Ix.Kernel.Admission.checkConstantsWith,
 Ix.Kernel.Admission.checkConstants]: 5788 compiled functions; inherited externs 113, implemented_by 0, unsafe 26, csimp 6; ruled computed_field 21, csimp 23, partial 9 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.publicOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

-- Without the rulings the entry's closure fails: they are what admits it.
/-- error: project-level execution replacements reached from [Ix.Kernel.Cached.checkDecls] -/
#guard_msgs (substring := true) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist

/-! ### Frozen statements -/

/-- info: Ix.Kernel.Admission.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
  {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_has_model

/-- info: Ix.Kernel.Admission.checkBytesWith_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {pre : Ix.Kernel.Reader.Prelude Ix.Kernel.Mode.anon} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytesWith hash binding pre limits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytesWith_has_model

/-- info: Ix.Kernel.Admission.checkBytes_has_model_values : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∃ M,
      ∀ (cv : Ix.Kernel.ConstantVal Ix.Kernel.Mode.anon) (value : Ix.Kernel.Expr Ix.Kernel.Mode.anon)
        (hint' : Ix.Kernel.ReducibilityHint),
        Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
          ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
            Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_has_model_values

/-- info: Ix.Kernel.Admission.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
  {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const (Ix.Kernel.roleKey Ix.Kernel.Role.false) [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_no_proof_of_False

/-- info: Ix.Kernel.Admission.checkBytesWith_no_False_theorem : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {pre : Ix.Kernel.Reader.Prelude Ix.Kernel.Mode.anon} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytesWith hash binding pre limits records blobs hint = Except.ok env →
    ∀ {t : Ix.Kernel.RoleTable},
      Ix.Kernel.Admission.admitBinding hash binding = Except.ok t →
        ∀ {constants : List (Address × Ixon.Constant)},
          Ix.Kernel.Admission.RecordsRead limits records constants →
            ∀ {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition},
              (owner, c) ∈ constants →
                c.info = Ixon.ConstantInfo.defn d →
                  d.kind = Ix.DefKind.thm →
                    (Ix.Kernel.Reader.definitionReader
                              (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) owner c d).read
                          d.typ =
                        Except.ok (Ix.Kernel.Expr.const (Ix.Kernel.roleKey Ix.Kernel.Role.false) []) →
                      False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytesWith_no_False_theorem

/-- info: @Ix.Kernel.Admission.checkBytes_reading : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∃ t pre,
      Ix.Kernel.Admission.admitBinding hash binding = Except.ok t ∧
        Ix.Kernel.Reader.preludeFor t = Except.ok pre ∧
          Ix.Kernel.Admission.WithinBatch limits records blobs ∧
            Ix.Kernel.Admission.UniqueKeys records blobs ∧
              Ix.Kernel.Admission.Authentic hash records blobs ∧
                ∃ constants,
                  Ix.Kernel.Admission.BindingAdmitted hash binding t ∧
                    Ix.Kernel.Admission.RecordsRead limits records constants ∧
                      Ix.Kernel.Admission.Hashed hash constants ∧
                        Ix.Kernel.Admission.Installed hash t pre constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_reading

/-- info: @Ix.Kernel.Admission.checkBytes_authentic : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.Authentic hash records blobs ∧ hash binding.bytes = binding.address -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_authentic

/-- info: @Ix.Kernel.Admission.checkBytesWith_reading : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {pre : Ix.Kernel.Reader.Prelude Ix.Kernel.Mode.anon} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytesWith hash binding pre limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.WithinBatch limits records blobs ∧
      Ix.Kernel.Admission.UniqueKeys records blobs ∧
        Ix.Kernel.Admission.Authentic hash records blobs ∧
          ∃ t constants,
            Ix.Kernel.Admission.BindingAdmitted hash binding t ∧
              Ix.Kernel.Admission.RecordsRead limits records constants ∧
                Ix.Kernel.Admission.Hashed hash constants ∧
                  Ix.Kernel.Admission.Installed hash t pre constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytesWith_reading

/-- info: Ix.Kernel.Admission.uniqueKeys_ok_iff : ∀ (records : Ix.Kernel.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Kernel.Admission.uniqueKeys records blobs = Except.ok () ↔ Ix.Kernel.Admission.UniqueKeys records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.uniqueKeys_ok_iff

/-- info: Ix.Kernel.Admission.authenticate_ok_iff : ∀ (hash : ByteArray → Address) (records : Ix.Kernel.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Kernel.Admission.authenticate hash records blobs = Except.ok () ↔ Ix.Kernel.Admission.Authentic hash records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.authenticate_ok_iff

-- What authentication states, for the bytes and for the decoded records.
/-- info: def Ix.Kernel.Admission.Authentic : (ByteArray → Address) →
  Ix.Kernel.Admission.Records → Ix.Kernel.Ingress.Blobs → Prop :=
fun hash records blobs =>
  (∀ (entry : Address × ByteArray), entry ∈ records → entry.fst = hash entry.snd) ∧
    ∀ (entry : Address × ByteArray), entry ∈ blobs → entry.fst = hash entry.snd -/
#guard_msgs (whitespace := lax) in
#print Ix.Kernel.Admission.Authentic

/-- info: def Ix.Kernel.Admission.Hashed : (ByteArray → Address) → Ix.Kernel.Ingress.Constants → Prop :=
fun hash constants =>
  ∀ (entry : Address × Ixon.Constant), entry ∈ constants → entry.fst = hash (Ixon.serConstant entry.snd) -/
#guard_msgs (whitespace := lax) in
#print Ix.Kernel.Admission.Hashed

/-- info: @Ix.Kernel.Reader.readRecords_nodup : ∀ {md : Ix.Kernel.Mode} {cx : Ix.Kernel.Reader.Ctx md}
  {st st' : Ix.Kernel.Reader.State md} {records : Array (Address × Ixon.Constant)}
  {out : Array (Ix.Kernel.Reader.CDecl md)},
  Ix.Kernel.Reader.readRecords cx st records = Except.ok (st', out) → (List.map Prod.fst records.toList).Nodup -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Reader.readRecords_nodup

/-- info: @Ix.Kernel.Admission.Installed.singleton : ∀ {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
  {pre : Ix.Kernel.Reader.Prelude Ix.Kernel.Mode.anon} {constants : List (Address × Ixon.Constant)}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.Installed hash t pre constants blobs hint env →
    ∀ {owner : Address} {c : Ixon.Constant},
      (owner, c) ∈ constants →
        Ix.Kernel.Reader.isSingleton c.info = true →
          ∃ st decl ev ds,
            Ix.Kernel.Reader.SingletonRead (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) st owner
                c decl ∧
              decl ∈ ds ∧
                Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified ev ds = Except.ok env ∧
                  ∀ (s : Ix.Kernel.Cached.InstallSkel Ix.Kernel.Mode.anon),
                    Ix.Kernel.Cached.declSkel decl = some s → ∃ ci, ci ∈ env.consts ∧ Ix.Kernel.Cached.ciSkel ci = s -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.Installed.singleton

/-- info: @Ix.Kernel.Admission.checkBytes_resources : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∃ constants,
      Ix.Kernel.Admission.RecordsRead limits records constants ∧
        Ix.Kernel.Admission.resourceUnits constants ≤
          2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_resources

/-- info: @Ix.Kernel.Admission.checkBytes_binding : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∃ t, Ix.Kernel.Admission.BindingAdmitted hash binding t -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_binding

/-- info: Ix.Kernel.Admission.admitBinding_ok_iff : ∀ (hash : ByteArray → Address) (b : Ix.Kernel.Admission.Binding)
  (t : Ix.Kernel.RoleTable),
  Ix.Kernel.Admission.admitBinding hash b = Except.ok t ↔ Ix.Kernel.Admission.BindingAdmitted hash b t -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.admitBinding_ok_iff

/-- info: structure Ix.Kernel.Admission.BindingAdmitted (hash : ByteArray → Address) (b : Ix.Kernel.Admission.Binding)
  (t : Ix.Kernel.RoleTable) : Prop
number of parameters: 3
fields:
  Ix.Kernel.Admission.BindingAdmitted.authentic : hash b.bytes = b.address
  Ix.Kernel.Admission.BindingAdmitted.canonical : t.wireWF = true ∧ t.toBytes = b.bytes
  Ix.Kernel.Admission.BindingAdmitted.wellFormed : t.check = Except.ok ()
constructor:
  Ix.Kernel.Admission.BindingAdmitted.mk {hash : ByteArray → Address} {b : Ix.Kernel.Admission.Binding}
    {t : Ix.Kernel.RoleTable} (authentic : hash b.bytes = b.address) (canonical : t.wireWF = true ∧ t.toBytes = b.bytes)
    (wellFormed : t.check = Except.ok ()) : Ix.Kernel.Admission.BindingAdmitted hash b t -/
#guard_msgs (whitespace := lax) in
#print Ix.Kernel.Admission.BindingAdmitted

/-- info: Ix.Kernel.RoleTable.ofBytes_eq_some_iff : ∀ (bytes : ByteArray) (t : Ix.Kernel.RoleTable),
  Ix.Kernel.RoleTable.ofBytes bytes = some t ↔ t.wireWF = true ∧ t.toBytes = bytes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.RoleTable.ofBytes_eq_some_iff

/-- info: @Ix.Kernel.Reader.Ctx.keyAt_eq_ok : ∀ {md : Ix.Kernel.Mode} {cx : Ix.Kernel.Reader.Ctx md} {a : Address}
  {k : Ix.Kernel.Reader.CName md}, cx.keyAt a = Except.ok k ↔ Ix.Kernel.Reader.keyOfAddress cx.store cx.roles a = some k -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Reader.Ctx.keyAt_eq_ok

/-- info: @Ix.Kernel.Reader.Ctx.memberKey_of_unbound : ∀ {md : Ix.Kernel.Mode} {cx : Ix.Kernel.Reader.Ctx md}
  {r : Ix.Kernel.ConstRef Address} {a : Address} {k : Ix.Kernel.Reader.CName md},
  cx.roles.names[r]? = none →
    cx.keys.address[r]? = some a →
      cx.memberKey r = Except.ok k →
        Ix.Kernel.Reader.resolve cx.store a = some r ∧ ∃ i, md.addressId? a = some i ∧ k = Ix.Kernel.Key.id i -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Reader.Ctx.memberKey_of_unbound

/-- info: @Ix.Kernel.model_exists : ∀ {md : Ix.Kernel.Mode} [md.Certified] (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  (ev : Ix.Kernel.Evidences md) (ds : Array (Ix.Kernel.Declaration md)) (env : Ix.Kernel.Env md),
  Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified ev ds = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
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
run_cmd Ix.Kernel.Audit.checkImportsWith #[`IxC.Kernel] Ix.Kernel.Audit.importAllowlist Ix.Kernel.Audit.elaborationImports Ix.Kernel.Audit.importDenylist

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`IxC.Kernel.Ixon.Reader, `IxC.Kernel.Ixon.ReaderSpec,
  `IxC.Kernel.Ingress.Records, `IxC.Kernel.Egress.Projection, `IxC.Kernel.Search, `IxC.Kernel.Ref,
  `IxC.Ixon.Types] Ix.Kernel.Audit.kernelImportAllowlist Ix.Kernel.Audit.elaborationImports Ix.Kernel.Audit.kernelImportDenylist

-- `Std` is admitted; the compiler frontend and third-party libraries are not.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Std.Data.TreeMap Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Command Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Batteries.Data.RBMap Ix.Kernel.Audit.importDenylist
-- `Ix.Kernel` is admitted; `Lean` only below the ruled elaboration-time imports.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `IxC.Kernel.Core Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Term Ix.Kernel.Audit.importDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed `Lean.Elab.Term
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.importers `IxC.Kernel.Core
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed `Ix.Tc
