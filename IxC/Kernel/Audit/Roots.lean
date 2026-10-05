import IxC.Kernel
import IxC.Ixon.Types
import IxC.Kernel.Admission.Theorems
import IxC.Kernel.Audit.Axioms
import IxC.Kernel.Audit.Imports
import IxC.Kernel.Audit.Runtime

/-! # The required roots and their frozen boundaries

This module is the certified gate's manifest. Its public roots are the
verified checker `Ix.Kernel.Cached.checkDecls` behind the Ixon reader: the
certified entry `Ix.Kernel.Admission.checkBytes` (and its pin-parametric form
`checkBytesWith`, and `checkConstants`/`checkConstantsWith` over decoded
records), and the public theorems of `Ix.Kernel.Admission.Theorems` (model
existence, no proof of the pinned `False`, fidelity, resources). The rulings `runtimeRulings` and
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
reaches 3022 compiled functions, with the computed-field overrides of
`Level`, `Expr` and `Name` and 20 proved csimps; the Ixon reader
(`readRecords` with `Admission.readStream`) reaches 1886, adding the
in-model generator's 10 `partial` definitions; the entry (the four
`publicOperations`) reaches 5295 with 121 inherited externs, adding the
byte stage (`preflight`, `uniqueKeys`, `decodeRecords`) and the committed
tables. The byte stage reads and re-encodes Ixon v4's TagN integers
(`Ixon.getTagN`, `getTagNWide`, `getTagN0Values`, `putTagN`, `tagNHeader`,
`tagNEnd1..6`), and no other integer code. The committed Nat-operation pins (`builtinNatOpPins`) are decoded
from a string table at first use, which brings in the eight string-scanning
externs `String.decodeChar`, `String.Pos.next`, `UInt32.decLe`,
`String.toUTF8` and `String.Pos.Raw.{extract, next, get, atEnd}`. No
`unsafe`, `partial`, `implemented_by` or csimp outside the rulings is
reached. -/

open Lean

namespace Ix.Kernel.Audit

/-- The public theorems (`docs/kernel.md`, "The theorems"): model
existence, no proof of the pinned `False`, and resources for the kernel entry,
at the committed tables and at every pin table, prelude and Nat-operation pin
list, and the two con-leche-derived theorems they rest on (`model_exists`,
`no_False_theorem_accepted`). -/
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
    ``Ix.Kernel.Admission.checkBytes_resources, ``Ix.Kernel.Admission.checkBytesWith_resources,
    ``Ix.Kernel.model_exists, ``Ix.Kernel.no_False_theorem_accepted]

/-- Fidelity and the facts it is built from: the reading of accepted bytes, the record-by-record reading of the
reader, per-record installation, and the address encoding's injectivity. -/
def fidelityRoots : Array Lean.Name :=
  #[``Ix.Kernel.Admission.checkBytes_reading, ``Ix.Kernel.Admission.checkBytesWith_reading,
    ``Ix.Kernel.Admission.checkConstantsWith_installed, ``Ix.Kernel.Admission.Installed.skels,
    ``Ix.Kernel.Admission.Installed.singleton, ``Ix.Kernel.Admission.checkBytesWith_eq,
    ``Ix.Kernel.Admission.checkBytes_with, ``Ix.Kernel.Admission.checkConstants_with,
    ``Ix.Kernel.Reader.readRecords_spec, ``Ix.Kernel.Reader.readRecords_nodup,
    ``Ix.Kernel.Admission.uniqueKeys_ok_iff, ``Ix.Kernel.Reader.readRecord_singleton,
    ``Ix.Kernel.Reader.StreamRead.singleton, ``Ix.Kernel.Reader.keyName_injective,
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
(`PinGen*.lean`, `NatOpPins.lean`) are not carried here: the Nat-operation pins
come from Ixon (`IxC/Kernel/Ixon/NatOpPinData.lean`). -/
def elaborationImports : ElaborationImports where
  importers := #[`IxC.Kernel.BasisGen]
  allowed := #[`Init, `Std, `Lean, `IxC.Kernel]

/-- Modules whose execution replacements are inherited Lean runtime. -/
def runtimeAllowlist : Array Lean.Name := #[`Init, `Std]

/-- The ruled exceptions to the runtime audit (`docs/kernel.md`, "Trust
surface"). Each names exactly what it admits:
* the `@[computed_field]` overrides of the kernel's `Level` (`hashData`),
  `Expr` (`data`) and `Name` (`hashData`);
* project `@[csimp]` replacements in `Ix.Kernel`, each only with a theorem
  on the standard axioms;
* `withPtrEq`, `withPtrAddr`, their `unsafe` implementations, and
  the pointer reads under them; and `isExclusiveUnsafe`, the reference-count
  read behind `withExclusive` (all `Init`, so already inherited);
* `Ix.Kernel.withExclusive`, `implemented_by` `Ix.Kernel.withExclusiveUnsafe`,
  whose type carries the obligation `k true = k false`;
* elaboration-time `meta` code in `BasisGen`
  (`unsafe evalTerm` wrappers paired by `implemented_by`), which compiled
  non-`meta` code cannot call;
* `partial` definitions of the in-model generator,
  `IxC/Kernel/Frontend/InModel*`. -/
def runtimeRulings : RuntimeRulings where
  computedFieldTypes := #[`Ix.Kernel.Level, `Ix.Kernel.Expr, `Ix.Kernel.Name]
  csimpModules := #[`IxC.Kernel]
  primitives := #[``withPtrEq, ``withPtrEqUnsafe, ``withPtrEqDecEq, ``withPtrAddr,
    ``withPtrAddrUnsafe, ``ptrEq, ``ptrAddrUnsafe, ``isExclusiveUnsafe]
  implementations := #[(`Ix.Kernel.withExclusive, `Ix.Kernel.withExclusiveUnsafe)]
  elaborationModules := #[`IxC.Kernel.BasisGen]
  partialModules := #[`IxC.Kernel.Frontend.InModel]

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
#guard_kernel_axioms Ix.Kernel.Reader.readRecord_singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.StreamRead.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Reader.keyName_injective [propext, Classical.choice, Quot.sound]
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
overrides of `Level`, `Expr` and `Name` (18) and 20 project csimps; the
reader adds the in-model generator's 10 `partial` definitions; the entry
adds the byte stage and the committed tables. The pin-parametric forms
(`checkBytesWith`, `checkConstantsWith`) reach 4525 functions; the
committed pin table, prelude and Nat-operation pin decoder add the rest. -/

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

/-- info: runtime closure of [Ix.Kernel.Cached.checkDecls]: 3022 compiled functions; inherited externs 83,
implemented_by 0, unsafe 22, csimp 4; ruled computed_field 18, csimp 20 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.Reader.readRecords,
 Ix.Kernel.Admission.readStream]: 1886 compiled functions; inherited externs 82, implemented_by 0,
unsafe 23, csimp 0; ruled computed_field 18, csimp 7, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.readerOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.Admission.checkBytes,
 Ix.Kernel.Admission.checkBytesWith,
 Ix.Kernel.Admission.checkConstantsWith,
 Ix.Kernel.Admission.checkConstants]: 5295 compiled functions; inherited externs 121, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.publicOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

-- Without the rulings the entry's closure fails: they are what admits it.
/-- error: project-level execution replacements reached from [Ix.Kernel.Cached.checkDecls] -/
#guard_msgs (substring := true) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist

/-! ### Frozen statements -/

/-- info: Ix.Kernel.Admission.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes limits records blobs hint = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_has_model

/-- info: Ix.Kernel.Admission.checkBytesWith_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {pins : Ix.Kernel.Reader.Pins} {pre : Ix.Kernel.Reader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytesWith_has_model

/-- info: Ix.Kernel.Admission.checkBytes_has_model_values : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ M,
      ∀ (cv : Ix.Kernel.ConstantVal) (value : Ix.Kernel.Expr) (hint' : Ix.Kernel.ReducibilityHint),
        Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
          ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
            Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_has_model_values

/-- info: Ix.Kernel.Admission.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_no_proof_of_False

/-- info: Ix.Kernel.Admission.checkBytesWith_no_False_theorem : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {pins : Ix.Kernel.Reader.Pins} {pre : Ix.Kernel.Reader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    ∀ {constants : List (Address × Ixon.Constant)},
      Ix.Kernel.Admission.RecordsRead limits records constants →
        ∀ {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition},
          (owner, c) ∈ constants →
            c.info = Ixon.ConstantInfo.defn d →
              d.kind = Ix.DefKind.thm →
                (Ix.Kernel.Reader.definitionReader
                          (Ix.Kernel.Admission.streamContext pins pre constants blobs hint) owner c d).read
                      d.typ =
                    Except.ok (Ix.Kernel.Expr.const Ix.Kernel.falseName []) →
                  False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytesWith_no_False_theorem

/-- info: @Ix.Kernel.Admission.checkBytes_reading : ∀ {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ pins pre natPins,
      Ix.Kernel.Reader.defaultPins = Except.ok pins ∧
        Ix.Kernel.Reader.builtinPrelude = Except.ok pre ∧
          Ix.Kernel.Reader.builtinNatOpPins = Except.ok natPins ∧
            Ix.Kernel.Admission.WithinBatch limits records blobs ∧
              Ix.Kernel.Admission.UniqueKeys records blobs ∧
                ∃ constants,
                  Ix.Kernel.Admission.RecordsRead limits records constants ∧
                    Ix.Kernel.Admission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_reading

/-- info: @Ix.Kernel.Admission.checkBytesWith_reading : ∀ {pins : Ix.Kernel.Reader.Pins}
  {pre : Ix.Kernel.Reader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.WithinBatch limits records blobs ∧
      Ix.Kernel.Admission.UniqueKeys records blobs ∧
        ∃ constants,
          Ix.Kernel.Admission.RecordsRead limits records constants ∧
            Ix.Kernel.Admission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytesWith_reading

/-- info: Ix.Kernel.Admission.uniqueKeys_ok_iff : ∀ (records : Ix.Kernel.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Kernel.Admission.uniqueKeys records blobs = Except.ok () ↔ Ix.Kernel.Admission.UniqueKeys records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.uniqueKeys_ok_iff

/-- info: @Ix.Kernel.Reader.readRecords_nodup : ∀ {cx : Ix.Kernel.Reader.Ctx}
  {st st' : Ix.Kernel.Reader.State} {records : Array (Address × Ixon.Constant)}
  {out : Array Ix.Kernel.Reader.CDecl},
  Ix.Kernel.Reader.readRecords cx st records = Except.ok (st', out) →
    (List.map Prod.fst records.toList).Nodup -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Reader.readRecords_nodup

/-- info: @Ix.Kernel.Admission.Installed.singleton : ∀ {pins : Ix.Kernel.Reader.Pins}
  {pre : Ix.Kernel.Reader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.Installed pins pre natPins constants blobs hint env →
    ∀ {owner : Address} {c : Ixon.Constant},
      (owner, c) ∈ constants →
        Ix.Kernel.Reader.isSingleton c.info = true →
          ∃ st decl ds,
            Ix.Kernel.Reader.SingletonRead
                (Ix.Kernel.Admission.streamContext pins pre constants blobs hint) st owner c decl ∧
              decl ∈ ds ∧
                Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified natPins ds = Except.ok env ∧
                  ∀ (s : Ix.Kernel.Cached.InstallSkel),
                    Ix.Kernel.Cached.declSkel decl = some s →
                      ∃ ci, ci ∈ env.consts ∧ Ix.Kernel.Cached.ciSkel ci = s -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.Installed.singleton

/-- info: @Ix.Kernel.Admission.checkBytes_resources : ∀ {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ constants,
      Ix.Kernel.Admission.RecordsRead limits records constants ∧
        Ix.Kernel.Admission.resourceUnits constants ≤
          2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_resources

/-- info: @Ix.Kernel.Reader.keyName_injective : ∀ {r s : Ix.Kernel.ConstRef Address},
  Ix.Kernel.Reader.keyName r = Ix.Kernel.Reader.keyName s → r = s -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Reader.keyName_injective

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
