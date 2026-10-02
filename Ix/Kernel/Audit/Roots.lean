import Ix.Kernel
import Ix.Ixon.Types
import Ix.Kernel.Admission.Theorems
import Ix.Kernel.Audit.Axioms
import Ix.Kernel.Audit.Imports
import Ix.Kernel.Audit.Runtime

/-! # The required roots and their frozen boundaries

This module is the certified gate's manifest. Its public roots are the
verified checker `Ix.Kernel.Cached.checkDecls` behind the Ixon reader: the
certified entry `Ix.Ixon.Admission.checkBytes` (and its pin-parametric form
`checkBytesWith`, and `checkConstants`/`checkConstantsWith` over decoded
records), and the public theorems of `Ix.Ixon.Admission.Theorems` (model
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
`publicOperations`) reaches 5309 with 123 inherited externs, adding the
byte stage (`preflight`, `uniqueKeys`, `decodeRecords`) and the committed
tables. The committed Nat-operation pins (`builtinNatOpPins`) are decoded
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
  #[``Ix.Ixon.Admission.checkBytes_has_model, ``Ix.Ixon.Admission.checkBytesWith_has_model,
    ``Ix.Ixon.Admission.checkConstants_has_model,
    ``Ix.Ixon.Admission.checkConstantsWith_has_model,
    ``Ix.Ixon.Admission.checkBytes_has_model_values,
    ``Ix.Ixon.Admission.checkBytesWith_has_model_values,
    ``Ix.Ixon.Admission.checkBytes_no_proof_of_False,
    ``Ix.Ixon.Admission.checkBytesWith_no_proof_of_False,
    ``Ix.Ixon.Admission.checkBytes_no_False_theorem,
    ``Ix.Ixon.Admission.checkBytesWith_no_False_theorem,
    ``Ix.Ixon.Admission.checkBytesWith_no_False_reference,
    ``Ix.Ixon.Admission.checkBytes_resources, ``Ix.Ixon.Admission.checkBytesWith_resources,
    ``Ix.Kernel.model_exists, ``Ix.Kernel.no_False_theorem_accepted]

/-- Fidelity and the facts it is built from: the reading of accepted bytes, the record-by-record reading of the
reader, per-record installation, and the address encoding's injectivity. -/
def fidelityRoots : Array Lean.Name :=
  #[``Ix.Ixon.Admission.checkBytes_reading, ``Ix.Ixon.Admission.checkBytesWith_reading,
    ``Ix.Ixon.Admission.checkConstantsWith_installed, ``Ix.Ixon.Admission.Installed.skels,
    ``Ix.Ixon.Admission.Installed.singleton, ``Ix.Ixon.Admission.checkBytesWith_eq,
    ``Ix.Ixon.Admission.checkBytes_with, ``Ix.Ixon.Admission.checkConstants_with,
    ``Ix.Kernel.IxonReader.readRecords_spec, ``Ix.Kernel.IxonReader.readRecords_nodup,
    ``Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff, ``Ix.Kernel.IxonReader.readRecord_singleton,
    ``Ix.Kernel.IxonReader.StreamRead.singleton, ``Ix.Kernel.IxonReader.keyName_injective,
    ``Ix.Kernel.IxonFold.checkDecls_installs, ``Ix.Kernel.IxonFold.checkDecls_model_defn_values]

/-- The executable entry whose runtime closure is audited: the certified entry
`Ix.Ixon.Admission.checkBytes`, which runs the verified fold behind the Ixon
reader, and that entry over explicit tables and over decoded records. -/
def publicOperations : Array Lean.Name :=
  #[``Ix.Ixon.Admission.checkBytes, ``Ix.Ixon.Admission.checkBytesWith,
    ``Ix.Ixon.Admission.checkConstantsWith, ``Ix.Ixon.Admission.checkConstants]

/-- The verified fold, the kernel of the entry. -/
def kernelOperations : Array Lean.Name := #[``Ix.Kernel.Cached.checkDecls]

/-- The Ixon reader of the entry. -/
def readerOperations : Array Lean.Name :=
  #[``Ix.Kernel.IxonReader.readRecords, ``Ix.Ixon.Admission.readStream]

/-- The certified entry's module, whose import closure is audited. -/
def publicModules : Array Lean.Name := #[`Ix.Kernel.Admission]

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
  #[`Init, `Std, `Ix.Kernel, `Ix.Address.Core, `Ix.Ixon.Types]

/-- The modules under `Ix.Kernel` that the kernel-side modules may not use:
the certified entry, which runs the kernel and the byte stage beside it, and
the audits. -/
def kernelImportDenylist : Array Lean.Name := #[`Ix.Kernel.Admission, `Ix.Kernel.Audit]

/-- Module prefixes the certified import closure may use: the kernel-side
list (`kernelImportAllowlist`), plus exactly the modules of the entry's byte
stage, as the import closure of `Ix.Ixon.Admission` has them.
Each is pure Lean core and is audited on its own terms elsewhere:
* `Ix.Ixon.Codec`, `Ix.Ixon.Wire`, `Ix.Ixon.WireCheck`,
  `Ix.Ixon.Bounded.Constant`, `Ix.Ixon.Bounded.Universe`, `Ix.Ixon.Canonical`:
  the canonical per-record decoder and its readers (`Ix.Ixon.Audit`, whose
  `dataImports` is `Init` and these);
* `Ix.Ixon.Admission`: the certified entry, and `Ix.Ixon.Admission.Bytes`,
  the batch limits (`preflight`) and the decoding loop (`decodeRecords`)
  (`Ix.Ixon.Admission.Audit`).
Nothing else under `Ix.Ixon` (in particular no projection hashing,
`Ix.Address.Pure`, block order or proof module: `importDenylist` carves the
entry's theorem and audit modules out of `Ix.Ixon.Admission`) and still no
`Lean` outside the ruled elaboration-time edges. -/
def importAllowlist : Array Lean.Name :=
  kernelImportAllowlist ++ #[`Ix.Ixon.Codec, `Ix.Ixon.Wire, `Ix.Ixon.WireCheck,
    `Ix.Ixon.Bounded.Constant, `Ix.Ixon.Bounded.Universe, `Ix.Ixon.Canonical, `Ix.Kernel.Admission]

/-- The modules under `importAllowlist`'s prefixes that the certified import
closure may not use: the entry's theorems and audit. -/
def importDenylist : Array Lean.Name :=
  #[`Ix.Kernel.Admission.Theorems, `Ix.Kernel.Admission.Bytes.Theorems, `Ix.Kernel.Admission.Audit,
    `Ix.Kernel.Audit]

/-- The proofs of the public theorems may additionally use the Ixon codec's
proof modules (`Ix.Ixon.Verify`, `Ix.Ixon.Bounded.Size`, with their Lean
proof tooling) and the theorem module itself. -/
def proofImportAllowlist : Array Lean.Name :=
  importAllowlist ++ #[`Ix.Ixon.Bounded.Size, `Ix.Ixon.Verify, `Ix.Kernel.Admission.Theorems, `Lean]

/-- The kernel's elaboration-time imports:
`Ix/Kernel/BasisGen.lean` (`public meta import Lean`) splices the
annotated basis and pins. Below these edges only Lean core, `Lean`, and
`Ix.Kernel` may appear. Upstream's pin generators and JSON pin dumps
(`PinGen*.lean`, `NatOpPins.lean`) are not carried here: the Nat-operation pins
come from Ixon (`Ix/Kernel/Ixon/NatOpPinData.lean`). -/
def elaborationImports : ElaborationImports where
  importers := #[`Ix.Kernel.BasisGen]
  allowed := #[`Init, `Std, `Lean, `Ix.Kernel]

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
  `Ix/Kernel/Frontend/InModel*`. -/
def runtimeRulings : RuntimeRulings where
  computedFieldTypes := #[`Ix.Kernel.Level, `Ix.Kernel.Expr, `Ix.Kernel.Name]
  csimpModules := #[`Ix.Kernel]
  primitives := #[``withPtrEq, ``withPtrEqUnsafe, ``withPtrEqDecEq, ``withPtrAddr,
    ``withPtrAddrUnsafe, ``ptrEq, ``ptrAddrUnsafe, ``isExclusiveUnsafe]
  implementations := #[(`Ix.Kernel.withExclusive, `Ix.Kernel.withExclusiveUnsafe)]
  elaborationModules := #[`Ix.Kernel.BasisGen]
  partialModules := #[`Ix.Kernel.Frontend.InModel]

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

#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkConstants_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkConstantsWith_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith_no_False_reference [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.model_exists [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.no_False_theorem_accepted [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkConstantsWith_installed [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.Installed.skels [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.Installed.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_with [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkConstants_with [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.IxonReader.readRecords_spec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.IxonReader.readRecords_nodup [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.IxonReader.readRecord_singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.IxonReader.StreamRead.singleton [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.IxonReader.keyName_injective [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.IxonFold.checkDecls_installs [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.IxonFold.checkDecls_model_defn_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesWith [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkConstantsWith [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkConstants [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.checkDecls [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.IxonReader.readRecords [propext, Classical.choice, Quot.sound]

/-! ### Import and runtime closures

The entry's import closure stays inside `importAllowlist`, below the ruled
elaboration-time edges inside `elaborationImports.allowed`; the theorems'
closure inside `proofImportAllowlist`. The runtime closures are frozen with
the rulings they use: the fold reaches the kernel's computed-field
overrides of `Level`, `Expr` and `Name` (18) and 20 project csimps; the
reader adds the in-model generator's 10 `partial` definitions; the entry
adds the byte stage and the committed tables. The pin-parametric forms
(`checkBytesWith`, `checkConstantsWith`) reach 4539 functions; the
committed pin table, prelude and Nat-operation pin decoder add the rest. -/

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith Ix.Kernel.Audit.publicModules Ix.Kernel.Audit.importAllowlist Ix.Kernel.Audit.elaborationImports Ix.Kernel.Audit.importDenylist

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Kernel.Admission.Theorems] Ix.Kernel.Audit.proofImportAllowlist Ix.Kernel.Audit.elaborationImports

-- The entry's byte stage is admitted; projection hashing, block order, the
-- codec proofs and `kernelImportAllowlist` are not widened.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Canonical Ix.Kernel.Audit.importDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Kernel.Admission Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Projection Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.BlockOrder Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Verify Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Kernel.Admission.Theorems Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Kernel.Admission.Bytes.Theorems Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Kernel.Admission.Audit Ix.Kernel.Audit.importDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Kernel.Admission.Bytes Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Address.Pure Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Data.Json Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Ixon.Canonical Ix.Kernel.Audit.kernelImportDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Kernel.Admission Ix.Kernel.Audit.kernelImportDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Kernel.Admission.Bytes Ix.Kernel.Audit.kernelImportDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Kernel.Audit.Roots Ix.Kernel.Audit.kernelImportDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Kernel.Ixon.Reader Ix.Kernel.Audit.kernelImportDenylist

/-- info: runtime closure of [Ix.Kernel.Cached.checkDecls]: 3022 compiled functions; inherited externs 83,
implemented_by 0, unsafe 22, csimp 4; ruled computed_field 18, csimp 20 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

/-- info: runtime closure of [Ix.Kernel.IxonReader.readRecords,
 Ix.Ixon.Admission.readStream]: 1886 compiled functions; inherited externs 82, implemented_by 0,
unsafe 23, csimp 0; ruled computed_field 18, csimp 7, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.readerOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

-- 5309: one less than the 5310 frozen before the alias `Ix.Ixon.Admission.checkBytes`
-- (which only called the kernel entry `Ix.Ixon.KernelAdmission.checkBytes`) was
-- deleted and the entry took its name: the alias's own compiled function left the
-- closure, and nothing else did (compared name by name).
/-- info: runtime closure of [Ix.Ixon.Admission.checkBytes,
 Ix.Ixon.Admission.checkBytesWith,
 Ix.Ixon.Admission.checkConstantsWith,
 Ix.Ixon.Admission.checkConstants]: 5309 compiled functions; inherited externs 123, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Audit.publicOperations Ix.Kernel.Audit.runtimeAllowlist Ix.Kernel.Audit.runtimeRulings

-- Without the rulings the entry's closure fails: they are what admits it.
/-- error: project-level execution replacements reached from [Ix.Kernel.Cached.checkDecls] -/
#guard_msgs (substring := true) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Kernel.Audit.kernelOperations Ix.Kernel.Audit.runtimeAllowlist

/-! ### Frozen statements -/

/-- info: Ix.Ixon.Admission.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_has_model

/-- info: Ix.Ixon.Admission.checkBytesWith_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {pins : Ix.Kernel.IxonReader.Pins} {pre : Ix.Kernel.IxonReader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytesWith_has_model

/-- info: Ix.Ixon.Admission.checkBytes_has_model_values : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ M,
      ∀ (cv : Ix.Kernel.ConstantVal) (value : Ix.Kernel.Expr) (hint' : Ix.Kernel.ReducibilityHint),
        Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
          ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
            Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_has_model_values

/-- info: Ix.Ixon.Admission.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_no_proof_of_False

/-- info: Ix.Ixon.Admission.checkBytesWith_no_False_theorem : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {pins : Ix.Kernel.IxonReader.Pins} {pre : Ix.Kernel.IxonReader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    ∀ {constants : List (Address × Ixon.Constant)},
      Ix.Ixon.Verify.Admission.RecordsRead limits records constants →
        ∀ {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition},
          (owner, c) ∈ constants →
            c.info = Ixon.ConstantInfo.defn d →
              d.kind = Ix.DefKind.thm →
                (Ix.Kernel.IxonReader.definitionReader
                          (Ix.Ixon.Admission.streamContext pins pre constants blobs hint) owner c d).read
                      d.typ =
                    Except.ok (Ix.Kernel.Expr.const Ix.Kernel.falseName []) →
                  False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytesWith_no_False_theorem

/-- info: @Ix.Ixon.Admission.checkBytes_reading : ∀ {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ pins pre natPins,
      Ix.Kernel.IxonReader.defaultPins = Except.ok pins ∧
        Ix.Kernel.IxonReader.builtinPrelude = Except.ok pre ∧
          Ix.Kernel.IxonReader.builtinNatOpPins = Except.ok natPins ∧
            Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
              Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
                ∃ constants,
                  Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
                    Ix.Ixon.Admission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_reading

/-- info: @Ix.Ixon.Admission.checkBytesWith_reading : ∀ {pins : Ix.Kernel.IxonReader.Pins}
  {pre : Ix.Kernel.IxonReader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet} {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytesWith pins pre natPins limits records blobs hint = Except.ok env →
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
        ∃ constants,
          Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
            Ix.Ixon.Admission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytesWith_reading

/-- info: Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff : ∀ (records : Ix.Ixon.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Ixon.Admission.uniqueKeys records blobs = Except.ok () ↔ Ix.Ixon.Verify.Admission.UniqueKeys records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff

/-- info: @Ix.Kernel.IxonReader.readRecords_nodup : ∀ {cx : Ix.Kernel.IxonReader.Ctx}
  {st st' : Ix.Kernel.IxonReader.State} {records : Array (Address × Ixon.Constant)}
  {out : Array Ix.Kernel.IxonReader.CDecl},
  Ix.Kernel.IxonReader.readRecords cx st records = Except.ok (st', out) →
    (List.map Prod.fst records.toList).Nodup -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.IxonReader.readRecords_nodup

/-- info: @Ix.Ixon.Admission.Installed.singleton : ∀ {pins : Ix.Kernel.IxonReader.Pins}
  {pre : Ix.Kernel.IxonReader.Prelude} {natPins : List Ix.Kernel.NatOpPinSet}
  {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.Installed pins pre natPins constants blobs hint env →
    ∀ {owner : Address} {c : Ixon.Constant},
      (owner, c) ∈ constants →
        Ix.Kernel.IxonReader.isSingleton c.info = true →
          ∃ st decl ds,
            Ix.Kernel.IxonReader.SingletonRead
                (Ix.Ixon.Admission.streamContext pins pre constants blobs hint) st owner c decl ∧
              decl ∈ ds ∧
                Ix.Kernel.Cached.checkDecls Ix.Kernel.CheckMode.verified natPins ds = Except.ok env ∧
                  ∀ (s : Ix.Kernel.Cached.InstallSkel),
                    Ix.Kernel.IxonFold.declSkel decl = some s →
                      ∃ ci, ci ∈ env.consts ∧ Ix.Kernel.Cached.ciSkel ci = s -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.Installed.singleton

/-- info: @Ix.Ixon.Admission.checkBytes_resources : ∀ {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ constants,
      Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
        Ix.Ixon.Verify.Admission.resourceUnits constants ≤
          2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_resources

/-- info: @Ix.Kernel.IxonReader.keyName_injective : ∀ {r s : Ix.Kernel.ConstRef Address},
  Ix.Kernel.IxonReader.keyName r = Ix.Kernel.IxonReader.keyName s → r = s -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.IxonReader.keyName_injective

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
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Kernel] Ix.Kernel.Audit.importAllowlist Ix.Kernel.Audit.elaborationImports Ix.Kernel.Audit.importDenylist

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Kernel.Ixon.Reader, `Ix.Kernel.Ixon.ReaderSpec,
  `Ix.Kernel.Ingress.Records, `Ix.Kernel.Egress.Projection, `Ix.Kernel.Search, `Ix.Kernel.Ref,
  `Ix.Ixon.Types] Ix.Kernel.Audit.kernelImportAllowlist Ix.Kernel.Audit.elaborationImports Ix.Kernel.Audit.kernelImportDenylist

-- `Std` is admitted; the compiler frontend and third-party libraries are not.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Std.Data.TreeMap Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Command Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Batteries.Data.RBMap Ix.Kernel.Audit.importDenylist
-- `Ix.Kernel` is admitted; `Lean` only below the ruled elaboration-time imports.
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Kernel.Core Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Lean.Elab.Term Ix.Kernel.Audit.importDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed `Lean.Elab.Term
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.importers `Ix.Kernel.Core
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed `Ix.Tc
