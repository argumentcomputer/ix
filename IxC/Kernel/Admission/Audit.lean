import IxC.Kernel.Admission.Bytes.Theorems
import IxC.Ixon.Verify.WorkAdmission
import IxC.Kernel.Admission.Theorems
import IxC.Ixon.Audit
import IxC.Kernel.Audit.Roots

/-! The byte adapter has its own import and runtime boundary. The pure
codec's allowlist is not widened.

The certified entry `Ix.Kernel.Admission.checkBytes` runs the verified checker
`Ix.Kernel.Cached.checkDecls` behind the Ixon reader; its closure is frozen with the ruled
constructs it reaches (`Ix.Kernel.Audit.runtimeRulings`), and the externs it
adds beyond the codec, the reader and the fold are listed. -/

namespace Ix.Kernel.Admission.Audit

/-- The certified entry's byte admission. -/
def operations : Array Lean.Name :=
  #[``Ix.Kernel.Admission.preflight, ``Ix.Kernel.Admission.uniqueKeys, ``Ix.Kernel.Admission.authenticate,
    ``Ix.Kernel.Admission.decodeRecords, ``Ix.Kernel.Admission.checkBytes]

/-- Admission runs the kernel's checker behind the Ixon reader
(`Ix.Kernel.Admission`, with the kernel `Ix.Kernel`: the checker with the
reader beside it; `Lean` only below the kernel's ruled
elaboration-time imports), whose closure admits `Std`
(`Ix.Kernel.Audit.importAllowlist`). -/
def dataImports : Array Lean.Name :=
  Ixon.Audit.dataImports ++ #[`IxC.Kernel, `Std, `IxC.Kernel.Admission]

def proofImports : Array Lean.Name := dataImports ++ #[`Lean, `Std, `IxC.Ixon.Verify,
  `IxC.Kernel.Admission.Theorems]

end Ix.Kernel.Admission.Audit

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`IxC.Kernel.Admission] Ix.Kernel.Admission.Audit.dataImports Ix.Kernel.Audit.elaborationImports Ix.Kernel.Audit.importDenylist

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`IxC.Kernel.Admission.Bytes.Theorems] Ix.Kernel.Admission.Audit.proofImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`IxC.Ixon.Verify.WorkAdmission] Ix.Kernel.Admission.Audit.proofImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`IxC.Kernel.Admission.Theorems] Ix.Kernel.Admission.Audit.proofImports

#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `IxC.Kernel.Admission.Bytes.Theorems Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Lean Ix.Kernel.Audit.importDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Std.Data.TreeMap Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Batteries Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `IxC.Kernel.Admission Ix.Kernel.Audit.kernelImportDenylist
#guard !Ix.Kernel.Audit.allowed Ixon.Audit.dataImports `IxC.Kernel.Admission

/- Measured independently before freezing. The certified entry reaches the
codec, with Ixon v4's TagN integer code (`Ixon.getTagN`, `getTagNWide`,
`getTagN0Values`, `putTagN`, `tagNHeader`, `tagNEnd1..6`), the byte stage
(`preflight`, `uniqueKeys`, `authenticate`, `decodeRecords`; the content hash
is a parameter, so no hasher), the binding section's admission
(`admitBinding`: `RoleTable.ofBytes`, `RoleTable.check`), the Ixon reader, the
committed default table and prelude and the verified fold. Its ruled
constructs are the fold's computed-field overrides and proved csimps and
the in-model generator's `partial` definitions. Step 4 retired the
Nat-operation pin decoder (`builtinNatOpPins`) and its eight string-scanning
externs, and the pin table's derived-shape check (`Reader.derivedShape`) with
`String.Slice.Pattern.Internal.memcmpStr`. Step 5a (typed keys) moved the count
from 5653 by the entry's change (`IxC/Kernel/Audit/Roots.lean`): `Key`'s three
computed-field overrides, its rendering for messages (`Key.toName`,
`Role.leanName`, `Derived.spell`) in, the closed terms that spelled role and
derived names out. Step 5b's `LetMeta` moved it from 5444 by the let contract's
equality, hash and `Repr` (`IxC/Kernel/Audit/Roots.lean`). -/
/-- info: runtime closure of [Ix.Kernel.Admission.preflight,
 Ix.Kernel.Admission.uniqueKeys,
 Ix.Kernel.Admission.authenticate,
 Ix.Kernel.Admission.decodeRecords,
 Ix.Kernel.Admission.checkBytes]: 5471 compiled functions; inherited externs 111, implemented_by 0, unsafe 26, csimp 4; ruled computed_field 21, csimp 21, partial 9 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Admission.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ix.Kernel.Admission.consume_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.preflight_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.uniqueKeys_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.authenticate_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.RecordsRead.hashed [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.RecordsRead.encode [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.RecordsRead.univNodes_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.RecordsRead.resourceUnits_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.RecordsRead.deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.decodeRecords_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Verify.Work.Admission.canonicalRecord_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Verify.Work.Admission.decodeLoop_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Verify.Work.Admission.decodeLoop_work_le [propext, Quot.sound]
#guard_kernel_axioms Ixon.Verify.Work.Admission.parserStage_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Verify.Work.Admission.parserStage_work_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_authentic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_binding [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.admitBinding_ok_iff [propext, Classical.choice, Quot.sound]

/-- info: Ixon.Verify.Work.Admission.parserStage_erases : ∀ (limits : Ix.Kernel.Admission.Limits)
  (records : Ix.Kernel.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs),
  (Ixon.Verify.Work.Admission.parserStage limits records blobs).fst = do
    Ix.Kernel.Admission.preflight limits records blobs
    Ix.Kernel.Admission.decodeRecords limits records -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Verify.Work.Admission.parserStage_erases

/-- info: Ixon.Verify.Work.Admission.parserStage_work_le : ∀ (limits : Ix.Kernel.Admission.Limits)
  (records : Ix.Kernel.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs),
  (Ixon.Verify.Work.Admission.parserStage limits records blobs).snd ≤
    16 * limits.maxTotalBytes + limits.maxRecords * (2 * limits.maxRecordUnivNodes + 3) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Verify.Work.Admission.parserStage_work_le

/-- info: Ix.Kernel.Admission.preflight_ok_iff : ∀ (limits : Ix.Kernel.Admission.Limits) (records : Ix.Kernel.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Kernel.Admission.preflight limits records blobs = Except.ok () ↔
    Ix.Kernel.Admission.WithinBatch limits records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.preflight_ok_iff

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

/-- info: Ix.Kernel.Admission.decodeRecords_ok_iff : ∀ (limits : Ix.Kernel.Admission.Limits)
  (records : Ix.Kernel.Admission.Records) (constants : Ix.Kernel.Ingress.Constants),
  Ix.Kernel.Admission.decodeRecords limits records = Except.ok constants ↔
    Ix.Kernel.Admission.RecordsRead limits records constants -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.decodeRecords_ok_iff

/-! ### The certified entry's public theorems -/

/-- info: Ix.Kernel.Admission.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
  {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_has_model

/-- info: Ix.Kernel.Admission.checkBytes_has_model_values : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∃ M,
      ∀ (cv : Ix.Kernel.ConstantVal) (value : Ix.Kernel.Expr) (hint' : Ix.Kernel.ReducibilityHint),
        Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
          ∀ (φ : Ix.Kernel.LevelParam → Nat) (ρ : Ix.Kernel.BVarIdx → V),
            Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_has_model_values

/-- info: Ix.Kernel.Admission.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
  {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const (Ix.Kernel.roleKey Ix.Kernel.Role.false) [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_no_proof_of_False

/-- info: Ix.Kernel.Admission.checkBytes_no_False_theorem : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
  {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∀ {t : Ix.Kernel.RoleTable} {pre : Ix.Kernel.Reader.Prelude},
      Ix.Kernel.Admission.admitBinding hash binding = Except.ok t →
        Ix.Kernel.Reader.preludeFor t = Except.ok pre →
          ∀ {constants : List (Address × Ixon.Constant)},
            Ix.Kernel.Admission.RecordsRead limits records constants →
              ∀ {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition},
                (owner, c) ∈ constants →
                  c.info = Ixon.ConstantInfo.defn d →
                    d.kind = Ix.DefKind.thm →
                      (Ix.Kernel.Reader.definitionReader (Ix.Kernel.Admission.streamContext t pre constants blobs hint)
                                owner c d).read
                            d.typ =
                          Except.ok (Ix.Kernel.Expr.const (Ix.Kernel.roleKey Ix.Kernel.Role.false) []) →
                        False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_no_False_theorem

/-- info: @Ix.Kernel.Admission.checkBytes_reading : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
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
                        Ix.Kernel.Admission.Installed t pre constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_reading

/-- info: @Ix.Kernel.Admission.checkBytes_authentic : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.Authentic hash records blobs ∧ hash binding.bytes = binding.address -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_authentic

/-- info: @Ix.Kernel.Admission.checkBytes_resources : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes hash binding limits records blobs hint = Except.ok env →
    ∃ constants,
      Ix.Kernel.Admission.RecordsRead limits records constants ∧
        Ix.Kernel.Admission.resourceUnits constants ≤
          2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_resources

/- The certified entry adds two Init externs beyond the codec, the reader
and the fold: `ByteArray.mk` and `Array.pop`, used to load the committed
default table and prelude (`Ix.Kernel.Reader.defaultTable`, `preludeFor`).
Step 4 removed nine: the eight string-scanning primitives of the retired
Nat-operation pin decoder (`builtinNatOpPins`) and
`String.Slice.Pattern.Internal.memcmpStr`, the retired pin table's
derived-shape check (`Reader.derivedShape`, through `String.startsWith`). No
further unsafe primitive. -/
/-- info: Additional certified-entry externs: [Array.pop, ByteArray.mk]
---
info: Additional certified-entry unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env
    (Ixon.Audit.operations ++ Ix.Kernel.Audit.kernelOperations ++ Ix.Kernel.Audit.readerOperations)
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Kernel.Admission.Audit.operations
  Lean.logInfo m!"Additional certified-entry externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified-entry unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
