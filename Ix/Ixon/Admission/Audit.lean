/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify.Admission
import Ix.Ixon.Verify.WorkAdmission
import Ix.Ixon.Consistency
import Ix.Ixon.Audit
import Ix.Kernel.Audit.Roots

/-! The byte adapter has its own import and runtime boundary. The pure
codec's allowlist is not widened.

The certified entry `Ix.Ixon.Admission.checkBytes` runs the verified checker
`Ix.Kernel.Cached.checkDecls` behind the Ixon reader; its closure is frozen with the ruled
constructs it reaches (`Ix.Kernel.Audit.runtimeRulings`), and the externs it
adds beyond the codec, the reader and the fold are listed. -/

namespace Ix.Ixon.Admission.Audit

/-- The certified entry's byte admission. -/
def operations : Array Lean.Name :=
  #[``Ix.Ixon.Admission.preflight, ``Ix.Ixon.Admission.uniqueKeys, ``Ix.Ixon.Admission.decodeRecords,
    ``Ix.Ixon.Admission.checkBytes]

/-- Admission runs the vendored checker behind the Ixon reader
(`Ix.Ixon.KernelAdmission`, and the kernel `Ix.Kernel`: the vendored checker
with the reader beside it; `Lean` only below the kernel's ruled
elaboration-time imports), whose closure admits `Std`
(`Ix.Kernel.Audit.importAllowlist`). -/
def dataImports : Array Lean.Name :=
  Ix.Ixon.Audit.dataImports ++ #[`Ix.Kernel, `Std, `Ix.Ixon.Admission,
    `Ix.Ixon.KernelAdmission]

def proofImports : Array Lean.Name := dataImports ++ #[`Lean, `Std, `Ix.Ixon.Verify,
  `Ix.Ixon.KernelConsistency, `Ix.Ixon.Consistency]

end Ix.Ixon.Admission.Audit

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Ixon.Admission] Ix.Ixon.Admission.Audit.dataImports Ix.Kernel.Audit.elaborationImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Verify.Admission] Ix.Ixon.Admission.Audit.proofImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Verify.WorkAdmission] Ix.Ixon.Admission.Audit.proofImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Consistency] Ix.Ixon.Admission.Audit.proofImports

#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Ix.Ixon.Verify.Admission
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Lean
#guard Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Std.Data.TreeMap
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Batteries
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Ixon.Admission
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Audit.dataImports `Ix.Ixon.Admission

/- Measured independently before freezing. The certified entry reaches the
codec, the byte stage (`preflight`, `uniqueKeys`, `decodeRecords`), the
Ixon reader, the committed tables and the verified fold. Its ruled
constructs are the fold's computed-field overrides and proved csimps and
the in-model generator's `partial` definitions. The committed
Nat-operation pins are decoded from a string table at first use
(`Ix.Kernel.IxonReader.builtinNatOpPins`), which adds eight
string-scanning externs (below). -/
/-- info: runtime closure of [Ix.Ixon.Admission.preflight,
 Ix.Ixon.Admission.uniqueKeys,
 Ix.Ixon.Admission.decodeRecords,
 Ix.Ixon.Admission.checkBytes]: 5308 compiled functions; inherited externs 123, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Ixon.Admission.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ix.Ixon.Verify.Admission.consume_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.preflight_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.encode [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.univNodes_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.resourceUnits_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.decodeRecords_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.canonicalRecord_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.decodeLoop_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.decodeLoop_work_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.parserStage_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.parserStage_work_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_eq [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_has_model_values [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_no_False_theorem [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes_resources [propext, Classical.choice, Quot.sound]

/-- info: Ix.Ixon.Verify.Work.Admission.parserStage_erases : ∀ (limits : Ix.Ixon.Admission.Limits)
  (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs),
  (Ix.Ixon.Verify.Work.Admission.parserStage limits records blobs).fst = do
    Ix.Ixon.Admission.preflight limits records blobs
    Ix.Ixon.Admission.decodeRecords limits records -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Work.Admission.parserStage_erases

/-- info: Ix.Ixon.Verify.Work.Admission.parserStage_work_le : ∀ (limits : Ix.Ixon.Admission.Limits)
  (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs),
  (Ix.Ixon.Verify.Work.Admission.parserStage limits records blobs).snd ≤
    16 * limits.maxTotalBytes + limits.maxRecords * (2 * limits.maxRecordUnivNodes + 3) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Work.Admission.parserStage_work_le

/-- info: Ix.Ixon.Verify.Admission.preflight_ok_iff : ∀ (limits : Ix.Ixon.Admission.Limits) (records : Ix.Ixon.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Ixon.Admission.preflight limits records blobs = Except.ok () ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.preflight_ok_iff

/-- info: Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff : ∀ (records : Ix.Ixon.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Ixon.Admission.uniqueKeys records blobs = Except.ok () ↔ Ix.Ixon.Verify.Admission.UniqueKeys records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff

/-- info: Ix.Ixon.Verify.Admission.decodeRecords_ok_iff : ∀ (limits : Ix.Ixon.Admission.Limits)
  (records : Ix.Ixon.Admission.Records) (constants : Ix.Kernel.Ingress.Constants),
  Ix.Ixon.Admission.decodeRecords limits records = Except.ok constants ↔
    Ix.Ixon.Verify.Admission.RecordsRead limits records constants -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.decodeRecords_ok_iff

/-! ### The certified entry's public theorems -/

/-- info: Ix.Ixon.Admission.checkBytes_eq : ∀ (limits : Ix.Ixon.Admission.Limits) (records : Ix.Ixon.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs) (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint),
  Ix.Ixon.Admission.checkBytes limits records blobs hint =
    Ix.Ixon.KernelAdmission.checkBytes limits records blobs hint -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_eq

/-- info: Ix.Ixon.Admission.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_has_model

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

/-- info: Ix.Ixon.Admission.checkBytes_no_False_theorem : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∀ {pins : Ix.Kernel.IxonReader.Pins} {pre : Ix.Kernel.IxonReader.Prelude},
      Ix.Kernel.IxonReader.defaultPins = Except.ok pins →
        Ix.Kernel.IxonReader.builtinPrelude = Except.ok pre →
          ∀ {constants : List (Address × Ixon.Constant)},
            Ix.Ixon.Verify.Admission.RecordsRead limits records constants →
              ∀ {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition},
                (owner, c) ∈ constants →
                  c.info = Ixon.ConstantInfo.defn d →
                    d.kind = Ix.DefKind.thm →
                      (Ix.Kernel.IxonReader.definitionReader
                                (Ix.Ixon.KernelAdmission.streamContext pins pre constants blobs hint) owner c d).read
                            d.typ =
                          Except.ok (Ix.Kernel.Expr.const Ix.Kernel.falseName []) →
                        False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_no_False_theorem

/-- info: @Ix.Ixon.Admission.checkBytes_reading : ∀ {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ pins pre natPins,
      Ix.Kernel.IxonReader.defaultPins = Except.ok pins ∧
        Ix.Kernel.IxonReader.builtinPrelude = Except.ok pre ∧
          Ix.Kernel.IxonReader.builtinNatOpPins = Except.ok natPins ∧
            Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
              Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
                ∃ constants,
                  Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
                    Ix.Ixon.KernelAdmission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_reading

/-- info: @Ix.Ixon.Admission.checkBytes_resources : ∀ {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ constants,
      Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
        Ix.Ixon.Verify.Admission.resourceUnits constants ≤
          2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_resources

/- The certified entry adds ten Init externs beyond the codec, the reader and
the fold: `ByteArray.mk` and `Array.pop`, used to load the committed pin
table and prelude (`Ix.Kernel.IxonReader.defaultPins`, `builtinPrelude`),
and the eight string-scanning primitives of the Nat-operation pin decoder
(`builtinNatOpPins`). No further unsafe primitive. -/
/-- info: Additional certified-entry externs: [Array.pop,
 String.decodeChar,
 String.Pos.next,
 UInt32.decLe,
 String.toUTF8,
 String.Pos.Raw.extract,
 String.Pos.Raw.next,
 String.Pos.Raw.get,
 String.Pos.Raw.atEnd,
 ByteArray.mk]
---
info: Additional certified-entry unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env
    (Ix.Ixon.Audit.operations ++ Ix.Kernel.Audit.kernelOperations ++ Ix.Kernel.Audit.readerOperations)
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Admission.Audit.operations
  Lean.logInfo m!"Additional certified-entry externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified-entry unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
