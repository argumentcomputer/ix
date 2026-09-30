/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify.Admission
import Ix.Ixon.Verify.WorkAdmission
import Ix.Ixon.Audit
import Ix.Kernel.Audit.Roots

/-! The byte adapter has its own import and runtime boundary. Neither the
kernel's in-memory boundary nor the pure codec's allowlist is widened. -/

namespace Ix.Ixon.Admission.Audit

def operations : Array Lean.Name :=
  #[``Ix.Ixon.Admission.preflight, ``Ix.Ixon.Admission.decodeRecords,
    ``Ix.Ixon.Admission.checkBytes]

/-- Admission runs the certified kernel, whose closure admits `Std`
(`Ix.Kernel.Audit.importAllowlist`, 2026-09-30). -/
def dataImports : Array Lean.Name :=
  Ix.Ixon.Audit.dataImports ++ #[`Ix.Kernel, `Std, `Ix.Ixon.Admission]

def proofImports : Array Lean.Name := dataImports ++ #[`Lean, `Std, `Ix.Ixon.Verify]

end Ix.Ixon.Admission.Audit

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Admission] Ix.Ixon.Admission.Audit.dataImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Verify.Admission] Ix.Ixon.Admission.Audit.proofImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Verify.WorkAdmission] Ix.Ixon.Admission.Audit.proofImports

#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Ix.Ixon.Verify.Admission
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Lean
#guard Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Std.Data.TreeMap
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Batteries
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.Admission
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Audit.dataImports `Ix.Ixon.Admission

/- Measured independently before freezing. The adapter reaches the existing
kernel and codec primitives only; the set-difference check below enforces
that adding the adapter introduces no further extern or unsafe primitive. -/
/-- info: runtime closure of [Ix.Ixon.Admission.preflight,
Ix.Ixon.Admission.decodeRecords, Ix.Ixon.Admission.checkBytes]: 1500 compiled functions;
inherited externs 69, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Ixon.Admission.Audit.operations #[`Init, `Std]

run_cmd do
  let env ← Lean.getEnv
  let externs (roots : Array Lean.Name) := (Ix.Kernel.Audit.runtimeClosure env roots).externs
  let components := externs Ix.Ixon.Audit.operations ++ externs Ix.Kernel.Audit.ingressOperations
  let added := (externs Ix.Ixon.Admission.Audit.operations).filter (!components.contains ·)
  unless added.isEmpty do
    throwError "byte admission adds externs beyond the codec and ingress closures: {added}"

#guard_kernel_axioms Ix.Ixon.Verify.Admission.consume_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.preflight_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.encode [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.univNodes_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.resourceUnits_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.decodeRecords_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytes_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytes_of_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytes_unique_keys [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytes_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.canonicalRecord_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.decodeLoop_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.decodeLoop_work_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.parserStage_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.parserStage_work_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytes [propext, Classical.choice, Quot.sound]

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

/-- info: Ix.Ixon.Verify.Admission.preflight_ok_iff : ∀ (limits : Ix.Ixon.Admission.Limits)
  (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Ixon.Admission.preflight limits records blobs = Except.ok () ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.preflight_ok_iff

/-- info: Ix.Ixon.Verify.Admission.decodeRecords_ok_iff : ∀ (limits : Ix.Ixon.Admission.Limits)
  (records : Ix.Ixon.Admission.Records) (constants : Ix.Kernel.Ingress.Constants),
  Ix.Ixon.Admission.decodeRecords limits records = Except.ok constants ↔
    Ix.Ixon.Verify.Admission.RecordsRead limits records constants -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.decodeRecords_ok_iff

/-- info: Ix.Ixon.Verify.Admission.checkBytes_ok_iff : ∀ (limits : Ix.Ixon.Admission.Limits)
  (cfg : Ix.Kernel.Config) (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (family : Option (Ix.Kernel.ConstRef Address)) (env : Ix.Kernel.Env Address),
  Ix.Ixon.Admission.checkBytes limits cfg records blobs family = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ constants,
        Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
          Ix.Kernel.checkEnv cfg constants blobs family = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytes_ok_iff

/-- info: @Ix.Ixon.Verify.Admission.checkBytes_of_reading : ∀ {limits : Ix.Ixon.Admission.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {constants : Ix.Kernel.Ingress.Constants}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.RecordsRead limits records constants →
      Ix.Ixon.Admission.checkBytes limits cfg records blobs family =
        Except.mapError Ix.Ixon.Admission.Error.kernel (Ix.Kernel.checkEnv cfg constants blobs family) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytes_of_reading

/-- info: @Ix.Ixon.Verify.Admission.checkBytes_reading : ∀ {limits : Ix.Ixon.Admission.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {env : Ix.Kernel.Env Address},
  Ix.Ixon.Admission.checkBytes limits cfg records blobs family = Except.ok env →
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ constants,
        Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
          Ix.Kernel.Ingress.Installed constants blobs family none env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytes_reading

/-- info: Ix.Ixon.Verify.Admission.checkBytes_has_model : ∀ (V : Type u_1)
  [inst : Ix.Kernel.Model.SetTheory V] {limits : Ix.Ixon.Admission.Limits} {cfg : Ix.Kernel.Config}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {env : Ix.Kernel.Env Address},
  Ix.Ixon.Admission.checkBytes limits cfg records blobs family = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytes_has_model

/-- info: @Ix.Ixon.Verify.Admission.checkBytes_resources : ∀ {limits : Ix.Ixon.Admission.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {env : Ix.Kernel.Env Address},
  Ix.Ixon.Admission.checkBytes limits cfg records blobs family = Except.ok env →
    ∃ constants,
      Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
        Ix.Kernel.Ingress.Installed constants blobs family none env ∧
          Ix.Ixon.Verify.Admission.resourceUnits constants ≤
            2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytes_resources

/-- info: Additional byte-admission externs: []
---
info: Additional byte-admission unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env
    (Ix.Kernel.Audit.ingressOperations ++ Ix.Ixon.Audit.operations)
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Admission.Audit.operations
  Lean.logInfo m!"Additional byte-admission externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional byte-admission unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
