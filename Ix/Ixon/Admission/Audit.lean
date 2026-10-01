/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Verify.Admission
import Ix.Ixon.Verify.WorkAdmission
import Ix.Ixon.Consistency
import Ix.Ixon.Audit
import Ix.Kernel.Audit.Roots

/-! The byte adapter has its own import and runtime boundary. Neither the
intrinsic kernel's in-memory boundary nor the pure codec's allowlist is
widened.

From L5 (plan v4) the certified entry `Ix.Ixon.Admission.checkBytes` runs
con-leche's verified checker behind the Ixon reader; its closure is frozen
with the ruled constructs it reaches (`Ix.Kernel.Audit.runtimeRulings`), and
the externs it adds beyond the codec, the reader and the fold are listed.
The intrinsic kernel's byte admission, `checkBytesIntrinsic`, keeps its L4
boundary as the reference kernel's until L6. -/

namespace Ix.Ixon.Admission.Audit

/-- The certified entry's byte admission (L5). -/
def operations : Array Lean.Name :=
  #[``Ix.Ixon.Admission.preflight, ``Ix.Ixon.Admission.decodeRecords,
    ``Ix.Ixon.Admission.checkBytes]

/-- The intrinsic reference kernel's byte admission (until L6). -/
def intrinsicOperations : Array Lean.Name :=
  #[``Ix.Ixon.Admission.preflight, ``Ix.Ixon.Admission.decodeRecords,
    ``Ix.Ixon.Admission.checkBytesIntrinsic]

/-- Admission runs con-leche's checker behind the Ixon reader (L5: `ConLeche`,
`Ix.Ixon.ConLecheAdmission`, and the reader under `Ix.Kernel`; `Lean` only
below con-leche's ruled elaboration-time imports) and the intrinsic reference
kernel, whose closure admits `Std` (`Ix.Kernel.Audit.importAllowlist`,
2026-09-30). -/
def dataImports : Array Lean.Name :=
  Ix.Ixon.Audit.dataImports ++ #[`Ix.Kernel, `Std, `Ix.Ixon.Admission, `ConLeche,
    `Ix.Ixon.ConLecheAdmission]

def proofImports : Array Lean.Name := dataImports ++ #[`Lean, `Std, `Ix.Ixon.Verify,
  `Ix.Ixon.ConLecheConsistency, `Ix.Ixon.Consistency]

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

/- Measured independently before freezing (L5; re-measured at int-4). The
certified entry reaches the codec, the Ixon reader, the committed tables and
con-leche's fold. Its ruled constructs are the fold's computed-field
overrides and proved csimps and the in-model generator's `partial`
definitions. L5 alone froze 33407 functions and 115 externs: the committed
Nat-operation pins were then upstream's JSON dumps spliced as one closed
term (`ConLeche.natOpPinSets`, 27,096 compiled functions, 26,957 of them
extracted closed subterms). Rebased onto L4b they are decoded from a string
table at first use (`Ix.Kernel.ConLecheReader.builtinNatOpPins`, 235
functions), which adds eight string-scanning externs (below). -/
/-- info: runtime closure of [Ix.Ixon.Admission.preflight,
 Ix.Ixon.Admission.decodeRecords,
 Ix.Ixon.Admission.checkBytes]: 5288 compiled functions; inherited externs 123, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Ixon.Admission.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

/- The intrinsic reference entry, unchanged from L4. It reaches the existing
kernel and codec primitives only; the set-difference check below enforces
that adding the adapter introduces no further extern or unsafe primitive. -/
/-- info: runtime closure of [Ix.Ixon.Admission.preflight,
Ix.Ixon.Admission.decodeRecords, Ix.Ixon.Admission.checkBytesIntrinsic]: 1834 compiled functions;
inherited externs 71, implemented_by 0, unsafe 3, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Ixon.Admission.Audit.intrinsicOperations #[`Init, `Std]

run_cmd do
  let env ← Lean.getEnv
  let externs (roots : Array Lean.Name) := (Ix.Kernel.Audit.runtimeClosure env roots).externs
  let components := externs Ix.Ixon.Audit.operations ++ externs Ix.Kernel.Audit.ingressOperations
  let added := (externs Ix.Ixon.Admission.Audit.intrinsicOperations).filter (!components.contains ·)
  unless added.isEmpty do
    throwError "byte admission adds externs beyond the codec and ingress closures: {added}"

#guard_kernel_axioms Ix.Ixon.Verify.Admission.consume_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.preflight_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.encode [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.univNodes_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.resourceUnits_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.RecordsRead.deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.decodeRecords_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytesIntrinsic_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytesIntrinsic_of_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytesIntrinsic_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytesIntrinsic_unique_keys [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytesIntrinsic_resources [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Admission.checkBytesIntrinsic_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.canonicalRecord_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.decodeLoop_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.decodeLoop_work_le [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.parserStage_erases [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Verify.Work.Admission.parserStage_work_le [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Admission.checkBytesIntrinsic [propext, Classical.choice, Quot.sound]
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

/-- info: Ix.Ixon.Verify.Admission.decodeRecords_ok_iff : ∀ (limits : Ix.Ixon.Admission.Limits)
  (records : Ix.Ixon.Admission.Records) (constants : Ix.Kernel.Ingress.Constants),
  Ix.Ixon.Admission.decodeRecords limits records = Except.ok constants ↔
    Ix.Ixon.Verify.Admission.RecordsRead limits records constants -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.decodeRecords_ok_iff

/-! ### The certified entry's public theorems (L5) -/

/-- info: Ix.Ixon.Admission.checkBytes_eq : ∀ (limits : Ix.Ixon.Admission.Limits) (records : Ix.Ixon.Admission.Records)
  (blobs : Ix.Kernel.Ingress.Blobs) (hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint),
  Ix.Ixon.Admission.checkBytes limits records blobs hint =
    Ix.Ixon.ConLecheAdmission.checkBytes limits records blobs hint -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_eq

/-- info: Ix.Ixon.Admission.checkBytes_has_model : ∀ (V : Type u_1) [inst : ConLeche.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env → Nonempty (ConLeche.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_has_model

/-- info: Ix.Ixon.Admission.checkBytes_has_model_values : ∀ (V : Type u_1) [inst : ConLeche.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ M,
      ∀ (cv : ConLeche.ConstantVal) (value : ConLeche.Expr) (hint' : ConLeche.ReducibilityHint),
        ConLeche.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
          ∀ (φ : ConLeche.LevelParam → Nat) (ρ : ConLeche.BVarIdx → V),
            ConLeche.Denotes M.cval env φ ρ value (M.cval cv.name φ) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_has_model_values

/-- info: Ix.Ixon.Admission.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [ConLeche.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∀ (ci : ConLeche.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = ConLeche.Expr.const ConLeche.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_no_proof_of_False

/-- info: Ix.Ixon.Admission.checkBytes_no_False_theorem : ∀ (V : Type u_1) [ConLeche.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∀ {pins : Ix.Kernel.ConLecheReader.Pins} {pre : Ix.Kernel.ConLecheReader.Prelude},
      Ix.Kernel.ConLecheReader.defaultPins = Except.ok pins →
        Ix.Kernel.ConLecheReader.builtinPrelude = Except.ok pre →
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
#check @Ix.Ixon.Admission.checkBytes_no_False_theorem

/-- info: @Ix.Ixon.Admission.checkBytes_reading : ∀ {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint}
  {env : ConLeche.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ pins pre natPins,
      Ix.Kernel.ConLecheReader.defaultPins = Except.ok pins ∧
        Ix.Kernel.ConLecheReader.builtinPrelude = Except.ok pre ∧
          Ix.Kernel.ConLecheReader.builtinNatOpPins = Except.ok natPins ∧
            Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
              ∃ constants,
                Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
                  Ix.Ixon.ConLecheAdmission.Installed pins pre natPins constants blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_reading

/-- info: @Ix.Ixon.Admission.checkBytes_resources : ∀ {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint}
  {env : ConLeche.Env},
  Ix.Ixon.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ constants,
      Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
        Ix.Ixon.Verify.Admission.resourceUnits constants ≤
          2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Admission.checkBytes_resources

/-! ### The intrinsic reference entry (until L6) -/

/-- info: Ix.Ixon.Verify.Admission.checkBytesIntrinsic_ok_iff : ∀ (limits : Ix.Ixon.Admission.Limits) (cfg : Ix.Kernel.Config)
  (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs) (family : Option (Ix.Kernel.ConstRef Address))
  (env : Ix.Kernel.Env Address),
  Ix.Ixon.Admission.checkBytesIntrinsic limits cfg records blobs family = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ constants,
        Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
          Ix.Kernel.checkEnv cfg constants blobs family = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytesIntrinsic_ok_iff

/-- info: @Ix.Ixon.Verify.Admission.checkBytesIntrinsic_of_reading : ∀ {limits : Ix.Ixon.Admission.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {constants : Ix.Kernel.Ingress.Constants}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.RecordsRead limits records constants →
      Ix.Ixon.Admission.checkBytesIntrinsic limits cfg records blobs family =
        Except.mapError Ix.Ixon.Admission.Error.kernel (Ix.Kernel.checkEnv cfg constants blobs family) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytesIntrinsic_of_reading

/-- info: @Ix.Ixon.Verify.Admission.checkBytesIntrinsic_reading : ∀ {limits : Ix.Ixon.Admission.Limits} {cfg : Ix.Kernel.Config}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)}
  {env : Ix.Kernel.Env Address},
  Ix.Ixon.Admission.checkBytesIntrinsic limits cfg records blobs family = Except.ok env →
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ constants,
        Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
          Ix.Kernel.Ingress.Installed constants blobs family none env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytesIntrinsic_reading

/-- info: Ix.Ixon.Verify.Admission.checkBytesIntrinsic_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.Model.SetTheory V]
  {limits : Ix.Ixon.Admission.Limits} {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)} {env : Ix.Kernel.Env Address},
  Ix.Ixon.Admission.checkBytesIntrinsic limits cfg records blobs family = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytesIntrinsic_has_model

/-- info: @Ix.Ixon.Verify.Admission.checkBytesIntrinsic_resources : ∀ {limits : Ix.Ixon.Admission.Limits} {cfg : Ix.Kernel.Config}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)}
  {env : Ix.Kernel.Env Address},
  Ix.Ixon.Admission.checkBytesIntrinsic limits cfg records blobs family = Except.ok env →
    ∃ constants,
      Ix.Ixon.Verify.Admission.RecordsRead limits records constants ∧
        Ix.Kernel.Ingress.Installed constants blobs family none env ∧
          Ix.Ixon.Verify.Admission.resourceUnits constants ≤
            2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Verify.Admission.checkBytesIntrinsic_resources

/-- info: Additional byte-admission externs: []
---
info: Additional byte-admission unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env
    (Ix.Kernel.Audit.ingressOperations ++ Ix.Ixon.Audit.operations)
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Admission.Audit.intrinsicOperations
  Lean.logInfo m!"Additional byte-admission externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional byte-admission unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"

/- The certified entry adds ten Init externs beyond the codec, the reader and
the fold: `ByteArray.mk` and `Array.pop`, used to load the committed pin
table and prelude (`Ix.Kernel.ConLecheReader.defaultPins`, `builtinPrelude`),
and the eight string-scanning primitives of the Nat-operation pin decoder
(`builtinNatOpPins`, L4b; int-4). No further unsafe primitive. -/
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
