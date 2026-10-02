import Ix.Kernel.Admission.Bytes.Theorems
import Ix.Ixon.Verify.WorkAdmission
import Ix.Kernel.Admission.Theorems
import Ix.Ixon.Audit
import Ix.Kernel.Audit.Roots

/-! The byte adapter has its own import and runtime boundary. The pure
codec's allowlist is not widened.

The certified entry `Ix.Kernel.Admission.checkBytes` runs the verified checker
`Ix.Kernel.Cached.checkDecls` behind the Ixon reader; its closure is frozen with the ruled
constructs it reaches (`Ix.Kernel.Audit.runtimeRulings`), and the externs it
adds beyond the codec, the reader and the fold are listed. -/

namespace Ix.Kernel.Admission.Audit

/-- The certified entry's byte admission. -/
def operations : Array Lean.Name :=
  #[``Ix.Kernel.Admission.preflight, ``Ix.Kernel.Admission.uniqueKeys, ``Ix.Kernel.Admission.decodeRecords,
    ``Ix.Kernel.Admission.checkBytes]

/-- Admission runs the kernel's checker behind the Ixon reader
(`Ix.Kernel.Admission`, with the kernel `Ix.Kernel`: the checker with the
reader beside it; `Lean` only below the kernel's ruled
elaboration-time imports), whose closure admits `Std`
(`Ix.Kernel.Audit.importAllowlist`). -/
def dataImports : Array Lean.Name :=
  Ixon.Audit.dataImports ++ #[`Ix.Kernel, `Std, `Ix.Kernel.Admission]

def proofImports : Array Lean.Name := dataImports ++ #[`Lean, `Std, `Ix.Ixon.Verify,
  `Ix.Kernel.Admission.Theorems]

end Ix.Kernel.Admission.Audit

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImportsWith #[`Ix.Kernel.Admission] Ix.Kernel.Admission.Audit.dataImports Ix.Kernel.Audit.elaborationImports Ix.Kernel.Audit.importDenylist

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Kernel.Admission.Bytes.Theorems] Ix.Kernel.Admission.Audit.proofImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Ixon.Verify.WorkAdmission] Ix.Kernel.Admission.Audit.proofImports

#guard_msgs (drop info) in
run_cmd Ix.Kernel.Audit.checkImports #[`Ix.Kernel.Admission.Theorems] Ix.Kernel.Admission.Audit.proofImports

#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Ix.Kernel.Admission.Bytes.Theorems Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Lean Ix.Kernel.Audit.importDenylist
#guard Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Std.Data.TreeMap Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Batteries Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.kernelImportAllowlist `Ix.Kernel.Admission Ix.Kernel.Audit.kernelImportDenylist
#guard !Ix.Kernel.Audit.allowed Ixon.Audit.dataImports `Ix.Kernel.Admission

/- Measured independently before freezing. The certified entry reaches the
codec, the byte stage (`preflight`, `uniqueKeys`, `decodeRecords`), the
Ixon reader, the committed tables and the verified fold. Its ruled
constructs are the fold's computed-field overrides and proved csimps and
the in-model generator's `partial` definitions. The committed
Nat-operation pins are decoded from a string table at first use
(`Ix.Kernel.Reader.builtinNatOpPins`), which adds eight
string-scanning externs (below). 5307 is one less than the 5308 frozen before
the alias of the former API (`Ix.Ixon.Admission.checkBytes`, which only
called the kernel entry `Ix.Ixon.KernelAdmission.checkBytes`) was deleted and
the entry took its name (now `Ix.Kernel.Admission.checkBytes`): the alias's
own compiled function left the closure, and nothing else did (compared name
by name). -/
/-- info: runtime closure of [Ix.Kernel.Admission.preflight,
 Ix.Kernel.Admission.uniqueKeys,
 Ix.Kernel.Admission.decodeRecords,
 Ix.Kernel.Admission.checkBytes]: 5307 compiled functions; inherited externs 123, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Kernel.Admission.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ix.Kernel.Admission.consume_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.preflight_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Admission.uniqueKeys_ok_iff [propext, Classical.choice, Quot.sound]
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
#guard_kernel_axioms Ix.Kernel.Admission.checkBytes_resources [propext, Classical.choice, Quot.sound]

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

/-- info: Ix.Kernel.Admission.decodeRecords_ok_iff : ∀ (limits : Ix.Kernel.Admission.Limits)
  (records : Ix.Kernel.Admission.Records) (constants : Ix.Kernel.Ingress.Constants),
  Ix.Kernel.Admission.decodeRecords limits records = Except.ok constants ↔
    Ix.Kernel.Admission.RecordsRead limits records constants -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.decodeRecords_ok_iff

/-! ### The certified entry's public theorems -/

/-- info: Ix.Kernel.Admission.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V]
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes limits records blobs hint = Except.ok env → Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_has_model

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

/-- info: Ix.Kernel.Admission.checkBytes_no_False_theorem : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V]
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∀ {pins : Ix.Kernel.Reader.Pins} {pre : Ix.Kernel.Reader.Prelude},
      Ix.Kernel.Reader.defaultPins = Except.ok pins →
        Ix.Kernel.Reader.builtinPrelude = Except.ok pre →
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
#check @Ix.Kernel.Admission.checkBytes_no_False_theorem

/-- info: @Ix.Kernel.Admission.checkBytes_reading : ∀ {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
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

/-- info: @Ix.Kernel.Admission.checkBytes_resources : ∀ {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ix.Kernel.Admission.checkBytes limits records blobs hint = Except.ok env →
    ∃ constants,
      Ix.Kernel.Admission.RecordsRead limits records constants ∧
        Ix.Kernel.Admission.resourceUnits constants ≤
          2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes -/
#guard_msgs (whitespace := lax) in
#check @Ix.Kernel.Admission.checkBytes_resources

/- The certified entry adds ten Init externs beyond the codec, the reader and
the fold: `ByteArray.mk` and `Array.pop`, used to load the committed pin
table and prelude (`Ix.Kernel.Reader.defaultPins`, `builtinPrelude`),
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
    (Ixon.Audit.operations ++ Ix.Kernel.Audit.kernelOperations ++ Ix.Kernel.Audit.readerOperations)
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Kernel.Admission.Audit.operations
  Lean.logInfo m!"Additional certified-entry externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified-entry unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
