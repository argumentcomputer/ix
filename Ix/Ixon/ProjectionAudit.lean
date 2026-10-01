/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.ProjectionProofs
import Ix.Ixon.Admission.Audit

/-! Projection hashing has an explicit boundary outside the dependency-free
kernel and codec. Only the shared Blake3 types and pure implementation are
allowed; permitting the entire Blake3 prefix would admit its FFI backends. -/

namespace Ix.Ixon.Projection.Audit

/-- The certified entry with projection reconstruction (L5). -/
def operations : Array Lean.Name :=
  #[``Projection.address, ``Projection.reconstruct, ``Projection.checkBytes]

/-- The intrinsic reference variant (until L6). -/
def intrinsicOperations : Array Lean.Name :=
  #[``Projection.address, ``Projection.reconstruct, ``Projection.checkBytesIntrinsic]

def dataPrefixes : Array Lean.Name :=
  Admission.Audit.dataImports ++ #[`Std, `Ix.Address.Pure, `Ix.Ixon.Projection]

def allowedData (name : Lean.Name) : Bool :=
  name == `Blake3 || name == `Blake3.Pure || Kernel.Audit.allowed dataPrefixes name

def allowedProof (name : Lean.Name) : Bool :=
  allowedData name || Kernel.Audit.allowed #[`Lean, `Ix.Ixon.Verify, `Ix.Ixon.ProjectionProofs,
    `Ix.Ixon.ConLecheConsistency] name

/-- The import closure of `roots` stays inside `allowed`, below con-leche's
ruled elaboration-time imports inside `Kernel.Audit.elaborationImports`
(L5: the certified checker's `BasisGen` and `PinGen` use `Lean` at
elaboration time only; L4b removed `NatOpPins` from those edges). -/
def checkImports (roots : Array Lean.Name) (allowed : Lean.Name → Bool) : Lean.Elab.Command.CommandElabM Unit := do
  let graph := Kernel.Audit.importEdges (← Lean.getEnv)
  for root in roots do
    unless graph.contains root do throwError m!"required root module is missing: {root}"
  let (closure, below) := Kernel.Audit.splitClosure graph Kernel.Audit.elaborationImports roots
  let offenders := closure.filter (!allowed ·) |>.qsort Lean.Name.lt
  unless offenders.isEmpty do throwError m!"forbidden projection imports: {offenders}"
  let elaborationOffenders := below.filter (fun module =>
    !allowed module && !Kernel.Audit.allowed Kernel.Audit.elaborationImports.allowed module)
    |>.qsort Lean.Name.lt
  unless elaborationOffenders.isEmpty do
    throwError m!"forbidden projection imports below the elaboration-time imports: {elaborationOffenders}"
  Lean.logInfo m!"projection import boundary passed: {closure.size} modules"

end Ix.Ixon.Projection.Audit

#guard_msgs (drop info) in
run_cmd Ix.Ixon.Projection.Audit.checkImports #[`Ix.Ixon.Projection] Ix.Ixon.Projection.Audit.allowedData

#guard_msgs (drop info) in
run_cmd Ix.Ixon.Projection.Audit.checkImports #[`Ix.Ixon.ProjectionProofs] Ix.Ixon.Projection.Audit.allowedProof

#guard !Ix.Ixon.Projection.Audit.allowedData `Ix.Ixon.ProjectionProofs
#guard !Ix.Ixon.Projection.Audit.allowedData `Ix.Ixon.Verify.Admission
#guard !Ix.Ixon.Projection.Audit.allowedData `Blake3.Rust
#guard !Ix.Ixon.Projection.Audit.allowedData `Blake3.C
#guard !Ix.Ixon.Projection.Audit.allowedData `Blake3.Pure.Proofs
#guard !Ix.Ixon.Projection.Audit.allowedData `Ix.Tc
#guard !Ix.Ixon.Projection.Audit.allowedData `Ix.Address
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Address.Pure
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Audit.dataImports `Ix.Ixon.Projection
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Ix.Ixon.Projection

/- Measured independently before freezing (L5; re-measured at int-4). The
certified entry adds projection reconstruction (pure BLAKE3) to the
certified byte admission. L5 alone froze 33519 functions and 124 externs;
rebased onto L4b, the committed Nat-operation pins are decoded from a string
table instead of upstream's JSON dumps spliced as one closed term (27,096
compiled functions), as in `Ix.Ixon.Admission.Audit`. -/
/-- info: runtime closure of [Ix.Ixon.Projection.address,
 Ix.Ixon.Projection.reconstruct,
 Ix.Ixon.Projection.checkBytes]: 5400 compiled functions; inherited externs 132, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Ixon.Projection.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

/- The intrinsic reference variant, unchanged from L4. Added primitives are
standard array and integer operations used by pure BLAKE3, not hash FFI
calls. -/
/-- info: runtime closure of [Ix.Ixon.Projection.address,
Ix.Ixon.Projection.reconstruct, Ix.Ixon.Projection.checkBytesIntrinsic]: 1962 compiled functions;
inherited externs 82, implemented_by 0, unsafe 3, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Ixon.Projection.Audit.intrinsicOperations #[`Init, `Std]

#guard_kernel_axioms Ix.Ixon.Projection.address_width [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.requests_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Reads.decode [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.reconstruct_ok_iff [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Added.preserves [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Added.lookup [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Added.primaries [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Expanded.complete [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Expanded.origin [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Expanded.primary [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Expanded.length [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytesIntrinsic_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytesIntrinsic_of_expansion [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytesIntrinsic_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytesIntrinsic_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytesIntrinsic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_of_expansion [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]

/-- info: def Ix.Ixon.Projection.address : Ixon.Constant → Address :=
fun record => Address.blake3Pure (Ixon.serConstant record) -/
#guard_msgs (whitespace := lax) in
#print Ix.Ixon.Projection.address

/-- info: Ix.Ixon.Projection.requests_spec : ∀ (constants : Ix.Kernel.Ingress.Constants)
  (request : Ix.Ixon.Projection.Request),
  request ∈ Ix.Ixon.Projection.requests constants ↔ Ix.Ixon.Projection.Requested constants request -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.requests_spec

/-- info: Ix.Ixon.Projection.reconstruct_ok_iff : ∀ (limit : Nat) (input output : Ix.Kernel.Ingress.Constants),
  Ix.Ixon.Projection.reconstruct limit input = Except.ok output ↔ Ix.Ixon.Projection.Expanded limit input output -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.reconstruct_ok_iff

/-- info: @Ix.Ixon.Projection.Added.primaries : ∀ {todo : List Ix.Ixon.Projection.Request}
  {input output : Ix.Kernel.Ingress.Constants},
  Ix.Ixon.Projection.Added todo input output → Ix.Ixon.Projection.primaries output = Ix.Ixon.Projection.primaries input -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.Added.primaries

/-- info: @Ix.Ixon.Projection.Added.lookup : ∀ {todo : List Ix.Ixon.Projection.Request}
  {input output : Ix.Kernel.Ingress.Constants},
  Ix.Ixon.Projection.Added todo input output →
    ∀ {key : Address} {record : Ixon.Constant},
      Ix.Kernel.Ingress.lookup input key = some record → Ix.Kernel.Ingress.lookup output key = some record -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.Added.lookup

/-- info: @Ix.Ixon.Projection.Expanded.complete : ∀ {limit : Nat} {input output : Ix.Kernel.Ingress.Constants},
  Ix.Ixon.Projection.Expanded limit input output →
    ∀ {request : Ix.Ixon.Projection.Request},
      Ix.Ixon.Projection.Requested input request →
        ∃ record,
          Ix.Ixon.Projection.Reads request record ∧
            Ix.Kernel.Ingress.lookup output (Ix.Ixon.Projection.address record) = some record -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.Expanded.complete

/-- info: @Ix.Ixon.Projection.Expanded.origin : ∀ {limit : Nat} {input output : Ix.Kernel.Ingress.Constants},
  Ix.Ixon.Projection.Expanded limit input output →
    ∀ {pair : Address × Ixon.Constant},
      pair ∈ output →
        pair ∈ input ∨
          ∃ request,
            Ix.Ixon.Projection.Requested input request ∧
              Ix.Ixon.Projection.Reads request pair.snd ∧ pair.fst = Address.blake3Pure (Ixon.serConstant pair.snd) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.Expanded.origin

/-- info: @Ix.Ixon.Projection.Expanded.length : ∀ {limit : Nat} {input output : Ix.Kernel.Ingress.Constants},
  Ix.Ixon.Projection.Expanded limit input output → List.length output ≤ List.length input + limit -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.Expanded.length

/-- info: Ix.Ixon.Projection.checkBytesIntrinsic_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Ixon.Admission.Limits)
  (cfg : Ix.Kernel.Config) (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (family : Option (Ix.Kernel.ConstRef Address)) (env : Ix.Kernel.Env Address),
  Ix.Ixon.Projection.checkBytesIntrinsic maxProjections limits cfg records blobs family = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ input output,
        Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
          Ix.Ixon.Projection.Expanded maxProjections input output ∧
            Ix.Kernel.checkEnv cfg output blobs family = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytesIntrinsic_ok_iff

/-- info: @Ix.Ixon.Projection.checkBytesIntrinsic_of_expansion : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {input output : Ix.Kernel.Ingress.Constants}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.RecordsRead limits records input →
      Ix.Ixon.Projection.Expanded maxProjections input output →
        Ix.Ixon.Projection.checkBytesIntrinsic maxProjections limits cfg records blobs family =
          Except.mapError (fun error => Ix.Ixon.Projection.Error.admission (Ix.Ixon.Admission.Error.kernel error))
            (Ix.Kernel.checkEnv cfg output blobs family) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytesIntrinsic_of_expansion

/-- info: @Ix.Ixon.Projection.checkBytesIntrinsic_reading : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {env : Ix.Kernel.Env Address},
  Ix.Ixon.Projection.checkBytesIntrinsic maxProjections limits cfg records blobs family = Except.ok env →
    ∃ input output,
      Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
        Ix.Ixon.Projection.Expanded maxProjections input output ∧
          Ix.Kernel.Ingress.Installed output blobs family none env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytesIntrinsic_reading

/-- info: Ix.Ixon.Projection.checkBytesIntrinsic_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.Model.SetTheory V]
  {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits} {cfg : Ix.Kernel.Config}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)}
  {env : Ix.Kernel.Env Address},
  Ix.Ixon.Projection.checkBytesIntrinsic maxProjections limits cfg records blobs family = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytesIntrinsic_has_model

/-! ### The certified entry's theorems (L5) -/

/-- info: Ix.Ixon.Projection.checkBytes_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Ixon.Admission.Limits)
  (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint) (env : ConLeche.Env),
  Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ input output,
        Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
          Ix.Ixon.Projection.Expanded maxProjections input output ∧
            Ix.Ixon.ConLecheAdmission.checkConstants output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_ok_iff

/-- info: @Ix.Ixon.Projection.checkBytes_of_expansion : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.RecordsRead limits records input →
      Ix.Ixon.Projection.Expanded maxProjections input output →
        Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint =
          Except.mapError Ix.Ixon.Projection.CheckError.checker
            (Ix.Ixon.ConLecheAdmission.checkConstants output blobs hint) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_of_expansion

/-- info: @Ix.Ixon.Projection.checkBytes_reading : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    ∃ input output,
      Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
        Ix.Ixon.Projection.Expanded maxProjections input output ∧
          ∃ pins pre natPins,
            Ix.Kernel.ConLecheReader.defaultPins = Except.ok pins ∧
              Ix.Kernel.ConLecheReader.builtinPrelude = Except.ok pre ∧
                Ix.Kernel.ConLecheReader.builtinNatOpPins = Except.ok natPins ∧
                  Ix.Ixon.ConLecheAdmission.Installed pins pre natPins output blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_reading

/-- info: Ix.Ixon.Projection.checkBytes_has_model : ∀ (V : Type u_1) [inst : ConLeche.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    Nonempty (ConLeche.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_has_model

/-- info: Ix.Ixon.Projection.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [ConLeche.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env},
  Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    ∀ (ci : ConLeche.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = ConLeche.Expr.const ConLeche.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_no_proof_of_False

/-- info: Additional projection externs: [ByteArray.mk,
 Array.emptyWithCapacity,
 UInt32.lor,
 UInt32.shiftLeft,
 UInt32.sub,
 UInt32.shiftRight,
 UInt32.xor,
 UInt32.add,
 UInt64.toUInt32,
 UInt32.ofNat,
 Nat.log2]
---
info: Additional projection unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Admission.Audit.intrinsicOperations
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Projection.Audit.intrinsicOperations
  Lean.logInfo m!"Additional projection externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional projection unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"

/-- info: Additional certified projection externs: [UInt32.lor,
 UInt32.shiftLeft,
 UInt32.sub,
 UInt32.shiftRight,
 UInt32.xor,
 UInt32.add,
 UInt64.toUInt32,
 UInt32.ofNat,
 Nat.log2]
---
info: Additional certified projection unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Admission.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Projection.Audit.operations
  Lean.logInfo m!"Additional certified projection externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified projection unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
