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

def operations : Array Lean.Name :=
  #[``Projection.address, ``Projection.reconstruct, ``Projection.checkBytes]

def dataPrefixes : Array Lean.Name :=
  Admission.Audit.dataImports ++ #[`Std, `Ix.Address.Pure, `Ix.Ixon.Projection]

def allowedData (name : Lean.Name) : Bool :=
  name == `Blake3 || name == `Blake3.Pure || Kernel.Audit.allowed dataPrefixes name

def allowedProof (name : Lean.Name) : Bool :=
  allowedData name || Kernel.Audit.allowed #[`Lean, `Ix.Ixon.Verify, `Ix.Ixon.ProjectionProofs] name

def checkImports (roots : Array Lean.Name) (allowed : Lean.Name → Bool) : Lean.Elab.Command.CommandElabM Unit := do
  let graph := Kernel.Audit.importGraph (← Lean.getEnv)
  for root in roots do
    unless graph.contains root do throwError m!"required root module is missing: {root}"
  let closure := Kernel.Audit.importClosure graph roots
  let offenders := closure.filter (!allowed ·) |>.qsort Lean.Name.lt
  unless offenders.isEmpty do throwError m!"forbidden projection imports: {offenders}"
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

/- Measured independently before freezing. Added primitives are standard
array and integer operations used by pure BLAKE3, not hash FFI calls. -/
/-- info: runtime closure of [Ix.Ixon.Projection.address,
Ix.Ixon.Projection.reconstruct, Ix.Ixon.Projection.checkBytes]: 1694 compiled functions;
inherited externs 81, implemented_by 0, unsafe 2, csimp 0 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntime Ix.Ixon.Projection.Audit.operations #[`Init, `Std]

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
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_of_expansion [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.checkBytes [propext, Classical.choice, Quot.sound]

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

/-- info: Ix.Ixon.Projection.checkBytes_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Ixon.Admission.Limits)
  (cfg : Ix.Kernel.Config) (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (family : Option (Ix.Kernel.ConstRef Address)) (env : Ix.Kernel.Env Address),
  Ix.Ixon.Projection.checkBytes maxProjections limits cfg records blobs family = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      ∃ input output,
        Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
          Ix.Ixon.Projection.Expanded maxProjections input output ∧
            Ix.Kernel.checkEnv cfg output blobs family = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_ok_iff

/-- info: @Ix.Ixon.Projection.checkBytes_of_expansion : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {input output : Ix.Kernel.Ingress.Constants}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.RecordsRead limits records input →
      Ix.Ixon.Projection.Expanded maxProjections input output →
        Ix.Ixon.Projection.checkBytes maxProjections limits cfg records blobs family =
          Except.mapError (fun error => Ix.Ixon.Projection.Error.admission (Ix.Ixon.Admission.Error.kernel error))
            (Ix.Kernel.checkEnv cfg output blobs family) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_of_expansion

/-- info: @Ix.Ixon.Projection.checkBytes_reading : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {family : Option (Ix.Kernel.ConstRef Address)} {env : Ix.Kernel.Env Address},
  Ix.Ixon.Projection.checkBytes maxProjections limits cfg records blobs family = Except.ok env →
    ∃ input output,
      Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
        Ix.Ixon.Projection.Expanded maxProjections input output ∧ Ix.Kernel.Ingress.Installed output blobs family none env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_reading

/-- info: Ix.Ixon.Projection.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.Model.SetTheory V]
  {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits} {cfg : Ix.Kernel.Config} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {family : Option (Ix.Kernel.ConstRef Address)} {env : Ix.Kernel.Env Address},
  Ix.Ixon.Projection.checkBytes maxProjections limits cfg records blobs family = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_has_model

/-- info: Additional projection externs: [ByteArray.mk,
 Array.emptyWithCapacity,
 Nat.shiftRight,
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
  let before := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Admission.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Projection.Audit.operations
  Lean.logInfo m!"Additional projection externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional projection unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
