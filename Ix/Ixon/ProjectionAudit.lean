import Ix.Ixon.ProjectionProofs
import Ix.Ixon.Admission.Audit

/-! Projection hashing has an explicit boundary outside the dependency-free
kernel and codec. Only the shared Blake3 types and pure implementation are
allowed; permitting the entire Blake3 prefix would admit its FFI backends. -/

namespace Ix.Ixon.Projection.Audit

/-- The certified entry with projection reconstruction. -/
def operations : Array Lean.Name :=
  #[``Projection.address, ``Projection.reconstruct, ``Projection.checkBytes]

def dataPrefixes : Array Lean.Name :=
  Admission.Audit.dataImports ++ #[`Std, `Ix.Address.Pure, `Ix.Ixon.Projection]

def allowedData (name : Lean.Name) : Bool :=
  name == `Blake3 || name == `Blake3.Pure || Kernel.Audit.allowed dataPrefixes name

def allowedProof (name : Lean.Name) : Bool :=
  allowedData name || Kernel.Audit.allowed #[`Lean, `Ix.Ixon.Verify, `Ix.Ixon.ProjectionProofs,
    `Ix.Ixon.KernelConsistency] name

/-- The import closure of `roots` stays inside `allowed`, below the kernel's
ruled elaboration-time imports inside `Kernel.Audit.elaborationImports`
(the kernel's `BasisGen` uses `Lean` at elaboration time
only). -/
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

/- Measured independently before freezing. The certified entry adds
projection reconstruction (pure BLAKE3) to the certified byte admission
(`Ix.Ixon.Admission.Audit`), with the same ruled constructs. -/
/-- info: runtime closure of [Ix.Ixon.Projection.address,
 Ix.Ixon.Projection.reconstruct,
 Ix.Ixon.Projection.checkBytes]: 5430 compiled functions; inherited externs 132, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Ixon.Projection.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ix.Ixon.Projection.address_width [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.requests_spec [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Reads.decode [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.reconstruct_ok_iff [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Added.preserves [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Added.lookup [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Added.primaries [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Expanded.complete [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Expanded.origin [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.Projection.Expanded.length [propext, Quot.sound]
-- The projection writer the reconstruction runs.
#guard_kernel_axioms Ix.Kernel.Egress.writeProjection_reading [propext]
#guard_kernel_axioms Ix.Kernel.Egress.writeProjection_roundtrip [propext]
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

/-! ### The certified entry's theorems -/

/-- info: Ix.Ixon.Projection.checkBytes_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Ixon.Admission.Limits)
  (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) (env : Ix.Kernel.Env),
  Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
        ∃ input output,
          Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
            Ix.Ixon.Projection.Expanded maxProjections input output ∧
              Ix.Ixon.KernelAdmission.checkConstants output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_ok_iff

/-- info: @Ix.Ixon.Projection.checkBytes_of_expansion : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.UniqueKeys records blobs →
      Ix.Ixon.Verify.Admission.RecordsRead limits records input →
        Ix.Ixon.Projection.Expanded maxProjections input output →
          Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint =
            Except.mapError Ix.Ixon.Projection.CheckError.checker
              (Ix.Ixon.KernelAdmission.checkConstants output blobs hint) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_of_expansion

/-- info: @Ix.Ixon.Projection.checkBytes_reading : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
      ∃ input output,
        Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
          Ix.Ixon.Projection.Expanded maxProjections input output ∧
            ∃ pins pre natPins,
              Ix.Kernel.IxonReader.defaultPins = Except.ok pins ∧
                Ix.Kernel.IxonReader.builtinPrelude = Except.ok pre ∧
                  Ix.Kernel.IxonReader.builtinNatOpPins = Except.ok natPins ∧
                    Ix.Ixon.KernelAdmission.Installed pins pre natPins output blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_reading

/-- info: Ix.Ixon.Projection.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_has_model

/-- info: Ix.Ixon.Projection.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.Projection.checkBytes_no_proof_of_False

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
