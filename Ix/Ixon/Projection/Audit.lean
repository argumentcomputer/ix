import Ix.Ixon.Projection.Theorems
import Ix.Kernel.Admission.Audit

/-! Projection hashing has an explicit boundary outside the dependency-free
kernel and codec. Only the shared Blake3 types and pure implementation are
allowed; permitting the entire Blake3 prefix would admit its FFI backends. -/

namespace Ixon.Projection.Audit

/-- The certified entry with projection reconstruction. -/
def operations : Array Lean.Name :=
  #[``Projection.address, ``Projection.reconstruct, ``Projection.checkBytes]

def dataPrefixes : Array Lean.Name :=
  Ix.Kernel.Admission.Audit.dataImports ++ #[`Std, `Ix.Address.Pure, `Ix.Ixon.Projection]

/-- The theorem and audit modules under `dataPrefixes`. -/
def dataDenied : Array Lean.Name :=
  Ix.Kernel.Audit.importDenylist ++ #[`Ix.Ixon.Projection.Theorems, `Ix.Ixon.Projection.Audit]

def allowedData (name : Lean.Name) : Bool :=
  name == `Blake3 || name == `Blake3.Pure || Ix.Kernel.Audit.allowed dataPrefixes name dataDenied

def allowedProof (name : Lean.Name) : Bool :=
  allowedData name || Ix.Kernel.Audit.allowed #[`Lean, `Ix.Ixon.Verify, `Ix.Ixon.Projection.Theorems,
    `Ix.Kernel.Admission.Theorems, `Ix.Kernel.Admission.Bytes.Theorems] name

/-- The import closure of `roots` stays inside `allowed`, below the kernel's
ruled elaboration-time imports inside `Kernel.Audit.elaborationImports`
(the kernel's `BasisGen` uses `Lean` at elaboration time
only). -/
def checkImports (roots : Array Lean.Name) (allowed : Lean.Name → Bool) : Lean.Elab.Command.CommandElabM Unit := do
  let graph := Ix.Kernel.Audit.importEdges (← Lean.getEnv)
  for root in roots do
    unless graph.contains root do throwError m!"required root module is missing: {root}"
  let (closure, below) := Ix.Kernel.Audit.splitClosure graph Ix.Kernel.Audit.elaborationImports roots
  let offenders := closure.filter (!allowed ·) |>.qsort Lean.Name.lt
  unless offenders.isEmpty do throwError m!"forbidden projection imports: {offenders}"
  let elaborationOffenders := below.filter (fun module =>
    !allowed module && !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.elaborationImports.allowed module)
    |>.qsort Lean.Name.lt
  unless elaborationOffenders.isEmpty do
    throwError m!"forbidden projection imports below the elaboration-time imports: {elaborationOffenders}"
  Lean.logInfo m!"projection import boundary passed: {closure.size} modules"

end Ixon.Projection.Audit

#guard_msgs (drop info) in
run_cmd Ixon.Projection.Audit.checkImports #[`Ix.Ixon.Projection] Ixon.Projection.Audit.allowedData

#guard_msgs (drop info) in
run_cmd Ixon.Projection.Audit.checkImports #[`Ix.Ixon.Projection.Theorems] Ixon.Projection.Audit.allowedProof

#guard !Ixon.Projection.Audit.allowedData `Ix.Ixon.Projection.Theorems
#guard !Ixon.Projection.Audit.allowedData `Ix.Kernel.Admission.Bytes.Theorems
#guard !Ixon.Projection.Audit.allowedData `Blake3.Rust
#guard !Ixon.Projection.Audit.allowedData `Blake3.C
#guard !Ixon.Projection.Audit.allowedData `Blake3.Pure.Proofs
#guard !Ixon.Projection.Audit.allowedData `Ix.Tc
#guard !Ixon.Projection.Audit.allowedData `Ix.Address
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Address.Pure Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ixon.Audit.dataImports `Ix.Ixon.Projection
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Ix.Ixon.Projection Ix.Kernel.Audit.importDenylist
#guard !Ixon.Projection.Audit.allowedData `Ix.Ixon.Projection.Audit
#guard !Ixon.Projection.Audit.allowedData `Ix.Kernel.Admission.Theorems
#guard Ixon.Projection.Audit.allowedData `Ix.Ixon.Projection

/- Measured independently before freezing. The certified entry adds
projection reconstruction (pure BLAKE3) to the certified byte admission
(`Ix.Kernel.Admission.Audit`), with the same ruled constructs and the same
codec: projection records are written with Ixon v4's TagN writer
(`Ixon.putTagN`, `tagNHeader`, `tagNEnd1..6`) and read with its reader
(`getTagN`, `getTagNWide`, `getTagN0Values`). -/
/-- info: runtime closure of [Ixon.Projection.address,
 Ixon.Projection.reconstruct,
 Ixon.Projection.checkBytes]: 5416 compiled functions; inherited externs 130, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ixon.Projection.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ixon.Projection.address_width [propext, Quot.sound]
#guard_kernel_axioms Ixon.Projection.requests_spec [propext, Quot.sound]
#guard_kernel_axioms Ixon.Projection.Reads.decode [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Projection.reconstruct_ok_iff [propext, Quot.sound]
#guard_kernel_axioms Ixon.Projection.Added.preserves [propext, Quot.sound]
#guard_kernel_axioms Ixon.Projection.Added.lookup [propext, Quot.sound]
#guard_kernel_axioms Ixon.Projection.Added.primaries [propext, Quot.sound]
#guard_kernel_axioms Ixon.Projection.Expanded.complete [propext, Quot.sound]
#guard_kernel_axioms Ixon.Projection.Expanded.origin [propext, Quot.sound]
#guard_kernel_axioms Ixon.Projection.Expanded.length [propext, Quot.sound]
-- The projection writer the reconstruction runs.
#guard_kernel_axioms Ix.Kernel.Egress.writeProjection_reading [propext]
#guard_kernel_axioms Ix.Kernel.Egress.writeProjection_roundtrip [propext]
#guard_kernel_axioms Ixon.Projection.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Projection.checkBytes_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Projection.checkBytes_of_expansion [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Projection.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Projection.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.Projection.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]

/-- info: def Ixon.Projection.address : Ixon.Constant → Address :=
fun record => Address.blake3Pure (Ixon.serConstant record) -/
#guard_msgs (whitespace := lax) in
#print Ixon.Projection.address

/-- info: Ixon.Projection.requests_spec : ∀ (constants : Ix.Kernel.Ingress.Constants)
  (request : Ixon.Projection.Request),
  request ∈ Ixon.Projection.requests constants ↔ Ixon.Projection.Requested constants request -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.requests_spec

/-- info: Ixon.Projection.reconstruct_ok_iff : ∀ (limit : Nat) (input output : Ix.Kernel.Ingress.Constants),
  Ixon.Projection.reconstruct limit input = Except.ok output ↔ Ixon.Projection.Expanded limit input output -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.reconstruct_ok_iff

/-- info: @Ixon.Projection.Added.primaries : ∀ {todo : List Ixon.Projection.Request}
  {input output : Ix.Kernel.Ingress.Constants},
  Ixon.Projection.Added todo input output → Ixon.Projection.primaries output = Ixon.Projection.primaries input -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.Added.primaries

/-- info: @Ixon.Projection.Added.lookup : ∀ {todo : List Ixon.Projection.Request}
  {input output : Ix.Kernel.Ingress.Constants},
  Ixon.Projection.Added todo input output →
    ∀ {key : Address} {record : Ixon.Constant},
      Ix.Kernel.Ingress.lookup input key = some record → Ix.Kernel.Ingress.lookup output key = some record -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.Added.lookup

/-- info: @Ixon.Projection.Expanded.complete : ∀ {limit : Nat} {input output : Ix.Kernel.Ingress.Constants},
  Ixon.Projection.Expanded limit input output →
    ∀ {request : Ixon.Projection.Request},
      Ixon.Projection.Requested input request →
        ∃ record,
          Ixon.Projection.Reads request record ∧
            Ix.Kernel.Ingress.lookup output (Ixon.Projection.address record) = some record -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.Expanded.complete

/-- info: @Ixon.Projection.Expanded.origin : ∀ {limit : Nat} {input output : Ix.Kernel.Ingress.Constants},
  Ixon.Projection.Expanded limit input output →
    ∀ {pair : Address × Ixon.Constant},
      pair ∈ output →
        pair ∈ input ∨
          ∃ request,
            Ixon.Projection.Requested input request ∧
              Ixon.Projection.Reads request pair.snd ∧ pair.fst = Address.blake3Pure (Ixon.serConstant pair.snd) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.Expanded.origin

/-- info: @Ixon.Projection.Expanded.length : ∀ {limit : Nat} {input output : Ix.Kernel.Ingress.Constants},
  Ixon.Projection.Expanded limit input output → List.length output ≤ List.length input + limit -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.Expanded.length

/-! ### The certified entry's theorems -/

/-- info: Ixon.Projection.checkBytes_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Kernel.Admission.Limits)
  (records : Ix.Kernel.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) (env : Ix.Kernel.Env),
  Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env ↔
    Ix.Kernel.Admission.WithinBatch limits records blobs ∧
      Ix.Kernel.Admission.UniqueKeys records blobs ∧
        ∃ input output,
          Ix.Kernel.Admission.RecordsRead limits records input ∧
            Ixon.Projection.Expanded maxProjections input output ∧
              Ix.Kernel.Admission.checkConstants output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.checkBytes_ok_iff

/-- info: @Ixon.Projection.checkBytes_of_expansion : ∀ {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint},
  Ix.Kernel.Admission.WithinBatch limits records blobs →
    Ix.Kernel.Admission.UniqueKeys records blobs →
      Ix.Kernel.Admission.RecordsRead limits records input →
        Ixon.Projection.Expanded maxProjections input output →
          Ixon.Projection.checkBytes maxProjections limits records blobs hint =
            Except.mapError Ixon.Projection.CheckError.checker
              (Ix.Kernel.Admission.checkConstants output blobs hint) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.checkBytes_of_expansion

/-- info: @Ixon.Projection.checkBytes_reading : ∀ {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.UniqueKeys records blobs ∧
      ∃ input output,
        Ix.Kernel.Admission.RecordsRead limits records input ∧
          Ixon.Projection.Expanded maxProjections input output ∧
            ∃ pins pre natPins,
              Ix.Kernel.Reader.defaultPins = Except.ok pins ∧
                Ix.Kernel.Reader.builtinPrelude = Except.ok pre ∧
                  Ix.Kernel.Reader.builtinNatOpPins = Except.ok natPins ∧
                    Ix.Kernel.Admission.Installed pins pre natPins output blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.checkBytes_reading

/-- info: Ixon.Projection.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.checkBytes_has_model

/-- info: Ixon.Projection.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.Projection.checkBytes maxProjections limits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ixon.Projection.checkBytes_no_proof_of_False

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
  let before := Ix.Kernel.Audit.runtimeClosure env Ix.Kernel.Admission.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ixon.Projection.Audit.operations
  Lean.logInfo m!"Additional certified projection externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified projection unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
