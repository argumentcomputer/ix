module

public import Ix.HostAdmission.Codec
public import Ix.HostAdmission.Merkle
public import Ix.RoleBinding.ArtifactTiered
public import Ix.SpecDigest

/-! Host commitments to actual target-artifact admission. A parsed statement
is not evidence. Verification replays the actual entry and matches every
commitment. There is no Source-value/CompileCorrect constructor here. -/

@[expose] public section

namespace Ix.HostAdmission

open Ix.RoleBinding

inductive Error where
  | encoding (message : String)
  | preparation (error : Artifact.Error)
  | tiered (error : Artifact.TierError)
  | identity (message : String)
  deriving Inhabited

instance : ToString Error where
  toString
    | .encoding e | .identity e => e
    | .preparation e => toString e
    | .tiered e => toString e

inductive Run (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) where
  | logical (receipt : Artifact.Receipt artifact limits)
  | tiered (receipt : Artifact.TierReceipt artifact limits)

def Run.prepared : Run artifact limits → Artifact.Prepared
  | .logical receipt => receipt.prepared
  | .tiered receipt => receipt.prepared

def Run.logicalEnv : Run artifact limits → Ix.Kernel.Env .anon
  | .logical receipt => receipt.target
  | .tiered receipt => receipt.logical

def Run.typed : Run artifact limits → List (Ix.Kernel.Tier.TierConst .anon)
  | .logical _ => []
  | .tiered receipt => receipt.tier

def MainMember (main : Option Address) (addresses : List Address) : Prop :=
  match main with | none => True | some address => address ∈ addresses

instance (main : Option Address) (addresses : List Address) : Decidable (MainMember main addresses) := by
  cases main <;> unfold MainMember <;> infer_instance

def KindAgreement (limits : Ix.Kernel.Admission.Limits) (records : Ix.Kernel.Admission.Records)
    (kind : Kind) : Prop :=
  ∃ constants, Ix.Kernel.Admission.decodeRecords limits records = .ok constants ∧
    constants.map (·.1) = records.map (·.1) ∧
    match kind with
    | .logical => constants.any (fun (_, c) => Ix.Kernel.Admission.isTierInfo c.info) = false
    | .tiered logicalRoot tierRoot =>
      constants.any (fun (_, c) => Ix.Kernel.Admission.isTierInfo c.info) = true ∧
      Merkle.root ((Ix.Kernel.Admission.partitionTier constants).1.map (·.1)).toArray = .ok logicalRoot ∧
      Merkle.root ((Ix.Kernel.Admission.partitionTier constants).2.map fun (_, a, _) => a) = .ok tierRoot

structure Facts (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (run : Run artifact limits) (kind : Kind) (spec root : Address) : Prop where
  closed : artifact.assumptions.isEmpty = true
  mainMember : MainMember artifact.main (run.prepared.records.map (·.1))
  currentSpec : Ix.SpecDigest.specDigest = .ok spec
  contentRoot : Merkle.root (run.prepared.records.map (·.1)).toArray = .ok (some root)
  kindAgreement : KindAgreement limits run.prepared.records kind

structure Components (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (run : Run artifact limits) where
  kind : Kind
  spec : Address
  root : Address
  facts : Facts artifact limits run kind spec root

def require (condition : Prop) [Decidable condition] (message : String) :
    Except Error (PLift condition) :=
  if proved : condition then .ok ⟨proved⟩ else .error (.identity message)

def unique (addresses : List Address) : Except Error (Std.HashSet Address) := do
  let mut seen := {}
  for address in addresses do
    unless address.hash.size == 32 do throw (.identity "host statement: prepared address width is not 32 bytes")
    if seen.contains address then throw (.identity "host statement: duplicate prepared address")
    seen := seen.insert address
  return seen

/-- All fields are derived from the complete actual receipt input, rather than
an independently proposed table, subject, main, or success flag. -/
def componentsOf (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (run : Run artifact limits) : Except Error (Components artifact limits run) := do
  let ⟨closed⟩ ← require (artifact.assumptions.isEmpty = true)
    "host statement: external artifact assumptions are unsupported"
  let p := run.prepared
  let addresses := p.records.map (·.1)
  let all ← unique addresses
  for main in artifact.main do
    unless main.hash.size == 32 do throw (.identity "host statement: main address width is not 32 bytes")
  let ⟨member⟩ ← require (MainMember artifact.main addresses)
    "host statement: main is not an actual input record"
  match rootEq : Merkle.root addresses.toArray with
  | .error e => throw (.encoding e)
  | .ok none => throw (.identity "host statement: no content root for an empty input")
  | .ok (some root) =>
    match specEq : Ix.SpecDigest.specDigest with
    | .error e => throw (.encoding e)
    | .ok spec =>
      match decoded : Ix.Kernel.Admission.decodeRecords limits p.records with
      | .error e => throw (.preparation (.bytes e))
      | .ok constants =>
        let ⟨keys⟩ ← require (constants.map (·.1) = addresses)
          "host statement: decoded records changed input coverage"
        let hasTier := constants.any fun (_, c) => Ix.Kernel.Admission.isTierInfo c.info
        let ⟨kind, kindAgreement⟩ : { k // KindAgreement limits p.records k } ← match run with
          | .logical _ => do
            if tier : hasTier = false then
              pure ⟨.logical, constants, decoded, keys, tier⟩
            else throw (.identity "host statement: logical mode has tier input")
          | .tiered _ => do
            let ⟨tier⟩ ← require (hasTier = true) "host statement: tier mode has no tier input"
            let parts := Ix.Kernel.Admission.partitionTier constants
            let logical := parts.1.map (·.1)
            let typed := parts.2.map fun (_, a, _) => a
            let partition ← unique (logical ++ typed.toList)
            unless partition.size == all.size && addresses.all partition.contains do
              throw (.identity "host statement: partition does not cover the complete input")
            match left : Merkle.root logical.toArray, right : Merkle.root typed with
            | .error e, _ | _, .error e => throw (.encoding e)
            | .ok l, .ok t => pure ⟨.tiered l t, constants, decoded, keys, tier, left, right⟩
        return { kind, spec, root, facts := ⟨closed, member, specEq, rootEq, kindAgreement⟩ }

def statementOf (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits)
    (run : Run artifact limits) : Except Error Statement :=
  (componentsOf artifact limits run).map fun value =>
    { kind := value.kind, hostSpecDigest := value.spec, bindingHash := run.prepared.binding.address
      contentRoot := value.root, main := artifact.main }

/-- This contains actual entry evidence and equality to its derived statement.
It is never deserialized from an untrusted claim or stored success marker. -/
structure Checked (statement : Statement) (artifact : Ixon.Env)
    (limits : Ix.Kernel.Admission.Limits) where
  run : Run artifact limits
  derived : statementOf artifact limits run = .ok statement

def certify (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except Error (Σ statement, Checked statement artifact limits) := do
  unless artifact.assumptions.isEmpty do
    throw (.identity "host statement: external artifact assumptions are unsupported")
  let input ← (Artifact.prepareRecords artifact limits).mapError .preparation
  let run ← if input.hasTier then
      (Artifact.checkTiered artifact limits).map Run.tiered |>.mapError .tiered
    else (Artifact.check artifact limits).map Run.logical |>.mapError .preparation
  match made : statementOf artifact limits run with
  | .error e => throw e
  | .ok statement => return ⟨statement, ⟨run, made⟩⟩

def verify (expected : Statement) (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except Error (Checked expected artifact limits) := do
  expected.check.mapError .encoding
  let ⟨actual, checked⟩ ← certify artifact limits
  if same : actual = expected then return same ▸ checked
  else throw (.identity "host statement: commitments differ from actual admitted artifact")

def verifyBytes (bytes : ByteArray) (artifact : Ixon.Env) (limits : Ix.Kernel.Admission.Limits) :
    Except Error (Σ statement, Checked statement artifact limits) := do
  let statement ← Statement.decode bytes |>.mapError .encoding
  return ⟨statement, ← verify statement artifact limits⟩

/-- Store.read does not authenticate its key. Every addressed verification
must check the bytes at that address before parsing or replaying admission. -/
def verifyAddressed (address : Address) (bytes : ByteArray) (artifact : Ixon.Env)
    (limits : Ix.Kernel.Admission.Limits) :
    Except Error (Σ statement, Checked statement artifact limits) := do
  unless Address.admissionHash bytes == address do
    throw (.identity "host statement: stored bytes do not match their address")
  verifyBytes bytes artifact limits

end Ix.HostAdmission
