import Lean
import Ix.Compiler.Coverage.Sources
import Ix.Compiler.IxIR1.HPTCache

/-! Complete diagnostic snapshots for comparing fresh compiler processes.
Ixon, IxIR₀, IxIR₁, and HPT records use their existing canonical bytes and
identities. The IxIR₂ JSON is a structural diagnostic only: it has no decoder,
content address, persistent cache role, or claim to be an IxIR₂ wire format.
Proof terms are erased; their retained executable artifacts are compared. -/

namespace Ix.Compiler.Coverage

open Lean Ix.Compiler.Ixon

instance : ToJson Address := ⟨fun address => toJson address.toHex⟩
deriving instance ToJson for Owned
deriving instance ToJson for Pipeline.Limits
deriving instance ToJson for Policy
deriving instance ToJson for IxIR1.HPT.Limits
deriving instance ToJson for IxIR1.HPT.ProducerLimits
deriving instance ToJson for IxIR1.HPT.ProducerStats
deriving instance ToJson for IxIR0.Literal
deriving instance ToJson for IxIR1.CtorId
deriving instance ToJson for IxIR2.Atom
deriving instance ToJson for IxIR2.ParamPassing
deriving instance ToJson for IxIR2.Param
deriving instance ToJson for IxIR2.Signature
deriving instance ToJson for IxIR2.BorrowLender
deriving instance ToJson for IxIR2.ValueCap
deriving instance ToJson for IxIR2.CreditCap
deriving instance ToJson for IxIR2.CtorSchema
deriving instance ToJson for IxIR2.Instr
deriving instance ToJson for IxIR2.Edge
deriving instance ToJson for IxIR2.CtorAlt
deriving instance ToJson for IxIR2.NatPeel
deriving instance ToJson for IxIR2.Terminator
deriving instance ToJson for IxIR2.Block
deriving instance ToJson for IxIR2.Function
deriving instance ToJson for IxIR2.Decl
deriving instance ToJson for IxIR2.Program
deriving instance ToJson for IxIR2.Validate.Stats
deriving instance ToJson for IxIR2.Pipeline.ConstructorInfo
deriving instance ToJson for IxIR2.Pipeline.RecursorOrigin

def hex (bytes : ByteArray) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut chars : Array Char := #[]
  for byte in bytes do
    chars := chars.push digits[byte.toNat / 16]!
    chars := chars.push digits[byte.toNat % 16]!
  return String.ofList chars.toList

def byteJson (bytes : ByteArray) : Json := toJson (hex bytes)

def ir0Entries (entries : List (Address × IxIR0.Decl)) : Json :=
  toJson (entries.map fun (address, declaration) =>
    Json.mkObj [("key", toJson address), ("preimage", byteJson declaration.preimage)])

def ir1Entries (entries : List (Address × IxIR1.Decl)) : Json :=
  toJson (entries.map fun (address, declaration) =>
    Json.mkObj [("key", toJson address), ("preimage", byteJson declaration.preimage)])

def ir0Block (block : IxIR0.MutualBlock.Result) : Json :=
  Json.mkObj [
    ("root", toJson block.blockAddress),
    ("preimage", byteJson (IxIR0.MutualBlock.Block.preimage block.blockMembers)),
    ("members", ir0Entries block.members), ("address_map", toJson block.addressMap)]

def ir0Group (group : IxIR0.Readdress.Group) : Json :=
  Json.mkObj [
    ("kind", toJson (match group with | .stable _ => "stable" | .mutual _ => "mutual")),
    ("entries", ir0Entries group.entries)]

/-- Complete eraser/addressing output, before the source erasure certificate
has been accepted. This is useful even when the next validator rejects. -/
def erasedSnapshot (root : Address) (erasure : EraseAddressed.Result) : Json :=
  Json.mkObj [
    ("raw_declarations", ir0Entries erasure.raw),
    ("raw_main", byteJson (IxIR0.Expr.bytes (.ref root))),
    ("groups", toJson (erasure.groups.map ir0Group)),
    ("declarations", ir0Entries erasure.declarations),
    ("main", byteJson erasure.main.bytes),
    ("blocks", toJson (erasure.addressed.blocks.map ir0Block)),
    ("address_map", toJson erasure.addressMap)]

def addressedSnapshot (constants : List (Address × Constant)) (root : Address)
    (config : Pipeline.Config) (fuel : Nat) : Except String Json := do
  let ctx := EraseValidator.eraseCtxOf (Pipeline.validatedEvalCtx constants config)
  let erasure ← (EraseAddressed.run ctx constants (.ref root) fuel).mapError reprStr
  return Json.mkObj [
    ("format", toJson "compilatrix/addressed-erasure/1"),
    ("source_erasure_certified", toJson false),
    ("ixir0", erasedSnapshot root erasure)]

def ir1Artifact : IxIR1.ReaddressAll.Artifact → Json
  | .stable address declaration =>
      Json.mkObj [("kind", toJson "stable"), ("root", toJson address),
        ("preimage", byteJson declaration.preimage)]
  | .ordinary address declaration =>
      Json.mkObj [("kind", toJson "ordinary"), ("root", toJson address),
        ("preimage", byteJson declaration.preimage)]
  | .mutual block =>
      Json.mkObj [("kind", toJson "mutual"), ("root", toJson block.blockAddress),
        ("preimage", byteJson (IxIR1.MutualBlock.Block.preimage block.blockMembers)),
        ("members", ir1Entries block.members), ("address_map", toJson block.addressMap)]

private def hptMembers (members : List (Address × IxIR1.HPT.Fact)) : Json :=
  toJson (members.map fun (address, fact) =>
    Json.mkObj [("key", toJson address), ("fact_bytes", byteJson fact.bytes)])

def hptCandidate (candidate : IxIR1.HPT.CandidateArtifact) : Json :=
  Json.mkObj [("program_root", toJson candidate.programIdentity),
    ("members", hptMembers candidate.members)]

def hptArtifact (artifact : IxIR1.HPT.Artifact) : Json :=
  Json.mkObj [
    ("program_root", toJson artifact.programIdentity),
    ("cache_key", toJson artifact.cacheKey), ("root", toJson artifact.address),
    ("dependencies", toJson artifact.dependencies), ("members", hptMembers artifact.members),
    ("bytes", byteJson (IxIR1.HPT.Cache.encodeArtifact artifact))]

def Source.inputSnapshot (source : Source) : Json :=
  Json.mkObj [
    ("root", toJson source.root),
    ("constants", toJson (source.constants.map fun (address, constant) =>
      Json.mkObj [("key", toJson address), ("bytes", byteJson (ser constant))])),
    ("literal_inputs", toJson (source.literals.map fun number =>
      Json.mkObj [("key", toJson (X86.ValidatedScalar.literalAddress number)),
        ("nat", toJson number)])),
    ("nat_block", toJson source.natBlock), ("policy", toJson source.policy)]

/-- Compare both pre-address and final graphs, every renaming map and mutual
artifact, the actual checked HPT certificate and summary records, and the
finite IxIR₂ sidecars. No `repr` digest stands in for any of these artifacts. -/
def Source.compilationSnapshot (source : Source) (attached : source.Attached) : Json :=
  let erasure := attached.source.erasure.result
  let lowering := attached.source.lowering
  let artifact := attached.source.artifact
  Json.mkObj [
    ("format", toJson "compilatrix/compiler-snapshot/1"),
    ("source", source.inputSnapshot),
    ("ixir0", erasedSnapshot source.root erasure),
    ("ixir1", Json.mkObj [
      ("root", toJson (IxIR1.Optimizer.graphRoot artifact.targetArtifacts artifact.main)),
      ("raw_declarations", ir1Entries lowering.raw),
      ("raw_main", byteJson lowering.mainCode.bytes),
      ("artifacts", toJson (artifact.targetArtifacts.map ir1Artifact)),
      ("declarations", ir1Entries artifact.targetDecls),
      ("main", byteJson artifact.main.bytes),
      ("address_map", toJson artifact.targetAddressMap),
      ("reserved", toJson lowering.result.reserved)]),
    ("hpt", Json.mkObj [
      ("producer_limits", toJson IxIR1.HPT.defaultProducerLimits),
      ("producer_stats", toJson attached.hpt.stats),
      ("candidate", toJson (attached.hpt.certificate.artifacts.map hptCandidate)),
      ("artifacts", toJson (attached.hpt.result.artifacts.map hptArtifact))]),
    ("ixir2_diagnostic", Json.mkObj [
      ("program", toJson attached.target.artifact.program),
      ("validation_stats", toJson attached.target.stats),
      ("parameter_worlds", toJson attached.sidecars.parameterEntries),
      ("constructors", toJson attached.sidecars.constructors),
      ("recursor_origins", toJson attached.sidecars.recursorOrigins)])]

end Ix.Compiler.Coverage
