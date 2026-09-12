import Compilatrix.IxIR2.Decode
import Std.Data.HashSet

/-!
# Addressed snapshot ingress and finite-context validation

Decoding establishes byte identity. This additional boundary checks the
claimed root, finite sidecar keys and layout preimages, then invokes the
existing ownership validator with caller-supplied limits. It does not infer
source provenance or prove a target ABI from an opaque layout descriptor.
-/

namespace Compilatrix.IxIR2.Wire

open Compilatrix.Ixon (Address Owned)
open Compilatrix.IxIR

def semanticsVersion : String := "ixir2-semantics/0"
def validatorVersion : String := "ixir2-ownership-flow/1"

structure Encoded (limits : Bounded.Limits) (artifact : Artifact) where
  bytes : ByteArray
  exact : bytes = artifact.preimage
  fits : artifact.Fits limits

def Artifact.encodeChecked (limits : Bounded.Limits) (artifact : Artifact) :
    Except String (Encoded limits artifact) := do
  if shape : artifactFits limits artifact then
    let bytes := artifact.preimage
    if size : bytes.size ≤ limits.maxBytes then return ⟨bytes, rfl, size, shape⟩
    else throw "IxIR2 snapshot: encoded byte limit"
  else throw "IxIR2 snapshot: representation limit"

theorem Encoded.roundtrip {limits : Bounded.Limits} {artifact : Artifact}
    (encoded : Encoded limits artifact) :
    Artifact.decodePreimage limits encoded.bytes = .ok artifact := by
  rw [encoded.exact]
  exact artifact.decodePreimage_roundtrip limits encoded.fits

def Artifact.context (artifact : Artifact) : Validate.Context :=
  { schemas := fun world constructor =>
      (artifact.schemas.toList.find? fun schema =>
        schema.world == world && schema.constructor == constructor).map (·.definition)
    scalarLeaves := artifact.scalarLeaves.toList
    allowExtern := artifact.policy.allowExtern }

private def uniqueKeys [BEq α] [Hashable α] (values : Array α) : Bool := Id.run do
  let mut seen : Std.HashSet α := {}
  for value in values do
    if seen.contains value then return false
    seen := seen.insert value
  return true

private def schemaKey (schema : Schema) : UInt8 × Address × Nat × Nat :=
  (schema.world.toBits, schema.constructor.block, schema.constructor.indIdx, schema.constructor.cidx)

private def blockLayouts (layouts : Std.HashSet Address) (block : Block) : Bool :=
  block.creditParams.all fun
    | .required layout | .optional layout => layouts.contains layout

private def functionLayouts (layouts : Std.HashSet Address) (fn : Function) : Bool :=
  fn.blocks.all (blockLayouts layouts)

private def declarationBlocks (program : Program) : Std.HashMap Address Nat :=
  program.declarations.foldl (fun counts entry =>
    if counts.contains entry.1 then counts else
      counts.insert entry.1 (match entry.2 with | .fn fn => fn.blocks.size | .extern _ => 0)) {}

private def factCoordinates (mainBlocks : Nat) (declarations : Std.HashMap Address Nat)
    (fact : Validate.ScalarLeafFact) : Bool :=
  let blocks := match fact.owner with
    | .main => some mainBlocks
    | .declaration address => declarations.get? address
  blocks.any (fact.block < ·)

/-- Finite metadata coherence. Ordering is retained in identity; duplicate
lookup keys are rejected, including otherwise-unused schema/layout rows. -/
def Artifact.wellFormed (artifact : Artifact) : Bool := Id.run do
  if artifact.policy.semantics != semanticsVersion ||
      artifact.policy.validator != validatorVersion then return false
  if !uniqueKeys (artifact.dependencies.map (·.role)) ||
      artifact.dependencies.any (·.role.isEmpty) then return false
  if !uniqueKeys (artifact.layouts.map (·.identity)) ||
      !uniqueKeys (artifact.schemas.map schemaKey) then return false
  if !artifact.layouts.all (fun layout => Address.blake3 layout.preimage == layout.identity) then
    return false
  let layouts : Std.HashSet Address := artifact.layouts.foldl (fun found layout =>
    found.insert layout.identity) {}
  if !artifact.schemas.all (fun schema => layouts.contains schema.definition.layout) then
    return false
  let declarations := declarationBlocks artifact.program
  if !artifact.scalarLeaves.all (factCoordinates artifact.program.main.blocks.size declarations) then
    return false
  if !functionLayouts layouts artifact.program.main then return false
  return artifact.program.declarations.all fun
    | (_, .fn fn) => functionLayouts layouts fn
    | (_, .extern _) => true

structure Checked (limits : Validate.Limits) (artifact : Artifact) where
  sidecars : artifact.wellFormed = true
  stats : Validate.Stats
  accepted : Validate.validateWithPolicy artifact.policy.credits limits
    artifact.context artifact.program = .ok stats

/-- Validation budgets are supplied by the consumer, never taken from the
untrusted snapshot. Source/ABI certification remains a separate premise. -/
def Artifact.check (limits : Validate.Limits) (artifact : Artifact) :
    Except String (Checked limits artifact) := do
  if sidecars : artifact.wellFormed then
    match accepted : Validate.validateWithPolicy artifact.policy.credits limits
        artifact.context artifact.program with
    | .ok stats => return ⟨sidecars, stats, accepted⟩
    | .error error => throw s!"IxIR2 ownership validation: {repr error}"
  else throw "IxIR2 snapshot: unsupported semantics or inconsistent finite sidecars"

structure Addressed (limits : Bounded.Limits) (bytes : ByteArray) (root : Address) where
  artifact : Artifact
  decoded : Artifact.decodePreimage limits bytes = .ok artifact
  identity : artifact.address = root

def Artifact.decodeAddressed (limits : Bounded.Limits) (bytes : ByteArray) (root : Address) :
    Except String (Addressed limits bytes root) := do
  match decoded : Artifact.decodePreimage limits bytes with
  | .error message => throw message
  | .ok artifact =>
      if identity : artifact.address = root then return ⟨artifact, decoded, identity⟩
      else throw "IxIR2 snapshot: content root mismatch"

theorem Addressed.canonical {limits : Bounded.Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) : decoded.artifact.preimage = bytes :=
  Artifact.decodePreimage_canonical limits decoded.decoded

theorem Addressed.fits {limits : Bounded.Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) : decoded.artifact.Fits limits :=
  Artifact.decodePreimage_fits limits decoded.decoded

theorem Addressed.root_eq {limits : Bounded.Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) : Address.blake3 bytes = root := by
  rw [← decoded.canonical]
  exact decoded.identity

/-- Reuse by root equality needs the same explicit pairwise collision premise
as other addressed IRs; no global injectivity of a 256-bit digest is assumed. -/
theorem Addressed.matches {limits : Bounded.Limits} {bytes : ByteArray} {root : Address}
    (decoded : Addressed limits bytes root) (expected : Artifact)
    (fits : expected.Fits limits) (identity : expected.address = root)
    (collision : Address.Blake3NoCollision decoded.artifact.preimage expected.preimage) :
    decoded.artifact = expected :=
  Artifact.preimage_injective limits decoded.fits fits
    (collision (decoded.identity.trans identity.symm))

structure Ingress (limits : Bounded.Limits) (validationLimits : Validate.Limits)
    (bytes : ByteArray) (root : Address) extends Addressed limits bytes root where
  checked : Checked validationLimits artifact

def Artifact.ingest (limits : Bounded.Limits) (validationLimits : Validate.Limits)
    (bytes : ByteArray) (root : Address) :
    Except String (Ingress limits validationLimits bytes root) := do
  let addressed ← Artifact.decodeAddressed limits bytes root
  let checked ← addressed.artifact.check validationLimits
  return { toAddressed := addressed, checked }

/-- An accepted persisted root exposes the actual decoded program and finite
context to the original policy-indexed ownership checker. -/
theorem Ingress.validated {limits : Bounded.Limits} {validationLimits : Validate.Limits}
    {bytes : ByteArray} {root : Address} (ingress : Ingress limits validationLimits bytes root) :
    bytes = ingress.artifact.preimage ∧ Address.blake3 bytes = root ∧
      ingress.artifact.wellFormed = true ∧
      Validate.validateWithPolicy ingress.artifact.policy.credits validationLimits
        ingress.artifact.context ingress.artifact.program = .ok ingress.checked.stats :=
  ⟨ingress.toAddressed.canonical.symm, ingress.toAddressed.root_eq,
    ingress.checked.sidecars, ingress.checked.accepted⟩

end Compilatrix.IxIR2.Wire
