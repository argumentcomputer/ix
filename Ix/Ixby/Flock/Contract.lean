module
public import Ix.Ixby.Claim

/-! Proof-free setup interfaces for the generic Flock execution backend.
There is no compiler implementation in this module. The dependent artifact
types fix its input boundary before native code is connected to it. -/

public section
@[expose] section

namespace Ix.Ixby.FlockBackend

open Commitment (Digest)

/-- Physical admission class, distinct from the reference semantic profile.
The circuit must constrain unused slots and exact halting within these bounds.
Changing this class is an explicit key upgrade, not an ordinary guest update. -/
structure Capacity where
  steps : Nat
  programBytes : Nat
  inputBytes : Nat
  outputBytes : Nat
  memoryCells : Nat
  frameCells : Nat
  deriving BEq, Repr

/-- Registered implementations of existing semantic operations. There is no
Stage 2 verifier/AIR/FRI opcode and no arbitrary host callback in this type. -/
structure PrimitiveRegistry where
  identity : Digest
  enabled : Array Primitive
  deriving BEq, Repr

/-- The complete compile input. In particular, no guest image, Stage 2 key,
proof, trace, or witness-dependent geometry can be supplied to compilation. -/
structure ExecSetupInput where
  profile : Profile
  capacity : Capacity
  primitives : PrimitiveRegistry
  flockProtocol : Digest
  backendImplementation : Digest
  deriving BEq, Repr

inductive SetupError where
  | profile (error : ProfileError)
  | revision
  | capacity
  | primitive
  | template
  | backend (message : String)
  deriving BEq, Repr, Inhabited

def ExecSetupInput.validate (request : ExecSetupInput) : Except SetupError Unit := do
  request.profile.validate |>.mapError .profile
  -- This is profile-indexed interface admission. Concrete native compilation
  -- additionally chooses the matching implementation and physical bit bounds.
  let c := request.capacity
  unless #[c.steps, c.programBytes, c.inputBytes, c.outputBytes, c.memoryCells, c.frameCells].all
      (fun n => 0 < n && n < 2 ^ 32) do throw .capacity
  unless request.profile.maxSteps ≤ c.steps && request.profile.programBytes ≤ c.programBytes &&
      request.profile.valueBytes ≤ c.inputBytes && request.profile.valueBytes ≤ c.outputBytes do
    throw .capacity
  unless request.primitives.enabled.all (fun op => (request.profile.primitiveOpcode op).isSome) do
    throw .primitive
  unless request.primitives.enabled.toList.Nodup do throw .primitive

/-- The only varying public F128 slots are the two 128-bit limbs of the full
Exec statement digest. Fixed words are owned by the compiled interpreter. -/
inductive PublicSlot where
  | fixed (low high : UInt64)
  | execDigestLow
  | execDigestHigh
  deriving BEq, DecidableEq, Repr, Inhabited

def validatePublicTemplate (slots : Array PublicSlot) : Except SetupError Unit := do
  unless (slots.filter (· == .execDigestLow)).size == 1 &&
      (slots.filter (· == .execDigestHigh)).size == 1 do throw .template

/-- A native implementation must instantiate this interface and prove its
constraint semantics. Computing metadata or a witness does not instantiate
`ExecSoundness`; no such implementation or theorem is supplied here. -/
structure ExecCompiler where
  Artifact : ExecSetupInput → Type
  compileExecProfile : (request : ExecSetupInput) → Except SetupError (Artifact request)
  circuitIdentity : {request : ExecSetupInput} → Artifact request → Digest
  publicTemplate : {request : ExecSetupInput} → Artifact request → Array PublicSlot

/-- Terminal compilation depends on the approved generic verifier artifact,
its fixed template, and terminal protocol/setup identities, never Stage 2.
The compiler is responsible for checking the artifact/template consistency. -/
structure TerminalSetupInput (compiler : ExecCompiler) (request : ExecSetupInput) where
  verifier : compiler.Artifact request
  fflonkProtocol : Digest
  srs : Digest
  terminalImplementation : Digest

structure TerminalCompiler (compiler : ExecCompiler) where
  Artifact : (request : ExecSetupInput) → TerminalSetupInput compiler request → Type
  compileTerminal : (request : ExecSetupInput) → (input : TerminalSetupInput compiler request) →
    Except SetupError (Artifact request input)

end Ix.Ixby.FlockBackend
