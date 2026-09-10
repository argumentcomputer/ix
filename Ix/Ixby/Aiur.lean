module
public import Ix.Ixby.Aiur.Objects
public import Ix.Aiur.Protocol
public import Ix.Aiur.Compiler

/-! Experimental host interface to the fixed-profile IxBy Aiur interpreters. Kept
separate from `Ix.Ixby` so the logical specification does not import an FFI
proof oracle. This is not a production proof/claim format or source bridge. -/

public section

namespace Ix.Ixby.AiurBackend

/-- Eight little-endian 32-bit limbs per digest. Each limb embeds injectively
in Goldilocks; packing an arbitrary eight-byte chunk would not. -/
def digestFields (digest : Commitment.Digest) : Array Aiur.G :=
  (Array.range 8).map fun i =>
    .ofNat (natOfBytesLE (digest.bytes.extract (i * 4) (i * 4 + 4)))

def statementFields (statement : Commitment.Statement) : Array Aiur.G :=
  digestFields statement.profile ++ digestFields statement.program ++
    digestFields statement.input ++ digestFields statement.output

/-- Raw advice intentionally performs no host admission: the circuit must
establish bounds, canonical decoding, execution, and commitment binding. -/
def artifactAdvice (programBytes inputBytes : Codec.Bytes) : Aiur.IOBuffer :=
  (default : Aiur.IOBuffer).extend 0 #[0] (programBytes.map Aiur.G.ofUInt8)
    |>.extend 1 #[0] (inputBytes.map Aiur.G.ofUInt8)

structure ScalarSystem where
  compiled : Aiur.CompiledToplevel
  system : Aiur.AiurSystem
  entry : Aiur.Bytecode.FunIdx

/-- Shared adapter for the experimental interpreter entrypoints. -/
private def buildSystem (source : Aiur.Source.Toplevel) (entryName : Lean.Name)
    (commitment : Aiur.CommitmentParameters) (fri : Aiur.FriParameters) :
    Except String ScalarSystem := do
  let compiled ← source.compile
  let some entry := compiled.getFuncIdx entryName
    | throw s!"missing IxBy entrypoint {entryName}"
  return ⟨compiled, Aiur.AiurSystem.build compiled.bytecode commitment fri, entry⟩

/-- Explicit backend parameters: callers choose a test or reviewed security
policy. The same compiled system is reused for different guest programs. -/
def ScalarSystem.build (commitment : Aiur.CommitmentParameters)
    (fri : Aiur.FriParameters) : Except String ScalarSystem := do
  buildSystem (← scalarToplevel) `ixby_scalar_exec commitment fri

/-- The control slice has its own fixed profile and key; guest function/block
tables and dynamic call stacks do not participate in compiling that key. -/
def ScalarSystem.buildControl (commitment : Aiur.CommitmentParameters)
    (fri : Aiur.FriParameters) : Except String ScalarSystem := do
  buildSystem (← controlToplevel) `ixby_control_exec commitment fri

/-- Structured values have a separate fixed profile/key. Physical object
pointers, ranks, and constructor tables are not public/advice inputs. -/
def ScalarSystem.buildObjects (commitment : Aiur.CommitmentParameters)
    (fri : Aiur.FriParameters) : Except String ScalarSystem := do
  buildSystem (← objectsToplevel) `ixby_objects_exec commitment fri

def ScalarSystem.claim (backend : ScalarSystem) (expected : Commitment.Statement) : Array Aiur.G :=
  Aiur.buildClaim backend.entry (statementFields expected) #[]

def ScalarSystem.execute (backend : ScalarSystem) (expected : Commitment.Statement)
    (programBytes inputBytes : Codec.Bytes) :
    Except String (Array Aiur.G × Aiur.IOBuffer × Array Aiur.QueryCount) :=
  backend.compiled.bytecode.execute backend.entry (statementFields expected)
    (artifactAdvice programBytes inputBytes)

def ScalarSystem.prove (backend : ScalarSystem) (expected : Commitment.Statement)
    (programBytes inputBytes : Codec.Bytes) : Except String Aiur.Proof := do
  -- The current native prove FFI can abort on execution failure. Preflight
  -- turns malformed advice into an ordinary error; it does not replace any
  -- circuit check, and verification still needs neither advice nor execution.
  let _ ← backend.execute expected programBytes inputBytes
  let (claim, proof, _) ← backend.system.prove backend.entry (statementFields expected)
    (artifactAdvice programBytes inputBytes)
  unless claim == backend.claim expected do throw "IxBy prover returned an unexpected claim"
  return proof

/-- Verifies the caller's expected statement, never an unchecked statement
returned by a prover. Does not need artifact bytes or rerun the evaluator. -/
def ScalarSystem.verify (backend : ScalarSystem) (expected : Commitment.Statement)
    (proof : Aiur.Proof) : Except String Unit :=
  backend.system.verify (backend.claim expected) proof

/-- Checked untrusted proof decoding; this is only native Aiur serialization,
not a new IxBy artifact envelope or production deployment policy. The existing
native decoder permits trailing bytes; exact canonical reserialization rejects
them here. The size cap is local transport policy, not part of Exec semantics. -/
def ScalarSystem.verifyBytes (backend : ScalarSystem) (expected : Commitment.Statement)
    (bytes : ByteArray) : Except String Unit := do
  if bytes.size > 64 * 1024 * 1024 then throw "IxBy experimental proof byte limit"
  let proof ← Aiur.Proof.ofBytesChecked bytes
  unless proof.toBytes == bytes do throw "IxBy noncanonical or trailing proof bytes"
  backend.verify expected proof

end Ix.Ixby.AiurBackend
