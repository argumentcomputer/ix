module
public import Ix.Ixby.Codec

/-! Domain-separated bindings for the experimental IxBy byte-execution
statement. Computing/checking these commitments is host/reference work, NOT
a STARK verifier. Hash binding relies on BLAKE3's cryptographic assumptions;
there is no axiom asserting that a finite hash is mathematically injective. -/

public section
@[expose] section

namespace Ix.Ixby.Commitment

structure Digest where
  bytes : Codec.Bytes
  size_eq : bytes.size = 32
  deriving BEq, DecidableEq, Repr

inductive Domain where
  | profile | program | input | output | statement
  deriving BEq, DecidableEq, Repr, Inhabited

def Domain.tag : Domain → UInt8
  | .profile => 0
  | .program => 1
  | .input => 2
  | .output => 3
  | .statement => 4

/-- Fixed ASCII prefix, NUL, one domain byte, then the complete payload.
No arbitrary string labels or ambiguous concatenations of variable fields. -/
def hash (domain : Domain) (payload : Codec.Bytes) : Digest :=
  let bytes := "IxBy/commit/v0".toUTF8.data ++ #[0, domain.tag] ++ payload
  ⟨Blake3.hash bytes, Blake3.hash_size bytes⟩

structure Statement where
  profile : Digest
  program : Digest
  input : Digest
  output : Digest
  deriving BEq, DecidableEq, Repr

/-- A compact digest of all four fixed-width statement components. -/
def Statement.digest (statement : Statement) : Digest :=
  hash .statement (statement.profile.bytes ++ statement.program.bytes ++
    statement.input.bytes ++ statement.output.bytes)

namespace Internal

/-- Low-level binding only. Public artifact/execute boundaries below establish
admission; hashing a payload alone does not validate its encoding or meaning. -/
def bind (profileBytes programBytes inputBytes outputBytes : Codec.Bytes) : Statement :=
  let profile := hash .profile profileBytes
  let program := hash .program (profile.bytes ++ programBytes)
  let input := hash .input (program.bytes ++ inputBytes)
  let output := hash .output (program.bytes ++ outputBytes)
  { profile := profile, program, input, output }

end Internal

/-- Build a statement for admitted canonical artifacts. This does NOT assert
that the supplied output is the result of executing the supplied program. -/
def ofArtifacts (profile : Profile) (programBytes inputBytes outputBytes : Codec.Bytes) :
    Except Codec.Error Statement := do
  let profileBytes ← Codec.encodeProfile profile
  let program ← Codec.decodeProgram profile programBytes
  let _ ← Codec.decodeInput profile program.value inputBytes
  let _ ← Codec.decodeOutput profile program.value outputBytes
  return Internal.bind profileBytes programBytes inputBytes outputBytes

/-- Reuse the canonicality/execution evidence already carried by a reference
run instead of reparsing its artifacts just to compute their commitments. -/
def ofExecution {profile : Profile} {programBytes inputBytes : Codec.Bytes}
    (execution : Codec.Execution profile programBytes inputBytes) : Except Codec.Error Statement := do
  let profileBytes ← Codec.encodeProfile profile
  return Internal.bind profileBytes programBytes inputBytes execution.outputBytes

inductive Error where
  | codec (error : Codec.Error)
  | mismatch (domain : Domain)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Reference checking of an expected commitment statement. It runs the
machine; this is not succinct verification and does not authorize the program
as an application verifier or establish any Ixon/source correspondence. -/
def executeAndCheck (profile : Profile) (programBytes inputBytes : Codec.Bytes) (fuel : Nat)
    (expected : Statement) : Except Error (Codec.Execution profile programBytes inputBytes) := do
  let execution ← Codec.execute profile programBytes inputBytes fuel |>.mapError .codec
  let actual ← ofExecution execution |>.mapError .codec
  unless actual.profile == expected.profile do throw (.mismatch .profile)
  unless actual.program == expected.program do throw (.mismatch .program)
  unless actual.input == expected.input do throw (.mismatch .input)
  unless actual.output == expected.output do throw (.mismatch .output)
  return execution

end Ix.Ixby.Commitment
