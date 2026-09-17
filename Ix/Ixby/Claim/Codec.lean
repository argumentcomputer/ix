module
public import Ix.Ixby.Claim.Basic

/-! Fixed-width, domain/version-separated experimental statement transport.
Decoding commits to exact re-encoding, not to the truth of an execution. -/

public section
@[expose] section

namespace Ix.Ixby.Claim

open Commitment (Digest Statement)
open Codec (Bytes)

abbrev execWireBytes : Nat := 140
abbrev publicWireBytes : Nat := 108

namespace Internal

def readDigest : Codec.Internal.Decoder Digest := do
  let bytes ← Codec.Internal.readBytes 32
  if size : bytes.size = 32 then return ⟨bytes, size⟩
  else throw .truncated

end Internal

def encodeExec (statement : Statement) : Except Codec.Error Bytes :=
  Codec.Internal.encode execWireBytes 0 do
    Codec.Internal.writeHeader "IXBE"
    for digest in #[statement.profile, statement.program, statement.input, statement.output] do
      Codec.Internal.writeBytes digest.bytes

def decodeExec (bytes : Bytes) : Except Codec.Error (Codec.Decoded encodeExec bytes) := do
  let statement ← Codec.Internal.decode execWireBytes 0 bytes do
    Codec.Internal.readHeader "IXBE"
    return Statement.mk (← Internal.readDigest) (← Internal.readDigest)
      (← Internal.readDigest) (← Internal.readDigest)
  Codec.Internal.canonicalize encodeExec bytes statement

def encodePublic (statement : PublicStatement) : Except Codec.Error Bytes :=
  Codec.Internal.encode publicWireBytes 0 do
    Codec.Internal.writeHeader "IXBR"
    for digest in #[statement.profile, statement.program, statement.output] do
      Codec.Internal.writeBytes digest.bytes

def decodePublic (bytes : Bytes) : Except Codec.Error (Codec.Decoded encodePublic bytes) := do
  let statement ← Codec.Internal.decode publicWireBytes 0 bytes do
    Codec.Internal.readHeader "IXBR"
    return PublicStatement.mk (← Internal.readDigest) (← Internal.readDigest) (← Internal.readDigest)
  Codec.Internal.canonicalize encodePublic bytes statement

end Ix.Ixby.Claim
