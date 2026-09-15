module
public import Ix.MultiStark.Verify.Codec.Wire

/-! Current length-prefixed native statement transport. These are the native
field-word claims; public Ixon claims use their separate canonical adapter. -/

public section
@[expose] section

namespace MultiStark.Verify.Codec

def encodeClaims (limits : DecodeLimits) (claims : Array (Array Field)) : Except DecodeError Bytes :=
  Wire.encode limits (Wire.writeVector (Wire.writeVector Wire.writeField) claims)

def decodeClaims (limits : DecodeLimits) (bytes : Bytes) :
    Except DecodeError (Canonical (encodeClaims limits) bytes) := do
  let claims ← Wire.decode limits bytes (Wire.readVector (Wire.readVector Wire.readField))
  Wire.canonicalize (encodeClaims limits) bytes claims

end MultiStark.Verify.Codec
