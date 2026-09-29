import Compilatrix.Ixon.V3.Tc.Driver

/-! Decoded and erased-typed v3 input, without resource admission. The
compiler front end (`Compilatrix.Src`) consumes this: v3 resource admission
is a census diagnostic, never a compile gate (design note 06 S40). The
existing `ValidatedInput` keeps its combined resource and typing contract. -/

namespace Compilatrix.Ixon.V3

/-- Strict anonymous decoding plus erased typing of exactly these bytes. -/
structure TypedInput (bytes : ByteArray) where
  env : Env
  decoded : decodeAnonymousEnv bytes = .ok env
  typingChecked : Tc.checkEnv env = .ok ()

/-- Decode and type-check; no resource profile is consulted. Literal types
are the kernel primitive identities by construction of the checker. -/
def validateTyped (bytes : ByteArray) : Except String (TypedInput bytes) :=
  match decoded : decodeAnonymousEnv bytes with
  | .error error => .error error
  | .ok env =>
    match typingChecked : Tc.checkEnv env with
    | .error error => .error error
    | .ok () => .ok { env, decoded, typingChecked }

theorem TypedInput.source_decoded {bytes : ByteArray} (input : TypedInput bytes) :
    decodeAnonymousEnv bytes = .ok input.env :=
  input.decoded

theorem TypedInput.typing_checked {bytes : ByteArray} (input : TypedInput bytes) :
    Tc.checkEnv input.env = .ok () :=
  input.typingChecked

end Compilatrix.Ixon.V3
