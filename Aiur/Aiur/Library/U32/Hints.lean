import Aiur.Hints
import Aiur.Library.U32

namespace Aiur.Library.U32

/-- An optional provider for the semantic evaluator. `toNat` is the embedding
host's canonical integer decoder. A bad decoder/answer cannot bypass any of the
library's assertions or table checks. These are raw constants, never opaque
values. Other channels can be supplied by the caller's fallback dispatcher. -/
def hints {F : Type} [NatCast F] (toNat : F → Nat)
    (fallback : HintDispatcher F := fun _ _ => .error .unavailable) : HintDispatcher F :=
  fun channel key =>
    let bytes (n : Nat) : Constant F :=
      .tuple ((List.range 4).map fun i => .field (((n / 256^i) % 256 : Nat) : F))
    let word (value : Constant F) : Option Nat := do
      let .tuple [.field a, .field b, .field c, .field d] := value | none
      some (toNat a + 256*toNat b + 65536*toNat c + 16777216*toNat d)
    let sum (values : List (Constant F)) : Except HintError (Constant F) := do
      let some words := values.mapM word | throw (.message "invalid u32 sum key")
      return bytes words.sum
    match channel, key with
    | "u32.bytes", .field value => .ok (bytes (toNat value))
    | "u32.sub", .tuple [.field a, .field b] =>
        .ok (bytes (toNat a % base + base - toNat b % base))
    | "u32.add", .tuple [a, b] => sum [a, b]
    | "u32.add3", .tuple [a, b, c] => sum [a, b, c]
    | "u32.lt", .tuple [.field a, .field b] =>
        .ok (.tuple [bytes (toNat a),
          bytes (toNat a % base + base - toNat b % base), bytes (toNat b)])
    | "u32.bytes", _ | "u32.sub", _ | "u32.add", _ | "u32.add3", _
    | "u32.lt", _ => .error (.message "invalid u32 hint key")
    | _, _ => fallback channel key

end Aiur.Library.U32
