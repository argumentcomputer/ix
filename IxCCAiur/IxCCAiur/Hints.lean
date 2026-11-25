import Aiur.Library.U32.Hints
import Aiur.Library.U64.Hints
import Aiur.Library.U32.Goldilocks

/-! # Host advice for lowered programs

The lowered module reads host advice (`hint`) on:
* `bytes_le` (`Aiur.Library.U64.hints`),
* `u32.{bytes,sub,add,add3,lt}` (`Aiur.Library.U32.hints`),
* `ixcc.divmod` (quotient and remainder for division helpers).

Advice is outside the program's meaning. In Formal Aiur's source semantics a
hint evaluates to any constant of its type (`Aiur.Generic.SourceSemantics`,
rule `hint`), and the lowered program checks what it is given. A wrong answer
here loses a derivation; it cannot make a wrong one.

`dispatcher` is the honest provider for the Lean evaluator
(`Aiur.Modules.Prepared.run`). The Rust host registers the same channels
(`crates/aiur/src/library/{u32,u64,ixcc}.rs`). -/

namespace IxCC.AiurBackend.Hints

/-- The honest advice for a lowered program over a field whose elements are
read as naturals by `toNat`: `(x / y, x % y)` on `ixcc.divmod` (Lean's
conventions at `y = 0`: quotient `0`, remainder `x`), plus `UInt64` and `UInt32`
library advice on every other channel. -/
def dispatcher {F : Type} [NatCast F] (toNat : F → Nat) : Aiur.HintDispatcher F :=
  fun channel key =>
    match channel, key with
    | "ixcc.divmod", .tuple [.field x, .field y] =>
      .ok (.tuple [.field ((toNat x / toNat y : Nat) : F), .field ((toNat x % toNat y : Nat) : F)])
    | "ixcc.divmod", _ => .error (.message "invalid divmod key")
    | _, _ =>
      Aiur.Library.U64.hints toNat
        (Aiur.Library.U32.hints toNat (fun _ _ => .error .unavailable)) channel key

end IxCC.AiurBackend.Hints
