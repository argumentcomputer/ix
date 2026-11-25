import Aiur.Library.U64.Hints
import Aiur.Library.U32.Goldilocks

/-! # Host advice for lowered programs

The lowered module reads two kinds of advice (`hint`): the `UInt64` library's
byte decompositions (channel `bytes_le`, `Aiur.Library.U64.hints`) and the
quotient and remainder of the division helper (`Lower.divmod`, channel
`ixcc.divmod`).

Advice is outside the program's meaning. In Formal Aiur's source semantics a
hint evaluates to any constant of its type (`Aiur.Generic.SourceSemantics`,
rule `hint`), and the lowered program checks what it is given: the division
helper asserts `q * y + r = x` and `r < y` on range-checked words
(`Gadgets.divmod_sound`). A wrong answer here loses a derivation; it cannot
make a wrong one.

`dispatcher` is the honest provider for the Lean evaluator
(`Aiur.Modules.Prepared.run`). The Rust host has the same channel
(`crates/aiur/src/library/ixcc.rs`). -/

namespace IxCC.AiurBackend.Hints

/-- The honest advice for a lowered program over a field whose elements are
read as naturals by `toNat`: `(x / y, x % y)` on `ixcc.divmod` (Lean's
conventions at `y = 0`: quotient `0`, remainder `x`), and the `UInt64`
library's own advice on every other channel. -/
def dispatcher {F : Type} [NatCast F] (toNat : F → Nat) : Aiur.HintDispatcher F :=
  fun channel key =>
    match channel, key with
    | "ixcc.divmod", .tuple [.field x, .field y] =>
      .ok (.tuple [.field ((toNat x / toNat y : Nat) : F), .field ((toNat x % toNat y : Nat) : F)])
    | "ixcc.divmod", _ => .error (.message "invalid divmod key")
    | _, _ => Aiur.Library.U64.hints toNat (fun _ _ => .error .unavailable) channel key

end IxCC.AiurBackend.Hints
