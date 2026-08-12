import Blake3.Rust
import Navigatrix.Ixon.Address
import Navigatrix.Ixon.Const

/-!
# Content addressing

blake3 over canonical Ixon serializations. The hash itself is FFI
(Rust blake3 via Blake3.lean) — a **trusted-extern ledger** entry per
`plans/runtime.md`: assumed semantics is the BLAKE3 function; the
endgame replacement is a verified Lean implementation compiled by our
own backend.

NB: no `#guard`/`#eval` here — executing the FFI at elaboration needs
the Blake3 shared lib loaded in the interpreter (`--load-dynlib`),
which the nix-built dependency artifact doesn't provide. Execution
tests live in the compiled `tests` executable (`Tests.lean`), run as a
flake check.
-/

namespace Navigatrix.Ixon

/-- blake3 of arbitrary bytes as an `Address`. -/
def Address.blake3 (x : ByteArray) : Address :=
  ⟨(Blake3.Rust.hash x).val⟩

/-- The content address of a constant: blake3 of its canonical
serialization. Canonicity of the codec (strict decoding, one spelling
per value) is what makes this a value identity. -/
def Constant.address (c : Constant) : Address :=
  .blake3 (ser c)

/-- Address of a bare expression (used for cache keys, not constants). -/
def Expr.address (e : Expr) : Address :=
  .blake3 (runPut (putExpr e))

end Navigatrix.Ixon
