import Ix.Compile.SourceContract.Elab

/-!
OS37 `bytes-builder` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS37BytesBuilder`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def emit (! b : ByteArray) (n : Nat) : ! ByteArray :=
  match n with
  | 0 => b
  | k+1 => emit (b.push 0) k
