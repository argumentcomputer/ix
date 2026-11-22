import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS17 `unique-push` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P05Push`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def push (@unique acc : List Nat) (x : Nat) : @unique List Nat := x :: acc
