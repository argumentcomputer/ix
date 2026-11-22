import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS35 `list-filter-fbip` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS35FilterOdd`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def filterOdd (@unique xs : List Nat) : @unique List Nat :=
  match xs with
  | [] => []
  | x :: rest => if x % 2 == 1 then x :: filterOdd rest else filterOdd rest
