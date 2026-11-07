import Ix.Compile.SourceContract.Elab

/-!
OS35 `list-filter-fbip` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS35FilterOdd`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def filterOdd (! xs : List Nat) : ! List Nat :=
  match xs with
  | [] => []
  | x :: rest => if x % 2 == 1 then x :: filterOdd rest else filterOdd rest
