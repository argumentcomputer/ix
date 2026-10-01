import Ix.Compile.SourceContract.Elab

/-!
OS26 `borrow-match` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P11BorrowMatch`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def viaBorrow (xs : List Nat) : Nat :=
  let borrow (~ v : List Nat) := xs
  match v with
  | [] => 0
  | _ :: _ => 1
