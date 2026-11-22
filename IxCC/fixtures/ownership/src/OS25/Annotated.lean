import Ix.Compile.SourceContract.Elab

/-!
OS25 `local-match` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P10LocalMatch`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def nonEmpty (~ xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | _ :: _ => 1
