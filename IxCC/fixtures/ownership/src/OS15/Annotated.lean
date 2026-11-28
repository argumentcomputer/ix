import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS15 `unique-reverse-acc` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P04RevUniqueAcc`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def revAcc (xs : List Nat) (@unique acc : List Nat) : @unique List Nat :=
  match xs with
  | [] => acc
  | x :: rest => revAcc rest (x :: acc)
