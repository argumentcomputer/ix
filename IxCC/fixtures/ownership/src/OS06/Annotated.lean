import Ix.Compile.SourceContract.Elab

/-!
OS06 `erased-proof-uses` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P39ErasedAbsurd`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def absurdUse (xs : List Nat) (0 h : xs ≠ []) : Nat :=
  match xs with
  | x :: _ => x
  | [] => absurd rfl h
