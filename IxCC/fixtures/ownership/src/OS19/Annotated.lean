import Ix.Compile.SourceContract.Elab

/-!
OS19 `unique-tree-node` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P28TreeUnique`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

inductive T where
  | leaf
  | node (l : T) (k : Nat) (r : T)

def swapT (! t : T) : ! T :=
  match t with
  | .leaf => .leaf
  | .node l k r => .node r k l
