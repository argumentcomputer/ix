import Ix.Compile.SourceContract.Elab
open scoped Ix.Modes

/-!
OS34 `static-vs-unique` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS34StaticUnique`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

inductive Tree where
  | nil
  | node (l : Tree) (r : Tree)

def leafPair (u : Unit) : @unique Tree := .node .nil .nil

def keep (@unique t : Tree) : @unique Tree := t

def entry (u : Unit) : @unique Tree := keep (leafPair u)
