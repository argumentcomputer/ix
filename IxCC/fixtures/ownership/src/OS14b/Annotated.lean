import Ix.Compile.SourceContract.Elab

/-!
OS14b `unique-nat-plain-caller` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `OS14PlainCaller`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def pred (! n : Nat) : Nat :=
  match n with
  | 0 => 1
  | k+1 => k

def entry (n : Nat) : Nat := pred n
