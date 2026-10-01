import Ix.Compile.SourceContract.Elab

/-!
OS05 `erased-index-match` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P26Vec`. Written for Compilatr.ix (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def vhead {0 α : Type} {0 n : Nat} : Vec α (n+1) → α
  | .cons a _ => a

def entry (n : Nat) : Nat := vhead (Vec.cons n (Vec.cons (n+1) Vec.nil))
