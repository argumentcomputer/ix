import Ix.Compile.SourceContract.Elab

/-!
OS01b `erased-proof-prop` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
a proof argument of a proposition that mentions another argument. Written for
Compilatr.ix (Apache-2.0 OR MIT). The pinned ix rejects it; its verdict is
recorded in `fixtures/ownership/verdicts.json`.
-/

def predPos (n : Nat) (0 _h : n > 0) : Nat := n - 1

def entry (n : Nat) : Nat := predPos (n + 1) (Nat.succ_pos n)
