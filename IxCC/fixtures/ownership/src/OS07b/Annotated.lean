import Ix.Compile.SourceContract.Elab

/-!
OS07b `erased-proof-wf` of the ownership suite (`fixtures/ownership/README.md`, MT.7),
from probe `P33CountdownWF`. Written for IxCC (Apache-2.0 OR MIT). The
pinned ix rejects it; its verdict is recorded in `fixtures/ownership/verdicts.json`.
-/

def countdownWF (n : Nat) (0 h : 0 ≤ n) : Nat :=
  if hn : n = 0 then 0 else countdownWF (n - 1) (Nat.zero_le _) + 1
termination_by n
decreasing_by omega

def entry (n : Nat) : Nat := countdownWF n (Nat.zero_le n)
