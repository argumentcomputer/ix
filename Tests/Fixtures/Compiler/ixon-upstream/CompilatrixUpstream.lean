module

public import Std

namespace CompilatrixUpstream

public def twice (function : Nat → Nat) (value : Nat) : Nat :=
  function (function value)

public def applyClosed : Nat :=
  twice (fun value => Nat.succ value) (Nat.succ Nat.zero)

public def captureClosed : Nat :=
  let seed := Nat.succ (Nat.succ Nat.zero)
  twice (fun _ => seed) Nat.zero

public def letClosed : Nat :=
  let step := fun value : Nat => Nat.succ value
  twice step (Nat.succ (Nat.succ Nat.zero))

public def addClosed : Nat :=
  Nat.add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)

public def recClosed : Nat :=
  Nat.rec (motive := fun _ => Nat) Nat.zero
    (fun _ result => Nat.succ result)
    (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

end CompilatrixUpstream
