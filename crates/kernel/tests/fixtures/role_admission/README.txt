basis.ixe: the closure of the Nat, Bool, Eq, PUnit, Empty, False, Quot and And
blocks and of the structural Nat operations (Nat.pred, Nat.add, Nat.sub,
Nat.mul, Nat.pow, Nat.beq, Nat.ble), extracted with `ix shard extract` from
the bound Init+Std artifact
(sha256 cb961f7219438620505a785e8942a6604b18e871dd00dc0ac15766234153117c)
and written back without the artifact's role binding. It carries the
compiler's records and names (without metadata, so only anonymous checks
apply); tests bind roles themselves.
