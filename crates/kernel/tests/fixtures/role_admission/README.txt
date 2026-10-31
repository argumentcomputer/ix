basis.ixe: the closure of the Nat, Bool, Eq, PUnit, Empty, False, Quot, And,
True, Iff and Nonempty blocks, of propext, Classical.choice and sorryAx, and of
the structural Nat operations (Nat.pred, Nat.add, Nat.sub, Nat.mul, Nat.pow,
Nat.beq, Nat.ble), extracted with `ix shard extract` from the bound Init+Std
artifact
(sha256 0d21dc6d906a86646deea50629d3367c2ab356dcd9a760c08fcf774ea389efd1)
and written back without the artifact's role binding. It carries the
compiler's records and names (without metadata, so only anonymous checks
apply); tests bind roles themselves.
