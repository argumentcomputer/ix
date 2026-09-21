module
public import Ix.Aggr.Circuit
public import Ix.Aggr.FunctionGroups
public import Ix.Aggr.Host
public import Ix.Aggr.Protocol
public import MultiStark

/-!
# The `ixAggr` toplevel

`ixAggr` is the recursive aggregation system for IxVM proofs. It reuses the
Ix-agnostic Multi-STARK verifier modules (`MultiStark/…`, unmodified) and
adds the heterogeneous `ix_aggr` entrypoint from `Ix/Aggr/Circuit.lean` — one
circuit that wraps or joins any mix of IxVM and `ix_aggr` child proofs, with
the shape chosen by advice. There is no separate lift stage: an IxVM proof
enters the recursion system through a wrap or directly as a join child.

Host wire contracts live in `Ix/Aggr/Protocol.lean`; statement folds live in
`Ix/Aggr/Host.lean`.
-/

public section

namespace Aggr

/-- The full aggregation toplevel: every Multi-STARK verifier module (via
`MultiStark.verifierBase`, unmodified) plus the `ix_aggr` circuit —
unpruned. Only tests should build on this; production uses `ixAggr`. -/
def ixAggrFull : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← MultiStark.verifierBase
  t.merge circuit

/-- The production aggregation toplevel: `ixAggrFull` pruned to `ix_aggr`'s
call closure. Every compiled function is a committed circuit whose openings
pad every proof of the system's execution, so functions only reachable from
unrelated entries (`verify_multi_stark_proof`, kernel-oriented helpers of the
shared modules, test/bench entries) cost real proof bytes if kept. -/
def ixAggr : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← ixAggrFull
  pure (t.prune [`ix_aggr])


end Aggr

end
