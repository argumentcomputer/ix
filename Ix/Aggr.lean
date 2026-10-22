module
public import Ix.Aggr.FFI
public import Ix.Aggr.Circuit
public import Ix.Aggr.FunctionGroups
public import Ix.Aggr.Host
public import Ix.Aggr.Protocol
public import LegacyMultiStark

/-!
# The `ixAggr` toplevel

`ixAggr` is the recursive aggregation system for LegacyIxVM proofs. It reuses the
Ix-agnostic Multi-STARK verifier modules (`LegacyMultiStark/…`, unmodified) and
adds the heterogeneous `ix_aggr` entrypoint from `Ix/Aggr/Circuit.lean` — one
circuit that wraps or joins any mix of LegacyIxVM and `ix_aggr` child proofs, with
the shape chosen by advice. There is no separate lift stage: an LegacyIxVM proof
enters the recursion system through a wrap or directly as a join child.

Host wire contracts live in `Ix/Aggr/Protocol.lean`; statement folds live in
`Ix/Aggr/Host.lean`.
-/

public section

namespace Aggr

/-- The full aggregation toplevel: every Multi-STARK verifier module (via
`LegacyMultiStark.verifierBase`, unmodified) plus the `ix_aggr` circuit —
unpruned. Only tests should build on this; production uses `ixAggr`. -/
def ixAggrFull : Except LegacyAiur.Global LegacyAiur.Source.Toplevel := do
  let t ← LegacyMultiStark.verifierBase
  t.merge circuit

/-- The production aggregation toplevel: `ixAggrFull` pruned to `ix_aggr`'s
call closure. Every compiled function is a committed circuit whose openings
pad every proof of the system's execution, so functions only reachable from
unrelated entries (`verify_multi_stark_proof`, kernel-oriented helpers of the
shared modules, test/bench entries) cost real proof bytes if kept. -/
def ixAggr : Except LegacyAiur.Global LegacyAiur.Source.Toplevel := do
  let t ← ixAggrFull
  pure (t.prune [`ix_aggr])


end Aggr

end
