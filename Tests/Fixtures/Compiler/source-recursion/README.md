The reviewed `expected.json` matrix pins D1's eight canonical synthetic Ixon
list-reversal cases, their checked HPT identities, and 25 rejection/fallback
checks. Each input is compiled
from source constants through the existing validator before optional checked
recursion recovery, ownership lowering, CFG lowering, and dynamic reuse.
No fixture supplies intermediate IR.

Generate full snapshots with `lake exe source-recursion /tmp/new-recursion`.
Run `lake exe check-source-recursion --fixture .lake/build/bin/source-recursion`
to compare two fresh compiler processes against the reviewed matrix and each
other. The report plus eight snapshots form the exact nine-file inventory.

The full snapshots retain canonical source/IR bytes, addressing graphs and
preimages, common lowering certificate checks, HPT candidates and canonical
cache records, full finite sidecars, configuration, selected CFGs and schemas,
and every observed and reclaimed heap. Case snapshots use format version 2;
the recovery policy and report format retain version 1. IxIR₂ JSON is diagnostic
and has no persistent codec identity.
The checker independently counts live terminal nodes and checks
`live + frees = allocs` before inspecting the fully reclaimed heap.
It also checks `baseline.allocs = selected.allocs + selected.reuses` and the
corresponding free equation for the actual physical outputs, at halt and
after release. At both phases, selected RC operations and peak live nodes
must not exceed the physical baseline.
The [focused documentation](../../docs/source-recursion.md) records the
composed source-to-selected-physical cost theorem and its shared-result domain,
including intermediate execution states. Exact counters and the separate
literal-to-recovered savings remain finite measurements.

Refresh this matrix only after reviewing the fixture or compiler-policy
change that explains the drift. The checker never rewrites expectations.
