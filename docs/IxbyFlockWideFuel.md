# Checked 64-bit global fuel component

`flock-stage3/host/src/ixby/wide_fuel` supplies a separate Boolean-R1CS ledger
for future segmented execution. The old u32 control state, IXBP encoding,
native Exec factories, and their setup identities remain unchanged. This
component does not admit a larger native Exec profile or prove an IXBF run.

## Relation and wiring

One F128 word packs exact u64 `remaining` and `consumed` integers in its low
and high lanes. The budget input has a u64 low lane and a zero high lane.
The component checks, without modular overflow:

```text
remaining + consumed = original budget
active step: next = (remaining - 1, consumed + 1)
halted padding: next = (remaining, consumed)
```

Active exhaustion, arithmetic carry/borrow, a changed total budget, and invalid
control kinds reject. The full low 32 bits of the control metadata encode
0 = evaluate, 1 = return, 2 = halted, or 3 = apply. Return consumes fuel,
including the terminal return; only already-halted padding is free.

The other 96 control-metadata bits belong to the separate control constraints.
The ledger does not validate kind transitions, instructions, frames, values,
heap access, or termination. In particular, its kind input must eventually
come from the actual pre-step machine-state wire, and its budget from the
admitted program. Host-selected kinds are not execution evidence.

`Fuel64StepSlot` always wires the residual to a verifier-owned zero. The
count-only pass remains lazy and agrees with actual emission. All output bits,
unused columns/rows, and count-aware constant stripes are constrained; the
in-place witness driver fully overwrites recycled padding.

## Evidence

Five ordinary tests check budgets through `u64::MAX`, crossing `2^32`, exact
exhaustion/padding, every output bit, high metadata bits, locally recomputed
invalid advice, count/emit agreement, and poisoned witness buffers.

The opt-in real Flock test uses one fixed six-step ledger setup. Its three
cases cross the u32 boundary, start at the measured Init transition count,
and consume the final unit of a `u64::MAX` budget. All verify in fresh
environment-cleared processes receiving only four expected public words and
the proof. The verifier does not evaluate a ledger trace or read guest data.

Each complete component bundle is **107,739 bytes** under the strict
`IXFUEL00` envelope and `ix:ixby:wide-fuel-conformance:v0` transcript domain.
These are not `IXBYEX00` Exec proofs. Modified expected budget/counter limbs,
proof/domain mutations, truncation, and trailing data reject. A substituted
middle row preserved its local budget equation and recomputed every derived
value, but fresh verification rejected the global wiring with
`Wiring(Gkr(ProductMismatch))`.

The local conformance run passed with four Rayon workers, a 32 GiB virtual-
address cap and a 600-second timeout. Observed GNU-time totals were 0.18 seconds
wall and 40,804 KiB maximum RSS. These tiny-component regression measurements
are not full guest/prover estimates or aggregate parent-plus-child memory.
No Flock pin, PCS geometry range, SRS, or existing resource budget was raised.

```sh
cargo test --release --locked --manifest-path flock-stage3/Cargo.toml \
  --workspace wide_fuel -- --test-threads=1
RAYON_NUM_THREADS=4 cargo test --release --locked \
  --manifest-path flock-stage3/Cargo.toml --workspace \
  ixby::wide_fuel::proof_tests:: -- --ignored --test-threads=1 --nocapture
```

[Constrained functional header tests](IxbyFunctionalCodec.md) now wire the
decoded original `maxSteps` directly into this ledger and reject a replacement
budget or a decoded budget wider than u64. Their control kinds are still
component inputs, not authenticated machine states.

Full-state boundary authentication, global segment composition, wider profile
encoding, and native constraint-to-reference refinement are still required.
See the [scaling plan](IxbyStage3ScalePlan.md).
