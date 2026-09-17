# IxBy / Flock native workspace

This independent Cargo workspace implements the current paged IxBy backend:
original-byte admission, authenticated code and memory, execution, output
serialization, commitments, and Flock leaf proofs. It uses **format 1,
semantics 2** for IXBF, IXFI, and IXFO. The old fixed-arena IXBY/IXBP backend
and its public factories have been removed.

## Current contract

- [Runtime and compiler handoff](../docs/CompilatrixRuntimeV2Handoff.md): unboxed
  numeric values, field/Nat conversions, persistent arrays, immutable byte
  builders, zero-copy slices, and physical limits.
- [Canonical encoding](../docs/IxbyEncoding.md): all headers, values, and 58 opcodes.
- [Functional intake](../docs/IxbyFunctionalIntake.md): strict host-side reading
  and pinned retained Init regression fixtures.
- [Paged admission](../docs/IxbyFlockPagedAdmission.md) and
  [execution](../docs/IxbyFlockPagedExecution.md): constrained original-byte path.
- [Stage 4](../flock-stage4/README.md): one recursive proof of the complete
  execution statement.
- [Batch tuning](../docs/IxbyBatchTuning.md): exact quota/padding census,
  workload-specific classes, and the 4K fetch prototype.

The reference model supports more than every physical proving class. The
current complete proof uses Nat128 and a Bytes terminal result; it has finite
frame, stack, input-span, and address limits. String primitive execution and
general native-circuit refinement to Lean remain open. The compiler owner
must integrate and certify the new representations before measuring CSLib.

## Build and checks

```sh
cargo check --locked --workspace --all-targets
cargo clippy --locked --workspace --all-targets -- -D warnings
cargo test --release --locked -p ixby-flock ixbf -- --test-threads=1
cargo test --release --locked -p ixby-flock collection_tests -- --test-threads=1
cargo test --release --locked -p ixby-flock paged_primitive -- --test-threads=1
```

Run from this directory. The workspace is excluded from the root Cargo build.
It has no dependency on the native Stage 2 verifier. `num-bigint` preserves
unbounded functional metadata during host intake; constrained capacities are
selected separately. Native integer execution generates advice, while circuit
relations independently check that advice.

Historical implementation details and measurements are preserved in the
[revision-1 workspace report](https://github.com/argumentcomputer/ix/blob/d4405b3ceb82e6d4cce19e48186f3272f8482e04/flock-stage3/README.md).
Those setup identities and measurements do not transfer to revision 2.
