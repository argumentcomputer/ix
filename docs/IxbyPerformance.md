# IxBy performance priorities

The completed CSLib reference run executes **2,268,502,805 logical
transitions**. Eleven compiler-runtime helpers account for **56.0%** of them.
Changing the work expressed by the program is therefore a substantial
opportunity alongside optimizing its proving circuit.

The [function cost record](../flock-stage3/profile/cslib-runtime-costs-v0.json)
joins all 6,763 observed block counts to the compiler's 681-function inventory.
It checks the complete observation against the pinned reference census and
checks the program hash against both the census and compiler inventory.
Counts are exclusive: a call instruction belongs to its caller, and the
callee's instructions belong to the callee. Return-control and apply-control
transitions are included in the denominator but have no function attribution.

| Runtime work | Functions | Reference transitions | Share of the complete run |
| --- | --- | ---: | ---: |
| Persistent array navigation | `treeGet`, `treeSet` | 479,966,998 | 21.2% |
| Byte rope management | `byteAppend`, `byteHeight`, `byteNode`, `byteBalance` | 328,622,405 | 14.5% |
| Four-bit numeric conversions | `toWord`, `fromWordLoop`, `nibbleWord`, `nibbleNat` | 240,523,261 | 10.6% |
| Extracting a numeric value from its wrapper | `natural` | 220,428,864 | 9.7% |

These counts identify opportunities. They are not measured speedups or counts
of instructions that an implementation can remove without replacement.

## First: direct conversions and simpler numeric representations

IxBy already has distinct Nat, Word32 and field scalars. The compiler runtime
also uses constructor wrappers containing a Nat and its cached low Word32,
or a raw Nat, or a field value. `natural` selects a representation and extracts
its mathematical value. Its entry block executes 110,214,432 times.

The runtime currently implements some conversions by consuming four bits at
a time and using a balanced comparison tree to cross scalar representations.
The four conversion helpers in the table execute 240.5 million transitions.
This is a good first target because the replacement operations have small,
precise specifications:

- Nat to Word32: the low 32 bits, explicitly modulo `2^32`.
- Word32 to Nat: the exact nonnegative integer value.
- Field to Nat, where needed: the canonical representative.

Add the logical primitives, canonical encoding, reference semantics and
constrained implementations together. Then update the compiler's numeric
runtime and its representation certificates. Boundary cases must include
zero, `2^32 - 1`, `2^32`, and larger Nats; the reference run observes 65-bit
Nats, so a blanket replacement of Nat with Word32 would change this workload.

A later representation change can keep typed scalars through arithmetic and
reserve wrappers for boundaries that need them. That can also reduce
constructor allocation, case dispatch and memory traffic. Its benefit needs
a new compiled-image trace.

## Next: native persistent array operations

`treeGet` alone executes 335 million transitions. Each tree level runs generic
comparisons, branches, division by two, projections and tail calls. `treeSet`
adds another 145 million transitions while rebuilding persistent paths.

Give indexed reads and persistent updates explicit operations and constrained
path traversal. Bounds checks and the correspondence between the path, index
and returned value remain proof obligations. Updates should retain structural
sharing so their implementation does not copy an entire array on each write.
This targets both interpreter overhead and the number of state/memory records
that reach the proving circuit.

## Native byte builders and slices

The current rope representation saves copying but expresses height checks,
node construction and balancing as interpreted functions. Those four helpers
account for 329 million transitions.

An explicit byte builder or persistent byte-sequence operations can perform
that management in constrained operations. Preserve sharing, checked ranges,
the exact output bytes and BLAKE3 behavior. Appending should not repeatedly
materialize the whole accumulated prefix. Measure bytes traversed and copied,
as well as logical transitions, on the replacement representation.

## Validation and current scope

These runtime changes are **proposals**. They require coordinated changes to
IxBy semantics, the compiler and the proof backend, followed by a new reference
run and matching output. A recompiled program has a new program commitment;
its admission proof and expected statement must bind that image explicitly.

The current [state-linking optimization](IxbyFlockPagedExecution.md#direct-state-linking)
keeps the original CSLib program and input bytes. It reduces the circuit work
needed to prove those existing transitions. Complete CSLib execution remains
unproved.

Reproduce the runtime cost record from the retained observer report and
compiler inventory:

```sh
python3 flock-stage3/profile/function_costs.py \
  --report /path/to/full-observer.json \
  --inventory /path/to/cslib.ixby.json \
  --reference flock-stage3/profile/cslib-reference.json \
  --program /path/to/cslib.ixby \
  --output /path/to/new-runtime-costs.json
```
