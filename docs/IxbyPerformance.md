# IxBy performance priorities

The [revision-2 runtime](CompilatrixRuntimeV2Handoff.md) now provides unboxed
numeric scalars and conversions, persistent arrays, immutable byte builders,
and zero-copy slices. Compiler adoption and a new CSLib measurement remain
pending. The runtime-helper counts below refer to the earlier compiled image.
The [batch tuning report](IxbyBatchTuning.md) separately measures physical
proof geometries on the current runtime, including a 4K fetch prototype.

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

The profiled compiler image implements some conversions by consuming four bits at
a time and using a balanced comparison tree to cross scalar representations.
The four conversion helpers in the table execute 240.5 million transitions.
This is a good first target because the replacement operations have small,
precise specifications:

- Nat to Word32: the low 32 bits, explicitly modulo `2^32`.
- Word32 to Nat: the exact nonnegative integer value.
- Field to Nat, where needed: the canonical representative.

Nat/Word32 and Nat/Field primitives, reference semantics, and constrained
implementations are available. The
[compiler handoff](CompilatrixRuntimeV2Handoff.md) describes the representation
and certificate changes still needed in Compilatrix. Boundary cases include
zero, `2^32 - 1`, `2^32`, and larger Nats; the reference run observes 65-bit
Nats, so a blanket replacement of Nat with Word32 would change this workload.

A later representation change can keep typed scalars through arithmetic and
reserve wrappers for boundaries that need them. That can also reduce
constructor allocation, case dispatch and memory traffic. Its benefit needs
a new compiled-image trace.

## Native persistent array operations

`treeGet` alone executes 335 million transitions. Each tree level runs generic
comparisons, branches, division by two, projections and tail calls. `treeSet`
adds another 145 million transitions while rebuilding persistent paths.

Revision 2 implements explicit indexed reads and persistent updates with
constrained path traversal. Updates share unchanged spans and tree paths;
they do not copy an entire array on each write. Compiler representation
certificates and general circuit-to-reference refinement remain obligations.
This targets both interpreter overhead and the number of state/memory records
that reach the proving circuit.

## Native byte builders and slices

The current rope representation saves copying but expresses height checks,
node construction and balancing as interpreted functions. Those four helpers
account for 329 million transitions.

Revision 2 implements immutable append/freeze builders and checked shared
slices. Append retains chunks; freeze copies each byte once. Native tests
check exact byte output, aliases, allocation counts, and BLAKE3 behavior.
Compiler integration must preserve the source byte-sequence semantics.
Measure bytes traversed and copied,
as well as logical transitions, on the replacement representation.

## Validation and current scope

The IxBy semantics and proof backend implement the runtime changes. Compiler
adoption and the measured CSLib benefit remain pending. Integration requires
a new reference run and matching output. A recompiled program has a new program commitment;
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
