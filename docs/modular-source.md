# Modular source certification

`Compilatrix.Modular` certifies consumer-supplied source units, transports
their checked facts through exact dependency environments, and assembles the
existing `Pipeline.ValidatedCompilation`. The reference compiles a fully
reachable **611-declaration closure in 11 units**. The monolithic entry point
rejects that same source at its unchanged 512-candidate limit.

This I3 slice supplies the source certificate boundary described in the
[roadmap](roadmap.md#i3-modular-source-certification). The
[recorded reference](performance/modular-source-2026-09-12/README.md) contains
checking costs, retained sizes, and replay information. Whole-program erasure,
readdressing, and IxIR₁ lowering still run during assembly. Automatic catalog
partitioning and the compiler's complete source closure remain follow-up work.

## Units and exact dependencies

An `Input` names a unit and supplies owned addressed Ixon constants, a finite
literal table, an optional Nat identity, and ordered imports naming other
units. Every owned constant's address is checked against its canonical bytes.
Every source reference and projection block must resolve within the unit or
its declared import closure. The public exports are all non-mutual constants;
generated raw declarations for executable mutual members also enter the
interface.

The scheduler accepts inputs in any dependency order and checks a dependency
before its consumers. Source ownership must be disjoint. Repeated imports
through a diamond coalesce only when their source, literal, and raw target
bindings agree exactly. Conflicts, absent imports, and cross-unit cycles are
errors. A mutual constant stays whole; a recursive SCC spanning constants
must be placed in one unit. The current API validates a supplied partition
and does not discover SCCs or choose a partition automatically.

The versioned query includes:

- Exact input bytes: owned constants, modes, local sharing tables, literal
  payloads, Nat identity, unit name, ordered imports, and derived exports.
- The `source-unit/1` policy, Ixon/schema and local-sharing mode, strict
  evaluation, no-extern/no-quotient choices, relation and premise versions,
  checker/eraser/lowerer fuel, and every per-unit compiler limit.
- Ordered dependency interfaces. Each contains its unit query digest, source
  Merkle root, public export keys, and every owned raw target declaration.

BLAKE3 keys identify candidates for reuse. The in-memory lookup also compares
the exact query, input, interfaces, full source/literal context, Nat identity,
and raw target context. Hash equality does not establish a proof of syntax or
context equality. A literal edit can preserve every source address and still
invalidate the affected certificates; this is an explicit reference case.

## Checking and composition

`produceUnit` discovers an ordered public coverage schedule. `checkUnit`
independently reruns the actual eraser, compares its complete raw output with
the supplied record, validates the schedule's exact coverage, and checks the
owned public declarations and executable mutual members. Imported certificates
move to the new context by checked exact binding comparisons and a proved
context-extension transformation. They do not run through source validation
again. The unit retains `CoverageDB` and simultaneous `MemberCoverage` for its
complete source context.

`assemble` checks aggregate limits, runs the whole-program addressed eraser,
and transports each unit's checked facts into that actual raw output. It
closes the union's member scope, certifies the chosen entry, and calls the
existing fully addressed IxIR₁ lowerer. Its result exposes the original
`Pipeline.ValidatedCompilation` and downstream theorem interfaces.
`Modular.Compiled.sourcePreservation` proves that successful evaluation of the
closed source entry has a related raw IxIR₀ result. It retains the existing
source `SharingWF` premise. Strict evaluation and the fixed absence of externs
discharge the existing oracle premise.

The generic `PErase`, `Covered`, and `MemberCoverage` transport fences use
`propext` and `Quot.sound`. The composed source theorem retains the production
pipeline's existing `Classical.choice` and native BLAKE3 dependency; it adds
no axiom or native interface. The theorem and exact axiom sets are pinned in
[`Fence.lean`](../Compilatrix/Fence.lean). Native linking and the extern
ownership ABI retain their existing separate obligations.

## Checked cache and retained records

`build` accepts a process-local `Cache policy` of already checked Lean values.
An exact hit reuses that value and its erased proof fields. Preparation still
checks source addresses, usage, dependency integrity, and resource bounds.
Changed units produce new evidence; only the current unit set is retained in
the returned cache. Existing cached records also cross the current consumer's
byte, syntax-depth, and aggregate binding limits before lookup.

Disk records contain a query, complete raw eraser output, and a coverage
schedule. They contain no serialized proof and are not checked cache objects.
`Wire.decodeRecord` and `Wire.decodeStore` accept canonical framed bytes under
`compilatrix/source-unit-record/1` and `compilatrix/source-unit-store/1`.
`restore` requires exactly one record per unit and reconstructs all evidence
in dependency order. Missing, duplicate, stale, incompatible, or malformed
records reject recovery. Ordinary compilation can produce a fresh record;
strict retained replay does not silently replace bad evidence.

The bounded decoder checks total bytes before parsing, sequence and natural
widths before allocating their contents, and nested IxIR₀ expression depth.
Canonical reencoding rejects trailing or noncanonical bytes. Typed record
ingress checks the same structural bounds and exact framed size. File reads
stop after at most the limit plus one byte. This is a retained-evidence format,
not a durable transactional cache service or an IxIR₂ snapshot extension.

## Resource policy

Every unit keeps the original `Pipeline.Limits` checks, including the default
512 public candidates, 131,840 validation attempts, and 134,217,728 source-node
work charge. Modular charging additionally counts executable mutual members:

```text
obligations(unit) = public candidates + executable mutual members
attempts(unit) = obligations × (obligations + 1) / 2 + obligations
work(unit) = attempts(unit) × expanded source units in its import closure
```

The obligation and attempt totals must fit the corresponding per-unit limits.
This conservative charge includes member-only units. Aggregate work sums the
unit charges, including repeated imported contexts. Aggregate size defaults
are:

| Resource | Default |
| --- | ---: |
| Units | 256 |
| Owned source constants | 16,384 |
| Proof obligations | 8,192 |
| Expanded source units | 1,048,576 |
| Imported source/literal/target bindings | 1,048,576 |
| Certificate source-node work | 1,073,741,824 |
| Aggregate queries/outputs and retained store bytes | 67,108,864 |
| Individual framed record bytes | 16,777,216 |
| Query or individual payload bytes | 1,048,576 |
| Sequence elements | 65,536 |
| Natural encoding bytes | 64 |
| IxIR₀ expression depth | 512 |

These aggregate and record-consumer limits are admission checks rather than
semantic certificate identity. Reuse and recovery apply the current bounds,
including to already checked cached records. The per-unit compiler policy
and checker fuels are part of the query itself.

Assembly still enforces the unchanged whole-program usage, erasure-append,
declaration, and lowering budgets. These limits bound different phases; the
aggregate modular limits do not promise acceptance for every source below
their individual maxima. See [resource budgets](resource-budgets.md).

## Indexed assembly checks

Whole-program IxIR₁ addressing now builds hash indexes for producer names,
emitted identities, ordinary declarations, and mutual blocks. It accumulates
the address map in reverse and restores the original order once. Dependency
and member order, exact-preimage collision checks, stable extern identities,
and canonical artifact bytes retain their original definitions.

The checker prepares shared original/emitted environments, forward and
reverse maps, and membership indexes. Reverse lookup preserves the first
producer when identical content is deduplicated. Lean proofs show that the
indexed semantic audit equals the original predicate, and that its additional
exact-image checks combined with semantic checking equal the original
exact-source predicate, including on malformed inputs. The production
checker uses those equalities to return the existing `CertifiedResult`;
it does not rerun an already successful semantic audit. The proof fence
retains the same native BLAKE3 dependency and logical axiom set.

The original list builder and audits remain callable as
`ReaddressAll.runReferenceCertified`. The
[assembly measurement suite](../benchmarks/assembly-scaling.md) compares their
complete artifacts, splits the assembly costs, and retains cold, unchanged,
dependency-edit, literal-premise-edit, and restored source cases. This change
does not remove repeated whole-program erasure, source context comparisons,
or bounded mutual-block work.

The [recorded assembly comparison](performance/assembly-scaling-2026-09-13/README.md)
reduces median assembly for the 611-declaration closure from 2,180 to 131 ms
with exact retained artifacts. Source evidence costs remain separate.

## Reproduction and validation

```sh
lake build source-modular check-source-modular
.lake/build/bin/source-modular run /tmp/modular-source-reference
.lake/build/bin/source-modular replay /tmp/modular-source-reference /tmp/modular-source-replay
.lake/build/bin/check-source-modular --fixture .lake/build/bin/source-modular
```

Output directories must be new. Each case retains exact source recipe bytes,
canonical certificate-store bytes, a complete artifact inspection snapshot,
and a deterministic summary. Timings live in a separate file and are not
compared for equality. Replay regenerates the fixed fixture source, checks it
against the retained recipe, independently checks the retained certificates,
and compares the complete artifact bytes.

The six cases cover an unchanged four-unit graph, a source dependency edit,
a literal-premise edit with unchanged source addresses, two units with a
growing simultaneous mutual-member scope, and two fully reachable wider
closures. All source, raw IxIR₀, addressed IxIR₀, and IxIR₁ results agree; IxIR₁
releases its complete store. The five smaller cases match monolithic
compilation byte for byte at raw/addressed IxIR₀ declarations, groups, blocks,
maps and main, plus complete IxIR₁ artifacts, declarations, map and main.
Both dependency edits reuse the unaffected unit and rebuild the three-unit
dependent cone; their artifacts also match independent cold compilation.

The `source-modular` Nix gate freezes the reviewed report, compares two fresh
artifact sets, runs retained recovery in another process, and checks 40
certificate/resource rejections plus six file mutations through public
replay. Inclusive boundary cases exercise records, stores, unit/aggregate
counts, and member-only obligation/attempt/work charges. Timing observations
have no CI threshold and establish no general compiler speedup.
