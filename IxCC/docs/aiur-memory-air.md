# Aiur memory AIR extraction

[`AIR.Memory.coherent`](../IxCC/Aiur/AIR/Memory/Projection.lean)
derives one coherent witness heap from the memory-table polynomials, distinct
bucket identities, and table heights below the Goldilocks characteristic.
Selected rows have selector exactly one. Their pointers may start anywhere
and cross the field boundary. No prior-store, honest allocator, zero-origin,
datatype-validity, or heap-acyclicity premise is used.

[`AIR.Memory.validate`](../IxCC/Aiur/AIR/Memory/Check.lean) checks
ordinary supplied tables and returns `Checked tables`. Its proof-only
[`Sound`](../IxCC/Aiur/AIR/Memory/Sound.lean) module derives activity,
coherence, exact value widths, heap agreement, and the existing
`MessageEval.memory` meaning for every selected cell. The caller supplies no
heap-coherence proof. The production aggregate imports the model and checker;
the extraction proofs and regressions remain separate.

## Exact local model

The source is `crates/aiur/src/memory.rs` at ix revision
`a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03`. A width-`w` table has columns
`[multiplicity, selector, pointer] ++ values`, with exactly `w` values.
Using `m`, `s`, and `p` for the first three columns, a prime for the next row,
and `t` for the transition selector, the four zero constraints are:

```text
s * (s - 1)
m * (1 - s)
(s' * t) * (s - 1)
(s' * t) * (p + 1 - p')
```

The last row reads the first row as its next row, with `t = 0`; other rows
have `t = 1`. There is no last-to-first pointer increment obligation. Empty
tables are allowed. Padding may carry arbitrary pointer and content fields,
subject to the table's fixed width and the checked activity condition.

The single physical lookup has weight `-m` and arguments
`s * [1, G.ofNat w, p] ++ values.map (s * ·)`. The physical memory channel is
one. `pull_weight` and `pull_arguments` prove the exact signed weight and
complete selected payload. The expression builder matches the Rust
constructors' constant-zero/one folding. Expression evaluation returns
`none` for missing current or next columns.

## What is proved from the polynomials

A selected next row on a real transition makes the third constraint give
`s = 1` and the fourth give `p' = p + 1`. Backward induction makes selected
rows a prefix. The existing short unit-cycle theorem then proves pointer
injectivity within any table of height below the characteristic, including
field wraparound. Unique bucket identities extend this to all tables and
yield the existing logical `Memory.Coherent` predicate and witness heap.

This coherence theorem needs no separate Boolean-selector premise. The
activity theorem additionally uses `s = 0 ∨ s = 1` to show that nonzero
multiplicity implies selection. The executable checker checks this condition
explicitly. Deriving it solely from `s * (s - 1) = 0` remains a general field
extraction obligation; this package adds no primality or no-zero-divisors
axiom. A self-referential cell and equal contents at distinct pointers remain
valid, as required by the [witness semantics](aiur-semantics.md).

## Checked admission and limits

The checker requires unique bucket widths, widths below the characteristic,
exact row shapes, Boolean selectors, all four equations at every row, and
each table's height below the characteristic. Distinct buckets can reuse a
pointer. Duplicate buckets are rejected even when their tables are identical
or empty. Selected rows with zero multiplicity still participate in the
prefix and heap-coherence proof.

Preflight runs before polynomial evaluation. Default limits are 256 tables,
65,536 total rows, width 256, and 1,048,576 total fields. The field count includes
the three leading columns and every padding field. The limits bound supplied
Lean data; this API has no binary assignment parser and does not identify
those data with a verifier-accepted assignment or verifying key.

## Independent reference and validation

The frozen [reference graphs](../fixtures/aiur-memory-air/expected.json)
come from the actual pinned Rust `Memory::build`, at widths 0, 1, 2, 7, and
256. The [optional exporter](../tools/aiur-memory-reference/README.md)
records producer revisions, source digests, and regeneration instructions.
It does not replace the Rust builder. Required CI compares the entire graph
with the Lean builder, exports it in a fresh process, and rejects eight
mutations of provenance, circuit inventory, bucket, activity, transition,
pull sign, channel, and pointer. This is conformance evidence for those five
fixtures; a universal Rust theorem and the full keyed IxVM comparison remain
outside its scope.

```sh
lake build IxCC.Aiur.AIR.Memory.Sound \
  IxCCTests.Aiur.MemoryAIR.Proofs IxCCTests.Fences.AiurMemoryAIR \
  tests-aiur check-aiur
lake exe tests-aiur
lake exe check-aiur --root .
lake exe check-aiur --dump-memory-air plans/aiur-memory-air.json
nix build .#checks.x86_64-linux.ixcc-aiur .#checks.x86_64-linux.ixcc-proofs
```

The suite adds 52 runtime assertions, 16 public kernel regressions, and 46
exact ordinary-logic axiom fences while preserving all 2264 prior fences.
The [rank AIR extension](aiur-rank-air.md) brings the total Aiur runtime suite
to 848 assertions. Function and primitive AIR
extraction, lookup-budget/key bindings, production IxVM export, the pure
reference evaluator and allocator relation, and source/DSL lowering remain
separate obligations. No production proof-acceptance or cost claim follows.
