# Source unique-list reversal

`UniqueReuse.compile` compiles a checked Ixon accumulator reversal through
consuming IxIR₁ emission and an independently validated IxIR₂ translation.
Static reuse removes replacement allocations without introducing reference
count operations. Every accepted finite input has a source-to-heap theorem,
exact execution costs, and complete result reclamation.

## Accepted source domain

The current domain is a closed finite Nat list and the exact non-indexed,
non-K, non-parametric list recursor in
[`UniqueReuse/Sources.lean`](../Compilatrix/UniqueReuse/Sources.lean).
Its shared constructor-building minor accepts a unique head and tail; its
accumulator and major are unique. The input, empty accumulator, and builder
come from the original source expression. The compiler recognizes the entire
erased entry, builder, recursor, and constructor declarations before removing
the known builder argument. It rejects other bodies or constructor shapes.
The proof covers arbitrary finite Nat lists in this domain; the executable
fixture generator caps its matrix inputs at 64 elements.

`recursor-modes/1` is an opt-in usage policy. It checks each rule's complete
lambda telescope as one saturated entry, retaining callable binder types and
checking every move, use count, and result world. Unknown and partial calls,
escaping closures, indexed recursors, motives, and K elimination are excluded
from this extension. Definitions first try the existing v0 checker, then the
bounded saturated-entry rule. Resolved nullary constructor references create
fresh unique cells. `Pipeline.certifyErasure` checks the explicit closed entry,
charges its structural work, and retains the ordinary strict erasure,
sharing-aware certificate, complete member coverage, and extern rejection.

`ModeEvidence` checks the original Ixon type and rule telescopes against the
recognized source schema. `IxIR0.RecursorInstance` records argument, field,
and result worlds in the canonical
`compilatrix/ixir0/recursor-instance/1` preimage. The literal instance has
arguments `[shared, unique, unique]`; specialization produces
`[unique, unique]`. Both have field vectors `[[], [unique, unique]]` and a
unique result. Ordinary IxIR₀ declaration syntax and evaluation are unchanged.

## Emission and fallbacks

The consuming IxIR₁ function extracts every field, shallow-frees its parent,
constructs the new accumulator, and tail-recurses. Its declaration receives
an ordinary canonical IxIR₁ address. `UniqueLower.Translation` is indexed by
that exact input. It translates extraction and shallow free to `takeUnique`
and `discardCredit`, then crosses the full ordinary IxIR₂ validator.

The optional static pass checks liveness at the emitted consumed register and
validates the complete rewritten program. The cons block replaces discard
and fresh allocation with `allocWith`; the nil block discards its final
credit. Every credit is consumed before a tail call or return, so execution
uses the existing `call-local/0` policy. The v0 and v1 shared-reuse interfaces
retain their existing behavior.

Disabled or budget-limited reuse retains the exact checked IxIR₂ baseline.
Any other optional reuse failure does the same. Target-validation failure
returns `Backend.ownedOnly`, retaining the proved consuming IxIR₁ artifact.
Source recognition and usage failures reject compilation at the source
boundary. General unique lowering and native heap instruction selection are
separate extensions.

## Proof and cost endpoints

`Compilation.sourceRefinesWithCostLaws` requires only the established source
oracle relation, source sharing well-formedness, and successful source
evaluation. Its `SourceResult` relates that source value to the exact reversed
list and supplies actual consuming execution, backend execution when present,
ownership, full release, and comparative costs. No caller-provided heap,
liveness, shape, ownership, or cost hypothesis is required.

`UniqueLower.Translation.forwardSimulation` covers every successful execution
of its indexed IxIR₁ input and both target interpretations. `Target.mainSteps`
proves the actual emitted program from the empty heap.
`Target.prefixResources` covers every physical prefix: reservations have
distinct owners and occupy empty slots, allocations balance with live nodes,
frees and reservations, RC work is zero, and the peak bound holds.

For `n` cons cells, terminal counters are:

| Observation | Allocations | Frees | Reuses | RC | Live | Peak |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Baseline, either interpretation | `2n + 2` | `n + 1` | 0 | 0 | `n + 1` | `n + 2` |
| Selected, logical | `2n + 2` | `n + 1` | 0 | 0 | `n + 1` | `n + 2` |
| Selected, physical | `n + 2` | 1 | `n` | 0 | `n + 1` | `n + 2` |

Physical reuse accounts for `2n` payload units. All reset counters stay zero.
The baseline spends `6n + 7` control steps; selected code spends `5n + 7`.
Main execution accepts any independent heap budget, including zero. Result
release spends exactly `2n + 1` heap units, empties the live heap, balances
all allocations with frees, and preserves RC, reuse, payload, and peak counts.
For three elements this is 5 allocations, 3 reuses, 1 free, zero RC, and peak 5;
release ends with 5 frees and no live nodes.

Reclamation uses finite list views and exact root ownership. It does not
assume links point toward older allocations: physical reversal can create
forward links. The new source, heap, step, loop, entry, resource, and public
wrapper proofs live in separate modules. Twenty-four theorem fences preserve
the existing Lean and BLAKE3 trust basis.

## Reproducibility gate

```sh
lake build source-unique-reuse check-source-unique-reuse
lake exe check-source-unique-reuse --fixture .lake/build/bin/source-unique-reuse
```

Seven cases cover empty, singleton, three-element, repeated and large Nat
values, 64 elements, and two checked fallback policies. Forty-three additional
checks cover source modes, malformed rules, specialization mutations, mode
identities, source work limits, unsafe target mutations, layout and liveness
rejection, consuming fallback execution, and independent budgets. The cases
also run in `tests`.

The independent checker imports no compiler or evaluator. It rebuilds the
canonical source, recursor-mode, IxIR₁ graph, and policy preimages, checks
their hashes, walks each returned heap using full constructor identities and
unit unique ownership, checks every reservation prefix, and verifies complete
reclamation. It compares all artifacts from two fresh producer processes
against the reviewed report and rejects twelve deliberate corruptions.
The `source-unique-reuse` Nix check runs the complete gate.

Provenance commits to complete source constant and entry bytes, the canonical
IxIR₁ graph, source and specialized recursor instances, checking/erasure fuel,
target limits, versioned usage/specialization/lowering/reuse policies, execution
policy, and selection outcome. It identifies an IxIR₁-plus-policy artifact.
IxIR₂ JSON is diagnostic and has no independent wire, content-address, or
persistent-cache claim.
