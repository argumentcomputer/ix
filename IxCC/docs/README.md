# Documentation guide

This guide indexes current contracts, plans and evidence. As reviewed on
2026-10-08, the scalar recheck pipeline is implemented and Phase 1.5 integration
remains incomplete. Documents for the retired pipeline, the Ixby
backend and the Stage2 fixture are on branch `jcb/ixby-archive` of the pre-merge
`argumentcomputer/Compilatr.ix` repository.

## Direction and process

- [Reviewer guide](reviewer-guide.md): top-down audit path across the end-to-end
  soundness theorems, TCB and axiom fences, Produce-and-Recheck split, compiler
  passes, Ring-0 PCC, and commit structure.
- [Workspaces and recovery](workspaces-and-recovery.md): recovery checkpoints,
  workspace retirement and validation.

- [Roadmap](roadmap.md): mission, current state, milestones across all tracks,
  benchmark rungs and the decision register.
- [End-to-end certification](end-to-end.md): the theorems the plan aims at for
  the x86 and Aiur back ends, the spine they share, and what each trusts.
- [Compiler design](compiler-design.md): the pipeline, its
  semantics, ownership and runtime design, backend, and trust obligations.
- [Development and validation](development-plan.md): landing work,
  validation commands and documentation maintenance.
- [CI builds and required coverage](ci.md): the current check surface and
  its coverage-change record.

## Designs of planned extensions

The [roadmap](roadmap.md#plan) orders these; nothing in them is implemented
unless a line says so.
- [Closures](closures-design.md): higher-order code by closed-world
  defunctionalisation (P8, P9).
- [Data, roots and effects](data-and-roots-design.md): heap completion,
  fixed-width integers, arrays, strings, library structures, the root and
  claim interface, state-machine effects.
- [Bignums](bignum-design.md): the limb library compiled by IxCC.
- [Certification](certification-design.md): grounding IxCC in Ixon and IxCK:
  the chain link by link, the premises discharged by proofs, the spine's
  milestones, the first grounded fragment, and the earlier items CD1–CD4.
- [Evaluator interface](evaluator-interface.md): SrcEval as a versioned
  contract and the Src image, what the Aiur evaluator route needs first.
- [Hardening](hardening-design.md): resource bounds for the verifier against
  dishonest input.
- [Resource soundness](resource-soundness-design.md): what usage, ownership
  and locality annotations guarantee, the ownership checker that verifies them
  and the instrumented-evaluator theorem.

## Source boundary

- [Compile and recheck boundary](compile-boundary.md): what the public
  theorem covers, the hashing dependencies, and the remaining source-adequacy
  obligations.
- [Ixon v4](ixon-v4.md): the ix pins (the v4 codec and the producer), contract encoding, strict
  decoding, catalog-v2 admission, erased typing, resource admission and
  claims.

## x86 target

- [Encoded instructions (E1)](x86-encoded-instructions.md): per-form
  encoder, decoder and byte-execution laws.
- [Streams and ELF objects (E2)](x86-stream-objects.md): complete-stream
  validation, relocations and object execution.
- [Stream checking](stream-checking.md): validation of production emission.
- [Reference model](x86-reference-model.md) and its
  [machine-readable pin](x86-reference-model.json): the Sail x86 candidate and
  the plan for agreement.

## Legacy Aiur bytecode model

Frozen; neither Aiur route of the plan uses it ([status](aiur-backend.md#status-in-the-plan)).
- [Overview](aiur-backend.md),
  [wire format](aiur-wire.md), [semantics](aiur-semantics.md),
  [static checks](aiur-static.md), [counter analysis](aiur-counter-analysis.md),
  [memory AIR](aiur-memory-air.md) and [rank AIR](aiur-rank-air.md).

## Trust and measurement

- [Trusted-extern ledger](trusted-extern-ledger.md) and its
  [machine-readable form](trusted-externs.json): native interfaces,
  specification assumptions and the build and seed supply chain.
- [Source steps](source-steps.md): the unit of SrcEval work (charged rule
  applications), its counter and the `src-steps` tool.
- [Benchmark design](benchmark-plan.md): comparison rules and rows; the
  [first-wave fixtures](../benchmarks/fixtures/README.md) and the optional
  [measurement runner](../benchmarks/runner/README.md).
- [Performance reports](performance/README.md): SrcEval step counts on the
  committed fixtures, and historical measurements of the retired pipeline.
- [2026-09-09 review](review-2026-09-09.md): a historical snapshot.
