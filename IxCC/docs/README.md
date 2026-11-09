# Documentation guide

This guide indexes current contracts, plans and evidence. As reviewed on
2026-10-08, the scalar recheck pipeline is implemented and Phase 1.5 integration
remains incomplete. Documents for the retired pipeline, the Ixby
backend and the Stage2 fixture are on branch `jcb/ixby-archive`.

## Direction and process

- [Reviewer guide](reviewer-guide.md): top-down audit path across the end-to-end
  soundness theorems, TCB and axiom fences, Produce-and-Recheck split, compiler
  passes, Ring-0 PCC, and commit structure.
- [Workspaces and recovery](workspaces-and-recovery.md): recovery checkpoints,
  workspace retirement and validation.

- [Roadmap](roadmap.md): mission, current state, phases, benchmark rungs and
  decisions.
- [Compiler design](compiler-design.md): the pipeline, its
  semantics, ownership and runtime design, backend, and trust obligations.
- [Development and validation](development-plan.md): landing work,
  validation commands and documentation maintenance.
- [CI builds and required coverage](ci.md): the current check surface and
  its coverage-change record.

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

## Aiur target

- [Backend overview](aiur-backend.md),
  [wire format](aiur-wire.md), [semantics](aiur-semantics.md),
  [static checks](aiur-static.md), [counter analysis](aiur-counter-analysis.md),
  [memory AIR](aiur-memory-air.md) and [rank AIR](aiur-rank-air.md).

## Trust and measurement

- [Trusted-extern ledger](trusted-extern-ledger.md) and its
  [machine-readable form](trusted-externs.json): native interfaces,
  specification assumptions and the build and seed supply chain.
- [Benchmark design](benchmark-plan.md): comparison rules and rows; the
  [first-wave fixtures](../benchmarks/fixtures/README.md) and the optional
  [measurement runner](../benchmarks/runner/README.md).
- [Performance reports](performance/README.md): historical measurements of
  the retired pipeline.
- [2026-09-09 review](review-2026-09-09.md): a historical snapshot.
