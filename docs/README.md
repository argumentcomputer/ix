# Documentation

Compilatr.ix compiles content-addressed Ixon through ownership-aware IRs to
selected native programs. Start with the [project overview](../README.md) for
scope and build commands.

## Reading paths

| Task | Start here |
| --- | --- |
| Understand the architecture | [Compiler design](compiler-design.md) |
| Find current work and acceptance gates | [Roadmap](roadmap.md) |
| Make and validate a change | [Development and validation](development-plan.md) |
| Follow a preservation proof | [Simulation strategy](simulation-strategy.md), then the relevant source-family contract below |
| Evaluate performance | [Results](performance/README.md), [implemented protocol](../benchmarks/protocol.md), and [benchmark design](benchmark-plan.md) |
| Audit an assumption or limit | [Trust ledger](trusted-extern-ledger.md), [resource budgets](resource-budgets.md), and [lowering restrictions](lowering-restrictions.md) |

The roadmap owns priorities and delivery state. Design documents explain
decisions; specifications define contracts; source-family pages record the
accepted domain, public theorem, and regression gate. Dated reviews and
performance reports preserve evidence from their recorded revisions.

## Source, identity, and analysis

| Reference | Contents |
| --- | --- |
| [Ixon wire format](ixon-v2-wire.md) | Encoding, strict decoding, ingress checks, and codec laws |
| [Canonical sharing](canonical-sharing.md) | Sharing structure, exact compressor images, evaluator coherence, and semantic identity |
| [Sharing policy](sharing-policy.md) | Frozen producer policy, pins, vectors, and change procedure |
| [Catalog ingress](catalog-ingress.md) | ix catalog manifests, anonymous expressions, roots, coherence, and aggregate limits |
| [Corpus contact](corpus-contact.md) | Pinned production Std catalog and its current acceptance boundary |
| [IR content addressing](ixir-content-addressing.md) | Declaration/mutual-block preimages, readdressing, and provenance |
| [HPT certificates](hpt-certificates.md) | Result-shape analysis, checked consumers, bounded production, and persistent caches |
| [Optimizer harness](optimizer-harness.md) | Pass policy, semantic attachment, reports, and fallback |
| [Resource budgets](resource-budgets.md) | Ingress, compilation, evidence, and cache limits |
| [Well-moded generator](well-moded-generator.md) | Seeded positive/negative cases, replay, and shrinking |

## Ownership and source compilation

| Reference | Contents |
| --- | --- |
| [IxIR₂ specification](ixir2-spec.md) | CFG syntax, capabilities, borrowing, credits, semantics, and checked lowering |
| [Credit refinement](credit-refinement.md) | Logical/physical execution, reservations, counters, and reclamation |
| [Source coverage](source-coverage.md) | Accepted upstream/synthetic inputs, stage failures, and artifact reproducibility |
| [Lowering restrictions](lowering-restrictions.md) | Exact supported fragment and conditions for extending it |
| [Recursion recovery](source-recursion.md) | Eager-list fold recognition, checked replacement, and source/resource proofs |
| [Reuse across calls](source-call-reuse.md) | Shared maps and reservations suspended across direct calls |
| [Unique reversal](source-unique-reuse.md) | Consuming emission, static reuse, and exact resource laws |
| [Borrowed calls](source-borrow.md) | Closed-program caller/callee rewriting and finite execution certificates |
| [Runtime borrowing](source-borrow-runtime.md) | Structural function proofs, lender lifetimes, and open-input costs |

## Native code and trust

| Reference | Contents |
| --- | --- |
| [Emitted instructions](x86-encoded-instructions.md) | Independent decoding and local execution agreement (E1) |
| [Streams and ELF objects](x86-stream-objects.md) | Byte PCs, calls, stack returns, parsing, provenance, and relocation (E2) |
| [Reference ISA model](x86-reference-model.md) | Pinned model, coverage, and remaining adapter/agreement work |
| [Closed native reversal](source-native-unique.md) | Source-selected bounded arena code and complete release |
| [Runtime native reversal](source-native-runtime.md) | Parameterized list ABI, source-to-object proof, and checked counter folding |
| [Upstream native computations](source-native-upstream.md) | Unchanged source exports, structural selection, and fallback |
| [Runtime scalar functions](source-native-scalar.md) | Exact arithmetic, branches, helpers, finite stack, and overflow behavior |
| [Physical scalar CFGs](source-native-physical-scalar.md) | Compositional instruction/edge/call selection, source export binding, and physical-to-ELF preservation |
| [Trust ledger](trusted-extern-ledger.md) | Native interfaces, seed/build trust, specification boundaries, and change control |

The [machine-readable trust ledger](trusted-externs.json) and
[reference-model pin](x86-reference-model.json) support the corresponding prose
contracts. Update integrity-pinned inputs through their documented checks.

## Measurements and historical review

[Performance reports](performance/README.md) retain timings, raw-result
identities, limitations, and replay instructions. [Counter-level thesis
evidence](thesis-counter-evidence.md) records deterministic interpreter counts.
The [2026-09-09 code and documentation review](review-2026-09-09.md) is a
historical snapshot; use the roadmap and focused specifications for current
status.
