# Fixed Stage2 verifier fixture

The fixture exports the unchanged `MultiStark.Verify.claimBytesWrapper` and a
configured `CompilatrixStage2Fixture.initStage2Guest` from the supplied ix
checkout at `e7de6d2818dbb5ad0888cc1218e5e67782d4b0ae`. The configured guest uses
the grouped Init benchmark [handoff](../fixtures/ixby-stage2/handoff.md) and
[target record](../fixtures/ixby-stage2/CURRENT-GROUPED-TARGET.json). This is an
implementation and benchmark target; production security approval is pending.

Both complete anonymous Ixon closures were exported without assumption cuts
or partial output. Upstream deep catalog validation accepted them. Upstream
anonymous kernel checking passed 2,873/2,873 targets for the original wrapper
and 10,622/10,622 targets for the configured guest. A second source file and
fresh exporter process reproduced the complete anonymous guest piece byte for
byte.

| Source | Anonymous constants | Original piece bytes | MAIN |
| --- | ---: | ---: | --- |
| `claimBytesWrapper` | 3,008 | 1,877,140 | `f34f4f717d9d2493a47bf8cb58f5e402568190da2789fcb00c81ed44d2dbc8d0` |
| `initStage2Guest` | 10,757 | 16,075,494 | `f758af421bd9c1955c5813b74cfd76bb76ee5e2c496d93034dc40fc4199dd632` |

The configured closure has 10,870 named transitive dependencies before
anonymous deduplication. Its original piece is stored with lossless gzip
compression; the gate verifies the exact decompressed SHA-256 and bytes.
The full file inventory, original roots, source module, writer executable
digest, and kernel results are in
[`fixture.json`](../fixtures/ixby-stage2/fixture.json).

The existing exporter from the supplied checkout produced these bytes. It
was not freshly rebuilt from the recorded source revision: automatic approval
review rejected running that external Nix environment with elevated access.
The executable digest and original serialized bytes are the writer evidence;
the checkout revision alone is not an authenticated executable build pin.

## Frozen configuration

The guest has exactly two runtime arguments: canonical public claim bytes and
raw private native multiproof bytes. Both keys, both entrypoints, and every
source resource limit are fixed in its declaration closure.

| Field | Fixed value |
| --- | --- |
| IxVM key | 744,159 bytes; BLAKE3 `3983867e9f70a82d990ea65e15265da105617317b95b4b1482e7a7b854ca8063` |
| `verifyClaimEntry` | Goldilocks reduction of 755 |
| Aggregate key | 181,630 bytes; BLAKE3 `75452941bc0dbe4a861c88c792067f34d7864f0460f305858a0a004ec409406e` |
| `aggregateEntry` | Goldilocks reduction of 243 |
| Allowed identity | 80 bytes; BLAKE3 `224668baa32c9e827a1751513d8976836f6e3d9aba3f1b3cca5c9cbd1b7ff19b` |
| Decoder | 16,777,216 bytes; 1,048,576 vector elements; 2,097,152 nested items |
| FRI | 1,024 queries; fold arity 256 |
| Transcript | 16,777,216 observation bytes; 64 sampling attempts |

These last three rows are source admission limits, not target capacities or
cryptographic security parameters. The native keys fix 100 queries, log blowup
2, cap height 0, binary FRI, a constant final polynomial, zero commit-grinding
bits, and 20 query-grinding bits. Function grouping and the default aggregate
lookup policy follow the target record.

`source-ixby-stage2 --freeze` checks both complete key-file hashes and the
80-byte allowed-identity preimage, then emits a reproducible Lean module.
The [elaboration commands](../fixtures/ixby-stage2/Freeze.lean) build ordinary
UInt8/BitVec/Fin, List, and Array constructor declarations through Lean's
kernel-checked `addDecl`. List segments contain at most 128 bytes. This avoids
elaborating nearly a million individual source expressions. Native Lean code
generation is unnecessary for these Ixon source declarations.

The hex parser and declaration builder run at elaboration time. The selected
guest's dependency closure contains the resulting fixed constructor data;
it has no runtime key-file loader, hex decoder, concatenation loop, or key
generator. The regression gate independently compares every encoded key byte
with the retained raw files and checks the generated module's exact digest.

## Current compilation boundary

Compilatrix rejects both closures during catalog canonical-address admission.
The first declaration is
`_private.Init.Data.Int.DivMod.Bootstrap.0.Int.emod_add_mul_ediv.aux`, address
`001bba8a1cbe777fb4950a7b58f2a500a6608dcd6151c75e3b63d859cab4a6e5`.
Its compression input has 13,195 units; the unchanged default limit is 4,096.

A separate exploratory run with a 65,536-unit limit reached another resource
rejection: `Lean.Omega.Constraint.combine_sat` requires 66,861 units. Raising
the limit further made the current structural canonicalizer too costly for
that exploration, which was stopped without a semantic result. The fixture
preserves the original full closure and default rejection. It does not omit
proof dependencies or silently raise compiler or guest limits.

| Requested artifact or evidence | Current result |
| --- | --- |
| Fixed source, keys, entrypoints, limits and complete Ixon closure | Retained and pinned |
| Ixby guest image and serialized profile | Unavailable: source admission rejects first |
| Exact target operation inventory and measured capacities | Unavailable until lowering succeeds |
| Source-to-image reflection | Unavailable for this guest |
| Current Flock executor compatibility | Not established |

The source needs runtime byte parsing/equality, indexing, bounded recursive
traversal, UInt bit operations and BLAKE3, Goldilocks base/extension arithmetic,
transcript sampling, and Merkle/AIR/OOD/PCS/FRI verification. Those are source
requirements, not a fabricated instruction inventory for an absent image.

## Required input and output ABI

The public input is exactly canonical closed `CheckEnv(root, none)` transport:
`e5 || root[32] || 00`, 34 bytes. The Init root remains a runtime input. The
private input is the raw native multiproof, excluding the enclosing
`Ixon.Proof` wrapper and expanded advice.

The source returns `some publicClaim` only on verification success and `none`
otherwise. The required Flock result ABI maps these to raw
`Ixby.Value.scalar (.bytes publicClaim)` and `Ixby.Value.erased`, respectively.
Compilatrix's ordinary Option/constructor layout does not establish this
mapping. The adapter needs its own certified source/target correspondence.

The [reusable symbolic checker](ixby-symbolic.md) rejects inspection of runtime
parameters. Proof parsing therefore requires a broader refinement argument
even after source ingress, lowering, and the ABI adapter work. Example-input
agreement cannot replace that theorem. The upstream conditional Stage2
composition still requires source/image reflection and actual executor
soundness.

## Route to an executable, certified guest

The next milestone is complete catalog admission of this exact guest. It is
not yet evidence that the guest compiles or runs. The remaining work has these
observable completion conditions:

1. **Scale exact canonical-address checking.** The current compressor repeatedly
   enumerates and deduplicates structural subtrees, scans occurrences for each
   representative, recomputes subtree hashes while sorting, and searches sharing
   tables while rewriting. Use an indexed DAG with exact structural keys,
   cached sizes/hashes, occurrence multiplicities, and indexed rewriting. Prove
   equality with the existing pinned-ix recognizer, including its ordering and
   collision tie-breaks. Retain explicit work bounds. Completion means that all
   10,757 constants pass the original address and full-catalog checks under a
   documented, measured compiler resource configuration.
2. **Obtain checked erasure for the complete runtime closure.** Run usage and
   source-certificate checks after ingress and record their actual failures.
   The current whole-program certificate path has a 512-candidate default and
   charges repeated dependency rounds; catalog acceptance does not remove those
   limits. Where necessary, extend dependency-ordered bounded certification and
   exact composition to this source. Any removal of proof-only runtime code must
   follow checked erasure of the original source, preserving the source bindings.
3. **Compile the required representations and primitive operations.** The
   reference target already defines bytes, Word32, Goldilocks/extension fields,
   and BLAKE3, but this compiler currently emits boxed functional code and has
   no lowering to those primitives. Add source-bound representation and
   primitive correspondence proofs, including fixed key bytes and bounded
   indices. Preserve the unchanged verifier definition and fixed configuration.
   Establish the two-byte-array input ABI and the exact raw bytes/erased output
   ABI above. Completion means a real canonical image/profile, successful
   reference execution of a valid proof, and rejection of malformed or
   claim-mismatched proofs.
4. **Prove reflection through runtime control flow.** Use a structural simulation
   or compositional checking argument covering branches, byte inspection, and
   bounded recursion for every admitted input. Extend the source connection all
   the way to `MultiStark.Verify.claimBytesWrapper`: the existing reusable
   theorem starts at IxIR0, and forward erasure alone does not establish the
   reverse source reflection needed by Stage2. Completion means the upstream
   `ByteExecutionRefinement SourceEvaluation` obligation for this exact source,
   image, profile, and ABI, without requiring a separate source run per input.
5. **Admit and prove execution in Flock.** Extract operations and measure execution
   resources from the actual image. Compare its control, value representations,
   primitives, and capacities with the selected executor implementation; extend
   the executor or add proved compiler transformations where they differ.
   Source decoder limits and successful reference runs cannot supply physical
   capacity evidence or `ExecSoundness`. Bind the admitted profile, image, ABI,
   and execution statement, then produce and verify an execution proof. Terminal
   composition additionally retains its own compression-soundness obligations.

These are implementation milestones, not completed claims. Ingress and checked
erasure should expose the next concrete compiler failures before selecting
target capacities. Primitive and control-flow proofs can be developed on small
runtime-input examples while that source work proceeds, with the unchanged
full verifier retained as the integration target.

## Reproduction

```sh
lake build source-ixby-stage2 check-ixby-stage2
lake exe check-ixby-stage2 --fixture .lake/build/bin/source-ixby-stage2
nix build .#checks.x86_64-linux.ixby-stage2

lake exe source-ixby-stage2 --freeze fixtures/ixby-stage2 /tmp/Stage2Guest.lean
lake exe source-ixby-stage2 fixtures/ixby-stage2 /tmp/stage2-report
```

The gate checks two fresh complete output sets, both current catalog
rejections, complete fixed key data, generated source equality, the original
decompressed Ixon bytes, and rejection of a changed byte in either key.
It does not build or run an Ixby guest.

To regenerate the source exports, use the recorded exporter and Lean 4.33.1
environment with the pinned upstream imports already built. Generate
`Stage2Guest.lean` in that project, then:

```sh
ix compile Stage2Guest.lean --no-build \
  --consts CompilatrixStage2Fixture.initStage2Guest \
  --out Stage2Guest.ixe --report Stage2Guest.report.json
ix pack Stage2Guest.ixe CompilatrixStage2Fixture.initStage2Guest \
  --anon --out initStage2Guest.ixe
ix check-rs initStage2Guest.ixe --anon
ix catalog assemble guest.ixc initStage2Guest.ixe \
  --labels CompilatrixStage2Fixture.initStage2Guest \
  --toolchains leanprover/lean4:v4.33.1 \
  --pins git:ix@e7de6d2818dbb5ad0888cc1218e5e67782d4b0ae
ix catalog verify guest.ixc --deep
```

Compare the raw piece and manifest with the retained pins. Preserve all key,
entrypoint, resource, ABI, and source-version bindings when changing this
fixture. A larger Init claim that exceeds the fixed source limits requires an
explicitly versioned configuration.
