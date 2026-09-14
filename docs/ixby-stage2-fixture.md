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

The default compiler resource configuration rejects both closures during
catalog canonical-address admission.
The first declaration is
`_private.Init.Data.Int.DivMod.Bootstrap.0.Int.emod_add_mul_ediv.aux`, address
`001bba8a1cbe777fb4950a7b58f2a500a6608dcd6151c75e3b63d859cab4a6e5`.
Its compression input has 13,195 units; the unchanged default limit is 4,096.

The indexed canonicality checker is now proved equal to the original
recognizer, including ordering, structural equality, and resource rejection.
With the explicit [Stage2 compiler budgets](../Compilatrix/Ixby/Stage2.lean),
all 10,757 constants pass full catalog admission with their original addresses
and manifest. A native run took 326 seconds. The largest single compression
input has 403,187 units; aggregate counts are 3,173,456 stored expression units,
10,374,993 expanded units, and 186,475,983 layer-1 visits. Guest limits and the
default compiler configuration are unchanged.

The next checked boundary is usage: the first declaration above reports
`freezeNeeded`. The admission report scans all constants and records 1,316 usage rejections:
1,090 ownership-freeze restrictions, 125 type-binder runtime-use restrictions,
and 101 syntactic lambda-telescope restrictions. The scan does not certify
these declarations. With dual Nat/String literal interpretation, raw erasure
succeeds for all 10,757 declarations, but all five externs remain reachable
in its dependency graph: `propext`, `Quot.sound`, `Classical.choice`,
`Lean.opaqueId`, and `String.Internal.append`. Typed proof erasure and runtime
primitive support remain necessary before this result can become an executable
Ixby guest.

The existing erasure relation uses an untyped, strict Ixon source evaluator.
Its syntactic type-scheme detection does not classify arbitrary terms of type
`Prop`. Dropping the usage check or deleting logical extern declarations would
not supply the typed source correspondence required here. A diagnostic kernel
replay identified 1,601 proof declarations and 215 type declarations in the
named closure. Lean's native compiler removes those proof dependencies; with
the two fixed key roots treated as constant-data boundaries, its diagnostic
runtime inventory contains 672 entries (including those two boundaries) and
51 standard-library externs.
That inventory describes Lean IR, not an emitted Ixby image or an accepted
Ixby primitive mapping.

The separate [typed frontend](ixby-lean.md) now exports the complete
[Stage2 binary](../fixtures/ixby-stage2/stage2.ixby) from the retained Lean source
and fixed adapter. The [full runtime format](ixby-binary.md) includes Nat,
Word32, bytes, native base/extension fields, BLAKE3, and all runtime control
instructions. A standalone process loads the artifact and runs the unchanged
reference evaluator. The valid proof returns the exact claim; seven invalid
cases return erased. The checked anonymous Ixon pipeline's usage and erasure
obligations remain separate from this working compilation path.

| Artifact or evidence | Current result |
| --- | --- |
| Fixed source, keys, entrypoints, limits and complete Ixon closure | Retained and pinned |
| Complete catalog admission under explicit Stage2 compiler budgets | Passed |
| Native execution of the unchanged source verifier | Exact claim acceptance; seven rejections |
| Complete executable Ixby binary | Retained; 1,002,355 bytes; reproducible fresh compilation |
| Serialized execution and input/output transport | Standalone loader; exact claim acceptance; seven rejections |
| Native field, extension, word, byte and BLAKE3 lowering | Emitted and tested against the source |
| Source-to-image reflection | Still open for this frontend |
| Proving executor integration | Separate downstream work |

The [binary inventory](../fixtures/ixby-stage2/reference-inventory.json)
contains 681 functions, 6,763 blocks, and 146 constructor layouts, with entry
680. It records the artifact SHA-256, complete function and constructor
inventories, primitive and instruction counts, explicit execution limits,
and static frame maxima. An independent decoder reconstructs its structural
fields from the binary.

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

## Compilation and downstream proof work

The typed compiler's executable deliverable is complete: the original fixed
configuration, full runtime operations, binary encoding, standalone loading,
and fixture executions are covered by the [compilation gate](ixby-lean.md).
The [format and handoff](ixby-binary.md) give the proving agent the artifact,
ABI, opcode table, capacities, and reproduction commands.

Formal source certification remains open. It must connect Lean's typed proof
erasure and each representation and primitive mapping to the exact source,
fixed data, and adapter. The reusable symbolic checker does not yet cover this
guest's runtime input inspection. A structural simulation or compositional
checker would need to cover branches, parsing, recursive calls, and the exact
bytes/erased observation for every admitted input.
The first [runtime representation proof slice](ixby-representation.md) supplies
exact number/byte laws and certificates for seven generated extension helpers.
It does not yet compose through this complete source or the Stage2 adapter.

Proving executor support, resource measurement, execution soundness, and
Stage2/Stage3 composition belong to the downstream proving effort. They do not
restrict this compiler's full functional binary format or prevent export.

## Reproduction

```sh
lake build source-ixby-stage2 check-ixby-stage2 stage2-source-run
lake exe check-ixby-stage2 --fixture .lake/build/bin/source-ixby-stage2 \
  --source-runner .lake/build/bin/stage2-source-run
nix build .#checks.x86_64-linux.ixby-stage2

lake exe source-ixby-stage2 --freeze fixtures/ixby-stage2 /tmp/Stage2Guest.lean
lake exe source-ixby-stage2 fixtures/ixby-stage2 /tmp/stage2-report
lake exe source-ixby-stage2 --admit fixtures/ixby-stage2 /tmp/stage2-admission
lake exe stage2-source-run fixtures/ixby-stage2 valid
lake exe stage2-ixby fixtures/ixby-stage2 compile /tmp/stage2.ixby
lake exe stage2-ixby fixtures/ixby-stage2 valid /tmp/stage2.ixby
nix build .#checks.x86_64-linux.ixby-lean
```

The gate checks two fresh complete output sets, both default catalog
rejections, complete fixed key data, generated source equality, the original
decompressed Ixon bytes, and rejection of a changed byte in either key. It also
runs complete admission under the Stage2 compiler budgets and compares every
field with the retained [admission report](../fixtures/ixby-stage2/admitted.json).
A source-byte mutation must be rejected without an admission report.
It does not build or run an Ixby guest. `--admit` performs full catalog
admission under the recorded Stage2 compiler budgets, then reports the usage
boundary, dual literal payloads, and unvalidated raw erasure inventory.

`stage2-source-run` executes the unchanged source reference using the repository
Lean toolchain. Its [35-module import closure](../vendor/stage2/upstream.json)
is retained byte for byte, and the gate checks its complete file inventory.
The two imported Goldilocks/BLAKE3 modules match the already vendored reference.
All eight source cases run in fresh processes. The valid case returns exactly
the 34-byte public claim. The seven rejection cases cover a changed root,
empty, truncated or malformed proof bytes, trailing public or private bytes,
and a wrong claim kind. Both keys and every source resource bound remain fixed.

The [smoke fixture](../fixtures/ixby-stage2/smoke.json) retains the valid raw
8,555,808-byte multiproof with lossless gzip compression and its exact 34-byte
claim. It comes from the grouped singleton fixture with the approved keys; it
is a valid runtime input for this guest, not the Init claim. The original
Ixon proof-envelope digest, checked extraction layout, raw proof digest, and
compressed file digest are retained separately. The source gate tests the
source. The separate typed frontend now also executes the compiled image;
its [eight binary execution cases](ixby-lean.md#reproduction-and-tests) establish
agreement on these fixtures, without universal source/image reflection.

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
