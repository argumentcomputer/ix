# IxIR content addressing

Status: canonical declaration and cycle-safe IxIR₀/IxIR₁ mutual-block
preimages, strict framed decoders with kernel roundtrip/canonicality proofs,
both whole-program address passes, evaluator/proof transport, and the fully
addressed production pipeline landed 2026-08-26. The validator deliberately
retains the exact legacy erasure as its proof-facing intermediate; its exact
call-aware certificates transport across both complete address maps. The
current modeled address-sensitive oracle has a concrete coherence theorem and
frozen cyclic executable fixture. The bounded HPT result-shape checker
materializes SCC-granular cache/summary identities over this graph, and its
first complete consumer now rebuilds changed declaration bodies under fresh
content addresses with exact evaluator transport. Its persistent storage now
offers bounded record-streamed snapshots plus a metadata-indexed per-key chunk
directory whose dependency-selected records are lazily checked and durably
repaired. Both publication paths use atomic rename bracketed by ledgered
stable-file/directory barriers. Address-exact double compilation remains
active; streaming/sharded index maintenance and cross-store scheduling remain
later scaling work.

IxIR₀ and IxIR₁ now have explicit, versioned BLAKE3 preimages in
`Compilatrix/IxIR0/Serialize.lean` and
`Compilatrix/IxIR1/Serialize.lean`. The common primitives live in
`Compilatrix/IxIR/Encoding.lean`; their shared strict readers and proof
combinators live in `Compilatrix/IxIR/Decode.lean`.

## Common grammar

- Natural numbers are canonical unsigned LEB128 over arbitrary-precision
  Lean `Nat`. The encoder is total and does not pass through `UInt64`; frozen
  guards include `2⁶⁴`, so truncation to zero cannot recur silently.
- A Boolean is one byte (`0` or `1`).
- A blob or UTF-8 string is a LEB128 byte length followed by its bytes.
- An array or list is a LEB128 element count followed by its elements in
  source order.
- An address is exactly its 32 raw bytes.
- Every sum constructor has a distinct one-byte tag. Product fields follow in
  declaration order.

The complete declaration preimages begin with an ASCII domain and NUL:

| IR | Domain |
| --- | --- |
| IxIR₀ | `compilatrix/ixir0/decl/1\0` |
| IxIR₁ | `compilatrix/ixir1/decl/1\0` |

Changing any tag, field order, primitive spelling, or domain is an address
version roll, not a compatible refactor.

## Constructor tags

IxIR₀ uses these tags:

| Type | Tags |
| --- | --- |
| `Literal` | `nat=0`, `str=1` |
| `Expr` | `var=0`, `ref=1`, `app=2`, `lam=3`, `letE=4`, `proj=5`, `lit=6`, `erased=7` |
| `Decl` | `defn=0`, `ctor=1`, `recursor=2`, `extern=3` |

IxIR₁ uses these tags:

| Type | Tags |
| --- | --- |
| `Atom` | `var=0`, `lit=1`, `erased=2` |
| `Op` | `pure=0`, `alloc=1`, `reuse=2`, `free=3`, `dup=4`, `drop=5`, `dropU=6`, `fetch=7`, `call=8`, `callSelf=9`, `papp=10`, `apply=11`, `extern=12` |
| `Code` | `ret=0`, `letOp=1`, `case=2` |
| `Decl` | `fn=0`, `extern=1` |

`IxIR0.Decl.address` and `IxIR1.Decl.address` are BLAKE3 of the corresponding
complete preimage; `Decl.addressed` pairs the computed key with the value.
Both layers expose `address_eq_iff_preimage_eq` under the exact pairwise
`Address.Blake3NoCollision` premise. They do not assert global injectivity of
a 256-bit hash. BLAKE3 remains the native boundary recorded in the trusted
extern ledger.

`Tests.IxIRAddressFixtures` freezes complete bytes and digests for a nested
IxIR₀ recursor and an IxIR₁ function containing allocation and branching.
Elaboration-time guards separately pin primitive and small constructor
spellings.

## Strict decoder boundary

`Compilatrix/IxIR0/Decode.lean` and `Compilatrix/IxIR1/Decode.lean` expose
`Decl.decodePreimage` for the complete domain-framed artifacts. Recursive
expressions/code and arbitrary-precision LEB128 values are input-fueled, so a
hostile byte string cannot induce logical nontermination. The entry point
requires full input consumption and then re-encodes the parsed declaration;
acceptance requires exact byte equality. Consequently the raw LEB128 reader
may parse a wider terminating language while every alternate/nonminimal
spelling is rejected at the public boundary.

Both IRs prove, in the kernel:

- `Decl.decodePreimage_roundtrip`: every canonical preimage decodes;
- `Decl.decodePreimage_canonical`: accepted bytes equal the result's canonical
  preimage;
- `Decl.preimage_injective`: canonical declaration preimages are injective.

`Compilatrix/Fence.lean` pins all six theorem cones to exactly `propext`,
`Classical.choice`, and `Quot.sound`. Compiled fixtures exercise the two golden
declarations and reject trailing bytes, wrong domains, invalid tags,
nonminimal LEB128, invalid nested UTF-8, and truncation at both IR layers.

## Cycle-safe IxIR₀ mutual blocks

`Compilatrix/IxIR0/MutualBlock.lean` supplies the strongly-connected artifact
format that ordinary declaration hashes cannot express. It first converts an
ordered set of transiently keyed IxIR₀ declarations into symbolic declarations.
Every global edge in that syntax is one of:

- `local(index)` (`tag 0` followed by canonical LEB128), when the concrete
  address names a member of the same ordered block; or
- `external(address)` (`tag 1` followed by 32 raw bytes), otherwise.

The complete ordered symbolic list uses the domain
`compilatrix/ixir0/mutual-block/1\0`. Its BLAKE3 digest is the block identity;
the transient producer keys are absent from these bytes. Executable member
keys are then independently derived as BLAKE3 of
`compilatrix/ixir0/mutual-member/1\0 || block-address || LEB128(index)`. Thus a
two-way definition/recursor edge is already finite before either member key is
chosen, while member order remains an explicit part of identity.

The boundary is both producer- and ingress-facing:

- `MutualBlock.runCertified` abstracts transient declarations, hashes the
  block, derives all member keys, materializes local edges, and retains an
  erased structural audit proving that the result is exactly the recorded
  address image and re-abstracts to the same block;
- `Block.decodePreimage` is input-fueled, full-consuming, and exact-reencoding;
  `Block.decodeArtifact` additionally rejects empty blocks and out-of-range
  local indices, while `Block.decodeMaterialized` derives and checks the final
  executable environment;
- duplicate temporary keys, temporary/reserved overlap, duplicate derived
  keys, and capture of a temporary, external, reserved, block, or member
  identity all fail closed.

The kernel proves block decoder roundtrip, accepted-byte canonicality, and
block-preimage injectivity. The fence separately pins the successful producer
audit with the ledgered native BLAKE3 axiom visible. Compiled fixtures freeze a
genuine cyclic block's
87-byte preimage, block digest, and both derived member keys; verify transient
name independence and member-order sensitivity; decode and rematerialize the
same environment; reject malformed framing/tags/counts/scope; and exercise the
exact old `memberAddr block (2^64-1) = block` alias as a protected-namespace
failure.

`Compilatrix/IxIR0/Readdress.lean` lifts the one-block constructor over a
whole erased program. Stable groups keep their keys, every mutual group gets a
separate symbolic block, and the union map rewrites all declarations plus the
main expression. It rejects duplicate raw keys, stable/transient/reserved
overlap, cross-block temporary edges, and capture of global external
references. Its audit records the exact declaration/main image, namespace
safety, forward environment lookup, and the fixed-point property of every
emitted lookup. A separate bidirectional isolation clause proves that every
reserved identity, stable declaration key, and external reference from either
a declaration or the main expression occurs on neither the producer nor image
side of the member map. This is stronger than fixed-point stability and
prevents reverse oracle dispatch from capturing an unrelated ABI key.

`Compilatrix/EraseAddressed.lean` is the migration seam around the existing
proof-facing eraser. It records constant grouping, preserves the old output
byte-for-byte as `Result.raw`, protects every source constant identity, and
returns the whole-program addressed result. `EraseAddressedSim.lean` exposes
the old eraser equation and proves exact closed-run transport.

`Compilatrix/IxIR0/ReaddressSim.lean` maps every address-bearing evaluator
object: expression/declaration references, constructor values, PAP heads,
closure bodies and captured environments, oracle arguments/results, and both
address-bearing error forms. A common-fuel induction over
`eval`/`apply`/`saturate`/`fire` proves evaluator equivariance. The concrete
context theorem is obtained from the executable lookup audits; pure programs
need no oracle premise, while extern programs state the exact structural
oracle compatibility required.

`Compilatrix/IxIR0/ReaddressProjectionSafe.lean` transports the stronger
fuel-indexed `ProjectionSafe.Eval`/`Apply`/`Saturate`/`Fire` witnesses, plus
bounded argument/application spines. Its one-way `Ctx.TraceRenames` relation
requires only successful lookups, so it relates the validator's literal raw
environment directly to the addressed environment without adding proof-side
aliases. `EraseAddressedSim.run_projectionSafeMain_of_run_eq_ok` specializes
that result to the exact main and maps retained by a successful production
erasure.

`Compilatrix/IxIR0/ReaddressOracle.lean` supplies the executable oracle view.
The forward address action is not globally invertible—a derived key is fixed
even though its transient predecessor also maps to it—so the adapter does not
attempt to unmap arbitrary runtime values. It reverse-resolves only the called
declaration key, passes the already-addressed argument values to the legacy
oracle, and maps a returned value forward. `Oracle.Readdressable` states the
compact coherence law needed at that boundary; the empty oracle, a split
key/argument proof rule, and `Readdressable.of_isolated_key` are reusable proof
rules. `Compilatrix/IxIR0/ReaddressOracleExamples.lean` applies the isolation
certificate to the ledger-recorded literal-Nat addition model at
`IxIR0.Examples.natAddExt`. The corresponding `EraseAddressedSim` evaluator
and exact-trace wrappers construct the addressed oracle internally.

## Cycle-safe IxIR₁ mutual blocks

`Compilatrix/IxIR1/MutualBlock.lean` supplies the corresponding checked
artifact for cycles that cross source-backed functions and generated closures.
It symbolically covers every static IxIR₁ address position: constructor
blocks in `alloc`/`reuse`, and the targets of `call`, `papp`, and `extern`.
Edges inside the ordered block use `local(index)`; all other edges retain a
full external address. The block and member domains are respectively
`compilatrix/ixir1/mutual-block/1\0` and
`compilatrix/ixir1/mutual-member/1\0`.

Like its IxIR₀ counterpart, the module exposes a strict, full-consuming,
exact-reencoding decoder; scope-aware ingress materialization; independently
derived executable member keys; collision and namespace checks; and a
successful-run semantic audit proving the concrete result is exactly the
recorded address image and re-abstracts to the same symbolic block. Kernel
roundtrip, accepted-byte canonicality, and preimage-injectivity theorems bring
the fence to twenty-two codec laws. The compiled fixture freezes a 99-byte
source/generated-style two-node cycle, its block and member digests, transient
name independence, order sensitivity, rematerialization, malformed framing and
scope rejection, and duplicate/reserved-identity failures.

`MutualBlock` remains the reusable constructor and ingress boundary;
`Compilatrix/IxIR1/ReaddressAll.lean` supplies the complete graph pass around
it.

## Whole-program IxIR₁ addressing

`ReaddressAll` treats every IxIR₁ function key as a producer name,
independent of lowering's source/generated partition. It builds a hash-indexed
dependency graph and runs both Kosaraju traversals with explicit array stacks,
so long chains do not consume the native call stack. SCC members retain input
declaration order. The condensation DAG is then emitted dependencies first by
a source-rank min heap, preserving the deterministic order obtained by always
selecting the first ready source component.

An acyclic function singleton uses the ordinary declaration preimage; a
cyclic singleton or multi-member SCC uses `MutualBlock`. `callSelf` carries no
address and remains an ordinary edge-free operation. `.extern` declaration
keys are the intentional stable exception: their arity-only bytes cannot name
the opaque oracle ABI selected by the existing key. Constructor identities are
not declaration producers at IxIR₁, so `LowerFullyAddressed` supplies them as
the pass's explicit `reserved` set.

The pass fails closed on duplicate producer keys, producer/reserved overlap,
capture of transient, reserved, external, stable-ABI, or already emitted
identities, and any observed same-digest/different-preimage collision. Exact
ordinary declarations and exact mutual blocks may deduplicate. The result
retains dependency-ordered `stable`/`ordinary`/`mutual` artifacts, one complete
raw-to-final map (including identity entries for externs), block provenance,
the reserved set, and the rewritten main code. Its executable semantic audit
checks the exact declaration/main image, map completeness, canonical artifact
identity, fixed-point lookups, absence of transient keys and references, and
pointwise protection of every reserved identity. `runCertified` records both
that audit and equality of the retained reserved set to the caller's input.

`Compilatrix/IxIR1/Readdress.lean` and
`Compilatrix/IxIR1/LowerAddressed.lean` remain the generated-only compatibility
boundary used by older theorem interfaces. Production uses
`Compilatrix/IxIR1/LowerFullyAddressed.lean`: it consumes the same raw
whole-pass result, reserves constructor identities, and invokes `ReaddressAll`
over source-backed and generated functions together. Both `Pipeline.compile`
and `Pipeline.compileValidated` use its indexed entry point.
`Pipeline.Artifact.targetArtifacts` retains complete provenance and
`targetAddressMap` is authoritative; `targetDecls` and `targetBlocks` are
projections. The old `generatedAddressMap` name remains only as a filtered
compatibility view.

`Compilatrix/IxIR1/ReaddressSim.lean` proves full evaluator equivariance under
an address map: contexts, declarations, environments, heaps, return values,
errors, oracle calls, and every mutually recursive evaluator entry are
transported. Its `runMain_mapAddresses` theorem is independent of hashing.
`ReaddressAllSim.lean` exposes the complete pass through that generic carrier,
and `LowerFullyAddressedSim.lean` composes it with the exact indexed and
unindexed lowering calls. The public results include exact run transport,
successful-result transport, constructor-identity stability, semantic forward
simulation, memory/stuck/unknown-reference exclusions, and exact instruction
counters. IxIR₁ extern declarations receive explicit identity entries in the
complete map, while undeclared direct extern references are outside its
producer domain. Consequently the ledger's IxIR₁ Nat-add fixture keeps the
same ABI key and is covered by the generic oracle pullback theorem rather than
needing the IxIR₀ member-key adapter law.

`LowerMutualAddressedSim.lean` keeps the IxIR₀ and IxIR₁ maps typed and
separate and composes them. `LowerMutualAddressedProgress.lean` closes the
validator path: an exact member-scoped `CertifiedSharedExpr` plus simultaneous
member coverage supplies the addressed call-aware trace, sealed lowering
contracts supply the raw target run, and the complete IxIR₁ map transports
it to the final artifact. `Pipeline.compileValidatedWithTrace` retains that
runtime-derived scope, the main certificate, member coverage, the exact
erasure result, and both lowering/address-pass equations.
`Pipeline.ValidatedCompilation.semanticForwardSimulation` projects those
witnesses into one fully addressed semantic endpoint. The IxIR₀ adapter
oracle is constructed internally from `Oracle.Readdressable`; source/legacy
oracle correspondence, target layout, compiler ownership, and extern behavior
remain explicit semantic or ABI premises.

The member-aware route intentionally does not strengthen a validated program
to globally all-shared. Accepted affine and unique declarations may be safe
when reached only through saturated known calls, so discharging the remaining
`CompilerContracts` premise requires a PAP-safe, owner-sensitive reachable-
store argument rather than a blanket ownership assumption.

The production semantic endpoint uses `AddressedValueGraph`: the final heap is
the address image of a raw heap carrying the existing `ValueGraph`. This is
strictly more accurate than textual heap identity because PAP nodes can carry
rekeyed source or generated functions. Constructor identities remain exact by
the retained reserved certificate.

Compiled fixtures freeze ordinary and mutual dependency order, exact-content
deduplication, namespace/collision failures, an 8192-node iterative SCC chain,
nested lifted lambdas, a constructor wrapper, a source/generated lowering
cycle, complete target maps and block digests, and execution of terminating
addressed programs. A genuine two-definition source cycle crosses both
production passes, removes every source/transient producer key, and yields the
same complete target artifact through direct and sharing-aware validated
compilation. The generic oracle fixture separately checks legacy-key reverse
dispatch, arity-sensitive failure, and forward mapping of an address-bearing
result. A second frozen fixture combines a genuine two-member IxIR₀ cycle
with the ledger-recorded Nat-add extern, proves the concrete coherence law,
pins the block and both member digests, and evaluates to literal `42` before
and after addressing. A regression also verifies that a derived member key
cannot capture an external identity referenced only by the main expression.

## Proved boundary and remaining frontier

The production declaration environment now contains only ordinary content
hashes, mutual-member keys derived from content-addressed blocks, and stable
extern ABI identities:

1. The theorem-facing `lowerAllAction` still uses `synthAddr` as an internal
   transient namespace; the production pipeline no longer emits those values
   as declaration keys or references. The evaluator/environment-renaming
   obligation is closed by `ReaddressSim`; `ReaddressAllSim` and
   `LowerFullyAddressedSim` transport the existing lowering simulations across
   the complete recorded `targetAddressMap` at the indexed entry point used by
   the pipeline. The generic transport has only the ordinary logical axioms
   reported by the fence. Production corollaries consume a successful native
   BLAKE3 pass, so their theorem cones intentionally expose
   `Blake3.HasherOps.hash._native.native_decide.ax_1✝`;
   `Compilatrix/Fence.lean` pins that exact ledgered exception. Digest fixtures
   run in the compiled test executable, with no second test hash.
2. Ixon mutual members still reach the *legacy proof-facing intermediate*
   through `memberAddr`, but not the production IxIR₀ or IxIR₁ environments.
   `EraseAddressed` preserves that raw list for existing erasure certificates,
   then the pipeline lowers only the certified block-derived image and records
   `erasedAddressMap`. The compiled mixed mutual recursor fixture checks that
   the old key is present in `rawErasedDecls`, absent from final `erasedDecls`
   and `targetDecls`, and that execution/cost behavior is unchanged. Generic
   evaluator transport, exact call-aware/projection-safe certificate transport,
   final target progress, and two-map certificate-sealed forward simulation are
   closed. `ReaddressOracle` now constructs the final-key oracle view and the
   final progress/simulation theorems consume only its compact
   `Readdressable` law. The current ledger-recorded IxIR₀ Nat-add model
   discharges that law from the successful pass's bidirectional isolation
   certificate; every future address-sensitive production oracle must add its
   own ledger entry and proof.
3. Extern declarations deliberately retain their existing keys. Their current
   declaration preimage records only arity, not the opaque ledger/oracle ABI,
   so hashing it would conflate distinct external services. IxIR₁ therefore
   keeps these keys stable; an IxIR₀ oracle that observes readdressed member
   keys must discharge `Oracle.Readdressable`. The current Nat-add model does,
   while the generic erasure-generated extern frontier remains explicitly
   unsupported until a concrete service receives a per-address ledger entry
   and source/target correspondence proof. Constructor block identities are
   likewise caller-owned rather than IxIR₁ declaration producers; the
   whole-program result retains and audits them as `reserved`.
4. The cached-analysis boundary is now persistent and checked: the bounded HPT
   checker materializes ordinary/mutual-SCC summaries whose query keys commit
   to program identities and dependency-summary addresses; a strict versioned
   record/store decoder treats every hit as untrusted; and the deterministic
   producer rebuilds only missing or rejected artifacts before the assembled
   certificate crosses the ordinary whole-program checker. Frozen
   precise/widened fixtures show dependency-cone invalidation without
   perturbing unrelated summaries. A canonical bounded single-file adapter
   synchronizes a verified sibling staging file, publishes it by atomic rename,
   and synchronizes both affected directories. A second adapter indexes
   canonical singleton chunks by cache-key filename, retains metadata rather
   than the full store payload, lazily opens only dependency-selected records,
   and publishes repairs through the same durable protocol. Pipeline entry
   points exercise cold creation, warm hits, corruption isolation/rejection,
   orphan staging, complete replacement, and local repair
   (`docs/hpt-certificates.md`).
5. Rebuilding an already-addressed IxIR₁ graph is now an exact production
   boundary. `ReaddressAll.rebuild` alpha-renames function producers into a
   domain-separated temporary namespace, reruns the ordinary SCC-aware pass,
   and composes the caller's old keys to final keys. The ordinary semantic
   audit is joined by `rebuildSemanticAudit`, which checks the main and every
   declaration under the total `rebuildRename`, validates reverse images only
   through emitted holes, and requires a producer preimage for every emitted
   declaration. `ReaddressAllSim` reflects that finite audit into an exact
   old-keyed context relation and transports the complete `runMain` result via
   `Readdress.mapRunResult`, without adding final-key aliases to the source
   environment. The checked HPT declaration-graph consumer exercises this
   adapter and composes the pipeline's original target map. The HPT store now
   publishes record-streamed, verified sibling staging files with an atomic
   rename plus ledgered file/directory barriers, providing power-loss-durable
   publication on the supported filesystem baseline. The first disk-backed
   per-artifact lazy chunk scheduler is also landed. Address-exact double
   compilation, streaming/sharded index maintenance, garbage collection, and
   cross-store scheduling remain later artifact and scalability stages; they are not
   prerequisites for eliminating transient producer names or rebuilding a
   changed graph in the current pipeline.

`synthAddr` and `memberAddr` therefore remain internal proof-stage labels, but
neither is emitted by the corresponding production address pass. The content-
addressing roadmap remains active for address-exact double compilation and
cross-store/sharded cache scaling, not for durable cache commits, the first
metadata-indexed per-key schedule, or exact
changed-graph rebuilding,
persistent checked cache ingress, the HPT semantic certificate, current
modeled-oracle coherence, IxIR₁ SCC integration, executable pipeline migration,
or certificate-level semantic transport. Future production extern
authorization remains a per-service ledger obligation rather than unfinished
content-addressing machinery.
