# The boundary between `compile` and the proved rechecker

`Recheck.sound` concerns a successful `Recheck.run cfg P cert`, where `P`
is already a Src program. It preserves the source evaluator's behavior
through the checked compiler pipeline. It does not state that arbitrary Ixon
bytes denote that Src program in the certified kernel's model. The existing
`compile_sound` and `compile_safe` names also have recheck-path premises;
their names do not supply a theorem about the `Recheck.compile` definition.

The separate [compiler bridge](../IxCC/Recheck/Proof/Compile.lean) now
proves that a successful actual `compile` returns an artifact accepted by
`run`. `compile_parts` records the exact successful ingress, producer and replay,
including `cfg.forInput` and the returned certificate. `compiled_sound` derives
the existing return, safe-source and divergence guarantees for that emitted
object. `compile_bytes` identifies the returned bytes with the replayed object.
These statements remain relative to the checked source stored in the artifact;
they do not identify its denotation with a certified kernel environment. Nor do
they relate that checked source semantically to the ingested program: the front
end (`Table.ofCert`, the relevance annotation and its checks, `Lazify.run`)
builds it, and the theorems state that the front end ran and how, not what it
preserves (open item S6 in the [certification design](certification-design.md)).

The implementation composes `compile = ingress; produce; run`. Every address
IxCC computes is pure BLAKE3: `Address.blake3` is defined as `Address.blake3Pure`
(`Ixon/Hash.lean`), so no statement depends on foreign hash code. The hashing
boundaries are:

| Boundary | Current computation | Role |
| --- | --- | --- |
| `V3.decodeAnonymousEnv` | `Address.blake3Pure`, including the canonical constant-root Merkle fold and the role binding's section | Authenticating Ixon objects, blobs, the closure root and, in a role-bound envelope, the role table ([byte contract](byte-contract.md)) |
| `Src.Ingress.ofEnv` | `Address.blake3` (pure; the block-member keys `V3.*ProjAddr`, `Ixon/V3/Keys.lean`) | Keying block members and constructors by their projection addresses; a projection record must be the alias of a member it keys |
| `V3.Tc.checkEnv` | `Address.blake3` (pure) for addresses; `Blake3.Rust.Hasher` for internal keys | Rechecking materialized object/blob hashes and constructing projection addresses (pure); expression/universe node, context and reduction-cache keys (the Rust hasher: internal hash-consing keys of the erased checker, not addresses anything names) |
| `Recheck.produceWith` relevance annotation; `Recheck.checkCanonicalRelevance` | The same erased typechecker's expressions and conversion | In `produce`, a proposal the relevance checks then decide. On the byte-level verifiers (`CompileClaim.verifyBytes`, `Ring0Sip.verifyBytes`, `ixcc check-cert`) `checkCanonicalRelevance` re-runs `Src.Relevance.annotate` on `(inp.env, cert.table)` and requires the certificate's annotation to equal its output, so the annotator is on their acceptance path. It has no correctness theorem: S1's closure on those paths rests on it annotating honest programs correctly |
| `Src.Resource.validateContext` | `Address.blake3Pure` plus the codec's pure framing operations | Binding raw effective profile bytes and checked equation selections to actual Src declarations; no resource-safety claim |
| Separate `V3.validate` / resource-claim API | Resource profile, object and claim commitments (pure), plus erased typing | Diagnostic addressed admission; not called by `Recheck.compile` or assumed by `Recheck.sound` |

The erased typechecker's remaining native call sites (its incremental hasher for
internal keys) are in `Ixon/V3/Tc/{Expr,Level,Metadata,Monad,Inductive,Support}.lean`;
`Support.finishHash` constructs its length proof explicitly, so no theorem
depends on the Blake3 package's `native_decide` length proof. A collision among
those keys can only change the checker's verdict, which no theorem uses. The
resource API hashes profiles and addressed objects in
`Ixon/V3/Resource/Addressed.lean` with the same pure function. Importing such a module is different from
calling that API: neither should be reported as a resource gate in `compile`.

Resource-selection checking adds a pure codec/hash dependency to the recheck
path. This is a check over supplied data. It preserves the existing theorem
statements and does not add a trusted resource verdict or an assumption about
scalar ownership crossing. Profiles enabling the new scalar exemption are
declined by this consumer until its representation condition is established.

The 2026-10-04 declaration audit reported only `propext`, `Classical.choice`
and `Quot.sound` for `Recheck.run` and `decodeAnonymousEnv`; `Address.blake3Pure`
uses `propext` and `Quot.sound`. `Tc.checkEnv`, `Recheck.ingress`, `produce`,
`compileInput`, `compile` and the separate resource validator used to reach
`Blake3.HasherOps.hash._native.native_decide.ax_1`, a `native_decide` proof of
`32 < 2 ^ System.Platform.numBits` inside the Rust hash's `HasherOps.hash`;
since every address became pure BLAKE3 (2026-11-10) none of them does.

The exact [compiler-bridge fences](../IxCCTests/Fences/Compile.lean)
record only `propext`, `Classical.choice`, and `Quot.sound` for program-level
soundness theorems (`Recheck.sound_of_eval`, `verifyProgram_*_sound`,
`verifyRing0Sip_sound`) and, since every address is pure BLAKE3, for the
byte-level and ingress-calling theorems too (`compile_sound`, `verifyBytes_*_sound`,
`verifyBytesRing0Sip_sound`); the replay fences are unchanged. The guarantees
retain `X86.Driver.Ok` and the source `GoesWrong` qualification. On the
immortal and zero-RC paths the root checks (`checkImmortalRoot`) narrow its
view-rejection case: at the claim's root the view accepts every result of the
shape the root's declared type describes (`Recheck.ResultShape`), so that case
means a result off the shape (`verifyProgram_immortal_rootShape`,
`verifyBytes_immortal_rootShape` and their `.zeroRc` forms). Erasure gives
every constructor a root's result can hold a row in the constructor table, so
a root compiled alone has a complete readback signature (`Recheck.Front.boolRows`
for the pinned `Bool`). The same guarantees stated with the shape view
(`Recheck.Front.shapeView`, the view restricted to the root's result shape)
have a view-rejection case that is exactly a result off the shape
(`Recheck.ShapeClaim`, `verifyProgram_immortal_shape`,
`verifyBytes_immortal_shape` and their `.zeroRc` forms); the view itself also
relabels, by table tag, a constructor of another type. On the plain-RC path
(`checkPlainRcRoot`) the view accepts every constructor tree of the root's
declared first-order type, so its view-rejection case means a result off that
shape (`Recheck.PlainShape`, `verifyProgram_plainRc_rootShape`,
`verifyBytes_plainRc_rootShape`). The stuck and trap cases remain, and
nothing proves that SrcEval returns a result of the shape: that is type
preservation for SrcEval, which is not proved. The guarantees apply to
both choices of the compiler's `typecheck` flag; neither choice supplies the
missing model-adequacy proof. Pure hashing on the verifier path does
not by itself prove source adequacy.

The stronger theorem relating an input closure to the certified kernel's
model is planned as the grounded statement of
[end-to-end certification](end-to-end.md). It takes as premises that IxCK
accepts the environment with the claim's root address and that the checked
source program is faithful to IxCK's reading of it, both discharged outside
IxCC (by IxVM proofs or a native kernel run), and adds the unfolding table's
validity in the model and SrcEval's adequacy with progress
([certification design](certification-design.md)). IxCC's own type checking
contributes nothing to it. This boundary does not assert that theorem or
weaken any existing fence to accommodate it.
