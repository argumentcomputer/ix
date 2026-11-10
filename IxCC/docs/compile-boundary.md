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

The implementation composes `compile = ingress; produce; run`. The current
hashing boundaries are:

| Boundary | Current computation | Role |
| --- | --- | --- |
| `V3.decodeAnonymousEnv` | `Address.blake3Pure`, including the canonical constant-root Merkle fold | Authenticating Ixon objects, blobs and the closure root |
| `V3.Tc.checkEnv` | `Address.blake3` and `Blake3.Rust.Hasher` | Rechecking materialized object/blob hashes; constructing projection addresses, expression/universe nodes, context and reduction-cache keys |
| `Recheck.produceWith` relevance annotation; `Recheck.checkCanonicalRelevance` | The same erased typechecker's expressions and conversion | In `produce`, a proposal the relevance checks then decide. On the byte-level verifiers (`CompileClaim.verifyBytes`, `Ring0Sip.verifyBytes`, `ixcc check-cert`) `checkCanonicalRelevance` re-runs `Src.Relevance.annotate` on `(inp.env, cert.table)` and requires the certificate's annotation to equal its output, so the annotator is on their acceptance path. It has no correctness theorem: S1's closure on those paths rests on it annotating honest programs correctly |
| `Src.Resource.validateContext` | `Address.blake3Pure` plus the codec's pure framing operations | Binding raw effective profile bytes and checked equation selections to actual Src declarations; no resource-safety claim |
| Separate `V3.validate` / resource-claim API | Native resource profile, object and claim commitments, plus erased typing | Diagnostic addressed admission; not called by `Recheck.compile` or assumed by `Recheck.sound` |

The erased typechecker's direct native call sites are in
`Ixon/V3/Tc/{Ingress,Expr,Level,Metadata,Monad,Inductive,Support}.lean`.
`Support.finishHash` constructs its length proof explicitly; that does not
replace the foreign hash implementation or prove its refinement. The existing
resource API still hashes profiles and addressed objects in
`Ixon/V3/Resource/Addressed.lean`. Importing such a module is different from
calling that API: neither should be reported as a resource gate in `compile`.

Resource-selection checking adds a pure codec/hash dependency to the recheck
path. This is a check over supplied data. It preserves the existing theorem
statements and does not add a trusted resource verdict or an assumption about
scalar ownership crossing. Profiles enabling the new scalar exemption are
declined by this consumer until its representation condition is established.

The 2026-10-04 declaration audit reports only `propext`, `Classical.choice`
and `Quot.sound` for `Recheck.run`. `decodeAnonymousEnv` has that same set;
`Address.blake3Pure` uses `propext` and `Quot.sound`. `Tc.checkEnv`,
`Recheck.ingress`, `produce`, `compileInput`, `compile`, and the separate
resource validator also reach
`Blake3.HasherOps.hash._native.native_decide.ax_1`. This is an inventory of
existing dependencies, not a new axiom or an assumption added to `run`.

The exact [compiler-bridge fences](../IxCCTests/Fences/Compile.lean)
record only `propext`, `Classical.choice`, and `Quot.sound` for program-level
soundness theorems (`Recheck.sound_of_eval`, `verifyProgram_*_sound`,
`verifyRing0Sip_sound`), and additionally record the existing
`Blake3.HasherOps.hash._native.native_decide.ax_1` dependency for byte-level
and ingress-calling theorems (`compile_sound`, `verifyBytes_*_sound`,
`verifyBytesRing0Sip_sound`). Mentioning the
actual ingress/producer in these statements exposes that dependency; no native
axiom declaration was added and the replay fences are unchanged. The guarantees
retain `X86.Driver.Ok` and the source `GoesWrong` qualification. On the
immortal and zero-RC paths the root checks (`checkImmortalRoot`) narrow its
view-rejection case: at the claim's root the view accepts every result of the
shape the root's declared type describes (`Recheck.ResultShape`), so that case
means a result off the shape, or, on the pinned-`Bool` route, a pinned `Bool`
constructor with no row in the constructor table
(`verifyProgram_immortal_rootShape`, `verifyBytes_immortal_rootShape` and their
`.zeroRc` forms). The stuck and trap cases remain, and nothing proves that
SrcEval returns a result of the shape. The guarantees apply to
both choices of the compiler's `typecheck` flag; neither choice supplies the
missing model-adequacy proof. Eliminating native hashing from ingress would not
by itself prove source adequacy.

The stronger theorem relating an input closure to the certified kernel's
model additionally needs authenticated decoding, accepted environment typing,
the intended equation/table interpretation and the Src evaluator's adequacy.
Those obligations belong to the staged certified-kernel integration. Phase
1.5 scopes this work; it does not assert that theorem or weaken any existing
fence to accommodate it.
