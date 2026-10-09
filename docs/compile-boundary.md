# The boundary between `compile` and the proved rechecker

`Recheck.sound` concerns a successful `Recheck.run cfg P cert`, where `P`
is already a Src program. It preserves the source evaluator's behavior
through the checked compiler pipeline. It does not state that arbitrary Ixon
bytes denote that Src program in the certified kernel's model. The existing
`compile_sound` and `compile_safe` names also have recheck-path premises;
their names do not supply a theorem about the `Recheck.compile` definition.

The implementation composes `compile = ingress; produce; run`. The current
hashing boundaries are:

| Boundary | Current computation | Role |
| --- | --- | --- |
| `V3.decodeAnonymousEnv` | `Address.blake3Pure`, including the canonical constant-root Merkle fold | Authenticating Ixon objects, blobs and the closure root |
| `V3.Tc.checkEnv` | `Address.blake3` and `Blake3.Rust.Hasher` | Rechecking materialized object/blob hashes; constructing projection addresses, expression/universe nodes, context and reduction-cache keys |
| `Recheck.produceWith` relevance annotation | The same erased typechecker's expressions and conversion | An untrusted oracle whose output is checked by the relevance checker |
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

A separate theorem about `compile` should first expose its composition:
success yields an ingested program and a certificate for which `run` succeeds.
It can then apply the existing recheck theorem relative to that program. Its
axiom fence must report the actual reachable dependency set, including any
native dependency in the statement, rather than silently copying `run`'s
fence. Eliminating native hashing from ingress does not prove source adequacy.

The stronger theorem relating an input closure to the certified kernel's
model additionally needs authenticated decoding, accepted environment typing,
the intended equation/table interpretation and the Src evaluator's adequacy.
Those obligations belong to the staged certified-kernel integration. Phase
1.5 scopes this work; it does not assert that theorem or weaken any existing
fence to accommodate it.
