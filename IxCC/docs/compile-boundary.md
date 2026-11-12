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
Which arguments the checked source passes by name is part of what it ran: the
table's `lazy` rows, which `Table.ofCert` accepts only for a pinned row or a
sparse casesOn at its binder count without a `resolve` entry (`Table.checkLazy`,
`Table.lazyResolveOk`), so a certificate cannot
make another definition's arguments by name.

The implementation composes `compile = ingress; produce; run`. Every address
IxCC computes is pure BLAKE3: `Address.blake3` is defined as `Address.blake3Pure`
(`Ixon/Hash.lean`), so no statement depends on foreign hash code. The hashing
boundaries are:

| Boundary | Current computation | Role |
| --- | --- | --- |
| `V3.decodeAnonymousEnv` | `Address.blake3Pure`, including the canonical constant-root Merkle fold and the role binding's section | Authenticating Ixon objects, blobs, the closure root and, in a role-bound envelope, the role table ([byte contract](byte-contract.md)) |
| `Src.KernelFront.accept` (in `Recheck.ingress`) | the certified kernel's tiered entry (`Ix.Kernel.Admission.checkBytesTieredUsing`) at IxCC's pure BLAKE3 (`KernelFront.hash`), with the artifact's own reducibility hints (advice about unfolding order; no guarantee depends on them) | The certified kernel's acceptance of the whole role-bound environment, every record reached or not: byte admission and authentication of every record and blob, the role table's admission, canonical decoding, the kernel's reader and verified fold over the logical records, the typing tier over the `partial` and `unsafe` definitions. Not optional; an unbound envelope is refused. Its accept gives, through the kernel's theorems, the reading's fidelity, a model and the strong model of the logical environment (`accept_spec`, `checkConstantsTiered_ok`) |
| `Src.Ingress.readConsts` with `KernelFront.pinsOfTable`; `KernelFront.Reading.build` | `Address.blake3` (pure; the block-member keys `V3.*ProjAddr`, `Ixon/V3/Keys.lean`) | Keying block members and constructors by their projection addresses (a projection record must be the alias of a member it keys); the pinned identities from the kernel's admitted role table; the program read against the kernel's reading (keys, addresses, declaration headers; refused with code `faithful`) |
| `Recheck.produceWith` relevance annotation; `Recheck.checkCanonicalRelevance` | the certified kernel's executed core over the accepted environment (`KernelFront.Kernel.annotateChecked`: inference, conversion, weak head normalisation and the annotation pass, each asked of the kernel's own term at the position IxCC's term occupies, with IxCC's term checked to correspond) | In `produce`, a proposal the relevance checks then decide. On the byte-level verifiers (`CompileClaim.verifyBytes`, `Ring0Sip.verifyBytes`, `ixcc check-cert`) `checkCanonicalRelevance` re-runs the kernel annotator on `(inp.kernel, cert.table)` and requires the certificate's annotation to equal its output (Stage A). Each class it gives is the kernel core's answer at that position and conversely (`KernelFront.Ctx.classify*_proof`, `_of_runs`); the composition of those runs into typing derivations at the evaluated positions is planned ([kernel front end](kernel-front-end-design.md)) |
| `Src.Resource.validateContext` | `Address.blake3Pure` plus the codec's pure framing operations | Binding raw effective profile bytes and checked equation selections to actual Src declarations; no resource-safety claim |
| Separate `V3.validate` / resource-claim API | Resource profile, object and claim commitments (pure); no typing (on every compile path the kernel's acceptance runs before resource admission) | Diagnostic addressed admission; not called by `Recheck.compile` or assumed by `Recheck.sound` |

**What ingress refuses, and how.** The certified kernel's acceptance is of the
whole artifact, so a record the kernel does not accept refuses every root of
the artifact, reached or not. Its refusal is `ixcc: ingress: kernel: kernel
front end, STAGE (CLASS): REASON`, exit status 1, where `STAGE` is the
kernel's (`envelope`, `bytes`, `binding`, `coverage`, `prelude`, `read`,
`kernel`) and `CLASS` its classification: *rejected* where the input is shown
wrong, *declined* otherwise. In particular:

- an unbound closure (`0xE4`): `envelope`, "the kernel admits only role-bound
  environments (0xE5); this one is unbound";
- an ill-typed record: `kernel` (declined), a type mismatch or a "function
  expected": the kernel does not take a failed conversion search as evidence
  that the input is wrong, so it declines rather than rejects;
- **any axiom other than `propext`, `Classical.choice` and `Quot.sound`, and
  any use of `sorryAx`, anywhere among the records**: `kernel` (declined),
  "non-standard axiom" at the axiom's record, or, for `sorryAx` (which the
  kernel installs nothing for), at the first record using it. Before the
  switch IxCC refused only a target that reached such an axiom relevantly
  (`Src.Admit`'s `relevant-axiom`); now the whole artifact is declined. That
  is the right verdict: an environment holding an arbitrary axiom (or a proof
  by `sorry`) may be inconsistent, so it has no model, and nothing IxCC would
  say about a program read from it could be grounded in the kernel's model.
  For these two, after the kernel's own line (`not implemented yet: use of the
  sorryAx axiom …`, `not implemented yet: non-standard axiom …`), `ixcc` prints
  one more line in plain words: that the artifact holds a `sorry` (or an axiom
  other than the standard three) somewhere among its records, that the kernel
  accepts an artifact only whole, and that this section explains it
  (`KernelFront.PolicyDecline`, told apart by the kernel's `notImplemented`
  failure and its message's leading prose part).

After the kernel, IxCC's own admission still refuses per root, with the
reference path from the root (`Src.Admit`, stage `admit`): a relevant
theorem, a relevant standard axiom (`Classical.choice` through
`Classical.propDecidable`, `propext`), a reached `partial` or `unsafe`
definition (the kernel types it and keeps it opaque, outside the logical
environment), an opaque outside the allowlist, a relevant type, a string
literal, a budget.

IxCC's erased type checker, with the native hasher it used for its internal
keys, was deleted by the switch to the kernel front end (step 4); no IxCC
module imports the Blake3 package's Rust interface. The
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
preservation for SrcEval, which is not proved. The byte-level guarantees
hold of every input ingress accepts, and ingress always runs the certified
kernel's acceptance (there is no unchecked mode); the acceptance does not
supply the missing model-adequacy proof, and it is not the grounded
statements' first premise, which is about the closure of the seeds under the
default table and the committed prelude ([kernel front end](kernel-front-end-design.md#acceptance)). Pure hashing on the verifier path does
not by itself prove source adequacy.

The stronger theorem relating an input closure to the certified kernel's
model is planned as the grounded statement of
[end-to-end certification](end-to-end.md). It takes as premises that IxCK
accepts the environment with the claim's root address and that the checked
source program is faithful to IxCK's reading of it, both discharged outside
IxCC (by IxVM proofs or a native kernel run), and adds the unfolding table's
validity in the model and SrcEval's adequacy with progress
([certification design](certification-design.md)). IxCC's erased type
checker, which the switch deleted, contributed nothing to it. This boundary does not assert that theorem or
weaken any existing fence to accommodate it.
