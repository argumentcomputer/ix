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
make another definition's arguments by name. So is which constants run as
fixed-width word primitives (SrcEval's rule F6w, stage W1 of
[DR2](data-and-roots-design.md#dr2-fixed-width-integers-and-int)): a
certificate's `word` entry is accepted only when the configuration enables
words (`Table.Config.words`, on by default since erasure emits the word primitive),
and then only at the operation's pinned
address with a stored theorem whose statement is the operation's equation
(`Table.checkWord`).

**The certificate's text.** `compile_parts` and its relatives relate the
certificate `produce` returns to `run`'s acceptance of it as a value. The
verifiers a user runs (`ixcc check-cert`, `compile --cert`, the claim
verifiers `CompileClaim.verifyBytes` and `Ring0Sip.verifyBytes`) read a
certificate from its text, with limits only that reader applies (64 MiB of
text, nesting 512, number tokens of 32 digits, and the decoders' limits:
[compiler design](compiler-design.md#middle-end-budgets), "Certificate text and
decode limits"). Since 2026-11-12 every producer reads its certificate back
from its file text through that reader before handing it on (`Cert.readBack`,
`RcReplay.Cert.readBack`), so `produce` returns the decoded certificate, and the
statements say so: `compileInput_text` (a successful `compileInput`'s producer
text is read by `Cert.ofText` as exactly the certificate `run` accepted) and
`producePlain_text` and `produceImmortal_text` (the same for the plain-RC and
immortal finishers, through `RcReplay.Cert.parse` and `Cert.ofText`), each with
the standard axioms. `ixcc compile` then runs `check-cert`'s verifier
(`Cli.checkText`: the reader, Stage A, the replay) on the text it is about to
write, takes the object from that verdict, and writes exactly that text
(`--emit-cert`; with `--cert`, the given file's text): the command line is IO
and no theorem covers it; `tests-cert-text` checks it on every committed root
under every mode. `CompileClaim.produce` returns the same text beside its
claim; the claim binds the object's hash, not the certificate.

The implementation composes `compile = ingress; produce; run`. Every address
IxCC computes is pure BLAKE3: `Address.blake3` is defined as `Address.blake3Pure`
(`Ixon/Hash.lean`), so no statement depends on foreign hash code. The hashing
boundaries are:

| Boundary | Current computation | Role |
| --- | --- | --- |
| `V3.decodeAnonymousEnv` | `Address.blake3Pure`, including the canonical constant-root Merkle fold and the role binding's section | Authenticating Ixon objects, blobs, the closure root and, in a role-bound envelope, the role table ([byte contract](byte-contract.md)); every record decoded by the kernel's canonical decoder and, as stored, bounded in depth (`V3.withinKernelDepth`: its expressions, shares expanded, at most 2,560; not the terms the kernel builds while typing), not by IxCC's consumer budget |
| `Src.KernelFront.accept` (in `Recheck.ingress`) | the certified kernel's tiered entry (`Ix.Kernel.Admission.checkBytesTieredUsing`) at IxCC's pure BLAKE3 (`KernelFront.hash`), with the artifact's own reducibility hints (advice about unfolding order; no guarantee depends on them) | The certified kernel's acceptance of the whole role-bound environment, every record reached or not: byte admission and authentication of every record and blob, the role table's admission, canonical decoding, the kernel's reader and verified fold over the logical records, the typing tier over the `partial` and `unsafe` definitions. Not optional; an unbound envelope is refused. Its accept gives, through the kernel's theorems, the reading's fidelity, a model and the strong model of the logical environment (`accept_spec`, `checkConstantsTiered_ok`) |
| `Src.Ingress.reach` and `Src.Ingress.readConsts` with `KernelFront.pinsOfTable`; `KernelFront.Reading.build` | `Address.blake3` (pure; the block-member keys `V3.*ProjAddr`, `Ixon/V3/Keys.lean`) | Reading only the records its seeds reach (every root the sidecar names, not only the chosen ones; the role table's pinned identities; the resource context's addresses; the equation theorems of the sidecar's proposals on reached subjects, read with their proofs; a theorem reached only as a constant read by its statement, `Src.Program.byStatement`), each within IxCC's consumer budget in what is read of it (refused with code `decode`, the record named); keying block members and constructors by their projection addresses (a projection record must be the alias of a member it keys); the pinned identities from the kernel's admitted role table; the program read against the kernel's reading (keys, addresses, declaration headers; refused with code `faithful`) |
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

Before the kernel, the envelope refuses a record it cannot authenticate or
the kernel's canonical decoder cannot decode, and a record nesting deeper than
the bound IxCC keeps ahead of the kernel: `ixcc: ingress: decode: ixon-v4: record ADDRESS nests
deeper than the kernel reads (2560, shares expanded)` (`V3.withinKernelDepth`:
every expression with its shares expanded; the kernel's acceptance recurses
natively on them and was measured to overflow a 2 MiB stack between 3,000 and
4,096 levels of one record and an 8 MiB one between 10,000 and 30,000). The
deepest records of real artifacts are far below it: 775 in IxCC's committed
closures, 325 in an Init+Std artifact, 1,221 in Mathlib (2026-11-12, shares
expanded). Universe depth is not bounded, as before. The bound keeps one
stored record within what the kernel survives; it does not make the kernel
safe. The kernel's canonical decoder runs before it and recurses on a record's
unshared nesting: a record nested about 30,000 deep without shares overflows a
2 MiB stack (about 100,000 on 8 MiB), as before ingress read only what its
seeds reach. And the kernel's conversion builds deeper terms than any stored
record: unfolding across records (about 4 records of 2,560 levels for 10,000 on
2 MiB) and shared chains can take it past its stack. Both are the kernel
package's to fix (the roadmap's "Hardening").

After the kernel, ingress reads the records its seeds reach
(`Src.Ingress.reach`, across every reference of what it reads), and refuses one
over IxCC's consumer budget (depth 256 with a `share` a leaf, 4,096 entries per
list) in what it reads: `ixcc: ingress: decode: ixon-v4: constant exceeds the
consumer budget (record ADDRESS, reached from …)`. The seeds (`Seeds.of`) are
exactly:

- every root the sidecar names, not only the roots a compile chooses with
  `--root` (so the program's numbering does not depend on the choice);
- the constants the kernel's admitted role table binds to the identities IxCC
  pins (`Nat` and its constructors and recursor, `Bool`, `Eq`, the `Decidable`
  constructors, the `Nat` primitives, the three standard axioms);
- every address the resource context names;
- read with their proofs: the resource context's equation theorems, and the
  equation theorem of every sidecar proposal whose subject is reached; what
  their proofs reach is read with proofs too.

Any other theorem reached is read by its statement (its type; its proof is not
read and what only the proof names is not reached). A record none of the seeds
reaches is not read, so it cannot refuse the artifact by IxCC's limits (only by
the kernel's). The seeds are wider than the target: a record over the budget
that another root of the sidecar reaches, or that a proposed equation's proof
uses, refuses every compile of the artifact with that sidecar, whichever roots
are chosen (`tests-recheck`, `Reach.seeds`).

Consequences, each a difference from the reader before 2026-11-12, which read
every record:

- **Table entries name only theorems read with their proofs.** `Table.checkEqn`,
  `checkCsimp` and `checkWord` refuse a theorem read by its statement, so an
  `eqn`, `csimp` or `word` entry, the producer's or a certificate's, is accepted
  only for a theorem that a proposal of the sidecar names (or a resource
  equation). The `ixcc/k1-equations/1` sidecar carries `eqn` proposals and, in
  its optional `theorems` list, `word` proposals only, so no certificate
  with a `csimp` entry verifies from a sidecar today (the roadmap's "csimp
  proposals"). A proposal whose subject is not read (not reached, or not in the
  artifact) gives the hint diagnostic `… is not in the program read` and no entry.
- **A root, a resource address or a proposal named by a projection address
  whose record the artifact does not store is not read**: ingress follows only
  records the artifact stores, and reaches a block member through its
  projection record. Such a root is refused: `ixcc: ingress: ingress: src
  ingress: root ADDRESS is not a record the artifact stores (…)`; such a
  resource address is "absent from the closure", such a proposal dropped. The
  reader before laid out every block and keyed its members whether or not their
  projection records were stored. `ix compile` stores one for every member and
  constructor (measured 2026-11-12 on IxCC's committed closures, the probes'
  artifacts, Init+Std and Mathlib: every block, every projection record), so
  this is a requirement on artifacts ([byte contract](byte-contract.md)), not a
  loss on any artifact `ix compile` writes.
- **A claim is verified with the sidecar it was produced with.** The program's
  constants and their numbering (`CId`s, which the certificate's table and
  relevance annotation name) depend on the records read, so on the whole
  sidecar: its roots and its proposals. A verifier given the same artifact and
  claim with a sidecar that names other roots or other proposals reads another
  program and refuses the claim with a certificate failure that does not say
  why (`tests-recheck`, `Reach.tamperedSidecar`, `Reach.verifierSidecar`). The
  claim does not bind the sidecar (it carries no hash of it); binding it is
  not done.

IxCC's own admission then refuses per root, with the
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
