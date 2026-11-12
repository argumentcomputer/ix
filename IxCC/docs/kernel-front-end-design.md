# The front end over the certified kernel

Written 2026-11-11. **Status:** decided by the owner: IxCC takes its type
information and its acceptance of an environment from the certified kernel
(the `IxCK/` package), and its own erased type checker is deleted. The
front end over the kernel (`IxCC.Src.KernelFront`,
[`Src/KernelFront`](../IxCC/Src/KernelFront), and `Recheck.ingress`) **is the
only front end** since the switch's step 3 ([The switch](#the-switch)): every
compile path's ingress is the kernel's acceptance and every annotation the
kernel annotator's. Step 4 deleted the earlier front end: the earlier
annotator, with `tests-kernel-front`'s comparison, which found the two
annotators equal on every committed closure, IxCC's catalog support, the
erased checker, the unbound environment's reading, IxCC's binding decoder and
the Rust hasher's import. The kernel's fix of its
blow-up on chains of `let`, made in parallel in the kernel package on this
branch, has landed ([resource bounds](#resource-bounds),
[decisions](#decisions)). This is most of the native
discharge of the premises in the [roadmap](roadmap.md#milestones) (SP-N): the
faithfulness check and the source of the typing derivations; the first
premise as restated on 2026-11-11 needs one more kernel run, on the closure
of the seeds ([below](#acceptance)). It is also the part of HD-1 that takes
typing off IxCC's own code.

## Current state

Before the switch, IxCC's front end read an `.ixe` environment with its own
decoder (`V3.decodeAnonymousEnv`), converted it into the table-free
`Src.Program` (`Src.Ingress.readConsts`), and asked its own erased type checker
(`IxCC/IxCC/Ixon/V3/Tc/`, 24 files, 12,680 lines, adapted from an earlier
Ixon checker of ix, with no soundness theorem) two kinds of question (the
table below is that state; since step 3 each row's last column is what the
kernel front end does instead, [below](#what-each-use-of-the-erased-checker-becomes)):

| Use | Question | Where | What rests on the answer |
| --- | --- | --- | --- |
| `Tc.checkEnv` | accept every declaration of the closure | `Recheck.ingress` when its `typecheck` flag is set, hence every byte-level verifier (`CompileClaim.verifyBytes`, `checkClaim`, `makeClaim`, `Ring0Sip.verifyBytes`), `ixcc compile` and `check-cert`; also `Src.load`, catalog admission, the resource-validation API and the census | nothing proved: the byte-level theorems carry only `typecheck = true → Tc.checkEnv inp.env = .ok ()` and hold with typing off |
| `Src.Relevance.annotate` | the type of a subterm in a context of opened binders; whether a type reduces to a Π-telescope ending in a sort; the sort of a type and its zero condition over the constant's universe parameters (D18) | the producer, and through Stage A (`Recheck.checkCanonicalRelevance`: the certificate's annotation must equal the annotator's) every byte-level verifier | an untrusted oracle: the recheck path decides the annotation (`Relevance.check`, `checkCanonical`); under the [end-to-end plan](end-to-end.md) it is the relevance clause of the faithfulness premise |
| not typing (moved out of `Tc` by the switch's step 2) | block-member keys (now `V3.*ProjAddr`, [`Ixon/V3/Keys.lean`](../IxCC/Ixon/V3/Keys.lean), pure BLAKE3 like every address IxCC computes), the `Nat` literal bytes and address order and hexadecimal reading (`V3.natFromBytesLE`, `Address.cmpBytes`, `Address.fromString`, [`Ixon/V3/Support.lean`](../IxCC/Ixon/V3/Support.lean)), the primitive table (`V3.PrimAddrs.canonical`, [`Ixon/V3/PrimAddrs.lean`](../IxCC/Ixon/V3/PrimAddrs.lean)) | ingress, the pinned identities, the sidecar's reader, the resource profile's literal pins and its `Eq` | — |

The recheck path (`Recheck.run` and everything it reaches) runs no typing:
it takes a `Src.Program` and checks the certificate's choices syntactically.

On the role-bound closures `ix compile` writes, the certified kernel checks
every record, with real bodies, in about a second and a quarter of a
gigabyte, where the erased checker takes three to four minutes and a gigabyte
(2.5 MB closures of about 3,600 records: the kernel 1.3–1.7 s and about
220 MB; the erased checker 169–231 s and 1.0–1.1 GB;
[measurements](#measurements)). The erased checker is the dominant cost of
every byte-level verifier ([hardening design](hardening-design.md)).

## What the kernel offers

- **Acceptance.** The kernel's entries take records, blobs and a role binding
  already split, and an explicit content hash (`IxCK/Kernel/Admission.lean`).
  The whole-artifact entry is the *tiered* one
  (`Ix.Kernel.Admission.checkBytesTieredUsing`,
  `IxCK/Kernel/Admission/Tier.lean`): byte admission of every record, the role
  table's admission, canonical decoding, then the partition of the records into
  logical ones and the `partial` and `unsafe` definitions Lean's compiler adds
  (the *typing tier*), the logical entry `checkConstantsWith` (the kernel's
  reader, then the verified fold `Ix.Kernel.Cached.checkDecls .verified`) over
  the logical records, and the typing tier over the others, every tier constant
  opaque and absent from the logical environment, and no logical record naming
  one (the *fence*). Its theorems
  (`IxCK/Kernel/Admission/TierTheorems.lean`): an accept is
  `checkConstantsWith`'s accept of the logical records, so every theorem about
  that entry applies to the logical environment as stated
  (`checkConstantsTiered_ok`): the reading's fidelity to the bytes
  (`Installed`, `checkConstantsWith_installed`), a model
  (`checkConstantsWith_has_model`), the strong model through the fold's accept
  (`checkConstantsWith_checkDecls`, then `Ix.Kernel.Cached.checkDecls_strongModel`,
  `IxCK/Kernel/Ixon/Values.lean`), and the environment's well-formedness
  (`EnvWF`). The logical entry alone (`checkBytes`, `checkBytesWith`) declines
  every closure `ix compile` writes, because each holds tier records.
- **Questions about open terms.** The executed core
  (`Ix.Kernel.Cached.coreKnotI .verified`, `IxCK/Kernel/Cached/CoreC.lean`)
  over an accepted environment's index answers inference, conversion, weak head
  normalisation and the annotation pass on terms whose free variables are
  typed (`.fvar i ty`, `i` below the depth), with memo tables in a state
  threaded through the calls, and a fuel that bounds each call's recursion.
- **What is proved about those answers.** The cached core simulates the fueled
  specification functions from any invariant state (`Ix.Kernel.Cached.ssimC`,
  `IxCK/Kernel/Verify/Cached/KnotC.lean`; the empty state is invariant,
  `CSOK.empty`); an accepting run of the specification yields a derivation of
  the relational judgements (`inferTypeCore_bridge`, `whnf_bridge`,
  `IxCK/Kernel/Verify/Rules/Bridge.lean`: `Infer env .full d e t`,
  `Red env d e e'`), for open terms at any depth; and every derivation is sound
  in every model meeting `RulesInputs` (`infer_sound`, `red_sound`,
  `IxCK/Kernel/Model/Rules/Sound.lean`), which a strong model of an accepted
  environment supplies (`Rules.RulesInputs.ofSem`,
  `IxCK/Kernel/Model/Capstone.lean`). `InferSem` says that, for every valuation
  of the context, the term's denotation is a member of its type's.

## The representation question

IxCC's terms and the kernel's are read from the same Ixon expressions by two
conversions that are the same structural function on every node (IxCC's
`Src.Ingress.convH`, the kernel's `Ix.Kernel.Reader.convExpr`), except in how
a constant is named. Above the terms the two readings differ:

| | IxCC's reading | The kernel's reading |
| --- | --- | --- |
| constants | dense `CId`s, in address order, a block laid out member by member then constructor by constructor | keys: a role key (`.role r`) where the role table binds the constant's reference, its address otherwise; a block member by its projection record's address |
| blocks | as stored | an inductive block regrouped into one declaration with its recursors; a definition block ordered by its `recur` references |
| counts | each recursor's parameters, motives, minors and indices; `k`; each constructor's index | only the sums the fold needs (`majorIdx`, `rulePrefix`); `k` computed at install |
| universes | the record's variable `i` is parameter `i` | the same, except a large eliminator's: its parameters are `n :: [0, …, n-1]` (`Reader.recLps`) |
| `let` | kept | kept by the reader; the annotation pass, which the fold runs on every declaration, substitutes every `let` away, so the installed values are `let`-free |
| nested and mutual inductives | as stored | the reader's in-process modeller adds auxiliary declarations, and rewrites the projection functions of a modelled structure into recursor form (`projRewrite`) |
| `partial` and `unsafe` definitions | ordinary constants, refused by `Src.Admit` when reached | the typing tier: typed, opaque, not in the logical environment |
| pinned identities | `Src.Pins`, from the role table | role keys |

So a position in IxCC's term is a position in the kernel reader's term (the
same node), but not in general a position in the *installed* declaration (the
`let`s are gone), and a kernel declaration does not carry everything IxCC's
program needs.

## Two shapes

**A. The kernel's reading throughout.** The program is translated from the
kernel's declarations: keys to `CId`s, role keys to pins, the modeller's
auxiliaries to Src constants or a decline, and relevance asked of the
translated positions.

**B. IxCC's reading, every question asked of the kernel's reading.** The
program is IxCC's reading, unchanged; the kernel accepts the same bytes; the
program is checked against the reading the kernel accepted (keys, addresses,
declaration headers, and the terms node for node wherever the program reads
them); and every relevance question is asked about the kernel reader's own
subterm at the position IxCC's term occupies.

| Criterion | A | B |
| --- | --- | --- |
| The faithfulness premise's term clause | true by construction for what the translation covers | checked: a decidable correspondence (`corr`) at every position the source evaluator evaluates and every type the program reads; a mismatch refuses |
| What the translation must reconstruct | the constant numbering and block layout, the recursor counts and `k`, the Src universe numbering of large eliminators, the `partial` and `unsafe` constants (absent from the logical environment): all from the Ixon records, so IxCC decodes them anyway | nothing; a key map and a universe renaming, both read from the kernel's own context |
| `let` | from the installed values, the program loses its `let`s and takes the annotation pass's substitution as its terms (its tree can be exponential in the record); from the reader's declarations, A is B's conversion with kernel keys | kept, as SrcEval evaluates them; the annotator reduces them as the kernel's annotation pass does when it asks |
| Nested and mutual inductives | auxiliaries become Src constants SrcEval does not know, or the block declines; rewritten projection functions change the program | IxCC's reading; the correspondence fails, and the program is refused, only where a runtime term is a rewritten projection function |
| Projections, literals, pins, role keys | translated | compared (`corr`), pins taken from the kernel's admitted table |
| What adequacy consumes | kernel typing facts about the translated positions | kernel typing facts about the kernel's own subterms at exactly the positions SrcEval evaluates, plus the correspondence as a checked proposition |
| Change to the program, the certificates and the objects | the numbering, the layout and the universes of large eliminators move: certificates and objects change | none: the program is the same function of the bytes |
| Size | the translation (3–6k lines by the earlier estimate) and its proofs, plus the risk above | the correspondence (about 300 lines), the annotator (about 400), the entry's preparation (about 450) |

**Recommendation: B.** It gives the adequacy proof what it consumes (facts
about the kernel's terms at the evaluated positions, and a decidable
correspondence it can take as a hypothesis discharged by the check), at a
fraction of A's size and with none of its changes to the program. A's one
advantage, correspondence by construction, holds only for the parts the
translation covers, and the rest of the program (numbering, layout, counts,
tier constants) comes from the Ixon records in either shape. B keeps IxCC's
decoder and conversion on the verifier path, so there are two readings of the
records; the correspondence is what makes them one at every position that
matters. It is the native check of the faithfulness clauses against the
kernel's reading, which the open decision on how faithfulness is discharged
(DO-6) lists as its third option; that decision's default for the native path
was the rebuilt ingress (A). B is the working default, awaiting the owner's
confirmation ([decisions](#decisions)).

## The design

### Acceptance

`KernelFront.accept` ([`Accept.lean`](../IxCC/Src/KernelFront/Accept.lean))
takes the environment IxCC decoded (its framing of the envelope; the kernel
package frames none) and hands the kernel's tiered entry exactly its records
and blobs, byte for byte, with its binding section:

1. `prepare` (untrusted): the role table admitted by the kernel
   (`admitBinding`), the records decoded by the kernel's canonical decoder,
   every bound role checked to designate a member of the closure, the
   artifact's own prelude records read by the kernel's reader under the
   artifact's table and checked against the pinned prelude shape, and the
   records in the kernel's check order (`Order.wholeEnv`, a port of ix's own
   whole-environment order: the prelude's records first, then a dependency
   order over references, the certified `Nat` operations' certificate ground
   and the literal edges). A wrong order is a decline at the entry, never an
   acceptance.
2. `acceptPrepared`: refuses unless the prepared binding is the envelope's and
   the ordered records, sorted by address, are the envelope's records; runs
   `checkBytesTieredUsing` at IxCC's pure BLAKE3 (`hash`), the artifact's
   prelude, IxCC's decoder caps as batch limits (`defaultLimits`) and the
   artifact's own reducibility hints (`HintTable.of`, below); and keeps the
   kernel reader's declarations of the same inputs with the same hints (the
   logical ones behind the prelude, and the tier reader's), which the annotator
   asks about.

A refusal carries the kernel's reason and classification (rejected or
declined, `TierError.outcome`). Only role-bound environments are accepted.
The acceptance is of the whole artifact: a record the kernel does not accept
refuses every root, reached or not. IxCC's own reading is of the records its
seeds reach (every root the sidecar names, the pinned identities, the resource
context's addresses, and the equation theorems of the proposals on reached
subjects; [below](#the-program-and-its-correspondence)), so its limits refuse
an artifact only where one of those reaches a record past them. An ill-typed record is *declined*, not
rejected (the kernel does not take a failed conversion search as evidence
that the input is wrong), and so is any axiom other than `propext`,
`Classical.choice` and `Quot.sound`, and any use of `sorryAx` (the kernel
installs nothing for it), anywhere among the records: such an environment may
be inconsistent, so it has no model, and nothing about a program read from it
could be grounded. What a user sees is in the [compile
boundary](compile-boundary.md).
`ix check-lean` admits a role-bound artifact by the same entry, prelude source
and order; the front end's acceptance differs from it only in the hash
function's implementation (IxCC's pure BLAKE3, ix's Rust BLAKE3 on a recorded
assumption that the two agree).

**Reducibility hints.** The envelope's hints section (§3 of the [byte
contract](byte-contract.md#the-artifact)) is part of the artifact, read by the
producer and the verifier alike: both run the same `Recheck.ingress` on the
same bytes. `HintTable.of` keys it as `ix check-lean` does (a block member's
hint under its projection record's address, a definition's under its own),
and the entry and the reading take `HintTable.lookup` of it; `AcceptedFrom`
states that the table is the one computed from the envelope's bytes.

- *What hints are.* Advice about the order in which conversion unfolds
  definitions (`opaque`, `abbrev`, a regular height): the kernel's lazy-delta
  step unfolds the side with the greater height first, as Lean's kernel does.
- *What they affect.* Time, and through the kernel's fuel possibly the
  verdict: the kernel may decline on fuel under one hint function and accept
  under another. No theorem depends on their being right: every theorem of
  the entry (`checkBytesTieredUsing_ok`, `checkConstantsTiered_ok`) holds for
  every hint function, and the program, the annotation, the certificate and
  the object do not read them. So a verdict is about the artifact as stored,
  hints section included, and an acceptance under any hints is the same
  acceptance.
- *Why they are passed.* Without them the kernel's reader computes every
  height from the stored values and has no `abbrev`, which is not Lean's order;
  on it a one-line `rfl` proof that Lean's kernel checks in a millisecond
  (`(BitVec.allOnes 16 ^^^ y).toNat = Nat.xor 65535 y.toNat`, and the
  `complement` word equations) took time exponential in the width, so any
  closure holding such a proof stalled `ixcc compile`
  ([kernel notes](../plans/aiur-backend/KERNEL-NOTES.md), section 10, a local
  working file). With them the same closure is accepted in about half a
  second.
- *What a hostile hint can do.* Make the kernel slow, or make it decline on
  fuel: never a different acceptance. `tests-kernel-front` checks this through
  the front end on three closures with the hints section removed, every hint
  regular at height 0, every hint `abbrev`, every hint `opaque` and the
  heights inverted: each case ends in the honest object and certificate or in
  a decline, and on the closure where the kernel without good hints is
  exponential it may run out of a time limit (bounding that is the kernel's,
  by a work budget). The section is not covered by the artifact's name `(H, ρ)`
  nor by a compile claim, so two parties may hold the same claim over files
  that differ in their hints: one may decline where the other accepts, never a
  different acceptance.

**What acceptance has to deliver, and what this entry delivers.** Since the
restatement of 2026-11-11 ([certification
design](certification-design.md#the-restatement-of-2026-11-11)), the first
premise of the end-to-end statements is that the kernel's reading of the
closure of the *seeds* (the target and the theorems the unfolding table
names), under the role table the certified IxVM work's claims are stated
under (the kernel's default table) and behind the committed prelude, has a
model with the laws; and the second premise includes typing derivations for
what the evaluator runs. The tiered entry's acceptance of the artifact gives
a model of the artifact's *whole* logical environment, under the artifact's
own table and behind the artifact's own prelude: more than the premise (every
logical record, not the closure) and different from it (another table and
prelude). It is the right early check for the producer, and its reading is
the one the annotator asks about; it is not, as it stands, a native discharge
of premise (i). That needs either three restriction lemmas (models of the
whole to the closure, the reading under the artifact's table to the default
one, the derivations to the closure) or a second run of the kernel's logical
entry on the closure alone under the claim's table and prelude (decided on
2026-11-11, DO-37; [certification design](certification-design.md#sp-n-native-discharge-of-the-premises)).
For the second, `Accept.lean` gains an entry that computes the closure of the
seeds in the accepted records (references, the certified operations' ground
and literal edges, recursors; a port of the kernel side's closure walk, since
IxCC may not import the root package), orders it with `Order`, and runs the
logical entry with the default binding and the committed prelude on exactly
those records; it keeps that run's declarations for the typing clause, and
checks that the artifact's table is a restriction of the default one and that
the closure holds no constant of a role the artifact's table leaves unbound.
Planned; nothing of it is built.

### The program and its correspondence

Ingress (`Recheck.ingress`, [`Recheck/Produce.lean`](../IxCC/Recheck/Produce.lean);
it was `KernelFront.ingress` beside the old front end until step 3 folded it in)
reads the records its seeds reach into the program (`Src.Ingress.reach`,
then `Src.Ingress.readConsts` for the chosen roots), takes the pins from the
kernel's admitted table (`pinsOfTable`, the role mapping of `Src.Pinned`), and
reads the program against the kernel's reading (`Reading.build`,
[`Reading.lean`](../IxCC/Src/KernelFront/Reading.lean)).

**What is read** (since 2026-11-12; before, every record of the artifact was
read, so a record no root reaches, over IxCC's consumer budget, refused the
artifact). The walk starts from every root the sidecar names (not only the
chosen ones, so the numbering does not depend on the choice and a producer's
and a verifier's ingress agree), the constants the admitted table binds to the
identities IxCC pins, every address the resource context names, and, as *proof
seeds*, the equation theorem of every sidecar proposal whose subject is
reached and the resource context's equation theorems. It follows every
reference of what is read, and a projection record to its block. A record a
proof seed reaches is read with its theorems' proofs; any other is read *by
statement*: a theorem's type is read, its proof is not read and its references
are not followed, its stored value is `Src.Term.unreadProof` and it is
recorded in `Program.byStatement`. The recursors of a reached inductive are not
followed (one the program uses is reached by reference: a `casesOn` names its
recursor). The result is the least fixpoint, a function of the records, the
sidecar and the table; IxCC's consumer budget applies to what is read of each
reached record. Nothing in IxCC takes a theorem's value as a runtime term:
SrcEval unfolds only safe definitions and allowlisted opaques, erasure the
same, and the annotator walks the runtime terms `Program.runtimeKeys` gives,
which name a value only under `isEvaluatedBody`. The consumers that examine a
theorem's proof refuse one read by statement: `Table.checkEqn`, `checkCsimp`
and `checkWord` (so a table entry names only a theorem whose proof was read), the
axiom-closure walk, and the recheck path's annotation check
(`Recheck.checkRelevanceKeys`, for an annotation naming its value). The kernel
still accepts the whole artifact, so every record IxCC reads is one the kernel
accepted.

The correspondence:

- every constant's kernel key is the reader's key for its identity
  (`Ctx.memberKey` of its block member or constructor), and the address the
  reader keys it by is the address IxCC keys it by;
- every constant's kind, universe parameter count and counts are those of the
  kernel's declaration under its key (`headerCheck`): a definition's kind; an
  inductive's parameters; a constructor's parameters and fields; a
  recursor's sums, its rules' constructors (under the key map) and field
  counts; a quotient constant's kind; a `partial` or `unsafe` constant is a
  tier constant.

The annotator then checks, for every runtime term it walks (a definition's
value, a recursor's rule), that IxCC's term corresponds to the kernel
reader's (`corr`: the same shape node for node, constants under the key map,
the same literals and contracts, universes under the constant's renaming), and
after annotating, that the type of every constant it reached and of every
theorem the unfolding table names corresponds (`checkReachedTypes`). An
equation's body is built by IxCC's table check from a theorem's type, so it is
translated rather than compared (`toKernel`); the theorem's type is compared.

### The annotation

`KernelFront.annotate` ([`Annotate.lean`](../IxCC/Src/KernelFront/Annotate.lean))
computes the same annotation as the old annotator, in the same format and the
same order, from the kernel's answers: from the roots, for each runtime term,
it walks IxCC's term and the kernel reader's together, opening each λ binder
as a free variable whose type is the binder's domain after the kernel's
annotation pass, and substituting each `let`'s value into its body as the
kernel's annotation pass does. At each binder, argument and let it classifies
the position:

- **proof under `w`**: the kernel's annotation pass and inference give the
  position's type `t`, inference gives `t`'s type `s`, and weak head
  normalisation gives `Sort u`; `w` is `u`'s zero condition over the
  constant's universe parameters (exact for every level form, D18), read back
  to IxCC's numbering for a large eliminator's terms;
- **type**: otherwise, when the type reduces to a Π-telescope ending in a
  sort;
- **relevant**: otherwise;

and gives each λ the zero condition of the sort of its body's type. The
kernel's binder datum (`BinderMeta.pw`) is the zero condition of a binder's
*codomain*, so the annotator asks about domains and arguments instead of
reading it. A binder written erased stays irrelevant whatever its type, as
before. Constant and constructor classes come from the kernel reader's types
the same way.

### Stage A

`KernelFront.checkCanonicalRelevance`: the certificate's annotation equals the
kernel annotator's output on the table the certificate's table certificate
gives (`checkCanonicalRelevance_iff`). It replaces the old one on the
byte-level path; the kernel is already there for acceptance.

### What each use of the erased checker becomes

Every use of the checker (`IxCC/IxCC/Ixon/V3/Tc/`) outside its own modules,
as the tree stood after step 2 (2026-11-11), and what it becomes. Steps 3 and
4 made every row's last column true; the checker is deleted:

| Use (where) | What rests on it | Becomes at the switch |
| --- | --- | --- |
| `V3.Tc.checkEnv` in `Recheck.ingress` (`Recheck/Produce.lean`), when its `typecheck` flag is set | acceptance on every byte-level path: `CompileClaim.verifyBytes`, `checkClaim`, `makeClaim`; `Ring0Sip.verifyBytes`; `Recheck.compile`, `compileWithContracts`; `RcReplay.compileAuto`; `ixcc compile` and `check-cert` | the kernel's tiered entry (`KernelFront.accept`, inside `KernelFront.ingress`), mandatory; each of them loses its `typecheck` parameter |
| `Src.Relevance.annotate` (`Src/Relevance/Annotate.lean`, which opens `Tc` and asks its inference, conversion and weak head normalisation) | the producers' relevance oracle (`Recheck.produceSource`; `RcReplay.produceFir`, `Recheck/Rc/Produce.lean`); Stage A (`Recheck.checkCanonicalRelevance`, hence `CompileClaim.checkCertCanonicalRelevance`, `Ring0Sip.verifyBytes`, `check-cert`); `Src.load`'s default oracle | `KernelFront.annotateChecked` (with `checkReachedTypes`); Stage A `KernelFront.checkCanonicalRelevance`; the module is deleted |
| `V3.Tc.checkEnv` in `Src.prepare` (`Src/Load.lean`), when `LoadConfig.typecheck`; `RelOracle` takes a `V3.Env` | the loader of the Src, Lam and pipeline suites and of `src-steps` | `KernelFront.ingress` and its annotator; `LoadConfig.typecheck` goes, and the oracle takes the accepted input |
| `V3.TypedInput`, `V3.validateTyped` (`Ixon/V3/Typed.lean`) | nothing: since step 2 only the umbrella `IxCC.lean` imports it | deleted |
| `ValidatedInput.typingChecked` in `V3.validate` (`Ixon/V3/Validate.lean`), and `ValidatedInput.typing_checked` | the resource-validation API (`check-ixon-v3`, `tests-ixon-v3`), which keeps typing as its prerequisite | the typing conjunct goes (resource admission and the literal pins stay); the kernel's acceptance where the input is role-bound. Its handoff fixtures are unbound |
| `Admitted.typingChecked` in `Catalog.admitWith` (`Ixon/V3/Catalog/Admit.lean`), and `Admitted.typing_checked` | catalog validator 1 (`check-ixon-v3-catalog`) | IxCC's catalog support retired in step 4 (validator 1 certified erased typing; ix retired it): the reader, the admission, its four fences, `ixcc-ixon-v3`'s catalog step, the two frozen catalogs and their tests |
| `Tc.initialState`, `getConstVerified`, `checkTarget`, `TcM.checkConst` in `Tools.Census.entries` (`Tools/Census.lean`) | the per-constant typing verdicts of the required `census` check, compared with reviewed baselines | the kernel's acceptance of the whole role-bound closure, its refusal naming the record; the baselines regenerated with the refreeze |
| `typecheck = true → V3.Tc.checkEnv inp.env = .ok ()` and `Src.Relevance.annotate … = .ok …` in statements: `Recheck.ingress_parts` (`Compiler/Proof.lean`), `verifyBytes_{immortal,zeroRc,plainRc}_sound` (`CompileClaim/Proof.lean`), `verifyBytesRing0Sip_sound` (`Ring0/Proof.lean`), and the bridge's `checkDecls_verifyBytes_immortal_denotes_nat` (`Models/KernelBridge/IxKernelBridge/NatBridge.lean`); the `typecheck` parameter alone in `compile_parts` and its siblings (`Recheck/Proof/Compile.lean`), `compileWithContracts_*` and `compileAuto_*_sound` (`Compiler/Proof.lean`), `checkClaim_iff` (`CompileClaim.lean`) | the byte-level guarantees | restated with the acceptance and the kernel Stage A conjuncts ([statements](#the-byte-level-theorems-after-the-switch)) |
| `--no-typecheck` (`Cli.lean`) | skips typing at ingress | removed ([the typing flag](#the-typing-flag)) |
| the erased checker's tests: `IxCCTests/IxonV3/{Typing,Primitives,K1}.lean` (`Tc.checkEnv`, `KUniv`, `univEq`, `getConstVerified`, `primAddrSet`, `tcUInt64BytesLE`) | `tests-ixon-v3`'s typing part | deleted; its assertions that are not typing (the primitive table against `primitives.tsv`, the `Nat` literal bytes) move to the suite's other parts |
| `IxCCTests/KernelFront/Diff.lean` (`V3.Tc.checkEnv`, the old front end) | the differential | the old side went in step 4 (the module is now `IxCCTests/KernelFront/Report.lean`: the kernel's acceptance, ingress, and every root through the producer and Stage A); the kernel front end's regressions stay, and its run over the refrozen corpus is the required differential's successor |
| docstrings: `Ixon/Hash.lean` (`V3.Tc.finishHash`, the Rust hasher's one user), `Src/Prim.lean` (`Tc.computeNatBin`), `Src/KernelFront/Front.lean`, `Ixon/V4/Convert.lean`, `CompileClaim.lean`, `Ring0.lean` | — | rewritten; with the checker gone, `Blake3.Rust` has no user in IxCC |
| not typing: the block-member keys, the `Nat` literal bytes, address order and hexadecimal reading, the primitive table | ingress, the pinned identities, the sidecar's reader, the resource profile | moved by step 2 to `V3.*ProjAddr` ([`Ixon/V3/Keys.lean`](../IxCC/Ixon/V3/Keys.lean)), `V3.natFromBytesLE`, `V3.natBytesLE`, `Address.cmpBytes`, `Address.fromString` ([`Ixon/V3/Support.lean`](../IxCC/Ixon/V3/Support.lean)) and `V3.PrimAddrs` ([`Ixon/V3/PrimAddrs.lean`](../IxCC/Ixon/V3/PrimAddrs.lean)); the kernel's key map checks the keys against its own reconstruction (`Reading.build`) |

The per-claim `typecheck` flag goes with the first row ([below](#the-typing-flag)).

## Statements

### The byte-level theorems after the switch

Restated at the switch's step 3 and proved, with their fences' names and axiom
sets unchanged (`propext`, `Classical.choice`, `Quot.sound`).
`Recheck.ingress_parts` ([`Compiler/Proof.lean`](../IxCC/Compiler/Proof.lean))
concludes, from `ingress bytes equations roots = .ok inp`:

- `decodeAnonymousEnv bytes = .ok inp.env`;
- the acceptance: `KernelFront.accept inp.env defaultLimits = .ok inp.kernel.acc`,
  `AcceptedFrom inp.env defaultLimits inp.kernel.acc` (the environment is
  role-bound; the kernel's entry ran on its binding section, on exactly its
  records and blobs, with the hint table computed from its hints section,
  `acc.hints = HintTable.of inp.env.hints acc.constants`) and
  `Ix.Kernel.Admission.checkBytesTieredUsing (preludeSource acc.pre) hash
  acc.binding acc.limits acc.records acc.blobs acc.hints.lookup = .ok (acc.env,
  acc.tier)` (`accept_spec`; the hint argument since 2026-11-12, before which
  the entry ran with none), from which the kernel's theorems
  give, for the logical records, the reading's fidelity, a model in every set
  theory and the strong model, at IxCC's hash, the artifact's prelude and the
  artifact's table;
- `Src.Resource.validate inp.program = .ok ()`;
- the program read against the kernel's reading:
  `Reading.build inp.kernel.acc inp.program = .ok inp.kernel.rd` and
  `inp.kernel.fe = mkFEnv inp.kernel.acc.env`;
- the program: the sidecar's chosen roots, the records the seeds reach
  (`Src.Ingress.reach inp.env (Seeds.of rawHints (pinsOfTable
  inp.kernel.acc.table)) = .ok records`), `Src.Ingress.readConsts inp.env
  records roots = .ok rawProg`, and `inp.program` is `rawProg` with the pinned
  identities of the kernel's admitted table (`pinsOfTable`) and the sidecar's
  resource context. The decode no longer implies that every record of the
  artifact is within IxCC's consumer budget (only the reached ones are, by
  `reach`); the program says what it said, of the records the seeds reach.

`CompileClaim.verifyBytes_{immortal,zeroRc,plainRc}_sound`
([`CompileClaim/Proof.lean`](../IxCC/CompileClaim/Proof.lean)) and
`Ring0.verifyBytesRing0Sip_sound` conclude all of these for the input their
verifier ingested, `inp.env.bindingAddress = c.roleTable`, and Stage A over
the kernel: `inp.kernel.annotateChecked { inp.program with table } = .ok
cert.relevance`. In place of the earlier `typecheck = true → Tc.checkEnv
inp.env = .ok ()` and `Src.Relevance.annotate inp.env {…} = .ok
cert.relevance`; the verifiers have no unchecked mode, and every theorem
lost its `typecheck` parameter (`_rootShape`, `_shape`, `checkClaim_ok_iff`,
the compiler's theorems in `Compiler/Proof.lean` and
`Recheck/Proof/Compile.lean`). The kernel bridge's
`checkDecls_verifyBytes_immortal_denotes_nat` concludes the acceptance in
place of `Tc.checkEnv`.

The acceptance conjunct says that the kernel accepts the environment with root
`H` under the table `ρ` the envelope carries. That was premise (i) of the
[end-to-end plan](end-to-end.md) as first stated; under the restated premise
it is more than, and different from, what is needed (above, "What acceptance
has to deliver"), and the native discharge adds the closure run.

### The annotation, against the kernel's judgements

Two directions, for each position the annotator classifies (a binder,
argument or let of a runtime term, at the kernel reader's subterm `a` at depth
`d`, the enclosing λ binders open):

1. **Tagged irrelevant ⇒ a type or a proof.** If the tag is `proof w`, the
   cached core's runs from the annotator's state give `annotate d a = a'`,
   `infer d a' = t`, `infer d t = s` and `whnf d s = Sort u` with
   `zeroCond u = w` (read back). By the kernel's simulation and bridge, the
   specification functions accept at some fuel, so `Infer env .full d a' t`,
   `Infer env .full d t s` and `Red env d s (.sort u)` hold; by `infer_sound`
   and `red_sound`, in every model meeting `RulesInputs` (every strong model of
   the accepted environment) and every valuation satisfying the context, the
   denotation of `a'` is a member of `t`'s, which is a member of `Sort u`'s; at
   a level assignment where `w` holds, `u` is zero, so `t` denotes a
   proposition and `a'` its proof. A `type` tag is the same with a
   Π-telescope ending in a sort.
2. **Every type or proof position SrcEval would evaluate is tagged.** SrcEval
   evaluates exactly the positions the walk visits (it never enters a subterm
   tagged irrelevant at every instance). At each, the tag is computed from the
   kernel's answers: whenever the runs above succeed with `Sort u`, the tag is
   `proof (zeroCond u)`, so the position is irrelevant at every level
   assignment where `u` is zero; a failure of the kernel's runs on a visited
   position refuses the program, except that a type whose own sort cannot be
   inferred counts as not a proof (as before).

**Proved now** (no `sorry`, standard axioms):

- `KernelFront.accept_spec` ([`Accept.lean`](../IxCC/Src/KernelFront/Accept.lean)):
  the acceptance statement above.
- `KernelFront.checkCanonicalRelevance_iff`: Stage A is equality with the
  kernel annotator's output.
- The classifier at one position, both directions
  ([`Proof.lean`](../IxCC/Src/KernelFront/Proof.lean)): a `proof w` class
  comes from successful cached-core runs with `Sort u` and `zeroCond u = w`
  (`Ctx.classifyTerm_proof`, `Ctx.classifyType_proof`); and such runs give that
  class (`Ctx.classifyTerm_of_runs`, `Ctx.classifyType_of_runs`).
- Direction 1 at one position, composed with the kernel's theorems, in the
  package that builds both IxCC and the kernel's proof tree
  ([`Models/KernelBridge/IxKernelBridge/KernelFront.lean`](../../Models/KernelBridge/IxKernelBridge/KernelFront.lean)):
  `infer_derives`, `whnf_derives` and `annotate_runs` (kernel-side lemma 1
  below, packaged from `ssimC` and the bridge); `classifyTerm_derivations`: for
  a well-formed accepted environment and an invariant memo state, a `proof w`
  class at a well-scoped position is the kernel's annotation `e'` of the
  position's term with `Infer env .full d e' t`, `Infer env .full d t ty`,
  `Red env d ty (.sort u)` and `w` the zero condition of `u`; and
  `classifyTerm_sound`: their readings `InferSem` and `RedSem` in every model
  meeting `RulesInputs`. The well-formedness of an accepted environment is the
  tiered entry's (`checkConstantsTiered_ok`).

**Left**, in order:

- the walk-level statement: each tag of the annotation is the classifier's
  answer at the position `Term.tagOrder` gives it, for the kernel term the walk
  reaches by opening and substituting (an induction over `walk`, about 1–2k
  lines), and the walk's invariant memo state and well-scoped positions;
- discharging `InferSem`'s premises at an opened position (kernel-side lemma 2)
  and relating the annotated term to the evaluated one (lemma 3);
- the adequacy work itself (SP-A, SP-1), which consumes both directions and
  the correspondence.

### Kernel-side lemmas needed

For the kernel's owners; each is about the kernel's existing functions, none
asks a change of behaviour:

1. **The cached core's answers are derivations, packaged.** For an accepted
   environment `env` (so `EnvWF env`), a state `s` with `CSOK .verified env s`,
   a term `e` with `Expr.WScoped d e`:
   `(coreKnotI .verified (mkFEnv env) checkFuel).infer d e s = .ok (t, s')`
   implies `Infer env .full d e t ∧ CSOK .verified env s' ∧ Expr.WScoped d t`,
   and the same for `whnf` (to `Red`) and `annotate`. The pieces exist
   (`ssimC`, `inferTypeCore_bridge`, `whnf_bridge`), and the bridge package
   packages them (`IxKernelBridge.KernelFront.infer_derives` and its siblings);
   the kernel's own public interface is the right home for them, and the
   annotation pass has no relational judgement to bridge to.
2. **Typing transport into opened subterms.** For an accepted definition (or
   rule) whose reader term is `v`, and a position of `v` reached by opening its
   λ binders with their annotated domains and substituting its `let`s: in every
   strong model and level assignment, the position's context satisfies
   `CtxOk` and the subterm reads (`denoteMeta … = some _`), the premises
   `InferSem` takes. This is the typing-transport question of SP-A, stated for
   the kernel's own reading.
3. **The annotation pass preserves denotation.** The kernel's facts are about
   the annotated subterm `a'` (its `let`s substituted, its binder data
   written); SrcEval evaluates the term with its `let`s. A lemma that the
   annotation pass preserves the interpretation of a readable term in every
   strong model connects them.
4. **A work budget.** The typing core's fuel bounds recursion depth, not
   work. Its exponential time on constants whose ∀s share one type at each
   step had its cause in universe levels, not terms: the ∀ rule built `imax u
   v`, a level shared as a DAG whose tree doubles per step, which
   `Level.simplify` and `levelHasParam` walked as trees. The fix was made in
   the kernel package on this branch, in parallel with the switch (the
   owner's decision of 2026-11-11), and has landed: the kernel caches the
   has-parameter bit and hash-conses the ∀ rule's levels ([hardening
   design](hardening-design.md#external-dependencies)), which closes those
   families. Levels that stay large (two chains at two universe
   parameters, each step mentioning the other) are now walked once per node:
   the kernel's level walks are memoised on shared levels (`docs/kernel.md`,
   "Running time"). What stays is the level comparison itself, coNP-hard for
   levels with `imax`, which takes time exponential in the number of universe
   parameters on some small constants (Lean's kernel refuses them, its
   comparison being incomplete). A step counter on the core's calls would not
   bound it, since the core makes few calls: the budget has to count the
   comparison's own calls, up to a bound the caller sets, and decline where it
   runs out. That budget,
   with acceptance stated within it, is what lets IxCC bound its verifier
   ([Resource bounds](#resource-bounds)); it is planned (KF-3).
5. **The rules' soundness over the public model** (added 2026-11-11).
   `infer_sound`, `defeq_sound` and `red_sound` are stated over the internal
   carrier with `RulesInputs`; soundness of the evaluator over every public
   `Model` with the laws needs them over that structure. The certified IxVM
   work plans to derive the internal invariant's public clauses from the
   public model's fields, which is the same step.
6. **A table restriction lemma** (added 2026-11-11). The reader's output on a
   record list is the same under a role table and under a restriction of it,
   when no record is the constant of a role the restriction leaves unbound.
   It lets a claim stated under the default table cover an artifact `ix
   compile` wrote with its own table.

Lemmas 2 and 3 are now part of the typing clause of the second premise: on
the native route they are how the kernel's runs become derivations at the
positions the evaluator runs.

## The typing flag

The flag (`typecheck : Bool := true` on `Recheck.ingress`, `verifyBytes`,
`checkClaim`, `makeClaim`, `compile`; `--no-typecheck` on `ixcc compile` and
`check-cert`) never contributed to a theorem and was not bound by the claim.
It is gone since step 3: acceptance is not optional on any byte-level path;
`--no-typecheck` is an unknown option (a usage error, exit status 2); an
unbound closure is refused with the kernel's reason; `--stats` reports the
kernel's acceptance (records, logical declarations and tier constants;
ingress's time includes it). A claim's meaning is "the kernel accepted the
environment with root `H` under the envelope's table and IxCC's object
refines SrcEval on the checked source program read from it", with no hidden
parameter. The claim already names the role table's address (`roleTable`,
validator 7; [byte contract](byte-contract.md)), so the table in that meaning
is the claim's. That is what the verifier checks; the grounded meaning the
end-to-end statements give it is about the closure of the seeds under the
paired IxVM claim's table ([end-to-end](end-to-end.md#the-shared-spine)).

## Dependency and the trust ledger

**Modules.** The front end imports `IxCK.Kernel.Admission.Tier` (the tiered
entry, which imports the logical entry and the reader), `IxCK.Kernel.Cached.CoreC`
(the executed core) and `IxCK.Kernel.Ixon.Prelude`: an 82-module closure (98
files since later kernel landings) of
about 49,000 lines, against 13 files before (the codec and the role
vocabulary). It includes the committed role data
(`IxCK/Kernel/Ixon/RoleData.lean`, 13,737 lines of hexadecimal records) through
the prelude module. It does not include the kernel's proof tree
(`IxCK/Kernel/Verify`, `IxCK/Kernel/Model`); theorems that compose with it live
where that tree is built.

**Build cost.** Measured on the build box: see the
[measurements](#measurements) below.

**The ledger** ([trust ledger](trusted-extern-ledger.md)). The dependency
entry's closure grows to the 82 files (98 since), each pinned by its SHA-256;
`imported_modules` lists the six modules IxCC's sources import (the codec's
three and the kernel's three); the
`@[csimp]` inventory grows with the kernel's replacements (each a proved
equality). The closure audit refuses `implemented_by` in a dependency; the
kernel has two kinds of site, and the entry records them as an enumerated
exception, `implemented_by_sites`, which the audit compares exactly with the
closure's sites. The list is the kernel's own audit's
(`Ix.Kernel.Audit.runtimeRulings`, `IxCK/Kernel/Audit/Roots.lean`):

- `Ix.Kernel.withExclusive`, implemented by `withExclusiveUnsafe`
  (`IxCK/Kernel/Exclusive.lean`), the one runtime substitution the kernel
  admits (`runtimeRulings.implementations`); its type carries the obligation
  `k true = k false`, so the substitution cannot change a value;
- the three elaboration-time evaluators of `IxCK/Kernel/BasisGen.lean`
  (`evalInfo`, `evalVal`, `evalEnv`, each implemented by its `unsafe` twin),
  `meta` code that compiled code cannot call (`runtimeRulings.elaborationModules`).

The kernel's audit also admits the `@[computed_field]` overrides of its
`Level`, `Expr`, `Name` and `Key` hashes, which are not `implemented_by` in
source, and no `partial` definition. The kernel's admission hash is a
parameter: no assumed substitution is admitted (the one ix admits, its Rust
BLAKE3 for `Address.admissionHash`, is the root library's, not the kernel's;
IxCC instantiates the hash with its pure BLAKE3).

## Resource bounds

On the byte-level path the kernel now runs on the claimant's bytes. What
bounds it:

- the batch limits (IxCC's decoder caps: 16,384 records, 1 MiB each, 16 MiB
  in all) and the kernel's per-record universe budget;
- the kernel's fuel, per call: a recursion-depth bound (`checkFuel`, 100,000),
  not a work bound;
- nothing else. IxCC cannot meter a function it does not own: no counter is
  exposed, and admission limits do not help against a payload of a few
  hundred bytes.

The kernel's typing core was exponential on a constant of a few hundred bytes
whose ∀s share one type at each step (`k` nested `let`s, `let a(j+1) : Type
:= aj → aj`, or the same chain in a sharing table): the ∀ rule built a
universe level whose tree doubles per step, and two level functions walked it
as a tree ([hardening design](hardening-design.md#external-dependencies)).
The kernel now hash-conses that level and caches its has-parameter bit
(at the time of the measurement below it folded the level with `mk_imax`'s
folds, since withdrawn; the times are of the same order). Measured on a role-bound closure of 206 records
with one such constant (the constant 200 to 330 bytes), each acceptance alone
in its own process, before and after the kernel's fix (the earlier erased
checker, which opens each `let` as a let-bound local and hash-conses its
terms, for comparison):

| `k` | erased checker | kernel front end, before | kernel front end, after |
| ---: | ---: | ---: | ---: |
| 24 | 0.14 s | 0.78 s | 0.027 s |
| 28 | 0.14 s | 12.1 s | 0.028 s |
| 30 | 0.19 s | 50.4 s | 0.028 s |
| 34 | | | 0.028 s |

All accept. (`tests-kernel-front` checks such a closure at `k = 200`.) Levels
that stay large (two chains at two universe parameters, each step
mentioning the other) no longer cost their trees: the kernel's level walks
are memoised on shared levels. What remains exposed is the level comparison
itself: deciding `l ≤ r` for levels with `imax` is coNP-hard, and the
kernel's complete comparison takes time exponential in the number of
universe parameters on some constants of a few hundred bytes (Lean's own
kernel refuses them, its comparison being incomplete). So the switch still adds an exposure the erased checker does not
have: a claimant can make the verifier's acceptance take as long as it likes
with a closure of ordinary size. The annotator asks the same core about
`let`-substituted subterms, so a root whose terms carry such a chain costs as
much again in the producer and in Stage A. The guard for these is a
dependency: a call budget in the kernel's level comparison (kernel-side
item 4), which the front end passes as a
budget and reports as a decline (milestone KF-3 below). Until that budget
exists (since the switch's step 3), the kernel's typing time on such levels is outside
the verifier's time bound, and a constant of a few hundred bytes chosen by a
claimant can hold `verifyBytes`, `Ring0Sip.verifyBytes` and `ixcc check-cert`
as long as it chooses. On every closure `ix compile` writes, the kernel is faster
([measurements](#measurements)).
The kernel's recursion depth on the verifier's 8 MiB stack is likewise the
kernel's to bound (HD-3 audits it with IxCC's own). Until it is, the envelope
bounds the depth of every stored record: its expressions, shares expanded, at
most `V3.kernelDepthLimit` (2,560) deep (`V3.withinKernelDepth`; universes are
not bounded in depth, as IxCC never bounded them). Measured on generated chains
(shared and flat, reached and unreached, four shapes), the kernel's acceptance
of one such record survives 3,000 levels on a 2 MiB stack and 10,000 on 8 MiB
and overflows at 4,096 and at 30,000 respectively; real artifacts stay far
below (deepest 775 in IxCC's committed closures, 325 in Init+Std, 1,221 in
Mathlib). IxCC's consumer budget (a `share` a leaf) never bounded the expanded
depth, so before the bound a shared chain of 100,000 levels in one record
crashed the verifier whether reached or not. The bound does not make the kernel
safe: it runs after the kernel's canonical decoder, which still overflows on a
record nested about 30,000 deep without shares on 2 MiB (100,000 on 8 MiB), and
it limits stored records, not the terms the kernel's conversion builds, which
unfolding across records takes past the stack (10,000 levels from five records
on 2 MiB; 40,000 from twenty on 8 MiB; a long string literal met as a
constructor does the same). These are the kernel package's to fix.

## The switch

The steps that make the new front end the only one, in an order that keeps
the tree green at every commit. The switch proceeds now (the owner's decision
of 2026-11-11, [decision 5](#decisions)); the kernel's fix of its blow-up on
`let` chains, made in parallel in the kernel package on this branch, has
landed; what stays exposed is under [resource bounds](#resource-bounds).

1. **Prerequisites (not this work).** The fixtures refrozen in the role-bound
   form (RL-1 phase 2; the kernel admits only role-bound environments, and
   the committed closures are unbound, selected without recursors, so its
   reader declines their inductive blocks), written by an `ix compile` that
   binds every role whose constant the closure brings in. An earlier `ix`
   bound neither `choice` nor `natLor` in the larger closures, and the
   kernel declined `Classical.choice` there as a non-standard axiom; the
   closures [measured](#measurements) below come from an `ix` that binds them.
   Done (2026-11-11): every committed closure is role-bound but the frozen
   typing bundles, catalogs and resource handoff vectors (the dated
   historical ownership records, unbound, were retired in step 4).
2. **Move what is not typing out of the checker** (a refactor, no behaviour
   change). **Done** (2026-11-11): the block-member keys (`V3.defnProjAddr`
   and its siblings, pure BLAKE3) to [`Ixon/V3/Keys.lean`](../IxCC/Ixon/V3/Keys.lean);
   the `Nat` literal bytes (`V3.natFromBytesLE`, `V3.natBytesLE`, formerly
   `Tc.tcNatBytesLE`) and address order and hexadecimal reading
   (`Address.cmpBytes`, the `Ord Address` instance, `Address.fromString`) to
   [`Ixon/V3/Support.lean`](../IxCC/Ixon/V3/Support.lean); the primitive table
   the resource adapter takes its literal types and `Eq` from (`V3.PrimAddrs`,
   with `canonical` and the parity table `leanParityTable`) to
   [`Ixon/V3/PrimAddrs.lean`](../IxCC/Ixon/V3/PrimAddrs.lean). `Tc` keeps the
   checker's own hashing helpers (`finishHash`, `tcUInt64BytesLE`), its
   reserved reduction markers and its primitive set. `Src.Ingress`,
   `Src.Hints`, `Src.Pinned` and the resource adapter no longer import the
   checker; [above](#what-each-use-of-the-erased-checker-becomes) is every use
   that remains.
3. **One commit: the kernel front end becomes the front end.** **Done**
   (2026-11-11), after the refreeze (step 1). `Recheck.ingress` returns the kernel front end's input (the `Recheck.Input`
   gains the accepted kernel input, or becomes `KInput`); `produceSource` uses
   `KernelFront.annotate`; `checkCanonicalRelevance` is the kernel one; the
   `typecheck` parameters go from `Recheck.ingress`, `compile`,
   `CompileClaim.verifyBytes`, `checkClaim`, `makeClaim`, `Ring0Sip`,
   `Src.load`, the census and the corpus tools, and `--no-typecheck` from
   `ixcc`; the theorems are restated (`CompileClaim/Proof.lean`'s
   `verifyBytes_*_sound`, and `_rootShape` and `_shape`, which lose the
   parameter; `Compiler/Proof.lean`'s `ingress_parts` and the compile
   theorems; `Recheck/Proof/Compile.lean`; `Ring0/Proof.lean`'s
   `verifyBytesRing0Sip_sound`; the bridge's
   `checkDecls_verifyBytes_immortal_denotes_nat`) with the acceptance and the
   kernel Stage A conjuncts, and their fences re-recorded (`front_wellAnnotated`,
   `Recheck/Proof/Parts.lean`, is about `Recheck.front`, which runs no typing,
   and does not change); the duplicated producer of `KernelFront.Front` folds
   back into `Recheck.Produce`.
4. **Delete** (no behaviour change: every registered root compiles to the same
   object and certificate). **Done** (2026-11-11), in groups:
   the earlier annotator (`IxCC/IxCC/Src/Relevance/Annotate.lean`) and
   `tests-kernel-front`'s comparison with it and with the erased checker (the
   module is now `IxCCTests/KernelFront/Report.lean`); IxCC's catalog support
   (the reader, the validator-1 admission, its four fences, the catalog step of
   `ixcc-ixon-v3`, the two frozen catalogs and their tests: validator 1
   certified erased typing, and ix retired it); the erased checker
   (`IxCC/IxCC/Ixon/V3/Tc/`, 24 files, 12,357 lines), `Ixon/V3/Typed.lean`,
   the typing conjunct of the resource-validation API (`V3.validate` types
   nothing; on every compile path the kernel's acceptance comes first), the
   checker's typing tests and its four typing bundles (the primitive table's
   parity, the `Nat` literal bytes and the API's resource cases kept in
   `IxCCTests/IxonV3/Validation.lean`; the K1 packs checked by the kernel's
   acceptance); the unbound environment's reading (`Src.Ingress.ofEnv`, its
   fence, `Pinned.pinsOf`; the fixed table `Pins.fixed`, `src-tables.tsv` and
   `pin-src-tables`, once listed with it, stay: they are not unbound-only, being
   the allowlist's address and the default pins, and the source of
   `Src.Pinned`'s `lazy` and allowlist rows, `src-names.tsv` and the
   diagnostics fixtures, on every compile path); IxCC's own binding decoder
   (`IxCC/IxCC/Ixon/V3/Binding.lean`: the envelope keeps the section's address
   and bytes, the kernel decodes and admits the table, and the pins read the
   table it admitted); and the `Blake3.Rust` import (no IxCC executable links
   the Rust hasher). The in-memory environment builder of the tests stays,
   renamed `IxCCTests/IxonV3/Builder.lean`. Removed in all: about 15,400 lines
   of Lean and 16,500 lines in all, including the dated historical ownership
   records the kernel front end refuses (unbound) and `ix` can no longer write.
5. **The ledger last** (done): the kernel closure and its exception were
   already recorded; the native-interface entry is gone, Blake3 is recorded as
   a git-pinned pure dependency (the two files IxCC takes from it, with three
   admitted `native_decide` default-argument proofs), and the ledger audits
   that IxCC imports only `Blake3.Pure` and that no executable the checks
   build links either of the package's native backends
   ([trust ledger](trusted-extern-ledger.md), "No native interface"); the
   integrity pins re-recorded by the documented procedure. The runs of `tests-kernel-front`, `corpus check` and
   `tests-corpus` over the refrozen corpus (every one through the kernel's
   acceptance and annotator) are the required differential's successor.

Suites affected: `tests-ixon-v3` (typing fixtures, the catalogs, the binding
decoder), `tests-relevance` and `tests-lam` (annotation mutation draws from
the annotator), `tests-recheck` (Stage A, the hostile and deep families),
`tests-pipeline`, `tests-corpus`, `corpus check` and `census` (every family
re-ingested through the kernel), `tests-own` (the historical
annotated-recursion part retired), `tests-kernel-front` (its comparison),
`ixcc-proofs` (restated fences in step 3; six fences gone with their theorems
in step 4).

## Measurements

On the build box (64 cores, Lean 4.34.1), 2026-11-11.

**Build.** A cold `lake build IxCC IxCCTests ixcc` before the kernel import:
4 min 31 s wall, 21.6 GB peak, 2,004 jobs. The first build after the import
compiled 66 kernel modules (74 s of module time in all, the longest
`IxCK.Kernel.Cached.ExprOpsC` at 5.7 s) and the new modules in 38 s wall at
1.7 GB peak; the same targets are now 2,165 jobs. The bridge package's cold
build (the kernel's proof tree and IxCC): 2 min 49 s, 4.8 GB.

**The differential.** Every committed corpus family and benchmark fixture
was rebuilt role-bound into scratch by `corpus rebuild` with the tree's `ix`,
and each closure was run through
both front ends by `tests-kernel-front`: acceptance; the program; for each
root, the annotation, the certificate and `Recheck.run`'s object; and Stage A
of the kernel front end on its own certificate. On every closure both front
ends accept, the programs are equal, and every root's annotation, certificate
and object are identical, or both front ends refuse the root with the same
reason (a root declined downstream still has its annotation compared). No
difference was found. Since the role-bound refreeze every committed closure is role-bound:
`tests-kernel-front` asks the kernel to accept each (all but the three below)
and runs this differential on those under 512 KiB.

Times: acceptance alone, in its own process (the erased checker's
`Tc.checkEnv`; the kernel's tiered entry with its preparation); each whole
front end alone in its own process (decoding, acceptance, the program and the
producer for every root), wall time and peak memory.

| Closure | Records | Roots (compiled, refused alike) | Erased checker | Kernel | Old front end | New front end |
| --- | ---: | --- | ---: | ---: | --- | --- |
| `phase1-abi/abi` | 728 | 21 (18, 3) | 3.1 s | 0.26 s | 3.6 s, 154 MB | 0.8 s, 111 MB |
| `phase1-scalar/scalar` | 3,682 | 23 (23, 0) | 180.0 s | 1.33 s | 220.5 s, 1,031 MB | 34.3 s, 249 MB |
| `phase1-scalar/bigctor` | 231 | 1 (1, 0) | 0.91 s | 0.04 s | 1.0 s, 140 MB | 0.14 s, 87 MB |
| `phase1-scalar/natShiftr` | 422 | 1 (1, 0) | 0.80 s | 0.09 s | 0.9 s, 114 MB | 0.21 s, 93 MB |
| `phase1-scalar/strictAndOr` | 300 | 2 (2, 0) | 0.32 s | 0.04 s | 0.45 s, 94 MB | 0.15 s, 87 MB |
| `phase1-scalar/tuple` | 233 | 1 (1, 0) | 0.20 s | 0.03 s | 0.28 s, 91 MB | 0.11 s, 85 MB |
| `phase1-scalar/typeFormerPolymorphism` | 233 | 1 (0, 1) | 0.20 s | 0.03 s | 0.28 s, 91 MB | 0.11 s, 85 MB |
| `phase1-resource/resource` | 3,625 | 10 (10, 0) | 169.1 s | 1.74 s | 180.3 s, 998 MB | 10.1 s, 249 MB |
| `phase1-boundary/boundary` | 818 | 59 (59, 0) | 4.6 s | 0.40 s | 5.8 s, 203 MB | 1.6 s, 118 MB |
| `phase1-boundary/tags16` | 752 | 1 (1, 0) | 3.2 s | 0.25 s | 3.4 s, 165 MB | 0.47 s, 107 MB |
| `phase1-boundary/tags17` | 755 | 1 (1, 0) | 5.7 s | 0.40 s | 5.2 s, 153 MB | 0.74 s, 113 MB |
| `phase1-boundary/tags125` | 1,079 | 1 (1, 0) | 12.0 s | 0.47 s | 16.1 s, 332 MB | 3.8 s, 306 MB |
| `phase1-decline/closures` | 225 | 2 (0, 2) | 0.20 s | 0.04 s | 0.28 s, 92 MB | 0.11 s, 85 MB |
| `phase1-decline/admit` | 348 | 4 (0, 4) | 0.41 s | 0.06 s | 0.50 s, 95 MB | 0.16 s, 87 MB |
| `phase1-decline/symbols` | 233 | 10 (10, 0) | 0.26 s | 0.05 s | 0.47 s, 92 MB | 0.22 s, 87 MB |
| `phase1-decline/panic` | 861 | 1 (0, 1) | 3.1 s | 0.25 s | 3.3 s, 138 MB | 0.47 s, 109 MB |
| `phase1-decline/params` | 243 | 3 (0, 3) | 0.29 s | 0.04 s | 0.39 s, 92 MB | 0.16 s, 85 MB |
| `phase1-decline/strings` | 4,670 | 1 (0, 1) | 390.8 s | 3.04 s | 392.8 s, 1,858 MB | 7.2 s, 355 MB |
| `phase2-closures/closures` | 708 | 5 (0, 5) | 1.6 s | 0.14 s | 2.0 s, 121 MB | 0.44 s, 101 MB |
| `phase2-arity/arity` | 3,661 | 25 (10, 15) | 231.2 s | 1.41 s | 198.1 s, 998 MB | 10.0 s, 247 MB |
| `ownership/*` (14 closures) | 216–353 | 16 (16, 0) | 0.17–0.42 s | 0.03–0.05 s | 0.25–0.53 s, 90–96 MB | 0.11–0.16 s, 85–89 MB |
| `bench-k1/fib` | 225 | 1 (1, 0) | 0.20 s | 0.04 s | 0.29 s, 92 MB | 0.12 s, 85 MB |
| `bench-k1/even-odd` | 266 | 1 (1, 0) | 0.24 s | 0.04 s | 0.34 s, 92 MB | 0.16 s, 87 MB |
| `bench-k1/gcd` | 508 | 1 (1, 0) | 1.2 s | 0.11 s | 1.4 s, 115 MB | 0.26 s, 97 MB |
| `bench-k1/sfib` | 352 | 1 (1, 0) | 0.43 s | 0.05 s | 0.55 s, 96 MB | 0.16 s, 89 MB |
| `bench-k1/tak` | 365 | 1 (1, 0) | 0.48 s | 0.06 s | 0.60 s, 98 MB | 0.17 s, 91 MB |
| `bench-k1/ackermann` | 3,551 | 1 (1, 0) | 217.7 s | 1.33 s | 222.8 s, 987 MB | 2.7 s, 245 MB |
| `bench-k1/collatz` | 3,586 | 1 (1, 0) | 225.7 s | 1.34 s | 225.8 s, 1,016 MB | 3.3 s, 249 MB |
| `bench-k1/prime-count` | 3,586 | 1 (1, 0) | 225.9 s | 1.32 s | 225.8 s, 1,021 MB | 3.5 s, 247 MB |
| `bench-k1/sum-loop` | 3,577 | 1 (1, 0) | 222.8 s | 1.39 s | 227.4 s, 1,003 MB | 3.0 s, 244 MB |
| `k1/k1` | 3,639 | 5 (5, 0) | 193.1 s | 1.31 s | 229.8 s, 993 MB | 8.3 s, 251 MB |

In all: 44 closures, 203 roots, 168 compiled with identical objects and the
kernel's Stage A accepting, 35 refused alike. The roots refused alike are
refused downstream of the front end, by both with the same message: more
parameters than the entry wrapper passes, closures before
defunctionalisation, a type former a relevant parameter receives, and the
admission rules (string literals, relevant theorems and axioms, opaque and
unsafe constants). The box ran other work meanwhile, and several of these
runs concurrently (the four large `bench-k1` closures together); the large
closures' times vary by up to about 15 % between runs.

At the time of this measurement five fixtures had no bound form; the
refreeze settled them (`phase1-decline`'s oracle driver; `phase1-boundary`
restated at 49/50 fields, and since 2026-11-12, when ingress reads only what
its seeds reach, at 254/255). One committed closure is not accepted, which
`tests-kernel-front` asserts: `src-diag` (the kernel declines its `sorry`).
`phase1-boundary`'s `fields255` and `tags126` are accepted, and ingress refuses
their roots at `decode`: each reaches a record over IxCC's consumer budget
(`mk255`, `casesOn`).

The kernel's logical entry alone (`checkBytesWith`) declines each closure
tried (`tuple`, `fib`, `abi`, `scalar`, `OS02-plain`) at its first `partial`
definition; its tiered entry behind the committed prelude (`checkBytesTiered`)
accepts them, their prelude records being the committed ones, in 83–91 % of the
front end's acceptance time. A hostile closure is measured under
[resource bounds](#resource-bounds).

## Milestones

| Id | Content | Exit test |
| --- | --- | --- |
| KF-0 | The front end beside the old one, the differential suite, the acceptance and classifier lemmas, the ledger's exception (this change) | `tests-kernel-front` passes; identical annotations, certificates and objects on every role-bound closure the kernel accepts |
| KF-1 | The walk-level annotation statement; the kernel-side lemmas 1–3 composed into direction 1 | fenced, standard axioms |
| KF-2 | The switch (steps 2–5). In progress: steps 2 and 3 done (2026-11-11); steps 4 and 5 (the deletion, the ledger) next | all required checks on the refrozen corpus; the deletion list gone |
| KF-3 | The kernel's bound on hostile levels (kernel-side item 4). Its fix of the blow-up on `let` chains, made in the kernel package on this branch in parallel with KF-2, has landed: the ∀ rule's levels hash-consed in the executed core (first folded with `mk_imax`'s folds, since withdrawn), the level's has-parameter bit cached; and since, the kernel's level walks memoised on shared levels (two interleaved chains at two universe parameters check in milliseconds). Planned: a call budget in the kernel's level comparison, set by the caller and passed by the front end | the hostile `let`-chain closure accepted in time flat in `k` (met: 28 ms at `k = 30` and at `k = 34`); a constant whose level comparison is exponential (the reduction from satisfiability in `docs/kernel.md`) declined within the budget (planned) |
| KF-4 | The closure run (planned, 2026-11-11): the closure of the seeds, the logical entry on it under the default table and committed prelude, the table-restriction check, the run's declarations kept for the typing clause. Done beside it (2026-11-12): IxCC's own reading is of the records its seeds reach (`Src.Ingress.reach`), so a record the target never reaches no longer refuses an artifact by IxCC's limits; the kernel still accepts the whole artifact. What the closure run would add: the kernel's run on the kernel's closure of the seeds (every reference, proofs included, and the recursors, certified-operation ground and literal edges it needs), under the default table and committed prelude, discharging premise (i) natively; the worklist can be shared over an edge function | on every role-bound K1 closure the closure run accepts, and its declarations are a sub-list of the tiered run's up to keys |

## Decisions

**Decided by the owner on 2026-11-11** (decision 5 below): the switch
proceeds now, and the kernel's blow-up on `let` chains is fixed in the
kernel package on this branch, in parallel with the switch (the fix has
landed; what stays exposed is under [resource bounds](#resource-bounds)). The fixtures were refrozen in the role-bound form, and the switch's step 3 followed. Item 6 (the
closure run for premise (i)) was decided the same day (DO-37).

Items 1, 2 and 3 below are the working defaults this work proceeds on, each
awaiting the owner's confirmation. The switch makes the front end as built
the only one, so after step 3 reversing 1, 2 or 3 changes the only front end
rather than choosing between two.

1. **Shape B, the native check of the clauses, for the native path.**
   Working default: yes (above). It reverses the default of the open decision
   on how faithfulness is discharged natively (DO-6, which preferred a
   rebuilt ingress).
2. **The tiered entry.** The front end accepts what the kernel's tiered entry
   accepts: the logical environment model-backed, the `partial` and `unsafe`
   definitions typed and opaque, refused by `Src.Admit` if reached. Working
   default: yes; the logical entry alone declines every closure `ix compile`
   writes.
3. **The artifact's own prelude.** As `ix check-lean`. The committed prelude
   (`preludeFor`, `checkBytes`) works only where the artifact's prelude
   records are the committed ones. Working default: the artifact's.
4. **Unbound environments.** Refused by the front end: with the switch
   decided this follows, since the kernel admits only role-bound
   environments. Since step 3 an unbound closure is refused at ingress. What
   stays unbound: the resource handoff fixtures, read without typing (the
   table of uses above); the catalog pieces went with IxCC's catalog support
   in step 4.
5. **The exposure on `let` chains** ([resource bounds](#resource-bounds)).
   The switch (step 3; the producer and the verifier go together) either
   lands with the exposure documented or waits for the kernel's fix
   (kernel-side item 4, KF-3). **Decided** (the owner, 2026-11-11): the
   switch proceeds now, with the exposure documented, and the kernel's fix is
   made in the kernel package on this branch, in parallel; both land before
   the branch is merged. (The earlier working default held the switch until
   the kernel's typing core had a work budget.) The exposure, measured when
   the decision was taken: acceptance of a role-bound closure of 206 records
   with one constant of `k` nested `let`s, each alone in its own process:

   | `k` | 16 | 20 | 22 | 24 | 26 | 28 | 30 |
   | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
   | erased checker | 0.14 s | 0.14 s | 0.14 s | 0.14 s | 0.14 s | 0.14 s | 0.19 s |
   | kernel front end | 0.03 s | 0.08 s | 0.22 s | 0.80 s | 3.1 s | 14.7 s | 52.2 s |

   The fix has since landed; [resource bounds](#resource-bounds) has the
   measurements after it and what stays exposed.
6. **The native discharge of premise (i)** (added 2026-11-11). Either keep
   the tiered whole-artifact acceptance and prove the three restriction lemmas,
   or add a run of the logical entry on the closure of the seeds under the
   default table and committed prelude. **Decided** (2026-11-11, DO-37 in the
   [roadmap](roadmap.md#open-decisions)): the closure run (KF-4); it costs one
   more kernel run over a subset of the records and a ported closure walk,
   and makes the native and the IxVM routes discharge one statement. The
   tiered acceptance stays as the producer's check either way.
