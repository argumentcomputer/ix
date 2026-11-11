# The front end over the certified kernel

Written 2026-11-11. **Status:** decided by the owner: IxCC takes its type
information and its acceptance of an environment from the certified kernel
(the `IxCK/` package), and its own erased type checker is to be deleted. The
new front end is **implemented beside the old one** (`IxCC.Src.KernelFront`,
[`Src/KernelFront`](../IxCC/Src/KernelFront)), with a differential suite
(`tests-kernel-front`); the switch that makes it the only front end is
**planned** ([The switch](#the-switch)). This is the native discharge of the
premises in the [roadmap](roadmap.md#milestones) (SP-N), together with the
part of HD-1 that takes typing off IxCC's own code.

## Current state

IxCC's front end reads an `.ixe` environment with its own decoder
(`V3.decodeAnonymousEnv`), converts it into the table-free `Src.Program`
(`Src.Ingress.readConsts`), and asks its own erased type checker
(`IxCC/IxCC/Ixon/V3/Tc/`, 24 files, 12,680 lines, adapted from an earlier
Ixon checker of ix, with no soundness theorem) two kinds of question:

| Use | Question | Where | What rests on the answer |
| --- | --- | --- | --- |
| `Tc.checkEnv` | accept every declaration of the closure | `Recheck.ingress` when its `typecheck` flag is set, hence every byte-level verifier (`CompileClaim.verifyBytes`, `checkClaim`, `makeClaim`, `Ring0Sip.verifyBytes`), `ixcc compile` and `check-cert`; also `Src.load`, catalog admission, the resource-validation API and the census | nothing proved: the byte-level theorems carry only `typecheck = true → Tc.checkEnv inp.env = .ok ()` and hold with typing off |
| `Src.Relevance.annotate` | the type of a subterm in a context of opened binders; whether a type reduces to a Π-telescope ending in a sort; the sort of a type and its zero condition over the constant's universe parameters (D18) | the producer, and through Stage A (`Recheck.checkCanonicalRelevance`: the certificate's annotation must equal the annotator's) every byte-level verifier | an untrusted oracle: the recheck path decides the annotation (`Relevance.check`, `checkCanonical`); under the [end-to-end plan](end-to-end.md) it is the relevance clause of the faithfulness premise |
| not typing | block-member keys (`Tc.*ProjAddr`, pure BLAKE3 like every address IxCC computes), `Tc.natFromBytesLE`, `Tc.PrimAddrs.canonical` | ingress, the resource profile's literal pins and its `Eq` | — |

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
   prelude and IxCC's decoder caps as batch limits (`defaultLimits`); and keeps
   the kernel reader's declarations of the same inputs (the logical ones behind
   the prelude, and the tier reader's), which the annotator asks about.

A refusal carries the kernel's reason and classification (rejected or
declined, `TierError.outcome`). Only role-bound environments are accepted.
`ix check-lean` admits a role-bound artifact by the same entry, prelude source
and order; the front end's acceptance differs from it only in the hash
function's implementation (IxCC's pure BLAKE3, ix's Rust BLAKE3 on a recorded
assumption that the two agree).

### The program and its correspondence

`KernelFront.ingress` ([`Front.lean`](../IxCC/Src/KernelFront/Front.lean))
builds the program exactly as before (`Src.Ingress.readConsts` for the chosen
roots), takes the pins from the kernel's admitted table (`pinsOfTable`, the
same role mapping as `Src.Pinned.ofRoles`), and reads the program against the
kernel's reading (`Reading.build`,
[`Reading.lean`](../IxCC/Src/KernelFront/Reading.lean)):

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

| Use | Becomes |
| --- | --- |
| `Tc.checkEnv` at ingress | the kernel's tiered entry (`accept`), mandatory |
| `Src.Relevance.annotate` in the producer | `KernelFront.annotate` (with `checkReachedTypes`) |
| Stage A on the byte-level path | `KernelFront.checkCanonicalRelevance` |
| `Tc.*ProjAddr` (block-member keys) | moved out of the checker's namespace (they are already pure BLAKE3); the kernel's key map already checks them against its own reconstruction (`Reading.build`) |
| `Tc.natFromBytesLE`, `Tc.PrimAddrs.canonical` (the resource profile's literal pins and its `Eq`) | moved out of the checker's namespace |
| `Src.load`, the census, catalog admission, the resource-validation API (which keeps typing as its prerequisite) | the kernel's acceptance where a role-bound environment is read; the catalogs (unbound pieces assembled by IxCC) keep their decoder-level admission, without typing |
| the per-claim `typecheck` flag | removed ([below](#the-typing-flag)) |

## Statements

### The byte-level theorems after the switch

`verifyBytes_immortal_sound` and its siblings
([`CompileClaim/Proof.lean`](../IxCC/CompileClaim/Proof.lean)) conclude today,
among the front-end facts, `inp.env.bindingAddress = c.roleTable` (the
envelope's role table is the claim's), `typecheck = true → Tc.checkEnv
inp.env = .ok ()` and `Src.Relevance.annotate inp.env {…} = .ok
cert.relevance`. After the switch they keep the first and conclude, in place
of the other two, for the kernel front end's input `kin`:

- `KernelFront.ingress envBytes equations roots = .ok kin` with
  `decodeAnonymousEnv envBytes = .ok kin.inp.env`;
- the acceptance (`accept_spec`): the environment is role-bound with binding
  `b`; the kernel's entry ran on `b`'s section, on exactly the envelope's
  records and blobs, and
  `Ix.Kernel.Admission.checkBytesTieredUsing (preludeSource kin.acc.pre) hash
  kin.acc.binding defaultLimits kin.acc.records kin.acc.blobs = .ok (kin.acc.env, kin.acc.tier)`;
  from which the kernel's theorems give, for the logical records, the
  reading's fidelity, a model in every set theory and the strong model, at
  IxCC's hash, the artifact's prelude and the artifact's table;
- Stage A: `KernelFront.annotateChecked kin {kin.inp.program with table} = .ok cert.relevance`.

The acceptance conjunct is then premise (i) of the [end-to-end
plan](end-to-end.md), discharged natively: the kernel accepts the environment
with root `H` under the table `ρ` the envelope carries.

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
4. **A work budget.** The typing core takes time exponential in the size of a
   well-typed constant whose `let`s duplicate a growing subterm (it substitutes
   every `let` eagerly and loses sharing when it reopens binder telescopes), and
   its fuel bounds recursion depth, not work. A step counter threaded through
   the core, with acceptance stated within the budget, is what lets IxCC bound
   its verifier ([Resource bounds](#resource-bounds)).

## The typing flag

The flag (`typecheck : Bool := true` on `Recheck.ingress`, `verifyBytes`,
`checkClaim`, `makeClaim`, `compile`; `--no-typecheck` on `ixcc compile`) never
contributed to a theorem and is not bound by the claim. With the kernel it
goes: acceptance is not optional on any byte-level path, `verifyBytes`,
`checkClaim` and `makeClaim` lose the parameter, `ixcc compile` and
`check-cert` lose `--no-typecheck` (an unbound closure is refused with the
kernel's reason, and `--stats` reports the kernel's acceptance: records, tier
constants and time). A claim's meaning is then "the kernel accepted the
environment with root `H` under the envelope's table and IxCC's object
refines SrcEval on the checked source program read from it", with no hidden
parameter. The claim already names the role table's address (`roleTable`,
validator 7; [byte contract](byte-contract.md)), so the table in that meaning
is the claim's.

## Dependency and the trust ledger

**Modules.** The front end imports `IxCK.Kernel.Admission.Tier` (the tiered
entry, which imports the logical entry and the reader), `IxCK.Kernel.Cached.CoreC`
(the executed core) and `IxCK.Kernel.Ixon.Prelude`: an 82-module closure of
about 49,000 lines, against 13 files before (the codec and the role
vocabulary). It includes the committed role data
(`IxCK/Kernel/Ixon/RoleData.lean`, 13,737 lines of hexadecimal records) through
the prelude module. It does not include the kernel's proof tree
(`IxCK/Kernel/Verify`, `IxCK/Kernel/Model`); theorems that compose with it live
where that tree is built.

**Build cost.** Measured on the build box: see the
[measurements](#measurements) below.

**The ledger** ([trust ledger](trusted-extern-ledger.md)). The dependency
entry's closure grows to the 82 files, each pinned by its SHA-256;
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
- nothing else. The kernel's typing core is exponential on a constant of a
  few hundred bytes whose `let`s duplicate a growing subterm, and IxCC cannot
  meter a function it does not own: no counter is exposed. Admission limits do
  not help (the payload is tiny). A syntactic refusal of `let` chains is
  evadable (the same blow-up through δ-reducts of separate definitions).

The erased checker had no closure-wide budget either ([hardening
design](hardening-design.md)), but it is not exponential on this family: it
opens each `let` as a let-bound local, as Lean's own checker does, and
hash-conses its terms. Measured on a role-bound closure of 206 records with
one such constant (`k` nested `let`s, the constant 200 to 330 bytes), each
acceptance alone in its own process:

| `k` | erased checker | kernel front end |
| ---: | ---: | ---: |
| 16 | 0.14 s | 0.03 s |
| 20 | 0.14 s | 0.08 s |
| 22 | 0.14 s | 0.22 s |
| 24 | 0.14 s | 0.80 s |
| 26 | 0.14 s | 3.1 s |
| 28 | 0.14 s | 14.7 s |
| 30 | 0.19 s | 52.2 s |

Both accept every one. So the switch adds an exposure the erased checker does
not have: a claimant can make the verifier's acceptance take as long as it
likes with a closure of ordinary size. The annotator asks the same core about
`let`-substituted subterms, so a root whose terms carry such a chain costs as
much again in the producer and in Stage A. The guard is a dependency: a step
counter in the kernel's core (kernel-side lemma 4), which the front end would
pass as a budget and report as a decline (milestone KF-3 below). Until then,
the kernel's typing time is outside the verifier's time bound. On every
closure `ix compile` writes, the kernel is faster ([measurements](#measurements)).
The kernel's recursion depth on the verifier's 8 MiB stack is likewise the
kernel's to bound (HD-3 audits it with IxCC's own).

## The switch

The steps that make the new front end the only one, in an order that keeps
the tree green at every commit:

1. **Prerequisites (not this work).** The fixtures refrozen in the role-bound
   form (RL-1 phase 2; the kernel admits only role-bound environments, and
   the committed closures are unbound, selected without recursors, so its
   reader declines their inductive blocks), written by an `ix compile` that
   binds every role whose constant the closure brings in. An earlier `ix`
   bound neither `choice` nor `natLor` in the larger closures, and the
   kernel declined `Classical.choice` there as a non-standard axiom; the
   closures [measured](#measurements) below come from an `ix` that binds them.
2. **Move what is not typing out of the checker** (a refactor, no behaviour
   change): the block-member keys (`Tc.defnProjAddr` and its siblings, already pure
   BLAKE3), `Tc.natFromBytesLE` and
   the pins the resource adapter takes from `Tc.PrimAddrs.canonical` (its
   literal types and `Eq`), into `IxCC/IxCC/Ixon/V3/`.
3. **One commit: the kernel front end becomes the front end.** Held, by the
   working default of [decision 5](#decisions), until the kernel's typing
   core has a work budget. `Recheck.ingress` returns the kernel front end's input (the `Recheck.Input`
   gains the accepted kernel input, or becomes `KInput`); `produceSource` uses
   `KernelFront.annotate`; `checkCanonicalRelevance` is the kernel one; the
   `typecheck` parameters go from `Recheck.ingress`, `compile`,
   `CompileClaim.verifyBytes`, `checkClaim`, `makeClaim`, `Ring0Sip`,
   `Src.load`, the census and the corpus tools, and `--no-typecheck` from
   `ixcc`; the theorems are restated (`CompileClaim/Proof.lean`'s
   `verifyBytes_*_sound` and `_rootShape`, `Recheck/Proof/Parts.lean`'s
   `front_wellAnnotated`, `Compiler/Proof.lean`, `Ring0/Proof.lean`) with the
   acceptance and the kernel Stage A conjuncts, and their fences
   (`IxCCTests/Fences/Compile.lean`) re-recorded; the duplicated producer of
   `KernelFront.Front` folds back into `Recheck.Produce`.
4. **Delete** (a separate commit, no behaviour change): `IxCC/IxCC/Ixon/V3/Tc/`
   (24 files, 12,680 lines), `IxCC/IxCC/Src/Relevance/Annotate.lean` (336),
   `IxCC/IxCC/Ixon/V3/Typed.lean` (34), the typing parts of
   `IxCC/IxCC/Ixon/V3/Validate.lean` (105) and
   `IxCC/IxCC/Ixon/V3/Catalog/Admit.lean` (49), the typing fixtures and their
   suite part (`fixtures/ixon-v4/typing/`, `IxCCTests/IxonV3/TypingFixtures.lean`),
   and IxCC's own binding decoder (`IxCC/IxCC/Ixon/V3/Binding.lean`, 171), whose
   reading the kernel's `admitBinding` replaces; about 13,500 lines.
5. **The ledger last**: the closure and the exception are already recorded;
   the integrity pins re-recorded by the documented procedure; the
   `tests-ixon-v3` typing part and the `tests-relevance` annotator part move to
   `tests-kernel-front`, whose runs over the refrozen corpus become the
   required differential's successor (a corpus-wide `KernelFront` pass in
   `corpus check`).

Suites affected: `tests-ixon-v3` (typing fixtures), `tests-relevance` and
`tests-lam` (annotation mutation draws from the annotator), `tests-recheck`
(Stage A, the hostile and deep families), `tests-pipeline`, `tests-corpus`,
`corpus check` and `census` (every family re-ingested through the kernel),
`ixcc-proofs` (restated fences).

## Measurements

On the build box (64 cores, Lean 4.34.1), 2026-11-11.

**Build.** A cold `lake build IxCC IxCCTests ixcc` before the kernel import:
4 min 31 s wall, 21.6 GB peak, 2,004 jobs. The first build after the import
compiled 66 kernel modules (74 s of module time in all, the longest
`IxCK.Kernel.Cached.ExprOpsC` at 5.7 s) and the new modules in 38 s wall at
1.7 GB peak; the same targets are now 2,165 jobs. The bridge package's cold
build (the kernel's proof tree and IxCC): 2 min 49 s, 4.8 GB.

**The differential.** Every committed corpus family and benchmark fixture
was rebuilt role-bound into scratch by `corpus rebuild` with the tree's `ix`
(the producer commands without `--unbound`), and each closure was run through
both front ends by `tests-kernel-front`: acceptance; the program; for each
root, the annotation, the certificate and `Recheck.run`'s object; and Stage A
of the kernel front end on its own certificate. On every closure both front
ends accept, the programs are equal, and every root's annotation, certificate
and object are identical, or both front ends refuse the root with the same
reason (a root declined downstream still has its annotation compared). No
difference was found. The committed role-bound closures (`tuple`, `fib`, and
since its registration the `phase1-bound` family, whose five closures are the
`phase1-scalar` rows below) are the suite's own and agree the same way.

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

Five fixtures have no bound form yet: the generator fails before it writes a
closure, so neither front end ran. `phase1-decline/loops` and `erase`: the
interpreter oracle prints no line. `phase1-boundary/fields254`, `fields255`
and `tags126`: a record over IxCC's own decoder budget
(`Constant.withinBudget`), which the committed unbound closures of the same
sources stay under.

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
| KF-2 | The switch (steps 2–5) | all required checks on the refrozen corpus; the deletion list gone |
| KF-3 | A work budget threaded through the kernel's core (kernel-side) and passed by the front end | a hostile `let`-chain closure declines within the budget |

## Decisions

The defaults below are the working defaults this work proceeds on. Each
awaits the owner's confirmation; none is decided.

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
4. **Unbound environments.** Working default: refused by the front end.
   Until the refreeze, the old front end stays the default for the unbound
   fixtures.
5. **The exposure on `let` chains** ([resource bounds](#resource-bounds)).
   The switch (step 3; the producer and the verifier go together) either
   lands with the exposure documented or waits for the kernel's work budget
   (kernel-side lemma 4, KF-3). Working default: the switch is held until
   the kernel's typing core has a work budget; steps 1 and 2 may proceed.
   The reason, measured: acceptance of a role-bound closure of 206 records
   with one constant of `k` nested `let`s, each alone in its own process:

   | `k` | 16 | 20 | 22 | 24 | 26 | 28 | 30 |
   | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
   | erased checker | 0.14 s | 0.14 s | 0.14 s | 0.14 s | 0.14 s | 0.14 s | 0.19 s |
   | kernel front end | 0.03 s | 0.08 s | 0.22 s | 0.80 s | 3.1 s | 14.7 s | 52.2 s |
