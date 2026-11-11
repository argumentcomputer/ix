# Certification: grounding IxCC in Ixon and IxCK

Written 2026-11-09; reworked 2026-11-10 around the goal of
[end-to-end certification](end-to-end.md) for the x86 and Aiur back ends,
grounded in Ixon and the certified kernel IxCK, and on 2026-11-10 again
around the owner's architecture, in which kernel acceptance and the image's
faithfulness are premises discharged by other proofs; and on 2026-11-11
around what the certified IxVM work's typing claims actually conclude: the
first premise is now the existence of a model, with laws, of the closure of
the target and the table's theorems, not acceptance of an artifact
([the restatement](#the-restatement-of-2026-11-11)). **Status:** the spine
below (SP-0 to SP-2, SP-A, SP-N) is **planned**; its adequacy core is
research-grade. SP-A's typing-transport question is answered: the model gives
no typing for subterms, so typing derivations become part of the second
premise. CD1 is partly done and its remaining clauses become the faithfulness
premise; CD2 is planned, off the critical path for grounding; CD3 is
planned, demoted to a separate product; CD4 *is* the spine's adequacy work.
The [roadmap](roadmap.md#plan) schedules the items; the
[compile boundary](compile-boundary.md) records what the current theorems
cover.

## What is proved today

`Recheck.sound` ([`Recheck/Proof/Soundness.lean`](../IxCC/Recheck/Proof/Soundness.lean))
and its relatives (`Recheck.RcReplay.sound`, `Recheck.compiled_sound`, the
`CompileClaim.verify*_sound` family, `verifyRing0Sip_sound`) say: if the linked
object returns `w` on a root and `Nat` arguments, then either the checked
source program `a.src` evaluates under SrcEval to a value whose view is `w`,
or that source *goes wrong* (`Front.GoesWrong`: it gets stuck, traps, or
returns a value the root's view rejects); a source that does not go wrong
gives an object that does not; a diverging source gives an object that
diverges or fails for a resource. At claim roots the root-shape corollaries
(`verifyBytes_{immortal,zeroRc}_rootShape`,
[`Recheck/Proof/RootShape.lean`](../IxCC/Recheck/Proof/RootShape.lean)) narrow
the view case to a result off the root's declared shape.

The chain from the bytes to the object's result, link by link:

| Link | Content | State | Under the plan |
| --- | --- | --- | --- |
| Claim bytes | `CompileClaim` encodes and decodes exactly | Proved (round trip). Binds the environment root, the role table's address (absent for an unbound environment), target, policy, arity and object hash only: not the certificate, the sidecar, the typing flag or `Recheck.Config` | SP-0: the claim also binds the image digest |
| IxCC's reading | `.ixe` bytes to IxCC's environment (`V3.decodeAnonymousEnv`), pure BLAKE3 authentication, canonicity evidence | Proved that it ran; IxCC's own framing of both envelopes, the role binding authenticated and decoded, pins from its role table ([byte contract](byte-contract.md)) | SP-0: pure BLAKE3 for every address; off the trusted path once faithfulness is a premise |
| IxCK's reading | the same bytes to IxCK's records and declarations | Proved by IxCK (`checkBytesWith_reading`, [`IxCK/Kernel/Admission/Theorems.lean`](../../IxCK/Kernel/Admission/Theorems.lean)); needs a role binding | the reading the premises are about |
| The two readings agree | IxCC and IxCK decode the same constants under the same keys | **Absent.** They share the constant decoder and the role vocabulary (`Ix.Kernel.Role`), not the framing or the reading into declarations | Not needed: premise (ii), or one reading by construction (SP-N) |
| Kernel acceptance ⇒ strong model | `checkDecls_sound`, `checkBytes_strongModel` | Proved by IxCK. **Not a premise of any IxCC theorem** | Premise (i), restated: a model with the laws of the closure of the target and the table's theorems, discharged by an IxVM `checkEnv` claim on those seeds or by a native run on that closure |
| The target names a kernel constant | `c.target` and IxCK's key agree | **Absent.** IxCC keys block members by projection addresses computed with the native BLAKE3 extern ([`Src/Ingress.lean`](../IxCC/Src/Ingress.lean)) | SP-0 (pure hashing, the claim binds the target) and premise (ii) |
| IxCC's erased type checker | `Tc.checkEnv` ([`Ixon/V3/Tc/Driver.lean`](../IxCC/Ixon/V3/Tc/Driver.lean)), run when the `typecheck` flag is set | **No soundness theorem**; every guarantee holds with typing on or off | Off the guarantee path (DC-3) |
| Ingress | environment to Src program (`Src.Ingress.ofEnv`) | Proved that it ran; no correspondence to IxCK's terms | Premise (ii) |
| Unfolding table | each entry valid in the kernel's model | Syntactic checks and the axiom closure proved (`checkAxiomClosure_sound`, [`Src/Table/Check.lean`](../IxCC/Src/Table/Check.lean)); **no semantic lemma** | SP-0's lemmas; the statements in premise (ii) |
| Relevance annotation | positions tagged irrelevant are types or proofs, and conversely | Structural soundness (`check_sound`, [`Src/Relevance/Proof/Sound.lean`](../IxCC/Src/Relevance/Proof/Sound.lean)); `checkCanonical` and `annotate` have no theorem | Premise (ii), against the kernel's typing, both directions |
| Lazification | by-name modes only (`Lazify.run_modeEq`, [`Src/Proof/Lazify.lean`](../IxCC/Src/Proof/Lazify.lean)) | Syntactic; meaning preservation not proved | Premise (ii); by-name slots are handled inside SP-1's relation |
| SrcEval and the kernel's model | adequacy | **Absent.** [`Models/KernelBridge`](../../Models/KernelBridge/README.md) is conditional, covers one real root and cannot reach recursion | SP-A, SP-1 |
| `GoesWrong` | the escape clause | Unbounded; a dishonest certificate can choose it; the view case is narrowed at claim roots | SP-1's progress |
| Src to typed x86 | erasure, the middle end, Fir, Own, Cfg, Lir, selection, allocation, layout | **Proved**, standard axioms | Done |
| Encoder, streams, ELF | E1 per form; E2 and `ELF.check_sound` | **Proved** | Done |
| Machine, loader | the byte machine is the processor; the loader maps what `ELFRead` parses | **Assumed** ([trust ledger](trusted-extern-ledger.md)) | XB-2 for the machine; the loader stays assumed |
| Driver | the caller that loads the object and calls its exports (the standalone executable's shell; the native suites' test shell), with symbol targets checked in the written file | **Assumed**; `X86.Driver.Ok` is satisfiable (`driver_exists`); the C driver is gone (X1); a caller with two call sites is modelled (`X86.LinkedAt`, `Recheck.sound_at`) and a non-faulting model run writes only the model's mapping (`X86.ByteAgree`) | X0-P for standalone executables |
| Readback | the observation names a value | Proved at the machine level; no statement in the model | SP-0's lemma |

Two open items keep the names that code comments use:
- **S6**: nothing relates `a.src` semantically to the ingested program. What
  is proved about the front end is that it ran and how (the rows from IxCC's
  reading to lazification). The faithfulness premise (SP-0) and adequacy
  (SP-1) below close it.
- **S8**: nothing relates SrcEval to the meaning of the Lean definition in
  the kernel's model. SP-A and SP-1 close it for the first fragment.

Three facts follow, each a reason for the plan's order.

- **The escape is the certificate's.** No theorem says that any check
  excludes `GoesWrong`, and a dishonest certificate can make SrcEval stuck or
  make it return a value the view rejects. A reviewer's probe did the second
  before `checkCanonical` ran on every program. So "the object returned
  `true`" tells a consumer nothing unless `¬GoesWrong` is known some other
  way, today only by running SrcEval to completion (`sound_of_eval`).
- **Typing contributes nothing proved.** The erased checker is about 12,700
  lines adapted from ix's Ixon-v3 checker, with no whole-checker soundness
  theorem
  ([trust ledger](trusted-extern-ledger.md#ix-frontend--ixon-v4-source-boundary)),
  and `verifyBytes`'s guarantees hold for both values of its `typecheck` flag
  ([compile boundary](compile-boundary.md)). With typing off, a bogus
  equation theorem passes `checkEqn` (which checks the theorem's type and
  axiom closure, not its proof) and the object computes the bogus right-hand
  side, with every theorem still true. Typing also dominates verification
  time ([hardening design](hardening-design.md)).
- **One allowlisted kind of entry contradicts IxCK's model.** SrcEval
  evaluates an `opaqueByValue` opaque through its stored value
  ([`Src/Semantics.lean`](../IxCC/Src/Semantics.lean), allowlist in
  [`Src/Pinned.lean`](../IxCC/Src/Pinned.lean)); IxCK's model records no
  value equation for opaques
  ([`IxCK/Kernel/Ixon/Values.lean`](../../IxCK/Kernel/Ixon/Values.lean)).

## Target statements

Notation: `kenv` is IxCK's environment read from the claim's bytes under the
bound role binding with pure BLAKE3; `kc` is IxCK's key for the claim's target;
`enc w` is the kernel term for an observation (a `Nat` literal, or the `j`-th
constructor of the result type).

| Form | Statement | Verdict |
| --- | --- | --- |
| Reduction | the object returns `w` ⇒ `kc ns` reduces or converts to `enc w` | **Not achievable** for the fragment that matters: IxCK never unfolds theorems, so well-founded recursion has no reduction to a value, and structural recursion would need SrcEval's equation rewriting simulated by `brecOn` reductions. This was the bridge's approach |
| Denotation with escape | ⇒ in every model with the laws `⟦kc ns⟧ = ⟦enc w⟧`, or the source goes wrong | Adds the kernel but keeps the certificate's escape; not useful to an evaluation-axiom consumer |
| **Grounded** | as above without the escape, for programs passing a checked fragment condition, quantified over every model (the public `Model`) with the laws of [the law table](#the-law-table) of the kernel's reading of the closure of the seeds, under the two premises below (existence; faithfulness and typing). Split into *soundness* (a returned value reads back as the denotation) and *progress* (no stuck, no trap) | **The target** |
| Evaluation axiom | soundness for a closed, level-free `Bool` term `e`, plus a binding of `e` to a compiled root | What IxVM needs to discharge `ax : e = true` |

A form over every model of the public structure *without* laws is false in
general (δ and ι do not hold there); the nearest achievable is models with
the laws. A form for roots using `opaqueByValue` or recorded interpretations
is false over all models with the laws (no law gives an opaque a value); the
nearest is models restricted to the interpretation.

## The architecture: premises discharged by proofs

IxCC does not have to establish by its own proofs that it reads the same
program as the kernel, or that the program is well typed. The owner's
architecture makes both *premises about content addresses*, discharged by
other proofs and composed by aggregation of claims about the same addresses:

> "If both accept the same bytes, and we can use a certified IxVM to create a
> certificate of typing, then presumably we could enforce that IxCC only runs
> over inputs accepted by IxC via an IxVM proof (provided the IxVM <-> IxC
> certification is solid)." (The owner, 2026-11-10; IxC is IxCK's former
> name. The plan is written on this basis, to be confirmed as DC-3 in the
> [roadmap](roadmap.md#decisions-to-confirm).)

IxCC's top-level statements are about the *seeds* `S` of a checked source
program `P` (an image with digest `D`) for target `c`: `c` and every theorem
`P`'s unfolding table names. Let `E` be the kernel's reading of the closure
of `S` under a role table (the kernel's reader, its prelude, and the records
reachable from `S`). The statements take two hypotheses:
1. **Existence.** `E` has a model with the laws of [the law
   table](#the-law-table) in every set theory.
2. **Faithfulness and typing.** `P` satisfies the faithfulness clauses with
   respect to `E`: it is the installed and lazified program read from the
   same records, each Src term corresponding node for node to the kernel
   reader's term (`let`s kept) whose annotation `E` stores; its `eqn` and
   `csimp` entries name theorems of `E` with the right statements; its
   relevance annotation is the one the kernel's typing judgement gives (every
   position tagged irrelevant is a type or a proof at its profile, and every
   proof position is tagged irrelevant); its pinned identities are the
   table's ([CD1](#cd1-the-front-end-theorem) lists the clauses). And every
   value, rule right-hand side and equation SrcEval runs has a typing
   derivation in `E` in the kernel's rules (`Infer`, `DefEq`, `Red`,
   [`IxCK/Kernel/Rules/Rel.lean`](../../IxCK/Kernel/Rules/Rel.lean)).

IxCC's obligations are then two theorems, kept apart because their
consumers differ: **soundness** (if SrcEval returns `v` for `c` on literal
inputs, `c` applied to them denotes what `v` reads back as, in every model of
`E` with the laws), which needs premise (ii) only; and **progress** (on
fragment-checked programs SrcEval is never stuck and never traps), which also
needs premise (i). The evaluator route's discharge of `ax : e = true` uses
soundness; the x86 claim uses both; removing `GoesWrong` is progress.

A consumer discharges existence with an IxVM `checkEnv` claim whose leaves are
`S`, and faithfulness and typing with the kernel circuit's lowering claim for
`(S, D)`, which has the kernel's reading and the types and checks the image
clause by clause; or natively (SP-N below). Composition is by aggregation of
claims about the same addresses, the mechanism IxVM already has for
conditional claims. IxCC embeds no proof verifier. That an accepted IxVM claim
gives a model is the IxVM workstream's consistency theorem, an external
dependency of this plan.

### The restatement of 2026-11-11

Until 2026-11-11 the first premise read "IxCK accepts the environment with
root `H` under role table `ρ`", discharged by an IxVM typing proof paired with
the compile claim on `(H, ρ)`. What the certified IxVM work (pull request #678
and its follow-up branches; none of it in this repository) states shows that
shape is wrong on four counts:

- **The conclusion is a model, not an acceptance.** For an accepted `check` or
  `checkEnv` claim in its default context (the kernel's default role table,
  validated; no user axioms; no assumed leaves), the statement is: the run
  exhibits a BLAKE3 collision, or the *claimed environment* has a model in
  every set theory. Neither of the kernel's entries is mentioned. Other role
  tables, user axioms and evaluation claims are outside it.
- **The subject is the closure of the claim's seeds, not an artifact.** The
  claimed environment is the kernel's reading, under the default table and
  behind the committed prelude, of the closure of the seeds in the records the
  run loaded (references, the certified operations' ground and literal
  edges, recursors), without the auxiliary constants of the kernel's
  inductive models. A seed that is `unsafe` or `partial` is refused, so a
  `checkEnv` claim over the whole of an `ix compile` artifact, which always
  holds `partial` definitions, is refused; its leaves must be safe constants.
  Records are named by their addresses, so the claimed reading is a function
  of the seeds and the table, whatever file the records came from (up to the
  order of the closure and unauthenticated reducibility hints, which do not
  change meaning).
- **The table theorems must be seeds.** An equation or `csimp` theorem is not
  in its function's closure. A model of the target's closure alone need not
  make it true, and two claims give two unrelated models, so the claim must
  be one `checkEnv` claim whose leaves include the target and every table
  theorem.
- **The role table differs.** The statement covers the default table, which
  binds every role; `ix compile` writes a table per artifact binding exactly
  the roles whose constants the artifact holds. By reading, for an artifact
  this repository's `ix` compiles at the committed toolchain, each such table
  binds a role to the address the same compiler gives the role's constant,
  which is the address the default table binds, so it is a restriction of the
  default table; that is not proved, and is checkable per artifact by
  decoding both tables. The bridge is a lemma beside the kernel's reader: the
  reading of a closure is the same under the default table and under a
  restriction of it, when the closure holds no constant of a role the
  restriction leaves unbound (which `ix compile`'s role selection ensures).
  Planned; not stated on either side.

What the IxVM statement still lacks for IxCC, as read on 2026-11-11:

- **It is a reduction, not yet a theorem.** The consistency theorem takes
  eight per-layer obligations (from the circuit's soundness to the assembly)
  as hypotheses; none is discharged in the trees read.
- **It does not fix values.** The claimed environment is related to the
  reader's declarations by name, level parameters and (annotated) type only;
  a definition may be stored as some other kind, or with some other value. A
  model's δ law is then about whatever value is stored, and the statement does
  not exclude `def P : Prop := False; theorem bad : P` being read with `P` an
  axiom. IxCC needs every stored definition to be the record's definition (its
  annotated value), and every recursor's rules the record's.
- **It exposes no typing.** The conclusion is the model alone; the derivations
  the proof builds per declaration (its judgement package over the kernel's
  rules) are not in it, and a model gives no typing for subterms. Typing is
  therefore part of premise (ii) here.

### The law table

What each SrcEval rule, and each kind of unfolding-table entry, needs of a
model, which law supplies it, and the law's state in the certified IxVM work
on 2026-11-11 (this repository's public `Model` has `mem`, `false_empty` and
`eq_equality` only; its internal `EnvModelM` carries all of the laws for an
accepted environment). *Typing* means the step also needs an argument's
denotation to lie in its domain, which only premise (ii)'s derivations give.
**Blocks** marks what the first grounded fragment cannot do without.

| Rule or entry | Fact about the model | Law | State there | Typing | First fragment |
| --- | --- | --- | --- | --- | --- |
| E1 `var`, by-name slots | a variable denotes its slot's value; a suspended term its denotation in its own environment | none: how `Denotes` reads variables and binders | in every model | no | yes |
| E2 `sort`, `pi` → `irr` | none (a type is never applied: applying `irr` is stuck) | none | — | no | yes |
| E3 literals | a `Nat` literal denotes its constructor form | none: `Denotes` reads literals so | in every model | no | yes |
| E4 `lam` → closure | a λ denotes its graph on the domain (the proof point in regime 0) | none: β and function η hold by the reading | in every model | — | yes |
| E5 `let` | the reader's term, `let`s kept, denotes what its stored annotation (the `let`s substituted) denotes | none: a substitution lemma for `Denotes` and "the annotation pass preserves denotation" | stated on neither side | no | **blocks** (Lean elaborates `let` and `have`) |
| E6 `proj` | the `i`-th projection of a constructor application is its `i`-th field | the projection of a constructor | to build | yes | **blocks** (instance methods, structures with proof fields) |
| E7 `app`, strict, by name, `irr` | application is graph application; by-name and strict agree (no effects) | none | in every model | yes (β needs the argument in the domain) | yes |
| E8 δ, a definition | a stored definition denotes its value, at the levels its use induces | δ (`defn_value`) | a field, proved, on a follow-up branch (not on the pull request's head) | no | **blocks** until the claim fixes values |
| E8, level instantiation | a constant depends on the level assignment only through its own parameters | level-parameter irrelevance | a theorem of the internal-backed model, not public | no | **blocks** (every level assignment) |
| E8, `prim` entry; F6 | the operation on literals denotes the literal of its value, for all literals (no `pow` cap) | the `Nat` accelerations | to build | no | **blocks**, unless derived from δ, ι and the role specifications (2–4k lines on IxCC's side) |
| E8, `eqn f thm` | `⟦f xs⟧ = ⟦rhs xs⟧` for arguments in the binders' domains | none: derived from `mem` of the stored theorem and of `Eq`, and `eq_equality` (an inhabited `@Eq A a b` forces `a`, `b` into the domains, since a graph read off its domain is empty, and then equal) | `mem`, `eq_equality` fields everywhere; the derivation is IxCC's lemma | yes (the arguments) | yes, with the theorem a seed |
| E8, `csimp f g thm` | `⟦@f⟧ = ⟦@g⟧` | as `eqn` | as `eqn` | no | yes, with the theorem a seed |
| E8, `case` entry; F5 | `T.casesOn` on a constructor is the selected minor on its fields | δ (`casesOn`'s value) and ι | δ and ι fields, proved | yes | yes |
| E8, `opaqueByValue` | an opaque denotes its stored value | none, by design | — | — | excluded |
| E8, theorem, axiom, other opaque, `unsafe`, `partial` | none: stuck | — | — | — | excluded by the fragment check (progress) |
| A1 β on a closure | graph application on the domain; SrcEval's `propWhen` gate agrees with the binder's regime | none | in every model | yes | yes |
| A2 partial applications; A3 stuck | none | — | — | — | yes |
| F1 constructors; `Nat.zero`, `Nat.succ` to literals | a constructor is its constant; `Nat.succ (lit n)` and `lit (n+1)` denote alike | none: the literal reading | in every model | no | yes |
| F2 ordinary ι, `Nat` literal majors | every stored rule computes as Lean's | ι (`iota_rule`) | a field, proved, on the same follow-up branch since 2026-11-11 | yes | yes |
| F3 subsingleton ι without the major | the major denotes the proof point, which is the constructor application, with indices equal | ι, proof irrelevance and the `Eq` derivation above | as ι | yes | yes (`Decidable` does not need it; `Eq.rec` casts do) |
| F4 empty recursors trap | no member of an empty type | `false_empty`-like emptiness of the inductive's denotation, from ι and `mem` | — | yes | progress only |
| F7 `Quot.mk`; F8 `Quot.lift` | `Quot.lift f h (Quot.mk a) = f a` | ι (the quotient's rules are stored as recursor rules) | as ι | yes | later fragment |
| E9 strings | — | — | — | — | later fragment |
| `lazy` entries | none: they change evaluation modes only (`Lazify.run_modeEq`) | — | — | — | yes |
| `inline` hints | none: no semantic effect | — | — | — | yes |
| `recKind` (ordinary, subsingleton, empty) | the kind is right at the profile | a faithfulness clause, decided with typing | — | yes | yes |
| relevance (`irr` at concrete levels) | an `irr` position is a type or a proof there, and conversely | a faithfulness clause; level irrelevance | — | yes | yes |
| (all rules) typing | every derivation of the kernel's rules is sound in every model with the laws | `infer_sound` and `defeq_sound` restated over the public model (they need δ, ι, the projections, structure and unit-like η and the `Nat` rows) | stated over the internal invariant only | — | **blocks** |

The blocking rows for the first fragment are therefore: values fixed by the
IxVM claim (or the native route), typing in premise (ii) with the rules'
soundness over the public model, `let` (ζ), the projection of a constructor,
the `Nat` operations, and public level irrelevance. Quotients, strings and the
data primitives block only later fragments. SP-0 states the laws in Lean as
an explicit structure of hypotheses about a model, named as on the IxVM side
where a law exists there, so that the statements elaborate here before any of
that work lands.

**What this removes from IxCC's obligations.**
- A soundness theorem for IxCC's erased type checker. It stops being part of
  any guarantee. Its remaining uses are untrusted production: the relevance
  annotator works through its expressions and conversion, and the producer
  can reject ill-typed input early with a diagnostic. On the verifier path it
  is at most an optional filter ([roadmap](roadmap.md#decisions-to-confirm)).
- A proof that IxCC's decoder and IxCK's reader agree. Either the party that
  holds the kernel's reading checks the image against it (the lowering claim),
  so IxCC's own decoder is not on the trusted path; or IxCC's ingress is
  rebuilt on IxCK's reader, so there is one reading by construction. The
  second needs IxCC to import IxCK's reader
  ([`IxCK/Kernel/Ixon/Reader.lean`](../../IxCK/Kernel/Ixon/Reader.lean), which
  imports IxCK's frontend, role-table and record modules), widening a
  dependency the [trust ledger](trusted-extern-ledger.md) records as the
  codec's 11 modules, and rewriting ingress over IxCK's terms, which regroup
  blocks, rewrite projections and model nested inductives with auxiliary
  blocks. Which one applies to which route is an [open
  decision](roadmap.md#open-decisions).
- The relevance clause as a theorem about IxCC's own classifier. It becomes a
  check against the kernel's typing judgement, which the party holding the
  types decides. `checkCanonical` and the byte-level re-derivation of the
  annotation stay as IxCC's own early refusals, untrusted.

**What it does not remove.** Soundness and progress of SrcEval for the
kernel's models. Existence says the environment has a model, and typing says
its terms are well typed; neither says that SrcEval computes the denotation.
They are what those proofs consume.

## The spine's work

In dependency order. Sizes are estimates, by comparison with erasure's
simulation over the same evaluator (10.1k lines,
[`Lam/Erase/Proof`](../IxCC/Lam/Erase/Proof)), the bridge's `Nat`-only
simulation (1.9k), IxCK's reader (1.3k) and IxCC's ingress (0.3k).

### SP-0. Same bytes and the conditional statement

**Planned; engineering, with small lemmas.** IxCC must consume exactly the
bytes the IxVM proof is about and state what it guarantees about them.

- **The same bytes.** IxCC reads role-bound (version-5) environments, which
  IxVM's claims are about and this repository's `ix compile` writes
  (implemented: [`Ixon/V3/Env.lean`](../IxCC/Ixon/V3/Env.lean), the
  [byte contract](byte-contract.md)); the fixtures' unbound envelope is a
  bridge, not the design.
- **The same hash.** Every address in the statement is the same mathematical
  function as in IxVM's claims: pure BLAKE3 (`Address.blake3Pure`) on the whole
  verifier path, including block-member projection addresses, which ingress
  computes today with the native extern
  ([`Src/Ingress.lean`](../IxCC/Src/Ingress.lean)). The byte-level theorems'
  one non-standard axiom is removed: by reading, it comes from a
  `native_decide` proof inside the Blake3 package's `finalizeWithLength`
  whose proposition is a bound on the output length, provable from
  `System.Platform.numBits_eq`.
- **The same identities.** Pinned identities come from the role table, as
  IxVM's do (implemented for role-bound closures, `Src.Pinned.ofRoles`); IxCC's
  fixed pins ([`Src/Pinned.lean`](../IxCC/Src/Pinned.lean)) stay for unbound
  closures.
- **The claim binds what composition needs.** The target and the image digest
  `D`, which together determine the seeds `S` (the target and the theorems
  `D`'s table names); the environment root `H` and the role table `ρ` stay as
  what IxCC read (today the claim binds the root, the role table, the target,
  the policy, the arity and the object hash; the image digest waits for the
  image). The verifier checks that `D` is the digest of the checked source
  program it compiled. A consumer pairs the claim with an IxVM `checkEnv`
  claim whose leaves are `S`, in the default context, and with the check that
  `ρ` is a restriction of that claim's table.
- **The conditional statement.** The laws as an explicit structure of
  hypotheses about a model (named as on the IxVM side where a law exists
  there); the faithfulness and typing predicate defined in Lean, with a
  structural map from IxCK's reader terms (`let`s kept) to `Src.Term` as its
  specification (nested inductives excluded); soundness and progress as
  separate propositions; the [x86](end-to-end.md#x86-the-proved-pipeline)
  and [evaluator](end-to-end.md#aiur-form-i-the-fixed-evaluator-circuit-first)
  statements, composed from today's object theorem, the two premises and
  soundness and progress taken as explicit hypotheses, which SP-1 discharges.
- **The small lemmas**, in every model with the laws:
  - `eqn f thm` and `csimp f g thm`: from `mem` (the stored theorem, and
    `Eq`) and `eq_equality`, which are fields of the public model already: an
    inhabited `@Eq A a b` forces `a` and `b` into their domains (a graph read
    off its domain is empty) and then equal; so `⟦f xs⟧ = ⟦rhs⟧` for
    arguments in the binders' domains and `⟦@f⟧ = ⟦@g⟧`; stated once, for
    IxCC and for an evaluation-axiom discharge path alike;
  - `case T`: δ on `T.casesOn` and ι on its recursor;
  - the fifteen `Nat` primitives (fourteen binary operations and `pred`,
    [`Src/Prim.lean`](../IxCC/Src/Prim.lean)): from the `Nat` accelerations
    law if the kernel side adds it, stated on all literals (the kernel's
    reduction table `natOpResult`,
    [`IxCK/Kernel/CoreDefs.lean`](../../IxCK/Kernel/CoreDefs.lean), declines
    `pow` above an exponent of `2^24`, a limit of reduction, not of meaning);
    otherwise derived by induction from δ, ι and the role specifications'
    equations, which the role table's admission checks;
  - recursor kinds: proof irrelevance, ι and emptiness;
  - `let`: a substitution lemma for `Denotes` and "the annotation pass
    preserves denotation", relating the reader's term to the stored one;
  - readback: an observation's tag is the constructor index, so it names a
    model value; `opaqueByValue` and recorded interpretations are excluded.

*Size [estimate]:* 6–13k lines: the envelope, hashing, pins and claim
binding 1.5–3.5k; the faithfulness predicate and term map 1–2k; the
statements and composition 0.5–1k; the lemmas 3.5–7k. *Calendar:* 2–4
months. *Exit:* the conditional statements fenced for the immortal and
zero-RC policies with adequacy as their one remaining hypothesis; the lemmas
fenced; the byte-level fences show the three standard axioms only; the K1
fixtures regenerated as role-bound environments verify under the new claim
format.

### SP-A. Typing transport, then an adequacy spike

**Planned (research).** *The typing-transport question, answered
2026-11-11.* A model, with all its laws, says nothing about the subterms of
a stored value: `Denotes` reads an application as graph application whatever
the argument, and a graph applied off its domain is empty. β at a local λ, a
closure passed as an argument, an equation used at its arguments and ι at a
major all need the argument's denotation in the domain, which only typing
gives. Existence (premise (i)) does not carry it: the IxVM statement concludes
the model alone, and the derivations its proof builds per declaration are not
in its conclusion. So typing is part of premise (ii): every value, rule
right-hand side and equation SrcEval runs has a derivation in the kernel's
rules, and the fundamental lemma reaches subterms by inverting it. Two kernel
facts are then needed, both planned on the kernel side and neither in this
repository: the derivations' soundness (`infer_sound`, `defeq_sound`) stated
over the public model with its laws (today over the internal carrier and
`RulesInputs`, which a public model does not supply); and, on the IxVM route,
the derivations themselves exposed with the claim (its records over the
rules) or proved by the lowering claim. On the native route they come from the
kernel's own runs (the run-to-derivation lemmas the bridge package proves).

The spike: soundness on `fib` from `bench-k1`, then on
`decide (fib 10 = 55)`, so that the `Decidable` case is tested early, end to
end. Denotational, not by reduction; over every model with the laws; the
environment from IxCK's reading of the fixture bytes; partial correctness
*with* progress; a hand-built correspondence for the few constants involved;
the typing derivations from the kernel's runs. *Exit:* the spike's theorem
fenced or a stop report naming what failed (dependent types, level-exact
relevance, by-name positions, subsingleton elimination without the major).
*Size:* 1–3 months [estimate]. Runs in parallel with SP-0 and the evaluator
interface.

### SP-1. Adequacy and progress on the first fragment

**In progress (since 2026-11-11; [the grounding library](#the-grounding-library-sp-1-in-progress)).** CD4's relation and progress, discharging SP-0's
hypotheses:
- a relation between SrcEval values and model elements, indexed by the
  kernel types the derivations give: literals to literals, constructors to
  constructor applications, closures and partial applications to functions on
  related arguments of the domain, `irr` to the denotation of its kept term
  (a proof denotes the proof point); environments slot by slot; step-indexed
  by SrcEval's clock;
- the fundamental lemma by induction on SrcEval's clocked definition, each
  rule discharged by SP-0's lemmas and the laws, with domain membership at
  each β, ι and equation from the derivations of premise (ii);
- progress: related terms never get stuck or trap. Traps are unreachable (the
  major of an empty eliminator would denote a member of ∅, and premise (i)
  gives a model). Stuckness needs the fragment condition, checked on `a.src`:
  no relevant axiom, theorem or non-allowlisted opaque; no string major; and
  the faithfulness premise's relevance clause in both directions;
- the grounded statements for `verifyBytes` (immortal and zero-RC) and for
  the evaluator route, conditional only on the two premises.

**Why a semantic relation, not a simulation by reduction.** The other way is
to simulate SrcEval by the kernel's reduction relation (`Red`) and conclude
by `red_sound`. The certified IxVM work's rules now have the moves that route
lacked here (an equation's proof rewriting its left side, a theorem
unfolding, reduction under an argument), so recursion through equations is no
longer out of reach. What remains against it: every certified β and every
equation rewrite carries a typing derivation of the *runtime* term (the
argument, the instance of the equation), which is a substitution instance
built during evaluation, so the simulation needs subject reduction for the
kernel's rules, which Lean's type theory lacks syntactically under
definitional proof irrelevance; and SrcEval never builds the proofs it skips,
while `Red` on `Decidable.isTrue h` needs `h`'s typing. The semantic relation
needs typing only for the stored terms (by inversion of their derivations),
relates skipped positions to their denotations without building them, and
uses the laws directly. *Size [estimate]:* the semantic relation 14–30k lines
in all (the relation and fundamental lemma 10–20k, by comparison with
erasure's simulation over the same evaluator, 10.1k, and the bridge's
`Nat`-only simulation, 1.9k; the uses of derivations at opened subterms 2–5k;
progress 2–5k); the simulation by `Red` 12–20k plus subject reduction, which
is research of unknown size. *Calendar:* 6–12 months after SP-A. *Exit:* both
[first-fragment tests](#the-first-grounded-fragment), fenced with the
standard axioms.

### The grounding library (SP-1 in progress)

**In progress since 2026-11-11; landed so far: the fundamental lemma from a
check (G1a), the generic `case` lemma and the root theorem, with `fib` and
`decide (fib 10 = 55)` as its instances (G1b).** The library `IxCCGrounding`
(`IxCC/IxCCGrounding/`, a Lake library of IxCC's package beside the production
library, built and run by the required check `ixcc-grounding`) is the real
development the adequacy spike (SP-A) recommended. It is the one library that
imports the kernel's model (`IxCK.Kernel.Denotes`, the statement half, in
`IxCCGrounding.Laws`); `check-build-graph` refuses an import of it, or of the
model, from the production library or from any program of the shared build.

**What is proved, fenced on `propext`, `Classical.choice` and `Quot.sound` or
fewer (`IxCCGrounding/Fence.lean`, 56 exact assertions):**

- *Soundness at a root* (`rootSound`, in `IxCCGrounding.Root`). For every
  program, kernel reading `env`, key map, level parameters, certificate
  annotation and finite set `Sl` of constants with the checked facts
  (`GroundFacts`, `CaseFacts`, `RootFacts`); every set theory and every model of
  `env` with the laws; assuming `SitesOk`: if SrcEval runs the root on
  first-order arguments to a value whose readback names a kernel term at the
  result type (`FoObs`, its tag checked by `ResultTag`), then, at every level
  assignment, the root applied to the arguments' terms denotes what that term
  denotes. Its instances: `fibRoot` (a root `Nat → Nat`: `fib n` denotes the
  literal SrcEval reads back) and `decideRoot` (a root `Bool` read back as
  constructor `1` denotes the kernel's `Bool.true`).
- *The fundamental lemma from the check* (`allP_of_check`, and its clause for
  constants, `const_of_check`): under the check and `SitesOk`, each of SrcEval's
  eight mutual functions returns values related to what their kernel
  counterparts denote, at every clock. F5's meaning at each `case` constant is no
  longer a hypothesis (`caseFires_of_check`).
- *The generic `case` lemma.* Model side (`caseIota`): at a `case` constant whose
  stored `casesOn`, recursor, rules and constructors have the checked shape,
  `casesOn` applied to arguments that fit its type, the last at a graph-regime
  site, with the major the image of constructor `j` at the `case`'s parameters and
  levels applied to as many fields as the constructor has, is minor `j` applied
  to the fields, along a graph-regime chain. By δ on `casesOn`, ι on the
  recursor, β through the rule's right-hand side and through the wrapper
  `casesOn` hands the recursor. SrcEval side (`caseFires_of_shape`): F5's
  meaning, from `caseIota`, the relation and canonicity.
- *The equation lemma* (`eqn_den`): a function whose equation theorem is stored
  with the checked shape denotes its equation body. It uses `mem` and
  `eq_equality` only.
- *The run terms run* (`runs_of_sites`, `fundHyps_of`), and *the checks are
  sound* (`groundFacts_of_check`, `caseFacts_of_check`, `rootFacts_of_check`,
  `foArgs_of_check`, `resultTag_of_check`, `boolListed_of_check`).

**Its hypotheses, each with who discharges it.** This is how far the landed
theorem is from the grounded statement of the [spine](end-to-end.md#the-shared-spine).

| Hypothesis | What it says | Who discharges it | Scheduled |
| --- | --- | --- | --- |
| `Laws.defn_value` | δ: a stored definition denotes what its value denotes | the IxVM side: the field `Model.defn_value` (`jcb/ixvmc-std-model`, proved) | done there; becomes a field here when their `Denotes.lean` lands on `main` |
| `Laws.iota_rule` | ι: every stored recursor rule computes, its right-hand side denoting (their `IotaLaw`, copied verbatim) | the IxVM side: `Model.iota_rule`, proved | as δ |
| `Laws.cval_params` | a constant depends on the level assignment only through its own parameters | the IxVM side: `Model.cval_params` | as δ |
| `Laws.proj_ctor` | the projection of a constructor, in value form (`ProjCtor`), **at a structure that is not a proposition** (its stored sort nonzero at the constructor's assignment). In a proof-irrelevant set model the image is then the field tuple, read at position `i + off` | the IxVM side | scheduled there as a public law (their third note, item 6); the restricted form sent to them 2026-11-11. Supplied at each use by `Faith.projSort` (the `proj` conjunct) |
| `Laws.nat_accel` | the fifteen `Nat` operations on all literals, `Bool` results included (`NatAccel`) | the IxVM side | scheduled there (item 6; DO-39) |
| `Laws.ctor_canon` | constructor canonicity across parameters and levels (`CtorCanon`), **at a family that is not a proposition at either level instantiation**: a constructor image built at other parameters and levels that lies in the family at these is the image at these, its fields fitting there. In a proof-irrelevant set model the image is then a tagged field tuple, which lies in the family at other parameters only if its fields lie in their types there | not scheduled by anyone: the IxVM side (who estimate it at 1–2k lines from the recursor's membership law and ι) or IxCC from that law; asked 2026-11-11 | consumed by the generic `case` lemma for a constructor-valued major; supplied there by `CaseWF.indSort` (the `caseShape` conjunct) |
| `groundCheck … = true` | every decidable fact of the closure: `GroundFacts` (the faithfulness clauses, the fragment, the `Nat` and `Eq` bases, each `eqn` entry's shape, the correspondence and closedness of every term SrcEval runs, `Ok`'s closure) and `CaseFacts` (each `case` entry's shape, conjuncts `caseShape` and `caseProg`) | IxCC: the check, run on the closure's bytes | done: true on the `fib` and `decide (fib 10 = 55)` closures (`tests-grounding`, in `ixcc-grounding`), with negative controls that each falsify exactly one conjunct |
| `RootFacts` | the root is in `Sl`, `Ok` at no levels, stored without level parameters at the first-order type `args → res`, its enumerations stored | IxCC: `rootCheck`, run on the closure | done on both closures |
| `FoArgs` | the arguments are literals, or an enumeration's listed constructor | IxCC: `foArgsB` | done on both closures, with a control |
| `ResultTag` | the observed tag names one constructor: every member of `Sl` reading back with that tag whose kernel entry is a field-less constructor has the named constructor's key | IxCC: `resultTagB`, run after the run on the observed result | done on both closures; rejects programs, see below |
| `BoolListed` (`decideRoot` only) | the pinned `Bool`'s listed constructor `1` is the pinned `Bool.true` | IxCC: `boolListedB` | done on `decide`, with a control |
| `SitesOk` | typing, in the one form it is consumed: at every `Ok` instance of every constant of `Sl` SrcEval unfolds, every application site it may evaluate is in the graph regime with its argument in the domain | IxCC | not discharged. G2: a site check from `mem` and stored types, its residue measured. G3: the residue, from the kernel's derivations (an accepted definition's derivation and the rules' soundness over the public model, both kernel side: the latter decided there 2026-11-11 and being estimated) and the walk-level annotation statement (KF-1, IxCC) |

**Two laws as first landed were false, and the instance theorems said nothing.**
As first landed, `ctor_canon` was stated for every constructor and `proj_ctor`
for every structure. Both are false in a proof-irrelevant set model, where every
proof is the one point `pt`. `ctor_canon`: `Exists.intro (fun _ => True) 1 pt`
is `pt`, fits at its own parameters and lies in the inhabited
`Exists (fun w => w = 0)`, so the law concluded that `pt` proves `1 = 0`; and in
the kernel's own set model (`IxCK/Kernel/SetTheory/Derive/Quot.lean`) `Quot.mk`
built at level `0` is `pt`, which is also a class of `quotSet 1 {ptTag} R`, so
the law concluded `pt ∈ {ptTag}`. `proj_ctor`: at a `Prop` structure with a data
field, such as `Nonempty` (the kernel installs its projection table), the image
is `pt`, every component of `pt` is `pt`, and the law concluded that every value
of the field's type is `pt`. Both grounding subjects' environments hold
`Quot.mk`, so in the kernel's set model `Laws` had no instance for them: `fibRoot`
and `decideRoot` as first landed said nothing there, not only the general
theorems. What is assumed now are the restricted forms in the table above: the
family or structure is not a proposition at the assignments involved, which the
check supplies from a decided fact (`NeverProp`: its stored sort's zero-ness datum
is `never`).

**Not yet shown: that `Laws` has a model.** Nobody has yet shown that `Laws`, in
its restricted form, has a model for any environment. Three fields are proved on
the side that owes them (`defn_value`, `iota_rule`, `cval_params`), two are
scheduled there (`proj_ctor`, `nat_accel`), and the restricted `ctor_canon` is not
scheduled by anyone. Until that side's theorem lands, every theorem of this
library is conditional on a hypothesis whose consistency rests on the arguments
written beside each law in `IxCCGrounding/Laws.lean` (and beside each use).

**Why each checked fact is there**, each the counterexample without it:

- *`CaseWF.indSort` (in `caseShape`) and `Faith.projSort` (in `proj`)*: the
  `case`'s inductive, and a projected structure whose constructor is in `Sl` and
  has fields, are stored with a sort that is never zero. Without them the
  generic `case` lemma and the projection case would need `ctor_canon` and
  `proj_ctor` at propositions, where both are false (above).

- *The constructor's field count in `caseIota`* (`Fs.length = cs.nF`, supplied by
  the relation): at `And.casesOn` with a motive into `Type`, the major proof point
  is also `And.intro` applied to its two parameters alone, so with no fields the
  lemma would conclude that `casesOn` returns the minor itself, while ι gives the
  minor applied to two proof points.
- *`CaseWF`, part of `caseShape`*: the shape's induction-hypothesis binders and
  recursive fields are free data, so without `recFields`/`ihs` (each hypothesis is
  the motive at a recursive field, whose domain is the inductive at the `case`'s
  parameters) the wrapper's β at a hypothesis has no justification; without
  `codom` a minor premise's codomain could mention an earlier minor, which
  `casesOn`'s wrapper reads as `casesOn`'s minor and the recursor's premise as a
  wrapper; without `regime` a field binder of a minor could be read in the
  proposition regime while the saturating site is not, and the minor would not
  apply to its fields along a graph-regime chain; without `ctorRaw` (the
  constructor's stored type closed, its level parameters covering it, as many as
  `indLevels`, its codomain the inductive at its own parameters) a constructor
  value built at another assignment and environment could not be moved to the
  `case`'s, where canonicity applies.
- *`FoArgs`, an enumeration argument the listed constructor*: an argument
  constructor outside `Sl` has an unconstrained key. With a second constant
  declared as `Bool`'s constructor `0` and keyed to `Bool.true`, SrcEval runs
  `not` on it to `true` (it selects by the declaration), the kernel to `false`.
- *`ResultTag` over the kernel's reading*: readback names a constructor by its
  declared index and gives tag `0` to a constant not declared as a constructor;
  with the pin `Bool.true` naming such a constant, `Nat.beq 1 1` reads back as
  tag `0`, `false`, where the kernel denotes `true`. A parameterised field-less
  constructor at the same index (`Option.none`) is likewise a different set.
- *`BoolListed`*: nothing else ties the pinned `Bool`'s constructor `1` to the
  kernel's `Bool.true`.

**The class of inductives the `case` shape covers.** `caseShape` is designed to
hold for a `case` constant over an ordinary recursor of an inductive with
parameters, no indices, and recursive fields that are the inductive itself at
the `case`'s parameters (`Nat`, `List`, binary trees, enumerations and
structures); measured, it holds for every `case` constant of the two committed
closures (`Nat.casesOn` among them). It fails, by
design, for indexed families (`Eq`, `Vector`: the shape has no indices), for
nested occurrences (a field `List T` inside `T`) and for recursive fields behind
a function type (a field `Nat → T`, whose induction hypothesis is not the motive
at the field). Such a program fails the check; nothing unsound is admitted.
Widening is G4.
Since the laws' restriction (2026-11-11) it also fails, and the projection case
too (`proj`), for a family whose stored sort can be zero at some assignment:
`PUnit`, a `Prop` structure (`And.casesOn` into `Type`), anything
universe-polymorphic down to `Prop`. Measured on the 20 corpus closures that load
(the nine `bench-k1` ones, `grounding/decide`, five of `phase1-scalar` and five of
`phase1-boundary`): no `case` entry and no structure of a closure's `Sl` is newly
refused; over whole program tables 3 to 7 `case` entries per closure that passed
`caseShape` before now fail it.

**What `ResultTag` rejects on the committed closures.** Both closures' `Sl`
hold `PUnit.unit` (index `0`, no parameters, no fields) beside `Bool.false`, so
`ResultTag` fails at tag `0`: on these closures every `Bool` root that returns
`false` is rejected (for instance `decide (fib 10 = 56)`), and every root whose
result type is an enumeration other than `Bool` and that returns its
constructor `0`. Roots returning `true` (tag `1`) and every `Nat` root pass.
Removing it needs a fact the relation does not give: that the value a root of
result type `D` returns is a constructor of `D`.

`Ok` is the certificate's own datum: the annotation's class of each constant
(`ConstRel.result`, the zero condition of the sort of its stored type, as the
kernel annotator computes it). Its correctness is not a hypothesis; the check
decides its closure (every constant at a position SrcEval may evaluate, in a run
term of an `Ok` instance, is at an `Ok` instance), which a complete annotation
gives.

**Still between the landed theorem and the grounded statement:**

- `SitesOk` (G2, G3) and the three laws not yet scheduled as fields here;
- `ResultTag`'s rejections above;
- the fragment: `let`, recursors fired directly, `Quot`, `csimp`, strings, and
  `case` constants outside the class above are excluded by the check (G4);
- progress (G5), which also consumes premise (i);
- the statement is over any program and kernel reading that pass the check; that
  the reading is the kernel's reading of the closure of the seeds (premise (i)'s
  subject) is the native route's and the IxVM claim's (SP-N, SP-0).

### SP-2. Widening

**Planned.** The fragment grows with the phases: `Quot` (F7, F8), nested
inductives, strings (E9), the data primitives of Phase 3 (one meaning lemma
each, stated at the SrcEval level so that the x86 heap and an evaluator's
write-once memory can both rest on it), plain-RC constructor-tree results, and
other roots than index 0. Each new SrcEval rule is a new version of the
[evaluator contract](evaluator-interface.md) and a new adequacy case.

### SP-N. Native discharge of the premises

**Planned, optional; its front end in progress.** For a consumer of x86
claims without an IxVM proof:
existence by running IxCK natively (its typing core's running time on hostile
input then matters to that verifier,
[hardening design](hardening-design.md#external-dependencies)), and
faithfulness and typing either by IxCC's verifier-side ingress rebuilt on
IxCK's reader, so that there is one reading by construction (the earlier
default of an [open decision](roadmap.md#open-decisions)), or by a native
check of the clauses against IxCK's reading (the working default now,
awaiting the owner's confirmation), with the typing derivations read off the
kernel's runs. Designed, and built beside the default front end, as the
[kernel front end](kernel-front-end-design.md): IxCK's tiered entry accepts
the whole artifact, IxCC's reading is checked against IxCK's, and the
relevance annotation comes from IxCK's inference; the erased type checker is
deleted at its switch. The switch proceeds now (the owner's decision of
2026-11-11; its step 2 is done), and IxCK's blow-up on chains of `let`,
fixed in the kernel package on this branch in parallel, has landed; the
native verifier the switch produces still inherits the kernel's exponential
time on universe levels it cannot fold, until the kernel's level-metering
work budget lands.

**Which entry discharges existence natively.** The tiered entry's acceptance
of the artifact gives a model of the artifact's whole logical environment,
under the artifact's table and behind the artifact's own prelude: more than
premise (i) needs, and a different reading from the IxVM claim's (the default
table, the committed prelude, the closure of `S`). Two ways to close the gap:
- *Restriction:* the closure of `S` is closed under references, so a model of
  the whole restricts to one of the closure (a restriction of models exists
  in the certified IxVM work, not here); then the two lemmas that the reading
  is the same under the default table and under the artifact's, and behind the
  committed prelude and the artifact's (when its prelude records are the
  committed ones), and a strengthening lemma for the derivations (a
  derivation in the larger environment that mentions only the closure's
  constants is one in the closure). About 2–4k lines, three lemmas over the
  reader and the rules.
- *The logical entry on the closure* (decided 2026-11-11, DO-37): compute the closure of `S` in
  the artifact's records under the same table as the IxVM claim (reference,
  certified-operation ground and recursor edges), order it, and run the
  kernel's logical entry with the committed prelude on exactly those records.
  It has no `partial` record (the tier's fence: no logical record names a
  tier constant, so a safe target's closure holds none). One more kernel run,
  over a subset of what the tiered entry already checks (at most about 1.7 s
  on the largest closures measured), and the closure walk (about 0.3–0.6k
  lines, ported, since IxCC may not import the root package's walk). Then
  both routes discharge one statement, and the derivations come from the same
  run.

*Size [estimate]:* 2–6k lines (an ingress correspondence for the first
fragment, 3–6k, is the upper bound if ingress is rebuilt).

## The first grounded fragment

The union of what the K1 programs need and what an evaluation axiom over
first-order data needs:
- closed `Bool` terms with all levels concrete, and roots with `Nat`
  parameters (level-monomorphic, root index 0, immortal and zero-RC
  policies);
- results: `Nat`, `Bool`, field-less enumerations;
- first-order inductive data without indices, including `Decidable` and
  structures with proof fields (the proofs pass as `irr`);
- `Nat` literals and the fifteen primitives;
- recursion through `eqn` entries (structural and well-founded) and
  structural recursors; `csimp` replacements; `match` through `case` entries;
  numerals and instance methods through δ and projections;
- closures as arguments (SrcEval has closures natively; on x86 they must be
  removed by inlining or, after Phase 2, by P8);
- excluded: `Quot`, strings, arrays, `opaqueByValue`, recorded
  interpretations, nested inductives, closures stored in data;
- the environment: the kernel's reading of the closure of the target and the
  table's theorems, under the default role table (or a restriction of it,
  with the bridging lemma).

`Decidable` is in the first fragment because every `native_decide` axiom has
the shape `Decidable.decide inst = true`, and ι on `Decidable.isTrue h` needs a
typing certificate for the proof `h` in a reduction-based account; a
semantic relation, in which a skipped proof relates to its denotation (the
proof point) without being built, does not.

What the first fragment needs from outside IxCC, by [the law
table](#the-law-table): the IxVM claim fixing values and its eight
obligations proved (IxVM route); the laws δ and ι (done there), the
projection of a constructor, the `Nat` operations on literals (or IxCC
derives them) and public level irrelevance; the rules' soundness over the
public model; "the annotation pass preserves denotation". None of it is in
this repository.

**Exit tests** (default, to confirm, [roadmap](roadmap.md#open-decisions)):
1. *Evaluator form:* `decide (fib 20 = 6765)`, with the environment derived
   from claim bytes, through SrcEval on its image, grounded;
2. *x86 form:* the compile claim of the K1 `fib` root, with the grounded x86
   statement, and then every K1 root.

## What is not achievable as posed

- The reduction form, for well-founded recursion: IxCK does not unfold
  theorems. The nearest is the grounded denotational form.
- Any statement over every model of the public structure without laws. The
  nearest is models with the laws.
- The first premise as "IxCK accepts the environment with root `H` under the
  artifact's table `ρ`", discharged by an IxVM claim paired on `(H, ρ)`: the
  IxVM claim concludes neither acceptance nor anything about `H`, refuses a
  `checkEnv` over an artifact holding `partial` records, and covers the
  default table only. The nearest is the restated premise (existence for the
  closure of the seeds), with the table restriction lemma.
- Soundness from existence alone, without typing: a model gives no typing
  for subterms. The nearest is typing as part of premise (ii).
- Roots using `opaqueByValue` or recorded interpretations, without
  restricting models. The nearest is a statement relative to the
  interpretation.
- Termination or completeness for any compiler with 63-bit `Nat` and clocks.
- Stage L as grounding: it relates the object to a host Lean function through
  the identification of that function with its Ixon image; it does not speak
  of IxCK's model of the bytes, and it does not apply to a claim whose subject
  is a term inside an environment ([CD3](#cd3-stage-l-a-proof-producing-translator)).

## The earlier items, corrected

The 2026-11-09 plan had four items. Their places now:

| Item | Then | Now |
| --- | --- | --- |
| CD1 | Five syntactic checker lemmas, first | Becomes the faithfulness premise, discharged by whoever holds the kernel's reading (SP-0 defines it). Clause 1 is in effect in `verifyBytes_*_sound` and clause 4 is proved; clause 2's semantic content is SP-0's table lemmas; clause 3 is checked against the kernel's typing judgement, in both directions; clause 5 comes from the role table |
| CD2 | Shape typing, before CD3 and CD4 | Off the critical path for grounding (SP-1's progress replaces it there). Kept for Ring-0 and IxOS confinement without semantics, and as the typing a per-program Aiur lowering needs |
| CD3 | Stage L, first | Demoted: a separate product for the bignum library and the IxOS monitor's `step`; does not ground anything in IxCK |
| CD4 | Stage K, a research spike | The spine's adequacy core: SP-A, then SP-1, over models with the laws, with existence, faithfulness and typing as premises, soundness and progress in the target |

## CD1. The front-end theorem

**Status:** partly done; the rest becomes the faithfulness premise (table
above). The statement as first planned, for an ingested program `P`, a table `T` and an
annotation `A` that `Recheck.front` accepts with result `a.src`:
1. `a.src` is `Lazify.run (install P T A)` with every check passed (in effect
   part of `verifyBytes_*_sound`, which exposes the decode, ingress, table,
   annotation and lazification steps);
2. each `eqn f thm` entry names a theorem of `P` whose statement is
   `∀ xs, f xs = rhs` with `rhs` the installed body, and each `csimp f g thm`
   one whose statement is `@f = @g`, every one with a standard-axiom closure
   (the closure part is proved: `checkAxiomClosure_sound`);
3. every position tagged irrelevant at a profile has a type that is a sort or
   a proposition at that profile (and, for progress, conversely: every proof
   position is tagged irrelevant);
4. `Lazify` changes only evaluation modes (proved: `Src.Lazify.run_modeEq`);
5. the pinned identities (`known`, `prim` entries) name the pinned constants.

As the *faithfulness premise*, the five clauses are what another program (the
IxVM kernel circuit, checking an image, or a native check against IxCK's
reading) runs on a closure and an image:
clauses 1, 4 and 5 are syntactic; clause 2 is syntactic once the theorem is
known to be accepted; clause 3 needs typing and is stated against the kernel's
typing judgement ("the position's type infers to `Sort 0` at the profile, or
the position is itself a type"), so the kernel circuit can decide it with its
own inference ([evaluator interface](evaluator-interface.md#faithfulness)).
Since 2026-11-11 premise (ii) adds a sixth clause, **typing**: each value, rule
right-hand side and equation the evaluator runs has a derivation in the
kernel's rules in the environment of premise (i). The kernel circuit holds
those derivations as it checks the closure; the native route reads them off
the kernel's runs. IxCC's obligation is to define the clauses precisely (SP-0)
and to prove that they imply what soundness and progress consume (SP-1), not
to prove its own checkers sound.

## CD2. Source safety: a checked shape typing

**Status: planned.**

**Motivation.** Removing `GoesWrong` for arbitrary accepted programs, not
just translated ones; making Ring-0 confinement unconditional on
source safety; rejecting hostile certificates that make the source stuck.

**Design.** A checked, erased *shape* typing on Src: shapes for □, `Nat`,
strings, each inductive with its constructors' field shapes per universe
profile, and functions by arity, checked by a proved checker over `a.src`
with the root's readback type as the result shape. The checker is decided
on Src, not implied by kernel type checking: kernel acceptance implies no
decidable shape system. An untrusted
annotator proposes the shapes.

**Proof obligation.** Progress and preservation for SrcEval on well-shaped
programs: a well-shaped root on well-shaped inputs returns a value of its
shape, traps, or times out; it never gets stuck, and the view always reads
the result back. Composed with `Recheck.sound`, this yields a corollary
without the stuck and view-mismatch cases. Two causes remain:
- a trap (`False.rec`), which only CD3 or CD4 exclude, since reaching it
  requires a proof of `False`;
- the stuck rule for bounded constructions of
  [DR2](data-and-roots-design.md#dr2-fixed-width-integers-and-int), whose
  erased proof shapes cannot see.

**Done for the roots of every path.** The view half is proved: at a root
that `checkImmortalRoot` accepts, the view reads back every result of the
shape the root's declared type describes (`Recheck.ResultShape`: a `Nat`, a
pinned `Bool` constructor, or a constructor of the result enumeration;
`Recheck.Front.view_resultShape`), so the view-mismatch case is SrcEval
returning a result off that shape. Erasure registers a row for every
constructor a root's result can hold (`Lam.Erase.resultCtors`), which the
pinned-`Bool` route needs (`Recheck.Front.boolRows`) and discovery needs for a
root compiled alone. The view also accepts some results off the shape (it
relabels a constructor of another type by its table tag), so the guarantees
are restated with the shape view, which accepts exactly the results of the
shape (`Recheck.Front.shapeView_none_iff`, `Recheck.ShapeClaim`). At a root
that `checkPlainRcRoot` accepts, the plain-RC view reads every constructor
tree of the root's declared first-order type (`Recheck.TreeShape`,
`Recheck.RcReplay.Front.view_plainShape`); there the converse and the heap
readback of the shape are not proved. Preservation, even for these result
types, is not proved and is not within reach without this design: canonical forms for an enumeration is the
easy last step, but showing that the result has the root's type needs a typing
relation for Src values, a soundness theorem for `Tc.checkEnv` giving it for
the ingested declarations, CD1 clauses 2 and 3 to carry it to `a.src`, and
subject reduction for every SrcEval step (δ through table entries, β,
recursor and `casesOn` rules, projections, primitives, `Quot`, and casts,
which SrcEval runs as identities).

**Trusted base.** No change.

**Dependencies.** CD1 (canonical relevance lets shapes treat irrelevant
positions as □).

**Size [estimate].** 5–7k lines, by comparison with the relevance checker
and its soundness proofs (2k lines together), which decide a similar per-node
property over the same terms.

**Exit.** A `GoesWrong`-free corollary of `Recheck.sound` and of the Ring-0
admission theorem for shape-checked programs, applied to every K1 root and
every compiled corpus root.

## CD3. Stage L: a proof-producing translator

**Status: planned** (prototype, when a consumer needs it), **research** (at
the scale of IxCK). Demoted from first place (to confirm,
[roadmap](roadmap.md#decisions-to-confirm)).

**Design.** Following the CakeML translator, a tool that takes a Lean
constant `f` and the compiled program `P` containing its Ixon image, and
produces a Lean theorem: for all inputs `xs`, SrcEval of `P`'s root on the
encodings of `xs` returns the encoding of `f xs` at some clock. It works
from `f`'s equation lemmas and functional induction, evaluating SrcEval
symbolically. The link between the Lean constant and its Ixon image comes
from ix's certified Lean-to-Ixon compiler (`Ix.Cert.CompileCorrect`; see the
root [README](../../README.md)), or is checked per constant.

**What it gives.** Composed with `Recheck.sound`: if the object returns `w`,
then `w` reads back as `f xs`; for a total `f`, `GoesWrong` is excluded for
that program. This is "the object computes this Lean function", which is what
the bignum library's layer 3 and the IxOS monitor's `step` want.

**What it does not give.** Grounding in IxCK: its statement is about the host
function, reached through the identification of `f` with its Ixon image, not
about IxCK's model of the claim's bytes, and it does not apply to a claim whose
subject is a term `e` inside an environment, which is what an evaluation axiom
is. So it is not on the spine.

**Fit.** First order and monomorphic first (K1, the
[bignum library](bignum-design.md#proof-obligation), state-machine roots);
higher-order and polymorphic functions after P8.

**Dependencies.** The front-end facts of SP-0 (or their syntactic
CD1 forms); ix's compile certificate for the identification of constants.

**Size [estimate].** Not estimated; a K1 prototype would give the first figure.

**Exit.** Prototype: `fib`, `gcd` and `ackermann` from K1 with end-to-end
corollaries "the object's result is `f xs`", fenced. Then the bignum
library's closure.

## CD4. Stage K: semantic adequacy

**Status: research**, leading. CD4 is SP-A followed by SP-1 above, with these
corrections to the 2026-11-09 statement (the third and fourth of 2026-11-11):
- **Models with laws.** The statement quantifies over every model of the
  public structure with the laws of [the law table](#the-law-table); the
  public model of `model_exists` on this branch validates no definitional
  unfolding and cannot carry δ through a body.
- **Existence, faithfulness and typing as premises.** The environment is the
  kernel's reading of the closure of the seeds; that it has a model is
  premise (i), discharged by an IxVM claim or a native IxCK run; typing is in
  premise (ii); IxCC's erased type checker supplies nothing.
- **Soundness and progress apart.** "Adequacy is not progress" is true of an
  untyped relation, not of the typed one this route needs: on the fragment,
  related terms neither get stuck nor trap, so the grounded statement has no
  escape; but only progress needs premise (i), and only the x86 claim needs
  progress.
- **Not over the internal invariant.** Stating it over `EnvModelM` or
  `RulesInputs` would tie it to the kernel's proof internals and exclude the
  model an IxVM claim gives, which is a public `Model`.

**What IxCK supplies here, and what the certified IxVM work adds.** Checked,
not assumed: `EnvModelM`'s fields cover δ for definitions, stored constants
inhabiting their types (theorems included), ι, projections and η, literals,
the structural `Nat` recurrences and the well-founded operations' guarded
clauses, and the `Eq` law
([`IxCK/Kernel/Model/Annot/EnvModelM.lean`](../../IxCK/Kernel/Model/Annot/EnvModelM.lean));
`RulesInputs` is built from it (`RulesInputs.ofSem`,
[`IxCK/Kernel/Model/Capstone.lean`](../../IxCK/Kernel/Model/Capstone.lean)).
The public `Model` here has `mem`, `false_empty` and `eq_equality`; the
certified IxVM work makes δ and ι public fields (proved there) and plans the
rest. Missing for the first fragment, as the law table marks: the projection
of a constructor and the `Nat` operations on literals as public laws (or
IxCC's derivations), public level irrelevance, the rules' soundness over the
public model, "the annotation pass preserves denotation", an opaque value law
(none, by design); and, if IxCK runs on the claim path, a typing core whose
work is bounded on hostile input (the chains of `let` that made it
exponential are fixed; universe levels the kernel cannot fold remain,
[hardening design](hardening-design.md#external-dependencies)).

**The hard points.** Dependent types (SrcEval drops type arguments the model
needs), level-exact relevance (`propWhen` at concrete levels), by-name slots,
and subsingleton elimination without the major (F3, which also fires
`Acc.rec`, so nothing guarantees that SrcEval terminates; fine for partial
correctness). Lean's type theory has no syntactic subject reduction under
definitional proof irrelevance with subsingleton elimination, so the relation
must be semantic.

## `Models/KernelBridge`: not the route

[`Models/KernelBridge`](../../Models/KernelBridge/README.md) proves a
conditional simulation of SrcEval into kernel reduction under a user-supplied
relation. Its approach cannot reach recursion (kernel reduction is weak-head,
so a recursive constant reduces only to its `brecOn` or `WellFounded.fix`
form) and relates every argument, type arguments included, so it cannot pass
what Lean elaborates (numerals through `OfNat`, instance methods, `match`
through `casesOn` with motives). CD4's denotational relation replaces it.
The package stays, with its gate, as a record of the approach until SP-1
lands; its layer that reads a literal's denotation off a reduction may be
reused for literals; then the package and its gate are removed (default, to
confirm, [roadmap](roadmap.md#open-decisions)).

## What each extension adds

| Extension | Spine (contract, image, adequacy) | CD2 (shapes) | CD3 (translator) | Aiur evaluator route |
| --- | --- | --- | --- | --- |
| P8 closures ([design](closures-design.md)) | nothing: P8 is below SrcEval | function shapes by arity | higher-order functions | nothing: the evaluator has closures natively |
| Heap completion, RC, reuse | nothing (below SrcEval) | — | — | nothing |
| Fixed-width integers, arrays, strings | new primitives: a new contract version, new image entries, one meaning lemma each at the SrcEval level | shapes for words and arrays; the bounded-construction rule remains | the primitives' meanings are their Lean bodies | the same meaning lemmas, implemented over write-once memory |
| Interpreted opaques (`mixHash`, `getNumBits`) | excluded from the grounded statement; statements relative to the interpretation, kept separate from evaluation through a stored value | — | the theorem holds only if `f`'s result is proved independent of the opaque | refused for discharging axioms |
| Bignums ([design](bignum-design.md)) | nothing above SrcEval (`Nat` is exact there) | — | the library closure (its layer 3) | shares the `Nat` specification with the evaluator's in-circuit `Nat` |
| Structured roots and the byte ABI | readback at the new types; the image's root interface | the root's shape | encoders and decoders are ordinary compiled code | readback to an Ixon expression |
| State-machine effects | per step | per step | `step` computes Lean's `step` | per step |

## The flagship targets

- **The certified kernel through IxCC.** The useful end statement is "if the
  object accepts the environment bytes, then IxCK's `checkDecls` accepts
  them", after which IxCK's soundness gives a model. Through the spine this
  needs a reflection step from models to the Lean function, for which no
  design exists; through CD3 the statement is direct, and the open question is
  whether the translator scales to IxCK's 1.3k–1.9k definitions (1,264 `def`
  and `abbrev` lines in the import closure of `IxCK.Kernel.Cached.Installed`,
  1,868 with admission and the Ixon reader) and the parts of `Init` and `Std`
  they use. The opaque constants in its closure
  ([DR5](data-and-roots-design.md#dr5-library-structures-and-opaque-constants))
  count against both unless IxCK removes them.
- **The IxOS monitor.** Confinement without the source-safety premise needs
  either progress for the monitor's fragment (SP-1's, once the fragment covers
  the monitor's data) or CD2; CD3 on the monitor's `step` makes its behaviour
  the Lean function's.

## Resources are not in the kernel's model

The spine grounds *meaning*: IxCK's model reads no usage, ownership or
locality contract, so no statement in it can say that a linear binding is
consumed once, that a unique value is unaliased or that a local value does not
escape. Resource soundness is therefore a separate, operational theorem about
an instrumented source evaluator, with IxCC's ownership checker as the
soundness basis for what the native compiler does with ownership (the owner's
decisions of 2026-11-14). It is planned in the [resource soundness
design](resource-soundness-design.md) and is not part of the end-to-end
statements.
