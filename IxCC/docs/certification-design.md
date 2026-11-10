# Certification: grounding IxCC in Ixon and IxCK

Written 2026-11-09; reworked 2026-11-10 around the goal of
[end-to-end certification](end-to-end.md) for the x86 and Aiur back ends,
grounded in Ixon and the certified kernel IxCK, and on 2026-11-10 again
around the owner's architecture, in which kernel acceptance and the image's
faithfulness are premises discharged by other proofs. **Status:** the spine
below (SP-0 to SP-2, SP-A, SP-N) is **planned**; its adequacy core is
research-grade and starts with the typing-transport question and a spike
(SP-A). CD1 is partly done and its remaining clauses become the faithfulness
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
| Claim bytes | `CompileClaim` encodes and decodes exactly | Proved (round trip). Binds the environment root, target, policy, arity and object hash only: not the role binding, the certificate, the sidecar, the typing flag or `Recheck.Config` | SP-0: the claim also binds the role table and the image digest |
| IxCC's reading | `.ixe` bytes to IxCC's environment (`V3.decodeAnonymousEnv`), pure BLAKE3 authentication, canonicity evidence | Proved that it ran; IxCC's own framing, version 4 without a role binding only | SP-0: role-bound envelopes, pure BLAKE3; off the trusted path once faithfulness is a premise |
| IxCK's reading | the same bytes to IxCK's records and declarations | Proved by IxCK (`checkBytesWith_reading`, [`IxCK/Kernel/Admission/Theorems.lean`](../../IxCK/Kernel/Admission/Theorems.lean)); needs a role binding | the reading the premises are about |
| The two readings agree | IxCC and IxCK decode the same constants under the same keys | **Absent.** They share only the constant decoder | Not needed: premise (ii), or one reading by construction (SP-N) |
| Kernel acceptance ⇒ strong model | `checkDecls_sound`, `checkBytes_strongModel` | Proved by IxCK. **Not a premise of any IxCC theorem** | Premise (i), discharged by an IxVM proof or a native run |
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
| Driver | `runtime_driver.c` and symbol lookup | **Assumed**; `X86.Driver.Ok` is satisfiable (`driver_exists`) | XB-1 |
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
| Denotation with escape | ⇒ in every strong model `⟦kc ns⟧ = ⟦enc w⟧`, or the source goes wrong | Adds the kernel but keeps the certificate's escape; not useful to an evaluation-axiom consumer |
| **Grounded** | as above without the escape, for programs passing a checked fragment condition, quantified over every model satisfying `RulesInputs` and the accepted environment's typing facts (so that IxVM's own model qualifies), under the two premises below (acceptance, faithfulness) | **The target** |
| Evaluation axiom | the grounded form for a closed, level-free `Bool` term `e`, plus a binding of `e` to a compiled root | What IxVM needs to discharge `ax : e = true` |

A form over every *weak* model is false in general (δ and ι do not hold there);
the nearest achievable is strong models. A form for roots using
`opaqueByValue` or recorded interpretations is false over all strong models;
the nearest is models restricted to the interpretation.

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

IxCC's top-level statements take two hypotheses about an environment whose
bytes have root address `H`, read under role table `ρ`:
1. **Acceptance.** IxCK accepts that environment.
2. **Faithfulness.** The checked source program, as an image with digest `D`,
   satisfies the faithfulness clauses with respect to IxCK's reading of those
   bytes: it is the installed and lazified program read from them; its `eqn`
   and `csimp` entries name accepted theorems with the right statements; its
   relevance annotation is the one the kernel's typing judgement gives (every
   position tagged irrelevant is a type or a proof at its profile, and every
   proof position is tagged irrelevant); its pinned identities are `ρ`'s
   ([CD1](#cd1-the-front-end-theorem) lists the clauses).

A consumer discharges acceptance with an IxVM typing proof for `H`, and
faithfulness with the kernel circuit's lowering claim for `(H, D)`, which has
the kernel's reading and the types and checks the image clause by clause; or
natively, by running IxCK and a native check (SP-N below). Composition is by
aggregation of claims about the same addresses, the mechanism IxVM already
has for conditional claims. IxCC embeds no proof verifier. That IxVM refines
IxCK, so that an IxVM proof of acceptance is IxCK's acceptance, is the IxVM
workstream's result and an external dependency of this plan.

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

**What it does not remove.** The adequacy of SrcEval for the kernel's
models, with progress. Acceptance says the program is well typed, not that
SrcEval computes its denotation; it is the premise that proof consumes.

## The spine's work

In dependency order. Sizes are estimates, by comparison with erasure's
simulation over the same evaluator (10.1k lines,
[`Lam/Erase/Proof`](../IxCC/Lam/Erase/Proof)), the bridge's `Nat`-only
simulation (1.9k), IxCK's reader (1.3k) and IxCC's ingress (0.3k).

### SP-0. Same bytes and the conditional statement

**Planned; engineering, with small lemmas.** IxCC must consume exactly the
bytes the IxVM proof is about and state what it guarantees about them.

- **The same bytes.** IxCC reads role-bound (version-5) environments, which
  IxVM's claims are about and this repository's `ix compile` writes; IxCC's
  ingress refuses them today ([`Ixon/V3/Env.lean`](../IxCC/Ixon/V3/Env.lean)),
  so the fixtures' unbound envelope is a bridge, not the design.
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
  IxVM's do; IxCC's own pins ([`Src/Pinned.lean`](../IxCC/Src/Pinned.lean))
  become a check against the table.
- **The claim binds what composition needs.** The environment root `H`, the
  target, the role table and the image digest `D` (today the claim binds the
  root, the target, the policy, the arity and the object hash). The verifier
  checks that `D` is the digest of the checked source program it compiled.
- **The conditional statement.** The faithfulness predicate defined in Lean,
  with a structural map from IxCK's terms to `Src.Term` as its specification
  (nested inductives excluded); the [x86](end-to-end.md#x86-the-proved-pipeline)
  and [evaluator](end-to-end.md#aiur-form-i-the-fixed-evaluator-circuit-first)
  statements, composed from today's object theorem, the two premises and an
  adequacy lemma taken as an explicit hypothesis, which SP-1 discharges.
- **The small lemmas**, in every strong model of the accepted environment:
  - `eqn f thm` and `csimp f g thm`: once each entry's theorem is identified
    by address in the accepted environment, from "accepted theorems are true
    in the model" (stored constants inhabit their types, and the `Eq` law), so
    `⟦f xs⟧ = ⟦rhs⟧` and `⟦@f⟧ = ⟦@g⟧`; stated once, for IxCC and for an
    evaluation-axiom discharge path alike;
  - `case T`: from the stored value of `T.casesOn` and the recursor rules;
  - the fifteen `Nat` primitives (fourteen binary operations and `pred`,
    [`Src/Prim.lean`](../IxCC/Src/Prim.lean)) against the kernel's literal
    laws and operation table (`natOpResult`,
    [`IxCK/Kernel/CoreDefs.lean`](../../IxCK/Kernel/CoreDefs.lean)), with no
    evaluation caps;
  - recursor kinds: proof irrelevance and emptiness;
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

**Planned (research).** First establish what IxCK's acceptance gives about
the *subterms* SrcEval evaluates. The model invariant states that each
constant's type is well denoted and its value denotes the constant
(`type_reads`, `type_wellDenotedV`, `defn_reads` in `EnvModelM`); the adequacy
relation needs, for every value SrcEval evaluates (definition values, rule
right-hand sides, `eqn` right-hand sides at concrete levels), a reading whose
binder domains are inhabited by related arguments. Whether that follows from
acceptance as IxCK states it, needs a new IxCK lemma (every accepted value has
typing derivations for its subterms), or needs a stronger premise than
acceptance, is undetermined. It decides whether premise 1 is strong enough as
stated, so it comes first.

Then the spike: the adequacy relation on `fib` from `bench-k1`, then on
`decide (fib 10 = 55)`, so that the `Decidable` case is tested early, end to
end. Denotational, not by reduction; over
IxCK's strong models; the environment from IxCK's reading of the fixture
bytes; partial correctness *with* progress; a hand-built correspondence for
the few constants involved. *Exit:* the answer on typing transport, and the
spike's theorem fenced or a stop report naming what failed (dependent types,
level-exact relevance, by-name positions, subsingleton elimination without
the major). *Size:* 1–3 months [estimate]. Runs in parallel with SP-0 and the
evaluator interface.

### SP-1. Adequacy and progress on the first fragment

**Planned (research core).** CD4's relation and progress, discharging SP-0's
adequacy hypothesis:
- a step-indexed relation between SrcEval values and model denotations:
  literals to literals, constructors to constructor applications, closures and
  partial applications to functions on related arguments, `irr` to any member
  of the slot's type; environments slot by slot;
- typing transport as SP-A settles it;
- the fundamental lemma by induction on SrcEval's clocked definition, each
  rule discharged by SP-0's lemmas and the model's laws;
- progress: related terms never get stuck or trap. Traps are unreachable (the
  major of an empty eliminator would denote a member of ∅). Stuckness needs
  the fragment condition, checked on `a.src`: no relevant axiom, theorem or
  non-allowlisted opaque; no string major; and the faithfulness premise's
  relevance clause in both directions;
- the grounded statements for `verifyBytes` (immortal and zero-RC) and for
  the evaluator route, conditional only on the two premises.

*Size:* 16–36k lines [estimate: the relation 12–25k, typing transport 0–8k
depending on SP-A, progress 4–10k]. *Calendar:* 6–12 months after SP-A.
*Exit:* both [first-fragment tests](#the-first-grounded-fragment), fenced
with the standard axioms.

### SP-2. Widening

**Planned.** The fragment grows with the phases: `Quot` (F7, F8), nested
inductives, strings (E9), the data primitives of Phase 3 (one meaning lemma
each, stated at the SrcEval level so that the x86 heap and an evaluator's
write-once memory can both rest on it), plain-RC constructor-tree results, and
other roots than index 0. Each new SrcEval rule is a new version of the
[evaluator contract](evaluator-interface.md) and a new adequacy case.

### SP-N. Native discharge of the premises

**Planned, optional.** For a consumer of x86 claims without an IxVM proof:
acceptance by running IxCK natively on the claim's bytes (its typing core's
blow-up on chains of `let` then matters to that verifier,
[hardening design](hardening-design.md#external-dependencies)), and
faithfulness by IxCC's verifier-side ingress rebuilt on IxCK's reader, so that
there is one reading by construction (the default of an [open
decision](roadmap.md#open-decisions); a native check of the clauses against
IxCK's reading is the alternative). *Size [estimate]:* 2–6k lines
(an ingress correspondence for the first fragment, 3–6k, is the upper bound if ingress is
rebuilt).

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
  interpretations, nested inductives, closures stored in data.

`Decidable` is in the first fragment because every `native_decide` axiom has
the shape `Decidable.decide inst = true`, and ι on `Decidable.isTrue h` needs a
typing certificate for the proof `h` in a reduction-based account; a logical
relation in which irrelevant positions relate to anything does not.

**Exit tests** (default, to confirm, [roadmap](roadmap.md#open-decisions)):
1. *Evaluator form:* `decide (fib 20 = 6765)`, with the environment derived
   from claim bytes, through SrcEval on its image, grounded;
2. *x86 form:* the compile claim of the K1 `fib` root, with the grounded x86
   statement, and then every K1 root.

## What is not achievable as posed

- The reduction form, for well-founded recursion: IxCK does not unfold
  theorems. The nearest is the grounded denotational form.
- Any statement over all weak models. The nearest is strong models.
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
| CD4 | Stage K, a research spike | The spine's adequacy core: SP-A, then SP-1, over strong models, with kernel acceptance as a premise and progress in the target |

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
IxCC's obligation is to define the clauses precisely (SP-0) and to prove that
they imply what the adequacy theorem consumes (SP-1), not to prove its own
checkers sound.

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

**Status: research**, leading. CD4 is SP-A followed by SP-1 above, with three
corrections to the 2026-11-09 statement:
- **Strong models.** The statement quantifies over models meeting
  `RulesInputs` and the accepted environment's typing facts, which IxCK's
  `EnvModelM` supplies; the weak `Model` of `model_exists` validates no
  definitional unfolding and cannot carry δ through a body.
- **Kernel acceptance as a premise.** The environment is the one IxCK reads
  from the claim's bytes under the bound role binding and accepts, a premise
  discharged by an IxVM proof or a native IxCK run; IxCC's erased type checker
  supplies nothing.
- **Progress in the target.** "Adequacy is not progress" is true of an untyped
  relation, not of the typed one this route needs: on the fragment, related
  terms neither get stuck nor trap, so the grounded statement has no escape.

**What IxCK already supplies.** Checked, not assumed, for this plan:
`EnvModelM`'s fields cover δ for definitions, stored constants inhabiting their
types (theorems included), ι, projections and η, literals and all fifteen
`Nat` operations, and the `Eq` law
([`IxCK/Kernel/Model/Annot/EnvModelM.lean`](../../IxCK/Kernel/Model/Annot/EnvModelM.lean));
`RulesInputs` is built from it (`RulesInputs.ofSem`,
[`IxCK/Kernel/Model/Capstone.lean`](../../IxCK/Kernel/Model/Capstone.lean)).
Missing: closed-form meanings of each `Nat` operation on literals (derivable,
SP-0); an opaque value law (none, by design); possibly typing derivations for
subterms of accepted values (SP-A decides); and, if IxCK ever runs on the claim path,
a typing core that is not exponential on chains of `let` (an IxVM-side fix,
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
