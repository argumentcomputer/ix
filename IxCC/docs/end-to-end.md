# End-to-end certification: one spine, two back ends

Written 2026-11-10; the premises restated 2026-11-11 (below). **Status:**
below the source evaluator the x86 route is implemented and proved; the
shared spine above it is **planned**; the Aiur routes are **planned**, the
first of them on the IxVM side. This page says
what "certified end to end" is to mean for each back end, what the routes
share and what each trusts. The [roadmap](roadmap.md#plan) schedules the
work; the [certification design](certification-design.md) plans the spine's
proofs; the [evaluator interface](evaluator-interface.md) specifies what the
Aiur evaluator route needs from IxCC first; the
[hardening design](hardening-design.md) covers dishonest input.

## The goal

The owner's goal (2026-11-10): end-to-end certification for both the x86 and
the Aiur back ends, grounded in Ixon and the certified kernel, IxCK. Earlier
statements of the same goal: a generally useful compiler for Lean code, with
certification; and certification hardened against dishonest input.

*Grounded* means two things. The statement is about the Ixon bytes a claim
names, read the way IxCK reads them, not about a program IxCC built by its
own reading. And the meaning it states is the one IxCK's model gives the named
constant, not the result of an evaluator IxCC wrote. Today's theorems have
neither: they relate the object to IxCC's source evaluator (SrcEval) on the
source program IxCC's front end built, with an escape when that source goes
wrong ([compile boundary](compile-boundary.md)).

## The shared spine

Every route shares four objects and the theorems that connect them.

1. **The Ixon bytes and a named constant.** An environment (`.ixe`) and a
   target address. IxCK reads the bytes with its reader
   ([`IxCK/Kernel/Ixon/Reader.lean`](../../IxCK/Kernel/Ixon/Reader.lean)) and
   admits them under a role binding
   ([`IxCK/Kernel/Admission.lean`](../../IxCK/Kernel/Admission.lean)). IxCC
   reads them with its own decoder (`V3.decodeAnonymousEnv`,
   [`Ixon/V3/Env.lean`](../IxCC/Ixon/V3/Env.lean)), which reads the role-bound
   envelope `ix compile` writes, authenticating its role table and taking its
   pinned identities from it, and the unbound one of the committed fixtures
   ([byte contract](byte-contract.md)).
2. **The kernel's model of the target's closure, with laws.** The
   environment the statements are about is the kernel's reading (IxCK's
   reader, under a role table) of the closure of the *seeds*: the target and
   every theorem the unfolding table names (its `eqn` and `csimp` entries),
   with what they reference. Those theorems are not in the target's own
   closure (an equation theorem refers to its function, not the other way),
   so they must be seeds. A *model* of an environment
   ([`IxCK/Kernel/Denotes.lean`](../../IxCK/Kernel/Denotes.lean), `Model`)
   interprets every constant as a set; on this branch it asks that each
   stored constant be a member of what its type denotes (`mem`), that `False`
   denote the empty set and that `Eq` denote equality (`eq_equality`), and
   nothing about values. The certified IxVM work (pull request #678 and its
   follow-up branches; not in this repository) is adding *laws* to that
   public structure: δ (a stored definition denotes what its value denotes)
   and ι (every stored recursor rule computes as Lean's, `Quot.lift`
   included) are fields there and proved; structure and unit-like η, the
   projection of a constructor and the `Nat` operations on literals are to
   be built. IxCC states its results over every model with the laws its
   evaluator needs ([the law table](certification-design.md#the-law-table)),
   not over the kernel's internal invariant `EnvModelM`
   ([`IxCK/Kernel/Model/Annot/EnvModelM.lean`](../../IxCK/Kernel/Model/Annot/EnvModelM.lean)),
   which carries all of them today for an accepted environment
   (`checkBytes_strongModel`,
   [`IxCK/Kernel/Admission/Reference.lean`](../../IxCK/Kernel/Admission/Reference.lean))
   and makes IxCK's reduction, conversion and inference sound (`red_sound`,
   `defeq_sound`, `infer_sound`,
   [`IxCK/Kernel/Model/Rules/Sound.lean`](../../IxCK/Kernel/Model/Rules/Sound.lean),
   through `RulesInputs`). A statement over the public structure is the
   smaller trusted surface and does not move when the invariant does.
3. **The checked source program.** The relevance-annotated Src program with
   its unfolding table that IxCC's front end builds from the bytes and the
   certificate (`a.src` in `Recheck.sound`). Serialized, it is the *image* the
   Aiur evaluator route runs.
4. **SrcEval's meaning in the kernel's model.** SrcEval
   ([`Src/Semantics.lean`](../IxCC/Src/Semantics.lean)) is the clocked
   big-step evaluator of Src, an environment machine that never evaluates an
   irrelevant position.

The spine's theorem, for the first grounded fragment
([certification design](certification-design.md#the-first-grounded-fragment)):

> **Grounded evaluation (planned).** Let `P` be a checked source program
> (an image with digest `D`) for target `c`, let the seeds `S` be `c` and the
> theorems `P`'s unfolding table names, and let `E` be the kernel's reading of
> the closure of `S` under a role table. Assume (ii) **faithfulness and
> typing**: `P` corresponds to `E` clause by clause, and every value, rule and
> equation SrcEval runs has a typing derivation in `E` in the kernel's rules.
> *Soundness:* if SrcEval on `P` returns `v` for `c` applied to the literals
> `xs`, and `v` reads back as the observation `w`, then in every set theory,
> every model of `E` with the laws and every level assignment, the constant
> `c` names, applied to `xs`, denotes what `w` names. *Progress:* if moreover
> (i) **existence**, `E` has a model with the laws, and `P` passes the
> fragment check, then SrcEval on `P` never gets stuck and never traps on `c`.

Soundness does not consume premise (i): it quantifies over every model, and
is true, but empty, if there is none. Premise (i) is what makes it say
something, and progress uses it (a trap would need a member of the empty set
`False` denotes). Progress removes the `GoesWrong` escape of today's
theorems, which a dishonest certificate can choose
([certification design](certification-design.md#what-is-proved-today)). The
evaluator route needs soundness alone (its run returned a value); the x86
claim needs both. Nothing in the spine depends on the back end. Until
2026-11-11 premise (i) read "IxCK accepts the environment with root `H` under
role table `ρ`", paired with a typing claim on `(H, ρ)`; the restatement and
its reasons are in the [certification
design](certification-design.md#the-architecture-premises-discharged-by-proofs).

**The premises are discharged by proofs, not by IxCC.** IxCC embeds no proof
verifier; claims about the same seeds compose by aggregation.

- **Premise (i) by an IxVM claim.** The certified IxVM work states, for an
  accepted `check` or `checkEnv` claim in its default context (the kernel's
  default role table, validated; no user axioms; no assumed leaves), that
  either the run exhibits a BLAKE3 collision or the *claimed environment* has
  a model in every set theory. The claimed environment is the kernel's
  reading, under the default role table and behind the committed prelude, of
  the closure of the claim's seeds in the records the run loaded, without the
  auxiliary constants of the kernel's inductive models. IxVM refuses a seed
  that is `unsafe` or `partial` (its follow-up branch also refuses an inert
  axiom such as `sorryAx`), so the paired claim is a `checkEnv` claim whose
  leaves are `S`, never one over a whole `ix compile` artifact, which always
  holds `partial` definitions. It discharges (i) once three things hold, none
  of them in this repository yet: that statement is today a reduction to
  eight per-layer obligations taken as hypotheses, and becomes a theorem when
  they are proved; it constrains the claimed constants by name, level
  parameters and type only, and must also fix their kind and stored value
  (else δ in a model is about some other value); and it covers the default
  role table only, while `ix compile` writes one table per artifact, so a
  lemma that the kernel reads a closure alike under the default table and
  under a restriction of it, when the closure holds no constant of a role the
  restriction leaves unbound, is needed beside the kernel's reader.
- **Premise (i) natively** (planned): the kernel's logical entry run on the
  closure of `S` alone, under the same table and prelude as the IxVM claim,
  so that both routes discharge one statement. The tiered whole-artifact
  acceptance the [kernel front end](kernel-front-end-design.md) runs today is
  more than (i) (every logical record of the artifact) and different from it
  (the artifact's table and prelude).
- **Premise (ii)** by the IxVM kernel circuit's *lowering claim* for `(S, D)`,
  which has the kernel's reading and the types and checks the image clause by
  clause; or natively, by the kernel front end's check of IxCC's reading
  against the kernel's and the kernel's derivations at each classified
  position. The typing part is stated in the kernel's rules (`Infer`,
  `DefEq`, `Red`) and needs their soundness in every model with the laws,
  which the kernel states today over its internal invariant only (a
  restatement over the public model is a dependency, planned on the kernel
  side).

So IxCC needs no soundness theorem for its own erased type checker and no
proof that its decoder agrees with IxCK's reader; it must read the same bytes
with the same hash, bind the target and `D` in its claims (so that `S` is
determined), define the faithfulness and typing clauses precisely, and prove
soundness and progress.

## Below the spine

### x86: the proved pipeline

**Implemented.** Src → Lam → Anf → Fir → Own → Cfg → Lir → Xv → Xl → typed
x86 → E1 → E2/ELF, each stage proved; `Recheck.sound`
([`Recheck/Proof/Soundness.lean`](../IxCC/Recheck/Proof/Soundness.lean)) and
the byte-level `verifyBytes_*_sound`
([`CompileClaim/Proof.lean`](../IxCC/CompileClaim/Proof.lean)) compose them
from claim bytes to the modelled object, relative to SrcEval on `a.src`.

> **x86, grounded (planned).** Let a compile claim verify
> (`CompileClaim.verifyBytes`), naming environment root `H`, role table `ρ`,
> target `c`, image digest `D` (a planned field), policy and object hash; let
> `S` be `c` and the theorems `D`'s table names, and `E` the kernel's reading
> of the closure of `S`. Assume premises (i) and (ii) for `(S, D)`. If the
> linked object returns `w` on inputs `ns`, then in every model of `E` with
> the laws, the constant `c` names applied to the literals `ns` denotes the
> value `w` reads back as.

It composes today's object theorem (the object refines SrcEval on the checked
source program, whose digest the verifier checks is `D`) with the spine:
progress removes the `GoesWrong` disjunct, soundness gives the denotation, and
readback names a model value. `H` and `ρ` stay in the claim as what IxCC
read: the records in which the closure of `S` was found, and the table its
pins came from (which must be a restriction of the table premise (i) is
stated under).

*Trusted:* the x86 instruction-set model (the byte machine is the processor,
`x86-v0-local-semantics`; the [reference-model route](x86-reference-model.md)
replaces this by agreement with the Sail model), the system loader
(`x86-v0-elf-writer`) and the driver model
(`x86-phase1-runtime-driver-model`, which the IxOS-0 step retires), all
recorded in the [trust ledger](trusted-extern-ledger.md); BLAKE3 collision
resistance wherever identity is stated; Lean's logic with its three standard
axioms. IxCK's soundness is a theorem in this repository, not an assumption.
When the premises are discharged by IxVM proofs, the proof system's
soundness and IxVM's consistency theorem (the IxVM workstream's result, whose
statement trusts the kernel's reader of Ixon records) join the base; when
they are discharged by running IxCK and a faithfulness check natively, only
that check's code joins it, and it is proved.
The certificate is not trusted: once every table entry is valid in the model
and progress holds, any accepted certificate yields the same denotation.

*Not covered:* what the usage, ownership and locality contracts guarantee.
Resource guarantees are outside this theorem; on this route the compiler acts
on a contract only where its own ownership checker verified it, and the
source-level resource theorem is planned separately ([resource
soundness](resource-soundness-design.md)).

*As a standalone executable* (the executable is implemented, the statement
planned). IxCC writes the executable itself (`ixcc compile --exe`), with its
own start-up shell, still trusted, and with no C driver; the same
statement is to be read off the process: "the linked object returns `w` on `ns`"
becomes "the executable run on the decimal forms of `ns` exits after writing
`w`", and later the program's own output bytes and exit code, or its trace of
platform events. The driver model leaves the trusted base; the loader's
post-state for a static executable and the platform's system-call model enter
it, and a claim about an executable binds the executable's hash, the platform,
the shell and the layout as well as the object's claim ([standalone
executables](standalone-executables-design.md)). For a numeric state machine
(`ixcc compile --exe --machine`, implemented) the statement is a session
theorem: every trace of platform events the process performs, with the
environment's answers, is one obtained by iterating the source step on those
answers unless the step goes wrong on the way (proved over the linked-object
model, from the per-call statement; that the shell realises the model is
assumed; [X2](standalone-executables-design.md#the-session-theorem)).

### Aiur, form (i): the fixed evaluator circuit (first)

**Planned; the circuit is the IxVM workstream's.** One formal-Aiur program,
the evaluator E, with one verifying key, runs SrcEval over images. The kernel
circuit proves a *lowering claim*: an image is a faithful reading of an Ixon
closure under a role binding. To discharge an evaluation axiom `ax : e = true`
(what `native_decide` and `bv_decide` now emit), an aggregation joins the
kernel circuit's claim that is conditional on `ax`, the lowering claim and E's
proof that SrcEval on the image returns `Bool.true` for `e`.

> **Aiur evaluator, grounded (planned).** If the aggregated proof verifies,
> then either the proof system was broken (a forged proof or a hash
> collision), or: premises (i) and (ii) hold for the image's seeds `S` and
> digest `D` (discharged by an IxVM `checkEnv` claim whose leaves are `S` and
> by the lowering claim, in the aggregate), SrcEval on the image returns `v`
> for `e` (E's run, with E's refinement of SrcEval proved on the IxVM side),
> and so, by soundness, in every model with the laws of the closure of `S`,
> `e` denotes the readback of `v`. For an evaluation axiom,
> `⟦e⟧ = ⟦Bool.true⟧`, so the axiom holds in every such model.

*IxCC's obligations:* SrcEval as a normative, versioned contract; the image
format with a decoder, a round-trip theorem and a deterministic producer; the
interfaces (pinned identities from the role binding, readback to an Ixon
expression, budgets as constants, universe profiles); the faithfulness
clauses, defined precisely so that the kernel circuit's lowering check can be
proved against them; and SrcEval's *adequacy* for the kernel's models (the
spine). *The IxVM workstream's:* E itself, its refinement of SrcEval on decoded
images, the kernel circuit's lowering check and the aggregation shape.

*Trusted:* the proof system's soundness (STARK, FRI, the hash), and the base
of the formal Aiur compiler's theorem, which is external to IxCC: the lowering
of a formal-Aiur program to circuits, its elaborator and exporter, and the
toolchain derivation of E's key; the aggregation layer and in-circuit verifier
until they are proved. No instruction-set, loader or driver model. IxCC's x86
pipeline is not on this route.

*Not covered:* resource guarantees. The evaluator runs over write-once
memory, so the contracts optimise nothing there; whatever they promise about a
program rests on the planned source-level resource theorem alone ([resource
soundness](resource-soundness-design.md)).

### Aiur, form (ii): per-program compilation (later)

**Research; designed, not scheduled.** A lowering from Fir to formal Aiur with a
backward simulation, so that each program gets its own circuit. It is faster
per step than the evaluator, but each program then has its own verifying key,
and nothing can yet check inside a circuit that a key is the compilation of a
given program, so until a key derivation is certified it serves standalone
proofs, not the discharge of evaluation axioms.

The design branches at Fir, which is first order with known calls,
constructors, `case`, projections and the `Nat` primitives, as formal Aiur
is; Own, Cfg, Lir and the x86 back end are not used. Fir's untyped objects
become one object enumeration per program, so shape typing (CD2 of the
[certification design](certification-design.md)) is an optimisation for wide
programs, not a prerequisite. A small `Nat` is one field element below 2^56,
range-checked by the formal Aiur word library; a result at or above that has no
derivation, which is this route's overflow: no proof, never a wrong one.
Division takes its quotient and remainder as advice and checks them; large
`Nat` needs limbs, whose specification is shared with the
[bignum library](bignum-design.md). The lowering is verified, not certifying:
it emits formal-Aiur syntax trees, and one translation-validation check runs
after formal Aiur's preparation step. The formal Aiur package is
self-contained (it needs only Mathlib, at the same toolchain, and imports
neither ix's root package nor IxCK), so the backend would be a separate
package depending on it and on IxCC, keeping Mathlib out of the x86 compiler's
build. A spike outside this tree lowered five K1 programs and ran them on
formal Aiur's evaluator against Fir's: 50 of 53 inputs agreed and 3 had no
derivation by design (two overflows of the 2^56 representation and one trap),
with no mismatch.

Its statement would compose: circuit acceptance ⇒ a run
of the formal-Aiur program (the external compiler theorem) ⇒ a Fir run (the
new backward simulation) ⇒ SrcEval on `a.src` (today's forward simulations)
⇒ the spine. It adds per-program trust in the toolchain's key derivation
until a formal key derivation exists.

*Not covered:* resource guarantees, as on the evaluator route ([resource
soundness](resource-soundness-design.md)).

The legacy Aiur model in this tree (the [legacy model](aiur-backend.md) docs,
`IxCC/Aiur`, about 5.8k lines, and the vendored snapshot, about 3.5k) checks a
bytecode format that neither form uses; the formal Aiur package supersedes or
contradicts all of it, and the [roadmap](roadmap.md#repository-and-landing)
retires it when the certified-IxVM work lands.

## What "certified end to end" means, by route

| | x86 | Aiur evaluator (i) | Aiur per program (ii) |
| --- | --- | --- | --- |
| Hypothesis | the claim verifies; premises (i) existence and (ii) faithfulness and typing for the seeds `S` (the target and the table's theorems) and the image digest `D`, discharged by IxVM proofs or natively; the object returns `w` | the aggregated proof verifies (it carries premises (i) and (ii)) | the program's circuit accepts, with (i) and (ii) |
| Conclusion | `w` reads back as what the target denotes on the inputs, in every model with the laws of the closure of `S` | `e` denotes the readback of E's result in every such model | as (i), for the compiled root |
| What IxCC proves above SrcEval | soundness and progress | soundness | soundness and progress |
| Above SrcEval | the spine | the spine | the spine |
| Below SrcEval | proved pipeline, E1, E2/ELF (implemented) | E refines SrcEval (IxVM side) | Fir → formal Aiur, backward (new) |
| Trusted | ISA model, loader, driver model; when (i) and (ii) come from IxVM proofs, also the proof system and IxVM's consistency theorem | proof system; formal Aiur compiler base; key derivation for E; aggregation; IxVM's consistency theorem (external, on the IxVM side) | as (i), plus per-program key derivation |
| State | below SrcEval implemented; spine planned | planned | research |

None of the routes gives termination or completeness: the object may time out
or fail for resources (63-bit `Nat` on x86 until bignums; trace-size limits on
Aiur) where the model has a value. None makes the *verifier* safe against
resource exhaustion; that is a separate property ([hardening
design](hardening-design.md)). On the proof-system routes a hostile input
costs the prover, not the verifier.

Roots that use opaque constants are outside every grounded statement: IxCK's
model keeps no value law for opaques ("Theorems and opaques keep no such
equation", [`IxCK/Kernel/Ixon/Values.lean`](../../IxCK/Kernel/Ixon/Values.lean)),
so neither SrcEval's evaluation of an allowlisted opaque through its stored
value nor a recorded interpretation holds in every model with the laws; the
certified IxVM work's public model keeps none either (an opaque constant is
stored with no value). Images used to discharge a grounded claim carry no
stored-value opaques (settled with the restatement of 2026-11-11). Statements
relative to a recorded interpretation remain available to compile claims
([DR5](data-and-roots-design.md#dr5-library-structures-and-opaque-constants));
the reading of that decision is to be confirmed
([roadmap](roadmap.md#decisions-to-confirm)).
