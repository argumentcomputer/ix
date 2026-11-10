# End-to-end certification: one spine, two back ends

Written 2026-11-10. **Status:** below the source evaluator the x86 route is
implemented and proved; the shared spine above it is **planned**; the Aiur
routes are **planned**, the first of them on the IxVM side. This page says
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
   [`Ixon/V3/Env.lean`](../IxCC/Ixon/V3/Env.lean)), which accepts only the
   version-4 envelope without a role binding.
2. **The kernel's acceptance and its model.** An environment IxCK accepts
   has a *strong* model (`checkDecls_sound`,
   [`IxCK/Kernel/Verify/Cached/MainC.lean`](../../IxCK/Kernel/Verify/Cached/MainC.lean);
   from bytes, `checkBytes_strongModel`,
   [`IxCK/Kernel/Admission/Reference.lean`](../../IxCK/Kernel/Admission/Reference.lean)):
   its invariant `EnvModelM`
   ([`IxCK/Kernel/Model/Annot/EnvModelM.lean`](../../IxCK/Kernel/Model/Annot/EnvModelM.lean))
   says that definitions denote their stored values, stored constants
   (theorems included) inhabit their types, recursor rules, projections and η
   hold, and literals and every `Nat` operation mean what they say. Packaged
   as `RulesInputs`
   ([`IxCK/Kernel/Model/Rules/Inputs.lean`](../../IxCK/Kernel/Model/Rules/Inputs.lean)),
   these facts make IxCK's reduction, conversion and inference sound
   (`red_sound`, `defeq_sound`, `infer_sound`,
   [`IxCK/Kernel/Model/Rules/Sound.lean`](../../IxCK/Kernel/Model/Rules/Sound.lean)).
   The weak public `Model` of `model_exists` states types only and validates
   no definitional unfolding ([`IxCK/Kernel/Denotes.lean`](../../IxCK/Kernel/Denotes.lean)),
   so the spine is stated over strong models.
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

> **Grounded evaluation (planned).** Let `H` be the root address of an
> environment and `ρ` a role table, and let `P` be a checked source program
> (an image with digest `D`) for target `c`. Assume two premises:
> (i) **acceptance**, IxCK accepts the environment with root `H` under `ρ`;
> (ii) **faithfulness**, `P` satisfies the faithfulness clauses with respect
> to IxCK's reading of those bytes. If `P` passes the fragment check and
> SrcEval on `P` returns `v` for `c` applied to inputs `xs`, then for every set theory, every strong model of the accepted
> environment and every level assignment, the kernel constant that `c` names,
> applied to the encodings of `xs`, denotes what the readback of `v` denotes.
> On fragment-checked programs SrcEval never gets stuck and never traps.

The last sentence is a progress result. It removes the `GoesWrong` escape of
today's theorems, which a dishonest certificate can choose
([certification design](certification-design.md#what-is-proved-today)).
Nothing in the spine depends on the back end.

**The premises are discharged by proofs, not by IxCC.** A consumer discharges
acceptance with an IxVM typing proof for `H`, and faithfulness with the IxVM
kernel circuit's *lowering claim* for `(H, D)`, which has the kernel's reading
and the types and checks the image clause by clause; or natively, by running
IxCK and a native check. The claims compose by aggregation over the same
addresses, as IxVM's conditional claims already do; IxCC embeds no proof
verifier. So IxCC needs no soundness theorem for its own erased type checker
and no proof that its decoder agrees with IxCK's reader; it must read the same
bytes with the same hash and the same role table, bind `H`, `ρ`, the target and
`D` in its claims, define the faithfulness clauses precisely, and prove
adequacy. That IxVM refines IxCK is the IxVM workstream's result, an external
dependency ([certification design](certification-design.md#the-architecture-premises-discharged-by-proofs)).

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
> target `c`, image digest `D`, policy and object hash, and assume premises
> (i) and (ii) for `(H, ρ, D)`. If the linked object returns `w` on inputs
> `ns`, then in every strong model of the accepted environment, the constant
> `c` names applied to the literals `ns` denotes the value `w` reads back as.

It composes today's object theorem (the object refines SrcEval on the checked
source program, whose digest the verifier checks is `D`) with the spine: the
two premises, valid table entries, adequacy with progress, and readback in
the model.

*Trusted:* the x86 instruction-set model (the byte machine is the processor,
`x86-v0-local-semantics`; the [reference-model route](x86-reference-model.md)
replaces this by agreement with the Sail model), the system loader
(`x86-v0-elf-writer`) and the driver model
(`x86-phase1-runtime-driver-model`, which the IxOS-0 step retires), all
recorded in the [trust ledger](trusted-extern-ledger.md); BLAKE3 collision
resistance wherever identity is stated; Lean's logic with its three standard
axioms. IxCK's soundness is a theorem in this repository, not an assumption.
When the premises are discharged by IxVM proofs, the proof system's
soundness and IxVM's refinement of IxCK (the IxVM workstream's result) join
the base; when they are discharged by running IxCK and a faithfulness check
natively, only that check's code joins it, and it is proved.
The certificate is not trusted: once every table entry is valid in the model
and progress holds, any accepted certificate yields the same denotation.

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
> collision), or: premises (i) and (ii) hold for the claim's `(H, ρ, D)`
> (discharged by the IxVM typing claim and the lowering claim in the
> aggregate), SrcEval on the image returns `v` for `e` (E's run, with E's
> refinement of SrcEval proved on the IxVM side), and so in every strong model
> of the accepted environment `e` denotes the readback of `v`. For an
> evaluation axiom, `⟦e⟧ = ⟦Bool.true⟧`, so the axiom holds in every such
> model.

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

The legacy Aiur model in this tree (the [legacy model](aiur-backend.md) docs,
`IxCC/Aiur`, about 5.8k lines, and the vendored snapshot, about 3.5k) checks a
bytecode format that neither form uses; the formal Aiur package supersedes or
contradicts all of it, and the [roadmap](roadmap.md#repository-and-landing)
retires it when the certified-IxVM work lands.

## What "certified end to end" means, by route

| | x86 | Aiur evaluator (i) | Aiur per program (ii) |
| --- | --- | --- | --- |
| Hypothesis | the claim verifies; premises (i) acceptance and (ii) faithfulness for the claim's `(H, ρ, D)`, discharged by IxVM proofs or natively; the object returns `w` | the aggregated proof verifies (it carries premises (i) and (ii)) | the program's circuit accepts, with (i) and (ii) |
| Conclusion | `w` reads back as what the target denotes on the inputs, in every strong model | `e` denotes the readback of E's result in every strong model | as (i), for the compiled root |
| Above SrcEval | the spine | the spine | the spine |
| Below SrcEval | proved pipeline, E1, E2/ELF (implemented) | E refines SrcEval (IxVM side) | Fir → formal Aiur, backward (new) |
| Trusted | ISA model, loader, driver model; when (i) and (ii) come from IxVM proofs, also the proof system and IxVM's refinement of IxCK | proof system; formal Aiur compiler base; key derivation for E; aggregation; IxVM's refinement of IxCK (external, proved on the IxVM side) | as (i), plus per-program key derivation |
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
value nor a recorded interpretation holds in every strong model. Statements
relative to a recorded interpretation remain available to compile claims
([DR5](data-and-roots-design.md#dr5-library-structures-and-opaque-constants));
the reading of that decision is to be confirmed
([roadmap](roadmap.md#decisions-to-confirm)).
