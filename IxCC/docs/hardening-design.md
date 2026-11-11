# Hardening against dishonest input

Written 2026-11-10. **Status:** the fixed budgets and certificate caps are
**implemented** ([Middle-end budgets](compiler-design.md#middle-end-budgets));
HD-0 to HD-3 below are **planned**. The owner's question, "isn't the point of
certification ultimately to be hardened completely against dishonest input?",
asks for two properties that no single theorem gives.

## Two properties

- **Soundness against a dishonest certificate or claim.** What the theorems
  give. A verifier that accepts must be right about the object, whatever the
  certificate chose. Today it is right *relative to SrcEval on the source it
  built, unless that source goes wrong*, and the certificate can choose to make
  it go wrong ([certification design](certification-design.md#what-is-proved-today)).
  The spine's progress result removes that choice for the first fragment
  (SP-1), and the table lemmas (SP-0) remove the certificate's influence on
  denotations. Until then, hostile certificates that make the
  source stuck are a known gap, refused in practice by `checkCanonical` and the
  root-shape checks, not by a theorem.
- **Bounded resources.** A verifier must also *finish*, within stated time,
  memory and stack, on any bytes. No correctness theorem says this: an
  accepting verifier that runs for a week is still sound. It needs its own
  design, measurement and gate.

On the [Aiur proof-system routes](end-to-end.md) the second property moves:
a hostile input costs the prover, who must produce a trace, and the
verifier's work is fixed by the proof system. On the x86 route the verifier is
IxCC's own code running on the claimant's bytes and certificate, so the
property is IxCC's.

## Current state

From bytes (an `.ixe` of at most 16 MiB, a sidecar and a certificate of at
most 64 MiB of JSON each), through `verifyBytes`, `checkClaim`,
`Ring0Sip.verifyBytes` and `ixcc check-cert`:

- **Bounded and measured.** Every recursion over term structure on the
  verifier path is held at least four times below its measured 8 MiB stack
  overflow by the depth budgets; every certificate list is capped in program
  quantities before its first reader, and the comparisons that walked lists
  per element are loops; `tests-recheck` runs every verifier entry point in a
  child process with an 8 MiB stack (and the wide inputs on 2 MiB) at and past
  each budget. Time apart from typing: the slowest accepted certificate built
  to stress the stages took 7.8 s; the stages' separately measured worst cases
  sum to about 45 s, an estimate, not a run. Memory is proportional to the
  input and capped by it (at most 2.9 GB measured). Details and figures are in
  [Middle-end budgets](compiler-design.md#middle-end-budgets).
- **Not bounded.** Typing at ingress, on by default, is the largest cost
  measured: 51.7 s of a 51.8 s check of the committed 1.1 MB `scalar.ixe`
  (0.46 s with typing off). The erased type checker's fuel is per constant
  (`Tc.maxRecFuel`), so a closure's typing is bounded only by the decoder's
  16,384-constant limit times that fuel; a closure at the 16 MiB limit has not
  been built. No certificate near all the stage limits at once has been built.
  Programs built in memory without ingress or `Recheck.checkSrc` (a stated
  precondition) reach about 12 GB in the front end at `maxSrcVisits`. No audit
  has covered every recursion on the verifier path below 8 MiB. The producer
  (`ixcc compile`) is not bounded the same way.

## The plan

**HD-0. Close the typing gap, add a fuzzing gate (planned; weeks).**
- A budget on the whole closure's typing (fuel shared across constants, or
  typing only the constants the roots reach), measured against `scalar.ixe`;
  until it lands, the documents say that typing time is outside the verifier's
  time bound.
- A required fuzzing check: generated hostile closures, sidecars and
  certificates (mutations of the committed ones, and the amplifier families
  `tests-recheck` already writes) through every byte-level verifier entry
  point, each run under a wall-clock and memory limit; a run past either limit
  fails the check.

**HD-1. Typing off the verifier path (planned; with SP-0).** Once IxCK's
acceptance is a premise discharged by an IxVM proof or a native kernel run
([certification design](certification-design.md#the-architecture-premises-discharged-by-proofs)),
IxCC's erased type checker leaves the guarantee path. Whether it stays as an
optional early filter, or is retired, is a [decision to
confirm](roadmap.md#decisions-to-confirm). Either way the dominant unbounded
cost leaves IxCC's verifier; where kernel acceptance is checked instead
becomes the question (an [open decision](roadmap.md#open-decisions)).

**HD-2. A metered verifier by construction (planned; after SP-0).** Replace
the patchwork of per-stage budgets by one work budget threaded through every
loop and recursion on the verifier path, charged before each unit of work,
and a theorem: the verifier's total work is at most a stated function of the
input's size. The fixed budgets stay as the stack bounds and as the
amplification limits within that total. *Size [estimate]:* 2–5k lines, by
comparison with threading the step budget through the resource checker's
expression walks and the certificate-cap rounds of November 2026.

**HD-3. Recursion off input-sized data (planned).** Every traversal of
input-sized data is a loop or a recursion whose depth a budget bounds, by an
audit of the verifier path, enforced by running every entry point at the
budgets on a 2 MiB stack (a quarter of the target). *Size [estimate]:* 1–2k
lines.

**Order.** HD-0 now; HD-1 with SP-0; HD-2 and HD-3 after SP-0, because SP-0
changes the verifier's front (the reader, the premises, the typing). Whether
HD-2 should precede the spine instead is an [open
decision](roadmap.md#open-decisions).

## External dependencies

- **The kernel's typing core.** IxCK's typing core is exponential in the size
  of a well-typed constant whose `let`s duplicate a growing subterm: a constant
  of about 225 bytes takes about a minute and each further `let` doubles the
  time. Lean's own kernel checks the same type in constant time. Any verifier
  that runs IxCK's admission on hostile bytes inherits this. *The cause is not
  established.* It was first attributed, by reading the code and without a
  profile, to substituting every `let` eagerly and losing the sharing when
  binder telescopes are rebuilt. But the core's binder operations already
  return a term unchanged outside its loose-variable range, and its typing
  memo is keyed on the term alone. The IxVM kernel circuit of the certified
  IxVM work (pull request #678) substitutes `let`s just as eagerly and is
  linear on the same family (that work's measurement of 2026-11-11, up to a
  thousand `let`s); what it has and
  IxCK's core lacks is interning of terms, so that equal terms are one object
  and compare in constant time, and a memo table for every function. A count
  of calls and memo misses per function would settle which of the core's
  functions doubles. The fix (interning and memoisation in the core, or
  charging its walks to a budget, or both) is the kernel owners' to decide. It
  matters to IxCC because IxCC's verifier is to run IxCK itself: the front end
  over the kernel ([kernel front end](kernel-front-end-design.md#resource-bounds))
  runs the kernel's entry and typing core on the claimant's bytes, and the core
  exposes no work counter for IxCC to bound; a step budget in the core is that
  front end's dependency.
- **The proof system's verifier** on the Aiur routes, which has its own
  parameter checks (the IxVM workstream's).
