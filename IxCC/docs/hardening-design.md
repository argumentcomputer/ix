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
- **Not bounded.** The certified kernel's acceptance at ingress (every
  byte-level entry point runs it; there is no unchecked mode) is bounded by the
  batch limits (16,384 records, 1 MiB each, 16 MiB in all) and its per-call
  recursion fuel, not by a work budget: on the committed closures it takes
  about a second and a half at the most (2.5 MB, about 3,600 records), where
  the erased type checker took about 200 s, but a hostile universe level can
  hold it as long as its author chooses (below, external dependencies). On an
  8 MiB and a 2 MiB stack it accepts the generated chains at IxCC's depth
  budget (`tests-recheck`'s stack part); a closure at the 16 MiB limit has not
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
IxCC's erased type checker leaves the guarantee path. It is retired, not
kept as a filter (DC-4, decided): the [kernel front
end](kernel-front-end-design.md) replaces it in the producer and on the
native verifier path, and the switch has made it the only front end (the
owner's decision of 2026-11-11); the checker's code is deleted (the switch's
step 4). The erased checker's cost leaves IxCC's verifier; the kernel's
typing core takes its place there, exponential on some universe-level
comparisons until its planned call budget lands (its blow-up on chains of `let` is
fixed, [below](#external-dependencies)).

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

- **The kernel's typing core.** IxCK's typing core took time exponential in
  the size of a well-typed constant whose ∀s share one type at each step: a
  constant of about 225 bytes (`k = 30` nested `let`s, `let a(j+1) : Type :=
  aj → aj`) took about 50 s, each further step doubling the time, where
  Lean's own kernel is flat. *The cause* (profiled with per-function counts):
  no work on terms doubles; two functions on universe levels did. The ∀ rule
  built its level as `imax u v`, and on such a chain the level is shared as a
  DAG of linear size whose tree doubles per step; `Level.simplify` (from the
  comparison of the inferred sort with the declared one) and `levelHasParam`
  (at every `.sort` node built) walked it as a tree. The `let` is incidental:
  a `let`-free chain of sharing-table entries (`T (j+1) = T j → T j`) did the
  same. *The fix* was made in the kernel package on this branch, in parallel
  with the switch of IxCC's front end to the kernel, which proceeds (the
  owner's decision of 2026-11-11), and has landed: the ∀ rule builds its
  level with the official kernel's `mk_imax`/`mk_max` folds (`Level.mkIMax`,
  which is always one of its arguments or their plain `imax`), in the
  specification, the executed core and the declarative rule with its
  soundness proof, and `Level` caches its has-parameter bit. Every such chain
  then checks in milliseconds at a thousand steps, through the kernel's entry
  and through IxCC's front end over it (28 ms at 30 `let`s where it took 50 s,
  [kernel front end](kernel-front-end-design.md#resource-bounds), which keeps
  the measurements from before the fix; `tests-kernel-front` checks such a
  closure at 200). Levels the folds cannot merge (two chains at two universe
  parameters each mentioning the other at every step, or levels unfolding
  builds by instantiating at `max u u`) stay shared as DAGs, and the kernel's
  level walks are now memoised on them (`docs/kernel.md`, "Running time"), so
  such constants also check in milliseconds. *Still exposed*: the level
  comparison itself. Deciding `l ≤ r` for levels with `imax` is coNP-hard
  (the reduction is in `docs/kernel.md`), so any complete comparison, the
  kernel's included, takes time exponential in the number of universe
  parameters on some small constants; Lean's kernel avoids this by an
  incomplete comparison that refuses them. It matters to IxCC because IxCC's
  verifier runs IxCK itself: since the switch, the erased checker is gone
  from the verifier path, and a closure of ordinary size carrying such a
  constant can hold the byte-level verifiers as long as its author chooses.
  The core exposes no work counter, and its fuel bounds recursion depth, not
  work; the planned guard is a call budget in the kernel's level comparison,
  set by the caller, which the front end passes and reports as a decline
  (KF-3). Until it
  lands, a verifier that runs IxCK's admission on hostile bytes needs a time
  and memory limit of its own.
- **The proof system's verifier** on the Aiur routes, which has its own
  parameter checks (the IxVM workstream's).
