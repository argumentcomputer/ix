# Evaluator interface: SrcEval as a contract, and the Src image

Written 2026-11-10. **Status:** EV-0 implemented ([source steps](source-steps.md));
EV-1 and EV-2 planned ([roadmap](roadmap.md#milestones)).

## What exists today

- **SrcEval** ([`Src/Semantics.lean`](../IxCC/Src/Semantics.lean)): the rules
  E1–E9, A1–A3 and F1–F8 are named only in the module's docstring; no
  identifier carries them, and there is no version.
- **The unfolding lemmas** are complete: one bind-form equation per case of
  the evaluator ([`Src/Proof/Unfold.lean`](../IxCC/Src/Proof/Unfold.lean)),
  and clock monotonicity ([`Src/Proof/Mono.lean`](../IxCC/Src/Proof/Mono.lean)).
- **The clock is a depth bound, not a step count.** In an application the
  function and the argument are evaluated at the same clock; only the charged
  rules (δ, β, ι, `case`, forcing a by-name slot, `Quot.lift`) evaluate their
  continuation one tick lower. The least clock at which `Src.run` succeeds
  (the test helper `leastClock`,
  [`IxCCTests/Src/Runs.lean`](../IxCCTests/Src/Runs.lean)) is the nesting depth
  of charges, not the work.
- **Entry points.** `Src.run` evaluates a constant root at all-zero levels on
  value arguments; there is no entry for a closed term.
- **Serialization.** None: nothing serializes `Src.Program`. The certificate
  carries the producer's decisions, not the program, which `Recheck.run`
  rebuilds from the closure.
- **Pins** come from the role table of a role-bound closure, through a stated
  mapping from the kernel's roles, and from a fixed table of addresses for an
  unbound one ([`Src/Pinned.lean`](../IxCC/Src/Pinned.lean),
  [byte contract](byte-contract.md#pinned-identities)).
- **Readback** gives constructor indices, not addresses
  ([`Src/Readback.lean`](../IxCC/Src/Readback.lean)).
- **Determinism.** The front end is a pure function of the closure, the
  sidecar and the configuration ([`Src/Load.lean`](../IxCC/Src/Load.lean)),
  but the sidecar (the root list, whose order fixes the constant numbering,
  and the equation proposals, which decide the table) is not fixed by the
  closure.
- **Budgets** are constants scattered over the front end (`Src.maxTermDepth`,
  the table's node limits, the universe-expansion limit).

## Why this comes first

The [Aiur evaluator route](end-to-end.md#aiur-form-i-the-fixed-evaluator-circuit-first)
runs SrcEval inside a fixed circuit over a serialized Src program, the
*image*. The IxVM workstream builds the circuit and proves it refines SrcEval;
it can start only when SrcEval is frozen, when an executable oracle exists to
test against, and when the image's layout is fixed. These pieces are small,
need no proof of adequacy, and are IxCC's to supply (ownership of the image
format is an [open decision](roadmap.md#open-decisions); the default is
IxCC). The same pieces serve the spine: the image *is* the checked source
program the grounded theorem speaks of.

## EV-0. Step counts

**Implemented**, as [source steps](source-steps.md) describes: the unit, the
counter (`IxCCTests/Src/Steps.lean`), the `src-steps` tool, three pinned rows in
`tests-src`, and the tables of every committed corpus family and benchmark
fixture ([performance/src-steps-2026-11-10](performance/src-steps-2026-11-10/README.md)).
The IxVM workstream's four families wait for their closures. The common unit of cost between IxCC's evaluator and IxVM's
kernel is one SrcEval step: one application of a charged rule. Because the
clock is a depth bound, counting needs a separate counter.

- **Deliverable.** A test executable with a counting twin of SrcEval, checked
  on every run against `Src.run`'s result at the same clock, that prints for a
  closure, a root and arguments the charged steps by rule family, the value,
  and the least clock; a regression in `tests-src` that the counted result
  equals `Src.run`'s on the K1 rows.
- **Programs.** The K1 rows at three sizes per family, and the IxVM
  workstream's four scalable families once it supplies their closures: mutual
  even/odd on `Nat`, a left fold of `Nat.add` over `List.range n`, naive
  structural `fib n` and `decide (∀ i < n, p i)` through `Nat.decidableBallLT`.
- **Exit.** The tables, reproducible from committed closures.
- **Size [estimate].** About 0.4k lines; days. The counter is a measurement
  tool, off every checked path.

## EV-1. The evaluator contract, version 1

- **The rules.** E1–E9, A1–A3 and F1–F8 as defined in
  [`Src/Semantics.lean`](../IxCC/Src/Semantics.lean) when EV-1 lands, with
  level-exact `irr` decisions at concrete levels (D18). A constant names the
  version; each rule gets an anchor on the arm that implements it, without
  renaming anything; a changelog document lists, per version, each changed
  rule and why; the contract's files are pinned so that a change without a
  version bump fails a check.
- **The proof interface.** The bind-form unfolding lemmas (D-1) and clock
  monotonicity, through which IxCC's own simulations reason, are the
  contract's lemma surface; an implementation is proved against them, not
  against the `match` in `eval`.
- **Entry points.** Three executable, clocked entries beside `Src.run`, for the
  differential oracle: a closed term at all-zero levels; the same for a
  `Bool`-typed term, returning the pinned `Bool` constructor; and the same read
  back as a constructor tree with `Nat` literals. A closed term `e` is made a
  root `r := e` of the program it is evaluated in; no new semantics is
  involved.
- **What may change later, none of it in version 1.** The mechanism of `irr`
  decisions is stable; the rule set is not final. Pending, each a new version:
  strings (E9, once arrays and strings land), raw fixed-width words and the
  stuck rule for bounded constructions
  ([DR2](data-and-roots-design.md#dr2-fixed-width-integers-and-int)), the
  array and byte-array primitives (DR3), interpreted opaques (DR5) and the
  question of evaluation through a stored opaque value (DC-2 in the
  [roadmap](roadmap.md#decisions-to-confirm)). P8, shape typing and the
  result-shape work change no rule.
- **Exit.** The version constant and changelog; the entries agree with
  `Src.run` on the K1 roots; the pin check fails on an unversioned change.
- **Size [estimate].** 0.3–0.6k lines and the documents; weeks.

## EV-2. The Src image, version 1

**Layout requirements**, set by a reader that is a circuit and pays per read:
- *word-oriented*: 32-bit words, not a byte stream;
- *index-resolved*: terms refer to constants by their dense index (`CId`),
  never by address, so the reader never walks an address-keyed map;
- *self-delimiting, one canonical encoding*: every structure carries its
  length, the decoder is total, and it rejects every non-canonical word
  sequence;
- *linked to Ixon*: each constant carries its Ixon address, and each `eqn` and
  `csimp` entry names its theorem.

**Subterms stay shared.** Src expands Ixon's shared subterms and keeps full
type terms, so a flat image is much larger than the closure: about 6 times the
closure's bytes for a small program (`fib` from `bench-k1`) and about 21 times
for the one-megabyte closures, by a measurement outside this tree. A circuit
hashes everything it reads, so the format the evaluator reads keeps subterms
shared: nodes in a fixed canonical order, each distinct subterm once, children
by node index. The tree form remains the specification of the content, and
decoding expands the DAG.

**Sections.**
- a header: magic, the format version, the contract version, the budgets
  (`Src.maxTermDepth` and the front end's other limits, gathered into one
  structure per format version), and a digest of the sidecar and the
  configuration, or nothing if the proposals become canonical (every
  `f.eq_def` for every reached recursive `f`, derivable from the closure);
- the constant table in `CId` order: the source identity, the Ixon address,
  the kind, the level-parameter count, the relevance record;
- the terms: Src's one level-polymorphic term per constant, with its
  level-exact relevance conditions, which a reader decides at concrete levels
  by one scan of a short list (duplicating terms per universe profile, as
  erasure does, is not needed);
- the unfolding table with strictly increasing keys, `eqn` and `csimp` entries
  naming their theorems;
- the roots;
- the pinned identities, which a consumer checks against its role table;
- `opaqueByValue` and, after DR5, recorded interpretations, as two separate
  sections; a discharge image carries both empty (DC-2).

**Theorems.** A Lean encoder and decoder over `Src.Syntax` alone, in the
kernel-evaluable style of the recheck path (structural recursion on the word
list), with: round trip (`encode p` decodes to a program equal to `p` up to
the extensional equality of its maps); injectivity of `encode`; uniqueness of
encodings (a word sequence the decoder accepts is the encoding of what it
decodes to, so the image's digest is a function of the program); totality. All
fenced with the standard axioms. The image's BLAKE3 digest is the program's
identity between the consumer's claims.

**Determinism.** The producer, the unfolding-table selection and the
relevance annotator are deterministic functions of the closure bytes, the role
table, the roots and the options; the annotation is a function of the program
once `checkCanonical` accepts it. Soundness does not need canonicity, because
the consumer checks; caching by content address does.

**Interfaces.**
- *Pinned identities* come from the role table of the closure (implemented:
  ingress reads it from a role-bound envelope, and the pins and the `prim`
  entries read it instead of the fixed table, which stays for unbound
  closures; [byte contract](byte-contract.md#pinned-identities)); the claim is
  to name that table (SP-0).
- *Readback* to an Ixon expression in one canonical form: a `Nat` value to a
  literal (little-endian, as Ixon stores it); a constructor value to its
  constructor by address at its universe arguments, applied to the readbacks
  of its parameters (closed on the first fragment) and fields, proof fields
  omitted or filled with a fixed placeholder, so readback is canonical up to
  proof irrelevance, as the model is. Its BLAKE3 address is the output address
  of an evaluation claim. A lemma that the readback denotes the value is part
  of SP-0's readback lemma.
- *Budgets* are admission limits for a circuit and change only with the
  format version.

**Exit.** The theorems fenced; the round trip over every committed closure in
a required gate; byte-identical images from two runs on two machines; their
digests committed as test vectors; the IxVM workstream's reader decodes the
same images.

**Size [estimate].** The codec about 0.5k lines and its proofs 1–2k, by
comparison with IxCC's canonical binary format for Aiur bytecode with its
proofs (1.3k lines, [`Aiur/Wire.lean`](../IxCC/Aiur/Wire.lean) and
`Aiur/Wire/`); the interfaces 0.5–1.5k. 1–3 months.

## Faithfulness

Faithfulness is the second premise of the grounded statements
([certification design](certification-design.md#the-architecture-premises-discharged-by-proofs)):
the image with digest `D` is the checked source program of the environment
with root `H`, as IxCK reads it under role table `ρ`. IxCC does not prove it
about its own decoder; whoever holds the kernel's reading checks it, which is
the IxVM kernel circuit's lowering claim for `(H, D)` on the evaluator route,
and on the x86 route either that claim or, natively, IxCC's verifier-side
ingress rebuilt on IxCK's reader (an [open decision](roadmap.md#open-decisions)).
IxCC's part is to define the clauses precisely, with a structural map from
IxCK's terms to `Src.Term` as their specification (SP-0), and to prove that
they imply what the adequacy theorem consumes (SP-1).

The clauses form a checklist over `(closure, image)`
([CD1](certification-design.md#cd1-the-front-end-theorem)): the image is the
installed and lazified program (syntactic); every `eqn` and `csimp` entry names
a theorem with the right statement and a standard-axiom closure (syntactic,
once the kernel has accepted the theorem); the pinned identities name the role
binding's constants (syntactic); and every position tagged irrelevant at a
profile has a type that infers to `Sort 0` at that profile or is itself a type,
and conversely every proof position is tagged irrelevant (stated against the
kernel's typing judgement, so the kernel circuit can decide it with its own
inference).

## What the evaluator route does not need from IxCC

The x86 back end, linking and the trust ledger; the compile claim to an ELF
hash; stage L; P8 (the evaluator has closures natively). It returns a second,
independent consumer of SrcEval, differential tests against `Src.run` on
IxCC's corpus and on harvested evaluation axioms, counterexamples to IxCC's
relevance annotator from the kernel's own inference, and measurements in
SrcEval steps.

## Later

- **Optimised images.** Feeding erased Lam or Anf after inlining to the
  evaluator saves carrying type arguments. Erasure and ANF conversion are
  deterministic and can be recomputed by a consumer; the heuristic passes
  would need certificates whose checker is small enough to write in a circuit
  language, which the recheck path's walk engine is not. Only after
  measurement.
- **Kernel-evaluable checking.** D17 keeps everything on the recheck path
  evaluable by Lean's kernel. Extending that to the image producer's checking
  half lets an evaluator run it as a Lean program.
