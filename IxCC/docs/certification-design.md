# Certification depth: from SrcEval to Lean's meaning

Written 2026-11-09. **Status:** C1 to C3 are **planned**, C4 is
**research**. This document plans the semantic obligations that separate
today's theorems from a certified compiler for Lean: the front end (review
finding S6), adequacy against the certified kernel's model (S8), and the
`GoesWrong` disjunct. The [roadmap](roadmap.md) schedules them; the
[compile boundary](compile-boundary.md) records what the current theorems
cover.

## What is proved today

- `Recheck.sound` ([`Recheck/Proof/Soundness.lean:50`](../IxCC/Recheck/Proof/Soundness.lean))
  and its relatives (`Recheck.RcReplay.sound`, `Recheck.compiled_sound`, the
  `CompileClaim.verify*_sound` family, `verifyRing0Sip_sound`) say: if the
  linked object returns `w` on a root and `Nat` arguments, then either the
  checked source program `a.src` evaluates under SrcEval to a value whose
  view is `w`, or that source *goes wrong*; a source that does not go wrong
  gives an object that does not; a diverging source gives an object that
  diverges or fails for a resource.
- *Goes wrong* (`Front.GoesWrong`) means the source gets stuck, traps, or
  returns a value the root's type does not read back
  ([Correctness statement](compiler-design.md#correctness-statement)).
- The statements also rest on the x86, loader and driver assumptions of the
  [trust ledger](trusted-extern-ledger.md), and the byte-level ones on the
  BLAKE3 dependency recorded in the [compile boundary](compile-boundary.md).

What is not proved:
- **S6.** `a.src` is what the front end built from the ingested program: the
  unfolding table installed, the certificate's relevance annotation
  installed and checked, by-name modes set by `Lazify`
  ([`Recheck/Run.lean:186`](../IxCC/Recheck/Run.lean),
  [`Src/Recheck.lean:32-45`](../IxCC/Src/Recheck.lean)). No theorem relates
  `a.src` semantically to the ingested program. What is proved about the
  front end is syntactic: `Relevance.check` has a soundness theorem
  (`check_sound`, [`Src/Relevance/Proof/Sound.lean:533`](../IxCC/Src/Relevance/Proof/Sound.lean));
  `checkAxiomClosure_sound`
  ([`Src/Table/Check.lean:440`](../IxCC/Src/Table/Check.lean)) says that no
  constant reachable from an `eqn` or `csimp` theorem in the program's
  reference graph (`AxiomReach`) is an axiom other than the standard three;
  and `Src.Lazify.run_modeEq`
  ([`Src/Proof/Lazify.lean:527`](../IxCC/Src/Proof/Lazify.lean)) says that
  `Lazify.run` changes nothing but application modes.
  `Relevance.checkCanonical` ([`Src/Relevance/Check.lean:894`](../IxCC/Src/Relevance/Check.lean))
  has no theorem, and nothing composes these facts into `Recheck.sound`.
- **S8.** Nothing relates SrcEval to the meaning of the Lean definition.
  ix's [`Models/KernelBridge`](../../Models/KernelBridge/README.md) is a
  conditional simulation lemma: given a user-supplied relation between Src
  constants and kernel terms, a successful `Src.run` on `Nat` literals is
  matched by kernel reduction. The 2026-11-09 review (R2) found the relation
  constructible only for definitions with no type arguments, numerals,
  instance methods, `match` or recursion (one of 69 fixture roots), and
  found two structural reasons:
  1. `RelTerm.app` relates every argument, type arguments and motives
     included, although SrcEval never inspects an irrelevant argument; there
     is no case for an inductive in `RelConstStep`, no projection rule, and
     no constructor other than `Nat.zero`/`Nat.succ`.
  2. Kernel reduction is weak-head, so a recursive definition's constant
     reduces only to its stored `brecOn` or `WellFounded.fix` form, never to
     the right-hand side of the equation SrcEval unfolds by. Every recursive
     program is out of reach of a simulation into reduction.
- **`GoesWrong` is unbounded.** A stuck source, which a hostile but
  consistent certificate can arrange, discharges every clause. Ring-0
  confinement inherits this: it is proved for one call on a source-safe input
  (`admittedRing0Sip_call_not_goesWrong`, header of
  [`Ring0.lean`](../IxCC/Ring0.lean)).

## The routes

Two routes reach Lean's meaning, and they answer different questions.

| | Stage K: semantic adequacy (C4) | Stage L: per-program translation (C3) |
| --- | --- | --- |
| Statement | For every model `M` of the environment the certified kernel accepts, the native result denotes `⟦target xs⟧_M` | The native result equals the Lean function applied to the inputs: a Lean proposition about the constant itself |
| Applies to | Every program the compiler accepts, once proved | Each program the translator processes |
| Removes `GoesWrong` | No (adequacy is not progress) | Yes, for total functions |
| Lean proposition for the kernel target | Needs a further reflection step from models to the Lean function, for which no design exists (2026-11-09 IXCC-ROUTE §3) | Direct |
| Difficulty | Research; the spike covered almost nothing | Engineering, scaling with program size |

**Recommendation.** Build C1 and C2 first (they are needed by both routes
and by Ring 0), then a C3 prototype, used first for the bignum library and
then for the flagship entry points. Pursue C4 as research, starting with a
spike on a recursive program. Both flagship targets consume a C3-shaped
statement.

## C1. The front-end theorem (S6)

**Status: planned.** Two parts are proved already, as standalone lemmas not
yet composed into a corollary: the axiom-closure part of clause 2
(`checkAxiomClosure_sound`) and clause 4 (`Src.Lazify.run_modeEq`).

**Statement.** For an ingested program `P`, a table `T` and an annotation
`A` that `Recheck.front` accepts with result `a.src`:
1. `a.src` is `Lazify.run (install P T A)` with every check passed (a
   shape lemma);
2. each `eqn f thm` entry names a theorem constant of `P` whose statement is
   `∀ xs, f xs = rhs` with `rhs` the installed body, and each `csimp f g thm`
   one whose statement is `@f = @g`, every one with a standard-axiom closure
   (soundness of `Table.check`, including the constructor and recursor
   parts of the axiom walk);
3. every position tagged irrelevant at a profile has a type that is a sort
   or a proposition at that profile (soundness of `checkCanonical`);
4. `Lazify` changes only evaluation modes, so forgetting modes gives back the
   installed program;
5. the pinned identities (`known`, `prim` entries) name the pinned
   constants.

**Proof obligation.** Each clause is a lemma of the form "checker returns
`ok` ⇒ property", about Src syntax. C1 does not change `Recheck.sound`; it is
the premise package C2, C3 and C4 consume to get from `a.src` back to `P`.

**Trusted base.** Removes "the front end builds the intended program" from
what a reader must take on trust.

**Dependencies.** None.

**Size [estimate].** 4–8k lines. Basis: the checkers it covers
(`Relevance/Check.lean` 0.9k, `Table/` 1.2k, `Lazify.lean` 0.3k) and the
existing relevance soundness proofs (1.1k).

**Exit.** The five lemmas fenced with the standard axioms, and a corollary
of `Recheck.sound` that exposes them for the accepted artifact.

## C2. Source safety: a checked shape typing

**Status: planned.**

**Motivation.** Removing `GoesWrong` for arbitrary accepted programs, not
just translated ones; making Ring-0 confinement unconditional on
source safety; rejecting hostile certificates that make the source stuck.

**Design.** A checked, erased *shape* typing on Src: shapes for □, `Nat`,
strings, each inductive with its constructors' field shapes per universe
profile, and functions by arity, checked by a proved checker over `a.src`
with the root's readback type as the result shape. The checker is decided
on Src, not implied by kernel type checking: kernel acceptance implies no
decidable shape system (decision D18 of the pre-merge notes). An untrusted
annotator proposes the shapes.

**Proof obligation.** Progress and preservation for SrcEval on well-shaped
programs: a well-shaped root on well-shaped inputs returns a value of its
shape, traps, or times out; it never gets stuck, and the view always reads
the result back. Composed with `Recheck.sound`, this yields a corollary
without the stuck and view-mismatch cases. Two causes remain:
- a trap (`False.rec`), which only C3 or C4 exclude, since reaching it
  requires a proof of `False`;
- the stuck rule for bounded constructions of
  [D2](data-and-roots-design.md#d2-fixed-width-integers-and-int), whose
  erased proof shapes cannot see.

**Trusted base.** No change.

**Dependencies.** C1 (canonical relevance lets shapes treat irrelevant
positions as □).

**Size [estimate].** 5–7k lines, the pre-merge estimate for this item
(SRC-10).

**Exit.** A `GoesWrong`-free corollary of `Recheck.sound` and of the Ring-0
admission theorem for shape-checked programs, applied to every K1 root and
every compiled corpus root.

## C3. Stage L: a proof-producing translator

**Status: planned** (prototype), **research** (at the scale of IxCK).

**Design.** Following the CakeML translator, a tool that takes a Lean
constant `f` and the compiled program `P` containing its Ixon image, and
produces a Lean theorem: for all inputs `xs`, SrcEval of `P`'s root on the
encodings of `xs` returns the encoding of `f xs` at some clock. It works
from `f`'s equation lemmas and functional induction, evaluating SrcEval
symbolically. The link between the Lean constant and its Ixon image comes
from ix's certified Lean-to-Ixon compiler (`Ix.Cert.CompileCorrect`; see the
root [README](../../README.md)), or is checked per constant.

**Proof obligation.** The generated theorem, composed with `Recheck.sound`,
gives: if the object returns `w`, then `w` reads back as `f xs`. For a total
`f`, SrcEval returns at some clock for every input, so `GoesWrong` is
excluded for that program. No model appears in the statement.

**Fit.** First order and monomorphic first (K1, the
[bignum library](bignum-design.md#proof-obligation), state-machine roots);
higher-order and polymorphic functions after P8.

**Trusted base.** Removes "SrcEval is the source's meaning" for each
translated program.

**Dependencies.** C1. ix's compile certificate for the identification of
constants.

**Size [estimate].** Not estimated in lines. The pre-merge plan estimated
3–6 person-months for this item (SRC-11), a K1 prototype included.

**Exit.** Prototype: `fib`, `gcd` and `ackermann` from K1 with end-to-end
corollaries "the object's result is `f xs`", fenced. Then the bignum
library's closure.

## C4. Stage K: semantic adequacy (S8)

**Status: research.**

**What replaces the bridge's relation.** A semantic logical relation between
SrcEval values and model denotations, proved by induction on SrcEval's
clocked derivations, in which every SrcEval rule is justified by a fact that
holds in every model of an accepted environment, not by kernel reduction:
- irrelevant positions, type arguments and motives relate to anything,
  since SrcEval never inspects them;
- δ through an `eqn` entry is justified by the validity of the accepted
  equation theorem in the model, so recursion needs no reduction to the
  right-hand side; `csimp` likewise by `@f = @g`;
- δ through a body, ι (recursor rules), projections, constructors of any
  inductive, `Quot`, and the cast family by the corresponding model facts;
- each `Nat` and string primitive by one lemma that its meaning equals the
  denotation of the pinned definition (the same lemma as the conservativity
  lemmas of [D2](data-and-roots-design.md#d2-fixed-width-integers-and-int)),
  for all fifteen `Nat` operations, independently of the kernel's evaluation
  caps;
- by-name positions and closures by the clock-indexed function case, as the
  Lam and Anf relations already do.

**Statement.** If the claim verifies and the object returns `w`, then for
every model `M` of the environment the certified kernel reads from the
claim's environment bytes, the claim's target applied to the inputs denotes
the value `w` reads back as in `M`, or the source goes wrong. The
environment and the root term must come from the claim's bytes and target
through IxCK's reader, which shares IxCC's Ixon codec (the 2026-11-09
review's B3-1). `model_exists` (`IxCK/Kernel/MainTheorem.lean:60`) makes the
statement non-vacuous for environments IxCK accepts.

**Needed from IxCK.** Model-level statements that accepted definitions
denote their bodies, accepted theorems hold, recursor rules and projections
hold, and literals denote themselves. Which of these IxCK's model already
states in a usable form was not checked for this plan.

**Difficulty.** Unknown. The universe-profile machinery (level-exact
relevance), by-name evaluation and the model's treatment of large
eliminations are the expected hard parts. The previous spike was 1.85k lines
for a fragment containing one real root (2026-11-09 IXCC-ROUTE).

**Exit.** A spike: `fib` from `bench-k1`, recursive, with numerals,
instance methods and `match`, related end to end with the environment
derived from the claim bytes. A size estimate for the whole of C4 follows
the spike.

## What each extension adds

| Extension | C1 | C2 (shapes) | C3 (translator) | C4 (adequacy) |
| --- | --- | --- | --- | --- |
| P8 closures ([design](closures-design.md)) | — | function shapes by arity; applying a non-closure is a shape error | higher-order functions, as CakeML's translator handles them | the function case of the relation (below SrcEval P8 adds nothing) |
| Heap completion, RC, reuse | — | — | — | — (all below SrcEval) |
| Fixed-width, arrays, strings | pins of the new primitives | shapes for words and arrays; the bounded-construction rule remains | primitives' meanings are their Lean bodies, so nothing new | one meaning lemma per primitive |
| Interpreted opaques (`mixHash`, `getNumBits`) | the interpretation entries | — | the Lean function depends on an opaque, so the theorem holds only if `f`'s result is proved independent of it; prefer targets without opaques | models restricted to the interpretation |
| Bignums ([design](bignum-design.md)) | — | — | the library closure (its layer 3) | — (below SrcEval) |
| Structured roots and the byte ABI | — | the root's shape | encoders and decoders are ordinary compiled code | readback at the new types |
| State-machine effects | — | per step | `step` computes Lean's `step` | per step |

## The flagship targets

- **The certified kernel through IxCC.** The useful end statement is "if the
  object accepts the environment bytes, then IxCK's `checkDecls` accepts
  them", after which IxCK's soundness gives a model. Through C4 this needs a
  reflection step from models to the Lean function, and in its model-based
  form also needs the kernel's own closure to be accepted; IXCC-ROUTE §3(b)
  and (c) found no design for either. Through C3 the statement is direct, and
  the open question is whether the translator scales to IxCK's 1.3k–1.9k
  definitions and the parts of `Init` and `Std` they use. The opaque
  constants in its closure (D5) count against C3 unless IxCK removes them.
- **The IxOS monitor.** C2 makes Ring-0 confinement independent of source
  safety; C3 on the monitor's `step` makes its behaviour the Lean function's.
