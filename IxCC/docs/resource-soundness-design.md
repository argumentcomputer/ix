# Resource soundness: what usage, ownership and locality annotations guarantee

Written 2026-11-14. **Status: planned.** Nothing here is proved; the
milestones RE-0 to RE-3 are in the [roadmap](roadmap.md#resource-soundness),
and RE-0 is in progress. Only the lines that say *implemented* describe code
that exists.

Ixon binders carry usage, ownership and locality *contracts* written in Lean
source ([source contracts](../../docs/source-contracts.md)). This document
states what each contract is meant to guarantee as a property to be proved,
records what checks them today and what is proved, and plans the two layers
the owner decided on (2026-11-14): IxCC's own ownership checker as the
soundness basis for everything the compiler does with ownership, and a
separate, operational resource theorem about the source evaluator. Resource
soundness is not part of the [end-to-end statements](end-to-end.md): the
kernel's model, which grounds them, reads no contract.

## The annotations, and the property each should satisfy

Ixon carries the contracts on three nodes: a λ carries its input's contract,
a ∀ its input's contract and the contract of its result (each arrow of a
curried type has its own), and a `let` the contract of its binding. The
defaults are many, shared and unrestricted. Surface prefixes are `0 1 & ! ~`
and `let borrow`
([`IxCK/Ixon/Types/Contract.lean`](../../IxCK/Ixon/Types/Contract.lean),
[`IxCK/Ixon/Types/Modes.lean`](../../IxCK/Ixon/Types/Modes.lean)).

Each property is stated relative to an evaluator that never evaluates a
position graded erased, and is what an accepted program must satisfy on every
run:

| Contract | Meaning ([Ixon v4](../../docs/Ixon-v4.md)) | Property to prove |
| --- | --- | --- |
| `0` erased | zero computational consumptions | the argument is never inspected at run time: the result is unchanged when every erased argument is replaced by □ |
| `1` linear | exactly one consumption | on every terminating path, the binding is consumed exactly once (passing it to a linear or affine binder, returning it, moving it into a constructor, or capturing it in a closure that is invoked, each count once) |
| `&` affine | at most one consumption | as linear, at most once |
| `!` unique | unique ownership | when the value is consumed in a unique position, no other live reference to it exists, so updating or freeing it in place is unobservable |
| `~` local | confined to a scope | the value, and anything that retains it (closures, aggregates, projections, views), is unreachable after the scope it is confined to ends; for a parameter, that is the call |
| `let borrow` | a view on an owner | while the view is live its owner is not moved, and the view does not outlive its scope |

## Current state

**What checks them.** ix's resource checker (`Ix/Resource/`, the
`resource-v1` claim; [resource checking](../../docs/resource-checking.md)) is an
executable analysis of each annotated definition's kernel body against its
declared type. It has no stated semantics and no soundness theorem. What is
proved about resources: the usage algebra's operations are sound for their
reading as sets of consumption counts (`covers_sound`, `add_sound`,
`mul_sound` and the `join` lemmas, in `IxCK/Ixon/Types/Contract.lean`), and
one-line facts about the checker's state helpers (scope ancestry, moving and
sharing an owner, ending a loan, the demand check; `Ix/Resource/Basic.lean`,
with IxCC's copy in
[`Ixon/V3/Resource/StateProofs.lean`](../IxCC/Ixon/V3/Resource/StateProofs.lean)).
No theorem mentions the analysis or its acceptance, and none relates
acceptance to any semantics. The checker's own documentation says the claim
is uncertified as a resource claim.

**The kernel.** IxCK keeps contracts as identity data: its conversion compares
the *input* contracts of λ and ∀ (and in η), not the *result* contracts of ∀;
its model reads no contract. Typing is certified; contracts are not.

**IxCC.** No compiler theorem takes resource acceptance as a premise, and the
compile pipeline does not run the resource checker (IxCC's copy,
[`Ixon/V3/Resource/`](../IxCC/Ixon/V3/Resource), is reached only from tests
and the separate validation API).
- *Implemented:* IxCC re-establishes `0` itself. The untrusted annotator
  marks a binder written `0` irrelevant (`honourErased`,
  [`Src/Relevance/Annotate.lean`](../IxCC/Src/Relevance/Annotate.lean)), and the
  proved checker `Relevance.check` enforces that such a binder is irrelevant
  and has no relevant use. SrcEval never evaluates an irrelevant position, so
  a wrong `0` can only make IxCC refuse or the source go wrong.
- `1`, `&`, `!`, `~` and borrows are carried through Src, Lam, Anf and Fir
  without meaning (D16). They influence only which of two memory policies is
  selected (a program whose contracts are all zero-RC compiles on the immortal
  back end), and one specialisation refusal; the three back ends' theorems are
  proved without any contract premise. So today a wrong annotation can change
  the memory policy among proved ones, never the result.

**A confirmed hole.** A theorem whose statement equates two arrow types that
differ only in a result contract is accepted by the kernel (by `rfl`, since
conversion ignores result contracts) and not analysed by the resource
checker, which does not analyse theorems and trusts their statements. A cast
across it then re-labels any function's result contract: a local result
escapes as unrestricted, a shared value is returned as unique, and a one-shot
closure over a unique owner becomes reusable. The same attack on an input
contract fails in the kernel. Nothing runs differently today, because IxCC
gives these contracts no effect; if the compiler trusted them, the second and
third would update shared data in place and the first would return a dead
stack value. It is being closed in the checker (RE-0). It is the same kind of
hole that Idris 2 closed by making multiplicities part of a function type's
identity.

**Where the source check and IxCC disagree.**
- *Which arguments `0` erases.* The checker erases an argument whenever the
  head's *type* exposes an erased binder, including variable and projection
  heads and types reached through a definition; IxCC honours `0` only at
  constant heads (their syntactic Π telescope) and β-redexes, so it computes,
  and consumes resources in, arguments the checker never counted.
- *Uses inside proofs.* The checker counts uses inside proof terms; IxCC erases
  every proof. The first refuses erased proofs passed to library lemmas and
  linear values mentioned in proofs; the second means a linear consumption
  inside a proof is no consumption at run time (no closed exploit is known).
- *What is checked versus what is compiled.* The checker analyses kernel
  bodies: structural recursion through `brecOn`, well-founded recursion
  through `WellFounded.fix`, `match` through auxiliary matchers. IxCC compiles
  through its unfolding table: equation right-hand sides, `csimp` targets,
  by-name constants, pinned primitives. Contract transport copies header
  contracts onto an equation's right-hand side and refuses contracts inside it,
  gated on profile fields that ix's resource profile does not have; nobody
  analyses the right-hand side's usage, and `csimp` checking ignores contracts
  without a resource context ([`Src/Table/Check.lean`](../IxCC/Src/Table/Check.lean)).
- *Reductions.* The checker unfolds safe `opaque` constants, which the kernel
  never unfolds; it has no ι, no literal arithmetic and no proof irrelevance,
  so it refuses kernel-correct programs, even in erased positions.
- *How much it refuses.* A linear, affine, unique or local parameter that is
  not the last one; any fresh unique value (no constructor result is unique);
  recursion over or threading of an annotated parameter; branching on a linear
  value; proofs; a numeral passed to an annotated parameter; any local or
  linear value passed to a library function. 40 of the 46 annotated sources of
  the ownership suite are refused, 37 of them by the checker
  ([`fixtures/ownership/verdicts.json`](../fixtures/ownership/verdicts.json)).
  The checker is conservative: apart from the hole above and the erasure
  boundary, it refuses rather than mis-counts.

## The two layers (owner, 2026-11-14)

### Layer 1: annotations are untrusted hints; IxCC's ownership checker verifies them

Source annotations are hints. The soundness basis for anything the compiler
does with ownership is IxCC's own ownership checker on IxCC's intermediate
representation ([Ownership, reference counting and
reuse](compiler-design.md#ownership-reference-counting-and-reuse), planned in
Phase 2), exactly as erasure is re-checked by the relevance checker today. The
source-level resource check stays as a front-end diagnostic.

What the checker must establish, with each written contract a lower bound it
verifies (D16: honoured exactly, never weakened):
- **Unique.** A unique parameter is a premise for the callee and an obligation
  verified at every call site; a unique result is an obligation verified at
  every return of the callee and a premise for its callers. Unique values come
  only from fresh allocation, verified unique parameters or verified unique
  results, and are never duplicated. In-place update, the planned use of a
  source uniqueness annotation, happens only through this verification and
  never by trusting the annotation.
- **Borrow.** A borrowed value is never consumed without an increment, and its
  owner is not consumed while a view derived from it is live; verified where
  the view is used.
- **Local.** When stack or region allocation is introduced, a local value is
  verified not to escape its region where it is allocated and used, with a
  tail call ending the caller's region (so a local value is not passed to a
  tail call unless the call is kept non-tail).
- **Linear and affine.** Owned values are already consumed exactly once on
  every path of the checked Own program; a linear source annotation adds no
  run-time effect of its own and needs no separate verification at this layer.
- **Erased.** Re-checked by the relevance checker, as today.

A contract the checker cannot verify is refused with a diagnostic that names
it (whether an internal contract may instead be dropped, compiling as if
unannotated, is an [open question](#open-questions)). With this layer, the
confirmed hole and the erasure and transport disagreements above can only cause
refusals, never unsound code.

### Layer 2: a source-level resource theorem

If the annotations are to mean something at the source level, and in
particular on the route that runs the evaluator in a proof system, which has no
ownership level below SrcEval, the meaning is this theorem. It is operational
and separate from the kernel-model grounding.

**The instrumented evaluator.** SrcEvalᴿ is SrcEval
([`Src/Semantics.lean`](../IxCC/Src/Semantics.lean)) with:
- a heap whose cells carry a reference count;
- on every environment entry, its binder's contract and a use counter;
- a stack of regions, one per checked scope (a call, a local `let`, a borrow
  `let`), with every cell tagged by the region it is confined to;
- the set of active loans per cell.

SrcEvalᴿ must refine SrcEval: the same values, and the instrumentation never
blocks a run that SrcEval completes.

**The checker.** A resource checker on the Src program IxCC actually evaluates
(after the unfolding table and relevance), written in the recheck path's
kernel-evaluable style. Checking the evaluated program removes the
transport problem: equation, `csimp` and `inline` entries are checked where
they are compiled, and `0` means exactly what SrcEval erases.

**The theorem.** For a program the checker accepts, every root and every
input meeting the root's contracts (unique inputs in fresh cells, local inputs
in the caller's region), every run of SrcEvalᴿ satisfies:
1. *Erased.* No value bound at an erased binder is read; equivalently, the
   result is unchanged when every erased argument is replaced by □. IxCC's
   relevance soundness already has this shape.
2. *Linear and affine.* When the scope of a linear (affine) binding ends on a
   terminating path, its use counter is exactly (at most) one, a closure's
   captures counted once per invocation.
3. *Unique.* Whenever a value is consumed in a unique position, its cell's
   reference count is one (the single-pointer property).
4. *Local.* When a region is popped, no cell tagged with it is reachable from
   the result or from any older region.
5. *Borrow.* A view is unreachable after its scope, and its owner is not
   moved while the loan is active.

**The proof** needs a typing invariant for the checker (subject reduction and
a substitution lemma) and Atkey's conditions on the usage algebra: it must be
a positive semiring with the zero-product property, which ix's
`{0, 1, &, many}` is, and usages on the typing judgement itself restricted to
`{0, 1}`. Types are formed and compared consuming nothing, as in ix's checker
today.

**The first fragment.** First-order code: no resource captured in a
closure; annotated variables used in types only at `0`; no eliminator applied
to an annotated value; recursion only through unannotated parameters. It
widens in this order:
- closures, which after P8 are constructor cells, so the closure discipline
  (a closure capturing a unique value is one-shot; one capturing a local value
  is local) becomes a field discipline;
- eliminators: a `case` rule that joins the branches' demands and splits
  availability per field, where the published difficulties lie (linear
  addition through a natural-number recursor; linearity under `case` blocks);
- recursion through equation theorems, which the checker sees as ordinary
  calls on the evaluated program;
- locality with regions and tail calls, before any stack allocation relies
  on it.

## Contracts must be part of a type's identity

A source-level statement survives conversion only if every type equality the
checker relies on preserves contracts: either the checker checks the equality
itself, or it comes from a conversion that compares *all* contracts. IxCK
compares input contracts but not result contracts, which is what the
confirmed hole exploits. Making result contracts part of type identity needs a
result contract on λ nodes, or checking λs against their expected ∀ instead
of inferring a default result; the alternative is to forbid non-default result
contracts wherever conversion can see them. This is a decision for the
kernel's owners, in IxCK and in the IxVM kernel alike, not IxCC work. Layer 1
does not depend on it: it verifies contracts on IxCC's own representation,
where no conversion applies.

## What each back end gets

- **The native route (x86).** In-place update and freeing for verified unique
  values; elided reference counting for borrowed and verified unique values;
  stack or region allocation for verified local values, once measured;
  one-shot closure cells reused without a test. All of it only where Layer 1
  verified the contract. The native route's memory safety rests on Layer 1 and
  the back ends' existing proofs, not on Layer 2 or on the source check.
- **The evaluator route (Aiur, fixed evaluator).** It runs SrcEval over
  write-once memory: there is no in-place update, no freeing and no stack, so
  uniqueness, locality and borrows have nothing to optimise; erased positions
  are already never evaluated. Annotations there are statements about the
  program, not optimisations, and their soundness rests on Layer 2 alone: a
  claim that a function consumes its argument once, or returns an unaliased
  value, means something on that route only if Layer 2 proves it.
- **The per-program route (Aiur, later).** Below Fir, write-once memory as
  well; as the evaluator route.

## Prior art

- C. McBride, "I Got Plenty o' Nuttin'" (2016): usages from a semiring on
  context entries, `0` for variables used only in types.
- R. Atkey, "Syntax and Semantics of Quantitative Type Theory" (LICS 2018):
  usages on the judgement restricted to `{0, 1}` because arbitrary ones break
  substitution; types formed and compared in the erased context; a positive
  semiring with the zero-product property.
- E. Brady, "Idris 2: Quantitative Type Theory in Practice" (ECOOP 2021), and
  Idris 2's multiplicity-subtyping bug, in which an equality of function types
  proved by reflexivity turned an unrestricted function into a linear one; it
  was fixed by making multiplicities part of a function type's identity. The
  result-contract hole here is the same kind of problem.
- P. Choudhury, H. Eades, R. Eisenberg, S. Weirich, "A Graded Dependent Type
  System with a Usage-Aware Semantics" (POPL 2021): soundness against a
  heap-based operational semantics in which lookup decrements an allowed usage,
  with non-interference of irrelevant resources and a single-pointer property.
  Layer 2 has this shape.
- D. Marshall, M. Vollmer, D. Orchard, "Linearity and Uniqueness: An Entente
  Cordiale" (ESOP 2022): linearity restricts the future, uniqueness guarantees
  the past; in-place update needs uniqueness. ix has both, as `1`/`&` and `!`.
- B. Moon, H. Eades, D. Orchard, "Graded Modal Dependent Type Theory" (ESOP
  2021): grades for computational and type-level uses, tracked separately.
- A. Abel, N. A. Danielsson, O. Eriksson, "A Graded Modal Dependent Type
  Theory with a Universe and Erasure, Formalized" (ICFP 2023): conditions under
  which erasure is sound (no erased matches on weak Σ-types, consistency), and
  the difficulty of linearity through a natural-number recursor.
- J.-P. Bernardy, M. Boespflug, R. Newton, S. Peyton Jones, A. Spiwack,
  "Linear Haskell" (POPL 2018): multiplicities on arrows, no subtyping between
  linear and unrestricted arrows.
- A. Lorenzen, L. White, S. Dolan, R. Eisenberg, S. Lindley, "Oxidizing OCaml
  with Modal Memory Management" (ICFP 2024): locality and uniqueness modes on
  argument and result positions; a closure capturing a unique value is
  one-shot and one capturing a local value is local; a tail call ends the
  caller's region, so local values are not passed to tail calls.

## Milestones

Sizes are estimates, with their basis.

| Id | Content | Depends on | Exit test | Size [estimate] | State |
| --- | --- | --- | --- | --- | --- |
| RE-0 | Close the result-contract relabelling hole in the resource checker | — | the three relabelling programs (local escape, shared returned as unique, a one-shot closure duplicated) are refused, as regression tests | small (checker side) | In progress, owned with the resource checker |
| RE-1 | Layer 1: the ownership checker verifies written unique and borrow contracts at both ends; in-place update only on verified uniqueness; erased re-checked as today | Phase 2's ownership checker (DR1) | the relabelling programs, compiled with the hole re-opened, get no in-place update; K2 and K3 annotated twins verified; a unique contract the checker cannot verify is refused with its name | 2–4k lines beyond the Own checker itself (by comparison with the plain-RC contract check, `checkContractPlainMap`) | Planned (Phase 2) |
| RE-2 | Layer 2, first fragment: SrcEvalᴿ, its refinement of SrcEval, a resource checker on Src, the five properties | EV-1 (the frozen evaluator contract that SrcEvalᴿ instruments) | the refinement and the five properties fenced; the checker accepts the first-order programs of the ownership suite that ix's checker accepts, and its verdicts are compared with ix's on the rest | 8–20k lines: SrcEvalᴿ 1–2k (SrcEval is 0.4k), the checker 2–4k (the relevance checker is 0.9k), the proofs 5–14k (erasure's simulation over the same evaluator is 10.1k) | Planned |
| RE-3 | Widening: closures as cells, eliminators, recursion through equations, locality with tail calls | RE-2; P8 for closures | per item | per item | Planned |

RE-1 and RE-2 are independent: the native route needs RE-1, the evaluator
route's annotations need RE-2. Neither depends on the spine's adequacy work;
RE-2 shares its object, the Src program actually evaluated, with the spine.

## Open questions

1. **Refuse or drop** (DO-25 in the [roadmap](roadmap.md#open-decisions)). When Layer 1 cannot verify a contract on an internal
   function, refuse the program (D16's reading, the default) or compile as if
   the contract were absent?
2. **The erasure boundary** (DO-26). IxCC decides relevance from the binder contract of
   the head's type at every application (and its relevance checker's rule is
   extended accordingly), or ix's checker grades an argument erased only where
   IxCC erases it. The default is the first: erasing more evaluates less, and
   the kernel already forces a λ reaching an erased variable to have an erased
   binder.
3. **Proofs in the source check.** ix's checker grades proof positions erased,
   with the same level-exact classification IxCC uses, so that the two agree;
   a change to that checker, for its owners.
4. **Result contracts in type identity** (DO-24). Compare them in conversion, or forbid
   non-default result contracts where conversion can see them: for the
   kernel's owners, in both kernels.
5. **When Layer 2 is needed** (DO-27). Before the evaluator route's claims mention
   annotations at all, or only when a consumer asks for a resource statement.
6. **One checker or two.** Whether ix's source check is eventually replaced by
   IxCC's certified checker on Src, or both are kept with agreement tests.
