# Higher-order code: closed-world defunctionalisation

Written 2026-11-09. **Status: planned (Phase 2).** Only the lines marked
*implemented* describe code that exists; everything else is design. The
[roadmap](roadmap.md) owns scheduling and exit criteria; the
[compiler design](compiler-design.md) owns the pipeline contracts and the
[pass identifiers](compiler-design.md#pass-identifiers) used here.

**Decision.** IxCC compiles higher-order code in stages: P3 inlining and P4
specialisation remove what they can (implemented); P8 *closed-world
defunctionalisation* turns every remaining λ into a constructor and every
unknown call into a call of a generated dispatcher (planned); P9 narrows
dispatch with untrusted flow facts (planned). Closure objects with code
pointers, `pap` and `apply`, which Lean's own IR uses, are not planned. They
are the fallback if one of the conditions under
[Fallback](#fallback-code-pointer-closures) is met. This settles the earlier
inconsistency: code comments name P8, while `compiler-design.md` described
Fir with closure objects. Fir stays first order.

## Motivation

Every target beyond K1 needs higher-order code that specialisation cannot
always remove.
- **The certified kernel (IxCK).** Its core is a record of six closures,
  `CoreFns` (`IxCK/Kernel/Core.lean:288`), rebuilt per fuel level by
  `coreKnot` (`:2120`), which closes over itself. The code is polymorphic in
  the monad (`[Monad m] [MonadExcept …]`) and runs at two monads.
  `Std.HashMap` takes `BEq` and `Hashable` dictionaries.
- **The IxOS monitor** is ordinary Lean library code (`List`, `Array`,
  `Except`, `StateT`), with the same dictionaries and monad stacks.
- **General programs.** `Decline.composeClosure`
  ([`Decline.lean:20-26`](../fixtures/corpus/phase1-decline/src/Decline.lean))
  builds a closure that grows on every iteration; no specialisation can
  remove it. Folds, `for` loops over monad transformers and callbacks are
  common in K2–K4 sources.

## Current state

- *Implemented.* P3 bounded inlining ([`Anf/Inline.lean`](../IxCC/Anf/Inline.lean),
  [`Anf/Walk.lean`](../IxCC/Anf/Walk.lean)) and P4 bounded specialisation
  ([`Anf/Specialize.lean`](../IxCC/Anf/Specialize.lean)). A certificate step
  may hold at most 64 specialisation decisions with masks of at most 64
  parameters ([`Recheck/Run.lean:173`](../IxCC/Recheck/Run.lean)), within the
  [middle-end budgets](compiler-design.md#middle-end-budgets). These passes
  remove the instance dictionaries of `fib` and the `forIn`/`Monad Id`
  closures of `sum-loop`.
- *Implemented.* The keys P8 needs: closure constructors `CtorKey.clo`,
  lifted λs `GKey.lam` and dispatchers `GKey.dispatch`
  ([`Key.lean:31-54`](../IxCC/Key.lean)), and the predicate
  `Anf.FirstOrder` ([`Anf/WellFormed.lean:262`](../IxCC/Anf/WellFormed.lean)).
- *Implemented.* Anf → Fir declines any program that still has a local
  function (`fn`), an unknown call (`app`) or a function-valued global
  ([`Fir/Lower.lean:246`, `:274-275`, `:343`](../IxCC/Fir/Lower.lean)), with
  `fir.closures: declined until P8 …` (`:68`). Fir's syntax
  ([`Fir/Syntax.lean`](../IxCC/Fir/Syntax.lean)) has known calls only.
  `Decline.applyArg` and `Decline.composeClosure` are recorded as
  `fir: fir.closures` in the decline corpus
  ([`corpus.json`](../fixtures/corpus/phase1-decline/corpus.json)).
- No P8 or P9 code exists.

## Options

| | A. Closure conversion | B. Closed-world defunctionalisation | C. Staged: P3/P4, then B, then P9 |
| --- | --- | --- | --- |
| Representation | A cell with a code pointer, arity and captures; `pap` for partial application, `apply` procedures for unknown calls (Lean IR's `Expr.pap`/`Expr.ap` and its runtime `lean_apply_*`; CakeML, CertiCoq, OCaml) | A constructor per λ and number of supplied arguments, captures as fields; one generated `dispatch m` global per call arity, a `case` over every closure key (Reynolds; GRIN; MLton's flow-directed variant) | B for whatever specialisation leaves; P9 replaces a dispatch site by a short `case` when flow facts name few keys |
| Completeness | Always | Needs a closed world: holds, see below | As B |
| Certificate | None: deterministic | None for P8: deterministic, re-run by `Recheck.run`; P9 reads facts that are correct for any value | As B |
| Ownership and RC | New object kind; `pap` and three `apply` variants (owned, borrowed, unique) in Own; runtime apply procedures | Closures are constructor cells: dup/drop, the plain-RC checker, release and later reuse apply unchanged | As B |
| Backend and Ring 0 | Needs `call r/m64` with a code-pointer validity premise, and a new control-flow argument for Ring 0 | Every call stays direct | As B |
| Separate compilation | Supported | Whole program only | As B, with A possible later at a boundary |
| Cost at a megamorphic site | One indirect call | A compare tree over keys | P9 narrows it; P4 removes most sites first |

**Why B (inside C) fits IxCC.**
1. **The world is closed.** The compiler's input is an address-closed Ixon
   closure, and compile-claim roots take only `Nat` parameters
   (`rootParamsAllNat`, [`CompileClaim.lean:284`](../IxCC/CompileClaim.lean)).
   Every closure a run can build therefore comes from a λ or a function
   global of the program, so a dispatcher over every closure key of an arity
   is complete without any analysis.
2. **No indirect calls.** The Ring-0 admission argument relies on the
   instruction table having no indirect branch rows (header of
   [`Ring0.lean`](../IxCC/Ring0.lean)). B keeps that property; A breaks it.
3. **RC sees only data.** A closure cell is an ordinary constructor cell, so
   no ownership rule, runtime procedure or heap-invariant clause is added.
   The bounded plain-RC route already handles constructor cells.
4. **The proof fits the existing framework.** The implemented Anf relation
   is structural rather than step-indexed: it relates literals, □ and
   constructors structurally and every closure to the same code under
   related environments ([`Anf/Proof/Rel/Basic.lean`](../IxCC/Anf/Proof/Rel/Basic.lean)).
   P8's relation is structural too (below), and the pass needs one
   dispatcher lemma.
5. **Specialisation first.** Lean's own compiler specialises
   instance-taking and higher-order functions before closure conversion
   (`@[specialize]`); P4 is the same idea and already runs. P8 handles what
   is left, so its cost lands only where specialisation fails.

**Costs of B.** Whole-program compilation only. Every λ of a given arity
joins the dispatcher's strongly connected component, which coarsens the
call graph that per-SCC analyses see. A site with many keys pays a compare
tree. Closure keys share the constructor tag space (at most
`Rt.maxTag = 0x7EFF` tags, [`Rt/Layout.lean:49`](../IxCC/Rt/Layout.lean)).
None of these has been measured; K4 and K6 rows decide whether P9 or a
jump table is needed.

## Design (planned)

### Position in the pipeline

Today's schedule ([`Anf/Pipeline.lean:9-22`](../IxCC/Anf/Pipeline.lean)) is
`P1 → P2 → prune → (P3 → P2)* → P4 → P2 → (P3 → P2)* → prune`. P8 is appended
after the last prune, then a shrink round, P9, and inlining of the
dispatcher arms P9 creates:

```text
… → prune → P8 → P2 → P9 → (P3 → P2)* → prune → Fir.lower
```

`Fir.lower` is unchanged: P8's output is `Anf.FirstOrder`, which is what
`Fir.lower` already accepts.

### The translation

| Anf | After P8 |
| --- | --- |
| `fn ps b` in global `g` at path `π`, with free variables `xs` in de Bruijn order | a new global `ℓ := GKey.lam (key g) π` with parameters `xs ++ ps` and body `b` (renamed); the binding becomes `con (clo ℓ 0) xs` |
| `glob h`, `h` a function global | `con (clo h 0) []`, field-less, hence an immediate below Own |
| `glob h`, `h` a CAF | unchanged (a zero-argument call) |
| `app f as` | `call (dispatch as.length) (f :: as)` |
| every other form | unchanged |

P8 adds one constructor-table entry per closure key `clo ℓ j`
(`0 ≤ j < n_ℓ`, where `n_ℓ` counts ℓ's non-capture parameters), with field
count `|xs| + j`, so `CtorInfo.ofKey` resolves it like a source constructor.

### Dispatchers

For each arity `m` that occurs, the global `dispatch m` takes the callee and
`m` arguments and cases on the callee's key. With `fs` the closure's fields,
the alternative for `clo ℓ j`:
- `j + m = n_ℓ` (saturated): tail call `ℓ (fs ++ as)`;
- `j + m < n_ℓ` (partial application): return `con (clo ℓ (j + m)) (fs ++ as)`;
- `j + m > n_ℓ` (over-application): `r := call ℓ (fs ++ as[:n_ℓ − j])`, then
  tail call `dispatch (m − (n_ℓ − j)) (r :: as[n_ℓ − j:])`.

This is Anf's `applyN` ([`Anf/Semantics.lean`](../IxCC/Anf/Semantics.lean))
written as code. Applying a literal, a data constructor or □ matches no
alternative and is stuck, exactly as `applyN` and SrcEval are stuck there;
a stuck source imposes nothing on the target.

### Erased arguments and by-name positions

Erasure keeps every binder slot and passes □ for irrelevant arguments
([Relevance and erasure](compiler-design.md#relevance-and-erasure)), so a
λ's arity counts its irrelevant parameters, and dispatchers pass □ like any
operand. A later dead-parameter pass (P5) may drop □ slots at known call
sites through a worker/wrapper split; dispatchers call the wrapper, so their
signatures keep the source arity. By-name arguments of `lazy` constants are
thunks of one □ parameter; P3 and P2 already remove those of `ite`, `dite`
and the Boolean connectives, and any survivor is an ordinary closure key.

### The workloads

- **Type-class dictionaries.** After erasure an instance is a CAF whose
  value is a constructor of methods. P3 inlines the CAF, P2 resolves the
  projection, and the method becomes a known call (implemented, K1). A
  dictionary passed as a parameter into a recursive polymorphic function is
  removed by P4. A dictionary stored in data or passed through an
  unspecialised recursion is, after P8, a constructor of closure
  constructors, and each method call is one dispatch.
- **Monad-polymorphic code.** P4 specialises on the `Monad` dictionary, a
  closed constructor tree, after which `bind`'s continuation is a local λ
  that P3 and β remove when `bind` is inlined. Continuations that survive
  (recursive `bind` chains, `StateT` over `Except` in a loop) become closure
  keys.
- **Records of closures.** `CoreFns`' six fields each become a closure key
  whose captures are `coreKnot`'s arguments. A call `r.whnf d e` is a
  projection followed by `dispatch 2`. Because the record is rebuilt per
  fuel level, the cells are short-lived, and reuse (Phase 2 ownership)
  matters for speed, not correctness.

### Known calls after P8

One shrink rule: `call (dispatch m) (g :: as)`, with `g := con (clo ℓ j) xs`
in scope, rewrites to that dispatcher alternative plus a `tick`. Together
with dead-`con` removal, a closure built and called locally becomes a
direct call of ℓ and allocates nothing. P4 can also specialise a
higher-order global on a closure constructor argument, since its masked
arguments are already constructor trees.

### P9 and the flow oracle

`Flow.analyse` (untrusted, run by `produce`) abstracts the program's
constructor values and reports, per dispatch site, which closure keys can
reach it. P9 rewrites a site with at most `D` keys (default 4) to a `case`
with those alternatives and the full dispatcher as the default arm. P9 is
correct for any facts, so the facts are certificate data and no flow
checker is needed; a wrong fact costs speed only.

### Ownership, runtime and backend

- A closure cell is a constructor cell: captures are scanned fields, and a
  field-less closure key is an immediate `2·tag + 1`.
- The bounded plain-RC route admits at most 31 scanned fields
  ([`Cfg/Rc/Native.lean:62`, `:81`](../IxCC/Cfg/Rc/Native.lean)). A λ with
  more captures is declined there until general layouts land
  ([data design](data-and-roots-design.md#d1-heap-completion)).
- Dispatchers take every parameter owned. Borrowed callees come from borrow
  inference on the dispatcher's callee parameter, and one-shot closures from
  a unique cell consumed by a unique clone of the dispatcher; both belong to
  the general ownership work of Phase 2, not to P8.
- A dispatcher is a `case` on a constructor key, which Cfg turns into a
  `switch` and `Rt.lower` into a compare chain on the header tag (the
  "Switch" paragraph of [`Rt/Lower.lean`](../IxCC/Rt/Lower.lean)). A jump
  table would need an indirect jump row; it is not planned.
- Clocks: a dispatch is one charged call, so the target charges at least as
  often as the source and the timeout clause holds as it does for inlining.

## Proof obligation

- **Theorem (planned): `Anf.Defun.correct`.** For a well-scoped Anf program
  `p` with `Anf.defun p = .ok q`: `q` is well scoped, `Anf.FirstOrder q`, and
  `q` simulates `p` in the shape of the existing Anf passes (the pass
  relation of [`Anf/Proof/Pass`](../IxCC/Anf/Proof/Pass/Basic.lean), with the
  value relation below), relative to Anf's semantics
  ([`Anf/Semantics.lean`](../IxCC/Anf/Semantics.lean)).
- **Value relation, structural.** Literals and □ relate to themselves,
  constructors pointwise, and a closure `clos ρ n b got` relates to
  `con (clo ℓ j) ws` when ℓ is a global of `q` whose body is P8's image of
  `b` over parameters `xs ++ ps`, `j = got.length`, and `ws` relates
  pointwise to the values of `xs` in `ρ` followed by `got`. No step index is
  needed, matching the implemented relation.
- **Dispatcher lemma.** Applying related values (`AppSim` in
  [`Anf/Proof/Rel/Basic.lean`](../IxCC/Anf/Proof/Rel/Basic.lean)) to a
  closure on the source side and through `dispatch m` on the target side
  gives related computations, by induction on the clock and on `n_ℓ − j`.
  The other constructs reuse the existing compatibility lemmas.
- **Composition.** P8 is one more step of the middle end, so it composes
  into `Anf.Pipeline.run_correct`
  ([`Anf/Proof/Pass/Pipeline.lean:166`](../IxCC/Anf/Proof/Pass/Pipeline.lean)).
  Its output satisfies `Fir.lower`'s precondition, so `Fir.convert_correct`
  ([`Fir/Proof/Correct.lean:171`](../IxCC/Fir/Proof/Correct.lean)) is
  unchanged. Roots take and return first-order values, where the relation is
  equality, so `Recheck.sound`, `Recheck.RcReplay.sound` and the compile-claim
  theorems keep their statements: still relative to SrcEval, still with the
  `GoesWrong` disjunct.
- **P9** is proved for every fact; the shrink rule is one rewrite lemma
  proved by unfolding the dispatcher.

## Trusted base

Unchanged: no runtime procedure, no x86 row, no ledger entry and no axiom.
The flow oracle is untrusted.

## Dependencies

- Needs: constructor cells under the selected memory policy (implemented:
  immortal cells, and the bounded plain-RC route up to 31 fields).
- Interacts with: P4's caps and the middle-end budgets, which count lifted
  globals and dispatchers; Phase 2 ownership for borrowed and one-shot
  closures.
- Enables: library code over dictionaries (`HashMap`, `Array.foldl`),
  monad transformers, and both [flagship targets](roadmap.md#flagship-targets).

## Size [estimate]

- P8, dispatcher generation and the table extension: about 1k lines of
  code. Proof: 4–8k lines. Basis: the estimate in the pre-merge design notes
  (untracked; see below), against IxCC's own Anf → Fir lowering (3.8k lines
  for `Fir/` with its proofs) and CertiCoq's closure conversion as surveyed
  there (about 0.5k lines of code and 9k of proof).
- The shrink rule: 0.1k + 0.3k. P9: 0.3k + 0.5–1k. Flow oracle: 1.5–2.5k,
  untrusted, no proof.
- Stop rule: if P8's proof passes about 9k lines, re-evaluate option A,
  which is the same class of proof.

## Exit criteria

1. `Decline.composeClosure` compiles at every level and natively and is
   certified; it moves from the decline corpus to a compiled family with its
   Lean-interpreter cases.
2. New corpus roots compile and certify both with P4 disabled (forcing P8)
   and enabled, with equal results: a dictionary-passing polymorphic
   recursion, a `StateT`-over-`Except` loop, partial and over-application
   through a stored closure, and a small fuel-indexed record-of-closures knot
   in the shape of `coreKnot`.
3. Every K2/K3 program whose frozen closure still has residual closures
   after P4 compiles (the census on the frozen closures decides which).
4. `fir.closures` is unreachable from a well-scoped Anf program; the
   remaining declines are specific (too many captures, tag space).

## Fallback: code-pointer closures

Option A becomes worth building only if one of these happens:
- P8's proof passes the stop rule above;
- a K4 or K6 row misses its target because of dispatch, after P9;
- separately compiled higher-order libraries, or closures crossing a
  program boundary (for example a SIP receiving a closure from the IxOS
  monitor), become requirements.

The third is the owner's call (see [roadmap decisions](roadmap.md#open-decisions)).
The default here is no: SIP boundaries pass first-order data, and libraries
that take closures are compiled into each program. Adding A later at a
boundary only, with dispatchers kept for internal calls, would cost a new
object kind, a `call r/m64` row with a target-validity premise, an extended
Ring-0 control-flow argument, and an estimated 6–9k proof lines (same
basis as above).

## Provenance and prior art

This design is the D19 decision of the pre-merge Compilatr.ix plans: design
note `02-erasure-middle.md` §8 (pass list, P8, P9), note `06-cross-check.md`
seam S45 and the research note `research/grin-ir.md` §5.3. Those notes are
untracked files under `plans/x86-v2/` of the pre-merge workspace and are not
in this repository; code comments that cite "02 §8", "03 §2.2" or "06 S45"
refer to them. Prior art they rely on:
- Reynolds' defunctionalisation, with Nielsen's paper proof of an
  analysis-free version for a simply typed call-by-value language (BRICS
  RS-00-47);
- GRIN (Boquist), which generates `apply` per program;
- MLton's flow-directed closure conversion into datatypes (Cejtin,
  Jagannathan and Weeks, ESOP 2000);
- closure conversion in Lean 4's IR, CakeML (`clos_known` for known calls)
  and CertiCoq.

No mechanised proof of whole-program defunctionalisation was found in that
survey; P8's proof is new work.
