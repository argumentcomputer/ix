# Higher-order code: closed-world defunctionalisation

Written 2026-11-09. **Status: in progress (Phase 2).** Started on 2026-11-10
at the owner's request, for the native route's generality. P8 is on the
compile and recheck path, as the middle end's closures step, and proved: its
correctness theorem composes into the end-to-end theorems (see [Current
state](#current-state); the decisions of 2026-11-13 and 2026-11-14 on root
arity are under [Proof obligation](#proof-obligation)). The known-dispatch
rule and P9 are not implemented. Only the lines marked *implemented* describe
code that exists; everything else is design.

**Place in the plan.** P8 is below SrcEval, so it adds nothing to the
[spine](end-to-end.md#the-shared-spine)'s obligations, and the Aiur evaluator
route does not need it: the evaluator has closures natively. It serves the x86
route, where Fir must be first order. The
[roadmap](roadmap.md) owns scheduling and exit criteria; the
[compiler design](compiler-design.md) owns the pipeline contracts and the
[pass identifiers](compiler-design.md#pass-identifiers) used here.

**Decision.** IxCC compiles higher-order code in stages: P3 inlining and P4
specialisation remove what they can (implemented); P8 *closed-world
defunctionalisation* turns every remaining λ into a constructor and every
unknown call into a call of a generated dispatcher (implemented); P9 narrows
dispatch with untrusted flow facts (planned). Closure objects with code
pointers, `pap` and `apply`, which Lean's own IR uses, are ruled out: they
need indirect calls, which compiled code does not contain (decision D20 of
2026-11-10, [Design decisions](compiler-design.md#design-decisions)), and no
closure crosses a program boundary (decision 1 of 2026-11-10 in the
[roadmap](roadmap.md#decisions-of-2026-11-10)). Fir stays first order.

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
  lifted λs `GKey.lam`, dispatchers `GKey.dispatch` and the roots' entries
  `GKey.entry` ([`Key.lean`](../IxCC/Key.lean)), and the predicate
  `Anf.FirstOrder` ([`Anf/WellFormed.lean:262`](../IxCC/Anf/WellFormed.lean)).
- *Implemented.* Anf → Fir refuses any program that still has a local
  function (`fn`), an unknown call (`app`) or a function-valued global
  ([`Fir/Lower.lean`](../IxCC/Fir/Lower.lean), `fir.closures`), and accepts
  only first-order programs (`Fir.Proof.lower_ok_firstOrder`). Fir's syntax
  ([`Fir/Syntax.lean`](../IxCC/Fir/Syntax.lean)) has known calls only. After
  the closures step below the refusal is unreachable
  (`Anf.Pipeline.Proof.closures_lower_ne_closures`).
- *Implemented, on the compile and recheck path: the closures step*
  ([`Anf/Pipeline/Closures.lean`](../IxCC/Anf/Pipeline/Closures.lean)), the
  middle end's last step, after the certificate's steps (`Anf.Pipeline.run`)
  and before `Fir.lower`, on both paths: the producers run it after
  `Anf.Pipeline.produce` (`Recheck.produceClosures`), and every replay of the
  middle end runs it (`Recheck.anfOf`, in
  [`Recheck/Run.lean`](../IxCC/Recheck/Run.lean)). It reads the source roots'
  declared parameter counts (`Recheck.declaredCounts`) and no certificate
  data, so the certificate format is unchanged. A program that is first order
  and whose roots take their declared counts passes unchanged (`plain`), so
  what compiled before the step was added compiles to the same bytes and P8's
  input checks cannot refuse it. Otherwise each root whose Anf parameter count
  is not its declared count gets an entry at the declared count
  ([`Anf/Entry.lean`](../IxCC/Anf/Entry.lean), key `GKey.entry`: the root's
  value applied to the entry's parameters), then P8 runs, then the middle
  end's size check.
- *Implemented.* The pass `Anf.defun`
  ([`Anf/Defun.lean`](../IxCC/Anf/Defun.lean), with the walk in
  [`Anf/Defun/Lift.lean`](../IxCC/Anf/Defun/Lift.lean) and the dispatchers in
  [`Anf/Defun/Dispatch.lean`](../IxCC/Anf/Defun/Dispatch.lean)), as designed
  below. Proved: its output is `Anf.FirstOrder`
  (`Anf.Defun.Proof.run_firstOrder`), `Fir.lower` declines no first-order
  program for closures (`Fir.Proof.lower_firstOrder`), and a lifted body is
  well scoped over its captures and parameters (`Anf.Defun.Proof.lifted_ws`);
  the value relation is defined
  ([`Anf/Proof/Defun/Rel.lean`](../IxCC/Anf/Proof/Defun/Rel.lean)); the
  dispatchers compute `applyN`, with their charges, on a cell whose key no
  earlier source has (`dispatch_exact`, `dispatch_under`, `dispatch_over` in
  [`Anf/Proof/Defun/Dispatch.lean`](../IxCC/Anf/Proof/Defun/Dispatch.lean));
  P8 keeps the roots and every input global's parameters
  (`Anf.Defun.Proof.run_roots`, `run_arity`); its key check is sound: passing
  it, the keys of the globals whose closures the program builds are pairwise
  distinct (`checkSources_ownerKeys`), and it is linear: each key is filed in
  a trie under a prefix-free code of the key and compared only with the keys
  filed there (`Defun.firstEqualKeysT`), finding the same pair as the
  bucketed specification (`firstEqualKeysT_eq`). Every closure source of a
  successful run has its own key (`sources_keys`), so the dispatcher lemmas
  hold of P8's own output with no further hypothesis (`run_dispatch_exact`,
  `run_dispatch_under`, `run_dispatch_over`, in
  [`Anf/Proof/Defun/Assemble.lean`](../IxCC/Anf/Proof/Defun/Assemble.lean)).
  The walk is the translation relation `Tr`: a successful run fixes a valid
  setting, with the input's globals at their ids with translated bodies, the
  dispatchers at their ids and distinct source keys (`ran_valid`, `run_valid`,
  in [`Anf/Proof/Defun/Translate.lean`](../IxCC/Anf/Proof/Defun/Translate.lean));
  the output is well scoped when the input is and its globals lie below its
  size (`wellScoped_run`, in
  [`Anf/Proof/Defun/WellScoped.lean`](../IxCC/Anf/Proof/Defun/WellScoped.lean));
  renaming free variables is exact on code without local functions, which is
  what lets a lifted body over its captures evaluate as the walk's image over
  the environment they came from (`eval_rename`, `capRen_env`, in
  [`Anf/Proof/Defun/Rename.lean`](../IxCC/Anf/Proof/Defun/Rename.lean)). The
  valid setting needs of the input only that its globals lie below its size:
  the walk itself refuses the out-of-scope captures and parameterless local
  functions the translation relation excludes. The dispatchers' switch work
  (`Defun.dispatchWork`: dispatchers times the square of the closure keys
  times the constructor table's length) is refused past `Anf.maxBackWork`
  before anything is built (`defun.budget`); a dispatcher cannot be split,
  since a switch has no default arm. The fundamental lemma holds at every
  clock bound (`Anf.Defun.Proof.fund`, in
  [`Anf/Proof/Defun/Fund.lean`](../IxCC/Anf/Proof/Defun/Fund.lean)), with
  the dispatcher simulation (`dispatch_sim`: applying related values in the
  source is calling the dispatcher of the arguments' arity in the target, a
  saturated call one charge deeper, by `SimUpTo.laterR`) and the call
  simulation (`call_sim`); environments are related pointwise and of at least
  the static depth, and a local function's closure relates to its cell over
  its whole related target environment. **P8 is correct**
  (`Anf.Defun.Proof.correct`, in
  [`Anf/Proof/Defun/Correct.lean`](../IxCC/Anf/Proof/Defun/Correct.lean)):
  for an input whose globals lie below its size, the output is first order
  and refines the input on every input of exactly the root's arity
  (`run_refines`); that the output is well scoped when the input is, which no
  later step needs, is the separate `wellScoped_run`. As a step, a program
  with ids exactly `0 … size - 1` gives one again (`step_correct`, `run_wf`),
  and followed by `Fir.lower` the Fir program refines P8's input on those
  inputs (`defun_lower_refines`). No P9 code exists.
- *Implemented: the step and its composition are proved.* The entries keep
  every global of their input at its id and refine it on every input of the
  declared count, on which every root of their output takes exactly the
  input's length (`Anf.Entry.Proof.run_refines`, `run_exactArity`, in
  [`Anf/Proof/Entry.lean`](../IxCC/Anf/Proof/Entry.lean)); so the step
  refines its input on those inputs and its output is first order
  (`Anf.Pipeline.Proof.closures_correct`, in
  [`Anf/Proof/Pass/Closures.lean`](../IxCC/Anf/Proof/Pass/Closures.lean)), and
  a program `Fir.lower` accepted, with its roots at their declared counts,
  passes it unchanged (`closures_of_lower`). The middle end with the step
  refines its Lam program on every covered input (`Recheck.anfOf_refines`, in
  [`Recheck/Proof/Middle.lean`](../IxCC/Recheck/Proof/Middle.lean)), and the
  end-to-end theorems hold on those inputs (see [Proof
  obligation](#proof-obligation)).
- *Tested.* Against the Anf evaluator (`tests-anf`) and end to end, natively,
  through the production compiler: `Decline.composeClosure` and the
  workloads of [Exit criteria](#exit-criteria) item 2 in the registered family
  [`phase2-closures`](../fixtures/corpus/phase2-closures/corpus.json)
  (`tests-corpus`: every level and natively); the K1 programs without
  equations and the same workloads with and without inlining and
  specialisation (`tests-pipeline --only defun`, which runs the compiler's
  stages under a chosen middle-end schedule with the closures step after
  it), and every workload certified both ways: `Recheck.compileInput` and a
  compile claim that `verifyProgram` and `verifyBytes` accept, under the
  production schedule and with specialisation and inlining disabled (where
  the step changes every workload), natively equal to Lean's values both
  ways. The `StateT`-over-`Except` loop with the library's `StateT.bind`
  (`Closures.stateLoop`) compiles and is certified since 2026-11-11: its
  dispatcher calls `StateT.bind`, of eight parameters, in tail position, past
  the seven arguments of a tail call, so `Fir.lower` makes that call a call
  and a return, a frame per iteration ([roadmap](roadmap.md), "Internal tail
  calls"; it was declined by allocation, `alloc.fallback`). The same loop in
  the same stack with the stack's `Monad` instance written for it
  (`Closures.stateLoopSE`, no function over seven parameters) compiles with
  proper tail calls and is
  certified. The roots of
  [`phase2-arity`](../fixtures/corpus/phase2-arity/corpus.json) (not
  registered), whose stored values have fewer or more leading λs than their
  declared types show, compile through their entries and agree with Lean.
- *Roots with a function parameter.* Closures do not cross a program
  boundary, so no caller of an object can pass a closure, and a root whose
  declared parameters include a function type has no meaningful caller.
  The compiler refuses such a root before it makes an object
  (`rt: rt.fnparam`, `Recheck.checkFnParams`): `ixcc compile` right after
  ingress, and every producer (`Recheck.produceClosures`), so every compile
  claim too. A parameter is refused when the relevance checker classifies it
  as relevant (not a type, type former or proof) and its declared domain,
  after unfolding definitions at its head, is a Π-type (`Nat → Nat`, or
  `NatFn := Nat → Nat`); not refused: `Nat`, `Bool` and other inductives,
  a structure with a function field, a type variable, type parameters and
  proofs (`Recheck/Declared.lean`, `fnParam?`). Every root refused this way
  is refused by the claims (`CompileClaim.rootParamsAllNat_of_fnParam`).
  `Decline.applyArg (f : Nat → Nat) (n : Nat)`, the one registered root of
  this kind, is refused; built without the check, the program builds no
  closure, so the dispatcher its call of `f` goes through has no
  alternative, and it traps when reached (status 4 natively), where the
  source is stuck too (on every input a caller can pass, it applies a
  number). With such a certificate the recheck path still builds the object
  (the check is the producer's), the executables' fragment refuses it
  (`Exe.fragment`, `exe.params`) and `verifyProgram` and `verifyBytes` reject a claim naming
  it (`CompileClaim.rootParamsAllNat` is false), so nothing certified is said
  of it. `tests-pipeline --only defun` asserts each.
- *Implemented: P8's own input checks.* The pipeline does not establish
  `Anf.WellScoped`, so the pass refuses (`defun.input`) what its correctness
  relies on and a well-scoped program never has: a global already keyed `lam`
  or `dispatch`, a closure key already in the constructor table, two globals
  whose closures the program builds with equal keys, a local function without
  parameters, a free variable of a local function out of scope, and the value
  of a global beyond the program's size; and a pinned constructor (`Nat`'s or
  `Bool`'s) keyed as a closure, which erasure never produces (it pins source
  constructors) and which would let the closure keys the pass adds change that
  constructor's arity. Besides the two declines of [Exit
  criteria](#exit-criteria) item 4, more captures than a cell holds and the tag space
  (`defun.captures`, `defun.tags`), it refuses nothing else but its budgets
  (`defun.budget`). P8's correctness needs of its input only that its globals
  lie below its size, which every middle-end step keeps (`Program.WF`); the
  checks above are what the walk and the proof rely on, so no lemma about
  well-scopedness of pipeline programs is needed.

## Options

| | A. Closure conversion | B. Closed-world defunctionalisation | C. Staged: P3/P4, then B, then P9 |
| --- | --- | --- | --- |
| Representation | A cell with a code pointer, arity and captures; `pap` for partial application, `apply` procedures for unknown calls (Lean IR's `Expr.pap`/`Expr.ap` and its runtime `lean_apply_*`; CakeML, CertiCoq, OCaml) | A constructor per λ and number of supplied arguments, captures as fields; one generated `dispatch m` global per call arity, a `case` over every closure key (Reynolds; GRIN; MLton's flow-directed variant) | B for whatever specialisation leaves; P9 replaces a dispatch site by a short `case` when flow facts name few keys |
| Completeness | Always | Needs a closed world: holds, see below | As B |
| Certificate | None: deterministic | None for P8: deterministic, re-run by `Recheck.run`; P9 reads facts that are correct for any value | As B |
| Ownership and RC | New object kind; `pap` and three `apply` variants (owned, borrowed, unique) in Own; runtime apply procedures | Closures are constructor cells: dup/drop, the plain-RC checker, release and later reuse apply unchanged | As B |
| Backend and Ring 0 | Needs `call r/m64` with a code-pointer validity premise, and a new control-flow argument for Ring 0 | Every call stays direct | As B |
| Separate compilation | Supported | Whole program only | As B |
| Cost at a megamorphic site | One indirect call | A compare tree over keys | P9 narrows it; P4 removes most sites first |

**Why B (inside C) fits IxCC.**
1. **The world is closed.** The compiler's input is an address-closed Ixon
   closure, and compile-claim roots take only `Nat` parameters
   (`rootParamsAllNat`, [`CompileClaim.lean:284`](../IxCC/CompileClaim.lean)).
   Every closure a run can build therefore comes from a λ or a function
   global of the program, so a dispatcher over every closure key of an arity
   is complete without any analysis.
2. **No indirect calls.** Compiled code contains no indirect call or jump
   (decision D20); the Ring-0 admission argument relies on the instruction
   table having no indirect branch rows (header of
   [`Ring0.lean`](../IxCC/Ring0.lean)). B keeps that property; A would break
   it, which rules A out.
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
None of these has been measured; K4 and K6 rows decide how much P9 and the
compare-tree layout matter.

## Design (planned)

### Position in the pipeline

The certificate's schedule ([`Anf/Pipeline.lean`](../IxCC/Anf/Pipeline.lean)) is
`P1 → P2 → prune → (P3 → P2)* → P4 → P2 → (P3 → P2)* → prune`. The closures
step follows it (*implemented*), outside the certificate's steps:

```text
… → prune → [ entries → P8 → size check ] → Fir.lower      (unchanged when plain)
```

`Fir.lower` is unchanged: P8's output is `Anf.FirstOrder`, which is what
`Fir.lower` already accepts. No shrink or prune follows P8 yet, and no P9.
A shrink after P8 would need certificate data (the rounds of each global,
P8's new globals among them), so P8 would have to become a certificate step
(a format change), and with today's rules it has nothing to do: a lifted body
was shrunk inside its parent, P8 adds only closure cells and dispatcher
calls, which no rule rewrites, and pruning finds nothing unreachable, since
the dispatchers reach every closure source. The shrink after P8 therefore
waits for the known-dispatch rule ([Known calls after P8](#known-calls-after-p8)),
with P9 and inlining of the dispatcher arms P9 creates:

```text
… → prune → P8 → P2 → P9 → (P3 → P2)* → prune → Fir.lower      (planned)
```

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
  ([data design](data-and-roots-design.md#dr1-heap-completion)).
- Dispatchers take every parameter owned. Borrowed callees come from borrow
  inference on the dispatcher's callee parameter, and one-shot closures from
  a unique cell consumed by a unique clone of the dispatcher; both belong to
  the general ownership work of Phase 2, not to P8.
- A dispatcher is a `case` on a constructor key, which Cfg turns into a
  `switch` and `Rt.lower` into a compare chain on the header tag (the
  "Switch" paragraph of [`Rt/Lower.lean`](../IxCC/Rt/Lower.lean)). A jump
  table would need an indirect jump row, which decision D20 excludes.
- Clocks: a dispatch is one charged call, so the target charges at least as
  often as the source and the timeout clause holds as it does for inlining.

## Proof obligation

- **Theorem (proved): `Anf.Defun.correct`.** For an Anf program `p` whose
  globals lie below its size with `Anf.defun p = .ok q`: `Anf.FirstOrder q`,
  and `q` refines `p` on every input of exactly the root's arity
  (`Sem.RefinesOn (ExactArity p)`, see the decision below), relative to
  Anf's semantics ([`Anf/Semantics.lean`](../IxCC/Anf/Semantics.lean)). The
  simulation is P8's own (its environments are related pointwise with a depth
  bound, and a closure relates to a cell), not an instance of the pass
  relation of [`Anf/Proof/Pass`](../IxCC/Anf/Proof/Pass/Basic.lean), whose
  value relation relates closures only to closures.
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
- **Composition (proved).** The closures step refines its input on every
  input of the declared count (`Anf.Pipeline.Proof.closures_correct`: the
  entries, `Anf.Entry.Proof.run_refines`, make such an input one of exactly
  each root's arity, `run_exactArity`, on which P8 refines), and its output
  satisfies `Fir.lower`'s precondition, so `Fir.convert_correct` is
  unchanged. Composed with the certificate's middle end
  (`Anf.Pipeline.Proof.run_correct`, every input) it gives
  `Recheck.anfOf_refines`: the middle end refines its Lam program on every
  *covered* input, `Recheck.Covered`: an input of exactly its source root's
  declared count (`Recheck.ExactDeclared`), or any input when the closures
  step left the certificate's program unchanged. Roots take and return
  first-order values, where the relation is equality, so `Recheck.sound`,
  `Recheck.RcReplay.sound`, `Recheck.compiled_sound` and the compile-claim
  theorems stay relative to SrcEval, with the `GoesWrong` disjunct, on every
  covered input (`Front.Covered`). For a program the step leaves unchanged,
  which is every program that compiled before the step was added with its
  roots at their declared counts (`Recheck.anfOf_of_lower`), every input is
  covered and they say what they said before (`Recheck.sound_unchanged`).
- **Decided 2026-11-13 and 2026-11-14: a root is called with exactly its
  declared number of parameters.** P8's refinement fails for an input that
  gives a root more arguments than it takes: Anf, Lam and SrcEval apply a
  root's result to further arguments; stage S has no typing theorem, so that
  result can be a closure, which the source applies and P8's output, holding
  a closure cell, cannot (its `applyN` of a cell is stuck; the test
  `IxCCTests.Anf.Defun.overAppliedRoot`). Every level below Anf already makes
  such inputs stuck (`Sem.entryRun`). On 2026-11-13 the owner chose a
  premise on the input (rather than making every level from SrcEval down
  apply a root as `Sem.entryRun` does); on 2026-11-14 the owner fixed the
  premise to exactly the declared count, since partial and over-application
  are not coherent for what a binary does. Lean's compiler does the same for
  an exported function: `@[export]` gives it the arity of its declared type,
  whatever the shape of its body. The decision has four parts:
  1. *The statement (implemented).* P8's refinement, and the end-to-end
     theorems that compose it (`Recheck.sound`, `Recheck.RcReplay.sound`,
     `Recheck.compiled_sound` and the theorems above them), hold for inputs
     of exactly the source root's declared parameter count, and for every
     input of a program the closures step leaves unchanged. The premise is
     one predicate on inputs and nothing else: `ExactArity` at Anf
     (`Sem.RefinesOn`, in [`Sem/Transform.lean`](../IxCC/Sem/Transform.lean)),
     `Anf.Entry.DeclExact` at the closures step and `Recheck.ExactDeclared`
     at the source ([`Recheck/Declared.lean`](../IxCC/Recheck/Declared.lean)),
     with `Recheck.Covered` adding the unchanged programs. The claim-level
     theorems (`verifyProgram_*_sound`, `verifyBytes_*_sound`,
     `verifyRing0Sip_sound`, `verifyBytesRing0Sip_sound`) are stated on the
     covered inputs and carry the conjunct that every input of the claimed
     root with exactly the claim's `abiArity` arguments, what the driver
     session executes, is covered (`Recheck.Artifact.covered_head`, from
     `rootParamsAllNat` and `root.params = abiArity`), so nothing at the claim
     level becomes conditional.
  2. *The declared count* is, for now, the number of leading arrows of the
     root's declared type as written (`Src.Term.pis`, which unfolds no
     definition), the quantity `CompileClaim.rootParamsAllNat` compares. No
     certificate can influence it. A result type that is a definition of a
     function type hides arrows: Lean's compiler unfolds such definitions
     when it computes an arity, IxCC does not, and such a root's entry
     returns a closure, which has no readback type and which the claim's
     readback-type check refuses. The planned ABI descriptor is where the
     count should eventually be stated explicitly.
  3. *The mechanism (implemented).* The closures step makes the entry, at
     Anf immediately before P8, for each root whose Anf parameter count is
     not its declared count: a global of that many parameters (key
     `GKey.entry`) that applies the root's value to them by the ordinary
     application mechanism, which P8 turns into a call through the
     dispatchers. The root's own arity, the leading λs of whichever body the
     certificate's table gives it, then no longer matters to the ABI. A root
     whose counts agree is untouched, so programs that compiled before keep
     their bytes; made at Anf before P8, the entry needs no lemma about the
     steps before it.
  4. *The former interim guard.* `Recheck.checkRootArities`
     ([`Recheck/RootArity.lean`](../IxCC/Recheck/RootArity.lean), code
     `rt.arity`, with `rootAritiesOk_spec` and `exactDeclared_cfg`) refuses
     a program whose compiled root takes other than its declared count.
     `Recheck.run` does not call it: with the entries every root's count is
     its declared count, and `tests-pipeline --only defun` calls it as a
     check that it never refuses.

  *Arity, before and with the entries.* No stage η-expands a root, and no
  stage after P1 changes a global's parameters: a root's Anf arity is the
  number of leading λs of the body the unfolding table gives it (its kernel
  value, an equation's body, or a `csimp` target, a constant: arity 0),
  which erasure (`Lam.Erase.rootId`) and P1 keep. The table is certificate
  data, so a certificate can change it: `main4 : Nat → Nat → Nat := g` has
  arity 0 from its kernel value and 2 with an η-long equation in the table;
  a well-founded definition's kernel value has no λ and its equation one.
  Before the closures step most roots with fewer λs than their declared count
  returned a closure and were declined at `fir: fir.closures`, and two shapes
  compiled at another count: a root that builds no closure (a
  `partial_fixpoint` definition `spin (n : Nat) : Nat → Nat := spin (n + 1)`,
  1 against 2) and a root whose declared result type is a definition of a
  function type (`main7 (a : Nat) : NatFn := fun b => …`, 2 against 1).
  With the entries every root is exported at its declared count: `spin` at 2;
  `main7` at 1, returning a closure with no readback type, not claimable.
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
  code. Proof: 4–8k lines. Basis: IxCC's own Anf → Fir lowering (3.8k
  lines for `Fir/` with its proofs), plus one new value relation and the
  dispatcher lemma; published mechanised closure conversions (CertiCoq's, in
  Coq) are of the same order of magnitude.
- The shrink rule: 0.1k + 0.3k. P9: 0.3k + 0.5–1k. Flow oracle: 1.5–2.5k,
  untrusted, no proof.
- Review point: if P8's proof passes about 9k lines, re-plan the proof
  (for example a different value relation); the representation is fixed by
  D20.

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

*Status.* Criterion 1 is met: `Decline.composeClosure` is compiled,
certified (its compile claim verifies) and run natively by `tests-pipeline
--only defun`, and its copy `Closures.composeClosure` runs its interpreter
cases at every level and natively in the registered family `phase2-closures`;
it left the decline corpus. Criterion 4 is met, for every program the closures
step accepts, well scoped or not (`Anf.Pipeline.Proof.closures_lower_ne_closures`,
`Recheck.anfOf_lower_ne_closures`); the step's own refusals are
`defun.captures`, `defun.tags`, `defun.budget`, `defun.input` and
`anf.entry`. Criterion 2 is met: every workload, the `StateT`-over-`Except` loop
in the form `Closures.stateLoopSE`, compiles and is certified under the
production schedule and with specialisation and inlining disabled (where the
closures step changes it), with Lean's values natively both ways
(`tests-pipeline --only defun`); so, since 2026-11-11, is the loop through the
library's `StateT.bind`, `Closures.stateLoop` (a tail call of more than seven
arguments is a call and a return, a frame per iteration; [Measured
limits](#measured-limits-2026-11-11)). Criterion 3 is not met. Frozen
with this tree's `ix` in a probe (not committed), the K2/K3 programs of
`benchmarks/fixtures` meet the production compiler as follows: `nqueens`,
`reverse`, `foldl`, `list-qsort`, `binarytrees` and `rbmap_fbip` are first
order after the middle end and compile unchanged by the step; `queue` keeps
closures and compiles through the step (43 closure keys, 3 dispatchers);
`rbmap` and `const_fold` keep closures and were declined by allocation at a
dispatcher's tail call of eight arguments (`rbmap`: a dispatcher of arity 7
tail-calls another; `const_fold`: a dispatcher tail-calls a lifted function of
seven captures and one parameter); since such a tail call is a call and a
return (2026-11-11) both compile, under plain RC (text 540 KB and 204 KB);
`rbmap_checkpoint` is declined at admission (string literals, an opaque
constant) before the middle end. So what stands between criterion 3 and the
K2/K3 programs today is heap work for the measured rows (the
[roadmap](roadmap.md)), and the size of what the closures step leaves.

## Measured limits (2026-11-11)

Measured with the closures step on the compile path, on the workloads, the
K2/K3 programs frozen in a probe, and the standalone-executables milestone's
probe library (a numeric state machine of `if` chains, no user closure). The
numbers are P8's: closure keys `K` (one per closure source and stage of
partial application, the sum of the sources' arities), dispatchers `M` (one
per arity of an unknown application), and the dispatchers' back-end work
`dispatchWork = M·K²·(T + K + 1)` (`T` the constructor table), past
`Anf.maxBackWork = 2^28` of which P8 refuses (`defun.budget`).
`tests-corpus --survey` prints them for every compiled root.

| Program | Anf nodes before P8 | `K` | `M` | share of the budget |
| --- | --- | --- | --- | --- |
| `phase2-closures` workloads (production schedule) | 52–257 | 2–8 | 1–2 | 0 % |
| the same but `stateLoop(SE)`, P1 and P2 only | 110–349 | 13–27 | 2–3 | 0 % |
| `Closures.stateLoop` (production) | 1,987 | 209 | 5 | 18 % |
| K2 `queue` | 349 | 43 | 3 | 0 % |
| K3 `rbmap` | 1,458 | 150 | 7 | 9 % |
| K3 `rbmap`, P1 and P2 only | 1,651 | 236 | 11 | 55 % (refused: the program's back-end work) |
| K3 `const_fold` | 1,157 | 248 | 4 | 23 % |
| X2 `fibMain` (first-order source; the probe library) | 6,230 (6,811 before the walk's move accounting) | 159 (237) | 2 | 3 % (10 %) |
| X2 `fibMainHO` (the probe library) | 7,953 (8,896) | 232 (353) | 2 | 9 % (33 %) |

Three limits, in the order ordinary code meets them:

1. **The walk's copy budget** (`Walk.maxCopy`, 8,192 nodes walked again per
   walk of a global) leaves closures in first-order code. A shrink round that
   would copy more fails, and `Shrink.produce` keeps the global as it was
   before that round (`fixpointWithin`), so every redex the round would have
   reduced stays. Until 2026-11-11 a β-reduction charged the whole body it
   walked, and an `if` chain nests its else-thunks, so the charges grew with
   the square of the chain while the walk visited each node once; now a
   once-used local function's first expansion is a move, not a copy
   (`Walk.betaFires`), and the 24-test `bif` chain and the 30-line message
   step with its primitives named reduce to one first-order function (text
   1,410 and 2,656 bytes, from 122 and 92 functions and 120 and 90 closure
   keys). Two stops remain. (a) *Case-of-case copies*: the join point that
   turns a `Decidable` into a `Bool` is jumped to with a known constructor
   from each arm, and case-of-case copies the selected alternative there, the
   else-alternative holding the rest of the chain, so these copies still grow
   with the square of the chain: on `if x == k` chains from 8 tests, and on
   the message step with `==`, the root's last shrink round fails (with
   case-of-case off it copies 28 to 32 nodes), so the `==` method, passed in a
   dictionary, stays a known global applied as a value (2 keys, 2
   dispatchers; `chain24` from 80 keys to 2). (b) *Inline rounds refused
   for one caller*: an inline round that one caller's walk exceeds (its
   inlined callees copy more than the budget) was refused for the whole
   program and ended the phase's rounds. The producer now retries such a
   round once without the callers whose walk the re-run refuses alone
   (`Anf.Pipeline.produce`, `Budgets.retryInline`). It is a producer change:
   the re-run checks every round as before, and no rule, budget or
   certificate format changes. A retried round gives the steps after it a
   larger program, which can fail a budget checked later where the run
   without the retry passes (the next shrink step can take the whole
   program past the back end's work budget; the closures step and the back
   end have budgets of their own); the producer then falls back to the run
   without the retry (`Anf.Pipeline.withRetryFallback`): `produce` itself
   for a failure in the middle end, and `ixcc compile` and
   `Recheck.compileInputRetry` (which `tests-corpus` uses) for a failure at
   any stage (the other producers, such as `Recheck.produce` and the claim
   producer, only for one in the middle end). Each run is the proved
   composition at its own configuration, so no statement changes. The
   probe library meets it: on `fibSplit` (`fibMain` with the step split into
   a function per phase) the run with the retry takes the program past the back end's
   work budget after a shrink step, and the fallback compiles it as before. On the probe library, without the retry → with
   it (measured on the same compiler):

   | root | closure keys | closure allocation sites | text bytes |
   | --- | ---: | ---: | ---: |
   | `stepOnly` | 150 → 117 | 274 → 309 | 101,252 → 112,973 |
   | `fibMain` | 159 → 127 | 297 → 350 | 109,837 → 123,846 |
   | `fibMainHO` | 232 → 146 | 405 → 366 | 139,504 → 127,462 |

   So the retry gives 20 to 37 % fewer keys, which is what the dispatch
   budget counts (limit 3). On `stepOnly` and `fibMain` it costs about 12 %
   more text and 13 and 18 % more allocation sites: inlining copies the
   branch thunks into more callers, where each is built and applied in the
   same global. On `fibMainHO` text and allocation sites fall as well (9 and
   10 %). The known-dispatch rule with steps after P8
   ([Known calls after P8](#known-calls-after-p8)) is expected to remove the
   extra allocation sites (a closure built and applied in one global becomes
   a direct call); it is not done. What the retry leaves is the callers
   whose inlined callees alone exceed one walk's copy budget. No registered
   root meets either stop (a), (b), and no registered root's object changes
   with the retry (none has a refused round, even with the inliner's callee
   size raised from 128 to 8,192 nodes). `tests-recheck` covers the retry
   (a round refused for one caller and retried without it) and its fallback
   (a program from bytes whose retried round's shrink step passes the back
   end's work budget, compiled without the retry). `tests-corpus --survey`
   prints each compiled root's keys, allocation sites and dispatch call
   sites.
2. **The tail-call limit**: an internal tail call passes at most seven
   arguments ([roadmap](roadmap.md), "Internal tail calls"), and a dispatcher
   tail-calls each closure's function with its captures and arguments, so a
   closure of more than seven captures and parameters, a dispatcher of arity
   seven reached by a tail call, or a function of more than seven parameters
   reached as a closure makes such a tail call. Until 2026-11-11 allocation
   declined it (`Closures.stateLoop`, K3 `rbmap` and `const_fold`); now
   `Fir.lower` makes it a call and a return, so these compile and a loop
   through one uses a frame per iteration (`stateLoop`: 32 bytes on the
   immortal route, 96 under plain RC), ending with the stack-exhaustion
   status when it runs long enough. Proper tail calls with stack-passed
   arguments, or dropping erased parameters (P5), remove the frame.
3. **The dispatch budget** refuses about 510 keys behind one dispatcher, 372
   behind five, 255 behind eight. No program the production schedule compiles
   is near it: the largest shares are K3 `const_fold`'s (23 %) and
   `Closures.stateLoop`'s (18 %), both compiled since tail calls past seven
   arguments are calls; `rbmap` without inlining and specialisation is refused
   by the back-end budget of the whole program.
   Closure-heavy code runs at 0.1–0.2 keys per Anf node before P8, so a
   program two to ten times `rbmap`'s size reaches the budget; IxCK's checker
   (a 12.6 MB closure, 42 times `rbmap`'s) would need thousands to tens of
   thousands of keys, past the budget and towards the tag space
   (`maxClosureKeys`, 32,512) [estimate]. The quadratic term is the back end's
   switch check: `Rt.testsDistinct` compares every pair of a switch's
   alternatives, each looked up in the constructor table. Checking distinct
   tests on the sorted tests, with the table indexed, makes it `K·log K`, with
   no change to P8, its proofs, the certificate or any object; the
   dispatcher's node budget (`maxGlobalNodes`) and the tag space are then the
   limits, the first lifted by splitting a dispatcher by key ranges.

## No code-pointer fallback

Code-pointer closures (option A) are not a fallback. They would need an
indirect-call row, which decision D20 excludes, and their remaining use, a
closure crossing a program boundary such as a SIP receiving one from the IxOS
monitor, is excluded by decision 1 of 2026-11-10: boundaries pass first-order
data, and higher-order libraries are compiled into each program that uses
them. If dispatch cost makes a K4 or K6 row miss its target after P4 and P9,
the remedies stay within direct calls: more specialisation, more P9 arms, and
a better compare-tree layout (a balanced search on the tag).
## Prior art

The design draws on:
- Reynolds' defunctionalisation, with Nielsen's paper proof of an
  analysis-free version for a simply typed call-by-value language (BRICS
  RS-00-47);
- GRIN (Boquist), which generates `apply` per program;
- MLton's flow-directed closure conversion into datatypes (Cejtin,
  Jagannathan and Weeks, ESOP 2000);
- closure conversion in Lean 4's IR, CakeML (`clos_known` for known calls)
  and CertiCoq.

We know of no mechanised proof of whole-program defunctionalisation; P8's
proof is new work.
