# Compiler design

This reference holds the enduring architecture and design constraints. The
[roadmap](roadmap.md) owns priorities, delivery state and acceptance gates.
Normative wire and trust contracts remain in their focused specifications:
- [Ixon v3](ixon-v3.md);
- [x86 instructions](x86-encoded-instructions.md);
- [x86 streams and objects](x86-stream-objects.md);
- the [trust ledger](trusted-extern-ledger.md).

The pipeline described here is being built (2026-09-29). The earlier
pipeline, its IRs and their contracts are on branch `jcb/ixby-archive`.

## Principles

- **Lean semantics, verified checkers.** Compilatr.ix is written and proved
  in Lean. Expensive analyses and profitability heuristics may be untrusted
  only when a proved checker validates their output, or when the
  transformation is proved correct for every heuristic choice. A rejected
  optimisation falls back to a checked baseline; invalid input is an error.
- **Contracts are lower bounds.** Ixon v3 usage, ownership, locality and
  borrow contracts are part of source identity.
  - The compiler honours every written contract and never weakens one.
  - It may establish a *stronger* guarantee (unique, local, borrowed,
    erased, one-shot) only through a proved checker on the compiled program.
  - Inferred guarantees never change Ixon bytes or addresses.
- **Small, separately proved passes.** Each pass has one responsibility and
  its own simulation. Core relations carry values and memory, not exact
  counters or costs. Cost, space and leak-freedom are separate, optional
  theorems.
- **Executable semantics.** Every IR has an executable, clocked semantics, so
  it can be tested differentially before and alongside its proofs.
- **No new axioms.** Public theorems use only `propext`, `Classical.choice`
  and `Quot.sound`, each with an exact fence. Runtime services, the ISA model
  and build inputs are recorded in the trust ledger.

## Correctness statement

For a compiled root `f` with first-order argument and result types:
- If the native entry returns `r` on inputs `xs`, then `r` reads back as a
  value `v`, and `f xs` denotes `v`.
- Every other outcome is an explicit resource failure (heap, stack, or Nat
  overflow until bignums) or an unfinished run.

This is partial correctness plus safety; termination is not claimed. The
statement is established in two stages:
1. **Against the source evaluator.** Its rules form the published semantic
   contract.
2. **Against every model of the environment accepted by ix-certified's
   `Ix.Kernel`.** A single adequacy theorem relates evaluator results to
   denotations.

## Pipeline

| IR | Form | Semantics | Main obligation |
| --- | --- | --- | --- |
| **Src** | Closed, relevance-annotated v3 kernel terms plus an unfolding table | Clocked big-step environment machine. It never evaluates irrelevant positions and calls lazy constants by name. | Adequacy against `Ix.Kernel`'s model |
| **Lam** | Erased λ-calculus: □, constructors, `case`, recursive definitions, primitives, `trap`; binder contracts retained | Clocked big-step | Erasure simulation |
| **Anf** | A-normal form with join points and known calls | Clocked big-step | Fuel-indexed logical relation; heuristic-parametric rewrites |
| **Fir** | First order: top-level functions, closure objects, `pap`/`apply`, tail calls | Clocked big-step | Forward simulation |
| **Own** | Explicit ownership: owned/borrowed parameters, `inc`/`dec`, reset/reuse credits, unique and local kinds | Clocked big-step over an abstract RC heap | Proved ownership checker ⇒ refinement of Fir |
| **Cfg** | Blocks with parameters over the same operations | Clocked small-step | The single big-step → small-step bridge |
| **Lir** | Words, memory, compare-branch, calls, runtime procedures | Clocked small-step | Heap → memory data refinement |
| **Xv / Xl** | x86-shaped operations on virtual registers, then on registers and slots | Small-step | One lemma per selection rule; allocation validator |
| **x86** | Typed x86: frames, ABI, layout | `X86.Eval` | Frame layout, layout, and generic `SafeSteps` into E1/E2 |

## Source semantics and replacements

The source evaluator's rules:
- β and ζ;
- δ, either by the kernel body or by an unfolding-table entry;
- ι by recursor rules, with induction hypotheses left unevaluated;
- projection;
- Nat and String literal primitives with exact semantics;
- `Quot`;
- the cast family, which reduces to the minor premise;
- `False.rec`, which traps.

**Unfolding-table entries.** Each is proposed by untrusted metadata and
checked against the admitted closure.

| Entry | Meaning |
| --- | --- |
| `eqn f thm` | Unfold `f` through a kernel-accepted `thm : ∀ xs, f xs = rhs`, usually `f.eq_def`. Structural, well-founded, mutual and `partial_fixpoint` recursion then compile as direct recursion. |
| `csimp f g thm` | Use `g` for `f` through a kernel-accepted `thm : @f = @g`. |
| `case T` | `T.casesOn` becomes a primitive case. |
| `inline f` | Unfold matchers and `@[inline]`/`@[macro_inline]` definitions. |
| `lazy f` | Pass arguments by name (`ite`, `dite`, `cond`, `Bool.or`, …). |
| `prim f op` | Compute `f` with a primitive proved against its pinned kernel body. |

In the model, an accepted equation theorem forces its two sides to denote the
same value, so every table entry preserves meaning. When an equation is
missing, the kernel body is compiled instead: correct, but eager.

Rejected: `partial` and `unsafe` definitions, and extern opaques that are not
admitted as ledgered runtime services. `implemented_by` compiles the
reference body.

## Relevance and erasure

**The annotation.** Each binder, argument, let, constructor field and
constant is marked relevant, proof or type.
- An untrusted analysis produces it.
- A proved structural checker verifies its consistency: irrelevant binders
  have no relevant uses, call sites match callee parameters, constructor and
  projection fields agree, and Prop eliminators are recognised by address.

**Why a wrong annotation is safe.** Marking a position irrelevant only makes
evaluation lazier, and the structural checks prevent erased code from
needing a value that was never computed. A wrong but consistent annotation
can make compilation fail; it cannot produce a wrong result.

**Erasure** then:
- drops irrelevant arguments, parameters and fields;
- turns casts into identities;
- unboxes single-field structures (`Fin`, `Subtype`, `BitVec`, `UInt64`, …);
- represents field-free enums as immediates.

## Ownership, reference counting and reuse

**Untrusted passes place reference-counting operations:**
- borrow inference;
- liveness-based dup/drop;
- drop and reuse specialisation;
- reset/reuse by shape and size class, with credits confined to one frame;
- `inc` coalescing.

**The proved checker** is a static linear typing of Own:
- owned values are consumed exactly once on every path;
- borrowed values are never consumed without an `inc`;
- unique values are never duplicated and come only from fresh allocation,
  unique parameters or unique results;
- credits are affine;
- static objects are never unique.

A checked program refines its Fir program up to heap isomorphism. When the
checker rejects the optimised output, the plain dup/drop output is used.

**v3 resource admission** remains an early, diagnosable gate. It is not a
premise of the compiler's theorems.

| Guarantee | Effect in generated code |
| --- | --- |
| unique | No RC traffic and no sharing test; fields move; in-place reuse |
| shared | Dynamic RC; reuse guarded by a runtime uniqueness test |
| borrowed | No `inc`/`dec` for the view or anything projected from it |
| local | Borrowed convention now; region or stack allocation later, once measured |
| one-shot closure | Captures move; the closure cell is freed or reused without a test |

## Runtime

**Representation.**
- Words are immediates when the low bit is set: small `Nat` as `2n+1`,
  enums, `Bool`, `Char`, and □.
- Objects carry one 8-byte header (scan count, auxiliary byte, tag, 32-bit
  RC), followed by scanned fields, then scalar fields.
- `UInt64` is unboxed.

**Services.**
- Allocation uses size-class free lists refilled by bump pointer from a heap
  region the caller supplies.
- Allocation, `inc`, `dec` and the uniqueness test have inline fast paths.
- Freeing is iterative.
- `Nat` overflow is an explicit failure until certified limb bignums land.

The runtime is ordinary Lir code under the same proofs. It links no C runtime
and does not depend on GMP.

## Backend

**Lir operands.** Each operand's constraints (use or definition, early or
late, any/register/stack/fixed/reuse) are derived from the operation's
semantics.

**Selection** is rule-based, with one lemma per rule against the typed x86
semantics. It covers:
- addressing modes and `lea`;
- fused compare-and-branch with inversion;
- short immediates;
- tagged `Nat` arithmetic with an overflow branch;
- `test` for tags;
- `setcc`/`cmov`.

Flags never live across instructions except in fused pairs.

**Register allocation.**
- An untrusted linear scan with splitting proposes per-operand locations,
  move edits and block-entry states.
- A proved validator checks them: location contents, parallel moves,
  clobbers, fixed and reuse constraints, the allocatable set, and the
  calling convention.
- Spilling every value is the fallback.

**Frames and ABI.**
- The internal calling convention is private; exported entries use SysV.
- Callee-saved registers come from the allocation, and leaf functions are
  frameless.
- The frame layout is checked, and prologues check the stack limit.
- Calls use native `call`/`ret`; tail calls become jumps.

**Layout.**
- A checked block permutation, fall-through, branch inversion and tunnelling.
- rel8 comes from untrusted relaxation, range-checked in E2.

## x86 model and trust

**The model.** The typed x86 machine and byte evaluator share one
declarative instruction table: operands, flag effects, write policy, safety
conditions and encoding. E1 proves encoding and decoding per encoding class.
E2 validates complete streams and ELF objects.

**Trust in the table.**
- Now: a hardware-differential gate and an independent decoder gate.
- Later: agreement with the pinned Sail x86 model
  ([reference-model record](x86-reference-model.md)).

## Bootstrap and trust

Upstream Lean is the Gen-0 seed for the compiler and its checkers. Its
kernel, code generator, runtime, host compiler, Nix inputs and native
dependencies are recorded bootstrap provenance.

Four obligations stay distinct:
1. theory adequacy of the source semantics, which `Ix.Kernel`'s model
   provides;
2. correctness of the executable compiler and checkers;
3. the remaining runtime, ISA, linker and loader assumptions, and Gen-0
   provenance, each with its own inventory;
4. statement faithfulness: roots are identified by their v3 addresses.
