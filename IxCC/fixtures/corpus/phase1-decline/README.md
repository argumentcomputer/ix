# The Phase 1 decline corpus

The `phase1-decline` family of the [fixture corpora](../../../docs/corpus.md)
(phase 1 plan, MT.4; research §9.4.3): real Lean programs outside the
Phase 1 fragment, each declined with the exact `stage: code` that
[`corpus.json`](corpus.json) records. A decline is data: when the compiler
starts accepting one of these programs, or declines it differently, the
suite fails and the manifest is updated with the new behaviour.

[`src/Decline.lean`](src/Decline.lean) holds the declined roots, compiled as
closures by theme (`admit` uses `partial` and `unsafe` on purpose under
`allow_constructs`; `nestedFor`, `mulN`, `unboxMatch` and `subtypeMatch` now
compile and run cases). [`src/Symbols.lean`](src/Symbols.lean) holds roots
that compile alone and collide when compiled together.

## Codes a source reaches

| `stage: code` | Root | Why |
| --- | --- | --- |
| `admit: unsupported` | `withPanic`, `stringLength` | a string literal in a relevant position (`panic!`'s message; `String.length` reaches the `String` library). Until the Ixon v4 refreeze, `stringLength`'s closure exceeded a count budget of the v3 decoder (`ingress: decode`); the v4 closure is within them |
| `rt: rt.params` | `six`, `fiveAndType`, `fiveAndProof` | six parameters; an erased type or proof parameter counts |
| `rt: rt.fnparam` | `applyArg` | a parameter of function type (`f : Nat → Nat`): a closure cannot cross a program boundary, so no caller can pass one and the root has no meaningful caller; refused right after ingress by `ixcc compile` and by every producer (`Recheck.checkFnParams`; which parameters are refused: `IxCC/Recheck/Declared.lean`) |
| `erase: erase-minor` | `recMinor` | `Nat.rec` with a variable minor premise (S25) |
| `admit: opaque` | `useOpaque`, `usePartial` | an `opaque` constant; a `partial def` (Lean adds it as an opaque constant, so `admit: partial` is not reached) |
| `admit: unsafe` | `useUnsafe` | an `unsafe def` |
| `admit: relevant-axiom` | `useChoice` | `Classical.choice` in a relevant position |
| `stacking: stacking.symbols` | `A_b` with `A.b`, `_x_y_` with `«x-y»`, `β` with `α`, `root_init` with `init` | `Rt.symbolOf` maps every character but an ASCII letter, digit or `_` to `_` (`«x-y»` → `cx__x_y_`, `α` → `cx__`) and `init` to `root_init` |

**Previously declined at `fir: fir.closures`, now compiled through the
closures step** (the roots' entries and P8): `composeClosure` (a closure
composed with itself per iteration) left this family for
[`phase2-closures`](../phase2-closures/README.md), where it runs its cases.
`applyArg` (a function argument applied) compiled from 2026-11-11 to its
refusal at `rt: rt.fnparam` the same day: built anyway, the program builds no
closure, so the dispatcher it calls has no alternative and traps on every
input (`tests-pipeline --only defun` still builds it that way and runs it).

**Previously declined, now compiled with cases:** `nestedFor` (nested `for`
loops, compiled via `.box` specialization and CPS matcher inlining), `mulN`
(a `for` loop reading a parameter besides its counter, compiled via spill-slot
reuse and clobber-aware `LinearScan`), and `unboxMatch` / `subtypeMatch`
(single-field structure and `Subtype` match unboxing in `Lam.Erase`).

Elsewhere: `relevance: relevance-C2` (`phase1-scalar`'s
`typeFormerPolymorphism`); `ingress: decode` for 255 fields and 126
constructors (`phase1-boundary`); `rt: rt.params` for arity 6 (`phase1-abi`).
`phase2-closures`' `stateLoop` was declined at `alloc: alloc.fallback` for a
tail call of eight arguments until 2026-11-11 (`Fir.lower` now makes such a
call a call and a return).

**Not a decline:** `twinB` compiled together with `twinA` (the same body, so
the same content address) compiles, but the object exports only the first
root's symbol (`--root twinB --root twinA` exports `cx_twinB` alone): the
second root is dropped without a decline.

## Codes no source reaches through ix

By reading the compiler (2026-10-01); these are not exercised here.

| Codes | Why |
| --- | --- |
| `erase-progwf`, `erase-univs`, `erase-proj`, `erase-record`, `erase-scope`, `erase-recursor`, `erase-ctor-layout`, `erase-pin`, `erase-key` | the certified kernel's acceptance, the kernel's recursors, relevance (S1, C3) or the annotator establish these forms first |
| `erase-const-kind`, `erase-root`, `erase-string`, `erase-budget`, `erase-C2`, `erase-C4`, `erase-S2`, `erase-fuel` | an earlier stage declines the same program first: admission (`opaque`, `unsafe`, `relevant-axiom`, `unsupported`, `budget`) or relevance (`relevance-C2`, `-C4`, `-S2`, `relevance-oracle` at depth 2¹⁴) |
| `erase-modes`, `erase-mode`, `erase-lazy` | by-name binders come only from pinned lazy constants and recursor minors, whose shapes Lazify and the pinned table fix; the sidecar carries only equation hints |
| `convert-root-name`, `convert-dense` | a root is always compiled strictly (`rootId` never uses a by-name key), so no source has a by-name root; erasure numbers globals densely |
| `fir.malformed`, `fir.missing`, `fir.pins` | invariants of the middle end's output and of erasure's pins |
| `rt.exports`, `rt.missing`, `rt.string`, `rt.prim`, `rt.bool`, `rt.form`, `rt.switch`, `rt.edge`, `rt.internal`, `rt.funs` | ingress requires a root; strings are declined at admission; every `Lam.Prim` is lowered; the others are invariants of Cfg |
| `rt.layout` | above 254 fields or tag `0x7EFF`: the decoder's depth budget declines such inductives at ingress first (`phase1-boundary`) |
| `rt.dispatch`, `rt.pins` | erasure emits one alternative per constructor of one inductive, without a default arm; the middle end never adds one; `Nat.zero` and `Nat.succ` have distinct pinned addresses |
| `stacking.layouts`, `.layout`, `.func`, `.export`, `.noEntry`, `.tooLarge`, `.clobbers`, `.malformed`, `.arity` | invariants of the backend's own output (`stacking.export` is pre-empted by `rt.params`) |
| `alloc.<check>`, `alloc.apply`, `select.address`, `select.fold` | the recheck path re-validates the allocation and selection `produce` made; only a foreign certificate reaches them |

Licence: Apache-2.0 OR MIT (original programs).
