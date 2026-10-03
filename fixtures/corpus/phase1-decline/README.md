# The Phase 1 decline corpus

The `phase1-decline` family of the [fixture corpora](../../../docs/corpus.md)
(phase 1 plan, MT.4; research §9.4.3): real Lean programs outside the
Phase 1 fragment, each declined with the exact `stage: code` that
[`corpus.json`](corpus.json) records. A decline is data: when the compiler
starts accepting one of these programs, or declines it differently, the
suite fails and the manifest is updated with the new behaviour.

[`src/Decline.lean`](src/Decline.lean) holds the declined roots, compiled as
closures by theme (one declined at ingress hides only its own roots; it uses
`partial` and `unsafe` on purpose). [`src/Symbols.lean`](src/Symbols.lean)
holds roots that compile alone and collide when compiled together.

## Codes a source reaches

| `stage: code` | Root | Why |
| --- | --- | --- |
| `fir: fir.closures` | `applyArg`, `composeClosure`, `nestedFor` | a function argument applied; a closure composed with itself per iteration; nested `for` loops (Phase 2, P8) |
| `admit: unsupported` | `withPanic`, `stringLength` | a string literal in a relevant position (`panic!`'s message; `String.length` reaches the `String` library). Until the Ixon v4 refreeze, `stringLength`'s closure exceeded a count budget of the v3 decoder (`ingress: decode`); the v4 closure is within them |
| `rt: rt.params` | `six`, `fiveAndType`, `fiveAndProof` | six parameters; an erased type or proof parameter counts |
| `erase: erase-minor` | `recMinor` | `Nat.rec` with a variable minor premise (S25) |
| `erase: erase-unbox-elim` | `unboxMatch`, `subtypeMatch` | a match on a one-field structure or a `Subtype` |
| `admit: opaque` | `useOpaque`, `usePartial` | an `opaque` constant; a `partial def` (Lean adds it as an opaque constant, so `admit: partial` is not reached) |
| `admit: unsafe` | `useUnsafe` | an `unsafe def` |
| `admit: relevant-axiom` | `useChoice` | `Classical.choice` in a relevant position |
| `alloc: alloc.fallback` | `mulN` | **a wrong decline** (MT.2 finding 1): a `for` loop that reads a parameter specialises into a loop function of 8 arguments, beyond the internal convention's 7 argument registers; nothing before allocation declines it |
| `stacking: stacking.symbols` | `A_b` with `A.b`, `_x_y_` with `«x-y»`, `β` with `α`, `root_init` with `init` | `Rt.symbolOf` maps every character but an ASCII letter, digit or `_` to `_` (`«x-y»` → `cx__x_y_`, `α` → `cx__`) and `init` to `root_init` |

Elsewhere: `relevance: relevance-C2` (`phase1-scalar`'s
`typeFormerPolymorphism`); `ingress: decode` for 255 fields and 126
constructors, and `fir: fir.closures` for a wide `match`
(`phase1-boundary`); `rt: rt.params` for arity 6 (`phase1-abi`).

**Not a decline:** `twinB` compiled together with `twinA` (the same body, so
the same content address) compiles, but the object exports only the first
root's symbol (`--root twinB --root twinA` exports `cx_twinB` alone): the
second root is dropped without a decline.

## Codes no source reaches through ix

By reading the compiler (2026-10-01); these are not exercised here.

| Codes | Why |
| --- | --- |
| `erase-progwf`, `erase-univs`, `erase-proj`, `erase-record`, `erase-scope`, `erase-recursor`, `erase-ctor-layout`, `erase-pin`, `erase-key` | erased typing, the kernel's recursors, relevance (S1, C3) or the annotator establish these forms first |
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
