# Lazy address-based ingress + declared trust surfaces

Working notes for the `ap/ixvm` branch. Two related changes, plus a
record of what was measured, what failed, and why — so the dead ends do
not get re-attempted.

## Why any of this

`main` typechecks a shard by ingesting the whole reference closure up
front: every constant is parsed, blake3-verified and converted into
kernel form, laid out positionally, and globally sorted, before a single
constant is checked. That works for Init and Lean. It does not work for
mathlib.

Measured on mathlib shard 4 of 32 (owned 45,310 constants, closure
277,434):

| phase | cost |
|---|---|
| `load_assumption_tree` over the 277k-leaf tree | ~75 s |
| `ingress_env` — parse + verify + convert all 277k | **>405 s, never finished** |
| check the 45,310 owned constants | never reached |

The wall is the second row, and it is structural: positional references
(`Const(idx)` into a flat list) *require* the whole closure to be
enumerated and laid out before anything can be checked.

## Change 1 — lazy resolution by content address

References become `CRef`: either `Std(addr)` (an env constant) or
`Member(block, offset)` (a member of a mutual block, which may have no
env-visible projection constant of its own). `get_ci` loads,
blake3-verifies and converts a constant on first dereference, memoized,
so nothing untouched is ever parsed. Mutual blocks load once per block
and validate their canonical member order on first touch, replacing the
single global sort over the whole closure.

Deleted: `load_with_deps`, `compute_layout`, `build_pos_map`,
`canonicalize_pos_map`, `build_canon_addr_map`, `build_convert_inputs`,
`convert_all`, `build_addr_tree` — the entire positional layout pipeline.

Identity of a reference is decided in three tiers, and the ordering
matters for soundness: pointer equality → equal; interned-norm equality
→ equal; otherwise decided by comparing **canonical content addresses**.
Pointer and interning information can therefore only ever produce the
*equal* verdict, which is sound (the Aiur store is content-addressed, so
one pointer means one content). The *unequal* verdict comes exclusively
from the exact address compare. This matters because the positivity
scan concludes "this field does not mention the block inductive" from a
negative — a false negative there would silently accept an illegal
inductive.

## Change 2 — the claim declares and enforces its trust surface

Laziness costs a property `main` had for free. On `main` a `Const(idx)`
can only point *into the ingested closure list*, and every entry in that
list is either checked or skipped-as-assumed, so "everything used is
checked or declared" holds structurally. Once `get_ci` can resolve any
address on demand, that guarantee evaporates.

So the claim now states what it checks, and the kernel enforces it:

`CheckEnv(root, assumptions)` — *every constant in `root` typechecks,
assuming at most the constants in `assumptions`*. `assumptions` is
**mandatory**; "assumes nothing" is the canonical empty (padding) tree
whose root is the zero address, a positive declaration rather than an
absent field.

`check_reachable` classifies every address the reference graph can name:

| lands in | action |
|---|---|
| `owned` | check it, recurse into its refs |
| `asm` | skip — a declared assumption (blob/literal addresses live here; a byte string has nothing to typecheck) |
| neither | **reject** — undeclared use |

Recursion stops at `asm`, so the walk covers `owned` plus one reference
level, never the full closure.

The enforcement lives in the **claim layer**, not the kernel, and that
placement is the whole trick: `Expr.Ref`/`Expr.Rec` are the only way to
name a constant and they index into the naming constant's `refs`, so the
reference graph is the complete naming mechanism and can be walked where
the declared maps already exist. Nothing is threaded through the kernel;
no expressions are walked.

"Check a constant and its whole closure" is now a declared `CheckEnv`
whose owned tree is the closure's constants and whose assumption tree is
its blob addresses.

## Channel conventions

| ch | contents | key | what pins it |
|----|----------|-----|--------------|
| 0 | claim bytes | blake3(claim) = **public input** | content |
| 1 | merkle tree bytes | tree root | content — re-fold and assert |
| 2 | constant wire bytes | content address | content |
| 3 | reducibility hint | defn address | **nothing** — see below |
| 4 | presence discriminator | address | **nothing** — see below |
| 5 | blob raw bytes | blob address | content |

An IOBuffer read is prover-chosen advice: `io_get_info` returns an
unconstrained `(idx, len)` and `#read_byte_stream` unconstrained bytes.
A read is legitimate only if it is **pinned** (something in-circuit
forces the unique correct value) or **harmless** (every value the prover
could supply yields the same verdict).

- ch 3 is unpinned and harmless: the hint only orders which side
  lazy-delta unfolds first. Delta preserves definitional equality either
  way, so an adversarial hint can exhaust fuel and cause a *rejection*,
  never an acceptance. Anyone touching lazy-delta must preserve this.
- ch 4 is unpinned, so it must never be able to select an unsound
  outcome. It is locked so both reachable outcomes are safe:
  `load_verified_constant` asserts `presence == 1`, and
  `check_reachable` skips only on 0/2. The prover's choice is therefore
  between "checked **and** loadable" and "neither checked nor loadable"
  — there is no setting yielding "usable but unchecked". Value 2 means
  an absent primitive and is honored only for the hardcoded primitive
  addresses, whose content blake3 pins; the stub it substitutes can only
  stall a reduction.

### A real soundness hole this fixed

Before the lock, `check_reachable` skipped on presence 0/2 while
`get_ci`/`load_verified_constant` loaded ch 2 *ignoring* presence. A
prover could ship a constant's real bytes on ch 2 and mark it ch 4 = 0:
its check was skipped, but its data was used. If that constant were
ill-typed, the dependent was accepted anyway. Found by adversarial audit,
not by any test — every honest witness sets ch 4 consistently, so the
suite was green throughout.

## The `Nat.add_comm` FFT regression: 44,037,801 → 86,717,419

Real, understood, and **not** caused by enforcement.

Three circuits are byte-identical across the two runs — `convert_expr`
751,801, `expr_inst_many` 730,217, `get_expr` 726,916 — so no extra
checking or conversion happens. The entire delta is blake3.

`blake3_compress` height *is* the compression count: **139 → 297, +158**,
and `blake3_g_function` rows rise by exactly 158 × 56. The cost follows
plain n·log n with no padding cliff:

```
(16623 × log₂16623) / (7775 × log₂7775) = 2.32   observed 52.2M/22.5M = 2.32
```

Those 158 compressions are the two merkle folds this change introduced
on the whole-closure path:

- owned tree over the closure's ~49 constants → 49 leaf + 48 node = 97
- asm tree over its ~30 blobs → 30 + 29 = 59

97 + 59 = 156 ≈ 158. That is the whole regression.

It is the literal price of declaring the checked set: pinning a set means
merkle-verifying it, and verifying means re-folding it. The old
`Check(addr, none)` was cheaper precisely because it declared nothing and
let the kernel derive the set.

Two things bound the impact:

1. **Shards are unaffected.** `run_check_env` already loaded both trees
   before this change; the marginal cost there is map lookups, which the
   identical-circuits evidence shows is negligible.
2. **`Nat.add_comm` is a worst case.** Its closure is tiny (49
   constants), so 156 tree hashes are comparable to the 139 hashes of
   real content. For a 45k-constant shard the fold is a rounding error.

Available optimization, not yet taken: the asm tree declares every blob
in the closure, but only blobs actually referenced by checked constants
need declaring.

## Dead ends — do not re-attempt

**Eliminating ch 4 by deriving const-vs-blob from the converted body.**
The idea was to collect the check-set as the `Const(Std _)` addresses
appearing in a constant's converted expressions, making the discriminator
unnecessary. It is catastrophic in Aiur's cost model, which memoizes on
the entire argument tuple, so every intermediate list becomes its own
memo entry and per-node set operations explode on shared expression DAGs.
Measured on `Nat.add_comm`, which normally runs in ~1.5 s:

- `list_concat` accumulation: **159 GiB** RSS, killed
- deduplicating union: **82 GiB** RSS, killed

Deduplication bounded the list *lengths* but not the number of distinct
memo keys, which is what actually explodes. `const_check_deps` uses the
constant's `refs` list instead — already parsed and deduplicated, so
obtaining it is free.

**Per-dereference merkle inclusion proofs** instead of materializing the
declared sets: ~18 blake3 compressions per distinct constant, against
blake3 already being ~60% of cost. Folding the tree once is cheaper by
roughly a log factor.

**A membership assert inside `load_verified_constant`.** It is the right
chokepoint — the only reader of constant data — but it would need the
declared map threaded through every kernel function that can reach
`get_ci`, which is the `top`/`addrs` threading this branch just removed.

## Aiur idioms worth knowing

- **Direct recursion, not accumulators.** Aiur memoizes on the full
  argument tuple, so an accumulator parameter changes every call and
  nothing is ever reused, even across identical shared subterms. Write
  `f(e) -> List` combining children with a memoized combinator, not
  `f(e, acc)`. Tail recursion buys nothing (stack depth is free) and
  actively costs sharing.
- **Pointer inequality proves nothing.** A pointer *hit* implies content
  equality and is sound; a miss implies nothing. Only ever conclude
  "equal" from pointers, never "unequal".
- **The DSL and the generated Rust kernel are two artifacts.** They only
  move together via `lake exe ix codegen`. Bytecode runs interpret the
  DSL directly and will mask a stale native kernel; the suite's
  codegen-parity tests will not.
- **The witness exists twice** — Lean (`ClaimHarness`) and Rust
  (`aiur_ixvm_witness.rs`) — and the CLI picks between them by
  `EnvHandle` availability. They must stay in lockstep. A mismatch
  presents misleadingly as an interpreter parity bug.

## Status

- ixvm suite green at commit `64066f8` (644 assertions), which is the
  lazy kernel plus the ch 4 lock, with FFT pins re-harvested.
- This commit adds mandatory assumptions and enforcement. Both
  interpreters agree on `Nat.add_comm`; FFT pins are **not** re-harvested
  yet, so the suite's pin assertions will fail until they are.

## Next

1. Re-harvest the 64 FFT pins; confirm the suite is green; commit.
2. Strip the debug scaffolds: the `checkFunction FAILED in {name}` trace
   in `Ix/Aiur/Compiler/Simple.lean`, and the interpreter stack-limit
   bump in `Ix/Cli/CheckCmd.lean`. Drop `synthetic_primitive_addrs` if it
   is genuinely dead.
3. Init shards, then Lean shards, then **mathlib shard 4** — the run this
   whole branch exists for, and the number that decides whether lazy
   ingress actually clears the 277k wall.
4. Open question that bounds the win and has never been measured: how
   many distinct constants a shard actually *dereferences*. If that
   approaches the full closure, lazy ingestion degenerates toward eager
   and the payoff shrinks. One instrumented run answers it.
