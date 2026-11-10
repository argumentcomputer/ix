# Bignums: a limb library compiled by IxCC

Written 2026-11-09. **Status: planned (Phase 4).** Nothing here is
implemented. The [roadmap](roadmap.md) owns scheduling; the
[data design](data-and-roots-design.md) owns the fixed-width words and arrays
this design builds on.

**Decision (owner, 2026-11-09).** Arbitrary-precision `Nat` is implemented
as new Lean code: the standard multi-precision algorithms, each proved in
Lean against the corresponding `Nat` operation, compiled by IxCC like any
other program and linked as the slow path of `Nat` arithmetic. No C bignum
code enters the trusted base. "A subset of GMP" describes the *scope*, the
`mpn`-level operations `Nat` needs; it does not describe the source. The
implementation draws on several published descriptions and libraries
([references](#references)) under the [provenance rule](#provenance-rule).

## Motivation

- **K5** (factorial, big Fibonacci, π and e digits) and every program whose
  `Nat` values pass 2^63.
- **The certified kernel.** IxCK computes on `Nat` literals with exact
  semantics; `pow` alone is capped, at exponents above 2^24
  (`IxCK/Kernel/CoreDefs.lean:820`).
- **A self-hosted checker.** IxCC's own recheck path compares 256-bit
  addresses as `Nat`s (`Pinned.addrNat`, [`Src/Pinned.lean`](../IxCC/Src/Pinned.lean)),
  so compiling it (the IxOS monitor's admission step) needs bignums.

## Current state

- *Implemented.* `Nat` is exact in every IR above Lir. At Lir a `Nat` is the
  tagged word `2n + 1` for `n < 2^63` (`Rt.natLimit`,
  [`Rt/Layout.lean:35`](../IxCC/Rt/Layout.lean)); a literal or result at or
  above 2^63 ends the run with `fail natOverflow`, a resource failure
  ([`Rt/Lower.lean:269-274`, `:334-405`, `:484`, `:669`](../IxCC/Rt/Lower.lean)).
  `natPow` and `natGcd` call the Lir procedures `rt_nat_pow` and `rt_nat_gcd`
  ([`Rt/Procs/Nat.lean`](../IxCC/Rt/Procs/Nat.lean)), which also fail on
  overflow. Readback reserves even words for a future bignum cell
  ([`Rt/Readback.lean:11`](../IxCC/Rt/Readback.lean)).
- *Implemented.* SrcEval's primitives are exact and uncapped
  (`Src.PrimOp.eval2`, [`Src/Prim.lean:20-34`](../IxCC/Src/Prim.lean)).
- The `phase1-boundary` corpus family records the 2^63 edge for every
  primitive ([corpus](corpus.md)).

## Scope

The operations, and the `Nat` functions they serve:

| Group | `Nat` operations | Notes |
| --- | --- | --- |
| Linear | `add`, `sub` (truncating), `pred`, `beq`, `ble`, `blt`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`, `log2` | carry and borrow chains; `log2` from the limb count and the top limb's leading zeros |
| Multiplication | `mul`, `pow` | schoolbook with a dedicated squaring loop; `pow` by left-to-right squaring |
| Division | `div`, `mod` (with Lean's `n / 0 = 0`, `n % 0 = n`) | Knuth's Algorithm D with normalisation; one-limb divisors separately |
| Number theory | `gcd` | Euclid on the division routine first |
| Conversion | `Nat.repr` and parsing | repeated division by 10^19 per limb group |

`Int`'s large values reuse the library as sign and magnitude, with Lean's
`Int` division families each proved; that is a follow-on within Phase 4.

**Stages.** Stage 1 is the schoolbook set above. Stage 2 adds, only where
K5 or a flagship measurement shows the need: Karatsuba and Toom-3,
division by an invariant word with a precomputed reciprocal (Möller and
Granlund), recursive division (Burnikel and Ziegler), divide-and-conquer
radix conversion, and Lehmer's gcd. Every threshold between algorithms is a
constant of the library; any value is correct.

## Representation

```text
small  2n + 1                       n < 2^63
big    pointer to a cell:           header (scan 0, a kind tag above Rt.maxTag, rc)
                                    · limb count n · capacity · limbs[capacity]
                                    value ≥ 2^63, limbs little-endian, limbs[n-1] ≠ 0
```

- **Normal form.** A value below 2^63 is always an immediate, and a cell's
  top limb is non-zero. Equality is then word equality or limb equality, and
  readback stays injective.
- **Fast paths stay as they are.** Each overflow check in `Rt.lower`
  (`natAdd`'s carry branch, `natMul`'s bound checks including the constant
  and squaring cases, `natShl`'s check, the `rt_nat_pow` and `rt_nat_gcd`
  overflow exits) keeps its fast path, and its failure branch becomes a call
  of the library's slow path. An operation on a cell operand tests the tag
  bit first (one `test` of both words' low bits for binary operations) and
  goes to the slow path.
- **Promotion and demotion.** The slow path builds a cell when the result
  is at least 2^63 and returns an immediate when it is not. `pred`,
  subtraction and the `Nat.succ` peel of `case` can demote.
- **Literals.** A literal at or above 2^63 becomes a static immortal cell in
  read-only data (the statics of [D1](data-and-roots-design.md#d1-heap-completion)),
  replacing today's `fail natOverflow` at the literal.
- **Mutation.** A unique operand with enough capacity is overwritten in
  place; a shared one is copied. The cell has no scanned fields, so
  releasing it is one `dec` that frees the cell.
- **Failure.** A number too large for the region is a heap failure.
  `Sem.Resource.natOverflow` ([`Sem/Result.lean:20`](../IxCC/Sem/Result.lean))
  is retired, with a gate map for every check that names it.

## What the library needs from earlier phases

- **Raw 64-bit limbs** ([D2](data-and-roots-design.md#d2-fixed-width-integers-and-int)).
- **Arrays of `UInt64` with in-place update under uniqueness**
  ([D3](data-and-roots-design.md#d3-arrays-and-byte-arrays)).
- **Three word primitives**, new pinned definitions of the library whose
  Lean bodies are their meaning, each with a conservativity lemma:
  add with carry (`UInt64 → UInt64 → Bool → UInt64 × Bool`), the full
  64×64→128 product (`UInt64 → UInt64 → UInt64 × UInt64`), and 128/64 division
  with the quotient-fits precondition (`hi < d`). Their bodies go through
  `Nat`, so without the primitives the library would overflow the tagged
  word it is meant to replace. Lowering: `mul r/m64` and `div r/m64` exist in
  the instruction table ([x86 instructions](x86-encoded-instructions.md)); an
  `adc` chain needs new rows and a decision on how a carry lives across
  instructions, because flags never live across instructions except in fused
  compare-and-branch pairs ([Backend](compiler-design.md#backend)). The
  first version materialises the carry in a register.
- **Pair results** without allocation (multi-value returns) matter for
  speed, not for correctness.

**Bootstrapping.** The library is compiled with today's lowering, in which a
`Nat` overflow fails. Its own `Nat` values are array sizes and indices, all
below 2^63, and its limbs are raw words, so it never needs itself. Programs
are compiled with the bignum lowering, whose slow paths call the library.
A test in the library's gate checks that no compiled library routine reaches
`natOverflow` on the differential inputs.

**Linking.** First, the library's closure is compiled into every program
that needs it, which is closed-world compilation as for any other library
code. A separately certified library object with a linking theorem is a
later scale optimisation.

## Proof obligation

Three layers, of which the third is the hard one.

1. **Library theorems (Lean, about the Lean definitions).** For each
   routine, `toNat (op a b) = toNat a ⋆ toNat b` over a little-endian limb
   view `toNat : Array UInt64 → Nat`, with the normal-form invariant
   preserved. Tools: `omega`, `Nat` lemmas from Lean core (`Nat.div_add_mod`
   and friends); only the three standard axioms, so no `bv_decide` or
   `native_decide`.
2. **Compiler theorem for the library program.** IxCC's existing pipeline
   theorems, instantiated at the library's Src program, give "the compiled
   routines refine SrcEval of the library", through the array data
   refinement of D3.
3. **SrcEval computes the Lean definitions.** Layer 1 speaks about the Lean
   functions; layer 2 about SrcEval running the library's Ixon image. Linking
   them is source adequacy for this one program, which no theorem provides
   today ([certification design](certification-design.md), S8). The planned
   route is the stage-L translator (C3 there) applied to the library's
   closure, which is small, first order and monomorphic. The fallback is a
   direct proof per routine by symbolic evaluation of `Src.run`.

With the three layers, `Rt.lower`'s data refinement for each `Nat` primitive
takes as premise "the linked slow path maps representations of `a` and `b`
to a representation of `a ⋆ b`, or fails for a resource", and discharges it
once per library version. The end-to-end statements (`Recheck.sound`,
`Recheck.RcReplay.sound`, the claim theorems) keep their form; overflow
simply stops being one of the resource failures.

**Until layer 3 exists**, the statement "SrcEval of the limb library
computes its Lean definitions" would be an explicit specification
assumption in the [trust ledger](trusted-extern-ledger.md), comparable to
today's "SrcEval is the source's meaning" and narrower. It adds no native
code. The owner's aim, bignums certified with no new trusted code, is met
only when layer 3 is proved.

### Kernel literals and SrcEval's exact `Nat`

- SrcEval's `Nat` is exact and uncapped; the compiled code must agree with
  it, and the library's layer-1 theorems are about Lean's `Nat`, so all three
  agree by construction.
- Lean's kernel accelerates `Nat` literals with GMP when it checks the
  library's proofs and when a `decide +kernel` gate evaluates `Recheck.run`.
  That is Lean's existing trusted kernel (the Gen-0 bootstrap in
  [Bootstrap and trust](compiler-design.md#bootstrap-and-trust)), not new
  trust. `Recheck.run` evaluates program `Nat`s only when constant folding.
- IxCK's literal extensions, and its `pow` cap, concern kernel evaluation;
  denotations are unaffected. They enter only the stage-2 adequacy proof,
  where each `Nat` primitive's meaning must equal its denotation.
- Native tests compare against Lean-compiled programs, whose `Nat` is GMP:
  a test oracle, not a premise.

## Trusted base

No new native code. Interim: one specification assumption until layer 3.
New x86 rows (an `adc` chain, if adopted) join the table and its
hardware-differential gate.

## Dependencies

D1 (cells with scalar payload), D2 (raw words and the word primitives), D3
(arrays, uniqueness), D1 again for static cells, and C3 of the
certification design for layer 3.

## Size [estimate]

- Stage 1 library with layer-1 proofs: 6–10k lines. Basis: CakeML's
  verified bignum library (schoolbook and Algorithm D) with about 2.3k proof
  lines plus 2.6k for its integration, as surveyed in the pre-merge numerics
  research (untracked); our proofs are stated against `Nat` rather than
  machine words, and carry normal-form invariants.
- Representation, slow-path calls, readback and the `Rt.lower` proofs: 3–6k,
  against `Rt/` (21.9k today).
- Stage 2 algorithms: 5–10k more; recursive division and divide-and-conquer
  conversion are the hardest, 2–3k each by the same survey.
- Layer 3 is counted under C3.

## Performance expectations

Nothing has been measured. Qualitatively:
- below 2^63 nothing changes except one tag test on paths that cannot
  prove both operands small;
- for small cells (a few limbs) the cost is the call, the allocation and
  the normal-form check;
- for large operands, schoolbook and Algorithm D are quadratic, and GMP's
  subquadratic algorithms and hand-scheduled assembly will be much faster
  there. Stage 2 narrows the gap; parity with GMP is not a goal;
- the carry representation decides the speed of the linear and
  multiplication loops.

Targets are set per rung after the first K5 measurements, as for other
rungs.

## Exit criteria

1. K5 (factorial, big Fibonacci, π digits, e digits) compiles and certifies
   and matches Lean-compiled output.
2. The `phase1-boundary` cases at 2^63 return values instead of
   `natOverflow`, and `natOverflow` is retired with its gate map.
3. Differential tests against Lean's `Nat` on random operands of 1 to 1,000
   limbs for every operation, and layer-1 theorems fenced with the standard
   axioms.
4. Layer 3 proved for the library closure, or, until then, the ledger
   assumption recorded with its exact scope.

## Alternatives considered

| Alternative | Why not |
| --- | --- |
| A trusted runtime bignum, as Lean does (GMP, or Lean's own fallback `src/runtime/mpn.cpp`) | Puts C in the trusted base, against the runtime decision in the [roadmap](roadmap.md#decisions) |
| Hand-written Lir procedures for the algorithms | Proofs over Lir are harder than over Lean; kept only for small dispatch stubs if they help |
| Porting verified machine code (s2n-bignum) | Fixed-size, cryptographic routines; its HOL Light proofs do not transfer |
| Replacing `Nat` by a library type through the unfolding table | Circular: the conversions between `Nat` and limbs need the very operations being replaced |

## References

What each reference is best for. Licences were checked on 2026-11-09 where
stated; "not checked" means the reference is used for its published text
only.

| Reference | Best for | Licence |
| --- | --- | --- |
| Knuth, *TAOCP* vol. 2, §4.3.1 (Algorithms A, S, M, D) | The base algorithms and the correctness argument for Algorithm D's quotient estimate | Book |
| Menezes, van Oorschot, Vanstone, *Handbook of Applied Cryptography*, ch. 14 (14.7 add, 14.9 sub, 14.12 multiply, 14.16 square, 14.20 divide, 14.54 binary gcd, 14.57 Lehmer) | Step-by-step pseudocode with explicit invariants, close to proof obligations | Book |
| Brent and Zimmermann, *Modern Computer Arithmetic* | Karatsuba and Toom, recursive division, subquadratic radix conversion, with analyses | Book |
| Möller and Granlund, "Improved division by invariant integers" (IEEE TC, 2011) | The reciprocal-based 2/1 and 3/2 word division | Paper |
| Burnikel and Ziegler, "Fast Recursive Division" (MPI report, 1998) | Recursive division | Paper |
| Go `math/big` | The clearest modern account of long and recursive division (the commentary in `natdiv.go`, citing Knuth and Burnikel–Ziegler, recursion threshold `divRecursiveThreshold`); divide-and-conquer `itoa` (`natconv.go`); 64-bit words | BSD-3-Clause |
| Rust `num-bigint` | Algorithm selection by size (schoolbook, Karatsuba, Toom-3, NTT in `mac3`); Algorithm D in `div_rem_core` and Burnikel–Ziegler above 64-digit divisors; 64-bit digits over a vector, close to our arrays | MIT or Apache-2.0 |
| LibTomMath | One routine per file, following HAC closely; Comba, Karatsuba, Toom, school and recursive division, Montgomery, Barrett. It uses 60-bit digits in 64-bit words, a different design point from our full 64-bit limbs | Public domain ("LibTom license") |
| Zig `std.math.big` | A compact limb-slice implementation: Karatsuba above 48 limbs (`llmulaccKaratsuba`), HAC 14.20 division, Lehmer gcd | MIT |
| Lean 4's `src/runtime/mpn.cpp` | What Lean itself does without GMP: "essentially Knuth's Algorithm A/S/M/D" | Lean is Apache-2.0; the file carries a 2011 Microsoft copyright |
| BearSSL `i31`/`i62` | Constant-time modular arithmetic for fixed sizes; outside this scope, a reference only if a constant-time contract is added | MIT (not re-checked) |
| CakeML's verified bignum library | The precedent for this design: limb routines proved at the source level and compiled by a verified compiler | BSD-3-Clause |
| WhyMP (Melquiond and Rieu-Helft; JFR 2019, J. Symb. Comp. 2023) | How to structure proofs of GMP-style algorithms (Toom-Cook, division, square root) | Papers only; code licence not checked |
| s2n-bignum | x86-64 code shapes for carry chains, proved in HOL Light | Apache-2.0 or ISC or MIT-0 |
| GMP and mini-gmp | Algorithm behaviour and edge cases, as a reference only | LGPLv3+ or GPLv2+ |

## Provenance rule

For implementers:
1. Implement the abstract algorithm from its published description.
2. Consult more than one reference for each routine.
3. Do not follow any one source's code structure function by function
   (structure, naming and comments included). This applies to every library
   above, and GMP and mini-gmp are consulted for behaviour only.
4. Name the references used in the module header.
