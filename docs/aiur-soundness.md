# Aiur verifier soundness repairs

Aiur's verifier must reject a false result even when a prover supplies trace
rows directly, without running the interpreter. The regressions in
`crates/aiur/src/synthesis/tests/` exercise four supplied-trace failures and
a native Merkle commitment-binding defect.

| Failure | Required invariant | Regression |
| --- | --- | --- |
| An inactive function row supplied a public proof of `3 * 5 = 16`. | Function and memory rows satisfy `multiplicity * (1 - selector) = 0`. | [Inactive rows](../crates/aiur/src/synthesis/tests/acceptance.rs) |
| Self-recursive and mutually recursive rows balanced their own calls without a finite execution. | Every constrained call strictly increases a range-checked rank. | [Self recursion](../crates/aiur/src/synthesis/tests/acceptance.rs), [call ordering](../crates/aiur/src/synthesis/tests/call_order.rs) |
| An empty return at rank seven supplied a public claim with output seven because lookup messages are zero-padded. | Public claims and constrained calls agree with the function's input and output arities; yields agree with their continuation. | [Message shapes](../crates/aiur/src/synthesis/tests/lookup_shapes.rs) |
| An inactive branch's store arguments changed a live call's lookup channel and supplied output seven for a program returning one. | Ungated arguments require a single function with terminal control and one selector. Constraint emission and lookup grouping use the same predicate. | [Empty branches](../crates/aiur/src/synthesis/tests/branchless.rs) |
| A large native Merkle cap omitted a shorter matrix: changing its values preserved the commitment, and altered openings verified. | The cap retains the injection layer of every committed matrix. | [Merkle cap coverage](../crates/aiur/src/synthesis/tests/mmcs.rs) |

## Call ranks and witness generation

Each function row has six little-endian rank bytes. A constrained call adds
six bytes for `callee_rank - caller_rank - 1` and requests the derived rank
`caller_rank + 1 + gap` in its lookup. The callee's return binds this rank
without a separate callee-rank column or equality constraint. Three byte-pair
lookups range-check each six-byte value. Ranks and gaps are below `2^48`, so
the derived rank is below `2^49`, below the Goldilocks characteristic. The
call lookup therefore cannot wrap around the field to permit a cycle.

Function query maps share a completion counter. Reversing completion order
assigns the root rank zero and gives each constrained callee a larger rank.
Promoting an earlier advice query refreshes its completion time after its
children are promoted. Shared callees retain a consistent rank. Witness
workers accumulate their byte-range queries locally; the prover merges those
counts before constructing the binary byte-table trace.

The compiler reserves six additional columns and three lookup slots per
function, and six columns and three additional lookup slots per constrained
call. These columns belong to the compiled proving layout and witness
generator. Regenerating the IxVM, aggregation and recursive-verifier execution
sources produces identical files because their instructions and function
indices are preserved.

## Structural bounds

System construction validates constrained-call arities, continuation yields,
canonical function-index and memory-width domains, circuit membership and
control counts. A circuit must reserve at least as many selectors as its
return/yield leaves, including yields consumed by a continuation.
Each constrained function's return arity is summarized once and reused at
every call site. Public-entry shapes are retained with the immutable program
so verifying a claim's shape takes constant time. Summaries include early
returns from nested continuations and reject inconsistent return arities.

Before checking proof openings, the public verifier validates the claim's
channel, entry visibility and arity. It also requires fixed byte tables to be
active at their exact preprocessed heights, and bounds the total number of
lookup consumers below the field characteristic. The bound includes the
public claim and every slot of each active trace row. Malformed metadata,
integer overflow and a bound reaching the characteristic are rejected.

These additional guards make the counting and byte-range assumptions explicit;
the fixed-table and global-count regressions do not claim another demonstrated
false-result acceptance. See [metadata bounds](../crates/aiur/src/synthesis/tests/lookup_budget.rs)
and [fixed tables](../crates/aiur/src/synthesis/tests/byte_shapes.rs).

## Native Merkle cap coverage

The native binary MMCS injects shorter matrices while walking from the
tallest matrix's leaves toward the root. A cap can stop that walk before a
shorter matrix is included. For an eight-row and a two-row matrix, cap
heights two and above omit the shorter matrix; changing that matrix leaves
the commitment unchanged and altered single and multiple openings verify.

Aiur rejects this geometry before checking openings. With trace log-degrees
`d`, LDE log-blowup `b`, and configured cap height `c`, it requires
`min(c, b + max(d)) <= b + d_i` for every active matrix. The implementation
avoids addition overflow and accounts for the native cap's height clamping.
Fixed-table activity makes the preprocessed matrices part of this check too.

Cap heights at most `b`, including the default root cap, satisfy the condition
without scanning degrees. Larger caps require a linear metadata check. No
AIR, trace width, FFT cost or proof encoding changes. Unsafe configurations
are rejected; the recursive verifier already requires cap height zero.

## Compatibility and validation

The activity, call-order and branch-gating repairs change affected AIR
expressions and verification keys. Rebuild proving systems and keys, and
regenerate stored proofs against the repaired systems. Public claim encoding
is preserved: its omitted rank is zero under lookup padding.

The native regressions cover supplied false witnesses as well as honest
execution, finite recursion, shared callees, advice promotion and grouped
circuits. Run them with:

```sh
cargo test --locked --release -p aiur --features parallel
cargo clippy --locked --release -p aiur --all-targets --features parallel -- -D warnings
lake exe ix codegen --check
lake test -- aiur-cross aiur-cost aiur-prove recursive-verifier ix-aggr
lake test -- --ignored ixvm
```

These repairs and regression tests address the defects above. They do not
establish complete compiler preservation or cryptographic soundness.
