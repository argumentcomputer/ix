# Implement canonical minimum sharing in Ix

Implementation plan, 2026-09-30 (revision 2, tracked in Ix). Target: an implementation and
reviewable PR in the **Ix repository**, covering its Lean and Rust paths. This file is a
plan, not evidence that the optimizer or migration already exists. Revision 1 and its
research oracles live in the Cybernet.ix research directory
`/home/jcb/projects/Cybernet.ix/plans/ixsy/sharing-optimality/` (read-only for this work).
Revision 2 adds §0 (workspace), §4.1 (proved reductions and bounds), §6.4 (sparse states),
the corpus-measurement gate P1.5, and §11 (parallel workstreams).

## 0. Workspace, toolchain and corpus

- Work in the git worktree `/home/jcb/projects/ix-sharing`, branch `ix-sharing`, based on
  `864130ec` (the revision the research inspected). Do not touch `/home/jcb/projects/ix`.
- The toolchain comes from the flake: run every `lake`/`cargo` command as
  `nix develop --command bash -c '<cmd>'` from the worktree root. `lake build ix IxTests`
  has already completed once in this worktree; incremental rebuilds are fast.
- Tests: `lake test -- sharing` runs `Tests/Ix/Sharing.lean`; `lake test -- ixon` the codec
  suite; `cargo test -p ixon` the Rust crate; `lake build IxCompileVerify` the proofs.
- A real corpus is available: `Init` compiled by the production Lean compiler to
  `/tmp/claude-1000/-home-jcb-projects-ix/9f80f39b-580f-424c-aa72-a746c6374a34/scratchpad/init.ixe`
  (65,995 constants, 195 MB). Regenerate with
  `lake exe ix compile Benchmarks/CompileInit.lean --out <path>` from the worktree root
  (NOT `Benchmarks/Compile/CompileInit.lean`, which is a separate Lake project that pulls
  Mathlib). Load it with `Ixon.deEnv` / `Ixon.deEnvAnon`; each `LazyConstant` exposes
  `rawBytes` (the exact production bytes) and `get` (the parsed `Constant`).
- The production root API is `Ix.CompileM.constantInfoRootExprs` and the rebuild logic in
  `Ix.CompileM.buildConstantWithSharing` (`Ix/CompileM.lean`); expand an existing table
  before re-optimizing (§7).

## 1. Outcome and scope

Replace heuristic selection as the canonical construction rule with an **exact minimum
sharing encoding** of a resolved anonymous Ixon constant/block. Equal anonymous ASTs with
the same ordered roots, contracts, refs/univs bindings and format must produce identical
bytes, regardless of pointer sharing, construction history, encoder implementation or
search strategy. Ixsy should call this pure data operation directly; it must not require
the Lean frontend.

“Minimum” means the fewest bytes in the **complete serialized Constant**, over all legal
sharing selections, table orders and occurrence-level inline/reference choices. A pinned
total tie-break selects one of the shortest encodings. This is stronger than a deterministic
heuristic, a local optimum, or a result no larger than the old heuristic.

For this PR, fix all non-sharing choices: ConstantInfo variant and fields, semantic member
and root order, constructor contracts, refs table, univs table and their indices. Do not
normalize universes, transform terms by definitional equality, reorder mutual members,
generate auxiliaries, alter declaration factoring, or jointly optimize metadata. The scope
is the smallest **sharing representation of that AST**, not the smallest equivalent program
or globally smallest `.ixe` environment.

Metadata must remain correct when primary sharing changes. Its contents cannot influence
the anonymous optimum or address. Metadata-table minimization is a separate task.

The exact minimum exists and can be computed by finite search for every finite admissible
input. A practical bounded invocation may return a resource error. It must never publish
an uncertified best-so-far result as canonical. Optimizer speed remains an engineering and
benchmarking obligation; no polynomial runtime claim has been established for full Ixon.

## 2. Starting evidence and source map

Research inspected Ix revision `864130ecaaee8aac9ddc38eaefdfc333fc793513` at
`/home/jcb/projects/Cybernet.ix/plans/refs/ix`; another local checkout was
`/home/jcb/projects/ix-cybernetix`. Refresh the target branch, repository instructions,
interfaces and test commands before implementing. Do not copy stale source over later work.
Use an isolated branch/worktree and submit the PR to Ix, not Cybernet.ix.

Relevant paths relative to the Ix checkout:

| Area | Files / entry points to inspect and update |
|---|---|
| Lean sharing | `Ix/Sharing.lean`: `analyzeBlock`, `decideSharing`, `buildSharingVec`, `applySharingCore`, `applySharing` |
| Lean codec and contracts | `Ix/Ixon.lean`: `putTag0`, `putTag4`, `putExpr`, `putConstant`, `Env.VERSION`; `Ix/IxonContract.lean`, `Ix/IxonMode.lean` |
| Rust sharing/codec | `crates/ixon/src/sharing.rs`, `serialize.rs`, `expr.rs` |
| Lean compiler integration | `Ix/CompileM.lean`: `constantInfoRootExprs`, `mutConstRootExprs`, `buildConstantWithSharing`; `Ix/AuxGen/CompileAux.lean` |
| Rust compiler integration | `crates/compile/src/compile.rs`: `apply_sharing_with_stats`, `apply_sharing_to_*`; `compile/mutual.rs`; `kernel_egress.rs`; `decompile.rs` |
| Cross-language boundary | `crates/ffi/src/lean_ixon/sharing.rs`, existing sharing comparison FFI |
| Metadata and ingress | `Ix/DecompileM.lean`, `Ix/Tc/Ingress.lean`, `Ix/Tc/IngressMeta.lean`, Rust `compile/decompile.rs` and kernel ingress consumers |
| Proofs | `Ix/Compile/Verify/Sharing.lean`, `CompileSharingCodec.lean`, downstream compiler codec theorems and audit manifests |
| Tests | `Tests/Ix/Sharing.lean`, Rust sharing tests, codec/compile/decompile differential suites |
| Version policy and docs | `docs/Ixon.md`, `docs/Ixon-v3.md`, format IDs, manifests, CLI/version checks, generated fixtures |

The current heuristic estimates `(uses−1)·size − uses·shareRefSize` before rewriting.
It uses logical expanded occurrence counts, ignores telescope savings in its subtree cost,
and prices provisional indices before emission changes their order. Existing sharing proofs
establish wire well-formedness/capacity, not size optimality.

Known complete-Constant measurements:

| Fixture | Old heuristic | No sharing | Better candidate / certified minimum |
|---|---:|---:|---:|
| `T2 → T2`, where `Tn = Prop → … → Prop` has n binders | 19 | 20 | **17, exact minimum** |
| `T16 → T16` | 81 | 78 | 46, feasible improvement |
| Nine independent repeated Ref atoms; hot atom previously at slot 8 | 676 | — | 578 with same entries reordered |

The small witness has `P = Sort(0)`, `T1 = All(P,P)`, `T2 = All(P,T1)`,
`R = All(T2,T2)`, default contracts, `Axio(false,0,R)`, refs `[]`, univs `[Zero]`.
Its old table is `[T1, All(P,Share(0))]`; the minimum stores only `[T2]`.

```text
old:     d200009117b1b10291170000911700b0000100  (19 bytes)
minimum: d200009117b0b001921700170000000100       (17 bytes)
```

Another closed fixture has two different minimum 25-byte encodings: let
`A = Prop → Prop`, `B = Prop → Type`, and root `A → A → B → B`, with
univs `[Zero, Succ Zero]`. Both entry orders `[A,B]` and `[B,A]` attain the minimum.
The nine-Ref ordering fixture is a wire/expansion witness, not a kernel-checked recursor.

Supporting material in this handoff directory:

- [Research report](REPORT.md), including the finite-space and dynamic-programming argument.
- [Independent Astra report](astra/report.txt), [production results](astra/production-results.txt),
  [source hashes](astra/sources.txt) and [production probe](astra/production-probe/main.rs).
- [Counterexample.lean](Counterexample.lean): subset codec, kernel-checked small byte-count
  equalities, and a complete 3,061,082-candidate search of the tiny witness.
- [ExactDP.lean](ExactDP.lean), [driver](RunExact.lean), and
  [results](exact-dp-results.txt): fixed-dictionary telescope recurrence checked against
  exhaustive variants in 260 cases; subset DP finds the 17-byte minimum with 16 states.

These scripts are research oracles. They do not implement the complete format, general
width buckets, production metering or the proposed structural-ID tie-break. Preserve the
distinction when transferring fixtures to Ix.

## 3. Normative canonical rule

Use the following concrete tie-break for this implementation. It permits exact merging of
equal-cost table-order histories and avoids making the optimizer algorithm part of identity.
Do not substitute a hash order, the old heuristic's order, or “first answer found.”

### 3.1 Logical input and feasible representations

1. Recover a finite anonymous AST DAG with **no unresolved Share leaves**. Existing tables
   must be expanded logically, with cycle/index validation, memoization and explicit bounds.
   Expansion need not allocate the full occurrence tree. Fresh compiler ASTs can enter
   directly after refs/univs allocation.
2. Use every ordered expression root of the complete ConstantInfo. At the inspected revision:
   definitions use type/value; axioms and quotients use type; recursors use type/rule bodies;
   mutual blocks flatten each member's roots in member order, including inductive/constructor
   types. Projection constants have no roots. Reuse or extract the production root API and
   check that rebuilding consumes exactly the same number/order of roots.
3. Candidate sharing tables contain ordinary expressions and Share references. In entry `i`,
   every Share index must be `< i`; roots may reference any table entry. Expansion must
   reproduce every original root exactly. No shifting, substitution or alpha-renaming of
   de Bruijn indices occurs at a Share.
4. All other Constant fields, refs/univs arrays and bindings are unchanged. Serialize each
   candidate with the canonical Ixon integer and maximal-telescope rules.

The backward-reference rule is part of this feasible class, even if a low-level decoder
accepts a larger class of raw graphs. Audit and document that distinction. The claim is a
minimum over valid backward-reference sharing encodings. Do not claim optimality over
unrestricted forward-reference graphs without extending the specification and search.

### 3.2 Deterministic structural term IDs

Collect all distinct rooted subterms of the expanded roots, including leaves and entire
roots. Equality includes every constructor, scalar, contract and ordered child. The initial
complete algorithm considers them all; candidate elimination requires a proof.

Assign IDs `0..N−1` as follows:

1. A leaf has height 0. A nonleaf has height `1 + max(child heights)`.
2. Process heights in increasing order. Children already have IDs.
3. At one height, sort distinct nodes by `(constructor tag, scalar payload vector,
   ordered child-ID vector)`, using numeric comparison for unsigned integers and ordinary
   lexicographic vector comparison, with a proper prefix ordered first.
4. Assign consecutive IDs in that order. Structurally identical keys are the same node.

Pin constructor tags and scalar vectors to the following grammar; all integer values are
compared numerically, not by host memory layout:

| Constructor/tag | Scalar vector | Ordered children |
|---|---|---|
| Sort / `0x0` | `[univIdx]` | `[]` |
| Var / `0x1` | `[deBruijnIdx]` | `[]` |
| Ref / `0x2` | `[refIdx, numberOfUnivs, univIdxs…]` | `[]` |
| Recur / `0x3` | `[recIdx, numberOfUnivs, univIdxs…]` | `[]` |
| Prj / `0x4` | `[typeRefIdx, fieldIdx]` | `[value]` |
| Str / `0x5` | `[refIdx]` | `[]` |
| Nat / `0x6` | `[refIdx]` | `[]` |
| App / `0x7` | `[]` | `[function, argument]` |
| Lam / `0x8` | `[binderContract.toBits]` | `[type, body]` |
| All / `0x9` | `[packAllContract(input,result)]` | `[type, body]` |
| Let / `0xA` | `[letContract.flags, binderContract.toBits]` | `[type, value, body]` |

There is no Share node in this input alphabet. Update the rule explicitly if the target
revision has additional semantic constructors/fields. The existing contract pack/unpack
theorems can justify the packed scalar keys. Hash tables and pointer caches may accelerate
discovery, but collisions must resolve by structural keys; hash equality alone is not the
normative identity. No metadata, names, allocator addresses or hash-map traversal order
participates in ID assignment.

### 3.3 Total minimization key

For feasible representation `e`, define:

```text
L(e) = byte length of the complete canonical serialized Constant
Q(e) = vector of structural IDs of its expanded sharing entries, in stored order
K(e) = (L(e), Q(e), serialized Constant bytes)

canonical(A) = the feasible e with lexicographically least K(e)
```

Compare `L` numerically, `Q` lexicographically as a vector of numeric IDs, and bytes by
unsigned lexicographic order. A proper vector prefix sorts first. The byte component makes
the final result unique after the table sequence is fixed.

This chooses a globally shortest encoding. It intentionally does **not** require the byte-
lexicographically first encoding across different table sequences. Both are canonical
definitions; this one supports the simpler exact DP below. Keep the distinction in docs
and tests. Minimum length is the primary criterion in every case.

## 4. Complete search space and proof obligations for reductions

Establish these facts before relying on the reduced search:

1. A table entry reachable from a root expands to a rooted subterm of that root.
2. Removing an unreachable entry preserves expansion and decreases length: surviving
   indices and the sharing-count width cannot increase.
3. Duplicate expanded entries are unnecessary. Redirect every use of the later entry to
   the earliest equal entry, delete it and reindex. Backwardness is preserved. A Share stays
   a Share, so telescope boundaries are unchanged; reference widths cannot increase. A
   positive-length entry is removed, so no minimum contains a duplicate.
4. Every remaining expression representation arises by choosing, at each occurrence,
   either its inline constructor or a reference to an equal available entry.

Hence all ordered subsets of the `N` distinct subterms, with all legal representation
choices for their entries and the roots, cover a minimum. Table order need not follow all
expanded-subtree edges: an earlier large entry can inline a subterm stored separately later.

Do not prefilter with the current positive-savings test, freeze current topological order,
force every occurrence of a selected term to use Share, or assume maximal DAG sharing is
byte-optimal. Each would exclude candidates that the exact specification allows.

Single-use elimination, dominance between subterms, decomposition into independent parts,
and restricted-model shortcuts may be worthwhile. They are optimizations only after their
soundness is established for the actual telescope, width and table-prefix cost model.

### 4.1 Reductions and bounds with proof sketches

These are the reductions the implementation may rely on. Each must be stated as a lemma
in the Lean development (P2/P3) before the optimized search uses it; the sketches here are
the intended proofs. Notation: `occ(t)` is the number of structural occurrences of subterm
`t` in the expanded roots, counted through every DAG edge with multiplicity and every
root occurrence; `size(t)` is `t`'s standalone inline byte length with no sharing.

**R1 — single-occurrence elimination.** If `occ(t) = 1`, no minimum stores `t`.
Proof: an entry for `t` can be referenced at most once (its one occurrence; no other
expression expands to `t`). If it is referenced zero times, §4(2) removes it. If exactly
once, replace that Share by the entry's own representation and delete the entry. The
replaced Share was a telescope endpoint; inlining a same-family constructor there merges
its header into the enclosing telescope, so the inlined bytes are at most the entry's
standalone bytes (one fewer if merged; if the merged telescope count crosses a Tag4 width
boundary, cutting again at the old boundary via the entry's own head still costs no more
than before). The Share (≥ 1 byte) disappears and all later indices decrease. Strict
decrease. Consequently candidates are exactly the subterms with `occ ≥ 2`, leaves included.

**R2 — one-byte terms.** If `size(t) = 1` (Var/Sort/Str/Nat with small index), no minimum
stores `t`: every reference costs ≥ 1 byte, so referencing never beats inlining, and the
entry itself costs ≥ 1 byte plus its Tag0 count unit. Generalize only with care: a term
with `size(t) = w` cannot profit from references of width ≥ w, but its width depends on
the final index, so that is a per-state prune, not a global one.

**R3 — unreachable and duplicate entries** are §4(2)–(3); keep them.

**LB — optimistic-dictionary lower bound for branch-and-bound.** At width-state `M` with
`k` entries stored, let `M⁺` grant every candidate term not in `M` a reference of width 1
and keep the widths of stored terms. Then
`F(M) + tag0Width(k) + fixedBytes + Σ_roots C_{M⁺}(root)` is a lower bound on every
completion of `M`: future entry bodies cost ≥ 0, references never get cheaper than width
1, and `C` is antitone in availability and monotone in widths. Any incumbent (unshared,
old heuristic, or the best certified-so-far) prunes states whose bound exceeds the
incumbent length; equal-length states must be kept for the tie-break (§6.3).

**Unit-width relaxation (sanity oracle, not the canonical rule).** In the model with no
telescope merging and every reference exactly one byte, the minimum is exactly “store every
positive-weight term with `occ ≥ 2`, in dependency order” (proof in the Astra addendum §6).
Use it as a test oracle for the width-state DP on inputs where telescopes cannot merge,
and as an optimistic estimate of how many entries the true optimum will have.

**Why the general problem is not obviously polynomial.** Sharing an ancestor reduces the
visible occurrences of its descendants, sharing a descendant shrinks the ancestor's body,
references cut telescopes, and only eight width-1 slots exist. The decision structure is a
fixpoint of an antitone operator (a parent and a child can each be profitable alone but
not jointly), which is the shape of independent-set-like problems. No hardness proof
exists either; P1.5 measures whether real candidate counts make the question moot.

## 5. Exact expression optimizer for a fixed dictionary

Let `M` map available expanded term IDs to their Share **byte widths**. Define `C_M(t)`
as the minimum byte length of a standalone expression expanding to `t` using those entries.
For materialization, additionally provide the chosen table sequence, which determines
the actual index of each available term.

For a leaf, compare its canonical inline bytes with its Share cost if available. For Prj
and Let, add the fixed scalar/contract header and optimal children. Whole-expression sharing
is also an option when its term ID is available.

For App, Lam and All, optimize the maximal matching spine explicitly. Suppose it has `l`
nodes, with each step's side children/contracts and a final nonmatching tail:

- Consider sharing the entire expression if available.
- For every inline prefix length `j` from 1 through `l`, charge the actual Tag4 header for
  `j`, every emitted contract byte, and each side child's optimal standalone cost.
- If `j < l`, the remaining matching spine can terminate that telescope only as a Share
  to the corresponding available subterm. Charge its reference width, or reject that cut
  if unavailable. Do not use an arbitrary inline representation of the same-family tail;
  the canonical writer would merge it back into the telescope.
- If `j = l`, charge the optimal standalone representation of the natural nonmatching tail.
- App traverses its function spine and emits arguments in the existing wire order; Lam/All
  traverse bodies and emit binder types/contracts in outer-to-inner order.

Memoize by `(dictionary-width state, term ID)` and share spine data/prefix sums where useful.
The scalar recurrence is polynomial per dictionary state; avoid enumerating the Cartesian
product of all child representations. Keep costs as exact naturals or sound checked values.

After selecting the winning table sequence, materialize each expression's shortest encoding
and choose unsigned byte-lexicographic order among equal-length options. Side expressions
are independent and their lengths add. A rope/DAG or streaming byte comparison may avoid
copying large tie candidates. Verify emitted bytes against the real serializer; an isolated
node-size estimate is not an acceptable substitute.

Required lemma: the recurrence considers every possible canonical telescope boundary and
returns the minimum standalone expression cost for the fixed dictionary. A plain bottom-up
choice of the cheapest standalone spine child is not sufficient because merging changes
the enclosing header cost.

## 6. Exact table selection and ordering

### 6.1 Width-state dynamic program

Share width is monotone in the index:

```text
shareWidth(i) = 1                         if 0 <= i < 8
             = 1 + minimum LE byte count if 8 <= i < 2^64
```

There are nine widths. A state assigns each term ID either absent or a width. Only states
reachable by filling consecutive actual index positions are valid; width 1 has capacity 8,
width 2 the next 248 positions, width 3 the next 65,280, and so on. Never freely assign a
cheap width beyond its capacity.

For state `M`, store `F(M)`, the least accumulated byte length of table bodies producing
that state. Also retain the lexicographically least term-ID prefix among equal-cost histories.
Start at the empty state with body cost zero. If `k` entries exist and `t` is absent:

```text
M' = M extended with t -> shareWidth(k)
candidateBodyCost = F(M) + C_M(t)
relax M' by (candidateBodyCost, priorTermIDSequence ++ [t])
```

The appended entry may use only the prior dictionary. Its own term is absent, so it cannot
refer to itself. Actual dependency order is satisfied by construction, including cases where
an earlier entry inlines a subterm that is added later.

At every reached state, evaluate stopping:

```text
totalLength(M) = F(M)
              + sum(C_M(root) for each ordered root)
              + tag0Width(k)
              + fixedNonExpressionConstantBytes
```

The fixed part includes ConstantInfo scalar fields, refs/univs tables and their lengths.
Account for the sharing-vector length exactly: Tag0 is one byte through 127 entries, two
through 255, then three, etc. There is no table-body concatenation telescope across entries.
Validate the decomposition against `putConstant` / `Constant::put` for every fixture.

Choose the stopping state by `(totalLength, retained term-ID sequence)`, then materialize
the byte-minimal expression choices for that sequence. This computes the full key in §3.3.

### 6.2 Why merging histories is exact

With the fixed grammar/tables, future expression **lengths** depend only on which expanded
subterms are available and each one's reference width. They do not depend on the exact
index within a width class or on previous entries' internal representations. Therefore a
larger accumulated body cost at the same state is dominated for every continuation.

On equal cost, same-state prefixes have equal length. Appending a common continuation
preserves their lexicographic order. Retaining the least term-ID prefix therefore preserves
the global secondary tie-break. It would not automatically preserve a different rule that
compared complete bytes before table IDs, since root bytes precede table bodies in the file.

A coarse bound is `10^N` states (absent plus nine widths) with `N` possible extensions per
state and polynomial expression optimization. Most assignments violate bucket capacities;
if `N <= 8`, the state is simply a subset, with `2^N` states. These are algorithmic upper
bounds, not a claim of necessary complexity or production-scale performance.

### 6.4 State representation

Never allocate `10^N` or `2^N` arrays. Represent a width-state as the sorted vector of
(term ID, width) pairs (equivalently the bucket sets), store reached states in a hash map
keyed by that vector, and expand states in order of `k` (entries stored) so that every
transition goes from layer `k` to layer `k+1`; the retained term-ID prefix for ties is
stored with the state. Per layer only the frontier is live. Meter states, transitions and
memo entries (§7) and fail closed when limits are hit.

### 6.3 Practical search and safe acceleration

Use the unshared encoding and old heuristic, when representable, to establish feasible
upper bounds. Exact-score improved candidates may tighten the bound. None of them proves
optimality. If the old heuristic's implementation can overflow on the input, skip that
upper-bound source; correctness cannot depend on it.

Branch-and-bound, A*, sparse subset states, memoization, parallel exploration and solver
backends are permitted if they compute the same minimum key. Every pruning condition needs
a proved lower bound or dominance argument. Do not prune equal-length branches that could
improve the canonical tie. Do not assume independent components are additive until shared
index capacities and the count prefix have been accounted for.

Keep an intentionally simple exact reference search for tiny inputs, independent of the
optimized search. The optimized implementation must agree with it, not merely beat the old
heuristic. A SAT/MILP backend is optional; a solver returning only a feasible incumbent is
not an exact-success result, and its proof/trust boundary must be explicit.

## 7. API, validation, resource accounting and arithmetic

Prefer a pure core over anonymous Ixon data, with explicit success/error results. Illustrative
API shapes, to adapt to the target repository's conventions:

```text
optimizeSharing(expandedRoots, limits)
  -> ExactSharingResult | SharingError

normalizeConstantSharing(constant, limits)
  -> Constant | SharingError

checkCanonicalSharing(constant, limits)
  -> canonical | noncanonical(expectedBytesOrDigest) | SharingError
```

`ExactSharingResult` contains rewritten roots and table, exact variable-byte cost, and
optional nonsemantic statistics. Full-Constant integration checks the fixed-cost accounting.
Failures distinguish malformed/cyclic sharing, index/format bounds, and resource exhaustion.
An optimizer must not return a truncated table, silently drop a root, wrap an index, or treat
the best feasible candidate as certified because its budget expired.

Meter distinct nodes, depth, states, transitions, memo storage, output bytes and tie-byte
comparison/materialization work. Avoid mandatory full tree expansion. Prefer deterministic
work counters for reproducible failures; wall-clock cancellation may abort but cannot select
a different successful encoding. Different limits may change success versus failure, never
the result of two successful invocations on the same input.

The semantic reference function can be total by finite search. The executable bounded API
returns an error when it cannot complete. Fuel/work limits are operational and must not
redefine the set over which “minimum” is claimed. Exposing a size cutoff as a smaller test
oracle is fine; silently using it as the production optimum is not.

Lean should reason with `Nat` costs and proved UInt64 conversion bounds. Rust must use
checked arithmetic or an equivalent exact bounded scheme. Logical occurrence counts and
unshared byte lengths may be exponential in the compact DAG size. Never rely on `usize` /
`isize` wraparound, or on `Nat.toUInt64` silently truncating. Saturation used only for
sound pruning must preserve the distinction between equal cost and strictly above the bound.

If normalizing an already shared Constant, expand against its table before optimization.
Applying the current `applySharing` again to Share-bearing roots is not normalization: the
function receives no old table and treats Share as a leaf.

## 8. Compiler, metadata and format integration

### 8.1 Both compiler routes and direct data callers

Build one explicit root extraction/reassembly interface per language. Derive roots from
ConstantInfo where feasible instead of accepting an unchecked second array. Validate lengths
and order during reassembly; do not use out-of-range fallbacks that leave stale expressions.

Route Lean definition/axiom/quotient/recursor/mutual/auxiliary compilation and Rust equivalents
through the exact implementation at the selected new construction version. Include kernel
egress, decompile/recompile routes and test FFI. Propagate errors through existing compiler
result types; do not preserve an infallible signature by returning the old heuristic on error.

Keep low-level Ixon decoding/encoding distinct from the expensive canonical-sharing check.
A caller must explicitly know whether it has only wire validity, well-founded share
expansion, or exact construction canonicality. Ixsy can invoke the pure normalizer/checker
without `Lean.Syntax`, `Lean.Expr`, elaboration or kernel typechecking.

### 8.2 Metadata invariants

Audit actual index spaces before remapping. At the inspected revision,
`CallSiteEntry.collapsed.sharingIdx` addresses the per-constant `metaSharing` vector, not
the block's `Constant.sharing` vector. Both start at zero. Do not offset collapsed indices
by the primary table length or merge these namespaces.

Metadata expressions may also contain Share references or extension refs/univs, according
to the pinned metadata format. If a payload depends on old primary entries, preserve its
logical expression by correct remapping or inlining before removing/reordering those entries.
Do not assume a one-to-one old/new slot map: the optimum can remove a previously stored term.
Preserve per-occurrence arena roots, binder data, call-site surgery, universe patches and
`Named.original`. A metadata-only edit must leave anonymous bytes unchanged.

Test mutual blocks with both shared anonymous terms and collapsed source call-site payloads.
Keep metadata optimization outside this primary-byte objective. Primary minimization does
not imply that the combined anonymous-plus-metadata artifact has globally minimum length.

### 8.3 Version and address migration

The inspected `docs/Ixon.md` and `Ixon.Env.VERSION` documentation require a version bump
when serialized bytes change, and require regeneration rather than old-version decoding.
The current header is v3 (`0xE3`). Follow the target repository's current policy: when making
the exact rule canonical for compilation, bump the coordinated format/construction version,
format IDs, manifest pins, readers/writers and golden fixtures. Determine the next version
from the actual target branch; do not hard-code a stale number from this plan.

The expression byte grammar need not change. Canonical construction and resulting addresses
do change. Do not silently redefine v3, invent an unrecorded per-file profile switch, or add
a multi-version decoder contrary to repository policy. The old heuristic may remain available
for research/regression comparisons and initial upper bounds; that does not make its output
canonical under the new version.

Recompile/regenerate affected artifacts and dependency addresses, environment roots, pins,
projection/member references, manifests and metadata address references through existing
production flows. Do not relabel an existing artifact with a new header while retaining
unverified contents. A standalone sharing normalizer should return the new Constant/address
and must not imply that it has migrated the whole dependent environment.

## 9. Proof and validation requirements

The formal target is a successful result's minimum **key**, not only wire well-formedness.
Organize Lean lemmas so the executable algorithm is connected to its specification:

1. Structural interning/ID determinism and collision-independent equality.
2. Share expansion correctness, bounds and backwardness, including all expression contracts.
3. Removal of unreachable/duplicate entries and completeness of ordered distinct subterms.
4. Exact serializer length decomposition, including all telescope and integer boundaries.
5. Fixed-dictionary recurrence soundness and completeness; materialization attains its cost
   and the least bytes among tied representations.
6. Width-state sufficiency, Bellman recurrence, history dominance and term-ID tie preservation.
7. Successful full optimizer output minimizes the specified key over all feasible encodings.
8. Determinism, preservation of resolved AST, and idempotence of expand-then-normalize.
9. `size(exact) <= size(unshared)` and `size(exact) <= size(old heuristic)` whenever those
   candidates are valid for the same problem; derive these from minimality.
10. Connection to the real Constant builder, Lean/Rust parity tests, and existing compiler
    codec/verification endpoints after the integration changes.

Do not establish a similarly named property of a detached toy encoder and present it as a
production theorem. Follow existing axiom/audit conventions; introduce no new `sorry` or
untracked axioms. If a proof milestone remains open, identify its exact statement and mark
the PR incomplete/draft rather than asserting the acceptance gate passed.

Tests must include:

| Group | Required coverage |
|---|---|
| Tiny exhaustive oracle | All table orders and independent occurrence choices; compare full key, not only size or expansion |
| Known regressions | 19→17 witness; heuristic worse than unshared; same selected entries with hot slot 8; two 25-byte minima and deterministic tie |
| Telescope behavior | App/Lam/All, nested/mixed constructors, different contracts, natural ends vs internal Share cuts, one term used in different spine contexts |
| Widths | Share 7/8, 255/256, 65535/65536 and remaining UInt64 boundaries; telescope length boundaries; Tag0 table counts 127/128 and 255/256 |
| Ordering | A parent stored before an independently stored descendant by inlining; actual backward refs; arbitrary incoming table orders after logical expansion |
| Semantic coverage | All ConstantInfo/MutConst kinds, multiple roots, all contracts, projections, no-expression constants, refs/recur/str/nat and universe indices |
| Representation independence | Different pointer/DAG/alias layouts; allocation order; map iteration; repeated DAG edges; different incoming valid encodings of the same AST |
| Safety and bounds | Bad indices, cycles, forward refs according to API policy, depth/state/output exhaustion, overflow, empty input, no silent partial success |
| Metadata | Per-occurrence metadata, call-site/eta surgery, collapsed payloads, metaSharing namespace, universe patches, original records, metadata-only edits |
| End-to-end | Lean/Rust byte equality, decode/encode equality, normalize fixpoint, compiler/decompiler roundtrip and new-format migration |

Large numeric boundary tests should exercise scalar helpers and forced dictionary states;
do not attempt `2^65536` exhaustive optimization to check a three-byte index. Reduced-width
model tests can exercise multi-bucket state merging, but cannot replace tests of actual
format widths. Generate small legal ASTs with an independent exhaustive oracle and shrink
failures to a saved counterexample.

## 10. Implementation sequence and acceptance gates

### P0 — Rebase the inventory and freeze the specification

Read target instructions, inspect callers/validators/format policy, and move this spec into
tracked Ix documentation. Pin the feasible backward-reference class, the exact key and
structural IDs above. Record any necessary revision-specific adaptation explicitly. Confirm
there is no frontend dependency in the public data API.

Deliver: reviewed spec, integration map and portable golden fixtures. Do not begin by
changing the existing heuristic's score and calling it canonical minimum.

### P1 — Independent oracle and serializer costs

Implement the tiny all-order/all-occurrence reference optimizer and exact size helpers.
Port the known fixtures; compare actual complete Constant bytes in Lean and Rust. Verify
the structural-ID ordering and key comparison independently.

Deliver: reproducible exact minima and tie vectors; scalar/telescope cost tests.

### P1.5 — Corpus measurement gate (run before designing P3 at scale)

Using the `init.ixe` corpus (§0), build a harness (`Benchmarks/SharingStudy.lean`, exe
`sharing-study` in `lakefile.lean`) that, for every constant: expands the stored table,
recovers the ordered roots, and reports (a) distinct subterms `N`, (b) candidates after R1
and R2, (c) the current table size, (d) `rawBytes.size`, the unshared size, and the size
the current heuristic reproduces from the expanded roots (must equal `rawBytes.size`;
count any mismatch as a harness bug). Report the distribution (percentiles, max, the ten
largest) and the total bytes. This decides P3's design: if candidates are small for almost
all constants, the sparse width-state DP with LB pruning is the production algorithm and
the remainder needs a resource-error story; if candidates are routinely in the hundreds,
additional proved reductions are required before any migration and the plan must be
revised. Report the numbers; do not pick a fallback silently.

### P2 — Fixed-dictionary optimizer

Implement every constructor and telescope recurrence with witnesses/materialization.
Compare it against enumeration over tiny dictionaries, including arbitrary dictionary order
and mixed inline/reference choices. Add the corresponding proofs.

Deliver: exact expression costs and byte-minimal witnesses for any fixed legal dictionary.

### P3 — Global exact search

Implement width-state DP, history tie-breaking and bounded error behavior. First establish
agreement with the unoptimized oracle, then add safe pruning, caching and fast paths with
separate correctness arguments. Keep cost computation and final materialization separate
where that saves memory.

Deliver: full-key minimum on successful calls, with state/transition/memory statistics and
an arbitrary finite-input reference algorithm. No heuristic fallback within the exact API.

### P4 — Production viability measurements

Benchmark actual singleton constants and mutual blocks from the repository's available
Init/Std/Lean and representative project compile fixtures. Include artificial nested sharing,
long spines, many independent candidates and index-boundary cases. Record distinct-subterm
counts, retained candidate counts after proved reductions, visited states/transitions,
old/unshared/new bytes, wall time, peak memory and all resource failures. Report distribution
and worst cases; a tiny witness's speed is not a production benchmark.

The naive exponential DP may be unusable at production sizes. Treat that as a concrete
performance result requiring additional exact reductions/algorithms or an explicit adoption
decision. Do not hide it behind a cutoff that changes the canonical result. Resource limits
must be documented and exercised, and ordinary compiler fixtures must not start failing
silently. An exact library plus an unready default migration is not a completed integration.

### P5 — Integrate and migrate

Switch all selected-version compiler/data routes together, propagate errors, preserve
metadata, update proof endpoints and bump the coordinated version under repository policy.
Regenerate fixtures and artifacts through their producers. Add explicit canonicality checks
at callers that require them without making every raw decode run the optimizer implicitly.

Deliver: matching Lean/Rust canonical output, intact roundtrips, version/address migration
evidence and reusable direct-Ixon entry points for Ixsy.

### P6 — Validate and submit the Ix PR

At the inspected revision, relevant commands include the following; refresh them against
the current toolchain and target's CI instructions:

```text
cargo test -p ixon
cargo test -p ix-compile
lake test
lake build IxCompileVerify
```

Run the focused exact-sharing/differential tests during development, then the affected
compile/decompile/codec and audit suites required by CI. Check formatting/lint using the
repository's documented commands. Include command outcomes and benchmark data; do not
claim a blocked or unrun check passed.

Create the branch and PR in Ix with a description that leads with the concrete failure:
the current canonical construction can encode `T2 → T2` in 19 bytes although 17 is possible,
and can even exceed unshared size. Explain the exact minimum key, backward-reference scope,
Lean/Rust integration, resource semantics, version/address impact, proof coverage and
measured performance. Link tracked tests/docs/benchmarks, not only this ignored research
directory. Keep the PR draft if any required acceptance gate remains unresolved.

The PR is complete when the implementation computes the specified minimum key on success,
all integration/version/metadata paths are coherent, required proofs and checks pass, and
production performance and failure behavior have been reported honestly. A deterministic
compression improvement alone does not satisfy this handoff.

## 11. Parallel workstreams

Independent agents own disjoint files; each works in its own worktree from `ix-sharing`
and commits to its own branch, and the integrator merges. Cross-stream interfaces are the
spec above (structural IDs §3.2, key §3.3, recurrence §5, DP §6) and the golden fixtures
in §2. Every stream reports verified facts only: commands run, their output, and what was
not run.

| Stream | Owns | Deliverable |
|---|---|---|
| W1 Lean exact core | `Ix/Sharing/Exact.lean` (new; split as needed), `Tests/Ix/SharingExact.lean`, `Tests/Main.lean` suite entry | Structural IDs, bounded share expansion, exact serializer-length helpers checked against `putExpr`, tiny all-order/all-occurrence oracle, fixed-dictionary telescope DP with materialization, sparse width-state DP with LB pruning and resource errors; P1–P3 tests including every §2 fixture |
| W2 Rust exact core | `crates/ixon/src/sharing_exact.rs` (new), its tests, `crates/ffi` differential hook | Same algorithm and key, checked arithmetic, differential test against Lean bytes via the existing FFI parity harness pattern (`Tests/Ix/IxonV3FFI.lean`) |
| W3 Corpus measurement | `Benchmarks/SharingStudy.lean`, `lakefile.lean` exe entry, `docs/sharing-minimum-measurements.md` | P1.5 numbers on `init.ixe`; once W1 lands, rerun with the exact optimizer under explicit limits and report success rate, byte savings vs heuristic, states/transitions and wall time |
| W4 Integration (after W1–W3 review) | `Ix/CompileM.lean`, `crates/compile`, metadata remap, version bump, proofs, docs | P5–P6 |

Do not start W4 until the P1.5 gate has been evaluated and the exact cores agree on all
fixtures.

## 12. Decision record after gate P1.5 (2026-09-30)

Measurements are in `sharing-minimum-measurements.md` (Init corpus, 55,386 rooted constants).

### 12.1 The width-state DP is not a production algorithm

Candidates after R1/R2 have median 34, p90 232, p99 1,187, max 22,458. Only 17% of constants
have ≤ 8 candidates. The exact search of §6 stays as the **oracle** for small inputs
(`Ix/Sharing/Exact/*`, suite `exact-sharing`) and is not the canonical construction.

### 12.2 The in-degree rule (MSS) beats the heuristic

“Store every compact-DAG node with in-degree ≥ 2 (edge multiplicity + roots) and standalone
size > 1; reference every occurrence; priority topological order” is the exact minimum of the
additive unit-width model. On Init it is 14.5% smaller than the heuristic in total, smaller
on 90.6% of constants, larger on 0.4% (total loss 933 bytes, max 50), never larger than
unshared, and reproduces the 17-byte and 46-byte witnesses. Its losses are all in tables
with > 8 entries, i.e. the index-tier effect.

### 12.3 Uniform reference width makes the exact minimum tractable

In the **uniform width model** (every Share costs `w` bytes, everything else the real Ixon
cost including telescopes and the Tag0 count prefix) adding a stored term never raises any
other node's cost, so the exchange argument of §4.1 classifies every candidate with DAG-only
bounds (`deg`, `headdeg`, `occ`, width-aware `payloadMin`/`payloadMax`):

| w | certain-stored | certain-excluded | uncertain | largest uncertain component p99 / max |
|---|---:|---:|---:|---|
| 1 | 80.5% | 0% | 19.5% | 4 / 45 |
| 2 | 64.1% | 14.9% | 21.0% | 5 / 44 |
| 3 | 54.4% | 24.3% | 21.3% | 6 / 44 |

Uncertain nodes interact only along DAG paths that avoid certain-stored nodes, so they split
into components (≤ 8 nodes for 99.7% of constants). The canonical algorithm is therefore:
classify → exhaustive search with a sound lower bound per component (cost via the §5
fixed-dictionary DP with all certain-stored terms available) → pinned dependency order
(in-degree descending, structural ID ascending). Its minimality proof is: exchange lemmas
for the two certain classes, independence of components, completeness of the finite search.
This is being implemented as `optimizeSharingUniform` (W1).

### 12.4 Format change: fixed per-constant Share width (proposal)

To make the uniform model the real byte count, the Share width must not depend on the index.
Proposal **D**: one width per constant chosen by the AST's candidate count `K` (deg ≥ 2 and
size > 1; an AST property, so the width never depends on the chosen table): 1 byte when
`K ≤ 16` (4-bit index in the tag's low nibble), 2 bytes when `K ≤ 4096` (12-bit index),
3 bytes otherwise (20-bit index). Cost measured on the MSS encoding vs today's index tiers:
+0.93% bytes (+638,883 on Init; MSS stays 13.7% below the heuristic). Alternatives measured:
B (2/3 bytes, cut at 2048) +2.07%, C (B plus 1 byte ≤ 8) +1.69%. Under D, 31,200 Init
constants use 1-byte references, 24,180 use 2, 6 use 3.

Decoder impact: the Share tag `0xB` changes from Tag4 to “flag nibble + index bits”, and the
reader must know `w` before the roots. Either write `K` (or `w`) in the constant header
before `ConstantInfo`, or move the sharing table ahead of the info. Everything else in the
grammar is unchanged. Backward references remain the feasible class (`SharingWF`).
**Status: proposed, awaiting decision.** Until decided, the exact uniform algorithm is
implemented parameterised by `w` and measured under scheme D's width choice.

### 12.5 Revised workstreams

- W1: `optimizeSharingUniform` + differential tests against the width-state oracle.
- W2: Rust port of the same, plus differential FFI test.
- W3: rerun the corpus with the exact uniform optimizer (bytes vs MSS/heuristic, class and
  component statistics, wall time, resource failures).
- W4 (after the format decision): Share width encoding, header field, `SharingWF`/codec
  proofs, compiler routes in Lean and Rust, metadata remap, version bump, fixtures.

### 12.6 Corrections from the W1 implementation (pinned rules)

- **R1 is an exchange, not an exclusion.** An in-degree-1 term `t` can be referenced once
  per inline write of its unstored parent `p`. Storing `p` instead (or turning extra writes of
  `p` into `Share(p)`) never increases length, so *some* minimum uses only in-degree ≥ 2 terms
  and the minimum length is unchanged, but ties exist. The canonical construction is defined as
  the minimum over tables whose entries have in-degree ≥ 2; "certain-stored" means "in every
  minimum of that class".
- **Continuation-only terms (`headdeg = 0`)** subtract the full `tag4Size(spine length)` of the
  entry's own telescope in the gain, not 1.
- **Certain-stored** requires gain ≥ 2 at the lower bounds (absorbs a Tag0 count boundary);
  **certain-excluded** is `(occ − 1) · size < occ · w` with exact `occ` and unshared size.
- **Count brackets:** when the stored count reaches a Tag0 boundary a knapsack over components
  decides which entries to drop.
- **Tie-break among minimum-length stored sets:** compare indicator vectors over structural IDs
  ascending, preferring "not stored" at the first difference (the smaller ID in the symmetric
  difference is left out). Decomposes over components. **Table order:** stored descendants
  first, then larger in-degree, then smaller ID.
- Lean (`Ix/Sharing/Exact/Uniform.lean`) agrees with the width-state reference on 400 generated
  inputs at w ∈ {1,2,3,5}; corpus measurement is W3's next task.

### 12.7 Tier layouts measured (MSS encoding, Init)

| Layout | 1-byte | 2-byte | Δ vs Tag4 tiers | worse constants |
|---|---|---|---:|---:|
| Tag4 (A) | 8 | 256 | — | — |
| F: two marker bits | 8 | 1,024 | −1.45% | 0 |
| G: nibble escapes 14/15 | 14 | 256 | −1.21% | 0 |
| D: fixed per constant | 16 | 4,096 | +0.93% | 23,342 |

Recommended layout **TagN** (nibble-bootstrapped) (formerly "TagN"): nibble `[L][M][c1][c0]`; `L=0` → 3-bit index; `L=1,M=0` → 2 bits +
1 byte (8..1031); `L=1,M=1,c∈{0,1,2}` → 2/4/8 following bytes (offsets continue; `c=3` invalid).
Bijective (each index has one encoding), capped only at 2^64 like every other count.
Two-phase construction (uniform-model selection → exact 8-slot allocation + pinned order →
re-materialisation under real widths) is being implemented parameterised by the layout.

### 12.8 Decision (2026-09-30): two-phase canonical construction with the TagN Share layout

Chosen over fixed-width D. Canonical sharing of a constant is `canonicalSharingTiered tagN`
(`Ix/Sharing/Exact/Tiered.lean`): phase 1 exact uniform-model selection at the nominal width
from the candidate count; phase 2 exact first-tier (8-slot) allocation, pinned priority order
beyond; phase 3 per-part re-materialisation under real widths. Each phase's optimality claim is
stated in its docstring; the width-1 model length is a provable lower bound on any encoding and
is used to report the gap. The Share tag `0xB` adopts the TagN nibble layout (no header
change, backward references unchanged, bijective so no canonical-integer check is needed).
Open: whether to adopt the TagN code for all Tag0/Tag4 integers (W3 measuring). W4
integration starts once the Rust uniform/tiered port agrees with Lean on fixtures.
