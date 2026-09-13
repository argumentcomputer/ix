# Aiur bug inventory

This records the fixes completed during the C8 work, including the subsequent
graph-decoder and constant-degree repairs. The nine main entries group
related failures by cause: four demonstrated verifier soundness defects,
three compiler defects, one reference-evaluator defect and one constraint
construction defect. Regression cases
are counted separately from bug classes.

| Defect | Observed failure | Implemented repair and regression evidence |
| --- | --- | --- |
| Inactive rows could supply results | An inactive function row supplied a false public result: `3 * 5 = 16` verified. Its return multiplicity remained nonzero while its computation constraints were disabled. | Enforce `multiplicity * (1 - selector) = 0` for function and memory rows. The supplied false result now rejects; local tests cover every grouped member and inactive memory rows. [Activity regressions](../crates/aiur/src/synthesis/tests/acceptance.rs), [checked arithmetic](../Ix/Aiur/Proofs/Activity.lean). The function forgery was demonstrated; the same missing condition was repaired in memory. |
| Cyclic calls could justify themselves | `f(x) = f(x)` admitted a public proof without any finite execution. A row's return could balance both the public request and its own recursive call. Mutually recursive rows could do the same. | Add range-checked 48-bit call ranks and nonnegative gaps, enforcing strict rank increase along constrained calls. Self/mutual cycles, equal/reversed ranks and attempted wraparound reject; finite recursion and shared callees verify. [Self-cycle regression](../crates/aiur/src/synthesis/tests/acceptance.rs), [rank and mutual-cycle regressions](../crates/aiur/src/synthesis/tests/call_order.rs), [well-foundedness proof](../Ix/Aiur/Proofs/CallOrder.lean). |
| A rank could be interpreted as an output | A function returning no values at rank seven verified against a public claim with output seven. Zero padding made the different message boundaries indistinguishable. | Check public channel, function visibility, input/output arity, constrained-call arities and continuation yields. The displaced-rank claim now rejects. [Native regressions](../crates/aiur/src/synthesis/tests/lookup_shapes.rs), [structural checks](../Ix/Aiur/LookupShapes.lean), [padding proofs and counterexample](../Ix/Aiur/Proofs/LookupMessages.lean). |
| The branchless optimization admitted inactive lookup writers | An empty match branch still contained a store lookup. Because the circuit had only one terminal selector, the optimization emitted its arguments without gating; they changed a live call's channel into a memory channel. Output seven verified for a program whose result was one, with all local equations and construction checks satisfied. | Require a single function with terminal control and one selector before omitting argument gates. Constraint emission and lookup grouping use the same decision. The forged result rejects and the honest result verifies. [Supplied-witness regression](../crates/aiur/src/synthesis/tests/branchless.rs), [unique-writer proof](../Ix/Aiur/Proofs/BranchlessSlots.lean). |
| Let hoisting changed effect order | Five programs reversed observable writes: array-update arguments, an operand before a later argument's lets, an I/O operation before its continuation, tuple elements and array elements. Both bytecode engines disagreed with both source evaluators. | Normalize each argument completely in source order; preserve operation/continuation sequencing; evaluate an array update's new value before its array in both normalization and lowering. The five cases now agree across all four evaluators. [Compiler regressions](../Tests/Aiur/Hoisting.lean), [normalization](../Ix/Aiur/Stages/Source.lean), [lowering](../Ix/Aiur/Compiler/Lower.lean). |
| Hoisting captured a shadowed variable | `let x = 10; (let x = 3; x) + x` compiled to six instead of thirteen. | Use distinct local names during argument normalization and preserve lexical scope during renaming. Renaming also preserves shared binders in pattern alternatives and local function-call occurrences. The `lexical-binding-scope` regression returns thirteen in both bytecode engines. [Regression](../Tests/Aiur/Hoisting.lean), [implementation](../Ix/Aiur/Stages/Source.lean). |
| Inlining lost the callee's return boundary | An explicit tail return was rejected after inlining; an early return escaped its callee and produced seven instead of ten in the caller. | Retain a normal call when the expanded callee contains an explicit return. Both tail-return and early-return cases pass in both bytecode engines. [Regressions](../Tests/Aiur/Hoisting.lean), [inlining guard](../Ix/Aiur/Stages/Source.lean). |
| The source reference skipped debug-argument effects | An argument that wrote one before a continuation wrote two produced `[2]` in the source reference and `[1, 2]` in the source interpreter. | Evaluate the optional debug argument, including its errors and early returns, before the continuation. The ninth compiler/reference fixture requires `[1, 2]` across all four evaluators. [Regression](../Tests/Aiur/Hoisting.lean), [reference evaluator](../Ix/Aiur/Semantics/SourceEval.lean). |
| Constant folding could crash constraint construction | The honest source program `eq_zero(0 * x)` panicked: the expression folded to a constant, but its independently tracked degree remained one. The emitter asserted that a constant must have degree zero. | Take the constant shortcut only at tracked degree zero; otherwise emit the usual two auxiliary columns and equations, as reserved by the compiler and witness generator. Six source variants verify at four inputs under singleton and grouped circuits; eight altered public outputs reject. A further 768 native/Lean row assignments compare outputs, metadata, column allocation and constraints. [Source/proving regressions](../Tests/Aiur/ConstantDegree.lean), [native regression](../crates/aiur/src/synthesis/tests/constant_degree.rs), [valued emission](../Ix/Aiur/Proofs/OperationRows.lean). |

The activity, rank and branchless AIR repairs change affected verification
keys; those systems need rebuilt keys. The arity repair adds validation without
changing AIR columns or expressions. Compiler fixes required regenerating the
three Rust VM files; generated-code parity and the existing VM checks passed.
The compiler repairs have regression coverage and supporting lemmas; complete
preservation proofs for normalization and inlining remain open.

Three additional implementation bugs were fixed during this work:

- **Deduplication emitted panic diagnostics for invalid callees.** Unchecked
  indexing printed panic messages even when the process returned success.
  Explicit default lookups preserve the previous result with empty stderr.
  The original 23-program syntax/remapping corpus still matches exactly.
  [Deduplication](../Ix/Aiur/Compiler/Dedup.lean),
  [compatibility and adversarial tests](../Tests/Aiur/Dedup.lean).
- **A proof example caused an import-time allocation failure.** The newly
  introduced symbolic memory counterexample was initially a closed array of
  `p + 1` rows, so native initialization attempted to allocate it. Making the
  period an argument keeps the example symbolic in theorem statements and
  avoids eager allocation. [Corrected example](../Ix/Aiur/Proofs/Memory.lean).
- **Malformed key graphs could panic during decoding.** A self-referencing
  node indexed an empty degree vector. The regression now returns an error.
  The decoder also checks forward references, root and column bounds,
  stage-two reads in lookup prefixes, degree overflow and incorrect maximum
  degrees before constructing a graph for evaluation. Valid keys retain the
  same bytes. This native decoder currently has no production callers in the
  workspace; serialization is the connected key path. No accepted false claim
  was demonstrated for this failure. [Decoder regressions](../crates/aiur/src/vk_codec.rs),
  [read-layout checks](../crates/aiur/src/graph_shape.rs),
  [checked graph evaluation](../Ix/Aiur/Proofs/ExpressionGraph.lean).

Several checks were added to discharge proof obligations without a demonstrated
accepted false claim for each one: checked deduplication with identity fallback,
global lookup-count/overflow bounds, and circuit membership/control-count
validation. Total comparison, hashing and tail-match definitions also removed
partial implementation boundaries. These are tracked in the
[verification documentation](kernel-verification.md); they are not additional
observed semantic bugs in the nine-entry count above.

Subsequent fixed-table hardening adds explicit activity and height checks at
the Aiur verifier boundary. The generic shape check permits altered byte-table
degree metadata and inactive fixed tables; the current PCS rejects an inactive
committed matrix without opening points. Aiur now requires fixed tables active
at their exact preprocessed heights before checking openings. The four native
regressions and all 17,910 native/Lean guard cases pass. This is not an additional
demonstrated false-claim acceptance. [Guard and regressions](../crates/aiur/src/synthesis/tests/byte_shapes.rs),
[checked model and column extraction](../Ix/Aiur/Proofs/ByteColumns.lean).

The separate effectful-call memoization mismatch remains unresolved:
the reference evaluators omit the runtime cache, so repeated identical calls
can have different I/O behavior. This mismatch is not counted as fixed here.

The subsequent byte-column checkpoint passes 54 parallel release Rust tests,
release Clippy with warnings denied, nine compiler/reference regression programs,
nine native comparison corpora, the complete Aiur component gate and all 1,345
broader execution/cost/proving assertions. Its exact audit covers 308 roots.
These results do not establish the remaining native verifier,
compiler and certified semantic/cryptographic obligations of full C8.

The graph checkpoint adds the decoder regression and passes all 59 parallel
release Rust tests, release Clippy, eleven native comparison corpora and the
complete component gate. Its 338-root audit preserves every earlier root,
frozen definition and worker body. The new graph corpora compare 88,228 layout
checks and 240 assignments across ten actual native graphs.

The constant-degree repair preserves the original 6,240 operation-row records
byte for byte. Its exact audit changes only the `eq_zero` branch of the frozen
valued emitter; all 338 theorem statements and axiom sets remain unchanged.
The native release suite passes 61 tests and release Clippy. This failure
prevented honest proof construction; it did not demonstrate acceptance of a
false claim. Existing programs that built successfully retain their emitted
AIR, column layouts and verification keys.

The frontend checkpoint connects symbolic addition, subtraction, multiplication
and equality-test emission to the valued model. All 1,752 smart-constructor
trees, 9,804 scalar emissions and 46,224 evaluated assignments match the actual
Rust frontend. Its 388-root audit preserves the repaired emitter and all 338
earlier root statements, axiom sets and worker bodies. This proof work adds no
new observed bug class; full compiler and cryptographic soundness remain open.

The base-graph checkpoint extends reflection through node sharing, graph folds,
constraint-root canonicalization and ordered lookup compilation. Its 425-root
audit preserves every earlier statement, axiom set and frozen definition.
All 1,484 native base graphs, 38 rejected specifications and 11,872 assignments
match Lean. This work adds no observed bug class; Rust refinement, extension
expansion and the cryptographic reduction remain open.

The operation checkpoint covers symbolic emission for all 34 operations,
complete sequences and lookup-slot accumulation. All 1,752 native sequences,
7,008 assignments and 438 cases with shared slots match exact expression trees
and evaluated results. Its 520-root audit preserves all prior statements,
axiom sets and frozen definitions. It adds no observed bug class or native AIR
change.

The block/circuit checkpoint extends symbolic reflection through recursive
branches, continuation merges and grouped circuit construction, then composes
it with base-graph compilation. All 384 native block trees / 1,536 assignments
and 96 native circuits / 384 assignments match exact expressions and valued
results. Its 586-root audit preserves every earlier statement, axiom set,
frozen definition and recursion worker. No new bug or native AIR change was
found. Rust refinement, accepted-proof extraction, earlier compiler passes
and the certified semantic/cryptographic endpoint remain open.
