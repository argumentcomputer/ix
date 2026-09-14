# Aiur proof migration audit

The source reference is `126000646da3324c26bd21a323b75819b8e2cc21` on
`jcb/monorepo`. The destination retains the newer kernel base and the
optimized Aiur implementation, including checked component layouts. This
review covers the migrated component boundary, not completed IxVM soundness.

The reviewed report contains 1,574 roots, 988 premise definitions and
197 recursion workers. Compared with the source report, 2,607 sections are
unchanged. No theorem root was removed. There are 58 changed root statements,
21 changed premise sections and one changed worker; 30 roots, 34 premises
and eight workers were added. One obsolete premise and seven workers from
the source implementation were removed.

| Changed boundary | Reason and reviewed scope |
| --- | --- |
| `opLayout_lookupUsage`, `opsLayout_lookupUsage`, control/block lookup usage, allocation branch lemmas and emitter allocation | The generic emitter uses six gap columns and four logical lookup slots per constrained call. These results now require an empty call-rank table. General allocation uses `Op.allocationFor`, covering zero, boundary and ordered ranks. |
| `finishCompilation`/`compile` lookup layout, lookup bounds, computed layout and column bounds; their `Backend` extraction, compilation and graph corollaries | The optimized component pass changes physical layouts. The migrated generic corollaries explicitly require `source.componentRanks = false`. This premise marks the remaining component-mode extraction obligation. It is not an assertion that the optimized IxVM already satisfies the old layout. |
| `emitCall_reflects`, valued/symbolic call emission, `CallsEmitted`, `TracksCalls`, `Op.allocation` | The child rank is `parent + 1 + packedGap`; there is no separate child column or order constraint. `EquationAvailable` permits a proved zero or an emitted equation. The derived order polynomial is proved identically zero, and satisfaction still follows in both cases. |
| `rewriteOp_layout`, `matchLayout_rewrite`, `rewriteCtrl_layout`, `rewriteBlock_layout` | Function renaming preserves layout when the selected call modes agree under the renaming. The statements compare executions from a supplied state with `LayoutRenaming`; the empty mode table satisfies this condition. |
| `SameCode.mk`, compilation, deduplication and grouping definitions | Component relayout changes continuation metadata. `SameCode` now compares complete block evaluations for every ambient program, fuel and state, while retaining function count and input arity. Relayout's proof establishes this relation directly. Deduplication and grouping retain the new metadata fields. |
| Valued and symbolic `circuitEmission` | An empty circuit emits no rank-range messages. This matches the native builder and was checked against empty-circuit, row and compiled-key corpora. |
| All changed `CompiledKey` constructors, success/selection/reflection lemmas, `CompiledBackend.circuits_bound`, `byte_graphs` and `circuits_preprocessed_absent` | Key reconstruction applies production lookup retuning using `key.parameters.logBlowup`. Success lemmas retain graph and physical dimensions and prove validity; fixed baseline grouping is no longer a conclusion. Exact key equality includes the selected grouping and degree. `circuit_success` now also uses `propext`; its prior axiom set was only `Quot.sound`. |
| Hoisting/inlining premises and the changed `hoistLetsAux` worker | The destination's fresh-name supply, function/argument freshening and unary/binary/list sequencing are retained. The obsolete `bindArguments` premise is replaced with the actual definitions. Targeted fixes preserve value-before-array update order and retain normal calls for explicit-return callees. Reference/native effect-order and return-boundary cases pass; general source reflection remains open. |

The new roots prove layout context and arity preservation, complete evaluation
preservation by relayout, empty-table specialization, mode-compatible
renaming, the derived call-order identity, and preservation of authored fields
by lookup retuning. Their premise bodies include the actual checked component
assignment and the total cost selector with machine-size and overflow guards.

The removed workers are the old `blockLayout`/`ctrlLayout` traversals,
`Pattern.freshenBindings`, `Pattern.maxNameLength`, `Term.bindArguments`,
`Term.freshenWith`, and `Term.maxNameLength`. Their replacements are the
two component DFS workers, `relayoutBlock`/`relayoutCtrl`, `Pattern.locals`,
`Pattern.mapLocals`, `Term.freshBound`, and `Term.freshen`. Each worker is
followed to its checked safe source declaration and its implementation is
included in the frozen report. The DFS proposal is independently validated
before it affects layout; the proof does not assume the proposal is correct.

The exact root axiom sets contain only ordinary Lean logic. The project
runtime boundary still contains `AiurSystem.build`, `AiurSystem.verify`,
`AiurSystem.vkBytes`, and `Proof.ofBytesChecked`; the same three partial
Hashable/Repr sources remain inventoried. There are no additional unsafe
runtime definitions, replacement implementations or excluded `Ix.Compiler`
imports. These runtime checks do not prove native verifier refinement.

Validation includes all 40 native/model corpora, four unchanged compiler
compatibility snapshots, and a retuned-key corpus covering 12 systems,
180 circuits, 720 assignments and 168 rejected validly encoded alterations.
The full `check-aiur` gate additionally compares the current report byte for
byte with the frozen manifest.

## Native component and physical-trace execution

The next reviewed boundary extends destination checkpoint
`11be019508abe48573cdb11063c3db8b40f1c607`. It adds 167 roots and 72 premise
definitions: 1,741 roots and 1,060 premises in total. The previous boundary
retains every root, premise and worker. Fifty existing root statements and
20 premise sections change; six worker implementations change and seven
workers are added, for 204 workers. Existing root axiom sets are unchanged.
The new roots use only the standard Lean axioms: one is axiom-free, ten use
`propext`, 35 also use `Quot.sound`, and 121 also use `Classical.choice`.

| Boundary | Reviewed meaning |
| --- | --- |
| Shared operation, block and member emission | An explicit call-rank table selects zero, boundary or ordered layout. Execution, call inventories, inactive rows, input preservation, auxiliary allocation and lookup cursors carry that same table. The empty-table default retains the fallback semantics. |
| `CallRankChecks`, component edge collection and finite execution | Every call still has its complete function message. Only same-component calls require gap ranges and the derived order equation. The actual constrained calls are included in the checked bytecode edge inventory. A boundary call's rank is bound by its active callee provider; an acyclic provider returns rank zero. |
| Component circuit members, queries and returns | Each member starts at its native column and slot offsets. Rank-range messages are gated by ranked members. Boolean selectors and checked branch/return counts imply query exclusivity, return selection and the terminal single-writer condition, including mixed circuits and empty circuits. |
| `compileNativeCircuit`, `CompiledKey.functionCircuit`, `CompiledKey.check` | The compared key chooses its emission policy from the actual component table. The global check rejects malformed nonempty component tables even when there are no function circuits. Constructors check physical read bounds, positive slot counts, raw query slot ranges and fallback member extents. Lookup retuning remains part of exact key equality. |
| `CompiledBackend.function_graph_reflects` | The former generic-layout premise is removed. The conclusion uses the selected native emitter and derives positive slot counts and bounds. Array widths and the successful checked constructor supply all physical reads; no graph-equality premise is added. |
| Component rows and the global pool | Provisional physical providers are interpreted before local execution is established. A single padded balance and a consumer count below the characteristic supply active callees and byte ranges. Local validity of the provisional table and separate function/byte balance are not premises of the physical endpoint. |
| `GraphSatisfied`, `graphLookupData`, `graph_trace_execution` | Function and memory matrices follow the actual key order and active-height metadata. Finite physical main rows supply valued witnesses. Every graph lookup is preserved in row/slot order; slot zero remains a provider regardless of its field multiplicity. Canonical byte columns and memory graph lookups supply the other providers. The endpoint proves the selected finite execution and functional memory. |
| Key trace metadata and `checked_graph_trace_execution` | Physical graph slot counts equal the execution trace's logical counts, including fallback/component layouts and all auxiliary tables. Fixed heights also agree. Matching the extracted trace bitmap and degrees to `CheckedProof` therefore supplies the exact budget already enforced during proof decoding, independently of lookup grouping. |

The new workers traverse component members, canonical function/memory traces,
their graph-satisfaction predicates and graph lookup extraction. The six
changed workers forward the selected mode table through the existing valued,
symbolic and lookup-usage traversals. Each has a checked safe source. The
four native externs, three partial Hashable/Repr sources and empty additional
unsafe/replacement inventories are unchanged; `Ix.Compiler` remains excluded.

The theorem's remaining inputs are physical base-graph satisfaction, canonical
fixed preprocessing, trace activation/height metadata, a checked logical-slot
budget, message widths and exact padded balance. PCS must authenticate those
traces and preprocessing; randomized lookup soundness must derive balance.
Compiler-to-source reflection and guest/kernel soundness are separate later
contracts. This endpoint is not an acceptance-to-no-False theorem.

The native key corpus now covers 24 systems, 360 circuits and 1,440 arbitrary
assignments. It rejects 336 validly encoded altered keys and 48 invalid
component certificates. A separate production-image check reconstructs the
pruned, grouped `verify_claim` image: 793 functions, 181 function circuits and
201 total key circuits. All native graphs, dimensions, lookup groups and
degrees match the checked key. Its 915,765-byte key uses explicit test
protocol parameters and is not a pinned production security release.

The full `check-aiur` gate passes: 605 strict build jobs, exact audit-manifest
comparison, four unchanged compiler snapshots, all 40 native/model corpora,
the production-image key check and backend acceptance/rejection tests.
Parallel release Rust tests pass (112 enabled tests), as do Clippy and
formatting. The selected integration suites, all three code-generation
comparisons and the complete 83-fixture IxVM corpus also pass. The generated
images and shard FFT cost of 8,523,899,042 are unchanged.
