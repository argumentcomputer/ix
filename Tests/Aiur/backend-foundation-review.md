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
