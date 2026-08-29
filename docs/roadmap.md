# Compilatr.ix roadmap

Live status ledger, last updated 2026-08-27. This is the single source of
truth for sequencing and completion status. Files under the local `plans/`
directory remain design notebooks and historical decision records; they do
not override this ledger.

Process rules:

- An adversarial review round is closed only by a disposition edit to this
  file — every critical/major finding becomes a fix, a row, or a one-line
  recorded rejection, in the same change. (Rounds: `plans/review-2026-08-13`,
  `-15`, `-18`; the 08-15 round was absorbed late, on 08-19, together with
  round 3 — this rule exists so that cannot recur silently.)
- The queue may be reordered when a dependency is discovered **or** on a
  recorded cost/risk reprioritization; update this file in the same change
  that changes the order or a completion claim.

Status vocabulary:

- **done** — implemented and covered by the check surface; where a theorem
  is claimed, it exists at the stated strength, and at least one
  non-degenerate executable witness exercises it (an identity partition,
  a sort-only table, or a `.sortV`-valued conclusion does not count).
- **done (executable)** — implemented and differentially tested; no theorem.
- **done (fragment)** — theorem-backed for an enumerated fragment; the
  frontier is named in the row.
- **active** — an implementation slice is in flight; every active row must
  appear in the immediate queue.
- **queued** — specified but not started.
- **deferred** — has an explicit later activation trigger, named in the row.

## Mission

Build a self-hosting certified toolchain from Ixon to native and zk targets
— native and zk code generation verified against the *same* Ixon
operational semantics — with an independently specified checker, an
explicit runtime theorem, and a shrinking trusted-extern ledger. The
end-to-end claim is observational equivalence between Ixon evaluation and
emitted machine execution, plus separate resource/capability guarantees.

Two scope notes keep that claim honest. Today's simulation theorems
transport source success only; the backward direction (error/divergence
preservation) is a tracked deferred row. And kernel soundness alone does
not make checked *statements* faithful; the faithfulness obligation
(verified printing, statement-faithful certificates) is tracked under the
deferred frontend milestone M4, which records — rather than silently
enacts — the decision to sequence the frontend after the backend spine.

## Current milestone ledger

### M0 — reproducible, auditable engineering baseline

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| Pinned Lean/Lake/Nix build | done | `flake.nix`, `flake.lock`, `lean-toolchain` |
| Library + compiled FFI test checks | done | `nix flake check`; `tests-ok` |
| Push/PR CI | done (authored) | `.github/workflows/ci.yml`, actionlint over the whole workflows directory; x86_64-linux only. **First execution triggered 2026-08-25** by the initial push of `main`@`59beadc` to the new remote (the workflow fires on push); the outcome is not yet observable from the dev environment (private repo, no authenticated `gh`/token) — becomes done on the first *observed* green remote run |
| Repository witness (local) | done | **Committed 2026-08-22** as one witness commit over the whole tree, on a green check surface (`nix flake check`: library, tests, CI-workflow lint, extern ledger; plus `lake exe tests` → `tests-ok`), ending the window in which no committed revision existed anywhere. Discovered at commit time: the repository had been in **detached HEAD with no branches at all** — `main` did not exist, so the entire history was reachable only through the reflog; `main` was created at `beddd38` before committing. `plans/` tracking was **decided against** (JCB, 08-22): it stays gitignored and single-copy, so every decision record and the three audit artifacts remain one machine away from loss — an accepted risk, recorded rather than silently carried |
| Off-machine witness (remote + first CI run) | landed (08-25; green pending) | activated by JCB 2026-08-25: `origin = git@github.com:argumentcomputer/Compilatr.ix.git` configured and `main` pushed through `59beadc` (the remote was empty; clean fast-forward). Every committed revision now exists off-machine, retiring the single-copy consequence for committed history — `plans/` stays single-copy by the 08-22 decision, and the in-flight working tree (progress-cluster tranche + today's roadmap/decision edits) remains local until its witness commit. The push triggered the first-ever CI execution; observing it needs the Actions page or an authenticated `gh` (none in the dev environment). Row completes — and the Push/PR CI row above flips to done — on the first observed green run. The committed-green-bookmark cadence is now in effect: witness commits on green check surfaces, pushed |
| Trusted-extern ledger | done | `docs/trusted-extern-ledger.md`; schema 2 distinguishes dependency and project native interfaces. The fail-closed validator checks 12 pinned Blake3 symbols plus both local durable-sync exports, exact local Lean/C inventories and source hash, per-module reachability, `opaque`/`def`/`attribute` forms, full-commit CI actions, and integrity-pinned build selection; missing inventory roots hard-fail |
| Actual dual-license grants | done | `LICENSE-APACHE`, `LICENSE-MIT` |
| One tracked live roadmap | done | this document |
| Sorry/axiom fence | done (fragment) | `Compilatrix/Fence.lean` (2026-08-19; extended 2026-08-27): `#guard_msgs`-pinned `#print axioms` for the flagship/equivalence theorems and all twenty-two codec laws — the previous nineteen plus IxIR₁ mutual-block roundtrip, accepted-byte canonicality, and preimage injectivity — including the contentful ordinary-definition ghost-erasure theorem `SimInstance.ghostDefinitionHeadSim`, configured quotient theorem `SimInstance.quotientIndSim`, explicit-oracle theorem `SimInstance.externAnswerSim`, escaped constructor-pap theorem `SimInstance.pairSplitProjectionSim`, definition-projection theorem `SimInstance.definitionProjectionSim`, mixed mutual-member theorem `SimInstance.mutualInductiveMemberSim`, cyclic definition/recursor theorems `cyclicDefinitionMembersSim`/`cyclicRecursorMembersSim`, the generic/contentful/whole-entry UsageCheck non-interference boundaries, and the indexed-environment lookup/resolver/lowerer equivalences. The whole-pass boundaries include `SimInstance.addIxIR1CompilerContracts`, `addIxIR1SemanticForwardSimulation`, `addIxIR1MemoryErrorUnreachable`, and the generic value-sealed `LowerSim.lowerAllAction_memoryErrorUnreachable_sealed` and `lowerAllAction_unknownRefUnreachable_sealed` (so M2b's "kernel-checked, no `native_decide`" claims are mechanical rather than editorial); the projection bridge pins `Sim.erasure_proj_sim`, its sharing-aware companion `erasure_proj_sim_inlineSharing`, `LowerSim.lowerE_proj_erasure_run_value_progress_within`, and the premise-free `lowerE_proj_var_run_value_sound`. The full certified-erasure progress chain is pinned too: `ProjectionSafeEval.of_erasure`, its member-scoped and sharing-aware forms, validator-exact projection and call-aware traces, the member-scoped call-aware bridge, the whole-pass trace-progress constructor, exact certificate target progress, whole-main projection-safe progress, sealed ordinary-stuck exclusion, and both compatibility and trace-sealed semantic-forward-simulation endpoints — all within {`propext`, `Classical.choice`, `Quot.sound`} — plus a declaration-level `sorry`/`axiom`/`native_decide` source scan in `check_trusted_externs.py`. The reclamation/cost extension pins finite release, actual no-`reuse` compiler output, whole-pass reclamation, pure address transport, the general allocation/live/free balance, its combined whole-pass and fully-addressed counter contracts, and the nonvacuous exact four-counter lowering witness. Content-address pins include both pure cycle-safe block codecs, the IxIR₀ evaluator induction, and two-map precomposition separately from successful mutual-block/whole-program/addressed-erasure and final lowering composition; only production content-address cones contain the exact native BLAKE3 axiom already recorded in the extern ledger |
| Ledger-validator Lean-root blind spot | done | root inventory is derived from the controlled `lakefile.lean` `lean_lib`/`lean_exe` declarations; unsupported syntax, an empty inventory, and missing roots are hard failures (migrated with the native sync target 2026-08-26) |
| ix parity baseline single-sourcing | done (08-25) | clean-archive ix capture at exact revision `6f18ea907b78d06f7dc0917c43beb385561c35f4` / tree `c09cfe3d`: two constant byte+raw-hash vectors (including all modes and a shared table), Rust-writer agreement, and six framed sharing input/output vectors are frozen in `Tests.lean`. Four sharing cases agree exactly; `forall-imp-real` and `flip` retain reviewed local strictness deltas. `Sharing.ixParityRevision` is the sole Lean revision literal; the dead `c98bb741` v4.31 shell/subproject harness is deleted. `docs/sharing-policy.md` records capture and re-pin protocol |

### M1 — Ixon v2 identity and source semantics

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| v2 wire format: mode-bearing syntax, strict canonical codec, `ixon-v2` namespace, succ-RLE bound | done | `docs/ixon-v2-wire.md`; total raw writers, input-fueled decoders, rejection guards, 110-byte golden wire fixture with its raw digest pinned through the real FFI path (`Tests.lean`) |
| Canonical sharing ladder S1–S5 | done | layer 1, total inliner, evaluator coherence, deterministic compressor, address identity — `docs/canonical-sharing.md` proof ladder; policy frozen as `compilatrix/ixon-v2-sharing/1` (`docs/sharing-policy.md`) |
| Codec roundtrip/canonicality laws | done | global accepted-byte canonicality for all five codecs; global roundtrip for `Address`/`Univ`; exact `wireWF` domains for `Expr`/`ConstantInfo`; `wireWF ∧ sharingWF` for `Constant` |
| bv_decide compiler trust in codec laws | done (08-26) | evicted every `bv_decide` proof step from the Ixon codec dependency cone (`Serialize.lean`, `Const.lean`, and `Expr.lean`). Reusable kernel-checked bit extensionality, bounded-natural arithmetic, and byte reconstruction now prove the little-endian and packed-header lemmas. `Compilatrix/Fence.lean` pins all ten roundtrip/canonicality laws, including the formerly excluded eight; each prints exactly {`propext`, `Classical.choice`, `Quot.sound`} with no native-reflection axiom |
| Encode-time `wireWF` | done (checked writer, 08-25) | `DecodeCheck.wireConstantWF` is an executable mirror proved exactly equivalent to `Constant.wireWF` through every nested variant. `encodeChecked` combines it with resource-bounded local semantic validation and returns either exact `ser` bytes or a structured wire/local/resource error; `encodeChecked_sound` proves the successful domain. Raw `ser` remains the proof/fixture API |
| Canonical inlined/address identity | done | `Constant.inlinedView_eq_iff_address?_eq` on `Addressable` under an explicit pairwise BLAKE3 no-collision premise; `Addressable` is the exact executable predicate `canonicalSharing ∧ DecodeCheck.checkedWF`, so malformed or wire-truncating constructed constants cannot acquire an address. Corpus-facing constructed values use `addressChecked[With]`, which additionally bounds layer-1 work and computes/caps fully expanded compressor input without allocating it; bare expressions expose only a context-local cache hash |
| Decode-time local index bounds | done (checked ingress + address gate, 08-25) | `Compilatrix/Ixon/DecodeCheck.lean`: `decodeChecked` composes a resource-bounded strict parser with a sharing-aware local walk. It checks ref/str/nat/projection-type indices vs. `refs`, sort and reference-instantiation indices vs. `univs`, every used `Univ.var` vs. the owning declaration's `lvls`, and self-`recur` vs. the enclosing mutual block (including ix's singleton-collapsed standalone `.defn`/`.recr` convention). It also checks the evaluator's exact recursor slicing equations: type Π-count = params+motives+minors+indices+major, rule λ-count = params+motives+minors+fields. Errors carry mutual-member/root sites; table-driven tests pin positive boundaries and each first-invalid index/count. Raw `de` stays the local proof/codec API; local-policy bytes use `decodeChecked`, while catalogs use `decodeIxonV2Checked` plus exact pinned-ix recompression. The corresponding constructed-value address gates apply the same local predicate. Cross-constant member/type coherence remains the store-ingest row |
| Decoder depth guard | done (checked ingress, 08-25) | `DecodeCheck.Limits` makes per-object bytes (64 MiB), expression/universe nesting (512 each), every input-driven sequence (4096), and the quadratic layer-1 charge (16 Mi visits) explicit and configurable. The ingress parser uses iterative accumulation for arrays, universe-argument vectors, and flattened app/λ/Π runs, checking counts before loops/allocation; recursive expression/universe descent consumes the explicit depth budget, then a linear preflight runs before sharing validation. Tests pin exact-limit success plus one-below layer-1 work and truncated hostile application-count, refs-count, expression-depth, and universe-depth inputs. Raw `de` remains logically total but native-stack-unbounded and is not an untrusted-ingress API |
| Structured decoder errors | done (ingress fragment, 08-25) | `DecodeCheck.Error` has data-bearing syntax, object/sequence/depth/structural resources (stable metric + actual + limit), sharing, ref-kind/index/bound, universe-index/variable, self-recursion, unresolved-share, and recursor type/rule arity cases, each semantic case rooted at its standalone or mutual declaration slot. The proof-oriented raw parser's strings are preserved under `.syntax`; splitting every low-level EOF/tag/canonicity message into typed constructors remains optional hardening, not a corpus-ingress blocker |
| Cross-constant member bounds | done (catalog ingress, 08-25) | `Catalog.validateStore` runs over the exact deduplicated address union: every projection block resolves to `.muts`, member indices and kinds agree for all four projection variants, constructor projections are in range, and every constructor's stored `cidx` equals its array position. Structured regressions pin an out-of-range member and a non-positional constructor ordinal |
| Source quotient ι | done (08-25) | `EvalCtx.quotientKind` explicitly authorizes an address/kind pair; configured `quotH` values use the four real source arities, saturated `Quot.mk` produces a non-applicable `quotV` wrapper, and `Quot.lift`/`Quot.ind` recover and apply its representative. Unconfigured addresses remain neutral and mismatched configuration is stuck. `Sharing/Eval.lean` preserves the configuration and proves coherence for quotient heads/wrappers; executable source/target guards return `37` through both eliminators |
| Evaluator neutral refinements | done (08-27) | `NeutralId.member` is block-qualified; `prj` resolves its local type ref through an exact `iPrj`/inductive member and rejects family drift; opt-in `EvalCtx.preserveNeutralElims` retains neutral projections and saturated neutral-major recursors as explicit application spines. Address-configured String literal majors now expand through the upstream `String.ofList (List.cons.{0} Char (Char.ofNat c) … (List.nil.{0} Char))` chain. The five heads are resolved and evaluated as ordinary constants, so the evaluator does not bake in String, Char, or List constructor layouts. Fuel monotonicity and sharing coherence cover the expansion. `EvalCtx.Strict` seals both opt-in behaviors because IxIR₀ does not yet model them; `MemberCoverage` carries that boundary, whole-program validation rejects either switch, and empty-scope simulation/lowering APIs expose the premise explicitly. Positive and exact-error guards cover projection identity/family/bounds, neutral spines and block identity, Unicode scalar order and empty strings, absent/malformed String configuration, ordinary family rejection, and the validator boundary. K-like reduction remains deliberately out of runtime scope because it is a defeq rule |
| UsageCheck metatheory | done (fragment) | Landed 2026-08-25 against the executable mutual checker: `UseVec` zero algebra, `check_ghost_zeros`, and `check_lam_dropped_entry_erased` prove that successful ghost walks and accepted eraser-dropped lambda heads compute zero usage. `Demand.dropped` now records the eraser's actual decision, so both explicit `erased` modes and ordinary `many` parameters over sort-like domains are zero-scaled; `UsageSound.erasureDropsBinder_eq_dropBinder` proves exact checker/eraser agreement through sharing and fuel. `ComputedErasedHead.of_checkedLambda` connects accepted lambdas to the witness, and `computedErased_eval_noninterference` joins two successful source runs through one common erased observation. Raw source-value equality is deliberately not claimed (closures may retain different irrelevant captures), and weak CBV still evaluates ghost arguments: termination/error irrelevance and typed higher-order/unknown-callee reasoning remain M3 work. The existing freeze restriction and its fixtures remain the ownership boundary |
| Sharing-policy tuning decision | done (dual-policy boundary, 08-25) | The local policy remains frozen as `compilatrix/ixon-v2-sharing/1`; the proposed residual-statistics/reference-order roll is formally dropped. Compatibility is isolated instead of conflated: `ix/ixon-v2-sharing@6f18ea90...` reproduces the pinned upstream effective-size heuristic and exact table image at catalog ingress, while the stronger local maximal-telescope/deletion-audit policy remains unchanged. Six captured vectors and the 54-constant production contact pin the split (`docs/sharing-policy.md`) |
| Ixon layer hygiene | done (08-27) | The earlier dead-helper deletion, documentation fixes, strict sharing bounds, decoder rejection guards, and evaluator quotient/definition-projection fixtures remain. `selfMutsOf` now has one definition in `Const.lean`, the lowest common layer for evaluator, eraser, validator, simulation, sharing, and usage checking; standalone definitions/recursors retain their singleton-block convention. `Uses.mul` is retained as the specification algebra for the future theory bridge but has exactly one executable role: `UsageCheck.UseVec.zeroScale` invokes it with `.erased` at an eraser-dropped argument boundary. Nonzero CBV composition stays `Uses.add` plus flow-sensitive ownership transitions; a guard and `zeroScale_eq_zeros` pin the zero-grade behavior. `Address.get` remains live through `memberAddr` |

### M2a — checked erasure to IxIR₀

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| IxIR₀ syntax and fueled semantics | done | evaluator + fuel monotonicity theorem |
| UsageCheck-gated executable eraser | done | checked pipeline rejects usage failure |
| Erasure simulation | done (fragment) | sorry-free over: kept vars, λ/let, literals with resolvable blobs, projections, refs, complete and escaping partial constructor-parameter prefixes, parameterized index-free recursor ι, complete and protected escaping indexed recursor spines, rule-local indexed recursive self calls, unfoldable and configured-opaque mutual-definition projections/members, non-self inductive members, simultaneous cyclic unfoldable-definition and recursor members, configured quotient type/`mk`/`lift`/`ind`, and configured opaque/axiom externs under explicit oracle correspondence; fenced by `Compilatrix/Fence.lean`. **`ValRel` constructor cases pin the target address** (`CtorAddr` premise, 08-19): a target ctor address must resolve in the source context to a `.cPrj` of exactly that block/inductive/ctor, so one address cannot relate two families; the `addE'` differential guard is address-sensitive per cell |
| Ghost arguments at definition heads | done (fragment) | landed 2026-08-25: `DefSpine` follows an unfoldable definition's literal implementation lambda telescope, `PErase.appDG` requires that runtime binder to drop independently of the executable eraser's declaration-type policy, the proof-producing validator reconstructs the same witness, and `SimInstance.ghostDefinitionHeadSim` pins a contentful `7̂` source-only argument / `9̂` result. Repeated and interleaved visible applications are covered by the spine; higher-order or otherwise unknown heads still conservatively keep their arguments |
| Executable-output certificate bridge | done (fragment) | the validator reconstructs every `PErase` clause of the proved fragment, including indexed projection/self/member heads, the exact let-captured `recW` continuation (`certifyExprWithRec`/`validateRecSpine`), unfoldable and configured-opaque `dPrj`/`recur`, and non-self inductive `recur`. `MemberScope.plan` names a finite set of definition/recursor holes; `validateMemberCoverage` checks each body/rule set once against the completed public coverage database and the same plan, then `CertifiedProgram.members` carries the simultaneous proof. Rule-local self validation deliberately reuses the environment certificate instead of recursively querying the member under construction. Negative guards reject an unprotected early-firing indexed pap, a mismatched mutual slot, an incomplete cyclic plan, an unconfigured opaque member, and opaque-member target arity drift. Standing acceptance criterion: the certified fragment must never silently lag the theorem fragment — **note this has no mechanical enforcement** (soundness is type-forced; completeness is discipline): maintain a fixture-per-`PErase`-constructor rule at review, or add an enumeration guard |
| Sharing support | done (fragment) | `erasure_sim_inlineSharing` composes evaluator coherence with share-free `PErase`; sharing-aware certificates validate original shared inputs against their inlined relation. `SharingWF` side conditions are still hand-discharged per fixture — the decoder-layer-1 bridge remains (missing: a `Frame.ofConst` WF lemma, entry-`sharesBelow` derivation, nonempty-env `ValuesSharingWF` helpers, and the store-ingest resolver invariant) |
| Constructor/recursor argument-policy cursor | done (fragment) | ctor params, recursor params, and complete or protected split source-only index segments at theorem + certificate + instance level (`Sim/Segment.lean` cursors; `Pair.mk`, List-shaped, and recursive one-index instances; `RecEraseSpine` keeps raw indexed intermediate paps out of the global value relation while `papRecIW` admits only their ignored continuation; the rec-major guard plus `RecMember.BlockParams` protect layout compatibility). Partial constructor and indexed-recursor prefixes use the protected-wrapper rows below; non-self inductive heads are erased absorptively, and `RecEraseSpine.memberHead` routes non-self recursors through simultaneous member coverage |
| Split/under-applied constructor-parameter spines | done (protected wrappers, 08-26) | `Erase.eraseRefHead` emits one ignored target lambda for every dropped source parameter not consumed by the visible spine, retiring the strict rejection switch without reopening the early-fire miscompile. `PErase.ctorW` and `ValRel.papCtorParams` relate partial source paps to those wrappers and prove closure under later generic application; the final wrapper exposes the field-arity target constructor exactly when the source finishes its parameters. The validator reconstructs the exact wrapper without global expression equality. `SimInstance.pairSplitProjectionSim` certifies a pap that escapes after one `Pair.mk` parameter through a let, then consumes the second parameter and fields `11`/`22` through a variable head and projects `22` on both sides; wrapper-shape drift is rejected and the theorem is axiom-fenced |
| Split indexed-recursor spines; indexed recursive self calls | done (protected continuations, 08-26) | `Erase.captureThenIgnoreN` evaluates and let-captures the pre-major target pap before exposing one ignored binder per remaining source-only index, avoiding both early target firing and de Bruijn capture. `PErase.recW` and `ValRel.papRecIW` prove that continuation closed under later generic application after escape through a variable or let, transitioning to `papRecI` exactly at the last index. `RecEraseSpine.selfHead` covers indexed rule-local `recur` without a cyclic `RecMember` premise; the already-certified self member comes from `EnvRel.selfB` at fire time. The validator reconstructs both shapes structurally. `SimInstance.indexedRecSplitSim` and `indexedRecSelfSim` use a contentful two-constructor one-index family whose step recursively reduces a base field to `73`; exact eraser-output and evaluator guards pass, and both theorems are axiom-fenced. Non-self indexed recursor heads use the same spine through `RecEraseSpine.memberHead` and the block-wide certificate |
| Mutual-block member coverage | done (all emitted member kinds, 08-26) | The projection and inductive slices remain: `Covered.defnProj`/`definitionProjectionSim` return `91`, while `PErase.recurI`/`ValRel.inductiveMember` and `mutualInductiveMemberSim` return `88` with exact block/slot checks. The finite `MemberScope.plan`, `MemberRel`, and `MemberCoverage` layer proves every named unfoldable-definition body or recursor rule set against the same holes, so cycles require no topological proof order. `PErase.recurD`/`recurR` and `RecEraseSpine.memberHead` consume the certificate during expression, recursor-fire, call-aware projection-safety, and IxIR₁ progress simulation. Configured opaque members use `Address.memberAddr block idx` as the source-oracle key and emitted target extern address; `PErase.recurO`, `MemberRel.externDefn`, and `Covered.externDefnProj` pin resolution and arity without weakening `OracleRel`'s same-address contract. `certifyProgram` returns the simultaneous proof after public coverage. Executable fixtures pin a genuine two-definition cycle (`71`), two alternating Nat recursors (`77`), and both wrapper/member-projection opaque paths (`83`); incomplete-plan, missing-configuration, and arity-drift guards fail closed, and the public simulations plus generalized progress bridges are axiom-fenced. The remaining address-engineering debt is the separate `memberAddr` retirement row |
| `memberAddr` retirement | done (production, certificate, and current modeled-oracle closure, 08-26) | `IxIR0.MutualBlock` removes the address cycle structurally; `IxIR0.Readdress` lifts it over all groups; `EraseAddressed` retains the exact old erasure for proof reuse and produces the block-derived image; and IxIR₀ evaluator equivariance maps closures, PAPs, constructors, errors, and oracle values. Both pipeline entries now lower only the addressed image, retain raw/final declarations plus the block/map provenance, and compiled fixtures prove old keys absent from final IxIR₀/IxIR₁ environments. `ReaddressProjectionSafe` maps the exact four-way call-aware trace directly from the literal raw environment; `LowerMutualAddressedProgress` composes validator certification, sealed target progress, and both production address maps into a final forward simulation. `ReaddressOracle` reverse-resolves only call keys, preserves already-addressed arguments, maps results forward, and reduces the final public theorems to a compact per-oracle coherence law. The whole-program audit now isolates reserved, stable, and declaration/main external identities from both sides of the map; `Readdressable.of_isolated_key` and `ReaddressOracleExamples` discharge the exact ledger-recorded IxIR₀ Nat-add model. A frozen cyclic block calls that extern and returns `42` before/after addressing, while main-only identity capture fails closed. The XOR remains only inside the source evaluator/legacy erasure relation and opaque-oracle configuration. Future production services still require their own ledger entry and correspondence proof, but no current modeled-oracle or production `memberAddr` key remains unfinished (`docs/ixir-content-addressing.md`) |
| Dropped-variable occurrences | done (fragment) | Landed 2026-08-25 for checked occurrences inside eraser-dropped arguments of known definition heads. `UsageSound.DroppedVariableFixture` propositionally derives the computed-zero witness from an accepted lambda check, certifies the exact `.app (.ref consumer) .erased` target, varies the source slot from `7̂` to `8̂`, and proves both runs share the contentful `9̂` erased observation; its whole-entry forward simulation and the generic theorem are axiom-fenced. This does **not** add the false raw `PErase.var` clause: a direct runtime read from a dropped slot is rejected by `typeBinderRuntimeUse`. Higher-order/unknown heads and termination/error non-interference remain outside the fragment |
| Extern/opaque correspondence | done (structural + explicit semantic premise, 08-26) | Configured opaque definitions and axioms certify against exact same-arity `IxIR0.Decl.extern` declarations. Opaque mutual definitions extend the same rule: source `.recur` and public `dPrj` dispatch on the emitted synthetic member address, so `OracleRelAt` remains a same-address contract rather than gaining an alias ledger. `ValRel.papExtern` covers under-saturation and exact saturation crosses that explicit oracle relation; the broad neutral-to-`◻` fallback is restricted to resolved inductive-projection type heads. Source sharing coherence preserves configured oracle calls. The validator checks address/kind/arity structure but cannot manufacture semantic oracle agreement, which remains an explicit premise through erasure simulation and the IxIR₁ progress bridges. `SimInstance.externAnswerSim` pins a two-argument axiom returning `42`; `opaqueMutualMemberSim`/`opaqueMutualProjectionSim` pin both mutual paths returning `83`, with unconfigured, arity-mismatch, and missing-oracle guards across the fixtures. The composed `Pipeline.Config` still supplies no production extern authorization and therefore fails closed on axioms |
| Certificate `Owned` fidelity | done (definition + quotient results) | landed 2026-08-25: fuel-free `TeleResultOwned` follows arrow and sharing spines without turning a cyclic/fuel-exhausted lookup into `.shared`; `Covered.defn` and `Covered.quot` carry exact source-telescope result ownership, `validateCovered` checks it against the actual erased declaration, and negative fixtures pin the definition and quotient mismatch diagnostics |
| Quotient compilation | done (08-25) | `Erase.quotientBody` exposes the exact four emitted definitions; `Covered.quot` pins resolver/configuration/body/ownership identity; `ValRel.quotType`, `quotV`, and `papQuot` cover erased types, wrapped representatives, and every strict application prefix. Saturated `lift`/`ind` reuse the generic application simulation at smaller source fuel. The proof-producing program/expression validators certify exact executable outputs, `SimInstance.quotientLiftSim`/`quotientIndSim` return contentful `37`, and `quotientIndSim` is axiom-fenced |
| Error/divergence preservation | deferred | `erasure_sim` transports source success only; the backward direction of the observational-equivalence claim activates with the M3 theory bridge |
| Eraser adequacy against kernel theory | queued | activates with the ix4lean theory bridge at M3 |

### M2b — explicit-memory IxIR₁

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| IxIR₁ store semantics and dynamic discipline | done | shared/unique nodes, RC, deep free, reuse, paps, counters. Scope note (08-19): the dynamic checker enforces *temporal and world* discipline; unique-aliasing violations are prevented at compile time only (`held` flags), not observed at run time |
| Mode-directed IxIR₀→IxIR₁ lowering | executable done; proof active | differential/leak/counter corpus and checked end-to-end fixture; error agreement is exact (`errAgree`: fuel↔fuel, address-exact unknown refs, pinned oracle/ABI/stuck pairs — 08-19). `LowerStateSim.lean` now closes the complete ownership and value-correspondence compiler-fuel clusters, including ordinary no-`recSelf` and current-self expression routes; `lowerAllAction_main_value_graph` lifts the semantic cluster to arbitrary successful whole-main compiler and evaluator runs. `LowerSim.lean` traces each `lowerDecl` through `lowerAllAction`, recovers generated-state suffixes, and jointly seals source declarations, generated declarations, and higher-order application with `compilerContracts_of_source_extra_below_step`. `Sim.applyOwnershipPreservesAt_of_sharedDeclsBelow` covers pap under-fill, saturation, over-application, and scalar externs. The exact `add 2̂ 3̂` whole-pass output instantiates the ownership boundary as `SimInstance.addIxIR1CompilerContracts` and the semantic boundary as `SimInstance.addIxIR1SemanticForwardSimulation`; the latter is a kernel-checked segmented trace of the actual compiler output and returns a `ValueGraph` realization of `5̂`. Generic semantic declaration/application sealing now comes from the actual whole-pass output via `lowerAllAction_compilerValueContracts`; exact call-aware erasure traces and `lowerAllAction_compilerTraceProgressContracts` now also construct callable target progress from whole-pass provenance. `LowerFullyAddressedSim.lean` carries exact evaluator results and all existing raw semantic/safety conclusions through the indexed production entry while preserving instruction counters and reserved constructor identities and rekeying every function producer; `LowerAddressedSim` remains the generated-only compatibility layer. The profile-sensitive cost theorem now also crosses that fully addressed boundary; remaining proof work is duplication cleanup |
| Lowering restrictions ledger | done (policy + executable boundary, 08-28) | `IxIR1.Lower.RestrictionKind.all` is a six-entry code-level inventory for no implicit freeze, no unique destructuring, shared/all-`many` function values, no unique captures, mode-monomorphic recursors, and saturated-only `recSelf`. Stable diagnostics are shared by the lowerer and generated corpus; an aggregate guard gives every entry an exact rejection witness, including a synthetic under-applied-self rule, while the seeded corpus now covers unique capture and the all-shared recursor ABI across 280 cases. `docs/lowering-restrictions.md` records each current enforcement path, planned lift, dependency, and wake condition. The restrictions remain deliberately fail-closed: unique trees still support zero-RC allocation, movement, return, and deep free but not computation until the unique-destructuring slice lands. |
| Formal memory-ownership simulation (RC/root conservation) | active | *renamed from "formal memory simulation" — the completed induction is ownership-only and success-conditional.* Heap/value/root foundations now cover every primitive memory operation; direct/self calls, recursor bodies, lifted functions, constructor wrappers, and pap application all have exact fuel-indexed contracts. `compilerContracts_of_source_extra_below_step` closes their mutual cycle, and `SimInstance.addIxIR1CompilerContracts` constructs both `CompilerContracts` and `ExtraFnContracts` from the actual nontrivial `lowerAllAction` result (five source-backed functions plus one lift); its `CompilerContracts.apply` is the first concrete `ApplyOwnershipContract`. This completes the ownership-contract exit criterion. `SimInstance.addIxIR1SemanticForwardSimulation` now discharges the semantic proposition for the nontrivial compiled fixture, and `lowerAllAction_compilerValueContracts` supplies the generic semantic contract boundary. The first duplication cut is also landed: `EmitSound.of_below`, `LowerResultSound.of_below`, and `LowerArgsSound.of_below` close uniformly bounded proofs, and base/primitive/call/apply emitter pairs now share one bounded body without changing their public signatures. The second cut now routes `FieldRetainPlan.sound`/`.soundBelow`, `ReleasePlan` ownership and graph soundness, and `releaseAll` ownership and graph soundness through one private bounded induction body per family; their exact and bounded public signatures remain unchanged. The third cut adds `OpSound.of_below` and routes constant argument/result discards, slot-backed argument discards, and recursor-major release through one private bounded ownership or graph body per family, again preserving the exact and bounded public APIs. The fourth cut removes the exact `release_slot` common helpers and shares bounded bodies across shared/affine ownership and graph release; final-use moves, move-borrows, repeated borrows, and arbitrary-count retains likewise expose their exact and bounded APIs from one bounded ownership or graph proof per family. The fifth cut routes the closure-capture semantic pipeline—one capture, recursive capture lists, local-lambda pap allocation, and both explicit-length and premise-free `lowerE` lambda adapters—through one private bounded graph proof per family, with exact APIs closed by `of_below`. The sixth cut collapses complete variable-expression and variable-borrow dispatches—including impossible entry, world, and mode branches plus final/repeated-use graph cases—into one private bounded body per dispatch while preserving their exact and bounded APIs. The seventh cut factors the scalar-identity graph transformer once and routes literal/erased leaf rules and their `lowerE` dispatches through private bounded bodies, again closing exact APIs with `of_below`. The eighth cut makes dynamic-borrow monadic inversion and descriptor dispatch one result-polymorphic core shared by bounded ownership, semantic graph, erased-reflection, and exact/bounded reachable-state adapters while retaining every public premise and result type. The ninth cut gives projection lowering one world-indexed operational core: unique-world rejection, borrow-bind inversion, descriptor dispatch, and output recovery are shared by bounded ownership, semantic graph, erased-result inversion, and exact/bounded reachable-state clients while their branch-specific logical adapters remain explicit. The tenth cut makes source-expression inversion and complete constructor dispatch one result-polymorphic core shared by ordinary semantic soundness, erased reflection, and exact/bounded reachable-state semantics; application-to-spine conversion is likewise single-sourced while recursive premises remain client callbacks. The eleventh cut makes semantic argument-list sequencing one result-polymorphic operational core shared by ordinary, bounded, reachable, and reachable-bounded clients; source-list inversion, `lowerE`/`lowerArgs` bind decomposition, and output recovery now occur once while each client retains its semantic composition and reachability facts. The twelfth cut gives `applyRest` one result-polymorphic operational core per function shape: shared-result guarding and fresh-slot reconstruction, or erased-argument release and scalar recovery, are each single-sourced across seven ordinary, bounded, and reachable semantic clients together with their shared-argument world/length normalization. The thirteenth cut gives erased spines one source/run-normalization core and every lower-then-apply spine one result-polymorphic semantic core: erased-head/result forcing, executable head/rest decomposition, erased reflection, and erased/non-erased dispatch are single-sourced across three erased and six dynamic/ordinary-variable ordinary, reachable, and reachable-bounded clients, while client-specific reachability packages remain adapters. The fourteenth cut makes `knownCall` prefix/tail sequencing one state-predicate- and result-polymorphic semantic core shared by ordinary, reachable, and reachable-bounded clients: prefix run inversion, source take/drop splitting, terminal output recovery, excess-tail dispatch, and intermediate-world normalization occur once, while reachability and current-self packages remain client adapters. The fifteenth cut makes static-reference spine classification one result-polymorphic eight-branch core shared by bounded ownership plus ordinary, reachable, and reachable-bounded semantics: unknown-reference rejection, source-declaration case analysis, and definition/constructor/recursor/extern under-versus-saturated arity splits occur once, with contracts and lookup-derived facts confined to branch adapters. The sixteenth cut lifts complete `lowerSpine` head and variable-entry classification into one dependent result-polymorphic core shared by bounded ownership plus ordinary, reachable, and reachable-bounded semantics: application, erased, static-reference, dynamic-head, ordinary-variable, and synthetic-`recSelf` routing occur once, while branch contracts and reachability remain client callbacks. The seventeenth cut gives let lowering one dependent result-polymorphic five-branch operational core shared by body-run inversion, bounded ownership, and exact/bounded semantics: value/body bind inversion, slot-versus-scalar classification, dead-use rejection, output recovery, and binder tracking occur once; reachable-state clients inherit it through the semantic adapters while installation and graph contracts remain callbacks. The eighteenth cut gives generated recursor prefixes one uniformly bounded composition core shared by their exact and bounded certificates: field-retain planning, major release, parameter-release planning, environment recovery, and emitter composition produce fixed limit-independent witnesses once, with `EmitSound.of_below` closing the exact API and limit specialization preserving the bounded API. The nineteenth cut gives generated recursor rules one dependent judgment-polymorphic constructor shared by their exact and bounded certificates: prefix normalization, RHS sequencing, alternative assembly, exact run reconstruction, and `RecursorEntryValid` elimination occur once, while the adapters retain only their flavor-specific `LowerResultSound` closure into `AltOwnershipContract`. The twentieth cut gives whole generated recursor finalization one definition-indexed result-polymorphic core shared by its exact and bounded certificates: canonical `FnDef` transport and `lowerRecursor`/`mapM` run reconstruction occur once, while plan-indexed exact contract sealing and one-index preservation remain adapters; traversal-plan construction entry points and public theorem signatures are unchanged. The twenty-first cut replaces the parallel exact and bounded recursor traversal inductives with one contract-parameterized `RecursorRulesPlanWith` spine: state threading, `List.mapM` reconstruction, and output-contract membership recurse once, while `RecursorRulesPlan` and `RecursorRulesPlanBelow` remain exact/bounded abbreviations with compatible `.nil`, `.cons`, `.run`, and `.forall_mem` entry points. The twenty-second cut factors the exact and evaluator-bounded reachable semantic cluster theorems through one predicate-polymorphic two-predecessor compiler-fuel core: zero construction, the vacuous spine-at-one boundary, argument/application/borrow stepping, prior-cluster recovery, and five-field assembly recurse once, while exact and bounded expression/spine callbacks retain their respective contracts and public structures. The twenty-third cut gives semantic argument/application compiler-fuel closure two predicate-polymorphic cores: exact and bounded `lowerArgs` share predecessor-hypothesis narrowing and recursive tail closure, while exact and bounded non-erased `applyRest` share zero/successor dispatch and argument-closure reuse; all four public theorem signatures and flavor-specific higher-order contracts remain unchanged. The twenty-fourth cut promotes the five-way two-predecessor cluster core to a downstream proof combinator and routes non-memory settlement, projection-safe progress, and source-trace-bounded progress through it: zero/spine-one boundaries, argument/application/borrow stepping, prior-cluster recovery, and record assembly now recurse once across five semantic/progress flavors, while flavor-specific expression/spine callbacks and all public structures and signatures remain explicit. The twenty-fifth cut brings bounded ownership `LowerClusterPreservesBelow` under the same reusable cluster combinator: ownership-specific extra-state monotonicity remains in callbacks, while zero/spine-one handling, two-predecessor recovery, and five-field assembly now share the sole recursion used by six ownership/semantic/progress flavors. `lowerAllAction_memoryErrorUnreachable_sealed` and `lowerAllAction_unknownRefUnreachable_sealed` now prove the separate public memory and closed-world propositions for an actual whole-pass output under the explicit source-guided progress package. `lowerAllAction_compilerTraceProgressContracts` constructs that package from exact source-fuel call traces and whole-pass provenance, and `lowerAllAction_main_progress_of_certificate_sealed` closes target progress for validator-certified programs without a `CompilerProgressContracts` premise. The twenty-sixth cut gives the field-retain and release plan inductives one dependent judgment-polymorphic traversal each: descriptor consumption, environment threading, and emitter composition now recurse once per plan across six bounded ownership, graph-soundness, and graph-progress consumers, while public theorem signatures and structural plan APIs remain unchanged. The twenty-seventh cut consolidates the remaining paired semantic list traversals: `AValsStable.traverseAligned` single-sources source-length normalization and slot/literal/erased dispatch for exact/bounded `releaseAll` graph soundness and graph progress, while `ValuesAt.lowerCaptures_core` single-sources capture bind inversion, state threading, and tuple reconstruction for exact/bounded capture soundness and capture progress; callbacks retain only their judgment-specific one-step composition. The twenty-eighth cut gives successful `lowerCapture` one result-polymorphic operational core shared by bounded ownership, exact/bounded graph soundness, and graph progress: missing/`recSelf`/released/unique rejection, shared retain-versus-move classification, overcount rejection, and exact output reconstruction occur once, while callbacks retain only flavor-specific retain/move contracts. The twenty-ninth cut gives successful `lowerLam` one result-polymorphic operational core shared by bounded ownership, exact/bounded graph soundness, graph progress, and slot-result inversion: fuel/pap-safety rejection, capture/fresh/body bind inversion, capture-count normalization, generated-declaration push, and exact pap-result reconstruction occur once, while callbacks retain only ownership or semantic provenance/pap contracts. The thirtieth cut layers `lowerLam_run_value_core` over the operational core so exact/bounded graph soundness and graph progress share lifted-code provenance, source-capture selection, represented-declaration recovery, lifted-function relation construction, and strict pap-prefix arithmetic; adapters retain only capture-argument construction and judgment-specific pap closure. The thirty-first cut routes the state-simulation lambda consumers through `lowerLam_run_core`: exact entry-consumption recovery and generated-function ownership sealing now share rejection, bind inversion, canonical body-run normalization, output recovery, and pushed-declaration state reconstruction, while their adapters retain only capture consumption and lifted-body ownership contracts. The thirty-second cut exposes exact predecessor-fuel equality from `lowerLam_run_core` and routes reuse-free lambda emission plus generated-declaration state preservation through it: both consumers now share successful-run dispatch, canonical capture/body runs, output reconstruction, and declaration insertion, while their adapters retain only capture-emitter reuse freedom and recursive state/code invariants. The thirty-third cut routes all four direct cost/profile lambda consumers through the shared lambda cores: exact and bounded semantic profiles inherit canonical capture identity, lifted-code provenance, declaration recovery, function relations, and PAP assembly from `lowerLam_run_value_core`, while ownership and dynamic run funding inherit rejection, bind inversion, output recovery, and declaration insertion from `lowerLam_run_core`; adapters retain only capture-budget normalization and PAP cost composition. The thirty-fourth cut gives profiled `knownCall` one reachability- and result-polymorphic sequencing core shared by ordinary/reachable exact/bounded proofs: prefix run inversion, source/profile take/drop splitting, terminal built-result equality and profile normalization, and excess-tail dispatch occur once, while adapters retain only judgment-specific argument/build/tail composition and ambient-state transport. The thirty-fifth cut exposes the static-reference operational dispatch core and routes all four ordinary/reachable exact/bounded profile consumers through it: unknown-reference rejection, source declaration classification, and definition/constructor/recursor/extern under-versus-saturated arity branching now remain single-sourced across ownership, value, and cost proofs, while adapters retain only judgment-specific contracts, source-environment lookup, and ambient-state evidence. The thirty-sixth cut exposes the complete `lowerSpine` head/entry dispatcher and routes all four ordinary/reachable exact/bounded profile consumers through it: application, erased, static-reference, dynamic-head, ordinary-variable, and synthetic-`recSelf` classification now remains single-sourced across ownership, value, and profile proofs, while adapters retain only profile contracts, current-self evidence, application normalization, and ambient-state transport. The thirty-seventh cut gives profiled `lowerE` one result-polymorphic source/run dispatcher shared by ordinary/reachable exact/bounded proofs: exact `DynamicCost` inversion for variable, lambda, let, projection, literal, and erased expressions plus reference/application spine normalization now occur once, while adapters retain only branch judgments, compiler contracts, recursive profile composition, and ambient/current-self transport. The thirty-eighth cut exposes the dynamic-borrow operational core and routes all four ordinary/reachable exact/bounded profile consumers through it: fallback `lowerE` bind inversion, descriptor classification, release-flag reconstruction, and final-state recovery now occur once across ownership, semantic, reflection, and profile proofs, while adapters retain only profile judgments and ambient-state transport. The thirty-ninth cut gives argument-list lowering a source-neutral operational core and layers semantic/profile source adapters over it: nil recovery, two-stage bind inversion, emitter/list reconstruction, and final-state recovery now occur once, while all four ordinary/reachable exact/bounded profile steps retain only profile composition and ambient/self transport; the exact/bounded strict-fuel profile closures also reuse the shared predicate-polymorphic induction. The fortieth cut gives non-erased `applyRest` a source-neutral operational core and a single profile-source adapter: result-world rejection, argument-run inversion, homogeneous shared-world recovery, output reconstruction, source-profile pairing, and source-argument nonemptiness now occur once across ordinary/reachable exact/bounded profile proofs, while the exact/bounded profile fuel closures reuse the shared predicate-polymorphic dispatcher. The forty-first cut gives erased `applyRest` the same layered boundary: successful argument-run inversion, full-release/result reconstruction, target-length recovery, and homogeneous shared worlds now live in one source-neutral core; semantic and profile adapters each recover their own paired source relation and source/target length once, serving three value and four ordinary/reachable exact/bounded profile clients whose bodies retain only argument-discard composition and ambient/self transport. The forty-second cut gives erased-head `lowerSpine` a direct source-neutral run normalizer and layered semantic/profile adapters: the `lowerSpine`-to-erased-`applyRest` reduction occurs once; semantic head/result forcing serves three value clients, while profiled head evaluation, erased application determinism, and canonical head/argument/application profile reconstruction serve four ordinary/reachable exact/bounded clients whose callbacks retain only scalar-head certificates, tail application, and ambient/self transport. The forty-third cut gives profiled lower-then-apply spines one result-polymorphic source adapter across dynamic syntactic heads and ordinary variables: source-profile inversion, canonical head/rest witness consumption, profile reconciliation, erased reflection/result forcing, and erased/non-erased dispatch occur once for eight ordinary/reachable exact/bounded clients, while adapters retain only their shape-specific inversion, head/application judgments, and ambient/self transport. The forty-fourth cut exposes successful let lowering's five-branch operational dispatcher across files: value/body bind inversion, slot-versus-constant and dead-versus-live classification, illegal dead erased/linear rejection, cleanup/output recovery, no-self installation maps, and first-entry tracking are now single-sourced for body inversion, bounded ownership, exact/bounded value semantics, and exact/bounded profiles; the two reachable profile clients inherit through those adapters, whose five callbacks retain only recursive profile pairing, release evidence, and binder installation/composition. The forty-fifth cut exposes projection lowering's five-descriptor operational dispatcher across files: unique-world rejection, borrow bind inversion, scalar/erased/slot descriptor classification, release-bit dispatch, and exact output recovery are now single-sourced for bounded ownership, exact/reachable value semantics, erased reflection, and exact/bounded profiles; the profile adapters retain only borrow judgments and the five source-projection outcomes, while their reachable clients inherit the same boundary. The forty-sixth cut promotes variable-expression and variable-borrow dispatch across judgment boundaries: missing, synthetic-`recSelf`, released, exhausted, mismatched-world, and repeated-unique rejection plus use-count splitting, release-bit selection, and exact output/state recovery now live in two public result-polymorphic cores shared by bounded ownership, exact/bounded value semantics, erased reflection, and exact/bounded profiles; ten direct clients retain only final-move/repeated-retain or final-shared-move/repeated-borrow callbacks, while eight complete/reachable profile branches inherit through the four profile adapters. The forty-seventh cut gives profiled `releaseAll` one bounded stable-list induction shared by its exact and target-fuel-bounded interfaces: source-length inversion, nil recovery, slot/literal/erased dispatch, environment threading, emitter composition, and zero-profile monotonicity now recurse once; `ProfileFundedEmitStateRunSound.of_below` closes the exact API while the bounded adapter remains direct, and both erased-application clients preserve their signatures. The forty-eighth cut routes profiled closure capture through the existing operational boundaries: `lowerCapture_run_core` now owns missing/recursive/released/unique rejection, retain-versus-move classification, and output recovery for both exact and bounded profile clients, while `ValuesAt.lowerCaptures_core` owns the sole selected-capture induction, bind inversion, state threading, and tuple reconstruction; private bounded adapters retain only profile funding/composition, exact APIs close through `of_below`, and all four public signatures remain unchanged. The forty-ninth cut removes every direct `ReleasePlan` and `FieldRetainPlan` induction from `CostTrace`: the existing dependent `.traverse` boundaries now single-source descriptor consumption, environment threading, and emitter composition across paired ownership allowances, executable profile funding, and bounded state-indexed profile preservation—three clients per plan—while their callbacks retain only identity, drop/retain costs, graph transport, and profile arithmetic; all six public theorem signatures remain unchanged. The fiftieth cut gives raw `releaseAll` one source-neutral dependent traversal: nil/constant/slot dispatch, environment bumping, exact output recovery, and drop-emitter composition now recurse once across paired ownership allowance and executable zero-profile funding clients; callbacks retain only their judgment-specific identity/drop composition, and both public signatures remain unchanged. The fifty-first cut moves successful `lowerCaptures` execution to one source-neutral foundational traversal in `LowerStateBase`: nil recovery, double-bind inversion, compiler-state threading, and emitter/list reconstruction now recurse once across three environment invariants, bounded ownership, source-aligned semantic/profile/progress through the `ValuesAt` adapter, result-length recovery, entry consumption, no-reuse emission, and paired ownership/executable-profile cost clients; callbacks retain only one-capture judgment composition, and every public signature remains unchanged. The fifty-second cut gives action-level `lowerCaptures` one property-polymorphic foundational traversal: left-to-right capture sequencing, environment threading, nested binds, and pure empty/final tuple construction now recurse once across `ExtraMonotone` and `PreservesStateNoReuse`; each client supplies only its `pure`/`bind` algebra and one-capture theorem, every public signature remains unchanged, and together with cut fifty-one all `lowerCaptures` recursion is confined to distinct successful-run and action-level cores. The row remains active for the remaining duplicated recursive families; the separate profile-sensitive `CostRefinement` boundary is now closed |
| Value correspondence (IxIR₀ ↔ IxIR₁) | active | Architecture chosen: keep `LowerResultSound` as the ownership/frame layer and build a companion semantic refinement, so source values do not infect every existing ownership lemma. `SimInstance.addIxIR1SemanticForwardSimulation` is the first non-degenerate consumer of `ValueGraph`: every successful source run is joined by fuel monotonicity to the exact `5̂` run, while a segmented kernel trace executes the exact compiled main and constructs its six-constructor target graph. The generic environment layer now includes `EntriesValueGraph`/`VEnvValueGraph`, semantic caller frames (`RootsGraph` is retained across later arguments), `LowerResultValueSound`, and `LowerArgsValueSound` with a checked cons rule. Literal, erased, final/repeated variable, arbitrary-count capture move/retain, and complete selected-capture traversal rules are checked. Lifted paps now have a concrete function relation: `LambdaPrefix` describes residual source closures, `ValuesAt` pins the compiler-selected environment values, and `CompilerLiftCodeRel` ties the fresh address to the exact canonical `lowerFnBody` run plus its accumulated declaration; provenance is monotone under later `ExtraExtends`. `LowerArgsValueSound.papp_graph`, `lowerLam_run_value_sound`, and `lowerE_lam_run_value_sound` connect fresh allocation to an actual heap `ValueGraph`; `LowerArgsValueSound.alloc_graph` does the same for constructors. Destructive graph transport is now factored through `StoreGraphRestricts`: shared/unique deep drops expose reverse shape inclusion, surviving `ValueGraph`/`ValuesGraph`/`RootsGraph` witnesses are rebuilt from post-state ownership, and both `ReleasePlan.valueSound` and `releaseAll_value_sound` preserve semantic environments and caller frames. The generic let seam is also checked: alias/materialized binder installation adds the bound source value, released-first-entry pop removes it, and `LowerResultValueSound.installThen` composes the body. **The projection borrow pipeline is instantiated (2026-08-22):** `SourceProject` names the source evaluator's two `.proj` outcomes and `SourceProject.of_eval` derives it from `IxIR0.eval` rather than from a hand reading of it; `lowerE_proj_run_value_sound` dispatches all four borrow descriptors against both source shapes, including the two pairings the descriptor-driven branch choice does not exclude — a constructor target reaching the erased descriptor (unsatisfiable midpoint) and an erased target reaching a slot (`fetchErasedSlot_false`). The second recorded an asymmetry worth keeping: `ValueGraph` inverts only on the *runtime* side (`ValueGraph.eq_erased_of_erased`), so an erased *source* value may still be realized by a pap node through the abstract `FunctionRel`, and the vacuity argument has to cover that node shape rather than assume `RVal.erased`. `lowerBorrow_dynamic_run_value_sound` closes the borrow dispatch through the two `asBorrow` adapters; `lowerE_proj_var_run_value_sound` is premise-free for variable targets, with two fixtures that exhibit the actual `lowerE` run (final-use release and repeated-use keep) and discharge the source premises at a two-field constructor selecting the second field. **Non-application head coverage is complete (2026-08-22):** `lowerE_lit_run_value_sound`, `lowerE_erased_run_value_sound`, `lowerE_var_run_value_sound` (final-use move and repeated-use retain, with every other entry state and world mismatch discharged from the successful run) and `lowerE_let_run_value_sound` join the existing `.lam` and the new `.proj` dispatch, so every `lowerE` head except `.app`/`.ref` — both routed through `lowerSpine` — now has a semantic dispatch. The let dispatch takes the bound-value and body correspondences as separate premises over `sourceEnv` and `boundSource :: sourceEnv`, and reuses the alias/materialize/release seam unchanged. **Call/application contract vocabulary landed (2026-08-22):** `SourceApplies` is the source side of a target argument list (fuel-free at the interface, with append/snoc/split); `SourceRefValue` pins a callee's source identity at the same address the layout relation uses; `FnValueContract`/`ApplyValueContract` with their `Below`/`mono` transports mirror `FnOwnershipContract`/`ApplyOwnershipContract` and bundle as `CompilerValueContracts`; `invoke_fn_value_below`, `runOp_call_value_below`, and `runOp_callSelf_value_below` are the operation-level primitives. **Design finding that shaped them, worth not rediscovering:** the obvious one-clause contract (source result only) is *unusable at a call site*. `GraphOwnsResult` demands `RootsGraph` for the caller's framed roots in the store the callee returns, and a general callee both frees and allocates, so neither `StoreGraphExtends` nor `StoreGraphRestricts` transports the frame — the obligation cannot be reconstructed by the caller and must be discharged by the callee. Both contracts therefore carry a second frame clause plus the ownership premise that justifies it, in lockstep with their ownership twins. **Semantic call/spine closure landed (2026-08-24):** exact entry-root reconstruction now rebuilds `VEnvValueGraph` from a callee-preserved `RootsGraph`; direct calls, `callSelf`, higher-order apply, and `knownCall` all consume the semantic contracts. Source argument/spine splitting and `CompilerFunctionRel` provide the canonical whole-pass relation; constructor calls prove exact saturation and preserve wrapper provenance; scalar externs cross an explicit oracle-compatibility contract. Static `.ref` dispatch covers definitions, recursors, constructors, and externs, while ordinary variables, synthetic `recSelf`, dynamic heads, erased arguments, and nested applications meet in `lowerSpine_run_value_sound`. Standalone `.app` and `.ref` expression routes are therefore semantically connected. **Reachable semantic induction closed (2026-08-24):** erased reflection is proved for all fuel; `SelfValueAvailable` threads substantive current-self contracts only through recursor environments; argument, borrow, apply-rest, spine, and expression judgments are indexed by an ambient final compiler state; and `lowerValueClusterWithin` closes their mutual compiler-fuel induction. `LowerResultValueSound.closeGraph` plus `lowerAllAction_main_value_graph` carry that result through the actual compiled main for arbitrary successful source/compiler/target runs, while `lowerAllAction_semanticForwardSimulation_of_targetProgress` isolates target-run existence as the separate progress premise. **Semantic contracts sealed (2026-08-24):** exact-fuel ordinary definitions, generated recursors (including Nat peeling and rule-index agreement), lifted paps, constructor wrappers, and `applyGo` now meet in `lowerAllAction_compilerValueContracts`. The seal recovers each exact `lowerDecl` run from the whole-pass trace and derives dead-parameter admissibility from successful `releaseSlots`; `lowerAllAction_main_value_graph_sealed` and `lowerAllAction_semanticForwardSimulation_of_targetProgress_sealed` no longer accept `CompilerValueContracts`. **Closed-world settlement landed (2026-08-25):** source-guided call and extern progress now strengthen the terminal classification itself, so `lowerAllAction_unknownRefUnreachable_sealed` is derived from the same whole-pass settlement and forward simulation no longer accepts a separate unknown-reference premise. **Certified erasure now closes call-aware target progress and semantic simulation (2026-08-25):** the exact fuel-indexed `IxIR0.ProjectionSafe` `Eval`/`Apply`/`Saturate`/`Fire` traces carry every dynamically selected definition, lifted closure, and recursor-rule body. Erasure and the executable validator derive those traces for the complete proof-producing `PErase` fragment, including sharing transport and the validator's exact `CertifiedSharedExpr.target`. Source-fuel-indexed declaration and application contracts then drive a strong induction over strictly smaller calls; the general `applyGo` producer covers erased functions plus pap under-fill, exact saturation, and over-application. IxIR₁ erased application now consumes its argument ownership before returning erased, matching IxIR₀'s absorbing application rule. `lowerAllAction_compilerTraceProgressContracts` rebuilds the mutually recursive callable package from actual whole-pass provenance, `lowerAllAction_main_progress_of_certificate_sealed` proves exact target success, and `lowerAllAction_semanticForwardSimulation_of_certificate_trace_sealed` closes the semantic endpoint with no `CompilerProgressContracts` premise. `CompilerContracts`, scalar extern value compatibility, and extern trace termination remain explicit boundaries. |
| Progress (`Err.mem` unreachability) | active | `Mono.lean` proves success monotonicity and persistence of every reached non-fuel error for the complete mutually recursive evaluator (with public code/op/invoke/apply/drop and top-level specializations). `Progress.lean` gives all-fuel safety and existential termination for shared/unique deep release; settlement now admits only success or ordinary stuckness, excluding both memory and closed-world failures. `LowerProgress.lean` carries successful progress and that stronger settlement through the continuation-style emitter API. The erased-slot seam is formal: `erasedReleasedSlot_fetch_not_progress` refutes unconditional successful progress, while `fetchErasedSlot_stop` admits the ordinary-stuck result safely. Settlement covers every argument operation, static/dynamic/erased spine shape, standalone reference, projection, let branch, and expression head; `lowerValueSettlementClusterWithin` closes their compiler-fuel induction. `lowerAllAction_main_settlement` yields both `lowerAllAction_memoryErrorUnreachable` and `lowerAllAction_unknownRefUnreachable`, with value-contract-sealed variants for actual whole-pass output; the latter removes the separate unknown-reference premise from `lowerAllAction_semanticForwardSimulation_of_admissibility_sealed`. The generic bridges are `memoryErrorUnreachable_of_settlement` and `unknownRefUnreachable_of_settlement`, and both sealed conclusions are axiom-fenced. `ProjectionSafeEval.of_erasure` now turns every successful proof-producing erasure trace into the constructor-only source invariant needed by the complete safe-progress cluster. `lowerAllAction_main_progress_of_projectionSafe` yields a successful exact-main run; monotonicity then gives all-fuel ordinary-stuck exclusion. Exact call-aware traces retain the validated callable-body evidence that raw provenance lacks. Source-fuel-indexed declaration/application producers and `lowerAllAction_compilerTraceProgressContracts` construct the full callable package from the actual whole pass; `lowerAllAction_main_progress_of_certificate_sealed` and its trace-sealed semantic corollary therefore need no `CompilerProgressContracts`. The row stays active for progress generalizations beyond the certified fragment and for the separate cost obligations |
| Reclamation | done for the current no-`reuse` lowerer (08-27) | `Reclamation.AllocationOrderInvariant` records positive live counts and strictly backward node edges for append-only heaps. Exact empty-root ownership then forces an impossible finite ascent, giving `live_eq_zero_of_empty_roots`; shared and unique release combine that result with release progress. `NoReuse.lean` proves exact reuse-counter preservation for every evaluator entry, proves every successful compiler emitter/body/recursor/wrapper and the complete `lowerAllAction` declaration list reuse-free, and combines `lowerAllAction_main_owned` with the zero-reuse trace bridge in `lowerAllAction_reclamation`. `NoReuseAddressed.reclamation_mapAddresses` transports release and live-count emptiness through any certified context renaming, with transparent and indexed fully-addressed production corollaries. The finite theorem, runtime/compiler bridge, concrete whole-pass theorem, and addressing boundary are axiom-fenced. In-place `reuse` deliberately remains outside this concrete-order invariant and will need a topology-preserving generalization when lowering begins to emit it |
| Cost refinement | done for the current lowerer (08-28) | `LowerSim.RunCostInvariant` separates result-independent counter facts from semantic `ValueGraph`, lifts them generically into `CostRefinement`, composes independent refinements pointwise, and uses successful-run uniqueness to promote one exact execution witness to all sufficient fuels. `Reclamation.StoreFootprint` carries allocation and live/free balance through every successful evaluator entry, including deep release, pap application, calls, and in-place reuse; fresh runs satisfy `nodes.size = allocs` and `live + frees = allocs`. `AllocationFreeCostSpec` exposes `frees ≤ allocs`; the current lowerer combines that law with exact `reuses = 0`, and the indexed fully addressed boundary transports both. `CostInstance.loweringCostWitness` pins a real nullary-constructor run at `(1, 0, 0, 0)`. `CostModel.loweringCostWitness` generalizes actual whole-pass lowering to every unary-constructor depth `n` at `(n + 1, 0, 0, 0)`, with source-result allocation and RC bounds. `IxIR0.DynamicCost` assigns an additive profile to successful `Eval`/`Apply`/`Saturate`/`Fire` derivations, so entered closure bodies and dynamically selected recursive rules contribute compositionally rather than by surface syntax; `ProjectionFree.Eval.of_run` recovers the trace from ordinary successful projection-free runs. The audit exposed an expressiveness gap in event counts alone: one closure event can capture an arbitrarily wide environment, and one pap event can duplicate an arbitrarily long captured prefix. The profile therefore now has an additive `retains` coordinate charged by dynamic environment, captured-prefix, and recursor-field widths. `IxIR1.CostTrace.ownershipAmortizedWeights` is a fixed tariff independent of the fixture observation: each evaluation pays `(1, 0, 1, 2)` and each retain candidate pays `(0, 0, 0, 2)`; `OwnershipAmortizedSpec` states the resulting componentwise obligations. `ObservationGrowthLE` composes ordinary counter allowances. The RC side now uses the stronger `sharedRcPotential`: `amortizedRc = rcops + sharedRcPotential`, and `RcPotentialGrowthLE` composes its allowances. Allocation creates at most one potential unit; `dupVals_rcPotential_growth` charges at most two per retained runtime value (one immediate instruction plus one future-drop unit). The mutual fuel induction behind `dropVal_amortizedRc`, `dropMany_amortizedRc`, `dropUVal_amortizedRc`, and `dropManyU_amortizedRc` proves that every successful recursive release conserves the amortized measure under the append-only positivity invariant, regardless of heap depth or branching. The strengthened induction simultaneously proves exact allocation-counter preservation for shared and unique deep release. `localOpOwnershipAllowance` now pairs ordinary allocation with RC potential for every non-recursive append-only primitive: allocation and PAP creation cost `(1, 1)`, `dup` costs `(0, 2)`, and pure/free/drop/dropU/fetch/extern cost `(0, 0)`; reuse and recursive call/application operations remain explicit contract boundaries. `OpOwnershipCostSound.of_local` combines that proof-producing table with allocation-order preservation and environment bounds, while `EmitOwnershipCostSound.id`, `.comp`, `.localOp`, and `.closeRet` compose paired contracts across the lowerer's difference-list emitters. The earlier RC-only table and judgments remain as compatibility projections. `sourceProfileOwnershipAllowance` projects a trace to `(evals, 2·retains + 2·evals)` and is provably additive. `CodeOwnershipCostSound.runCertificate` closes any funded paired code contract into `OwnershipAmortizedRunCertificate`; allocation and zero-reuse facts plus a fresh-run potential bound then imply `OwnershipAmortizedSpec`, obtaining `frees ≤ evals` from exact heap balance and raw `rcops` by discarding the final nonnegative potential. `CodeOwnershipCostSound.withinBudget` reaches the public tariff directly, and `ProfileCostRefinement.of_ownershipAmortizedCertificate` lifts the certificate to the profile-sensitive refinement. `DynamicCost.Eval.surfaceEvals_le` proves a profile lower bound from executed surface sites. Consequently `SimInstance.addIxIR1DynamicCostRefinement` derives at least 15 evaluations for the actual recursive whole-pass `add 2̂ 3̂` program and covers its exact target observation `(12, 0, 6, 24)` without putting that observation into the weights. The profile, potential algebra, deep-drop theorem, certificate seam, and concrete cone are axiom-fenced. Paired recursive run contracts now cover `call`, `callSelf`, `apply`, `invoke`, and every `applyGo` shape; exact-continuation and state-indexed bridges instantiate primitive emitters against runtime states. Combined semantic/profile rules cover literal, erased, variable, complete `let`, borrowing, projection, and local-lambda lowering. The lambda path includes exact capture sequencing, arbitrary-count moves, retained-capture charging, lifted-function provenance, and PAP allocation, then widens the live-capture profile to the source environment's conservative retain width. The bounded `CompilerProfileContracts` fixed point now simultaneously seals source declarations, residual PAP invocation, and higher-order application from an actual whole-pass run. Ordinary definitions, recursors, externs, constructor wrappers, and lifted lambdas all have residual saturation certificates; `lowerAllAction_main_profileFundedCodeRun_sealed` closes the compiled main, `lowerAllAction_profileCostRefinement_sealed` exposes the generic raw theorem, and `lowerAllIndexedFullyAddressed_profileCostRefinement_sealed` transports the same budget through the SCC-aware production boundary. Source-profile completeness (for example, projection-free or certified call-aware traces), ownership contracts, and scalar extern compatibility remain explicit semantic premises. |
| `reuse_sound` modulo location renaming | done | premise generalized to `List.Perm` (08-19) with the transposition witness the old equality form could not instantiate — a two-field unique `Cons(x,xs)` reused as `Cons(x,acc)` (list-reverse shape), proved end-to-end beside the original identity-partition fixture (which now supplies `.of_eq`); `RootOwnership.perm` is the transport; counter differences remain deliberately outside `HeapIso`. Reuse pairing remains an IxIR₂ pass (M2c) |
| Result ownership in declarations | done | `IxIR0.Decl.defn` and `IxIR1.FnDef` carry `Owned`; erasure preserves the innermost Ixon arrow result (defaulting non-functions to `.shared`), declaration bodies lower at their signature, direct calls check demands, and shared paps/unknown `apply` cannot conceal unique results. `invoke` dynamically checks hand-written declarations, with `invoke_fn_result_hasWorld` connecting success to the simulation predicate. Erasure's forced `.many` on dropped binders/lets is the adjacent mode seam; the certificate side is the M2a `Owned`-fidelity row |
| Extern heap-argument consumption | queued | v1 dynamically enforces scalar-only arguments/results in both directions, so no heap ownership crosses; a production heap-valued ABI still requires an explicit ownership policy |
| Validator-gated pipeline | done | `Pipeline.compileValidated`: usage gate → addressed erasure (retaining exact raw output) → raw per-constant `Covered` coverage fixpoint → `certifyProgram`/`certifySharedProgram` → exact raw cross-check → lower the block-derived image → SCC-aware whole-program IxIR₁ addressing. The validator derives the simultaneous definition/recursor member scope from the exact submitted program, and the sharing-aware certificate retains the same member-coverage proof. It fails closed with the first validator or readdressing diagnostic. Native checks pin direct/validated equality of both maps and block identities, old-key absence, runtime/cost preservation, a genuine cyclic block through the sharing branch, and out-of-fragment behavior; `compile` remains documented as accepting out-of-fragment programs |
| IR content addressing | active (both whole-program passes, modeled-oracle coherence, and durable single-file plus indexed-chunk HPT caching landed, 08-26) | Canonical arbitrary-`Nat` encoding, exhaustive strict codecs, and twenty-two kernel roundtrip/canonicality/injectivity laws are fenced. IxIR₀ and IxIR₁ both have symbolic mutual blocks, collision-checked materialization, SCC-aware whole-program readdressing, executable semantic audits, evaluator transport, and complete production provenance. `LowerFullyAddressedSim` and `LowerMutualAddressedProgress` carry exact runs, errors, costs, final progress, and certificate-sealed forward simulation across both maps. HPT cache queries/summaries have strict record/store codecs, checked artifact-local rebuilds, bounded record-streamed snapshots, and a metadata-only per-key directory index that lazily reads dependency-selected chunks; all writes use atomic rename bracketed by ledgered staged-file and affected-directory barriers. Remaining addressing work is address-exact double compilation; streaming/sharded index maintenance, garbage collection, and cross-store scheduling remain later scaling work (`docs/ixir-content-addressing.md`) |
| Mutual blocks in the IRs | done (both production passes, 08-26) | both IRs have exhaustive symbolic syntax, strict scope-aware codecs, independently derived member identities, collision-checked producer/ingress materialization, executable audits, frozen genuine-cycle vectors, whole-program SCC integration, and evaluator/proof transport. The ordinary evaluators continue to consume materialized address environments; a real two-definition cycle now crosses both production passes and the sharing-aware validated pipeline |
| HPT analysis + certificate checker | active (bounded, durable single-file plus lazy indexed-chunk storage, semantically sound recursive-field stage and readdressed declaration-graph consumer, 08-26) | `IxIR1.HPT` checks an untrusted whole-program post-fixpoint over scalar, constructor, PAP, and unknown-heap facts. Detailed constructors recursively retain exact field facts within explicit depth, shape, field, and coordinate budgets; allocation, fetch, reuse, and case binders preserve that detail, while identity-only/dynamic uncertainty and alias-sensitive reuse widen conservatively. Version-3 query/summary identities and version-2 artifact records make the recursive encoding an explicit address/wire roll; strict cache ingress and artifact-local repair still cross the ordinary checker. The mutually recursive store interpretation and subset/conversion lemmas are axiom-fenced, and a depth-two fixture covers double fetch, nested cases, exact/one-below checker/cache limits, codec roundtrips, deterministic production, and shallow-budget widening. Single-file ingress/staging verification processes one bounded record at a time; `HPTCacheDirIO` separately indexes canonical singleton chunks from headers and lazily loads only dependency-selected payloads under exact entry/framed/read budgets. The ledgered native boundary durably publishes both snapshots and independent chunk repairs. Regressions pin pure-codec parity, malformed-stream and namespace rejection, stale-corruption isolation, selected local repair, sync type discipline, cleanup, full replacement, and ignored orphan transactions. The checked case-pruning consumer rewrites one root, supplied code, or the complete declaration graph with exact evaluator transport. Streaming directory enumeration, sharding/GC, cross-store scheduling, and controlled power-cut recovery remain future scaling/platform evidence (`docs/hpt-certificates.md`) |
| IxIR₀ˢ specialization | queued | scalar/layout refinements before lower native IRs |

### M2c — native/zk backend wedge

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| ISA decision record | done | decided 2026-08-25 (JCB): **x86-64 first**; RV64 re-sequenced to ISA #2 with named wake conditions (Sail→Lean export maturing, zk/attestation demand, RISC-V host demand) — `plans/isa-decision-2026-08-25.md`. Deciding argument: certification-bar parity — the Sail→Lean export is not yet a usable proof substrate, so every candidate proves against a hand-written fragment semantics at the CompCert boundary, collapsing the proof-ease case and leaving bootstrap/host economics decisive (single x86_64 machine, native differential co-sim on the deployment silicon, Tc-parity reachable with one backend). Encoder trust is staged, not permanent: the AST→bytes layer is scheduled for per-form verification into the fence (E0→E2), ultimately exceeding the CompCert bar at the encoder. Also disposes the `bootstrap-strategy` open decision point; zk alignment recorded as neutral post-SP1/Zisk (the native/zk split is at the shared middle IR) |
| IxIR₂ CFG/join-point IR | queued | activates after the M2b simulation foundation; owns the free+alloc→`reuse` pairing and the brecOn→direct-recursion recovery question (essential for performance, under-formalized anywhere) |
| One ISA semantics + emitter | queued | x86-64 System V user-mode fragment per `plans/isa-decision-2026-08-25.md`: hand-written fragment semantics over a typed instruction AST shared with the emitter (fragment containment by typing; the trusted surface is one `encode : Instr → Bytes` plus a minimal ELF64 `.o` writer and system `ld`, each a recorded trust row); oracle pinning vs. XED/objdump plus a test-only native co-sim harness; staged encoder verification E0→E2 (per-form round-trip/injectivity via the codec-lemma toolkit — no `bv_decide`, per the M1 finding — then the fetch/decode stream theorem under the emitter's boundary-integrity invariant); EFLAGS-locality selector invariant recorded up front so flags stay out of the simulation relation; scalar division lowers to a runtime intrinsic to keep the #DE trap surface out of v0. "Sail-derived semantics preferred" survives as the ISA #2 wake condition, not as ISA #1 guidance |
| Regalloc/analysis certificate checker | queued | must refine the shared middle semantics; `EraseValidator` is the established proof-producing-validator template. x86 costs recorded in the ISA decision: tied two-address operands and 15-GPR pressure land in the checker; EFLAGS appear only as local def-use pairs (the flags-locality selector invariant keeps flag liveness out of the certificate) |
| Defunctionalization boundary decision | queued | GRIN-style whole-world analysis inside the addressed closure vs. closure fallback at open boundaries |
| End-to-end FIP benchmark | queued | the interpreter-level FIP guard exists but runs hand-written IR — no compiler path emits `reuse` today (pairing is the IxIR₂ row); missing: one native binary, result and capability checked — under the ISA decision that binary runs natively on the existing x86_64 check surface, no emulator in the loop |
| zk target + cost model | deferred | design the shared-middle cost semantics against Aiur constraint costs; the zk path is active upstream (external coordination) — the remaining confirmation is the joint cost-model conversation |

### M2.5 — measurement and corpus contact

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| Instruction-level alloc/reuse/free/RC counters | done | IxIR₁ `Store` and exact guards |
| Interpreter-level counter benchmarks | done (fragment) | Landed 2026-08-25 in `IxIR1/ThesisBench.lean` and `docs/thesis-counter-evidence.md`: three mechanically same-shape (`eraseModes`) all-shared/mode-directed pairs pin equal decoded results and exact before/after-release counters. Totals hold allocations/frees fixed at 18/18 with zero reuse while RC instructions fall from 18 to 3 (15 saved, 83⅓%); the mixed dead-parameter case keeps the result shared and isolates a two-RC saving on only its affine dead argument. Mode-adversarial guards pin duplicate shared vs. linear, dead affine vs. linear, dereliction, and freeze boundaries. Frontier: deterministic interpreter counts are not wall time; unique data is still never inspected, so the first computational unique fixture (list reversal through a case) awaits unique destructuring, and compiler-emitted reuse awaits IxIR₂ pairing |
| Untrusted-ingestion readiness gate | done (bounded in-memory boundary, 08-25) | The object/address/index/performance/certificate slices remain as previously recorded. `Ixon.Catalog` closes the multi-object boundary over ix v1 `.ixc` manifests and ixon-v2 anonymous `.ixe` semantic prefixes: strict/resource-bounded framing; exact pinned-ix compressor-image recognition; file, blob, constant, environment, member, and content-root binding; fat identical-overlap dedup vs. chunk no-redeclaration; owner-wise chunk member coverage; and store-wide projection/constructor coherence. `CatalogIO` adds a non-symlink regular-file directory adapter with pre-read declared/observed size gates. Aggregate limits count storage occurrences separately from the final union, with exact-boundary/one-below tests plus manifest/piece truncation and file/inner-hash drift. The output is the sorted constant list consumed by `Pipeline`. Scope is explicit: `.ixe` name/metadata/comment tails are hash-bound but opaque, and the API is bounded/in-memory; streaming/mmap and chunk-wise certificate scheduling remain scalability work (`docs/catalog-ingress.md`, `docs/resource-budgets.md`) |
| Native/atomic/zk benchmark dimensions | deferred | native time needs M2c; atomic RC needs a thread model (deferred axes); zk cost needs the M2c cost model |
| Corpus fixture format + loader | done (bounded in-memory, 08-25) | `Catalog.load[With]` accepts the exact ix `.ixc` manifest bytes plus positionally resolved fat/chunk `.ixe` bytes, applies `DecodeCheck.decodeIxonV2CheckedWith` and `Constant.addressIxonV2CheckedWith` to every stored constant, verifies all catalog commitments and duplicate rules, and returns a sorted deduplicated `List (Address × Constant)` plus raw blobs and exact stats. `CatalogIO.loadDir[With]` resolves the exact fat/chunk filenames behind pre-read file and aggregate limits; `catalog-contact` is the compiled operational harness. The contracts, opaque anonymous metadata tail, defaults, and future streaming adapter are specified in `docs/catalog-ingress.md` |
| Well-moded program generator | done (executable, 08-25) | `IxIR1/WellModedGen.lean` generates 260 seeded/replayable closed mains across all 26 schemas: 180 accepted source/target tree-agreement + leak-freedom cases and 80 exact-diagnostic mode-boundary rejections. It covers unique-consuming and exact-once linear values, dead affine/shared bindings, mixed-mode calls, projections, recursion, externs, captures, paps, erasure, freeze/dereliction, and other ownership errors. Template-preserving shrinking is invoked on failure; seed, final state, counts, and fingerprint are pinned in the compiled test (`docs/well-moded-generator.md`). `nix flake check path:.` is green with the compiled corpus in `tests` |
| First bounded Std catalog fixture | done (production contact, 08-25) | A byte-exact one-member fat catalog generated by ix `6f18ea90` from a theorem closure over real `Std` is checked in as hex with no reencoder. `Catalog.load` accepts all 54 constants under unchanged defaults and freezes roots plus every aggregate counter (267-byte manifest, 14,600-byte piece, 2,143 stored / 3,877 expanded expression units, 34,656 layer-1 visits). Upstream `check-rs` accepts 47/47 work constants; Compilatrix then deterministically reaches the honest current-fragment boundary, rejecting address `131533e9...c6c4` with `freezeNeeded`. The compiled regression pins bytes, hash, provenance, roots, stats, and outcome; `CatalogIO`/`catalog-contact` exercises the directory path. Available 49 GiB Palomar and incomplete 101 GiB TruthMines material exceed the in-memory policy and motivate streaming/chunk scheduling rather than widened limits (`docs/corpus-contact.md`) |
| Address-equality frontend oracle | queued (contact trigger met, 08-25) | Compare complete re-encoded environments, not pretty syntax — this is the compat-bar metric for upstream-elaboration parity. Activate after the well-moded generator tranche or earlier if an upstream frontend artifact becomes available |
| Ix.Tc parity benchmark | deferred | trigger: native backend. stdlib/mathlib, 1 and N threads; the borrow axis (deferred axes) is the concurrency keystone |

### M3 — kernel theory and self-hosting bridge

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| Theory bridge to lean4ix + ix Tc verification | queued (re-scoped 08-25) | *replaces the former "vendor as ix4lean" row* (`plans/ix-rebaseline-2026-08-25.md`): the theory home is public `argumentcomputer/lean4ix` plus ix's `Ix/Tc/Verify/` (substantially public; 4.33/v2 rebase on the branch). This repo's obligations shrink to the bridge — erasure adequacy stated against that theory, `many_fragment_conservative` stated against the lean4ix pin. `plans/ix4lean.md` retained as the historical vendoring runbook |
| Reconcile scope with ix's Tc verification | done (08-25) | resolved by the re-baseline decision record: adopt/bridge — no local vendoring, no local checker rewrite |
| Extend theory with Uses/Owned | queued | prove `many`-fragment conservativity, stated against the pinned public lean4ix as the credibility anchor (anchor renamed 08-25; obligation unchanged) |
| Ixon-native checker retarget | retired (08-25) | overtaken: ix's checker is Ixon-native and is being verified in the ix line; nothing to retarget here |
| Connect Ixon semantics/erasure adequacy | queued | replaces fresh evaluator assumptions with the theory bridge |
| Bootstrap realism | queued | examine upstream stage0 reproducibility; decide the Gen-1 performance fallback (is an interpreter-speed self-host acceptable?) — cheap to de-risk early; the answer shapes M2c priorities |
| Compile the compiler with itself | deferred | requires native backend + runtime subset |
| Diverse double compilation | deferred | address-exact independent Gen-1 reproduction |

### M4 — frontend and statement faithfulness

Deliberately sequenced after the backend spine — recorded here so the
narrowed near-term mission is a decision, not an omission. Activates on
demand or after M3.

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| Vendored-elaborator retargeting | deferred | vendor upstream parser/macros/elaborator; retarget to mode-annotated Ixon with usage/universe metavariables |
| Mode surface syntax v0 | deferred | explicit annotations only, no usage inference; strawman in `plans/` |
| Statement faithfulness | deferred | verified printer + round-trip theorem; statement-faithful zk certificates. Kernel soundness alone does not prevent misleading-statement attacks |
| Reflection/TCB policy | deferred | if ix admits proof-by-evaluation, the backend enters the soundness TCB, outranking frontend verification — record the policy either way. The codec `bv_decide` finding was a concrete instance of this trust class and was retired 2026-08-26 by replacing native reflection with kernel-checked proofs; the broader policy question remains |

## External coordination

Sequencing this repository does not control; each item names its in-repo
consequence.

| Item | State | In-repo consequence |
| --- | --- | --- |
| ix Ixon-v2 merge branch | **pushed** (08-25) | `jcb/ix-formalization3` @ `6f18ea90` (includes the main merge: TruthMines, lean4ix, v4.33.1) carries wire-identical v2 end-to-end (Lean + Rust) plus the `Ix/Compile/Verify` formalization. Compilatrix re-baselined onto it **by revision** — stage-1 vectors now mechanically confirm local codec bytes/addresses and record the compressor boundary (`plans/ix-rebaseline-2026-08-25.md`). Operating model recorded there: within one format id the two implementations are byte-identical (vector-pinned); new annotations fork under a format-id bump, staged here first, ported upstream when stable — the flow that produced v2. Remaining PR-shaped items: upstream the strict-decode deltas (DefKind/safety catch-alls, L1 sharing rules — both directions local-stricter) and the store-ingest policy; the transition decision landed in the staged code as an env-version-2 cutover; the reencoder is demoted (M2.5) |
| ix parity baseline staleness | resolved (08-25) | exact rev/tree capture at `6f18ea90`/`c09cfe3d`, frozen in local runtime vectors; four compressor cases are exact and two stricter local outputs are explicit waivers. The obsolete `c98bb741` harness and subproject are deleted |
| Toolchain reconciliation | staged (08-25) | public ix and the branch are on v4.33.1; this repo pins v4.33.0. Bump staged at re-baseline stage 2 (branch merges to ix main), together with the flake lean4-nix pin. The obsolete v4.31 capture subproject was retired in stage 1 |
| zk path | active upstream | Aiur is core and moving (FFT cost model 2026-08-07; a plan exists to transport the proved Tc acceptance property to the Aiur stack); remaining confirmation is the joint cost-model design conversation before the M2c cost model hardens |
| lean4ix (ex-lean4lean) tracking | passive | the argumentcomputer fork became the standalone public repo `argumentcomputer/lean4ix`, pinned by ix (#592); tracked as the theory anchor for the M3 bridge — local vendoring dropped (M3 rows, 08-25) |
| Ix.Tc DAG-schedule restructuring | overtaken, ix-side | ix implemented work-stealing over an atomic next-index instead of a DAG schedule; the parity benchmark design should assume that reality |

## Deferred axes registry

Design axes intentionally frozen. Previously registered only in untracked
notes; one line each — the design note is the record.

| Axis | Design note | Wake condition |
| --- | --- | --- |
| Borrow (`&`) | `plans/substructural-types.md`, `plans/backend.md` | promoted to design driver by Tc-parity concurrency; earliest at IxIR₀ˢ |
| Regions/locality | `plans/regions.md` | v1 library `runRegion` after M2b; v2 locality mode bit requires a hash roll |
| Usage polymorphism | `plans/Uses.lean` | blocks mode-polymorphic recursors and generic `map`; earliest with IxIR₀ˢ |
| Modal inductives + layout/unboxing | `plans/substructural-types.md` | with IxIR₀ˢ specialization |
| Capability-ladder certificates | `plans/substructural-types.md` | rc-free → heap-free → alloc-free → panic-free; with the native backend |
| Duplication primitives / freeze representation | `plans/Uses.lean` | uniform rc-headers vs. headerless unique — decide before IxIR₁ layout freezes further; this is a wake condition for the planned `Op.freeze` lift, not pre-decided by the v0 restriction contract |
| Floats | `plans/runtime.md` | IEEE/Flocq-style axiomatization; on demand |
| Threads / atomic RC | `plans/runtime.md`, `plans/backend.md` | a thread model precedes the atomic benchmark dimension and Tc parity |

## Runtime retirement track

The per-symbol state and exit criteria live in
[`trusted-extern-ledger.md`](trusted-extern-ledger.md). Near-term persistent
runtime work is allocator/memcpy-class primitives, verified bignums, and the
syscall boundary; floats and threads are deferred axes above. "Empty target
extern ledger" is a long-term milestone; bootstrap provenance remains a
separate obligation.

## Immediate implementation queue

1. **Generalize the semantic whole-pass theorem — completed for the
   validator-certified fragment (2026-08-25)**: the first exit is met —
   `addIxIR1CompilerContracts` seals ownership on the exact SimInstance output,
   and `addIxIR1SemanticForwardSimulation` gives that compiled main a
   source-to-target `ValueGraph` theorem without `native_decide`. The
   architecture is a companion semantic refinement layered over the existing
   `LowerResultSound`, not an expansion of its ownership postcondition. The
   first duplication cut is landed: uniform bounded proofs close through
   `EmitSound.of_below`, with the base/primitive/call/apply pairs sharing one
   proof body. Continue collapsing recursive pairs as they are touched. The
   fifty-third cut gives `releaseSlots` separate foundational traversals for
   successful runs and action-level properties. Mode rejection, environment
   and depth threading, tail recovery, and emitter reconstruction now recurse
   once across no-`recSelf`, entry-count, admissibility, and reuse-freedom;
   monadic sequencing recurses once across `ExtraMonotone` and
   `PreservesStateNoReuse`. All six public signatures remain unchanged, while
   the proof-producing `ReleasePlan.run` recursion stays at its distinct plan
   boundary. The fifty-fourth cut promotes raw `releaseAll` traversal into
   `LowerStateBase`: empty, constant, and slot normalization, environment
   advancement, and drop-emitter composition now recurse once across
   no-`recSelf`, entry-count, `recSelf` position, exact-entry, and reuse-free
   clients plus the paired cost consumers. The existing
   `LowerSim.releaseAll_traverse` signature remains as a compatibility wrapper
   over the foundational core, and all downstream public signatures are
   unchanged. The fifty-fifth cut places a dependent
   `selectedEntriesFrom_traverse` beside the entry builder: selected-bit
   dispatch, consecutive absolute-slot advancement, and released/held entry
   construction now recurse once across length, runtime realization,
   source/runtime value graphs, and no-`recSelf`; adapters retain only their
   filtered-source, slot-lookup, world, and graph evidence, and every existing
   public signature remains unchanged. The fifty-sixth cut places a dependent
   `parameterEntries_traverse` beside the canonical parameter-telescope
   builder: tail layout, absolute-slot advancement, and appended-slot
   construction now recurse once across length, no-`recSelf`, runtime
   realization, and source/runtime value graphs; adapters retain only their
   list arithmetic, slot lookup, world, and graph composition, and every
   existing public signature remains unchanged. The fifty-seventh cut gives
   canonical `parameterDrops` release planning one result-polymorphic
   `parameterDrops_releasePlan_traverse`: admissibility splitting, tail
   framing, output-length recovery, shared/affine release, entry update,
   depth advancement, and emitter composition now recurse once across the
   ordinary and count-tracking constructors; the tracked adapter supplies
   only empty/live/dead output invariants, and every existing public signature
   remains unchanged. The fifty-eighth cut places a dependent
   `recursorFieldRetains_traverse` beside the canonical retain builder and
   layers a result-polymorphic `recursorFieldRetains_plan_traverse` over it:
   descending entry indices, ascending absolute field slots, zero-use
   omission, released placeholder framing, live-slot activation, depth
   advancement, and `dup` emitter construction now recurse once across
   ordinary/count-tracking plan construction, runtime coverage, value-graph
   alignment, and retain-count bounds; adapters retain only output invariants
   and witness transport, and public signatures remain unchanged. The
   fifty-ninth cut routes the remaining structural APIs of `ReleasePlan` and
   `FieldRetainPlan` through their existing dependent traversals: logical-entry
   length preservation, appended-frame transport, prefixed-entry transport and
   descriptor offsetting, sequential release-plan composition, and exact
   `releaseSlots`/`applyRecursorFieldRetains` execution no longer recurse
   independently. Each plan family now has exactly one direct plan induction;
   the duplicate all-shared parameter-admissibility proof is a compatibility
   alias to the canonical theorem, and every public signature remains
   unchanged. The sixtieth cut gives `EntriesRealize` and
   `EntriesValueGraph` one dependent traversal each: logical-entry,
   source-value, and root threading plus released/held/`recSelf` dispatch now
   recurse once across append, graph forgetting and reconstruction,
   source-length and lookup, depth/store transport, and indexed
   release/hold/counter-update clients. Callbacks retain only their
   judgment-specific slot, world, value, root, and store-witness transport;
   both relation families now have exactly one direct induction, and every
   public signature remains unchanged. The sixty-first cut gives
   `LambdaPrefix` one dependent traversal: source-environment growth, lambda
   peeling, supplied-prefix threading, and residual-value propagation now
   recurse once across the strict arity bound, one-step under-saturated
   extension, full semantic saturation, closure shape and non-erasure,
   canonical projection-safe replay, and profile saturation and
   under-application funding. Callbacks retain only application/evaluation
   witnesses, replay bounds, reserve inequalities, and profile arithmetic;
   the relation now has exactly one direct induction repository-wide, and
   every public signature remains unchanged. The sixty-second cut gives
   `RecursorRulesPlanWith` one dependent state-threaded traversal: compiler
   state, source rule/tag, generated alternative, successful head execution,
   and the per-alternative contract now recurse once across exact `mapM`
   execution, pointwise contract membership, bounded alternative-to-source
   run provenance, and source-rule-to-selectable-alternative provenance.
   Callbacks retain only bind normalization, membership splitting, run-plan
   inversion, and tail witness packaging; the generic relation and its exact
   and bounded specializations now have exactly one direct plan induction
   repository-wide, and every public signature remains unchanged. The
   sixty-third cut gives `AValsStable` one source-neutral dependent
   traversal and rebuilds its source-aligned adapter on that foundation:
   slot-driven environment bumps and literal/erased identity threading now
   recurse once across aligned value/progress/profile release, descriptor
   realization after unrelated runtime pushes, and bounded ownership
   `releaseAll`. Callbacks retain only length inversion, one-descriptor
   realization, discard composition, graph transport, and profile arithmetic;
   the relation now has exactly one direct induction repository-wide, and
   every public signature remains unchanged. The sixty-fourth cut gives
   `AValsRealize` one dependent lockstep traversal: ownership-world,
   lowered-descriptor, runtime-value, and one-descriptor realization threading
   now recurse once across synchronized list lengths and exact `resolveAtoms`
   fold execution. Callbacks retain only successor-length arithmetic and
   one-atom resolution/composition; the relation now has exactly one direct
   induction repository-wide, and every public signature remains unchanged.
   The sixty-fifth cut gives `SourceArgsEval` one dependent lockstep
   traversal: source-expression/value threading, exact per-argument
   evaluation, and tail evidence now recurse once across length
   synchronization and prefix/suffix restriction. Callbacks retain only
   successor-length arithmetic and `take`/`drop` count dispatch; the relation
   now has exactly one direct induction repository-wide, and every public
   signature remains unchanged. The sixty-sixth cut gives `SourceApplies`
   one dependent state-threaded traversal: initial value, argument list,
   final value, exact head application, and tail evidence now recurse once
   across concatenation, numeric/list splitting, and result determinism.
   Callbacks retain only append normalization, `take`/`drop` count dispatch,
   and one-step fuel-independent uniqueness; the relation now has exactly one
   direct induction repository-wide, and every public signature remains
   unchanged. The sixty-seventh cut gives `ProjectionSafeArgs` one dependent
   lockstep traversal: source-expression/value synchronization, exact
   per-argument projection safety, and tail evidence now recurse once across
   length synchronization, ordinary semantic forgetting, and prefix/suffix
   restriction. Callbacks retain only successor-length simplification,
   evaluation-witness extraction, and `take`/`drop` count dispatch; the
   relation now has exactly one direct induction repository-wide, and every
   public signature remains unchanged. The sixty-eighth cut gives
   `IxIR0.ProjectionSafe.EvalsBelow` one dependent lockstep traversal:
   source-expression/value synchronization, exact per-argument fuel bounds
   and projection-safe traces, and tail evidence now recurse once across
   limit monotonicity, length synchronization, prefix/suffix restriction,
   address transport, and lowering conversion. Callbacks retain only bound
   transitivity, successor-length simplification, `take`/`drop` count
   dispatch, one-head address transport, and shallow-trace conversion; the
   relation now has exactly one direct induction repository-wide, and every
   public signature remains unchanged. The sixty-ninth cut gives
   `IxIR0.ProjectionSafe.AppliesBelow` one dependent state-threaded
   traversal: initial, intermediate, and final values, the argument spine,
   exact per-step fuel bounds and safe application traces, and tail evidence
   now recurse once across limit monotonicity, spine concatenation,
   numeric/list splitting, address transport, semantic forgetting, and
   dynamic-cost profiling. Callbacks retain only bound transitivity,
   append/`take`/`drop` normalization, one-head address transport, and
   semantic/profile conversion; the relation now has exactly one direct
   induction repository-wide, and every public signature remains unchanged.
   The source-environment relation,
   semantic argument sequencing, and
   scalar/final/repeated-variable companion rules are also landed;
   RC-increment and fresh-allocation transport are factored through
   `StoreGraphExtends`. Lifted paps now carry selected-capture and residual-
   closure correspondence backed by exact generated-body provenance, and the
   lambda branch produces a generic `ValueGraph`. Constructor allocation,
   graph-preserving slot/argument release, erased-application cleanup, and
   the generic let install/pop composition are now landed. Projection
   borrowing is landed too (08-22): the `lowerE`/`lowerBorrow` dispatch over
   all four descriptors, both source-shape-mismatched pairings closed by
   unreachability, the dynamic-borrow adapter, and two run-exhibiting
   fixtures — and with the literal, erased, variable, and let dispatches
   beside it, every `lowerE` head except `.app`/`.ref` now has a semantic
   dispatch. The call/application contract vocabulary, callee-frame
   reconstruction, static and dynamic spine routes, erased reflection, and
   the complete ambient-state compiler-fuel induction are now landed.
   `lowerAllAction_main_value_graph` applies the result to arbitrary
   successful `lowerAllAction` outputs and successful target runs;
   `lowerAllAction_semanticForwardSimulation_of_targetProgress` states the
   exact remaining split. The semantic-contract exit is now met:
   `lowerAllAction_compilerValueContracts` reconstructs ordinary and recursor
   declaration runs from the actual whole pass, derives dead-parameter
   admissibility from successful release execution, and seals declarations
   with `applyGo` by evaluator-fuel induction. The sealed whole-main and
   forward-simulation theorems no longer accept `CompilerValueContracts`.
   The separate progress row now has evaluator monotonicity for success and
   every terminal error, total deep release, source-guided callable
   contracts, and dual success/settlement continuation composition. A formal
   erased-slot counterexample shows that unconditional successful progress is
   false for raw IxIR₀ lowering; its full projection dispatcher instead
   settles safely at ordinary stuckness. The recursive settlement cluster and
   generic/value-sealed whole-main `Err.mem` exclusion are now closed.
   Settlement was then strengthened to exclude unresolved declaration and
   oracle lookups as well: `lowerAllAction_unknownRefUnreachable_sealed` is the
   fenced whole-pass consequence, and the public forward-simulation theorem no
   longer asks for `UnknownRefUnreachable`. The validated-erasure bridge is now
   complete rather than projection-local: `ProjectionSafeEval.of_erasure`
   proves constructor-only projection safety for every successful evaluation
   in the full `PErase` fragment, including indexed-recursion spines, and its
   sharing-aware companion transports that proof through `inlineSharing`;
   `ProjectionSafeEval.of_certifiedSharedClosed` and the sealed certificate
   endpoint consume the validator's exact `CertifiedSharedExpr.target`.
   `lowerValueProgressSafeClusterWithin` carries the invariant through all
   argument, call, spine, borrow, let, and expression lowering routes;
   `lowerAllAction_main_progress_of_projectionSafe` closes the exact compiled
   main. The sealed erasure theorems consequently exclude ordinary stuckness
   at every fuel and produce semantic forward simulation without an
   `OrdinaryStuckUnreachable` premise. The callable exit is now met as well:
   exact fuel-indexed `IxIR0.ProjectionSafe` traces retain the validated bodies
   selected by calls and recursors; source-fuel declaration/application
   producers cover erased application and pap under-fill, saturation, and
   over-application; and `lowerAllAction_compilerTraceProgressContracts`
   reconstructs the simultaneous package from actual whole-pass provenance.
   `lowerAllAction_main_progress_of_certificate_sealed` gives exact target
   success, while
   `lowerAllAction_semanticForwardSimulation_of_certificate_trace_sealed`
   removes the `CompilerProgressContracts` premise from the certificate-level
   theorem. The remaining explicit boundaries are ownership/value coherence
   (`CompilerContracts` and `ExternValueContract`) and scalar extern
   termination (`ExternTraceProgressContract`).
2. **Completed 2026-08-25 — M2a ghost arguments at definition heads**:
   `DefSpine` + `PErase.appDG`, proof-producing validator reconstruction, a
   contentful `7̂`-discard / `9̂`-result fixture, an axiom-fenced public
   simulation theorem, and exact definition-result `Owned` validation.
3. **Completed 2026-08-25 — UsageCheck semantic non-interference**:
   executable ghost-zero metatheory, exact checker/eraser drop alignment,
   common-target successful-run non-interference, and a checked/certified
   contentful dropped-variable occurrence fixture.
4. **Completed 2026-08-25 — Thesis counter evidence (fragment)**:
   three same-shape all-shared/mode-directed programs, exact result/counter
   reports, a pinned 18→3 aggregate RC-op delta, and mode-adversarial
   fixtures. Computational unique inspection still activates with the
   unique-destructuring lift.
5. **Completed 2026-08-25 — Re-baseline stage 1 golden vectors**:
   exact clean-archive capture at `6f18ea90`, upstream Lean/Rust sharing
   suite green, Rust/Lean constant writers equal, two constant byte/address
   pairs and six sharing frames frozen locally, four exact policy cases and
   two explicit strictness waivers, obsolete shell/subproject harness retired.
   The upstream strict-decode contributions remain external coordination; the
   v1→v2 reencoder leaves the queue (demoted to certified-pass candidate;
   M2.5 row, `plans/ix-rebaseline-2026-08-25.md`).
6. **Completed 2026-08-25 — untrusted-ingestion gate**: the codec/address
   slice is complete: `DecodeCheck.decodeChecked`, local
   index/universe/self bounds, evaluator-exact recursor-count coherence,
   structured contextual errors, explicit object/depth/sequence budgets,
   iterative flat decoding, checked encode-time `wireWF`, constructed-value
   address gating, serialized exact-boundary/truncated-hostile cases, and the
   deterministic no-crash/accepted-byte-canonicality harness. The next slice
   is also complete: a build-once hash index now backs source resolution,
   validator contexts, indexed lowering, and target evaluation on the corpus
   path, with fence-pinned equivalence to the transparent `Env.ofList` model
   and a 4096-entry executable guard. The performance/certificate slice is now
   complete too: one structural accounting module bounds layer-1 scans,
   sharing expansion/compression, monolithic erasure, all caller fuels, and
   proof-producing coverage scaling with exact structured failures. The
   certificate decision is bounded per-declaration proof construction with no
   catalog-wide `decide`/`native_decide`; oversized units fail closed pending a
   compact/chunked design. The final slice is now complete too:
   `Ixon.Catalog` mirrors `.ixc`/anonymous `.ixe` framing, binds file/object and
   Merkle identities, implements fat/chunk duplicate and member-coverage
   policies, aggregates every ingress dimension, and validates projection and
   constructor coordinates across the complete store. Exact-boundary,
   overlap, duplicate, truncation, hash-drift, and coherence regressions are
   compiled into `tests`.
7. **Completed 2026-08-25 — first bounded ix catalog contact**: the exact
   production Std closure under `fixtures/ixon-std-contact` passes the deep
   catalog boundary with 54 constants and unchanged defaults. Tests freeze its
   manifest/piece bytes and hash, provenance, member/content roots, every
   structural counter, and the exact downstream `freezeNeeded` result. The
   on-disk adapter and compiled `catalog-contact` target are part of the check
   surface. Measurements of the much larger available corpora are recorded in
   `docs/corpus-contact.md` as the streaming/chunk-scheduling frontier.
8. **Completed 2026-08-25 — well-moded IxIR₀ program generator**: the seeded
   260-case corpus covers all 26 positive/adversarial schemas, with 180
   source/target readback + leak-freedom checks and 80 exact mode-diagnostic
   checks. Every case self-replays from its seed/index/state token; schema
   shrinkers preserve expectations and minimize failures; counts, final state,
   and fingerprint are frozen in the compiled test. The full flake surface is
   green (`docs/well-moded-generator.md`).
9. **Completed 2026-08-25 — source quotient ι and M2a compilation**:
   configured source reduction with a distinct saturated wrapper, full
   sharing coherence, exact public erased bodies, generic partial/saturated
   logical-relation cases, proof-producing program and expression
   certificates, contentful `37` witnesses for both eliminators, and an
   axiom-fenced public simulation theorem. The address-equality frontend oracle
   remains queued because no independent frontend environment producer exists
   yet.
10. **Completed 2026-08-26 — mutual-block member coverage**: unfoldable and
    configured-opaque definition projections/members, non-self inductive
    members, and simultaneous cyclic definition/recursor closure are landed at
    evaluator relation, proof-producing validator, exact executable fixture,
    lowering-progress bridge, and axiom-fence levels. Opaque source evaluation
    now uses the emitted synthetic member address as its oracle identity, so
    the existing same-address oracle relation applies unchanged. The later
    IxIR₀ address pass now confines that `memberAddr` identity to the retained
    proof-facing intermediate rather than the production environment.
11. **Completed 2026-08-26 — IR content addressing, production
    block-identity and modeled-oracle stage**: `IxIR.Encoding` provides total canonical unsigned
    LEB128 (including a frozen `2⁶⁴` spelling), fixed-width addresses, length
    framing, and domain separation. Exhaustive IxIR₀/IxIR₁ declaration and
    mutual-block codecs have strict input-fueled decoders, exact re-encoding,
    independently derived member keys, and twenty-two fenced kernel
    roundtrip/canonicality/injectivity laws. Both layers now have collision-
    checked whole-program passes and executable semantic audits. IxIR₀
    grouping crosses erasure, evaluator semantics, exact validator traces, and
    the executable `ReaddressOracle` adapter. IxIR₁ `ReaddressAll` discovers
    SCCs across source and generated functions with hash-indexed, explicit-
    stack Kosaraju; stable dependency ordering hashes ordinary singletons and
    materializes cyclic components through `MutualBlock`. Extern ABI identities
    remain stable, constructor identities are retained as an audited reserved
    set, and every other producer is absent from final keys and references.
    `LowerFullyAddressedSim` transports exact execution, all public error
    exclusions, semantic graphs, and costs; `LowerMutualAddressedProgress`
    closes certificate-sealed target progress and forward simulation across the
    two complete maps. Both pipeline entries use this boundary and retain
    artifact/block provenance plus `targetAddressMap`. A frozen genuine source
    cycle crosses both passes and direct/sharing-aware validated compilation;
    an 8192-node chain guards iterative SCC discovery. `synthAddr` and
    `memberAddr` are therefore proof-stage labels, not production declaration
    keys. The IxIR₀ audit now certifies that stable, reserved, and all
    declaration/main external identities are absent from both sides of the
    member map. A reusable isolated-key rule proves coherence of the exact
    ledger-recorded Nat-add oracle; a frozen cyclic block calls it and returns
    `42`, and the theorem cones are axiom-fenced. IxIR₁ externs retain their
    ABI keys by construction. The reusable IxIR₁ already-addressed graph
    rebuild now runs the SCC pass through a temporary producer namespace,
    certifies an exact source-to-emitted graph action, and transports complete
    evaluator results without source aliases. HPT cache snapshots now use
    bounded record-streamed ingress, verified sibling staging, staged-file and
    affected-directory stable-storage barriers, and atomic rename. A separate
    metadata-only directory index lazily schedules canonical per-key chunks and
    durably repairs only selected misses/rejections. The next addressing work
    is address-exact double compilation; sharded/streaming index maintenance,
    garbage collection, and cross-store scheduling remain scaling extensions;
    any future production oracle is a new per-service
    ledger/correspondence obligation.
12. **HPT analysis + certificate checker — active; persistent semantically
    sound recursive-field stage and readdressed complete-program consumer
    completed 2026-08-26**: `IxIR1.HPT` introduces the
    first untrusted analysis boundary over the exact `ReaddressAll` graph. Its
    canonical domain distinguishes scalar results, constructor identities,
    exact PAP targets/fill counts, and unknown heap. Constructors may carry a
    recursively detailed field vector whose entries preserve
    scalar/constructor/PAP roots and their retained constructor fields.
    Allocation records those facts, fetch re-roots a selected field, and reuse
    forgets alias-sensitive argument identities before storing them. All
    parameters start at `top`;
    identity-only and dynamic fetch uncertainty widens conservatively. The
    case transfer resolves its scrutinee, filters finite constructor shapes by
    alternative tag and exact arity, reverses source-order fields into evaluator
    binder order, and joins matching vectors pointwise. Matching identity-only
    or unknown facts widen the binders, while Nat tag 1 recovers a scalar
    predecessor when peeling is enabled. The
    checker requires an exact whole-program post-fixpoint, canonical/unique
    coverage, static call/PAP well-formedness, scalar extern facts, and a linear
    structural preflight before interpretation or hashing. It materializes
    summaries at ordinary/mutual-SCC granularity under version-3 recursively
    field-aware
    domains, binding each cache query to its program artifact plus prior
    dependency-summary addresses. A frozen precise/widened fixture covers PAP
    application, a detailed constructor, an allocation→fetch path, and a
    genuine two-member cycle; five cache keys and summary addresses,
    dependency-cone invalidation, tamper rejection, exact and one-below budgets,
    pipeline `Certificate.top`, success theorems, and axiom fences are checked.
    `IxIR1.HPTSound` gives result and field facts a concrete meaning over
    evaluator stores and values, then proves the complete code/op/invoke/apply
    transfer by mutual fuel induction without assuming well-moded code.
    Executable post-fixpoint acceptance implies that local premise, so every
    accepted function row covers every successful saturated invocation; the
    pipeline exports the same theorem against its exact target environment. A
    mutually recursive family of pure semantic lemmas interprets every
    retained field layer and transports refinement through allocation, fetch,
    and constructor/Nat alternative environments. A separate content-addressed regression checks
    precise and joined fields, binder reversal, wrong-tag filtering, widening,
    alias-forgotten fields, Nat peeling, checker and producer acceptance, and a
    concrete Nat `7` result. A depth-two fixture checks double fetch and nested
    case precision, concrete Nat `11` results, deterministic production,
    recursive cache record/store roundtrips, exact and one-below depth limits,
    and conservative shallow-budget producer widening. A
    deliberately aliased unique-node fixture proves why old finite facts are
    forgotten: reuse changes constructor A to B, the exact-A claim is rejected,
    and the accepted unknown-heap row covers the observed B result.
    `IxIR1.HPTProduce` follows the committed dependency order, solves each
    ordinary or mutual artifact from bottom with synchronous inflationary
    rounds, and preserves prior summaries in a hash index. Independent
    per-artifact/global round caps plus shape and field caps widen only the
    current artifact to `top`; the final candidate still crosses `runWith`.
    `Production` stores that checker equality and exposes post-fixpoint,
    content-audit, and evaluator theorems through both HPT and pipeline APIs.
    The fixture reaches the hand-authored precise result in exactly nine rounds,
    repeats byte-for-byte, widens only the SCC at eight, and exercises
    independent shape and field fallbacks. `IxIR1.HPTCache` assigns independent
    versioned domains to canonical artifact records and sorted store files,
    bounds parsing before variable allocation, and schedules exact-query,
    content-audited, locally post-fixed hits in dependency order. Missing or
    rejected rows rebuild with the same local producer; downstream keys observe
    the accepted summary address; and the assembled candidate crosses the
    ordinary whole-program checker. `Cache.Production` retains that checker
    equality, with its post-fixpoint/audit/evaluator and pipeline corollaries
    axiom-fenced. `HPTCacheIO` provides a bounded non-symlink regular-file
    adapter and the pipeline exposes pure and file-backed APIs. Cold/warm,
    malformed-record repair, widened dependency cones, deterministic store
    ordering, duplicate/noncanonical/outer-corruption rejection, filesystem
    contact, and exact/one-below cache budgets are compiled regressions.
    `IxIR1.HPTCasePrune` adds the first semantics-preserving consumer: a finite
    heap-only row filters impossible constructor indices from an immediate
    direct-call result case. `run` handles one supplied root;
    `runRecursive` descends through every continuation and alternative body in
    a supplied `Code` and sums removals. Both local-post-fixpoint theorems prove
    exact `runCode` equality for all outcomes. `rewriteCurrent` applies the
    traversal to the dynamic self frame without changing arity/result world;
    a strong-fuel proof covers `callSelf`, yields exact `runMain` equality, and
    is exposed through checked, directly produced, and cached artifact-main
    APIs. `IxIR1.HPTCasePruneProgram` now rewrites every stored function body
    and the main. A common evaluator-fuel proof covers direct invocation,
    dynamic self calls, PAP application, and recursive drops in the logical
    old-keyed graph. `ReaddressAll.rebuild` then uses a domain-separated
    temporary producer namespace and the ordinary SCC pass to regenerate
    content addresses; ordinary and exact-source audits fail closed before
    `runMain_exact_of_rebuild_eq_ok` transports the complete result under its
    total address action. Pipeline checked/produced/cached program APIs install
    that graph and compose the artifact's original target map, while marking
    the input analysis stale. The compiled graph fixture removes a stored
    branch, changes the caller address and main edge, passes both audits,
    preserves its detailed store/result, and checks map composition. Those
    theorem cones are axiom-fenced. File persistence now streams canonical
    records through ingress, sibling staging, and record-wise verification;
    the ledgered native boundary then synchronizes the staged file and the two
    directory sides of atomic rename. Compiled regressions cover exact
    pure-codec parity, exact size admission, malformed-stream rejection, sync
    type discipline, cleanup, complete replacement, and ignored interrupted-
    write orphans while the prior destination remains readable. Power-loss-
    durable publication is landed on the ledgered filesystem baseline. The
    metadata-only directory adapter indexes canonical singleton headers,
    lazily reads the dependency-selected records, isolates stale corruption,
    and durably repairs selected chunks under exact entry/framed/read budgets;
    controlled power-cut testing, streaming/sharded directory maintenance,
    garbage collection, and cross-store scheduling remain broader work
    (`docs/hpt-certificates.md`).

The queue may be reordered on a discovered dependency or a recorded
cost/risk reprioritization; update this file in the same change that
changes the order or completion claim.
