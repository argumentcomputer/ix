# Compilatr.ix roadmap

Live status ledger, last updated 2026-08-22. This is the single source of
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
| Push/PR CI | done (authored) | `.github/workflows/ci.yml`, actionlint over the whole workflows directory; x86_64-linux only. **Never executed: no git remote is configured**, so "runs on push/PR" has never happened — becomes done on the first green remote run |
| Repository witness | active | **Committed 2026-08-22** as one witness commit over the whole tree, on a green check surface (`nix flake check`: library, tests, CI-workflow lint, extern ledger; plus `lake exe tests` → `tests-ok`), ending the five-month window in which no committed revision existed. `plans/` tracking was **decided against** (JCB, 08-22): it stays gitignored and single-copy, so every decision record and the three audit artifacts remain one machine away from loss — an accepted risk, recorded rather than silently carried. Still open: **no remote is configured**, so push and the first CI run have still never happened. Add the remote, push, let CI run once, then adopt a committed-green-bookmark cadence so frontier work never again coincides with "no green revision exists anywhere" |
| Trusted-extern ledger | done | `docs/trusted-extern-ledger.md`; fail-closed drift validator, hardened 2026-08-19: non-40-hex `uses:` refs rejected, extern audit covers the whole trusted package tree (12 Blake3 symbols, per-module reachability cross-checked against real imports) and `opaque`/`def`/`attribute` forms, `auditSrc` feeds the workflows *directory* plus `.envrc` (now integrity-tracked), missing inventory roots hard-fail; 16-mutation self-test transcript in the 08-19 session record |
| Actual dual-license grants | done | `LICENSE-APACHE`, `LICENSE-MIT` |
| One tracked live roadmap | done | this document |
| Sorry/axiom fence | done (fragment) | `Compilatrix/Fence.lean` (2026-08-19; extended 2026-08-22): `#guard_msgs`-pinned `#print axioms` for nine flagship theorems and the two `Address` codec laws — the 08-22 additions are the two whole-pass boundaries `SimInstance.addIxIR1CompilerContracts` and `addIxIR1SemanticForwardSimulation` (so M2b's "kernel-checked, no `native_decide`" claim for the compiled `add 2̂ 3̂` output is mechanical rather than editorial) plus the premise-free `LowerSim.lowerE_proj_var_run_value_sound` — all within {`propext`, `Classical.choice`, `Quot.sound`} — plus a declaration-level `sorry`/`axiom`/`native_decide` source scan in `check_trusted_externs.py`. Frontier: the other eight codec laws are unpinnable (bv_decide row, M1) |
| Ledger-validator Lean-root blind spot | done | root inventory now derived from `lakefile.toml` (`[[lean_lib]]`/`[[lean_exe]]`); empty inventory and missing roots are hard failures (2026-08-19) |
| ix parity baseline single-sourcing | queued | the parity revision is pinned in four places (`Sharing/Compress.lean` `ixParityRevision`, `check_ix_sharing_baseline.sh`, `sharing-policy.md` prose, `Tests.lean` — the last is mechanically synced to the constant; script and prose are not); make the script consume the Lean constant, and document why `scripts/ix-sharing-baseline/` deliberately pins v4.31.0 against the repo's v4.33.0. **New (08-19): the pin is stale against ix `origin/main`** — `29bdf707` (serialize.rs) and `5996ae27` (+446 `Ix/Ixon.lean`, new 772-line `canon_univ.rs`) touch pinned paths; the sharing-policy change protocol requires a re-pin-or-waiver decision |

### M1 — Ixon v2 identity and source semantics

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| v2 wire format: mode-bearing syntax, strict canonical codec, `ixon-v2` namespace, succ-RLE bound | done | `docs/ixon-v2-wire.md`; total writers, input-fueled decoders, rejection guards, 110-byte golden fixture (its layer-2 address now pinned through the real FFI path, `Tests.lean`) |
| Canonical sharing ladder S1–S5 | done | layer 1, total inliner, evaluator coherence, deterministic compressor, address identity — `docs/canonical-sharing.md` proof ladder; policy frozen as `compilatrix/ixon-v2-sharing/1` (`docs/sharing-policy.md`) |
| Codec roundtrip/canonicality laws | done | global accepted-byte canonicality for all five codecs; global roundtrip for `Address`/`Univ`; exact `wireWF` domains for `Expr`/`ConstantInfo`; `wireWF ∧ sharingWF` for `Constant` |
| bv_decide compiler trust in codec laws | queued | discovered by the fence (2026-08-19): the `Univ`/`Expr`/`ConstantInfo`/`Constant` laws rest on `bv_decide` lemmas in `Serialize.lean`/`Const.lean`, each recording a `Std.Tactic.BVDecide.Reflect.verifyBVExpr` native-reflection axiom — compiler trust outside the axiom triple, with content-derived names too unstable to pin. Either evict `bv_decide` from those ~8 byte-level lemmas (kernel-checked `decide` at the 8-bit widths) or record the trust explicitly in the extern ledger; until then the eight laws stay outside the fence |
| Encode-time `wireWF` | queued | the proved roundtrip domain is a caller obligation with no enforcement: `putConstant` silently truncates ≥2⁶⁴ counts (`Nat→UInt64`), so the writer is not a checked injection. Add a checked-writer API or an encode-time `wireWF` guard |
| Canonical inlined/address identity | done | `Constant.inlinedView_eq_iff_address?_eq` on `Addressable` under an explicit pairwise BLAKE3 no-collision premise; bare expressions expose only a context-local cache hash |
| Decode-time local index bounds | queued | ref/str/nat vs. refs table; sort and universe-arg indices vs. univs table; `Univ.var` vs. `lvls` (**silent misevaluation**: out-of-range reads as 0 and can collapse an `imax`, changing a `sort` feeding real computation); self-`recur` vs. own block; `prj` type-ref (checked nowhere); **recursor-count coherence** (params/motives/minors/indices decode as independent u64s, never cross-checked against rule `fields` — `fire`'s take/drop can mis-slice, a semantic-corruption vector). Note these bounds are a precondition of *meaningful addressing*: semantically garbage constants mint real addresses today (`address?` is independent of index sanity) |
| Decoder depth guard | queued | decode fuel bounds allocation but not recursion depth: deeply nested input is a stack crash, and **flat counted arrays crash too** (non-tail `getListN`/`getTag0List`; executed threshold ~1–3M elements). Natural fix: one shared counted-sequence codec used by `Expr` and `Const` (also removes ~500 lines of per-struct proof plumbing) |
| Structured decoder errors | queued | decoder errors are interpolated strings; align with the existing `Eval.Err`/`UsageErr` taxonomies |
| Cross-constant member bounds | queued | projection member/ctor indices into block addresses need the store; belongs with store ingestion at the M2.5 corpus boundary, not byte decoding |
| Source quotient ι | queued | `Quot.lift/ind` applied to `Quot.mk` stays neutral today (now pinned by an evaluator guard, 08-19); a bounded addition — one `Head` tag, one config field, one `fire` arm, mirroring the natLit peel — that unblocks M2a quotient simulation |
| Evaluator neutral refinements | queued | neutral-major recursor/projection currently hard-`stuck` instead of neutral; `NeutralId.member` lacks block qualification; String.rec literal peeling; `prj` type-ref cross-check. K-like reduction deliberately out of scope (defeq); externs deliberately absent until IxIR₀ |
| UsageCheck metatheory | queued | `UsageCheck.lean` has zero theorems — the eraser gate is untheoremed. **Freeze contract decided by restriction (2026-08-20):** the checker now rejects unique values at non-unique argument, let, and result sinks, matching the lowering's no-coercion worlds (`plans/freeze-contract-2026-08-19.md`, Option A); the three witness guards and stable diagnostic are pinned. Adoption falsified the proposal's zero-compatibility-cost estimate: IxIR₁ constructors are demand-polymorphic while Ixon constructor result ownership is fixed, so the composed fixture had compiled through an implicit freeze; it is now a two-constructor unique/shared witness with an explicit projection path, and the decision record carries the correction. The computed-erased non-interference slice is now unblocked and targets this aligned checker; typed unknown-callee ownership stays M3-blocked |
| Sharing-policy tuning decision | queued | Upgrades 1–2 (residual-statistics greedy, reference-ordered indices) were never implemented and the pre-freeze window has closed; either record a formal drop in `sharing-policy.md` or schedule one policy roll before the ix merge |
| Ixon layer hygiene | done (fragment) | landed 2026-08-19: dead `getBool01`/writer-spec views/`collectAll` (it lived in `Expr.lean`)/non-`?` `Address.ofBytes` deleted; `maxSuccExpansion` doc name fixed; the 16 `≤ UInt64.size` compressor bounds aligned to strict `<`; quot-kind/mut-tag negative decode fixtures; evaluator `dPrj` + quotient-neutrality guards; `selfMutsOf` ×3→×2 (`Erase` now delegates to `Eval`'s; the `UsageCheck` copy stays deliberately — the gate does not import the evaluator; real home is `Const.lean` at the next layer touch). Corrections: `Address.get` is live (`memberAddr` uses it) and was wrongly listed. Remaining: the `selfMutsOf` move, `Uses.mul`'s fate |

### M2a — checked erasure to IxIR₀

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| IxIR₀ syntax and fueled semantics | done | evaluator + fuel monotonicity theorem |
| UsageCheck-gated executable eraser | done | checked pipeline rejects usage failure |
| Erasure simulation | done (fragment) | sorry-free over: kept vars, λ/let, literals with resolvable blobs, projections, refs, complete visible constructor-parameter prefixes, parameterized index-free recursor ι, and fully supplied visible indexed recursor spines; fenced by `Compilatrix/Fence.lean`. **`ValRel` constructor cases now pin the target address** (`CtorAddr` premise, 08-19): a target ctor address must resolve in the source context to a `.cPrj` of exactly that block/inductive/ctor, so one address can no longer relate two families; the `addE'` differential guard is address-sensitive per cell |
| Ghost arguments at definition heads | queued | every ordinary polymorphic application (`.app (.ref defn) ◻`) is outside `PErase`, the validator, and the instance suite — the single largest coverage extension for real programs (measured family cost: ~800–1,300 proof + 150–300 validator + 150–250 instance lines). Next M2a slice after the current LowerSim tranche |
| Executable-output certificate bridge | done (fragment) | the validator reconstructs every `PErase` clause of the proved fragment, indexed spines included (`certifyExprWithRec`/`validateRecSpine`); a negative guard rejects the early-firing indexed pap. Standing acceptance criterion: the certified fragment must never silently lag the theorem fragment — **note this has no mechanical enforcement** (soundness is type-forced; completeness is discipline): maintain a fixture-per-`PErase`-constructor rule at review, or add an enumeration guard |
| Sharing support | done (fragment) | `erasure_sim_inlineSharing` composes evaluator coherence with share-free `PErase`; sharing-aware certificates validate original shared inputs against their inlined relation. `SharingWF` side conditions are still hand-discharged per fixture — the decoder-layer-1 bridge remains (missing: a `Frame.ofConst` WF lemma, entry-`sharesBelow` derivation, nonempty-env `ValuesSharingWF` helpers, and the store-ingest resolver invariant) |
| Constructor/recursor argument-policy cursor | done (fragment) | ctor params, recursor params, and complete source-only index segments at theorem + certificate + instance level (`Sim/Segment.lean` cursors; `Pair.mk`, List-shaped, and one-index instances; `RecEraseSpine` keeps indexed intermediate paps out of the global value relation; the rec-major guard plus `RecMember.BlockParams` protect layout compatibility). Frontier: the split/under-applied row below |
| Split/under-applied drop spines; indexed recursive self calls | queued (miscompile closed) | **the wrong-code channel is closed (08-19)**: the eraser now rejects split or under-saturated known-constructor parameter spines at erase time (strict by default in both pipeline entry points; pinned message; positive/negative guards) — the validator's own substrate is the documented opt-out since it independently rejects the identical shapes at the relation level. Remaining: design the protected application/value relation to *admit* these spines (or record permanent exclusion); indexed `recSelf` and first-class indexed member refs are still rejected explicitly — a recursive indexed-family (Fin/Vec-shaped) fixture activates with the lift |
| Mutual-block member coverage | queued | non-self `recur`/`memberAddr` refs, `dPrj`, and `muts`-member `Covered` cases are outside the relation |
| `memberAddr` retirement | queued | synthetic XOR member addresses have no collision fence and no owner (`memberAddr block (2⁶⁴−1) = block` exactly — the wraparound is unguarded); retire into real IR content addressing (M2b row) |
| Dropped-variable occurrences | queued | blocked on UsageCheck semantic non-interference (M1 metatheory row) |
| Extern/opaque correspondence | queued | per-address `OracleRel` backed by ledger entries; must replace the current silent `ValRel.neu → ◻` weakening — invasively (`.neu` is load-bearing in every neutral-absorption path). At corpus scale the neutral hole becomes the dominant coverage gap (proof terms flow as kept neutrals; extern-backed arithmetic and quotient computation land in ◻ or outside the fragment) |
| Certificate `Owned` fidelity | queued | `Covered.defn` binds the erased declaration's result ownership free and `validateCovered` wildcards it — the certificate third of the mode/ownership chain M2b's lowering consumes. Add the owned-equality premise and have the validator discharge it from its exact output |
| Quotient compilation | queued | the erased side exists (`Erase.lean` compiles `mk`/`lift`/`ind`); missing is source quotient ι (M1 row), then the simulation |
| Error/divergence preservation | deferred | `erasure_sim` transports source success only; the backward direction of the observational-equivalence claim activates with the M3 theory bridge |
| Eraser adequacy against kernel theory | queued | activates with the ix4lean theory bridge at M3 |

### M2b — explicit-memory IxIR₁

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| IxIR₁ store semantics and dynamic discipline | done | shared/unique nodes, RC, deep free, reuse, paps, counters. Scope note (08-19): the dynamic checker enforces *temporal and world* discipline; unique-aliasing violations are prevented at compile time only (`held` flags), not observed at run time |
| Mode-directed IxIR₀→IxIR₁ lowering | executable done; proof active | differential/leak/counter corpus and checked end-to-end fixture; error agreement is exact (`errAgree`: fuel↔fuel, address-exact unknown refs, pinned oracle/ABI/stuck pairs — 08-19). `LowerStateSim.lean` now closes the complete expression cluster, ordinary no-`recSelf` bodies, lifted bodies, full recursor rules/RHSs, and structural constructor wrappers. `LowerSim.lean` traces each `lowerDecl` through `lowerAllAction`, recovers generated-state suffixes, and jointly seals source declarations, generated declarations, and higher-order application with `compilerContracts_of_source_extra_below_step`. `Sim.applyOwnershipPreservesAt_of_sharedDeclsBelow` covers pap under-fill, saturation, over-application, and scalar externs. The exact `add 2̂ 3̂` whole-pass output instantiates the ownership boundary as `SimInstance.addIxIR1CompilerContracts` and the semantic boundary as `SimInstance.addIxIR1SemanticForwardSimulation`; the latter is a kernel-checked segmented trace of the actual compiler output and returns a `ValueGraph` realization of `5̂`. Remaining proof work is the generic semantic induction plus progress, reclamation, and cost refinement |
| Lowering restrictions ledger | queued | no freeze op — aligned by restriction 2026-08-20: `UsageCheck` rejects unique values at non-unique sinks; the planned lift is deep `Op.freeze`, with wake conditions in `plans/freeze-contract-2026-08-19.md`; the let seam's lift is mode carry, not freeze. Also: no unique destructuring, all-`many`-only paps/function values, unique captures rejected, mode-monomorphic recursors, saturated-only `recSelf`. **These compose into a wall (08-19 analysis): unique data can be allocated, moved, returned, and deep-freed — and never inspected**, so the substructural value deliverable today is zero-RC alloc/move/free of never-inspected trees. Each remaining restriction needs a lift-restriction slice or a permanent-decision record |
| Formal memory-ownership simulation (RC/root conservation) | active | *renamed from "formal memory simulation" — the completed induction is ownership-only and success-conditional.* Heap/value/root foundations now cover every primitive memory operation; direct/self calls, recursor bodies, lifted functions, constructor wrappers, and pap application all have exact fuel-indexed contracts. `compilerContracts_of_source_extra_below_step` closes their mutual cycle, and `SimInstance.addIxIR1CompilerContracts` constructs both `CompilerContracts` and `ExtraFnContracts` from the actual nontrivial `lowerAllAction` result (five source-backed functions plus one lift); its `CompilerContracts.apply` is the first concrete `ApplyOwnershipContract`. This completes the ownership-contract exit criterion. `SimInstance.addIxIR1SemanticForwardSimulation` now discharges the semantic proposition for the nontrivial compiled fixture. The first duplication cut is also landed: `EmitSound.of_below`, `LowerResultSound.of_below`, and `LowerArgsSound.of_below` close uniformly bounded proofs, and base/primitive/call/apply emitter pairs now share one bounded body without changing their public signatures. The row remains active because the remaining duplicated recursive families, the generic semantic theorem, and the separate `MemoryErrorUnreachable`, `Reclamation`, and `CostRefinement` propositions are unproved |
| Value correspondence (IxIR₀ ↔ IxIR₁) | active | Architecture chosen: keep `LowerResultSound` as the ownership/frame layer and build a companion semantic refinement, so source values do not infect every existing ownership lemma. `SimInstance.addIxIR1SemanticForwardSimulation` is the first non-degenerate consumer of `ValueGraph`: every successful source run is joined by fuel monotonicity to the exact `5̂` run, while a segmented kernel trace executes the exact compiled main and constructs its six-constructor target graph. The generic environment layer now includes `EntriesValueGraph`/`VEnvValueGraph`, semantic caller frames (`RootsGraph` is retained across later arguments), `LowerResultValueSound`, and `LowerArgsValueSound` with a checked cons rule. Literal, erased, final/repeated variable, arbitrary-count capture move/retain, and complete selected-capture traversal rules are checked. Lifted paps now have a concrete function relation: `LambdaPrefix` describes residual source closures, `ValuesAt` pins the compiler-selected environment values, and `CompilerLiftCodeRel` ties the fresh address to the exact canonical `lowerFnBody` run plus its accumulated declaration; provenance is monotone under later `ExtraExtends`. `LowerArgsValueSound.papp_graph`, `lowerLam_run_value_sound`, and `lowerE_lam_run_value_sound` connect fresh allocation to an actual heap `ValueGraph`; `LowerArgsValueSound.alloc_graph` does the same for constructors. Destructive graph transport is now factored through `StoreGraphRestricts`: shared/unique deep drops expose reverse shape inclusion, surviving `ValueGraph`/`ValuesGraph`/`RootsGraph` witnesses are rebuilt from post-state ownership, and both `ReleasePlan.valueSound` and `releaseAll_value_sound` preserve semantic environments and caller frames. The generic let seam is also checked: alias/materialized binder installation adds the bound source value, released-first-entry pop removes it, and `LowerResultValueSound.installThen` composes the body. **The projection borrow pipeline is instantiated (2026-08-22):** `SourceProject` names the source evaluator's two `.proj` outcomes and `SourceProject.of_eval` derives it from `IxIR0.eval` rather than from a hand reading of it; `lowerE_proj_run_value_sound` dispatches all four borrow descriptors against both source shapes, including the two pairings the descriptor-driven branch choice does not exclude — a constructor target reaching the erased descriptor (unsatisfiable midpoint) and an erased target reaching a slot (`fetchErasedSlot_false`). The second recorded an asymmetry worth keeping: `ValueGraph` inverts only on the *runtime* side (`ValueGraph.eq_erased_of_erased`), so an erased *source* value may still be realized by a pap node through the abstract `FunctionRel`, and the vacuity argument has to cover that node shape rather than assume `RVal.erased`. `lowerBorrow_dynamic_run_value_sound` closes the borrow dispatch through the two `asBorrow` adapters; `lowerE_proj_var_run_value_sound` is premise-free for variable targets, with two fixtures that exhibit the actual `lowerE` run (final-use release and repeated-use keep) and discharge the source premises at a two-field constructor selecting the second field. **Non-application head coverage is complete (2026-08-22):** `lowerE_lit_run_value_sound`, `lowerE_erased_run_value_sound`, `lowerE_var_run_value_sound` (final-use move and repeated-use retain, with every other entry state and world mismatch discharged from the successful run) and `lowerE_let_run_value_sound` join the existing `.lam` and the new `.proj` dispatch, so every `lowerE` head except `.app`/`.ref` — both routed through `lowerSpine` — now has a semantic dispatch. The let dispatch takes the bound-value and body correspondences as separate premises over `sourceEnv` and `boundSource :: sourceEnv`, and reuses the alias/materialize/release seam unchanged. Next: the source-result call/application contract needed by reference and higher-order application — the only remaining heads — before closing the remaining compiler/whole-program induction |
| Progress (`Err.mem` unreachability) | queued | only the target proposition exists; every operational ownership theorem conditions on `.ok`. The completed ownership seal guarantees exact RC accounting for successful runs, but use-after-free freedom is still delivered by the dynamic checker rather than a progress theorem |
| Reclamation | queued | underivable from the current invariant: `RootOwnership` has no reachability/positivity clause and admits rootless self-owning cycles, so "closed runs end at `live = 0`" needs a heap-closure/acyclicity invariant decision (strengthen the invariant vs. a separate trace-level theorem family) |
| `reuse_sound` modulo location renaming | done | premise generalized to `List.Perm` (08-19) with the transposition witness the old equality form could not instantiate — a two-field unique `Cons(x,xs)` reused as `Cons(x,acc)` (list-reverse shape), proved end-to-end beside the original identity-partition fixture (which now supplies `.of_eq`); `RootOwnership.perm` is the transport; counter differences remain deliberately outside `HeapIso`. Reuse pairing remains an IxIR₂ pass (M2c) |
| Result ownership in declarations | done | `IxIR0.Decl.defn` and `IxIR1.FnDef` carry `Owned`; erasure preserves the innermost Ixon arrow result (defaulting non-functions to `.shared`), declaration bodies lower at their signature, direct calls check demands, and shared paps/unknown `apply` cannot conceal unique results. `invoke` dynamically checks hand-written declarations, with `invoke_fn_result_hasWorld` connecting success to the simulation predicate. Erasure's forced `.many` on dropped binders/lets is the adjacent mode seam; the certificate side is the M2a `Owned`-fidelity row |
| Extern heap-argument consumption | queued | v1 dynamically enforces scalar-only arguments/results in both directions, so no heap ownership crosses; a production heap-valued ABI still requires an explicit ownership policy |
| Validator-gated pipeline | done | `Pipeline.compileValidated` (08-19): usage gate → strict erase → per-constant `Covered` coverage fixpoint → `certifyProgram`/`certifySharedProgram` in discovered dependency order → exact target cross-check → lower; fails closed with the first rejected address + validator diagnostic. Guards pin agreement with `compile` on the mixed-mode fixture and an exact-message rejection of an out-of-fragment program; `compile` remains, documented as accepting out-of-fragment programs |
| IR content addressing | queued | IxIR₀/IxIR₁ serialization + addresses; retires `synthAddr`/`memberAddr` placeholders; prerequisite for cached fixpoints, HPT certificates, and address-exact double compilation |
| Mutual blocks in the IRs | queued | deferred at both IR levels; pairs with the M2a member-coverage row |
| HPT analysis + certificate checker | queued | first analysis-driven validated pass; design the certificate format first — none exists |
| IxIR₀ˢ specialization | queued | scalar/layout refinements before lower native IRs |

### M2c — native/zk backend wedge

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| ISA decision record | queued | record candidates and criteria (zk-coprocessor alignment, Sail spec availability, regalloc-certificate cost) before building; today "target decision still open" has no in-tree analysis |
| IxIR₂ CFG/join-point IR | queued | activates after the M2b simulation foundation; owns the free+alloc→`reuse` pairing and the brecOn→direct-recursion recovery question (essential for performance, under-formalized anywhere) |
| One ISA semantics + emitter | queued | trusted encoder first, verified assembler later; Sail-derived semantics preferred |
| Regalloc/analysis certificate checker | queued | must refine the shared middle semantics; `EraseValidator` is the established proof-producing-validator template |
| Defunctionalization boundary decision | queued | GRIN-style whole-world analysis inside the addressed closure vs. closure fallback at open boundaries |
| End-to-end FIP benchmark | queued | the interpreter-level FIP guard exists but runs hand-written IR — no compiler path emits `reuse` today (pairing is the IxIR₂ row); missing: one native binary, result and capability checked |
| zk target + cost model | deferred | design the shared-middle cost semantics against Aiur constraint costs; the zk path is active upstream (external coordination) — the remaining confirmation is the joint cost-model conversation |

### M2.5 — measurement and corpus contact

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| Instruction-level alloc/reuse/free/RC counters | done | IxIR₁ `Store` and exact guards |
| Interpreter-level counter benchmarks | queued | unblocked today, and reframed as **thesis evidence**: the substructural bet has zero quantitative support (the differential corpus contains no unique-consuming or linear parameter; the unique world is exercised only via dead params/lets). Same programs, all-shared vs. mode-directed, rcops/allocs/frees deltas, plus mode-adversarial fixtures; the "first computational unique fixture" (unique list reversal through a case) activates with the separate unique-destructuring lift; the adopted freeze restriction fixes its all-unique shape but does not itself enable the case |
| Untrusted-ingestion readiness gate | queued | named precondition of corpus contact: decode-time index bounds + recursor-count coherence (M1 rows), the depth guard, structured errors, a byte fuzzer (no-crash + reencode-equals-input via `CanonicalLaw`), encode-time `wireWF`, `Env.ofList` replacement, a perf budget for the known superlinear sites (quadratic layer-1 check, compressor, monolithic `eraseProgram`, kernel-`decide` certificates), and the certificate-scaling decision (kernel `decide` will not survive corpus scale; interacts with the M4 reflection/TCB row) |
| Native/atomic/zk benchmark dimensions | deferred | native time needs M2c; atomic RC needs a thread model (deferred axes); zk cost needs the M2c cost model |
| Corpus fixture format + loader | queued | specify how a stdlib-scale environment arrives (serialized v2 bytes?); `Env.ofList` linear lookup will not survive stdlib scale inside the differential harness |
| Well-moded program generator | queued | property-based IxIR₀ generation to harden the differential harness before corpus contact; bias it mode-adversarially (unique-consuming/linear parameters) |
| First stdlib-scale fixture | deferred → decouplable | the old trigger (ix Ixon-v2 merge branch) is external, unstarted, and unsocialized. Decoupling path: the certified v1→v2 reencoder's front half is a v1 *reader* — building `reencode_sound` in-repo yields stdlib-scale fixtures without upstream landing anything, and delivers the candidate first certified pass; the ix merge remains the upstreaming path, not the fixture gate |
| Address-equality frontend oracle | deferred | trigger: corpus contact. Compare complete re-encoded environments, not pretty syntax — this is the compat-bar metric for upstream-elaboration parity |
| Ix.Tc parity benchmark | deferred | trigger: native backend. stdlib/mathlib, 1 and N threads; the borrow axis (deferred axes) is the concurrency keystone |

### M3 — kernel theory and self-hosting bridge

| Deliverable | Status | Evidence / next condition |
| --- | --- | --- |
| Vendor pinned lean4lean-derived theory as ix4lean | queued | provenance snapshot + sorry-frontier audit; groundwork exists (root toolchain already co-pinned to lean4lean's; divergence/bug notes in the reference checkout); runbook in `plans/ix4lean.md`. The cheap slice (snapshot + provenance + sorry-frontier audit) is unblocked now and decays in value as upstream moves; full M3 activates after the current M2b tranche closes |
| Reconcile scope with ix's Tc verification | queued | new (08-19): ix is verifying its own Lean-side Ixon checker in-repo (WHNF, inference, DefEq, inductive ingress PRs landed), which overlaps the retarget row below — decide adopt/bridge/ignore before committing to rewrite-scale work |
| Extend theory with Uses/Owned | queued | prove `many`-fragment conservativity, stated against the pinned upstream as the credibility anchor |
| Ixon-native checker retarget | queued | ix4lean's checker replays `Lean.Expr` today; retargeting to Ixon is rewrite-scale work, currently unowned — potentially shrunk by the reconciliation row above |
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
| Reflection/TCB policy | deferred | if ix admits proof-by-evaluation, the backend enters the soundness TCB, outranking frontend verification — record the policy either way. Note the fence's bv_decide finding (M1) is a small live instance of exactly this trust class |

## External coordination

Sequencing this repository does not control; each item names its in-repo
consequence.

| Item | State | In-repo consequence |
| --- | --- | --- |
| ix Ixon-v2 merge branch | not started, **unsocialized** | ix has no v2 branch and zero mentions of this work (surveyed 08-18) — post an RFC (wire doc + policy freeze + intentional deltas + reencoder plan) before more divergence accrues. The PR-shaped deliverable: certified v1→v2 reencoder (`reencode_sound` — candidate first certified pass, and the M2.5 decoupling path), upstreaming the strict-decode findings, the both-versions-vs-cutover transition decision, a joint field-enumeration-order pin, and the store-ingest policy |
| ix parity baseline staleness | action required | `origin/main` moved past the pin on pinned paths (`29bdf707`, `5996ae27` incl. the new 772-line `canon_univ.rs` — universe canonicalization is canonical-form-relevant); the sharing-policy change protocol requires a re-pin-or-waiver decision |
| Toolchain reconciliation | pending merge | this repo pins v4.33.0 (lean4lean's pin); ix sits at v4.31.0; reconcile at the merge/vendoring point. The skew is live today in `scripts/ix-sharing-baseline/` |
| zk path | active upstream | Aiur is core and moving (FFT cost model 2026-08-07; a plan exists to transport the proved Tc acceptance property to the Aiur stack); remaining confirmation is the joint cost-model design conversation before the M2c cost model hardens |
| Upstream lean4lean tracking | passive | pinned as patch source and credibility anchor until the M3 snapshot |
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

1. **Repository witness** (minutes, externally blocked): the tree is
   committed (08-22) on a green check surface and the `plans/` question is
   decided (stays ignored). Remaining: no remote exists — add it, push, let
   CI run once, then adopt the committed-green-bookmark cadence. Everything
   below already has a local durable witness; it has no off-machine one.
2. **Generalize the semantic whole-pass theorem**: the first exit is met —
   `addIxIR1CompilerContracts` seals ownership on the exact SimInstance output,
   and `addIxIR1SemanticForwardSimulation` gives that compiled main a
   source-to-target `ValueGraph` theorem without `native_decide`. The
   architecture is a companion semantic refinement layered over the existing
   `LowerResultSound`, not an expansion of its ownership postcondition. The
   first duplication cut is landed: uniform bounded proofs close through
   `EmitSound.of_below`, with the base/primitive/call/apply pairs sharing one
   proof body. Continue collapsing recursive pairs as they are touched. The
   source-environment relation, semantic argument sequencing, and
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
   dispatch. Next specify the semantic call/application contract needed by
   those two remaining heads, then carry the companion judgment through the
   remaining lowering induction. Exit: the
   theorem applies to arbitrary successful `lowerAllAction` outputs satisfying
   the compiler/environment premises.
3. **M2a coverage: ghost arguments at definition heads** (about a week by
   the measured family cost): theorem + validator + a contentful instance
   + differential guard — the largest real-program coverage win. Bundle
   the `Covered` `Owned`-fidelity premise.
4. **UsageCheck semantic non-interference**: the
   computed-erased slice, unblocking dropped-variable occurrences.
5. **Thesis evidence** (days): interpreter-counter benchmarks (all-shared
   vs. mode-directed on the same programs) + mode-adversarial fixtures;
   the first computational unique fixture activates with the
   unique-destructuring lift.
6. **Reencoder + corpus decoupling** (parallelizable): v1 reader +
   `reencode_sound` skeleton; post the ix RFC; execute the parity
   re-pin-or-waiver decision.
7. **Untrusted-ingestion gate** (days): decode bounds + recursor-count
   coherence + depth guard via the shared counted-sequence codec +
   structured errors + fuzzer + encode-time `wireWF`.

The queue may be reordered on a discovered dependency or a recorded
cost/risk reprioritization; update this file in the same change that
changes the order or completion claim.
