# Handoff: Lean v4.33.0 bump — remaining integration work

> **Consolidated** (`jcb/module-fix-on-v4.33`): this branch is now merged
> with post-#571 main (the upstream-from-TruthMines mega-PR #569 and the
> Prop-mutual `.below` fix #571), and carries the module-mode
> full-content compile fix on top: `getFileEnv` always imports at the
> classic/private level (an `OLeanLevel.exported` import axiomizes
> imported theorems and drops `_private.*` — the cause of main's
> `tc-pins`/`tc-accel-diff` reds), with the `module` header honored as
> seed scoping via `Ix.EnvScope.defaultConstList` instead. The catalog
> smoke test gained a `Plausible` entry (new LSpec dep at these pins).
> Post-merge: `lake test` 2,661 assertions green, `cargo test
> --workspace --release` 1,254 passed. The §2.3 ixvm OOM and the Blake3
> unmerged-branch pin (§2, item 1) carry over unchanged — the latter
> still blocks merging.

Status of this branch (`update/lean-v4.33.0`): ix is adapted to Lean v4.33.0
and the `lean4lean` pin now tracks the fork's v4.33 dev tip (§1). `lake
build` is green across every target, `cargo check --workspace` is clean,
the Rust kernel's 674 tests pass, and `IxTcVerify` builds all 438 modules
with both trust audits (`Audit.Completed`, `Audit.Statements`) passing.
`lake test` is green (2640 assertions) and `lake test -- cli` passes.

Two gates are not satisfied. `lake lint -- --wfail` passes, but that gate
excludes `IxTcVerify`; building that library under `--wfail` still logs
331 warnings, now entirely ix's own (§2.4). And `lake test -- --ignored
ixvm` OOMs inside the Aiur toplevel build (§2.3).

This file records everything still open from the v4.29 → v4.33 release-notes
audit: the lean4lean integration steps, kernel-semantics divergences between
ix's checkers and the upstream Lean kernel (open and cleared), and
non-blocking follow-ups. Ingest fully before starting integration.

## 1. lean4lean: the bump — DONE

`lakefile.lean` pins `4844eda4`, the fork's `dev` tip after PR #5. That
revision clears every non-`sorry` warning the v4.33 linters logged (785 of
them) and annotates the 16 frontier `sorry`s with `set_option warn.sorry
false`, so the whole library is `--wfail` clean and its CI now gates on it
(`build-args: --wfail`). The certified inductive-environment and projection
development came in PR #4 (`3d1390ae`), which this builds on. Its
`lean-toolchain` is stable `leanprover/lean4:v4.33.0` and it requires
batteries at the same rev ix already pins, so no other dependency moved.
`Benchmarks/Compile/lake-manifest.json` inherits the pin through the `ix`
path require and was synced to match.

The previous pin (`5e5bb767`) reproduced the kernel soundness bug fixed
upstream in Lean v4.32.1 (leanprover/lean4#14498): its `addOpaque` never
called `checkNoMVarNoFVar` on the opaque's *value*, so it accepted the
axiom-free `False` construction from leanprover/lean4#14484 — reachable
from ix via `Benchmarks/Lean4Lean.lean:209` (`.opaqueInfo → addDeclAt`).

Hardening confirmed present at the new pin:

- `checkNoMVarNoFVar` on an opaque's value (#14498);
- `checkNoMVarNoFVar` on inductive *and* constructor types, before nested
  elimination (#14577/#14607);
- rejection of the reserved `_nested` name prefix (#14616);
- mutual-block `levelParams` uniformity (#14608) — note ix deliberately
  does not enforce this; see §3.

Green against the new pin: the `lean4lean` package itself,
`Lean4LeanBench`, `bench-lean4lean`, and `Ix/Tc/Verify/Level.lean` (the
lean4lean-interop spike, and the only ix module the new Theory/Verify
surface actually broke).

## 2. Integration steps — remaining

0. **The `IxTcVerify` v4.33/lean4lean port — DONE.** Nothing downstream of
   lean4lean could compile under the old pin, so all of this only surfaced
   once the dependency built. All 438 modules build; the recurring causes,
   for whoever hits them again:

   *v4.33 elaborator.* A pure `let` in `do` no longer emits
   `pure _ >>= _` — it is a term-level `have`, so `run_pure_bind` /
   `ReaderT.run_pure` / `pure_bind` steps and the matching
   `WF.bind (WF.pure …)` proof layers became no-ops and were dropped. A
   `return` inside `try` now routes through the early-return transformer;
   `RecM.try?` was respelled with `tryCatch`/`pure` to keep the plain
   `EStateM.tryCatch` its proofs reason about. `do` loops carry their
   state as a `Prod`, not an `MProd`. Guard `if`s survive as
   `if false = true then …` and need explicit reduction.

   *v4.33 `simp`.* Many `simpa … using h` no longer bridge a gap the
   elaborator closes anyway; those became `exact`. `simp` also stopped
   unfolding semireducible definitions during matching — `KVLCtx` is now
   an `abbrev` for that reason, and assorted call sites name the
   definition explicitly. The largest single class: `simpa [f] using h`
   where the goal and `h` differ only by delta/iota on a plain `def`
   (`TcM.runRec`, `StepWFAtOn`, `BlockCatalog.Contains`, `KExpr.addr` on a
   literal). `simpa` closes with reducible transparency and now fails;
   `exact` unfolds at default transparency and succeeds. Reach for `exact`
   before growing the simp set. A related trap: `runRec`'s equation lemma
   is eta-expanded (`runRec x s = …`), so naming it in a simp set does
   nothing against an unapplied `runRec y`.

   *Audit manifests.* `Audit/Completed.lean` and `Audit/Statements.lean`
   are exact-match, so a *shrinking* trust boundary fails them too. The
   new pin discharges `Lean4Lean.TrProj`'s `sorryAx` (15 roots), ~56 roots
   no longer reach the `ctxAddrForLbrUncached` native axiom, and the
   `canonicalAuxOrder` native axiom is `ax_9`, not `ax_15` — that index
   counts `native_decide` sites in `Ix/Tc/Inductive.lean` and shifts
   whenever one is added or removed. To re-derive a whole manifest at
   once, make `Audit.check` `logError` instead of `throwError` for one
   build; it otherwise stops at the first mismatch.

   *Core/batteries.* `Nat.imax` → `Lean.Nat.imax` (moved into the `Lean`
   namespace, same definition); `Batteries.RBNode.cmpLT_iff` →
   `RBTree.RBNode.cmpLT_iff`; `Except` has no `DecidableEq`, so
   `Ingress/LiteralBlobs.lean` defines a private one for its
   `native_decide` obligations.

   *lean4lean API.* `VEnv` gained `structEtas`; `VDecl.block` became
   `mutualDef`; `Checked` gained `kTarget`/`kTarget_eq`;
   `fieldsR`/`recArgsR`/`resultIndicesR` gained an `ElimMode` argument;
   `List.Forall₂.length_eq` moved into the `Lean4Lean` namespace; ix's
   local `instL_lamN`/`instN_lamN` are now upstream and were deleted.

1. **Blake3 `blake3_rs_shared` — resolved, on an unmerged branch.**
   `lakefile.lean:190` fetches that target to build
   `ix_native_decide_dynlib`, which gates *every* `IxTcVerify` module. The
   target and the `cdylib` crate-type live only on Blake3.lean's
   `native-decide-dynlib` branch, now rebased onto v4.33 and pinned here
   at `730f910a` (two commits ahead of Blake3 main, zero behind). Do not
   merge this branch until that one merges to Blake3 main; then re-pin to
   main. Nothing to do with lean4lean.

2. **`DefEq/PropositionClassifier.lean` — RESOLVED, but it added an
   assumption; review it.** Fallout from this branch's own `fix(tc):
   classify Prop up to universe normalization`, not from v4.33 or
   lean4lean: the classifier case-split on `u.isZero` while production
   returns `u.isSemanticZero`. It now splits on `isSemanticZero`, whose
   `true` branch must show `toVLevel u ≈ .zero`.

   That routes through `Level.normalizeLevel_eval`, which needs
   `u.size < UInt64.size` — a load-bearing bound (see the note at
   `Ix/Tc/Verify/Level.lean:127`: a 2⁶⁴-succ tower really would wrap and
   mis-normalize), and there is no `support x → x.size < UInt64.size`
   lemma. So `PropositionClassifierContext` gained a `universes` field:

       universes : ∀ {u info}, support (.sort u info) → u.size < UInt64.size

   This mirrors the convention at `DefEq/StructuralCongruence.lean:24` and
   `DefEq/SameHeadSpine.lean:28`, and the `u` it constrains is always
   covered by the run support (direct WHNF hands back `support (.sort u
   info)` alongside the reduced expression). But the structure is only
   ever a hypothesis, never constructed, so this **adds an assumption the
   eventual instantiation has to discharge** rather than proving anything.
   Supporting lemma: `KUniv.toVLevel_equiv_zero_of_isSemanticZero`
   (`Ix/Tc/Verify/Level.lean`), beside the existing negative direction.

3. **The suite — run, with one tier unreachable locally.** `lake test` is
   green (2640 assertions, exit 0) and `lake test -- cli` passes. None of
   the audit watch-points below fired.

   The `ixvm` runner OOMs, and the cause is now localized. It is **not**
   the pin list, **not** any pinned constant, and **not** the shared
   `--ignored` setup. Phase markers through the runner body show every
   step completing — `kernelChecks`, `loadIxonEnv Nat.add_comm`, all six
   claim builders, `claimContains`, `serdeNatAddComm` — and the kill
   landing on the next line:

       match AiurTestEnv.build IxVM.ixVM, AiurTestEnv.build IxVM.ixVMFull

   i.e. `toplevel.compile` + `AiurSystem.build`/`circuitShapes` over both
   IxVM toplevels. Peak RSS 42–44 GB locally; a larger machine reached
   ~79 GB, so it grows rather than needing a fixed budget. Zero assertions
   ever print.

   Ruled out by measurement, so nobody repeats them:
   - Pin-list size: trimming `kernelCheckEntries` to one tiny constant
     (`IxVMInd.Even`) reproduces the same OOM at the same point.
   - Any individual pinned constant, including the
     `Int8.toInt64_ne_minValue._proof_1_2` entry suspected on
     `jcb/lean-v4.33.0-rebase` — it is not in this branch's 72-entry
     table at all, yet this branch OOMs identically.
   - The shared `--ignored` setup (`get_env!` + forcing `ignoredSuites`):
     `lake test -- --ignored shard-map` completes in 722 MB.
   - The `MemSizes` `Lean.RBTree` → `Std.TreeSet` migration below:
     reverting it reproduces the OOM unchanged (42.05 GB).

   Consequences for review:

   - `Tests/Ix/IxVM.lean` pinned
     `String.Slice.Pattern.Model.NoPrefixForwardPatternModel.rec`, which
     v4.33 removed. It is repinned to `NoPrefixPatternModel.rec` — the
     surviving class of the same shape (a `Prop` class over a `∀`-typed
     field, which is what the pin exists to drive: it is the regression
     driver for `is_rec_field`'s per-peel whnf, added in #510).
   - **Its FFT cost is still the old constant's number and is certainly
     wrong.** Re-pin it, and expect the other core-derived pins to have
     drifted too — the checked constants' bodies changed with the
     toolchain. The failure message prints the actual value.

   Watch-points from the release-notes audit, none of which fired in the
   suites that did run:
   - `Tests/FFI/Refcount.lean` — v4.30's borrow-inference overhaul
     (leanprover/lean4#12830, #13136 RC coalescing) may shift caller-side
     inc/dec counts. Diagnose with `trace.Compiler.inferBorrow` before
     adjusting expectations.
   - `Tests/Ix/Kernel/CheckEnv.lean:191-192` pins private `Std.Time` names
     (`Std.Time.PlainTime.format._sparseCasesOn_1`); `Std.Time` was
     refactored in v4.32 and the fixtures may not resolve.
   - Decompile roundtrip — v4.30 #12987 introduced `foo._f` helper
     constants for structural recursion. `classifyAuxGen`
     (`Ix/CallSiteSurgery.lean`) deliberately routes unknown suffixes to the
     plain-definition path and ix's own v4.33 oleans contain no `._f`, but
     dependency environments may carry them; the roundtrip suite confirms.
   - `Ix/Tc/Primitive.lean:221-222` hard-codes canonical addresses for
     `PUnit._sizeOf_1` and `SizeOf.sizeOf`; v4.31 #13320 un-exposed
     auto-generated `sizeOf` definitions, which can invalidate those hashes.
   - Expect broad content-address churn vs v4.29-era artifacts and
     re-baseline rather than debug: derived Prop instances flipped
     `def`→`theorem` (v4.31 #13304), imported `partial` defs regain their
     marking across module boundaries (v4.33 #14609), `Float`/`Float32`
     were redefined around `Float.Model`, derived `BEq`/`Inhabited` bodies
     changed, and several core decls changed exposure/reducibility. All
     `.ixe` fixtures and pinned address tables from v4.29 will differ.

4. **The lint gate — passing; `IxTcVerify` still excluded.**
   `lake lint -- --wfail` reports nothing in ix. None of the v4.31
   linters the audit worried about (`redundantVisibility`,
   `redundantExpose`, `simp.varHead`) fired. What did:

   - `Lean.RBTree` is deprecated in favour of `Std.TreeSet`. The only
     Lean-side use was `Bytecode.MemSizes` (`Ix/Aiur/Compiler/Layout.lean`),
     migrated; the API is identical except `fold` → `foldl`. The remaining
     `RBTree` hits in the tree are unrelated: `Batteries.Recycling.RBTree`
     (`Ix/Tc/Level.lean`, `Ix/IxonUniv.lean` — a different, non-deprecated
     type that `IxTcVerify` reasons about) and `Ix/IxVM/RBTreeMap.lean`
     (a red-black tree written in the *guest* DSL).
   - `linter.unusedVariables` on a dead `rtc ←` rebind in
     `Ix/AuxGen/BRecOn.lean`, and `linter.defProp` on
     `Tests/Ix/Compile/LevelSpellings.lean`'s `wfTwoEqDef`. The latter is
     suppressed with a scoped `set_option`: the fixture deliberately pins
     the prop-valued-`def` constant class metaprograms emit, so `defProp`
     is silenced rather than obeyed.

   `lake lint -- --wfail` now passes: the six `Lean4Lean/Inductive/Add.lean`
   warnings that blocked it are gone at the new pin (§1), and ix's own
   non-`IxTcVerify` targets are clean.

   `IxTcVerify` is still excluded from the `build-all` lint driver — a
   pre-existing decision from main (`a0537747c`, 2026-07-24, refined by
   `7ff054b56`). Its stated reason, that the dependency's `sorry` warnings
   would fail `--wfail`, no longer holds: lean4lean is warning-free at this
   pin, including the 16 frontier sorries, which upstream annotated with
   `set_option warn.sorry false`. `lake build IxTcVerify --wfail` now logs
   331 warnings and **all of them are ix's own** — 287 `unusedSimpArgs`,
   33 `defProp`, 7 deprecations, 3 assorted — across 93 modules, with zero
   `sorry` warnings from anywhere. `Ix.Tc.Verify.Audit.SorryFrontier`
   independently confirms no ix declaration uses `sorryAx`.

   So the exclusion is now purely about ix's own lint debt, and clearing
   those 331 would let `IxTcVerify` join the gate. Most are the same v4.33
   simp change as the port (§2.0): simp sets that no longer need
   `pure_bind`/`ReaderT.run_pure`. The linter names the exact argument to
   drop in each case. Update the `lean_lib IxTcVerify` comment when this
   changes — as written it blames the dependency.

5. **Limits, only if they fire.** v4.31 #13030 made heartbeats accumulate
   faster (upstream raised limits 20–50% in places); v4.33 #13956 bounded
   kernel recursion by `maxRecDepth` instead of the physical stack. If
   `IxTcVerify` or deep replays hit deterministic timeouts or
   `(kernel) deep recursion`, raise the seven
   `set_option maxHeartbeats 800000` sites under `Ix/Tc/Verify/` and add
   `maxRecDepth` options before chasing phantom regressions.

## 3. Kernel-semantics divergences vs upstream v4.33 — OPEN

These are places where ix's checkers (Ix/Tc reference kernel, Rust
`crates/kernel`, IxVM model) knowingly differ from the upstream C++ kernel
after this branch. Each needs a decision or work; none is a known
unsoundness.

- **Theorem delta-unfolding (v4.30 #12973).** Upstream made theorem bodies
  kernel-opaque "in almost all ways"; ix still unfolds `.thm` like `.defn`
  (`Ix/Tc/Whnf.lean:404,421`; IxVM `Ix/IxVM/Kernel/DefEq.lean:1002`,
  `Whnf.lean:486,775`). Sound (theorem bodies are well-typed) but strictly
  more permissive: ix can certify proofs Lean's kernel rejects. Do NOT gate
  blindly — the kernel still unfolds theorems in iota-major position (see
  the comment near `Ix/IxVM/Kernel/Whnf.lean:755` citing
  `Rat.instEncodable._proof_1`), so a blanket gate rejects real mathlib.
  The updated lean4lean is the executable spec for exactly where theorem
  unfolding is allowed: replay a corpus (ix's env, then the
  `Benchmarks/Compile` mathlib/FLT environments) through both checkers,
  diff acceptance, then port lean4lean's exact rule into `Ix/Tc/Whnf.lean`,
  the Rust kernel, and IxVM together, with a regression fixture.

- **IxVM still uses the syntactic universe-zero test.** The Lean and Rust
  kernels were fixed on this branch to classify Prop up to normalization
  (`KUniv.isSemanticZero` / `is_semantic_zero`; see commit `fix(tc):
  classify Prop up to universe normalization`, mirroring
  leanprover/lean4#14613/#14615 — `Sort (imax 1 0)` is `Prop`). The IxVM
  model retains the literal-`Zero` test (`Ix/IxVM/Kernel/DefEq.lean:647-669`
  documents the old three-kernel lockstep, now stale). Until ported, IxVM
  diverges from the other two ix kernels AND from upstream: proof
  irrelevance, struct-eta's Prop guard, and Prop-elimination classification
  can disagree on normalizable-zero universes. Port `isSemanticZero` into
  the IxVM model and its fixtures as a dedicated change, and update the
  lockstep comment.

- **Mutual-block universe uniformity (v4.33 #14608) — deliberately not
  enforced.** Upstream's kernel now requires identical `levelParams` across
  a mutual block (only reachable via metaprogramming, only
  `partial`/`unsafe`). ix checks members compositionally (cross-references
  arity-checked at infer; per-member `lvls` in the `muts` form) and its own
  block clustering may legitimately group members Lean never required to be
  uniform — enforcing uniformity could reject valid content. Consequence:
  ix accepts (metaprogrammed, unsafe) blocks upstream rejects. The pinned
  lean4lean now enforces it in `addMutual`, so a parity replay will report
  this divergence by construction — treat that as expected, not as a
  finding, unless a *non*-metaprogrammed case shows up. Otherwise this
  stands as a documented, justified divergence.

- **Regression-fixture ports.** ix has no fixtures for the v4.32/v4.33
  soundness-bug shapes. Port upstream's repros as Ix/Tc test fixtures:
  `issue14484.lean` (opaque fvar; ix ingress rejects fvars/mvars at
  `Ix/CompileM.lean:777` — the fixture pins that), `issue_14576_min.lean`
  (nested phantom params; see cleared item below), and a
  `Sort (imax 1 0)` Prop-classification case exercising `isSemanticZero`
  end-to-end (the Rust unit tests cover `univ_eq`; an integration-level
  fixture does not exist yet).

## 4. Kernel-semantics divergences — CONSIDERED AND CLEARED

Verified during this branch's audit; recorded so they are not re-derived.

- **Nested-inductive phantom params (#14577/#14607): not vulnerable.**
  Upstream's bug was checking ctor types only *after* nested elimination
  (dropped `Ds` escaped checking). ix fully infers the declared ctor type
  in its original nested form (`Ix/Tc/Check.lean:441`) before the
  positivity walk (`Ix/Tc/Inductive.lean:585-624`), so the params are
  checked as ordinary subterms; ix's aux expansion is ephemeral and
  compile-side. The exploit's `Expr`-hash/approxDepth collision vector does
  not map to Blake3 content addressing.

- **Universe-arity at delta (v4.30 #12817): already defended.** Both
  kernels check const arity at infer (`Ix/Tc/Infer.lean:63`,
  `crates/kernel/src/infer.rs:99`) and error — never default — on
  out-of-range substitution (`substUniv`, `tc.rs` `subst_univ`). The
  egress-side `getD mkAnon` (`Ix/Tc/EgressLean.lean:63`) is display
  metadata; Lean re-checks anything re-added.

- **`_nested` reserved prefix (v4.33 #14616): no collision.** ix's
  `._nested.` auxiliaries (`Ix/AuxGen/Nested.lean`) are ephemeral — never
  persisted, never re-added to a Lean environment; the commit path
  (`Ix/Commit.lean`) adds commitment-address names. Names are erased
  metadata in anon-mode checking, so no checker-side rejection is needed.

- **`isNeverZero` (`Ix/Tc/Inductive.lean:301`): sound as-is.** Its
  true-cases are genuinely never-zero under any assignment; false just
  falls through to the conservative single-ctor analysis, matching the
  large-eliminator semantics.

- **FFI/ABI across v4.29 → v4.33: no layout regression.** All 17 hardcoded
  constructor layouts in `crates/ffi/src/lean.rs` were audited against
  v4.33 declarations — byte-correct for both the `Ix.*` mirror types and
  the real Lean kernel objects `lean_env.rs` decodes. The one real bug
  found (pre-existing): `Lean.Int` decoded as a ctor when it is a
  `Nat`-representation builtin — fixed on this branch (`fix(ffi): decode
  Lean.Int by value`). `lean-ffi` needs no changes (bindings regenerate per
  build; none of the removed/changed `lean.h` symbols are used).

## 5. Non-blocking follow-ups

- **FFI pointer-liveness hardening.** `crates/ffi/src/lean_env.rs:594,615`
  key caches by raw `lean_object*` across a decode session; soundness rests
  on callers keeping arguments alive, and v4.30's RC/borrow changes shift
  free/reuse timing. v4.30 added `Runtime.hold` (#13270) for exactly this —
  wrap the Lean-side callers of the env-decoding externs, or take explicit
  refs in Rust. Related audit caveats: the `LeanIx*` layout types' `alloc`
  path must never be pointed at real Lean types (the phantom trailing
  `hash` object slot coincidentally overlays Lean's computed-field scalar,
  which is safe to read one-below but wrong to allocate), and the
  `assert!(i < num_obj)` bound cannot catch an off-by-one into that slot.

- **Benchmark re-baselining.** Pre-v4.30 numbers are not comparable: the
  LCNF backend rewrite landed end-to-end (~15% smaller binaries), LLVM
  19 → 22, DiscrTree fixes (~10% faster `import Mathlib`), `ByteArray`
  equality is now `memcmp`, default 1GB stacks on all threads. Re-baseline
  `bench.json` / CI benchmarks; do not chase cross-version deltas.

- **Thread-pool interaction.** v4.32 #13123 reclaims idle pool workers
  after 5s; reclaimed-and-respawned workers pick up the stack size current
  at spawn. ix sets it via `rs_lean_set_thread_stack_size`
  (`Ix/Tc/ParCheck.lean:57`) — verify it still runs before the parallel
  check phase, and expect lower RSS with possible thread-churn in bursty
  phases.

- **OpenSSL now linked into the Lean runtime** (v4.32 #12030/#13988): a
  plausible duplicate-symbol/version-skew source on the `net`-featured
  `ix` exe, where iroh brings its own TLS stack. No breakage observed;
  watch link errors on that target.

- **`lake setup-file` JSON parsing.** `Ix/Common.lean:266-274` string-splits
  the JSON and v4.33 #14300 enlarged `setup.json`; the code's own TODO asks
  for a real JSON parse.

- **`Benchmarks/CompileFC`** is deliberately frozen at Lean v4.27.0 on
  upstream `lenianiva/lean4-nix` (its overlay API still works there). Do
  not bump it as part of toolchain updates.
