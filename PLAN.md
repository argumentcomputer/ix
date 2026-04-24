# PLAN — `Toplevel.compile_correct` closure

## Audit (2026-04-27)

**Branch**: `ap/aiur-compiler`. Single WIP commit `601a0a0` on top of `2994616`.

**Build**: `lake build` green. 9 declaration-level sorries.

**Files** (selected, by LoC):
- `Ix/Aiur/Proofs/ConcretizeSound.lean` — 9147 LoC, 6 sorries.
- `Ix/Aiur/Proofs/CompilerProgress.lean` — 6098 LoC, 0 sorries.
- `Ix/Aiur/Proofs/DedupSound.lean` — 5435 LoC, 0 sorries.
- `Ix/Aiur/Proofs/CheckSound.lean` — 3879 LoC, 0 sorries.
- `Ix/Aiur/Proofs/LowerCalleesFromLayout.lean` — 3841 LoC, 0 sorries.
- `Ix/Aiur/Proofs/LowerSoundCore.lean` — 2439 LoC, 1 sorry (internal-decomposed: 7 granular sub-sorries).
- `Ix/Aiur/Proofs/LowerShared.lean` — 1666 LoC, 0 sorries.
- `Ix/Aiur/Proofs/CompilerPreservation.lean` — 1104 LoC, 0 sorries.
- `Ix/Aiur/Proofs/StructCompatible.lean` — 664 LoC, 0 sorries.
- `Ix/Aiur/Proofs/ConcretizeProgress.lean` — 901 LoC, 0 sorries.
- `Ix/Aiur/Proofs/ConcreteEvalInversion.lean` — 531 LoC, 0 sorries.
- `Ix/Aiur/Proofs/SimplifySound.lean` — 532 LoC, 0 sorries.
- `Ix/Aiur/Proofs/LowerSoundControl.lean` — 485 LoC, 2 sorries.

**Test gate**: not run this session (RustFFI cost). Last known green: prior session.

## Sorry inventory

| # | Loc | Theorem | Type | Notes |
|---|---|---|---|---|
| S1 | ConcretizeSound:1025 | `runFunction_preserves_FnFree_body` | F=1 monolithic | ~1200 LoC mutual induction over 6 interp-family functions; missing `unflattenValue_FnFree` aux. |
| S2 | ConcretizeSound:2013 | `concretize_preserves_TermRefsDt` | F=1 monolithic | ~300 LoC composition chain. |
| S3 | ConcretizeSound:2266 | `concretize_preserves_runFunction` | F=1 monolithic | ~3500 LoC 40-arm structural induction; the heart theorem. |
| S4 | ConcretizeSound:5527 | `concretize_under_fullymono_dt_flat_size_agree` | F=1 | TASK C from PLAN_3B. ~500-1000 LoC infra needed (per-Typ flat-size correspondence). Session lost ~3000 LoC of decomposition work. |
| S5 | ConcretizeSound:8273 | `spine_transfer` | F=1 | ~500-700 LoC backward-trace + rank-lift. Has its own sig caveat about FullyMono dependency. |
| S6 | ConcretizeSound:9126 | `concretize_extract_function_at_name` | F=1, **defer** | Architectural circular-import blocker. Marked dead-code path. |
| S7 | LowerSoundCore:1459 | `toIndex_preservation_core_extended` | F=1 internal-decomposed | 7 granular sub-sorries (`.tuple`/`.array`/`.proj`/`.get`/`.slice`/`.set`/`.letLoad`/`.load`/`.app` + 1 in `.u8BitDecomposition`). 30/37 arms F=0. Need `ValueHasTyp` typed-Value invariant carrier (~300+ LoC) for 6 access arms; `.app` deferred to S1's mutual induction. |
| S8 | LowerSoundControl:58 | `Function_body_preservation_succ_fuel` | F=1 | Wires S7 + per-arm semantic lemmas + `RefCompat`-extension to `AppCompat`. |
| S9 | LowerSoundControl:229 | `body_compile_ok` | F=1 | Wires S7 (progress side, fully F=0) + block-level dispatch for `.match`/`.ret`/`.matchContinue`/`.return`/`.yield`. |

## Sig defects (found, unresolved)

### SD1 — `WellFormed.fullyMonomorphic` excludes IxVM

**Discovery (2026-04-27)**: `FullyMonomorphic t` rejects polymorphic source code. IxVM (`Core.lean`, `Kernel.lean`, `Blake3.lean`, `Sha256.lean`) uses generic `List<T>`, `Option<T>`, `list_length<T>` etc. throughout — 12 polymorphic defs in Core, 42 in Kernel.

**Why it's there**: proof shortcut. Under FullyMono, `concretizeName g #[] = g`, so source and concrete decls share a namespace. Without it, every preservation lemma must thread `concretizeName` mangling explicitly.

**Soundness**: NOT a real precondition — `concretize` IS the monomorphization, runs regardless of source polymorphism. FullyMono is a proof convenience.

**Fix scope**: 174 references across 9 files. Multi-week rewrite of the `_under_fullymono` family.

**Status**: TEMPORARY tag in `WellFormed`, marked for removal. See "Refactor — Polymorphic source support" section below.

### SD2 — `AppFreeTyp` stricter than `wellFormedDecls` enforces

**Discovery (2026-04-27)**: `AppFreeTyp` (no `.app` constructor anywhere) is strictly stronger than what `wellFormedDecls` enforces. `wellFormedType`'s `.app` arm only requires `args.size = dt.params.length`; under FullyMono args=#[], but `.app g #[]` syntactically survives. `expandTypeM` and `zonkTyp` preserve `.app` structurally without rewriting (`Compiler/Check.lean:394`).

**Implication**: any proof strategy assuming "no `.app` types after checkAndSimplify under FullyMono" is unsound.

**Refined strategy** (NOT YET IMPLEMENTED): exploit `IndexMap.insert` at existing key = `pairs.set` in-place (no size growth, verified at `Ix/IndexMap.lean:39`). This obviates the need for `concretizeSeed = empty` reasoning.

### SD3 — `ConstrainedCallGraphAcyclic` removed (2026-04-27)

`hasConstrainedCall` was a placeholder returning `False`. The acyclicity predicate trivially held. Never consumed by any proof. Removed from `WellFormed` — was dead-weight.

## Architecture

```
Source.Toplevel
  ├── mkDecls         → Source.Decls
  ├── checkAndSimplify
  │     ├── wellFormedDecls
  │     ├── typecheck (mvar resolution + zonking)
  │     └── simplifyDecls
  │       └────────────→ Typed.Decls
  ├── concretize       (Typed.Decls → Concrete.Decls)
  │     ├── drainMono  (worklist: pending → seen + mono + newFunctions/newDataTypes)
  │     ├── concretizeBuild  (srcStep + dtStep + fnStep folds → monoDecls)
  │     └── step4Lower (Typ → Concrete.Typ via typToConcrete)
  ├── lower            (Concrete.Decls → bytecode + preNameMap)
  └── deduplicate      (bytecode → bytecode + remap)
```

**Semantic chain**:
```
Source.Eval.runFunction (decls, name, args, io, fuel)
  ≈[InterpResultEq]
Bytecode.Eval.runFunction (bytecode, funIdx, flatten args, io, fuel)
```

`InterpResultEq` is asymmetric: source-ok → bytecode-ok-and-equivalent; bytecode permitted to over-succeed where source errors.

## Path to F=0 closure (5-phase plan)

All Phase numbering relative to this plan. Each Phase is multi-round.

### Phase 0 (Required): Polymorphism refactor — drop `FullyMonomorphic`

**Why first**: `FullyMonomorphic` excludes IxVM. ALL downstream proof work targets a `WellFormed` that real Aiur programs don't satisfy. Building atop FullyMono is building on quicksand.

**Scope**: 174 references across 9 files; ~5000 LoC rewrite.

**Strategy**:

1. **Reformulate** `_under_fullymono` lemmas to take a generic `mono : (Global × Array Typ) → Option Global` correspondence (this is `drained.mono` from concretize). Source name `g` resolves to concrete name `mono[(g, args)]?.getD g`.

2. **Bridge lemma**: `concretize_produces_mono_correspondence : tds.concretize = .ok cd → ∃ mono, ...` — packages `drained.mono` as a public-facing certificate.

3. **Rewrite the 7 `_under_fullymono` theorems** in `ConcretizeSound.lean`:
   - `concretize_under_fullymono_preserves_ctor_kind_fwd`/`bwd`
   - `concretize_under_fullymono_preserves_dataType_kind_fwd`
   - `concretize_under_fullymono_ctor_idx_agree`
   - `concretize_under_fullymono_dt_flat_size_agree` (S4)
   - `flatten_agree_under_fullymono`
   - `concretize_extract_function_at_name` (S6)

   Each becomes `concretize_preserves_*` with explicit `mono` argument.

4. **Update `compile_correct`** body to thread `mono` through. The actual top-level statement does not change — `WellFormed` drops `fullyMonomorphic` but adds nothing (the new bridge is intrinsic to `monoTerminates`).

5. **Update PLAN_3B.md** — its TASK C/B closure becomes the polymorphic-aware versions of those theorems.

**Estimated cost**: 8-15 agent rounds, ~5000 LoC. Multi-week.

**Test gate after Phase 0**: `WellFormed t` for IxVM `core` (Core.lean) decidable to `True` — no FullyMono blocker.

### Phase 1: Lower-pass core soundness extension (in progress)

**Status**: 30/37 preservation arms F=0. 7 remaining sub-sorries inside `toIndex_preservation_core_extended` (S7).

**Remaining**: 6 access arms (`.proj`/`.get`/`.slice`/`.set`/`.letLoad`/`.load`) need a `ValueHasTyp v τ` typed-Value invariant carrier in `IsCoreExtended` (~300+ LoC), then `flattenValue_slice_at_offset` helper closes them all. `.app` arm deferred to Phase 5 (mutual fuel-IH with `concretize_preserves_runFunction`).

**Estimated cost**: 2-4 rounds, ~500-800 LoC.

### Phase 2: TASK C — `_dt_flat_size_agree` (S4)

**Status**: lost ~3000 LoC of session decomposition work in revert. Rebuild post-Phase 0.

**Approach**: under polymorphism-aware framework (Phase 0 complete), use `mono`-correspondence to lift Typ flat-size agreement. The mutual fuel-induction structure (Layer 1 of prior session) survives — only the `_under_fullymono` wrapping changes.

**Estimated cost**: 4-8 rounds, ~2000-3000 LoC of new infra (Layer 1 mutual proof + DeclsAgreeOnDtFM derivation + size-eq + composition).

**Replaces**: PLAN_3B.md (now obsolete in its FullyMono form).

### Phase 3: `concretize_preserves_TermRefsDt` (S2)

Mirror of `concretize_preserves_FirstOrderReturn` (closed F=0). ~300 LoC composition chain over the per-step preservation lemmas.

**Estimated cost**: 1-2 rounds.

### Phase 4: `runFunction_preserves_FnFree` (S1)

Largest single chunk. Mutual induction over 6 interp-family functions (`runFunction`, `interp`, `applyGlobal`, etc.) + `unflattenValue_FnFree` aux. ~1200 LoC.

Independent of Phase 0 outcome (operates on `Concrete.Decls`).

**Estimated cost**: 3-5 rounds.

### Phase 5: `concretize_preserves_runFunction` (S3) + `spine_transfer` (S5) + LowerSoundControl wiring

The heart-theorem composition. Once Phases 0-4 done:
- S3: 60-100 LoC composition.
- S5: ~500-700 LoC (own backward-trace infra).
- S8/S9 (LowerSoundControl): wire S7 + per-arm semantic lemmas.

**Estimated cost**: 3-6 rounds.

### Total

~25-40 agent rounds, ~12,000-15,000 LoC. Multi-month if pursued single-thread. Parallelizable phases: 1, 4, 5-helpers. Phase 0 + Phase 2 sequential.

## PLAN_3B.md status

**Deprecated as written**. PLAN_3B targets `flatten_agree_under_fullymono` — itself a `_under_fullymono` theorem that Phase 0 obsoletes.

Useful infrastructure documented in PLAN_3B that survives Phase 0:
- `Typ.MatchesConcreteFM` predicate (structural correspondence). Generalizes cleanly to use `mono` correspondence.
- `Source.Decls.DeclsAgreeOnDtFM` predicate (structure form). Strengthens to bidirectional under `mono`.
- Layer 1 mutual proof shape: `typFlatSizeBound_agree` + `dataTypeFlatSizeBound_agree`. Body unchanged; takes generic `DeclsAgreeOnDt` instead of `_FM` variant.

**Action**: rewrite PLAN_3B.md as Phase 2 detail post-Phase 0. Keep current PLAN_3B.md as reference until then.

## Methodology

### Sorry-budget management

- Per-declaration sorry count is the headline metric.
- Granular sub-sorries with **BLOCKED** notes preferred over monolithic (memory `feedback_granular_sorries`).
- Net +N sorries acceptable when each new sorry is a precisely-named bridge (sig-fix exemption).
- Phase 0 will introduce many sub-sorries during decomposition; expect net +N in early rounds, then -N as closures land.

### Agent dispatch

**What works** (~30-60 tool uses):
- Tightly-scoped task with concrete code stubs.
- Pre-checked infra hypotheses (`#synth`, `#check`).
- Explicit BLOCKED-note instructions for fallback.

**What fails**:
- Long agent runs (100+ tool uses) hit transport breakages OR over-plough on speculative paths.
- Agents removing infrastructure they don't fully understand → file inconsistencies (Phase 2 agent on 2026-04-27 removed `drained_empty_*` without updating callers, broke build).

**Mitigation**:
- ≤ 80-100 tool uses per round.
- Agents NEVER delete proof infrastructure they aren't fully replacing in the same session.
- Background agents (`run_in_background: true`) for long runs; main thread monitors via mtime/size, kills via `TaskStop` on staleness.
- Sequential agents on same file. Parallel agents only via worktree isolation (heavy merge cost).

### Banned (per memory)

- `sed`, `awk`, `head`, `tail`, `cat` for file I/O — use `Read` tool.
- `lake test` during agent runs (RustFFI, slow).
- `git` commands inside agents (approval prompts).
- `cargo clippy` — use `cargo xclippy`.
- `lake test` bare — use `lake test <suite-name>`.
- `lake build` before `lake test` — test builds automatically.
- `timeout N lake build`.

### Conventions

- Aiur source: `snake_case` for fn/locals; `PascalCase` for ctors.
- Lean: structural recursion over `Nat.strongRecOn` (not `Nat.strong_induction_on`).
- `@[expose]` on cross-module def bodies that need unfolding.
- Anonymous constructor `⟨...⟩` for structures; pattern matching for destructuring.

### Sig-fix > proving weaker-than-true

When a theorem is FALSE-as-stated, fix the signature, thread the new hypothesis through downstream callers. NEVER prove a weakened version that vacuously passes. Examples in this codebase:
- `concretizeName` not globally injective → `Typed.Decls.ConcretizeUniqueNames`.
- `eval_congr_dedup` arity-mismatch → `WellFormedCallees`.
- `sizeBound_ok_of_rank` vis arg → `SizeBoundVisInv`.

### Decompose-then-close

Round N: add invariants + decompose opaque sorry into precise sub-pieces (count unchanged or +N). Round N+1: close sub-pieces F=0.

## Anti-patterns

1. `axiom` substitution for proof body — use `sorry` for visibility.
2. Sub-sorry stacking beyond net-decrease (allowed only under sig-fix exemption).
3. `lake test` during agent run.
4. Mathlib tactics (`set X := Y with hX`, etc.) — see TACTICS.md "Mathlib-only tactics to avoid".
5. Missing `@[expose]` on defs crossing module boundaries.
6. Props in `Proofs/` files — move to `Semantics/`.
7. Vacuous-hypothesis axioms (`_unused : Unit`, `True`-alias stub bodies).
8. **Sig defects as features**: when a theorem is FALSE-as-stated, fix sig + thread callers BEFORE body work.
9. **Imperative compiler code blocking proofs**: refactor compiler-side `Id.run (do for in)` / EStateM mutable accumulator to pure form first.
10. **Building on `_under_fullymono` for compile_correct**: the FullyMono assumption excludes IxVM. Do not author NEW `_under_fullymono` lemmas; refactor existing ones in Phase 0.

## Persistence rules

- `grind`/`simp only`/`rw` failing → `split + cases`.
- Fold-body mismatch → `List.foldlM_congr_body` (`Lib.lean`).
- **Sig defects are DROP-EVERYTHING priority**: fix sig + caller discharge BEFORE body work.
- **Compiler refactors first**: when proof blocked on imperative compiler code, refactor compiler-side first (saves 100-300 LoC per proof).
- **Don't bulk-delete agent files before merging** their decomposition tree (memory `feedback_merge_before_delete`).
- **Single-agent dispatches edit real files directly** (memory `feedback_single_agent_no_scratch`); scratch only for parallel runs.
- **Amend topmost commit** on `ap/aiur-compiler` (memory `feedback_amend_topmost`).
- **Don't commit PLAN.md / PLAN_3B.md** (memory `feedback_no_plan_md_commit`).

## Agent dispatch template

```
READ FIRST: TACTICS.md + PLAN.md + MEMORY.md.
TASK: <one closure target OR one sig-defect fix>.
WORKING FILE(S): <list>.
BUILD: lake build <module> (no `lake test`, no bare `lake build`).
BANNED: sed, awk, head, tail, cat, mkdir, touch, rm, cp, lake test, git, cargo, timeout.
RULES: F=0 ideal; F=1 OK with BLOCKED note; granular sub-sorries > monolithic;
       no Mathlib; no vacuous-hyp axioms; no axiom-for-sorry swaps.
TARGET: ≤100 tool uses. Report build status + per-target F-status + LoC delta.
```
