# PLAN_3B — Sorry 3b `.ctor` arm closure (exhaustive)

> **DEPRECATED 2026-04-27**: This plan targets `flatten_agree_under_fullymono`,
> a `_under_fullymono` theorem that becomes obsolete in Phase 0 of `PLAN.md`.
> The `FullyMonomorphic` assumption excludes IxVM (polymorphic source code),
> so building closure work atop it is unsound for the real `compile_correct`
> target. See `PLAN.md` "Sig defects → SD1" + "Phase 0".
>
> **Reusable infrastructure** that survives Phase 0 (rewritten to take a
> generic `mono : (Global × Array Typ) → Option Global` correspondence
> instead of FullyMono):
>
> - `Typ.MatchesConcreteFM` predicate (structural correspondence).
> - `Source.Decls.DeclsAgreeOnDtFM` predicate.
> - Layer 1 mutual proof shape (`typFlatSizeBound_agree` +
>   `dataTypeFlatSizeBound_agree`) — body unchanged; takes generic predicate.
> - `mkDecls_dt_implies_ctor_keys` (CheckSound) — independent of FullyMono.
> - TASK B Layer 1+2 explicit-form ctor lemmas — generalize cleanly.
>
> **Lost on 2026-04-27 revert**: ~3000 LoC of session decomposition work on
> ConcretizeSound:5527. Will rebuild as Phase 2 of `PLAN.md` post-Phase 0.



## Target

`Ix/Aiur/Proofs/ConcretizeSound.lean:flatten_agree_under_fullymono` — `.ctor g args` arm.
Currently F=0 conditional on 3 sub-sorries (`_ctor_kind_bwd`, `_ctor_idx_agree`,
`_dt_flat_size_agree`). The `_ctor_kind_bwd` itself has 4 internal sub-sorries.

## Goal sig

```lean
theorem flatten_agree_under_fullymono
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (_hmono : FullyMonomorphic t)
    (_hdecls : t.mkDecls = .ok decls)
    (_hts : t.checkAndSimplify = .ok typedDecls)
    (_hconc : typedDecls.concretize = .ok concDecls)
    (funcIdx : Global → Option Nat) :
    ∀ (v : Value),
      flattenValue decls funcIdx v = Concrete.flattenValue concDecls funcIdx v
```

## Pipeline recap

```
decls (Source.Decls)
  --[checkAndSimplify]--> typedDecls (Typed.Decls)
  --[concretize = drain + concretizeBuild + step4Lower fold]--> concDecls (Concrete.Decls)
```

Under `FullyMonomorphic t`:
- All source/typed dt + fn `params = []`.
- `concretizeName g #[] = g` (name preservation under empty args).
- Source ctor key `g = dt.name.pushNamespace c.nameHead` for some dt + c.

## Closed pieces (all amended into commit `82f3c2f`)

- Phase A.1: `checkAndSimplify_preserves_ctor_kind_fwd` F=0.
- Phase A.2: `PhaseA2.concretizeBuild_preserves_ctor_kind_fwd` F=0.
- Phase A.3: `step4Lower_preserves_ctor_kind_fwd` F=0.
- Phase A.4: `concretize_under_fullymono_preserves_ctor_kind_fwd` F=0.
- `concretize_under_fullymono_preserves_ctor_kind_bwd` F=0.
- `mkDecls_dt_implies_ctor_keys` F=0 (CheckSound).
- TASK B Layer 1: `PhaseA2.concretizeBuild_at_typed_ctor_explicit_general` F=0.
- TASK B Layer 2: `step4Lower_constructor_explicit` F=0.
- TASK B Layer 3a: `LawfulBEq Constructor` manual instances in `Stages/Source.lean:400` and `Stages/Concrete.lean:338`.
- TASK B Layer 3b: `mkDecls_dt_ctor_nameheads_distinct` F=0 (CheckSound:3394) + `MkDeclsInvDistinct` chain (CheckSound:3210-3393).
- TASK B Layer 3c: `concretize_under_fullymono_ctor_idx_agree` F=0 (ConcretizeSound:5178).
- Phase D wiring of `flatten_agree_under_fullymono` F=0 conditional on 1 remaining sub-sorry (was 3).
- TASK C scaffolding: `Typ.MatchesConcreteFM` predicate (CS:5362), `Source.Decls.DeclsAgreeOnDtFM` predicate (CS:5392), `TypFlatSizeAgreeFM` predicate (CS:5512), fuel-zero leaves + leaf arm lemmas (CS:5409-5486).
- `Typ.instantiate_empty_id`, `mkParamSubst_nil`, `SrcDtParamsMonoP_mkDecls` (non-private), `checkAndSimplify_keys_local` (non-private), `fnStep_foldl_with_fname_yields_function`.

## Remaining sub-sorries

PLAN_3B-scope: just **TASK C** (`concretize_under_fullymono_dt_flat_size_agree`, ConcretizeSound:5541).

Out-of-scope sorries in ConcretizeSound (other plans/files):
- L1050 — `FnFreeBody` mutual induction scaffold (~1200 LoC, separate sub-system).
- L2019 — `concretize_preserves_TermRefsDt` (~300 LoC composition chain).
- L2303 — top-level `concretize_preserves_runFunction` (depends on TASK C + others).
- L8295 — `DirectDagBody` rank-lift (~500-700 LoC).
- L9143 — final layoutMap inputs flat-size.

### Methodology for agent dispatch on remaining sub-sorries

Lessons from session history (commits `342f86f`, `0e61b35`, plus failed `_ctor_idx_agree` attempts):

**What worked**:
- Single-task agent with concrete code stub + lemma sig + ≤200 LoC budget (Agents 1, 2, Layer 1, Layer 2).
- Pre-checking infra hypotheses in main thread (e.g., `#synth LawfulBEq Constructor` before dispatching).

**What failed**:
- Composition agent (Layer 3 of `_ctor_idx_agree`) hit 2 hard blockers:
  1. `LawfulBEq Constructor` NOT auto-derived (verified via `#synth` check in main thread). Auto-`deriving LawfulBEq` doesn't work due to `Constructor`'s `BEq` being structurally derived from `Repr, BEq` deriving clause; manual instance needs to unfold `Constructor.beq` which doesn't exist by that name (auto-generated has different naming).
  2. Positional ctor nameHead distinctness: existing `mkDecls_ctor_companion` gives ctor membership but not pairwise distinctness. Need new invariant tracked through `mkDecls_dataTypeStep`'s inner ctor fold's `if allNames.contains` check.
- Long agent runs (50-150 tool uses) hit transport breakages, returning blank result with partial state.

**Going forward**:
- Each agent ≤ 80 LoC, ≤ 30 tool uses target.
- Pre-check Lean stdlib hypotheses (LawfulBEq, decidable equality, structural lemmas) in main thread first.
- For `_ctor_idx_agree` Layer 3: need 3 separate agents (LawfulBEq instance, distinctness invariant, composition).
- Background agents (`run_in_background: true`) untested but worth trying for >30 tool use estimates.

### TASK A: `concretize_under_fullymono_preserves_ctor_kind_bwd` ✅ DONE

**Location**: ConcretizeSound.lean:~3585.

**Sig**:
```lean
theorem concretize_under_fullymono_preserves_ctor_kind_bwd
    {t : Source.Toplevel} {decls : Source.Decls}
    {typedDecls : Typed.Decls} {concDecls : Concrete.Decls}
    (hmono : FullyMonomorphic t)
    (hdecls : t.mkDecls = .ok decls)
    (hts : t.checkAndSimplify = .ok typedDecls)
    (hconc : typedDecls.concretize = .ok concDecls)
    {g : Global} {cd_dt : Concrete.DataType} {cd_c : Concrete.Constructor}
    (hcd : concDecls.getByKey g = some (.constructor cd_dt cd_c)) :
    ∃ src_dt src_c, decls.getByKey g = some (.constructor src_dt src_c)
```

**Strategy**: Stage 1 (concrete → mono) ✓ done via `step4Lower_backward_ctor_kind_at_key`.
Stage 2 (mono → source) via `concretize_build_excludes_polymorphic` (CS:649) + 4 origin cases:
- Origin 1 (typed has srcD at g): cases on srcD's kind.
  - srcD = `.constructor`: source .ctor at g via `FnMatchP_checkAndSimplify` backward.
  - srcD = `.function`: contradicts mono .ctor unless origin 4 holds. Need origin-4 detection.
  - srcD = `.dataType`: symmetric to .function.
- Origin 2 (∃ f ∈ newFunctions, f.name = g): mono → .function (helper `fnStep_foldl_with_fname_yields_function` ✓ done). Contradicts mono .ctor.
- Origin 3 (∃ dt ∈ newDataTypes, dt.name = g): without origin 4, mono → .dataType. Need helper. With origin 4: dispatch.
- Origin 4 (∃ dt ∈ newDataTypes, ∃ c ∈ dt.constructors, dt.name.pushNamespace c.nameHead = g):
  - Use StrongNewNameShape: dt.name = source dt key (g_orig).
  - `c.nameHead` matches some `c_orig.nameHead` in dt_orig.constructors (via `dt.constructors.map nameHead = orig.constructors.map nameHead`).
  - Apply `mkDecls_dt_implies_ctor_keys` (NEW lemma, see below) to derive source has .ctor at `g_orig.pushNamespace c_orig.nameHead = g`.

**TASK A.1** (sub-task): `mkDecls_dt_implies_ctor_keys` in CheckSound.lean.

**Sig**:
```lean
theorem mkDecls_dt_implies_ctor_keys
    {t : Source.Toplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k dt, decls.getByKey k = some (.dataType dt) →
      ∀ c ∈ dt.constructors,
        decls.getByKey (k.pushNamespace c.nameHead) = some (.constructor dt c)
```

**Strategy**: combined invariant `MkDeclsInvDtCtor (acc) := MkDeclsInv acc ∧ <dt-to-ctor existence>`.
Preservation chain mirrors existing `MkDeclsInv` chain:
- `MkDeclsInvDtCtor_default`
- `MkDeclsInvDtCtor_functionStep`
- `MkDeclsInvDtCtor_dataTypeStep` (uses helpers below)
- `MkDeclsInvDtCtor_mkDecls`

Helpers needed (place after `MkDeclsInv_ctor_fold` at CheckSound:2393):
- `MkDeclsInv_dataTypeStep_mid`: extracts mid-state (post dt-insert pre-ctor-fold) `MkDeclsInv` from existing dataTypeStep proof's body.
- `ctor_fold_inserts_all`: after inner ctor fold, every ctor in `dataType'.constructors` has its key entry. Parameterized by `ctors_already`.
- `ctor_fold_preserves_other_key`: ctor fold preserves `getByKey k` for any `k` already in `acc.1.contains` (i.e., not equal to any newly-inserted ctor key).
- `MkDeclsInv_ctor_fold_dt_preserved`: dataTypeName's entry preserved through ctor fold.

**Estimated LoC**: ~400 (helpers) + ~100 (chain) = **~500 LoC**.

**Current attempt** (commits not pushed): partial code in CheckSound:~2519+ has sigs + bodies but build errors:
- Multiple `show ... at hget` syntax issues — fix: `change ... at hget`. (4 instances; user already corrected 3.)
- `ctor_fold_preserves_other_key` has 2 internal sorries in equality case — needs additional hypothesis `dataType'.name = dataTypeName` threaded through.
- Other downstream errors cascade from these.

**Discharge approach for agent**:
1. Read current CheckSound state (lines 2393-2710 area).
2. Fix `show ... at hget` → `change ... at hget` patterns.
3. Add `(hname : dataType'.name = dataTypeName)` hypothesis to `ctor_fold_preserves_other_key`.
4. Close the equality case using hname.
5. Update callers to thread hname.
6. Verify build green.

### TASK B: `concretize_under_fullymono_ctor_idx_agree` (Layer 1 + 2 done; Layer 3 blocked)

**Status**: Layer 1 (`PhaseA2.concretizeBuild_at_typed_ctor_explicit`) F=0. Layer 2 (`step4Lower_constructor_explicit`) F=0. Layer 3 (composition + findIdx? agreement) BLOCKED.

**Layer 3 blockers** (each is a SUB-AGENT task):

#### Sub-agent 3a: `LawfulBEq Constructor` instances (~50 LoC)

Files: `Ix/Aiur/Stages/Source.lean`, `Ix/Aiur/Stages/Concrete.lean`.

Verified in main thread: `#synth LawfulBEq Constructor` fails. Auto-`deriving LawfulBEq` doesn't work because `Constructor` uses `deriving BEq` which produces an unnamed `instBEqConstructor` — manual `LawfulBEq` instance requires unfolding via the inferred BEq.

Strategy: write manual instance using `BEq.beq` decomposition + LawfulBEq String + LawfulBEq (List Typ).

Pattern:
```lean
instance : LawfulBEq Constructor where
  eq_of_beq {a b} h := by
    have : a.nameHead == b.nameHead ∧ a.argTypes == b.argTypes := by
      rw [BEq.beq] at h
      -- Unfold derived beq. May need `simp only [show Constructor.beq = ... from rfl]` or similar.
      exact ⟨..., ...⟩
    obtain ⟨h1, h2⟩ := this
    cases a; cases b
    congr <;> [exact eq_of_beq h1; exact eq_of_beq h2]
  rfl {a} := by
    rw [BEq.beq]
    cases a
    -- Unfold derived beq, then use LawfulBEq.rfl.
    sorry  -- replace with concrete tactics
```

Hint: search Lean stdlib for `instLawfulBEqOfDecidableEq` — if `Constructor` has `DecidableEq`, `LawfulBEq` may be derivable via decidability. Check `deriving DecidableEq` works.

If that doesn't work, use `set_option diagnostics true` to see inferred BEq form.

#### Sub-agent 3b: Positional ctor nameHead distinctness (~120 LoC)

File: `Ix/Aiur/Proofs/CheckSound.lean`.

Sig:
```lean
theorem mkDecls_dt_ctor_nameheads_distinct
    {t : Source.Toplevel} {decls : Source.Decls}
    (hdecls : t.mkDecls = .ok decls) :
    ∀ k dt, decls.getByKey k = some (.dataType dt) →
      ∀ i j (hi : i < dt.constructors.length) (hj : j < dt.constructors.length),
        (dt.constructors[i]'hi).nameHead = (dt.constructors[j]'hj).nameHead → i = j
```

Strategy: extend `MkDeclsInv` with a 4th conjunct (positional distinctness for the dt's ctors), or write a separate `MkDeclsInvDistinct` with parallel preservation chain. Mirrors recent `MkDeclsInvDtCtor` pattern.

Inner ctor fold's `if allNames.contains ctorName` check ensures: when processing the j-th constructor, its `dataType.name.pushNamespace c.nameHead` not yet in allNames. If two ctors at positions i < j have `c_i.nameHead = c_j.nameHead`, then at j-th step, `dataType.name.pushNamespace c_j.nameHead = dataType.name.pushNamespace c_i.nameHead` IS in allNames (from i-th step), causing error. So successful fold ⟹ distinct.

#### Sub-agent 3c: Layer 3 composition (~150 LoC)

File: `Ix/Aiur/Proofs/ConcretizeSound.lean`.

Uses Layer 1 + Layer 2 + sub-agents 3a + 3b. Closes `concretize_under_fullymono_ctor_idx_agree` F=0.

Strategy: 
1. Apply `PhaseA2.concretizeBuild_ctor_origin` to dispatch on origin.
2. For both origins, derive positional bijection between src_dt.constructors and cd_dt.constructors via Layer 1 + Layer 2.
3. Apply `mkDecls_ctor_companion` to get `src_c ∈ src_dt.constructors`. Use `List.mem_iff_getElem` to get position i.
4. Use sub-agent 3b's distinctness lemma to show src_c is at UNIQUE position in src_dt.constructors.
5. By bijection + Layer 2's nameHead correspondence, cd_c is at same position i in cd_dt.constructors.
6. By distinctness on cd side (derived via bijection), cd_c at unique position i.
7. Both findIdx? return Some i. Equal.

Total Layer 3: ~320 LoC across 3 sub-agents.

### Original TASK B (preserved for reference)

**Location**: ConcretizeSound.lean:~3650.

**Sig**:
```lean
theorem concretize_under_fullymono_ctor_idx_agree
    (...)
    (hsrc : decls.getByKey g = some (.constructor src_dt src_c))
    (hcd : concDecls.getByKey g = some (.constructor cd_dt cd_c)) :
    src_dt.constructors.findIdx? (· == src_c) =
      cd_dt.constructors.findIdx? (· == cd_c)
```

**Strategy**: 
1. Trace the chain source → typed → mono → concrete for the `(src_dt, src_c)` pair.
2. typed has `(src_dt, src_c)` at g (FnMatchP backward — used by Phase A.4 already).
3. mono has `(md_dt, md_c)` at g where md_dt.constructors = src_dt.constructors.map (rewrite-ize) (under FullyMono empty subst, this is identity via `Typ.instantiate_empty_id` only on `.app`-free types — OR via direct rewriteTyp = id on tds-types).
4. concrete has `(cd_dt, cd_c)` at g where cd_dt.constructors = md_dt.constructors.mapM typToConcrete-ize (length preserved, position preserved).
5. cd_c at position k iff src_c at position k in src_dt (transformations are functions, preserve == element-wise).
6. findIdx? returns same Nat.

**Required helpers**:
- `concretize_dt_constructors_correspondence`: under FullyMono + hsrc + hcd, derive `cd_dt.constructors.length = src_dt.constructors.length` AND positional element correspondence.
- `findIdx?_via_image`: list lemma — if elements transform via function f, findIdx? agrees on transformed predicates.

**Sub-decomposition**:
- B.1: rewriteTyp on `src_c` with empty subst + drained.mono = identity-like (under FullyMono no `.app`s reachable in tds-types, OR `.app g #[]` rewrites to `.ref g` preserving structure).
- B.2: typToConcrete preserves positional structure of constructor list via mapM.
- B.3: position-tracking via `Array.foldl_induction` motive on monoDecls construction.
- B.4: findIdx? Nat-equality from elementwise function-preserves-eq.

**Estimated LoC**: ~250.

**Discharge approach for agent**:
1. Add `concretize_dt_constructors_correspondence` lemma (~150 LoC).
2. Use to prove `concretize_under_fullymono_ctor_idx_agree` (~80 LoC).
3. Verify build green.

### TASK C: `concretize_under_fullymono_dt_flat_size_agree`

**Location**: ConcretizeSound.lean:~3700.

**Sig**:
```lean
theorem concretize_under_fullymono_dt_flat_size_agree
    (...)
    (hsrc : decls.getByKey g = some (.constructor src_dt src_c))
    (hcd : concDecls.getByKey g = some (.constructor cd_dt cd_c)) :
    dataTypeFlatSize decls {} src_dt =
      Concrete.dataTypeFlatSize concDecls {} cd_dt
```

**Strategy**:
1. Both sides compute via fuel-bounded recursion. dataTypeFlatSize folds over ctor argTypes + max + 1.
2. Need: source dt's constructors and concrete dt's constructors have IDENTICAL flat-size sums per ctor.
3. Per ctor i: `src_dt.constructors[i].argTypes` flat-sum = `cd_dt.constructors[i].argTypes` flat-sum.
4. Per arg j: `typFlatSize decls {} (src_dt.constructors[i].argTypes[j])` = `Concrete.typFlatSize concDecls {} (cd_dt.constructors[i].argTypes[j])`.
5. Per-Typ flat-size correspondence: source `typFlatSize` agrees with concrete `Concrete.typFlatSize` after `typToConcrete`-image.

**Required helpers**:
- `typFlatSize_under_fullymono_eq`: per-Typ structural correspondence under FullyMono (~150 LoC).
- `dataTypeFlatSize_correspondence`: lift to whole dt (~50 LoC).

**Sub-decomposition**:
- C.1: leaves (`.unit`/`.field`/`.pointer`/`.function`/`.mvar`): trivial agreement.
- C.2: `.tuple`/`.array`: recursive via IH.
- C.3: `.ref g`: source typFlatSize via `decls.getByKey g` lookup → dt at g → recurse on dt's argTypes. concrete via `concDecls.getByKey g` lookup. Use `concretize_dt_correspondence_under_fullymono` (TASK B's helper).
- C.4: `.app g args`: under FullyMono args = #[]. Source typFlatSize on `.app g #[]` = source typFlatSize on `.ref g`. typToConcrete on `.app g #[]` = `.ref g` (under empty mono). So concrete typFlatSize on `.ref g`. Same.
- C.5: fuel induction with bound `decls.size + 1`.

**Estimated LoC**: ~300.

**Discharge approach for agent**:
1. Write `typFlatSize_under_fullymono_eq` with structural induction + fuel + dt-cycle handling (~200 LoC).
2. Lift to `dataTypeFlatSize_under_fullymono_eq` (~50 LoC).
3. Use in `concretize_under_fullymono_dt_flat_size_agree` (~30 LoC).

## Closure trajectory (updated 2026-04-26)

| Session | Task | LoC | Sorry count |
|---|---|---|---|
### Earlier campaign (TASK A + TASK B)

| Round | Task | F-status |
|---|---|---|
| Closed | TASK A.1 (`mkDecls_dt_implies_ctor_keys`) | F=0 |
| Closed | TASK A (`_ctor_kind_bwd`) | F=0 |
| Closed | TASK B Layer 1 (`concretizeBuild_at_typed_ctor_explicit`) | F=0 |
| Closed | TASK B Layer 2 (`step4Lower_constructor_explicit`) | F=0 |
| Closed | TASK B Layer 3a (LawfulBEq Constructor) | F=0 |
| Closed | TASK B Layer 3b (`mkDecls_dt_ctor_nameheads_distinct`) | F=0 |
| Closed | TASK B Layer 3c (`_ctor_idx_agree` composition) | F=0 |

### Session 2026-04-26 (TASK C campaign)

Massive progress on TASK C via cascading agent dispatches. Initial monolithic
sorry at `_dt_flat_size_agree` decomposed into a tractable F=1 tree with ~3000+
LoC of supporting infrastructure added.

| Round | What | F-status |
|---|---|---|
| Layer 1 | `TypFlatSizeAgreeFM` mutual proof + `DeclsAgreeOnDtFM` strengthened structure | F=0, ~246 LoC |
| Layer 2+3 | `dataType_kind_bwd` + composition + initial decomposition | F=0 (2a), F=1 cascade |
| Sig-defect fix | Replaced FALSE `fuel_monotone` with `concretize_size_eq_under_fullymono` | F=0 strategy |
| Cdc β | `step4Lower_foldlM_dt_consistency` + literal-form lemmas | F=0, ~256 LoC |
| Cdc α | `concretizeBuild_dt_consistency` decomposition | F=1 → 2 sub-sub-sorries (linked to L3) |
| Size-eq L1+L4+L5 | IndexMap-foldlM size induction infra (~474 LoC) | F=0 modulo `@[expose]` bridge |
| Size-eq bridge | Added `@[expose]` to `IndexMap.size`; closed L1/L4/L5 mechanically via `rfl` | F=0 |
| Size-eq L2 | `concretizeSeed_empty_under_fullymono` via `AppFree*` predicates | F=0 modulo A/B/C |
| L2 B+C | `collectInTypedTerm_empty_of_AppFreeTerm` + `collectCalls_empty_of_AppFreeTerm` | F=0, ~189 LoC |
| L2 A | `typedDecls_AppFreeDecl_of_fullyMonomorphic` | **F=2 sig defect** — see below |

### Remaining TASK C scope sub-sorries

1. **2b fwd** at line 6733 (~250 LoC): per-position constructor argType correspondence at every dt key under FullyMono. Mirror of TASK B Layer 1+2 lifted to dataType.
2. **A.α** at line 7294: `typedTyp_AppFree_of_fullyMonomorphic` — typed-side AppFreeTyp preservation through checkAndSimplify.
3. **A.β** at line 7316: `typedTerm_AppFree_of_fullyMonomorphic` — typed-side AppFreeTerm preservation through checkAndSimplify.

### KEY SIG DEFECT (discovered 2026-04-26)

The `AppFreeTyp` predicate (no `.app` constructor at all) is **strictly stronger**
than what `wellFormedDecls` enforces under `FullyMonomorphic`. Specifically,
`wellFormedType`'s `.app` arm only requires `args.size = dt.params.length`
(i.e., `args.size = 0` under FullyMono); it does NOT reject `.app g #[]`
syntactically. `expandTypeM` and `zonkTyp` preserve `.app` structurally without
rewriting (verified at `Compiler/Check.lean:394`).

**Consequence**: source/typed types can contain `.app g #[]` even under
`FullyMonomorphic + wellFormedDecls`. The `concretizeSeed = empty` strategy
(L2) is therefore unsound as stated.

**However** — under FullyMono, even when `.app g #[]` types exist:
1. `concretizeName g #[] = g`.
2. `drainMono` allocates `mono[(g, #[])] = g` and pushes `g`-named clones to
   `newFunctions`/`newDataTypes`.
3. `concretizeBuild`'s subsequent `dtStep`/`fnStep` folds insert these clones
   at keys `g` ALREADY OCCUPIED by srcStep's typedDecls copy — **IndexMap.insert
   at existing key is `pairs.set` (in-place), NOT push, so size is preserved**
   (verified at `Ix/IndexMap.lean:39`).
4. Hence `concretizeBuild.size = typedDecls.size` holds independently of
   newFns/newDts being empty.

**Refined strategy** (NOT YET IMPLEMENTED): replace L2 (`concretizeSeed_empty`)
with a direct `concretizeBuild_size_eq_under_fullymono_v2` that exploits in-place
overwrite at duplicate keys. The L4 currently closed by L1+L4+L5 agent likely
already accommodates this — recheck.

### Recommended next steps

**Option A** (continue F=0 attempt): replace AppFree-based path with the
in-place-overwrite argument. Recheck L4's actual close to see if it still holds
when newFns/newDts non-empty. If yes, A.α/A.β become unreachable. If no,
refactor L4.

**Option B** (accept F=1 status): leave the 3 sub-sorries with comprehensive
BLOCKED notes documenting the sig defect + refined strategy. Move on.

**Option C** (upstream change): strengthen `wellFormedType` to reject
`.app g #[]` syntactically (or normalize via `expandTypeM`). Closes A.α/A.β
naturally but requires source-language compiler change.

**Final state**: TASK C is **F=1** with 3 well-documented granular sub-sorries.
`flatten_agree_under_fullymono` is F=1 conditional on these 3.

**Net infrastructure added across the TASK C campaign**: ~3000+ LoC of
foundational proofs (mutual fuel induction, IndexMap-foldlM size lemmas,
AppFree predicates, literal-form step4Lower/concretizeBuild lemmas, dataType
kind preservation backward, etc.), all F=0.

## Agent dispatch templates

### Agent 1: Fix CheckSound build (`mkDecls_dt_implies_ctor_keys` infrastructure)

**Working dir**: `/workspace/dev/lean/ix/`.

**Goal**: Make `Ix.Aiur.Proofs.CheckSound` build green. Fix existing errors in current attempt.

**Approach**:
1. Read CheckSound.lean lines 2393-2710 to see current state.
2. `lake build Ix.Aiur.Proofs.CheckSound 2>&1 | grep -E "^error" | head -20` to see errors.
3. Fix mechanically per error:
   - `show ... at hget` → `change ... at hget` (4-5 instances).
   - `ctor_fold_preserves_other_key` equality case: add `(hname : dataType'.name = dataTypeName)` hypothesis. Use to derive `dataType'.name = dataTypeName` so dt at dataType'.name = dt at dataTypeName, gives MkDeclsInv constraint.
   - Update callers of `ctor_fold_preserves_other_key` to pass `hname`.
4. Verify build clean: `lake build Ix.Aiur.Proofs.CheckSound 2>&1 | grep -E "^error"` empty.
5. Verify tests still pass: `lake test -- aiur-cross 2>&1 | grep -E "FAIL|fail"` empty.
6. Commit via `git commit --amend --no-edit`.

**Constraints**:
- Don't add new `sorry`s.
- Keep all existing lemma sigs.
- Don't touch other files.

### Agent 2: TASK B (after A done)

Once Agent 1 done + bwd closed in TASK A: dispatch agent for ctor_idx_agree. Needs:
- Read PLAN_3B.md TASK B section.
- Implement `concretize_dt_constructors_correspondence` + `concretize_under_fullymono_ctor_idx_agree`.
- Use Phase A.4 forward + StrongNewNameShape + step4Lower's per-arm shape lemmas.

### Agent 3: TASK C (after A + B done)

Dispatch agent for dt_flat_size_agree. Needs structural correspondence from TASK B + per-Typ flat-size induction.

## Constraints for all agents

- Single-agent serial mode: edit real files directly (per memory).
- BANNED: `sed`, `awk`, `head`, `tail`, `cat`, `mkdir`, `touch`, `rm`, `cp`, `lake test`, `git`.
- Use `lake build <module>` for checking (not `lake test`).
- F=0 ideal; F=1 OK with BLOCKED note + sig-defect flag if detected.
- No Mathlib; no vacuous-hyp axioms; no axiom-for-sorry swaps.

## Existing infrastructure references

- `MkDeclsInv` family: CheckSound:~2188-2459.
- `MkDeclsInv_ctor_fold`: CheckSound:2284. Preserves invariant through inner ctor fold (parameterized by `ctors_already`).
- `MkDeclsInv_dataTypeStep`: CheckSound:2395.
- `MkDeclsInv_mkDecls`: CheckSound:2459.
- `mkDecls_ctor_companion`: CheckSound:2511 (forward direction; this plan's TASK A.1 is its dual).
- `mkDecls_dt_key_is_name`: CheckSound:2520.
- `concretize_build_excludes_polymorphic`: ConcretizeSound:649. 4-origin classification.
- `concretize_drain_preserves_StrongNewNameShape`: ConcretizeSound:2771.
- `step4Lower_fold_kind_at_key`: ConcretizeSound:2958.
- `step4Lower_function_shape` / `step4Lower_dataType_shape` / `step4Lower_constructor_shape`: ConcretizeSound:2825/2809/2844.
- `step4Lower_preserves_other_key`: ConcretizeSound:2861.
- `step4Lower_foldlM_no_key_preserves`: ConcretizeSound:2932.
- `Typ.instantiate_empty_id`: ConcretizeSound:1715.
- `concretizeName_empty_args`: ConcretizeSound:898.
- `IndexMap.indexMap_foldlM_eq_list_foldlM`, `IndexMap.getByKey_insert_self`, `IndexMap.getByKey_insert_of_beq_false`, `IndexMap.mem_pairs_of_getByKey`, `IndexMap.getByKey_of_mem_pairs`: standard IndexMap helpers in `/workspace/dev/lean/ix/Ix/IndexMap.lean`.

## Notes on FullyMono-specific simplifications

- `FullyMonomorphic t` ⟹ `∀ f ∈ t.functions, f.params = []` AND `∀ d ∈ t.dataTypes, d.params = []`.
- All source/typed/mono/concrete dts have `params = []`.
- `mkParamSubst [] _ = (fun _ => none)` (`mkParamSubst_nil`).
- `Typ.instantiate (fun _ => none) = id` on Typ (`Typ.instantiate_empty_id`).
- `concretizeName g #[] = g` (`concretizeName_empty_args`).
- `args.size = dt_orig.params.length = 0` ⟹ `args = #[]`.
- StrongNewNameShape: drained.newDataTypes' names = source dt-keys; ctor nameHeads pairwise match.
